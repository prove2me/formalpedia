-- Prove2me | Definitions.Def_LiqPremiaEq_Gam
-- name    : LiqPremiaEq_Gam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:02.916081+00:00
-- url     : https://prove2.me/theorems/1ad58553-2c99-42da-9b36-a6a926d26420
-- title:
--   Aggregate risk aversion $\bar\gamma$, the vector $c$ and the risk-aversion matrix $\Gamma$
-- statement:
--   Let $N\ge 2$ agents have risk aversions $\gamma^1,\dots,\gamma^N>0$, agent $N$ the most risk-averse. The **aggregate risk aversion** is
--
--   $$\bar\gamma=\Big(\sum_{n=1}^N\frac1{\gamma^n}\Big)^{-1}\qquad(3.4),$$
--
--   the vector $c=(c_1,\dots,c_{N-1})^\top$ has entries
--
--   $$c_n=\bar\gamma\Big(\frac1{\gamma^n}-\frac1{\gamma^N}\Big),$$
--
--   and the **risk-aversion matrix** is the $(N-1)\times(N-1)$ matrix
--
--   $$\Gamma=\mathrm{diag}\{\gamma^1,\dots,\gamma^{N-1}\}-\frac1N\,\mathbb 1_{N-1}\mathbb 1_{N-1}^\top\,\mathrm{diag}\{\gamma^1-\gamma^N,\dots,\gamma^{N-1}-\gamma^N\}\qquad(4.7),$$
--
--   i.e. $\Gamma_{nm}=\gamma^n\delta_{nm}-(\gamma^m-\gamma^N)/N$. $\Gamma$ drives the coupled forward-backward system of Lemma 4.2 and the Riccati system (4.8).
--
--   **Formalization Note** Agents are `Fin (M + 1)` with $N=M+1$; agent $N$ is `Fin.last M`, and $\Gamma$, $c$ are indexed by `Fin M` (agents $1,\dots,N-1$ via `Fin.castSucc`). No positivity is built in: the theorems state their hypotheses on $\gamma$.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, eq. (3.4), p.5; eq. (4.7), p.6; Lemma 4.4, p.8

import Mathlib

open Matrix

namespace LiqPremiaEq

/-- The aggregate risk aversion `γ̄ = (∑ₙ 1/γⁿ)⁻¹` of the `N = M + 1` agents.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (3.4), p.5.

**Formalization Note** Agents are `Fin (M + 1)`; the paper's agent `N` (the most risk-averse,
(3.2)) is `Fin.last M`, and the paper's agents `1, …, N − 1` are `Fin M` via `Fin.castSucc`. -/
noncomputable def gbar {M : ℕ} (γ : Fin (M + 1) → ℝ) : ℝ :=
  (∑ n, 1 / γ n)⁻¹

/-- The vector `c = (c₁, …, c_{N−1})ᵀ`, `cₙ = γ̄ (1/γⁿ − 1/γᴺ)`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Lemma 4.4, p.8.

**Formalization Note** Indexed by `Fin M` (agents `1, …, N − 1`); `γᴺ = γ (Fin.last M)`. -/
noncomputable def cvec {M : ℕ} (γ : Fin (M + 1) → ℝ) : Fin M → ℝ :=
  fun n => gbar γ * (1 / γ n.castSucc - 1 / γ (Fin.last M))

/-- The risk-aversion matrix
`Γ = diag{γ¹, …, γ^{N−1}} − (1/N) 1_{N−1} 1ᵀ_{N−1} diag{γ¹ − γᴺ, …, γ^{N−1} − γᴺ}`,
an `(N − 1) × (N − 1)` matrix with entries `Γₙₘ = γⁿ δₙₘ − (γᵐ − γᴺ)/N`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.7), p.6.

**Formalization Note** `N = M + 1` is the real number `(M : ℝ) + 1`; rows and columns are
indexed by `Fin M`. -/
noncomputable def Gam {M : ℕ} (γ : Fin (M + 1) → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.diagonal (fun n => γ n.castSucc)
    - (1 / ((M : ℝ) + 1)) • Matrix.of (fun (_ : Fin M) (m : Fin M) => γ m.castSucc - γ (Fin.last M))

end LiqPremiaEq


