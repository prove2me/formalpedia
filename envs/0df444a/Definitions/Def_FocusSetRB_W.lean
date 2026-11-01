-- Prove2me | Definitions.Def_FocusSetRB_W
-- name    : FocusSetRB_W
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:45.77142+00:00
-- url     : https://prove2.me/theorems/e1e62521-70a0-472d-9b88-2acff5d2bcbb
-- title:
--   The weight matrix $W$, its maximal eigenvalue $\lambda_W$ and the norm $\|\cdot\|_W$
-- statement:
--   The **weight matrix** of the paper is
--
--   $$
--   W=\sum_{k=0}^{\infty}\big(P_{\bar\pi^*}-\Xi\big)^k\big(P_{\bar\pi^*}^\top-\Xi^\top\big)^k ,
--   $$
--
--   where $\Xi$ has every row equal to $\mu^*$. Each term is symmetric positive semidefinite and the $k=0$ term is the identity. $\lambda_W$ denotes the maximal eigenvalue of $W$, and for a row vector $u\in\mathbb R^{|\mathbb S|}$ the $W$-weighted $L_2$ norm is
--
--   $$
--   \|u\|_W=\sqrt{u\,W\,u^\top}.
--   $$
--
--   $\lambda_W$ measures how slowly $P_{\bar\pi^*}$ mixes, and it is the only chain-dependent quantity in the constant of Theorem 1.
--
--   **Formalization Note** $W$ is an infinite sum of real matrices with the entrywise topology. If the series does not converge, Lean assigns the sum the value $0$. Lemma 11 states that it converges under Assumption 1, and every theorem of the mission that uses $W$ assumes Assumption 1. $\lambda_W$ is written as the maximal Rayleigh quotient $\sup_{\|u\|_2=1}uWu^\top$, which equals the largest eigenvalue of the symmetric matrix $W$.
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Definition 2, eq. (30), p.17; ‖·‖_W: Lemma 1, p.17

import Mathlib
import Definitions.Def_FocusSetRB_piBar

namespace FocusSetRB

open Matrix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The weight matrix `W` of the `W`-weighted `L₂` norm (arXiv:2402.05689v4, Definition 2,
eq. (30), p.17): `W = ∑_{k=0}^∞ (P_π̄* − Ξ)^k (P_π̄*ᵀ − Ξᵀ)^k`.

**Formalization Note.** A `tsum` in `Matrix S S ℝ` (entrywise topology). A `tsum` of a
non-summable family is `0` in Lean; Lemma 11 (milestone `FocusSetRB.lemma_11`) is the statement
that the series converges under Assumption 1, and no item of the mission uses `W` without
Assumption 1. -/
noncomputable def W (M : SingleArmMDP S) (y : S → Bool → ℝ) : Matrix S S ℝ :=
  ∑' k : ℕ, (Ppi M y - Xi y) ^ k * ((Ppi M y)ᵀ - (Xi y)ᵀ) ^ k

/-- `λ_W`, the **maximal eigenvalue** of `W` (arXiv:2402.05689v4, Definition 2, p.17).

**Formalization Note.** Written as the maximal Rayleigh quotient
`sup_{‖u‖₂ = 1} u W uᵀ`, which equals the largest eigenvalue because `W` is symmetric (each term
`A^k (Aᵀ)^k` of (30) is). The unit sphere is compact and nonempty for nonempty `S`, so the real
supremum is attained. -/
noncomputable def lamW (M : SingleArmMDP S) (y : S → Bool → ℝ) : ℝ :=
  ⨆ u : {u : S → ℝ // ∑ s, u s ^ 2 = 1}, u.1 ⬝ᵥ (W M y *ᵥ u.1)

/-- The `W`-weighted `L₂` norm `‖u‖_W = √(u W uᵀ)` of a row vector `u ∈ ℝ^{|𝕊|}`
(arXiv:2402.05689v4, Lemma 1, p.17). -/
noncomputable def normW (M : SingleArmMDP S) (y : S → Bool → ℝ) (u : S → ℝ) : ℝ :=
  Real.sqrt (u ⬝ᵥ (W M y *ᵥ u))

end FocusSetRB


