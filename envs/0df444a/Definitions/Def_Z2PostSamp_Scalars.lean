-- Prove2me | Definitions.Def_Z2PostSamp_Scalars
-- name    : Z2PostSamp_Scalars
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:08.568978+00:00
-- url     : https://prove2.me/theorems/0f4bba3d-1ef2-4b33-a46d-12f5da50e145
-- title:
--   Scalar parameters: $A_\lambda$, $k_0$, $F$, the fixed points $q_\alpha$, $a_\alpha$, $\bar q_\alpha$
-- statement:
--   With all logarithms natural, set
--
--   $$A_\lambda=\max\Big\{256,\ \frac{64}{\log(2/(1+\lambda^{-2}))}\Big\},\qquad k_0=\min\{n,\lceil A_\lambda\log n\rceil\}.$$
--
--   The scalar channel function is $F(u)=\mathbb E\tanh^2(u+\sqrt u\,G)$, $G\sim\mathcal N(0,1)$. For $r,t\ge0$ the **positive root** $q$ is the positive solution of $q=F(rq+t)$; it exists and is unique when $t>0$, or $t=0$ and $r>1$. For $\alpha\in[0,1]$, $r_\alpha=\lambda^2(1-\alpha)$, $t_\alpha=\lambda^2\alpha$, $q_\alpha$ is the positive root at $(r_\alpha,t_\alpha)$, $a_\alpha=r_\alpha(1-q_\alpha)$ and $\bar q_\alpha=\alpha+(1-\alpha)q_\alpha$.
--
--   These constants set the length of the uniform prefix and the coefficients of the conditional TAP objectives.
--
--   **Formalization Note** $F$ is a Bochner integral of a bounded continuous integrand, hence a genuine expectation. The positive root is $\sup\{q\in(0,1]: q=F(rq+t)\}$ (every solution is at most $1$ and the positive one is unique in the cases used); where no positive solution exists the value is $0$, and no statement of the mission uses that case without excluding it.
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), (2.3), p.7; (2.9), p.10; §3.1, p.14

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Z2PostSamp

noncomputable section

/-!
# Scalar parameters: `A_λ`, `k₀`, the channel function `F`, and the fixed points `q_α`, `a_α`

Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), (2.3), p.7: `A = A_λ = max{256, 64/log(2/(1 + λ^{−2}))}`,
`k₀ = min{n, ⌈A log n⌉}`; (2.9), p.10: for `α ∈ [0,1]`, `r_α = λ²(1 − α)`, `t_α = λ²α`,
`F(u) = E tanh²(u + √u G)`, `q_α = F(r_α q_α + t_α)` (the positive solution), `a_α = r_α(1 − q_α)`,
`G ∼ N(0,1)`; p.14: `q̄_α = α + (1 − α) q_α`; §3.1, p.14: whenever `t > 0`, or `t = 0` and `r > 1`,
`q` denotes the unique positive solution of `q = F(rq + t)`.

**Formalization Note.** All logarithms are natural (p.7). `F` is a Bochner integral of the bounded
continuous integrand `tanh²(u + √u x)` against `N(0,1)`, so it is a genuine expectation; it is only
used at `u ≥ 0`. The positive root is `posRoot r t = sSup {q ∈ (0,1] | q = F(rq + t)}`: every
solution satisfies `q ≤ 1` because `tanh² < 1`, and §3.1 proves that the positive solution is unique
whenever `t > 0` or `t = 0, r > 1`, so this `sSup` is that solution. Where no positive solution
exists (`t = 0`, `r ≤ 1`) the value is `0`; no statement of the mission uses that case without
excluding it. `⌈·⌉` is `Nat.ceil`; `log n = 0` at `n ≤ 1`, where `k₀ = 0`.
-/

/-- `F(u) = E tanh²(u + √u G)`, `G ∼ N(0, 1)` (2.9). -/
def Fch (u : ℝ) : ℝ :=
  ∫ g, Real.tanh (u + Real.sqrt u * g) ^ 2 ∂(gaussianReal 0 1)

/-- The positive solution `q` of `q = F(rq + t)` (§3.1, p.14). -/
def posRoot (r t : ℝ) : ℝ :=
  sSup {q : ℝ | 0 < q ∧ q ≤ 1 ∧ q = Fch (r * q + t)}

/-- `r_α = λ²(1 − α)` (2.9). -/
def rAl (lam α : ℝ) : ℝ := lam ^ 2 * (1 - α)

/-- `t_α = λ²α` (2.9). -/
def tAl (lam α : ℝ) : ℝ := lam ^ 2 * α

/-- `q_α`, the positive solution of `q = F(r_α q + t_α)` (2.9). -/
def qAl (lam α : ℝ) : ℝ := posRoot (rAl lam α) (tAl lam α)

/-- `a_α = r_α(1 − q_α)` (2.9). -/
def aAl (lam α : ℝ) : ℝ := rAl lam α * (1 - qAl lam α)

/-- `q̄_α = α + (1 − α) q_α` (p.14). -/
def qbarAl (lam α : ℝ) : ℝ := α + (1 - α) * qAl lam α

/-- `A_λ = max{256, 64 / log(2/(1 + λ^{−2}))}` (2.3). -/
def Acoef (lam : ℝ) : ℝ := max 256 (64 / Real.log (2 / (1 + (lam ^ 2)⁻¹)))

/-- `k₀ = min{n, ⌈A_λ log n⌉}` (2.3). -/
def k0 (n : ℕ) (lam : ℝ) : ℕ := min n ⌈Acoef lam * Real.log n⌉₊

end

end Z2PostSamp


