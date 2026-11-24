-- Prove2me | Definitions.Def_TailRiskSharing_VaRConv_Supplement_Simplex
-- name    : TailRiskSharing_VaRConv_Supplement_Simplex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:44:06.760093+00:00
-- url     : https://prove2.me/theorems/51b272ab-4ead-47aa-a34d-94641a3f4aa5
-- title:
--   (25) — nonnegative proportional coefficients and affine allocations
-- statement:
--   For $n$ agents and a total risk $X$, let $\Delta_n=\{c\in\mathbb R^n:c_i\geq0,\ \sum_i c_i=1\}$. The proportional-allocation objective and its global optimizer predicate are
--
--   $$J_X(c)=\sum_{i=1}^n\rho_i(c_iX),\qquad c\in\Delta_n,\quad J_X(c)\leq J_X(d)\ \text{for every }d\in\Delta_n.$$
--
--   For real cash transfers $\mu_i$, the associated affine allocation is $X_i=\mu_i+c_iX$. The condition $\sum_i\mu_i=0$ is imposed when claiming feasibility, not included in the definition of this function.
--
--   The simplex includes zero coefficients. The optimizer predicate does not assert that any optimizer exists; this matters for the counterexample to the printed attainment claim.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 23, (25) and Theorem 5

import Mathlib

namespace TailRiskSharing.VaRConv.Supplement

/-- (25) p.23: nonnegative coefficients summing to one, including the boundary. -/
def Simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {c | (∀ i, 0 ≤ c i) ∧ ∑ i, c i = 1}

/-- (25) p.23: exactly the sum of the agents' risks of c_i X. -/
def simplexObjective {Ω : Type*} {n : ℕ} (ρ : Fin n → (Ω → ℝ) → ℝ)
    (X : Ω → ℝ) (c : Fin n → ℝ) : ℝ :=
  ∑ i, ρ i (fun ω => c i * X ω)

/-- (25) p.23: a global minimizer, with no existence assumed. -/
def IsSimplexOptimizer {Ω : Type*} {n : ℕ} (ρ : Fin n → (Ω → ℝ) → ℝ)
    (X : Ω → ℝ) (c : Fin n → ℝ) : Prop :=
  c ∈ Simplex n ∧ ∀ d ∈ Simplex n, simplexObjective ρ X c ≤ simplexObjective ρ X d

/-- Theorem 5 p.23: affine allocations with cash transfers (zero-sum is a separate condition). -/
def affineAllocation {Ω : Type*} {n : ℕ} (X : Ω → ℝ) (μ c : Fin n → ℝ) :
    Fin n → Ω → ℝ := fun i ω => μ i + c i * X ω

end TailRiskSharing.VaRConv.Supplement


