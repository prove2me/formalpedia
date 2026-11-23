-- Prove2me | Definitions.Def_LargeBSP_Homog_Supplement_PureBundle
-- name    : LargeBSP_Homog_Supplement_PureBundle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T16:53:28.813088+00:00
-- url     : https://prove2.me/theorems/2717a95e-e9d7-49cd-ab38-70993eaebb07
-- title:
--   §5.4, p. 22 — pure-bundle optimum p⋆(N), discount g⋆(N), σ, Cramér condition (Assumption 5)
-- statement:
--   The pure-bundling problem at zero marginal cost. The customer's valuations have common law with mean $\mu$, and $V_N(N)=\sum_{n\le N}X_n$ is the value of the full bundle.
--
--   1. **Revenue.** At price $p$ it is
--   $$R_N(p)=p\,\mathbb P\bigl(V_N(N)\ge p\bigr).$$
--   2. **Optimal price.** $p^\star(N)\ge0$ is optimal if $R_N(q)\le R_N(p^\star(N))$ for every $q\ge0$.
--   3. **Discount.** $g^\star(N)=N\mu-p^\star(N)$.
--   4. **Standard deviation.** $\sigma$ is the standard deviation of the valuation law.
--   5. **Assumption 5 (Cramér).** There is $K>0$ with $\mathbb E[e^{tX_1}]<\infty$ for all $|t|<K$.
--
--   These objects enter the second-order analysis of Lemma A2 and Theorem 6.
--
--   **Formalization Note** A customer indifferent between the bundle and no purchase buys it. The paper leaves this tie open. Under the strict event $V_N(N)>p$ the supremum of the revenue is the same, but no optimal price exists for discrete valuation laws, while the paper takes $p^\star(N)$ to be an optimal solution. The moment generating function is an extended nonnegative integral.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), SHA-256 1dfcad7675689de2118550b720b7488b45737ecd5ee5cd6085e5b5d0250d40cd, §5.4 and Assumption 5, p. 22

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LargeBSP.Homog.Supplement

/-- Pure-bundle revenue `p · P(V_N(N) ≥ p)` at zero cost (§5.4, p. 22). A customer indifferent
between the bundle and no purchase buys it (the page leaves this tie open). With the strict event
`V_N(N) > p` the supremum over prices is the same but is not attained for discrete laws, and the page
takes `p⋆(N)` to be an optimal solution. -/
noncomputable def pureRevenue {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (N : ℕ) (p : ℝ) : ℝ :=
  p * (P {ω | p ≤ V (fun i => X i ω) N N}).toReal

/-- `p` is an optimal solution of the pure-bundling problem over nonnegative prices. -/
def IsPureOptimum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (N : ℕ) (p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ q : ℝ, 0 ≤ q → pureRevenue P X N q ≤ pureRevenue P X N p

noncomputable def discount (ν : Measure ℝ) (p : ℕ → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) * (∫ x, x ∂ν) - p N

/-- The actual standard deviation of the valuation law. -/
noncomputable def sd (ν : Measure ℝ) : ℝ :=
  Real.sqrt (∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν)

/-- Cramer's condition, Assumption 5; a lintegral, so a divergent MGF is not counted as finite. -/
def CramerCondition (ν : Measure ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, |t| < K →
    (∫⁻ x, ENNReal.ofReal (Real.exp (t * x)) ∂ν) < ⊤

end LargeBSP.Homog.Supplement


