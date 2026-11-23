-- Prove2me | Definitions.Def_LargeBSP_Homog_Supplement_Mixture
-- name    : LargeBSP_Homog_Supplement_Mixture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T16:52:25.103995+00:00
-- url     : https://prove2.me/theorems/4dc9c89c-3ebb-4658-841b-60c3cf1b4389
-- title:
--   Assumption 4 and Theorem 4, p. 16 — law of cZ, limiting cost curve, double integral in (18)
-- statement:
--   Objects of the cost-dependent valuation model $X_n=c_nZ_n$. Let $C$ have law $F_C$ and $Z$ have law $F_Z$, independently, both nonnegative.
--
--   1. **Valuation law.** $F_X$ is the law of $CZ$. Its mixture form is $\int F_Z(x/c)\,dF_C(c)$, where the integrand at $c=0$ is $\mathbf 1\{x\ge0\}$, because the product is then $0$.
--   2. **Limiting cost.** With $q(t)=F_X^{-1}(1-t)$, for $t>0$,
--   $$\bar c(t)=\int c\,\bigl(1-F_Z(q(t)/c)\bigr)\,dF_C(c).$$
--   3. **Limiting gain.** For $t>0$, the double integral in (18) is
--   $$J(t)=\int\!\!\int_{q(t)/c}^{\infty}c(z-1)\,dF_Z(z)\,dF_C(c).$$
--
--   At $t=0$ the bundle is empty, so $\bar c(0)=J(0)=0$. Items with $c=0$ contribute $0$ to both integrals.
--
--   **Formalization Note** The cases $c=0$ and $t=0$ are separate branches. Lean's $x/0=0$ and $\inf\emptyset=0$ would otherwise give a wrong atom and, for an unbounded $F_X$, a wrong empty-bundle cost. The law of $CZ$ is the image of the product measure under multiplication.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), SHA-256 1dfcad7675689de2118550b720b7488b45737ecd5ee5cd6085e5b5d0250d40cd, Assumption 4 and Theorem 4, p. 16; (A10), p. A5; (A12), p. A6

import Mathlib
import Definitions.Def_LargeBSP_Homog_Supplement_Costs

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LargeBSP.Homog.Supplement

/-- Law of C Z for independent C and Z; this retains the atom due to zero costs. -/
noncomputable def productLaw (κ ρ : Measure ℝ) : Measure ℝ :=
  Measure.map (fun az : ℝ × ℝ => az.1 * az.2) (κ.prod ρ)

/-- The mixture cdf, with the deterministic zero product treated explicitly. -/
noncomputable def mixtureCdf (κ ρ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ a, (if a = 0 then (if 0 ≤ x then 1 else 0) else cdf ρ (x / a)) ∂κ

/-- Limiting cost curve, Theorem 4. At t=0 there is an empty bundle; the cutoff is +∞,
not Lean's default value for the real infimum of an empty quantile set. -/
noncomputable def mixtureCost (κ ρ : Measure ℝ) (t : ℝ) : ℝ :=
  if t = 0 then 0 else
    ∫ a, (if a = 0 then 0 else
      a * (1 - cdf ρ (quantile (cdf (productLaw κ ρ)) (1 - t) / a))) ∂κ

/-- The literal double integral in (18), with its empty-bundle and zero-cost cases. -/
noncomputable def mixtureGain (κ ρ : Measure ℝ) (t : ℝ) : ℝ :=
  if t = 0 then 0 else
    ∫ a, (if a = 0 then 0 else
      ∫ z in Set.Ioi (quantile (cdf (productLaw κ ρ)) (1 - t) / a),
        a * (z - 1) ∂ρ) ∂κ

end LargeBSP.Homog.Supplement


