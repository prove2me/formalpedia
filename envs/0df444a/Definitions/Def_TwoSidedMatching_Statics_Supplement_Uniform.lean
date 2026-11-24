-- Prove2me | Definitions.Def_TwoSidedMatching_Statics_Supplement_Uniform
-- name    : TwoSidedMatching_Statics_Supplement_Uniform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:02:38.836948+00:00
-- url     : https://prove2.me/theorems/879c27c5-fc88-4625-b027-c5346e86b467
-- title:
--   Online Appendix p. 5 — uniform quantile optimization, including zero widths
-- statement:
--   Let $C<V$ be the seller and buyer centers, and let $d,s\ge0$ be their dispersions. The inverse buyer-survival and seller-distribution quantiles, at common volume $q\in[0,1]$, are
--
--   $$B(q)=V+d-2dq,\qquad S(q)=C-s+2sq.$$
--
--   The objective is $q(B(q)-S(q))$. Define $\mu^*$ as the largest maximizer, $p^*=B(\mu^*)$, $w^*=S(\mu^*)$, and $\bar J^*$ independently as the supremum of the objective. The price turning threshold is exactly $\max\{((V-C)/3-x)^+,(\sqrt{(V-C)x}-x)^+\}$.
--
--   These definitions retain the zero-width uniforms and support the complete dispersion comparisons. **Formalization Note** The optimizer set is nonempty and compact, and the objective image is nonempty and bounded; attainment is asserted by the theorem. The source's proof on Supplemental Note pp. 16–17 supplies this quantile reading, including signed prices outside the nonnegative-price domain of (D). Agreement with (D) is a conclusion on their common domain, not an assumption.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Online Appendix p. 5, Theorem 4; Supplemental Note pp. 16–17, proof of Theorem 4

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Fluid

namespace TwoSidedMatching.Statics.Supplement

/-- Uniform inverse survival and cost quantiles. These also describe point masses. -/
def uniformB (V d q : ℝ) : ℝ := V + d - 2 * d * q
def uniformS (C s q : ℝ) : ℝ := C - s + 2 * s * q

def uniformObjective (V C d s q : ℝ) : ℝ :=
  q * (uniformB V d q - uniformS C s q)

/-- The maximizers, not a closed-form solution of the optimization problem. -/
def uniformOptimizers (V C d s : ℝ) : Set ℝ :=
  {q | q ∈ Set.Icc 0 1 ∧ ∀ r ∈ Set.Icc 0 1,
    uniformObjective V C d s r ≤ uniformObjective V C d s q}

noncomputable def uniformMu (V C d s : ℝ) : ℝ :=
  sSup (uniformOptimizers V C d s)

noncomputable def uniformP (V C d s : ℝ) : ℝ :=
  uniformB V d (uniformMu V C d s)
noncomputable def uniformW (V C d s : ℝ) : ℝ :=
  uniformS C s (uniformMu V C d s)

/-- Profit remains an independent optimization value. -/
noncomputable def uniformValue (V C d s : ℝ) : ℝ :=
  sSup (uniformObjective V C d s '' Set.Icc 0 1)

/-- The precise turning threshold from Theorem 4. -/
noncomputable def turn (V C other : ℝ) : ℝ :=
  max (max ((V - C) / 3 - other) 0)
    (max (Real.sqrt ((V - C) * other) - other) 0)

/-- Agreement of a positive-width uniform distribution with the existing density model. -/
def IsUniformMarket (E : TwoSidedMatching.Statics.Environment) (V C d s : ℝ) : Prop :=
  E.loB = V - d ∧ E.hiB = V + d ∧ E.loS = C - s ∧ E.hiS = C + s ∧
  (∀ x ∈ Set.Icc E.loB E.hiB, E.fB x = 1 / (2 * d)) ∧
  (∀ x ∈ Set.Icc E.loS E.hiS, E.fS x = 1 / (2 * s))

end TwoSidedMatching.Statics.Supplement


