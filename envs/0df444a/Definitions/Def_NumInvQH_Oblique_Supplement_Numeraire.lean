-- Prove2me | Definitions.Def_NumInvQH_Oblique_Supplement_Numeraire
-- name    : NumInvQH_Oblique_Supplement_Numeraire
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:39:00.141237+00:00
-- url     : https://prove2.me/theorems/21996f11-e896-4705-afa2-3317d7a90e93
-- title:
--   Appendix D standing market and change-of-measure assumptions
-- statement:
--   Let $S=(X,Y)$ have at least two assets, with a designated coordinate $X$. The Appendix D model requires local square integrability of $S$ under $P$, $X,X_->0$, $X_T\in L^2(P)$, and local square integrability of $\widehat S=S/X$ under
--   $$\frac{d\widehat P}{dP}=\frac{X_T^2}{E[X_T^2]}.$$
--   Every object is computed from the original market and probability measure. No extra moment condition, nice-numeraire bound or deflator is bundled into these assumptions.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, p. 35, Appendix D standing assumptions

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Characteristics

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NumInvQH.Oblique.Supplement

/-- Exactly the standing assumptions at the start of Appendix D. -/
def AppendixD {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (S : Process Ω (Fin d → ℝ)) (first : Fin d) : Prop :=
  2 ≤ d ∧
  let X := fun t ω => S t ω first
  LocallySquareIntegrable P ℱ T S ∧ Positive P T X ∧ MemLp (X T) 2 P ∧
    LocallySquareIntegrable (changedMeasure P T X) ℱ T (discounted S X)

end NumInvQH.Oblique.Supplement


