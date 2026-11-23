-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:22.036945+00:00
-- url     : https://prove2.me/theorems/52b6fc38-a873-45c2-bac5-3c99250941d3
-- title:
--   Pair Unfold Pf A
-- statement:
--   Definitions and structural lemmas for Pair Unfold Pf A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPfA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
instance countGL : Countable (GL (Fin r) E) := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := E)
  have : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  exact Function.Injective.countable Units.val_injective
variable {X} {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))
def T : Set (Frame X.Ψ r) := {x | x ∈ X.dom ∧ D.Δ x ≠ 0 ∧ D.zOf x ∈ FF}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf


