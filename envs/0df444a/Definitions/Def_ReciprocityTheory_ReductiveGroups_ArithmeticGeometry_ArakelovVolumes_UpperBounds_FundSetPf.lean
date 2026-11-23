-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:45:45.164814+00:00
-- url     : https://prove2.me/theorems/0224d09d-a907-4cd1-8d65-0adc2cd5bc81
-- title:
--   Fund Set Pf
-- statement:
--   Definitions and structural lemmas for Fund Set Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FundSetPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (x0 : Frame X.Ψ r)
def R (z z' : V (nd X)) : Prop :=
  ∃ δ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact δ (cpt X x0 z) = rmul (cpt X x0 z') b
def Sat (A : Set (V (nd X))) : Set (V (nd X)) := {z | z ∈ OmF X x0 ∧ ∃ z' ∈ A, R X x0 z z'}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end ReciprocityTheory.ChartRestriction.G.AR.Up


