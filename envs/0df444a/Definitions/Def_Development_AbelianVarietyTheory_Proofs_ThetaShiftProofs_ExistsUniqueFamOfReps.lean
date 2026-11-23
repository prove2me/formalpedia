-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:29.631496+00:00
-- url     : https://prove2.me/theorems/de88d70d-c4b2-4015-bfc2-53c046b22a79
-- title:
--   Exists Unique Fam Of Reps
-- statement:
--   Definitions and structural lemmas for Exists Unique Fam Of Reps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFamOfReps.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FamFree
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
abbrev FamSec (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))
abbrev multiples (D : DegPre R) (k : ℕ) : AddSubgroup D.X := (nsmulAddMonoidHom k : D.X →+ D.X).range
end GlobalTheory.FamFree
namespace GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
end GlobalTheory


