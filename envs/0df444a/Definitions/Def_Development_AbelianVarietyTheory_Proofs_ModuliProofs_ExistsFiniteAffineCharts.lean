-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteAffineCharts
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteAffineCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:14.176311+00:00
-- url     : https://prove2.me/theorems/5d23fad1-90e9-4ec1-a633-5a7e3c072b30
-- title:
--   Exists Finite Affine Charts
-- statement:
--   Definitions and structural lemmas for Exists Finite Affine Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteAffineCharts.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
namespace GlobalTheory.FinAffineCharts
variable {X : Scheme.{0}}
noncomputable def refineLB (L : LB X) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) : LB X :=
  ⟨κ, W, fun a b => res (inf_le_inf (h a) (h b)) (L.g (c a) (c b))⟩
end GlobalTheory.FinAffineCharts


