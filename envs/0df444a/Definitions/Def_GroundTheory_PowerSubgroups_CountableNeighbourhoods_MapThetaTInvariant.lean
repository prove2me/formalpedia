-- Prove2me | Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
-- name    : GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:38:31.124412+00:00
-- url     : https://prove2.me/theorems/6532a375-e669-4f5e-b44d-446241dd0eef
-- title:
--   Map Theta TInvariant
-- statement:
--   Definitions and structural lemmas for Map Theta TInvariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/MapThetaTInvariant.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_BiEquivariantSigmaInvariant_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Variant₂.N1
open MeasureTheory Topology Filter ValuativeRel
namespace MapThetaTInvariant
section LocalField
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
end LocalField
section GeneralLinear
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
open GroundTheory.Automorphic.ContragredientTranspose in

lemma continuous_transposeGL {F : Type*} [Field F] [TopologicalSpace F] {n : ℕ} :
    Continuous (transposeGL : GL (Fin n) F → GL (Fin n) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_transpose
  · exact Units.continuous_coe_inv.matrix_transpose
open GroundTheory.Automorphic.ContragredientTranspose in

noncomputable def thetaTContinuous : GL (Fin n) F ≃ₜ* GL (Fin n) F :=
  { (thetaT : GL (Fin n) F ≃* GL (Fin n) F) with
    continuous_toFun := continuous_transposeGL.inv
    continuous_invFun := continuous_transposeGL.inv }
end GeneralLinear
end MapThetaTInvariant
open MapThetaTInvariant
end GroundTheory.Variant₂.N1


