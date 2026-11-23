-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotient
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:14.751435+00:00
-- url     : https://prove2.me/theorems/2668ab31-b201-437f-9c5f-840cb8b3e307
-- title:
--   Theta Pair Contragredient Quotient
-- statement:
--   Definitions and structural lemmas for Theta Pair Contragredient Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairContragredientQuotient.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct
namespace GlobalTheory.ThetaGL.DualPair
section General
variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def ev (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G W) :
    V ⊗[ℂ] smoothPart π.dual →ₗ[ℂ] W →ₗ[ℂ] V :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun (v : V) (l : smoothPart π.dual) => (l : Module.Dual ℂ W).smulRight v)
    (fun v v' l => by ext w; simp)
    (fun c v l => by
      ext w
      show (l : Module.Dual ℂ W) w • c • v = c • (l : Module.Dual ℂ W) w • v
      exact smul_comm _ _ _)
    (fun v l l' => by ext w; simp [add_smul])
    (fun c v l => by ext w; simp [smul_smul]))
end General
end GlobalTheory.ThetaGL.DualPair


