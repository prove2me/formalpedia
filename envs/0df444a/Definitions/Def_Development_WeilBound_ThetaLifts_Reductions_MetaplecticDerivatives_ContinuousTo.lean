-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousTo
-- name    : Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousTo
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:44.133599+00:00
-- url     : https://prove2.me/theorems/4a65e41d-9ff8-41a5-9890-49d1d909498b
-- title:
--   Continuous To
-- statement:
--   Definitions and structural lemmas for Continuous To, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousTo.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply


set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
namespace PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace MpA
theorem dense_sch : DenseRange (schwartzToL2 l) :=
  SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top
def ext (V : (Sch l →L[ℂ] Sch l)ˣ) (hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖) : L2 l ≃ₗᵢ[ℂ] L2 l :=
  (ContinuousLinearEquiv.unitsEquiv ℂ (Sch l) V).toLinearEquiv.extendOfIsometry
    (schwartzToL2 l).toLinearMap (schwartzToL2 l).toLinearMap dense_sch dense_sch fun f => hn f
abbrev gs (l : Type) [Fintype l] : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)
theorem eps_mem : Mem ((1, LinearIsometryEquiv.neg ℂ, -1) : Amb l) :=
  ⟨fun f => by simp, fun w f => by simp, fun w f => by simp, fun s' f _ => by simp⟩
def eps : G l := ⟨((1, LinearIsometryEquiv.neg ℂ, -1) : Amb l), eps_mem⟩
end MpA
open MpA
end PositivityTheory.ThKR.Mp
end


