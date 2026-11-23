-- Prove2me | Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
-- name    : CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:16.436728+00:00
-- url     : https://prove2.me/theorems/3b1d8c15-d167-4be2-a6e5-bc27a0cdecce
-- title:
--   Norm Exp Sub Le
-- statement:
--   Definitions and structural lemmas for Norm Exp Sub Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/NormExpSubLe.lean

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
namespace CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]
def mq (S : Eu l →L[ℝ] Eu l) : Sch l →L[ℂ] Sch l :=
  smulLeftCLM ℂ fun x : Eu l => ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I
def vf (H : Eu l →L[ℝ] Eu l) (f : Sch l) : Sch l :=
  bilinLeftCLM (ContinuousLinearMap.id ℝ (Eu l →L[ℝ] ℂ)) H.hasTemperateGrowth (fderivCLM ℝ (Eu l) ℂ f)
end CompanionTheory.ThKR.LL


