-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceImmersiveGeneral
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceImmersiveGeneral
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:51:05.976264+00:00
-- url     : https://prove2.me/theorems/3070a7d6-181c-5533-a4d8-cb7c798f107a
-- title:
--   PSlice Immersive General
-- statement:
--   Definitions and structural lemmas for PSlice Immersive General, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceImmersiveGeneral.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceImmersiveGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology MeasureTheory
noncomputable section
def hyperplaneEmb (d : ℕ) : (Fin d → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi
    (Fin.cons 0 fun j => ContinuousLinearMap.proj j : Fin (d + 1) → (Fin d → ℂ) →L[ℂ] ℂ)
def sliceMap {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (γ : GroundTheory.Heights₂.Heights.VarBranch J (d + 1) p) : (Fin d → ℂ) → Fin n → ℂ :=
  fun t => γ.toFun (hyperplaneEmb d t)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


