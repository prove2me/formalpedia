-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:37:18.319265+00:00
-- url     : https://prove2.me/theorems/1ed7e8d0-dd9c-4237-9832-648ce8580fd5
-- title:
--   Exists Cone Measure Pos Rank
-- statement:
--   Definitions and structural lemmas for Exists Cone Measure Pos Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasurePosRank.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder ComplexConjugate
noncomputable section
namespace GlobalTheory.HCXi.ConeOne
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
def radMeas (N : ℕ) : Measure ℂ := (volume : Measure ℂ).withDensity fun c => ENNReal.ofReal (‖c‖ ^ (2 * N))
instance (N : ℕ) : SFinite (radMeas N) := by unfold radMeas; infer_instance
def par (k r' : ℕ) (p : ℂ × HPar k r') : Fin (2 * (1 + r') + k + 1) → ℂ :=
  p.1 • (es0 k r' + liftVec k 1 r' p.2.1 + hb k r' p.2.1 p.2.2 • e0 k r')
instance hparSFinite (k r' : ℕ) : SFinite (volume : Measure (HPar k r')) := by
  rw [Measure.volume_eq_prod]; infer_instance
end GlobalTheory.HCXi.ConeOne
namespace GlobalTheory.HCXi
open ConeOne Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
end GlobalTheory.HCXi


