-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLevi
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLevi
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:40:27.331796+00:00
-- url     : https://prove2.me/theorems/a86a13b1-2e34-4a4d-8e87-7fef006073aa
-- title:
--   Parabolic Line Stabilizer Levi
-- statement:
--   Definitions and structural lemmas for Parabolic Line Stabilizer Levi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
namespace GlobalTheory.HCXi.LineStabiliser
open GlobalTheory.LevelUnitary GlobalTheory.LevelStabiliser
variable (k r' : ℕ)
def fst : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩
def lst : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩
end GlobalTheory.HCXi.LineStabiliser


