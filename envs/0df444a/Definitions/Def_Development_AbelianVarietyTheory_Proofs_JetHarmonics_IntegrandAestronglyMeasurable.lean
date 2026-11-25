-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:41.678848+00:00
-- url     : https://prove2.me/theorems/95fc204c-1314-4536-bb1d-308d7890eea9
-- title:
--   Integrand Aestrongly Measurable
-- statement:
--   Definitions and structural lemmas for Integrand Aestrongly Measurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IntegrandAestronglyMeasurable.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
namespace GlobalTheory.RegularisedIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def SqIntegrable (D : RealPlaceData k r Wp Wq) (α : ℝ) : Prop :=
  0 ≤ α ∧ Integrable (fun g : Mt k r =>
    gN (Matrix.of g : Mat k r) ^ (-α) * gN (Matrix.of g : Mat k r) ^ (-α)) D.μG
variable {D : RealPlaceData k r Wp Wq} {α : ℝ}
end GlobalTheory.RegularisedIntegral


