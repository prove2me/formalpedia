-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ChartExistence
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ChartExistence
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:15:30.729897+00:00
-- url     : https://prove2.me/theorems/48b7ce24-2ed0-5020-8b36-124c8878b03a
-- title:
--   Chart Existence
-- statement:
--   Definitions and structural lemmas for Chart Existence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ChartExistence.lean

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
namespace GlobalTheory.CompanionTheory.ProdExChart
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def lieSub (Hm : Mat n) : Submodule ℝ (Mat n) where
  carrier := {Y | Lie Hm Y}
  add_mem' := fun {A B} hA hB => by
    have hA' : Aᴴ * Hm + Hm * A = 0 := hA
    have hB' : Bᴴ * Hm + Hm * B = 0 := hB
    change (A + B)ᴴ * Hm + Hm * (A + B) = 0
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hA', hB', add_zero]
  zero_mem' := by simp [Lie]
  smul_mem' := fun c A hA => by
    have hA' : Aᴴ * Hm + Hm * A = 0 := hA
    change (c • A)ᴴ * Hm + Hm * (c • A) = 0
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hA', smul_zero]
end GlobalTheory.CompanionTheory.ProdExChart


