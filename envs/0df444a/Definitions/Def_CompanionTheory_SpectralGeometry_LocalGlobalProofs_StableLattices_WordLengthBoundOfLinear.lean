-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordLengthBoundOfLinear
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordLengthBoundOfLinear
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:16:41.774659+00:00
-- url     : https://prove2.me/theorems/82f4576d-caeb-54ca-9f1d-88d1f43ab01e
-- title:
--   Word Length Bound Of Linear
-- statement:
--   Definitions and structural lemmas for Word Length Bound Of Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WordLengthBoundOfLinear.lean

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
noncomputable section
namespace GlobalTheory.CompanionTheory.BmuWordBd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def lieSub {n : ℕ} (Hm : Mat n) : Submodule ℝ (Mat n) where
  carrier := {X | Lie Hm X}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Lie] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, ha, hb, add_zero]
  zero_mem' := by simp [Lie]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, Lie] at *
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ha, smul_zero]
end GlobalTheory.CompanionTheory.BmuWordBd


