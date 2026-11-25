-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AdaptExists
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AdaptExists
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:17:25.780615+00:00
-- url     : https://prove2.me/theorems/6e85573c-07fe-4b12-a583-801608863e76
-- title:
--   Adapt Exists
-- statement:
--   Definitions and structural lemmas for Adapt Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AdaptExists.lean

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
namespace GlobalTheory.CompanionTheory.BmuAdapt
section general
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
end general
def s2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)
def col (k r : ℕ) (j : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if j.val = r then s2 • (bvec (wI k r 0) + bvec (wI k r (Fin.last k)))
  else if j.val = r + k then s2 • (bvec (wI k r 0) - bvec (wI k r (Fin.last k)))
  else bvec j
def G0 (k r : ℕ) : Mat (2 * r + k + 1) := Matrix.of fun i j => col k r j i
section entries
variable {k r : ℕ} {i j : Fin (2 * r + k + 1)}
end entries
end GlobalTheory.CompanionTheory.BmuAdapt


