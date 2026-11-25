-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DerivedSeriesDerivation
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DerivedSeriesDerivation
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:26:49.290834+00:00
-- url     : https://prove2.me/theorems/81dd608a-1d73-5aaf-96f5-ead515a0d342
-- title:
--   Derived Series Derivation
-- statement:
--   Definitions and structural lemmas for Derived Series Derivation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DerivedSeriesDerivation.lean

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
namespace GlobalTheory.CompanionTheory.BmuDsDer
section general
variable {E E' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]
def dL (a : E → E) (Φ : E × E' → V) (q : E × E') : V := fderiv ℝ Φ q (a q.1, 0)
def dR (b : E' → E') (Φ : E × E' → V) (q : E × E') : V := fderiv ℝ Φ q (0, b q.2)
end general
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
def dW (W : List (Mat n)) (Φ : Mat n × Mat n → H) : Mat n × Mat n → H :=
  W.foldr (fun Y => dL fun g => g * Y) Φ
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
end GlobalTheory.CompanionTheory.BmuDsDer
end


