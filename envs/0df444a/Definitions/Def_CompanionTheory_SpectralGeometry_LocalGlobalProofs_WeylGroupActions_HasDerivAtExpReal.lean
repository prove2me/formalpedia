-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_HasDerivAtExpReal
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_HasDerivAtExpReal
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T17:00:54.216803+00:00
-- url     : https://prove2.me/theorems/26def003-9e44-4b2f-a24e-b6e132414e26
-- title:
--   Has Deriv At Exp Real
-- statement:
--   Definitions and structural lemmas for Has Deriv At Exp Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/HasDerivAtExpReal.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_ExpEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
namespace GlobalTheory.CompanionTheory.HolCoef
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def cone : Set (B.Mat 4 0) := {g | g 4 4 ≠ 0}
def IsHolHom {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (K : ℕ) (f : B.Mat 4 0 → E) : Prop :=
  AnalyticOnNhd ℂ f cone ∧ ∀ t : ℂ, t ≠ 0 → ∀ g ∈ cone, f (t • g) = (t ^ K)⁻¹ • f g
def minor2 (g : B.Mat 4 0) : ℂ := (g.submatrix ![3, 4] ![3, 4]).det
def minor3 (g : B.Mat 4 0) : ℂ := (g.submatrix ![2, 3, 4] ![2, 3, 4]).det
def minor4 (g : B.Mat 4 0) : ℂ := (g.submatrix ![1, 2, 3, 4] ![1, 2, 3, 4]).det
def coef (p N : ℕ) (g : B.Mat 4 0) : ℂ := (g 4 4 ^ N)⁻¹ * (minor2 g ^ p * minor3 g ^ p * minor4 g)
def wt (p N : ℕ) : Fin (2 * 0 + 4 + 1) → ℂ := ![0, 1, (p : ℂ) + 1, 2 * (p : ℂ) + 1, 2 * (p : ℂ) + 1 - N]
def eul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a b c d : Fin (2 * 0 + 4 + 1)) (f : B.Mat 4 0 → E) :
    B.Mat 4 0 → E := fun g => g c d • fderiv ℂ f g (Matrix.single a b 1)
section deriv
variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
end deriv
end GlobalTheory.CompanionTheory.HolCoef


