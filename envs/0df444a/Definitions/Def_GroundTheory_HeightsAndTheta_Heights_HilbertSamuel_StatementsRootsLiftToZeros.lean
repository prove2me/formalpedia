-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsLiftToZeros
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsLiftToZeros
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:36.987968+00:00
-- url     : https://prove2.me/theorems/a8c8da64-faef-48b1-8393-7740eb8229db
-- title:
--   Statements Roots Lift To Zeros
-- statement:
--   Definitions and structural lemmas for Statements Roots Lift To Zeros, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsRootsLiftToZeros.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
def RootsLiftToZeros.Statement : Prop :=
  ∀ (σ : Type) (P : Ideal (MvPolynomial σ ℚ)) (e : ℕ) (ℓ : Fin e → MvPolynomial σ ℚ)
    (u : MvPolynomial σ ℚ) (G : Polynomial (MvPolynomial (Fin e) ℚ)),
    (∀ g : MvPolynomial σ ℚ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ),
      p.Monic ∧ p.eval₂ (aeval ℓ).toRingHom g ∈ P) →
    (∀ Q : Polynomial (MvPolynomial (Fin e) ℚ), Q.eval₂ (aeval ℓ).toRingHom u ∈ P → G ∣ Q) →
    ∀ (y : Fin e → ℂ) (t : ℂ), G.eval₂ (aeval y).toRingHom t = 0 →
      ∃ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) ∧ (fun j => aeval z (ℓ j)) = y ∧ aeval z u = t
end GroundTheory.Heights₂.Heights.HilbertSamuel


