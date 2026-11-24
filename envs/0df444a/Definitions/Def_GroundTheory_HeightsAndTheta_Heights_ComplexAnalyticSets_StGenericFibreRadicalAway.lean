-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:17.073618+00:00
-- url     : https://prove2.me/theorems/f7e81493-114d-46fa-8b8f-35b0769cc16b
-- title:
--   St Generic Fibre Radical Away
-- statement:
--   Definitions and structural lemmas for St Generic Fibre Radical Away, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGenericFibreRadicalAway.lean

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
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
def IsRadicalAway {R : Type*} [CommRing R] (K : Ideal R) (g : R) : Prop :=
  ∀ f ∈ K.radical, ∃ k : ℕ, g ^ k * f ∈ K
def fibreIdeal {σ : Type*} {n : ℕ} (K : Ideal (MvPolynomial (Fin n) (MvPolynomial σ ℂ))) (t : σ → ℂ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  K.map (MvPolynomial.map (eval t))
def GenericFibreRadicalAway.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (n : ℕ) (K : Ideal (MvPolynomial (Fin n) (MvPolynomial σ ℂ)))
    (g : MvPolynomial (Fin n) (MvPolynomial σ ℂ)), IsRadicalAway K g →
    ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      IsRadicalAway (fibreIdeal K t) (MvPolynomial.map (eval t) g)
end
end GroundTheory.Heights₂.Heights


