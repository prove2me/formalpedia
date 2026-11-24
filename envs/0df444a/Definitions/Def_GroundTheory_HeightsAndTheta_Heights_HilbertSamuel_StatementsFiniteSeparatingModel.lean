-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiniteSeparatingModel
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiniteSeparatingModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:35.643061+00:00
-- url     : https://prove2.me/theorems/fb8204b1-4dcf-4f26-b42e-c42e3c8a6d69
-- title:
--   Statements Finite Separating Model
-- statement:
--   Definitions and structural lemmas for Statements Finite Separating Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsFiniteSeparatingModel.lean

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
open MvPolynomial Filter Topology
def FiniteSeparatingModel.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℚ)) (f : MvPolynomial σ ℚ) (x : σ → ℂ),
    P.IsPrime → f ∉ P → (∀ g ∈ P, aeval x g = 0) →
    ∃ (e : ℕ) (ℓ : Fin e → MvPolynomial σ ℚ) (u : MvPolynomial σ ℚ)
      (G : Polynomial (MvPolynomial (Fin e) ℚ)) (c D : MvPolynomial (Fin e) ℚ),
      G.Monic ∧ c ≠ 0 ∧ D ≠ 0 ∧
      (∀ i : σ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ), p.Monic ∧
        ∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
          p.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (z i) = 0) ∧
      (∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
        G.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (aeval z u) = 0) ∧
      (∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
        aeval (fun j => aeval z (ℓ j)) c ≠ 0 → aeval z f ≠ 0) ∧
      (∀ (y : Fin e → ℂ) (t : ℂ), aeval y D ≠ 0 → G.eval₂ (aeval y).toRingHom t = 0 →
        ∃ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) ∧ (fun j => aeval z (ℓ j)) = y ∧ aeval z u = t) ∧
      (∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
        (fun j => aeval z (ℓ j)) = (fun j => aeval x (ℓ j)) → aeval z u = aeval x u → z = x)
end GroundTheory.Heights₂.Heights.HilbertSamuel


