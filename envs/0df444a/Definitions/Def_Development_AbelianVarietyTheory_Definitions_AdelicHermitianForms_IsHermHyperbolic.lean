-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
-- name    : Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:31.823664+00:00
-- url     : https://prove2.me/theorems/1687c19b-9599-40ed-8009-8b9d3f40867d
-- title:
--   Is Herm Hyperbolic
-- statement:
--   Definitions and structural lemmas for Is Herm Hyperbolic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/IsHermHyperbolic.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}
def hf (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) : R :=
  ∑ a, ∑ b, x a * G a b * σ (y b)
def IsU (σ : R →+* R) (G γ : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ x y, hf σ G (γ.mulVec x) (γ.mulVec y) = hf σ G x y
def tv (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (t : R) : Matrix (Fin n) (Fin n) R :=
  1 + Matrix.of fun a b => t * x a * ∑ e, G b e * σ (x e)
def TvGen (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) : Submonoid (Matrix (Fin n) (Fin n) R) :=
  Submonoid.closure {m | ∃ x t, hf σ G x x = 0 ∧ t + σ t = 0 ∧ m = tv σ G x t}
structure IsHerm {E : Type} [Field E] (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) : Prop where
  invol : ∀ a, σ (σ a) = a
  ne_id : ∃ a, σ a ≠ a
  herm : ∀ a b, σ (G a b) = G b a
  det_ne : G.det ≠ 0
end GlobalTheory.UTrans


