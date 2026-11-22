-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
-- name    : Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:04.321814+00:00
-- url     : https://prove2.me/theorems/1299518c-fbd2-494c-8819-94699d1ed8a4
-- title:
--   Hat1
-- statement:
--   Definitions and structural lemmas for Hat1, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/Hat1.lean

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
namespace GlobalTheory.AdLat
open NumberField IsDedekindDomain
open scoped TensorProduct
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
abbrev RA : Type := FiniteAdeleRing (𝓞 F) F ⊗[F] E
variable {E}
def fv {n : ℕ} (v : Fin n → E) : Fin n → RA F E := fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ v i
def hat {n : ℕ} (L : Set (Fin n → E)) : AddSubgroup (Fin n → RA F E) :=
  AddSubgroup.closure {z | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L, z = fun i => a ⊗ₜ x i}
def hat1 (J : Set E) : AddSubgroup (RA F E) :=
  AddSubgroup.closure {z | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ J, z = a ⊗ₜ x}
def latOf {n : ℕ} (g : Matrix (Fin n) (Fin n) (RA F E)) (L : Set (Fin n → E)) : Set (Fin n → E) :=
  {v | fv F v ∈ g.mulVec '' (hat F L : Set (Fin n → RA F E))}
variable {F}
def sg (A : Type) [CommRing A] [Algebra F A] (c : E ≃ₐ[F] E) : A ⊗[F] E →ₐ[F] A ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id F A) (c : E →ₐ[F] E)
def hermA (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) : RA F E :=
  ∑ a, ∑ b, x a * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G a b) * sg (FiniteAdeleRing (𝓞 F) F) c (y b)
end GlobalTheory.AdLat


