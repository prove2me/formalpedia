-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
-- name    : Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:39.697514+00:00
-- url     : https://prove2.me/theorems/3aff97d7-b4c5-47ab-9297-35874d636921
-- title:
--   Is Herm Form
-- statement:
--   Definitions and structural lemmas for Is Herm Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/IsHermForm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnRep
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
def hermE (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ a, ∑ b, x a * G a b * c (y b)
def IsUnE (c : E ≃ₐ[F] E) {n : ℕ} (G γ : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ x y, hermE c G (γ *ᵥ x) (γ *ᵥ y) = hermE c G x y
def IsHermForm (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ x, c (c x) = x) ∧ c ≠ 1 ∧ (∀ a b, c (G a b) = G b a) ∧ G.det ≠ 0
def refl (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) : Matrix (Fin n) (Fin n) E :=
  1 + ((u - 1) / hermE c G x x) • Matrix.vecMulVec x (G *ᵥ fun b => c (x b))
def Moved (c : E ≃ₐ[F] E) (P : Ideal (𝓞 E)) : Prop :=
  ∃ a ∈ P, ∃ b : 𝓞 E, (b : E) = c (a : E) ∧ b ∉ P
def SplitOr (c : E ≃ₐ[F] E) (N : ℕ) (s : 𝓞 E) : Prop :=
  s ≠ 0 ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → Moved c P ∨ (N : 𝓞 E) ∈ P
def SplitOff (c : E ≃ₐ[F] E) (N : ℕ) (s : 𝓞 E) : Prop :=
  s ≠ 0 ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → Moved c P ∧ (N : 𝓞 E) ∉ P
def CongAt {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (δ : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ t : ℕ, t.Coprime N ∧ ∀ v ∈ L, ∃ w ∈ L, t • (δ *ᵥ v - v) = D • w
variable [NumberField F]
def IsUnA (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y
variable (F) in

def fm {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (RA F E) :=
  γ.map fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ x
variable (F) in

def CongAtA {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (k : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)),
    t • (k *ᵥ z - z) = D • w
def SplitPl (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ P : Ideal (𝓞 E), P.IsPrime ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal ∧ Moved c P
def SuppSplit (c : E ≃ₐ[F] E) {n : ℕ} (N : ℕ) (h : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∃ e : FiniteAdeleRing (𝓞 F) F, e * e = e ∧ {v | e v ≠ 0}.Finite ∧
    (∀ v, e v ≠ 0 → SplitPl c v ∧ (N : 𝓞 F) ∉ v.asIdeal) ∧ (e ⊗ₜ[F] (1 : E)) • (h - 1) = h - 1
end GlobalTheory.UnRep


