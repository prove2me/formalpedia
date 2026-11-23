-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsKMOne
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_IsKMOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:14.688452+00:00
-- url     : https://prove2.me/theorems/26c78def-206d-49b5-876f-7200378a04bc
-- title:
--   Is KMOne
-- statement:
--   Definitions and structural lemmas for Is KMOne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsKMOne.lean

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
namespace GlobalTheory.UCls
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
def IsUA (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  IsUnit g.det ∧ ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y
def IsKM (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    (k : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  IsUA c G k ∧ (∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ x - x = M • y) ∧ ∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ y = x
def ratM (F : Type) [Field F] [NumberField F] [Algebra F E] (γ : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) (RA F E) :=
  γ.map fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ x
def UEquiv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    (g g' : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∃ γ : Matrix (Fin n) (Fin n) E, IsUA c G (ratM F γ) ∧ ∃ k, IsKM c G L M k ∧ g' = ratM F γ * g * k
def classNo (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) : ℕ∞ :=
  ENat.card (Quot fun a b : {g // IsUA c G g} => UEquiv c G L M a.1 b.1)
def IsTA (c : E ≃ₐ[F] E) (t : RA F E) : Prop := t * sg (FiniteAdeleRing (𝓞 F) F) c t = 1
def TEquiv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) (t t' : RA F E) : Prop :=
  ∃ u : E, u * c u = 1 ∧ ∃ k, IsKM c G L M k ∧ t' = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ u) * t * k.det
def torusNo (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) : ℕ∞ :=
  ENat.card (Quot fun a b : {t // IsTA c t} => TEquiv c G L M a.1 b.1)
end GlobalTheory.UCls


