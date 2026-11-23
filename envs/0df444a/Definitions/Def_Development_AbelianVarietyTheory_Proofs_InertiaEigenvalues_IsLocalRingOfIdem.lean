-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:57.333818+00:00
-- url     : https://prove2.me/theorems/e63a9b2b-d246-4b4e-99dd-29c194296d68
-- title:
--   Is Local Ring Of Idem
-- statement:
--   Definitions and structural lemmas for Is Local Ring Of Idem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
def cut (B : InvAlg K) (e : B.A) (he : B.σ e = e) : InvAlg K where
  A := B.A ⧸ Ideal.span {e}
  σ := Ideal.quotientEquiv _ _ B.σ (by rw [Ideal.map_span]; simp [he])
  σ_σ := fun y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [B.σ_σ]
  σ_alg := fun a => by
    rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, Ideal.quotientEquiv_mk, B.σ_alg]
  g := Ideal.Quotient.mk _ B.g
section Orb
variable {O : Type} [CommRing O] {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']
theorem mem_mulLat (t : Aˣ) (L : Submodule O A) (y : A) : y ∈ mulLat O (t : A) L ↔ ((t⁻¹ : Aˣ) : A) * y ∈ L := by
  unfold mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro h
    exact ⟨_, h, by simp⟩
theorem stabLat_mulLat (t : Aˣ) (L : Submodule O A) : stabLat O (mulLat O (t : A) L) = stabLat O L := by
  ext s
  change (∀ y, y ∈ mulLat O (t : A) L ↔ (s : A) * y ∈ mulLat O (t : A) L) ↔ ∀ y, y ∈ L ↔ (s : A) * y ∈ L
  simp only [mem_mulLat]
  constructor
  · intro h y
    have := h ((t : A) * y)
    rwa [Units.inv_mul_cancel_left, mul_left_comm, Units.inv_mul_cancel_left] at this
  · intro h y
    rw [mul_left_comm]
    exact h _
def orbWt (G : Subgroup Aˣ) (X : Set (Submodule O A)) : Orb O G X → ℚ :=
  Quot.lift (fun L => (((stabLat O L.1 ⊓ G).relIndex (intUnits O A ⊓ G) : ℕ) : ℚ)) (by
    rintro L M ⟨t, -, h⟩
    simp only [h, stabLat_mulLat])
end Orb
def IsIso {B C : InvAlg K} (φ : B.A ≃ₐ[K.E] C.A) : Prop :=
  (∀ y, φ (B.σ y) = C.σ (φ y)) ∧ φ B.g = C.g
namespace IsIso
variable {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A}
theorem prod {B₂ C₂ : InvAlg K} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A} (h : IsIso φ) (h₂ : IsIso φ₂) :
    IsIso (B := B.prod B₂) (C := C.prod C₂) (φ.prodCongr φ₂) :=
  ⟨fun y => Prod.ext (h.1 y.1) (h₂.1 y.2), Prod.ext h.2 h₂.2⟩
end IsIso
theorem one_sub_fixed (B : InvAlg K) {e : B.A} (he : B.σ e = e) : B.σ (1 - e) = 1 - e := by
  rw [map_sub, map_one, he]
end GlobalTheory.UnitLemma.Orbit


