-- Prove2me | solution 1 for Algebra.exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/401c0796-0108-567c-9c7b-dd9e4a9f10ea

import Mathlib
import Theorems.Thm_eq_one_of_isNilpotent_sub_one_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast

set_option autoImplicit false

universe u

namespace P2M
namespace PatchMu

open Localization

theorem isNilpotent_of_forall_algHom_eq_zero (A₀ : Type u) [CommRing A₀] {R : Type u} [CommRing R] [Algebra A₀ R] (x : R)
    (hx : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (ψ : R →ₐ[A₀] Ω), ψ x = 0) :
    IsNilpotent x := by
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  haveI : IsDomain (R ⧸ J) := Ideal.Quotient.isDomain J
  let Ω : Type u := AlgebraicClosure (FractionRing (R ⧸ J))
  let ψ₀ : R →+* Ω :=
    (algebraMap (FractionRing (R ⧸ J)) Ω).comp ((algebraMap (R ⧸ J) (FractionRing (R ⧸ J))).comp (Ideal.Quotient.mk J))
  letI : Algebra A₀ Ω := (ψ₀.comp (algebraMap A₀ R)).toAlgebra
  haveI : DecidableEq Ω := Classical.decEq Ω
  let ψ : R →ₐ[A₀] Ω :=
    { toRingHom := ψ₀
      commutes' := fun _ => rfl }
  have h0 : ψ x = 0 := hx Ω ψ
  have h1 : (algebraMap (FractionRing (R ⧸ J)) Ω) ((algebraMap (R ⧸ J) (FractionRing (R ⧸ J))) (Ideal.Quotient.mk J x)) = 0 := h0
  rw [map_eq_zero, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ J) (FractionRing (R ⧸ J)))] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1

theorem eq_of_pow_eq_one_of_forall_algHom_eq (A₀ : Type u) [CommRing A₀] {R : Type u} [CommRing R] [Algebra A₀ R]
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit ((n : ℕ) : R)) (α β : R) (hα : α ^ n = 1) (hβ : β ^ n = 1)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (ψ : R →ₐ[A₀] Ω), ψ α = ψ β) :
    α = β := by
  set η : R := α * β ^ (n - 1) with hη
  have hβn : β ^ (n - 1) * β = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0), hβ]
  have hηn : η ^ n = 1 := by
    rw [hη, mul_pow, ← pow_mul, hα, one_mul, mul_comm, pow_mul, hβ, one_pow]
  have hnil : IsNilpotent (η - 1) := by
    refine isNilpotent_of_forall_algHom_eq_zero A₀ (η - 1) fun Ω _ _ _ _ ψ => ?_
    have hψβn : ψ β ^ n = 1 := by rw [← map_pow, hβ, map_one]
    have : ψ η = 1 := by
      rw [hη, map_mul, map_pow, h Ω ψ, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0), hψβn]
    rw [map_sub, this, map_one, sub_self]
  have hη1 : η = 1 := eq_one_of_isNilpotent_sub_one_of_pow_eq_one hnil hn hηn
  calc α = α * (β ^ (n - 1) * β) := by rw [hβn, mul_one]
    _ = η * β := by rw [hη, mul_assoc]
    _ = β := by rw [hη1, one_mul]

section Local

variable {A₀ : Type u} [CommRing A₀] {B : Type u} [CommRing B] [Algebra A₀ B]

noncomputable def algHomOfComp {Ω : Type u} [Field Ω] [Algebra A₀ Ω] (f : B) (ψ : Localization.Away f →+* Ω)
    (hψ : ∀ a : A₀, ψ (algebraMap A₀ (Localization.Away f) a) = algebraMap A₀ Ω a) : Localization.Away f →ₐ[A₀] Ω :=
  { toRingHom := ψ
    commutes' := hψ }

@[scoped simp]
theorem algHomOfComp_apply {Ω : Type u} [Field Ω] [Algebra A₀ Ω] (f : B) (ψ : Localization.Away f →+* Ω)
    (hψ : ∀ a : A₀, ψ (algebraMap A₀ (Localization.Away f) a) = algebraMap A₀ Ω a) (z : Localization.Away f) :
    algHomOfComp f ψ hψ z = ψ z := rfl

def Good (n : ℕ) (v : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω], (B →ₐ[A₀] Ω) → Ω) (f : B) : Prop :=
  ∃ ε : Localization.Away f, ε ^ n = 1 ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (φ : Localization.Away f →ₐ[A₀] Ω),
      v Ω (φ.comp (IsScalarTower.toAlgHom A₀ B (Localization.Away f))) = φ ε

end Local

end P2M.PatchMu
p2m_reactivate "P2MW.S_Algebra_exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast.P2M P2MW.S_Algebra_exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast.P2M.PatchMu"
p2m_reactivate "P2MW.S_Algebra_exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast.P2M"

open P2M.PatchMu Localization in
theorem solution
    (A₀ : Type u) [CommRing A₀] (B : Type u) [CommRing B] [Algebra A₀ B] (n : ℕ) (hn : IsUnit ((n : ℕ) : B))
    (v : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω], (B →ₐ[A₀] Ω) → Ω)
    (hloc : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], ∃ f : B, f ∉ 𝔭 ∧ ∃ ε : Localization.Away f, ε ^ n = 1 ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (φ : Localization.Away f →ₐ[A₀] Ω),
        v Ω (φ.comp (IsScalarTower.toAlgHom A₀ B (Localization.Away f))) = φ ε) :
    ∃ ε : B, ε ^ n = 1 ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (φ : B →ₐ[A₀] Ω), v Ω φ = φ ε := by

  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have h01 : (0 : B) = 1 := by
      have h := hn
      rw [Nat.cast_zero, isUnit_zero_iff] at h
      exact h
    refine ⟨0, by rw [pow_zero], ?_⟩
    intro Ω _ _ _ _ φ
    exact absurd (by rw [← map_one φ, ← h01, map_zero]) (one_ne_zero (α := Ω)).symm
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hnpos

  let S : Set B := {f | Good n v f}
  have hspan : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (Ideal.span S) hne
    haveI : 𝔪.IsPrime := h𝔪.isPrime
    obtain ⟨f, hf𝔪, hgood⟩ := hloc 𝔪
    exact hf𝔪 (hle (Ideal.subset_span (show f ∈ S from hgood)))

  choose ε hεn hε using fun a : S => (show Good n v a.1 from a.2)

  have hcompat : ∀ a b : S,
      IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b : B)) a.1 (b : B) (ε a) =
        IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b : B)) b.1 (a : B) (ε b) := by
    intro a b
    let P : Type u := Localization.Away (a * b : B)
    let jR : Localization.Away (a : B) →+* P := IsLocalization.Away.awayToAwayRight (P := P) a.1 (b : B)
    let jL : Localization.Away (b : B) →+* P := IsLocalization.Away.awayToAwayLeft (P := P) b.1 (a : B)
    have hnP : IsUnit ((n : ℕ) : P) := by
      have h := hn.map (algebraMap B P)
      rwa [map_natCast] at h
    refine eq_of_pow_eq_one_of_forall_algHom_eq A₀ hn0 hnP (jR (ε a)) (jL (ε b))
      (by rw [← map_pow, hεn, map_one]) (by rw [← map_pow, hεn, map_one]) ?_
    intro Ω _ _ _ _ ψ

    have hRa : ∀ r : A₀, (ψ.toRingHom.comp jR) (algebraMap A₀ (Localization.Away (a : B)) r) = algebraMap A₀ Ω r := by
      intro r
      rw [IsScalarTower.algebraMap_apply A₀ B (Localization.Away (a : B)), RingHom.comp_apply,
        IsLocalization.Away.awayToAwayRight_eq, ← IsScalarTower.algebraMap_apply]
      exact ψ.commutes r
    have hLb : ∀ r : A₀, (ψ.toRingHom.comp jL) (algebraMap A₀ (Localization.Away (b : B)) r) = algebraMap A₀ Ω r := by
      intro r
      rw [IsScalarTower.algebraMap_apply A₀ B (Localization.Away (b : B)), RingHom.comp_apply,
        IsLocalization.Away.awayToAwayLeft_eq, ← IsScalarTower.algebraMap_apply]
      exact ψ.commutes r
    let ψa : Localization.Away (a : B) →ₐ[A₀] Ω := algHomOfComp (a : B) (ψ.toRingHom.comp jR) hRa
    let ψb : Localization.Away (b : B) →ₐ[A₀] Ω := algHomOfComp (b : B) (ψ.toRingHom.comp jL) hLb
    have ha : ψa.comp (IsScalarTower.toAlgHom A₀ B (Localization.Away (a : B))) =
        ψ.comp (IsScalarTower.toAlgHom A₀ B P) := by
      apply AlgHom.ext
      intro x
      show ψ (jR (algebraMap B (Localization.Away (a : B)) x)) = ψ (algebraMap B P x)
      rw [IsLocalization.Away.awayToAwayRight_eq]
    have hb : ψb.comp (IsScalarTower.toAlgHom A₀ B (Localization.Away (b : B))) =
        ψ.comp (IsScalarTower.toAlgHom A₀ B P) := by
      apply AlgHom.ext
      intro x
      show ψ (jL (algebraMap B (Localization.Away (b : B)) x)) = ψ (algebraMap B P x)
      rw [IsLocalization.Away.awayToAwayLeft_eq]
    have h1 := hε a Ω ψa
    have h2 := hε b Ω ψb
    rw [ha] at h1
    rw [hb] at h2
    show ψa (ε a) = ψb (ε b)
    rw [← h1, ← h2]

  obtain ⟨r, hr, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top S hspan ε hcompat
  refine ⟨r, ?_, ?_⟩
  ·
    apply Localization.algebraMap_injective_of_span_eq_top S hspan
    funext a
    rw [Pi.algebraMap_apply, Pi.algebraMap_apply, map_pow, map_one, hr a, hεn]
  ·
    intro Ω _ _ _ _ φ

    obtain ⟨a, ha⟩ : ∃ a : S, φ (a : B) ≠ 0 := by
      by_contra hall
      push_neg at hall
      have hle : Ideal.span S ≤ RingHom.ker φ.toRingHom := by
        rw [Ideal.span_le]
        intro f hf
        exact hall ⟨f, hf⟩
      rw [hspan, top_le_iff] at hle
      have h1 : φ 1 = 0 := (RingHom.mem_ker).mp (hle ▸ Submodule.mem_top : (1 : B) ∈ RingHom.ker φ.toRingHom)
      exact one_ne_zero ((map_one φ).symm.trans h1)

    have hunit : IsUnit (φ.toRingHom (a : B)) := (Ne.isUnit ha)
    let φa₀ : Localization.Away (a : B) →+* Ω := IsLocalization.Away.lift (a : B) hunit
    have hφa : ∀ t : A₀, φa₀ (algebraMap A₀ (Localization.Away (a : B)) t) = algebraMap A₀ Ω t := by
      intro t
      rw [IsScalarTower.algebraMap_apply A₀ B (Localization.Away (a : B))]
      show IsLocalization.Away.lift (a : B) hunit (algebraMap B _ (algebraMap A₀ B t)) = _
      rw [IsLocalization.Away.lift_eq]
      exact φ.commutes t
    let φa : Localization.Away (a : B) →ₐ[A₀] Ω := algHomOfComp (a : B) φa₀ hφa
    have hfac : φa.comp (IsScalarTower.toAlgHom A₀ B (Localization.Away (a : B))) = φ := by
      apply AlgHom.ext
      intro x
      show IsLocalization.Away.lift (a : B) hunit (algebraMap B _ x) = φ x
      rw [IsLocalization.Away.lift_eq]
      rfl
    have key := hε a Ω φa
    rw [hfac] at key
    rw [key, ← hr a]
    show IsLocalization.Away.lift (a : B) hunit (algebraMap B _ r) = φ r
    rw [IsLocalization.Away.lift_eq]
    rfl

end S_Algebra_exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast
end P2MW
export P2MW.S_Algebra_exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast (solution)
