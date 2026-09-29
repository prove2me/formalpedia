-- Prove2me | solution 1 for Algebra.FormallySmooth.existsUnique_algHom_apply_eq_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/97210bab-892b-58de-b90f-88db95c71880

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallySmooth_existsUnique_algHom_apply_eq_of_isNilpotent

set_option autoImplicit false

open scoped BigOperators

universe u v w

namespace FormalCoordinatesAlongSectionP1

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

section Proj

variable (e : A →ₐ[R] R)

def proj (a : A) : A := a - algebraMap R A (e a)

theorem e_proj (a : A) : e (proj e a) = 0 := by
  simp [proj]

theorem proj_mem (a : A) : proj e a ∈ RingHom.ker e :=
  (RingHom.mem_ker).mpr (e_proj e a)

theorem proj_of_eq_zero {a : A} (ha : e a = 0) : proj e a = a := by
  simp [proj, ha]

theorem self_eq_algebraMap_add_proj (a : A) : a = algebraMap R A (e a) + proj e a := by
  simp [proj]

theorem proj_add (a b : A) : proj e (a + b) = proj e a + proj e b := by
  simp only [proj, map_add]; ring

theorem proj_smul (r : R) (a : A) : proj e (r • a) = r • proj e a := by
  simp only [proj, Algebra.smul_def, map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply]; ring

theorem proj_algebraMap (r : R) : proj e (algebraMap R A r) = 0 := by
  simp [proj]

theorem proj_mul (a b : A) :
    proj e (a * b) = algebraMap R A (e a) * proj e b + algebraMap R A (e b) * proj e a +
      proj e a * proj e b := by
  simp only [proj, map_mul]; ring

end Proj

section Coord

variable {e : A →ₐ[R] R} {g : ℕ} {x : Fin g → A}

theorem exists_coeff (hx : ∀ i, e (x i) = 0)
    (hgen : RingHom.ker e ≤ Ideal.span (Set.range x) ⊔ RingHom.ker e ^ 2)
    {a : A} (ha : a ∈ RingHom.ker e) :
    ∃ c : Fin g → R, a - ∑ i, c i • x i ∈ RingHom.ker e ^ 2 := by
  obtain ⟨s, hs, q, hq, rfl⟩ := Submodule.mem_sup.mp (hgen ha)
  obtain ⟨d, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hs
  refine ⟨fun i => e (d i), ?_⟩
  have hrw : (∑ i, d i * x i + q) - ∑ i, e (d i) • x i = ∑ i, proj e (d i) * x i + q := by
    simp only [proj, Algebra.smul_def, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hrw]
  refine add_mem (sum_mem fun i _ => ?_) hq
  rw [pow_two]
  exact Ideal.mul_mem_mul (proj_mem e (d i)) ((RingHom.mem_ker).mpr (hx i))

theorem coeff_unique
    (hind : ∀ c : Fin g → R, (∑ i, c i • x i) ∈ RingHom.ker e ^ 2 → c = 0)
    {a : A} {c c' : Fin g → R}
    (hc : a - ∑ i, c i • x i ∈ RingHom.ker e ^ 2)
    (hc' : a - ∑ i, c' i • x i ∈ RingHom.ker e ^ 2) : c = c' := by
  have h : (∑ i, (c' - c) i • x i) ∈ RingHom.ker e ^ 2 := by
    have hsub := sub_mem hc hc'
    have hrw : (a - ∑ i, c i • x i) - (a - ∑ i, c' i • x i) = ∑ i, (c' - c) i • x i := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      ring
    rwa [hrw] at hsub
  have h0 := hind _ h
  have : c' - c = 0 := h0
  exact (sub_eq_zero.mp this).symm

variable (hx : ∀ i, e (x i) = 0)
  (hgen : RingHom.ker e ≤ Ideal.span (Set.range x) ⊔ RingHom.ker e ^ 2)
  (hind : ∀ c : Fin g → R, (∑ i, c i • x i) ∈ RingHom.ker e ^ 2 → c = 0)

noncomputable def coord (a : A) : Fin g → R :=
  (exists_coeff hx hgen (proj_mem e a)).choose

theorem coord_spec (a : A) :
    proj e a - ∑ i, coord hx hgen a i • x i ∈ RingHom.ker e ^ 2 :=
  (exists_coeff hx hgen (proj_mem e a)).choose_spec

include hind in
theorem coord_eq {a : A} {c : Fin g → R}
    (h : proj e a - ∑ i, c i • x i ∈ RingHom.ker e ^ 2) : coord hx hgen a = c :=
  coeff_unique hind (coord_spec hx hgen a) h

include hind in
theorem coord_add (a b : A) : coord hx hgen (a + b) = coord hx hgen a + coord hx hgen b := by
  apply coord_eq hx hgen hind
  have hrw : proj e (a + b) - ∑ i, (coord hx hgen a + coord hx hgen b) i • x i =
      (proj e a - ∑ i, coord hx hgen a i • x i) + (proj e b - ∑ i, coord hx hgen b i • x i) := by
    simp only [proj_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    ring
  rw [hrw]
  exact add_mem (coord_spec hx hgen a) (coord_spec hx hgen b)

include hind in
theorem coord_smul (r : R) (a : A) : coord hx hgen (r • a) = r • coord hx hgen a := by
  apply coord_eq hx hgen hind
  have hrw : proj e (r • a) - ∑ i, (r • coord hx hgen a) i • x i =
      r • (proj e a - ∑ i, coord hx hgen a i • x i) := by
    simp only [proj_smul, Pi.smul_apply, smul_eq_mul, mul_smul, smul_sub, Finset.smul_sum]
  rw [hrw]
  exact Submodule.smul_of_tower_mem _ r (coord_spec hx hgen a)

include hind in
theorem coord_algebraMap (r : R) : coord hx hgen (algebraMap R A r) = 0 := by
  apply coord_eq hx hgen hind
  simp [proj_algebraMap]

include hind in
theorem coord_x (j : Fin g) : coord hx hgen (x j) = Pi.single j 1 := by
  apply coord_eq hx hgen hind
  have hrw : proj e (x j) - ∑ i, (Pi.single j (1 : R) : Fin g → R) i • x i = 0 := by
    rw [proj_of_eq_zero e (hx j)]
    simp [Pi.single_apply, Finset.sum_ite_eq']
  rw [hrw]
  exact zero_mem _

include hind in

theorem coord_mul (a b : A) :
    coord hx hgen (a * b) = e a • coord hx hgen b + e b • coord hx hgen a := by
  apply coord_eq hx hgen hind
  have hrw : proj e (a * b) - ∑ i, (e a • coord hx hgen b + e b • coord hx hgen a) i • x i =
      algebraMap R A (e a) * (proj e b - ∑ i, coord hx hgen b i • x i) +
        algebraMap R A (e b) * (proj e a - ∑ i, coord hx hgen a i • x i) +
        proj e a * proj e b := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib]
    simp only [proj_mul, Algebra.smul_def, map_mul, mul_sub, Finset.mul_sum]
    ring_nf
  rw [hrw]
  refine add_mem (add_mem (Ideal.mul_mem_left _ _ (coord_spec hx hgen b))
    (Ideal.mul_mem_left _ _ (coord_spec hx hgen a))) ?_
  rw [pow_two]
  exact Ideal.mul_mem_mul (proj_mem e a) (proj_mem e b)

theorem decomp (a : A) :
    a = algebraMap R A (e a) + ∑ i, coord hx hgen a i • x i +
      (proj e a - ∑ i, coord hx hgen a i • x i) := by
  simp only [proj]; ring

end Coord

section Uniqueness

variable {e : A →ₐ[R] R} {g : ℕ} {x : Fin g → A}
  (hx : ∀ i, e (x i) = 0)
  (hgen : RingHom.ker e ≤ Ideal.span (Set.range x) ⊔ RingHom.ker e ^ 2)
  {C : Type w} [CommRing C] [Algebra R C] (J : Ideal C)
  {φ φ' : A →ₐ[R] C}
  (hφ : ∀ a : A, e a = 0 → φ a ∈ J) (hφ' : ∀ a : A, e a = 0 → φ' a ∈ J)
  (hxφ : ∀ i, φ (x i) = φ' (x i))

include hx hgen hφ hφ' hxφ in

theorem sub_mem_pow : ∀ k : ℕ, 1 ≤ k → ∀ a : A, φ a - φ' a ∈ J ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro a
    rw [pow_one, self_eq_algebraMap_add_proj e a]
    simp only [map_add, AlgHom.commutes, add_sub_add_left_eq_sub]
    exact sub_mem (hφ _ (e_proj e a)) (hφ' _ (e_proj e a))
  | succ k hk ih =>
    intro a

    have hI2 : ∀ q ∈ RingHom.ker e ^ 2, φ q - φ' q ∈ J ^ (k + 1) := by
      intro q hq
      rw [pow_two] at hq
      refine Submodule.mul_induction_on hq (fun m hm n hn => ?_) (fun y z hy hz => ?_)
      · have hrw : φ (m * n) - φ' (m * n) = φ m * (φ n - φ' n) + (φ m - φ' m) * φ' n := by
          simp only [map_mul]; ring
        rw [hrw]
        refine add_mem ?_ ?_
        · rw [pow_succ']
          exact Ideal.mul_mem_mul (hφ m ((RingHom.mem_ker).mp hm)) (ih n)
        · rw [pow_succ]
          exact Ideal.mul_mem_mul (ih m) (hφ' n ((RingHom.mem_ker).mp hn))
      · have hrw : φ (y + z) - φ' (y + z) = (φ y - φ' y) + (φ z - φ' z) := by
          simp only [map_add]; ring
        rw [hrw]
        exact add_mem hy hz

    have hdec := decomp hx hgen a
    set q := proj e a - ∑ i, coord hx hgen a i • x i with hq
    have hqmem : q ∈ RingHom.ker e ^ 2 := coord_spec hx hgen a
    have hrw : φ a - φ' a = φ q - φ' q := by
      conv_lhs => rw [hdec]
      simp only [map_add, map_sum, map_smul, AlgHom.commutes, hxφ]
      ring
    rw [hrw]
    exact hI2 q hqmem

include hx hgen hφ hφ' hxφ in
theorem eq_of_isNilpotent (hJ : IsNilpotent J) : φ = φ' := by
  obtain ⟨N, hN⟩ := hJ
  have hN1 : J ^ (N + 1) = ⊥ := by rw [pow_succ, hN, zero_mul]; rfl
  ext a
  have h := sub_mem_pow hx hgen J hφ hφ' hxφ (N + 1) (Nat.succ_le_succ (Nat.zero_le N)) a
  rw [hN1, Submodule.mem_bot] at h
  exact sub_eq_zero.mp h

end Uniqueness

section Existence

variable {e : A →ₐ[R] R} {g : ℕ} {x : Fin g → A}
  (hx : ∀ i, e (x i) = 0)
  (hgen : RingHom.ker e ≤ Ideal.span (Set.range x) ⊔ RingHom.ker e ^ 2)
  (hind : ∀ c : Fin g → R, (∑ i, c i • x i) ∈ RingHom.ker e ^ 2 → c = 0)

include hx hgen hind in

theorem exists_of_pow_eq_bot [Algebra.FormallySmooth R A] :
    ∀ k : ℕ, 1 ≤ k → ∀ (C : Type w) [CommRing C] [Algebra R C] (J : Ideal C), J ^ k = ⊥ →
      ∀ c : Fin g → C, (∀ i, c i ∈ J) →
        ∃ φ : A →ₐ[R] C, (∀ a : A, e a = 0 → φ a ∈ J) ∧ ∀ i, φ (x i) = c i := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro C _ _ J hJ c hc
    rw [pow_one] at hJ
    refine ⟨(Algebra.ofId R C).comp e, fun a ha => by simp [ha], fun i => ?_⟩
    have hci : c i = 0 := by simpa [hJ] using hc i
    simp [hx i, hci]
  | succ k hk ih =>
    intro C _ _ J hJ c hc
    have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk

    obtain ⟨φk, hφkI, hφkx⟩ := ih (C ⧸ J ^ k) (J.map (Ideal.Quotient.mk (J ^ k)))
      (by rw [← Ideal.map_pow, Ideal.map_quotient_self])
      (fun i => Ideal.Quotient.mk (J ^ k) (c i)) (fun i => Ideal.mem_map_of_mem _ (hc i))

    have hJk_le : J ^ k ≤ J := Ideal.pow_le_self hk0
    have hJJk : J * J ^ k = ⊥ := by rw [← pow_succ', hJ]
    have hJkJk : J ^ k * J ^ k = ⊥ :=
      le_bot_iff.mp ((Ideal.mul_mono_left hJk_le).trans hJJk.le)
    have hnil : IsNilpotent (J ^ k) := ⟨2, by rw [pow_two, hJkJk]; rfl⟩

    let Ψ : A →ₐ[R] C := Algebra.FormallySmooth.lift (J ^ k) hnil φk
    have hΨ : ∀ a, Ideal.Quotient.mk (J ^ k) (Ψ a) = φk a :=
      fun a => Algebra.FormallySmooth.mk_lift _ _ _ a
    have hΨI : ∀ a : A, e a = 0 → Ψ a ∈ J := by
      intro a ha
      have h := hφkI a ha
      rw [← hΨ, Ideal.mem_quotient_iff_mem_sup] at h
      simpa [sup_eq_left.mpr hJk_le] using h
    have hΨproj : ∀ a : A, Ψ a - algebraMap R C (e a) ∈ J := by
      intro a
      have h := hΨI (proj e a) (e_proj e a)
      simpa [proj, map_sub, AlgHom.commutes] using h

    let err : Fin g → C := fun i => Ψ (x i) - c i
    have herr : ∀ i, err i ∈ J ^ k := fun i =>
      Ideal.Quotient.eq_zero_iff_mem.mp (by simp only [err, map_sub, hΨ, hφkx, sub_self])

    let D : A → C := fun a => -∑ i, algebraMap R C (coord hx hgen a i) * err i
    have hD_mem : ∀ a, D a ∈ J ^ k := fun a =>
      neg_mem (sum_mem fun i _ => Ideal.mul_mem_left _ _ (herr i))
    have hD_add : ∀ a b, D (a + b) = D a + D b := by
      intro a b
      simp only [D, coord_add hx hgen hind, Pi.add_apply, map_add, add_mul,
        Finset.sum_add_distrib, neg_add]
    have hD_mul : ∀ a b, D (a * b) = algebraMap R C (e a) * D b + algebraMap R C (e b) * D a := by
      intro a b
      simp only [D, coord_mul hx hgen hind, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add,
        map_mul, add_mul, Finset.sum_add_distrib, neg_add, Finset.mul_sum, mul_assoc, mul_neg]
    have hD_algebraMap : ∀ r : R, D (algebraMap R A r) = 0 := by
      intro r
      simp only [D, coord_algebraMap hx hgen hind, Pi.zero_apply, map_zero, zero_mul,
        Finset.sum_const_zero, neg_zero]
    have hD_x : ∀ j, D (x j) = -err j := by
      intro j
      simp only [D, coord_x hx hgen hind, Pi.single_apply]
      simp [Finset.sum_ite_eq']

    have hvan1 : ∀ a b, (Ψ a - algebraMap R C (e a)) * D b = 0 := fun a b =>
      (Submodule.mem_bot C).mp (hJJk ▸ Ideal.mul_mem_mul (hΨproj a) (hD_mem b))
    have hvan2 : ∀ a b, D a * D b = 0 := fun a b =>
      (Submodule.mem_bot C).mp (hJkJk ▸ Ideal.mul_mem_mul (hD_mem a) (hD_mem b))

    let Φ : A →ₐ[R] C :=
      { toFun := fun a => Ψ a + D a
        map_one' := by
          have h1 : D 1 = 0 := by simpa using hD_algebraMap 1
          simp [h1]
        map_mul' := by
          intro a b
          simp only [map_mul, hD_mul]
          linear_combination -(hvan1 a b) - hvan1 b a - hvan2 a b
        map_zero' := by
          have h0 : D 0 = 0 := by simpa using hD_algebraMap 0
          simp [h0]
        map_add' := by
          intro a b
          simp only [map_add, hD_add]; ring
        commutes' := by
          intro r
          simp only [AlgHom.commutes, hD_algebraMap, add_zero] }
    refine ⟨Φ, fun a ha => add_mem (hΨI a ha) (hJk_le (hD_mem a)), fun j => ?_⟩
    show Ψ (x j) + D (x j) = c j
    rw [hD_x]
    simp [err]

include hx hgen hind in
theorem exists_of_isNilpotent [Algebra.FormallySmooth R A]
    {C : Type w} [CommRing C] [Algebra R C] (J : Ideal C) (hJ : IsNilpotent J)
    (c : Fin g → C) (hc : ∀ i, c i ∈ J) :
    ∃ φ : A →ₐ[R] C, (∀ a : A, e a = 0 → φ a ∈ J) ∧ ∀ i, φ (x i) = c i := by
  obtain ⟨N, hN⟩ := hJ
  have hN1 : J ^ (N + 1) = ⊥ := by rw [pow_succ, hN, zero_mul]; rfl
  exact exists_of_pow_eq_bot hx hgen hind (N + 1) (Nat.succ_le_succ (Nat.zero_le N)) C J hN1 c hc

end Existence

end FormalCoordinatesAlongSectionP1

open FormalCoordinatesAlongSectionP1 in
theorem solution
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FormallySmooth R A]
    (e : A →ₐ[R] R) {g : ℕ} (x : Fin g → A) (hx : ∀ i, e (x i) = 0)
    (hgen : RingHom.ker e ≤ Ideal.span (Set.range x) ⊔ RingHom.ker e ^ 2)
    (hind : ∀ c : Fin g → R, (∑ i, c i • x i) ∈ RingHom.ker e ^ 2 → c = 0)
    {C : Type w} [CommRing C] [Algebra R C] (J : Ideal C) (hJ : IsNilpotent J)
    (c : Fin g → C) (hc : ∀ i, c i ∈ J) :
    ∃! φ : A →ₐ[R] C, (∀ a : A, e a = 0 → φ a ∈ J) ∧ ∀ i, φ (x i) = c i := by
  obtain ⟨φ, hφI, hφx⟩ := exists_of_isNilpotent hx hgen hind J hJ c hc
  refine ⟨φ, ⟨hφI, hφx⟩, fun φ' hφ' => ?_⟩
  exact (eq_of_isNilpotent hx hgen J hφI hφ'.1 (fun i => (hφx i).trans (hφ'.2 i).symm) hJ).symm

end S_Algebra_FormallySmooth_existsUnique_algHom_apply_eq_of_isNilpotent
end P2MW
export P2MW.S_Algebra_FormallySmooth_existsUnique_algHom_apply_eq_of_isNilpotent (solution)
