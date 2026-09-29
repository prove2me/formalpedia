-- Prove2me | solution 1 for AddCommGroup.exists_fg_saturation_of_isHomogeneous_degree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5d8ee7c5-5234-52ae-bdc3-a7be39f9b6d7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_exists_fg_saturation_of_isHomogeneous_degree

set_option autoImplicit false

namespace P2mEndDisc

open MvPolynomial Module

theorem eval_smul_of_isHomogeneous {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℚ} {D : ℕ}
    (hP : P.IsHomogeneous D) (k : ℚ) (v : σ → ℚ) :
    eval (k • v) P = k ^ D * eval v P := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = D := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_apply]
    exact (hP.degree_eq_sum_deg_support hd).symm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem eval_zero_of_isHomogeneous {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℚ} {D : ℕ}
    (hP : P.IsHomogeneous D) (hD : D ≠ 0) : eval (0 : σ → ℚ) P = 0 := by
  have h := eval_smul_of_isHomogeneous hP 0 0
  rw [zero_smul, zero_pow hD, zero_mul] at h
  exact h

section Setting

variable {R : Type*} [AddCommGroup R] (deg : R → ℤ) (D : ℕ)
  (hpoly : ∀ (m : ℕ) (α : Fin m → R), ∃ P : MvPolynomial (Fin m) ℚ, P.IsHomogeneous D ∧
    ∀ n : Fin m → ℤ, (deg (∑ i, n i • α i) : ℚ) = MvPolynomial.eval (fun i => (n i : ℚ)) P)

include hpoly in

theorem deg_smul (x : R) (k : ℤ) : (deg (k • x) : ℚ) = (k : ℚ) ^ D * deg x := by
  obtain ⟨P, hP, hev⟩ := hpoly 1 (fun _ => x)
  have h1 := hev (fun _ => k)
  have h2 := hev (fun _ => 1)
  simp only [Fin.sum_univ_one, one_smul] at h1 h2
  rw [h1, h2]
  have : (fun _ : Fin 1 => ((k : ℤ) : ℚ)) = (k : ℚ) • (fun _ : Fin 1 => ((1 : ℤ) : ℚ)) := by
    funext i; simp
  rw [this, eval_smul_of_isHomogeneous hP]

include hpoly in
theorem deg_zero (hD : D ≠ 0) : deg 0 = 0 := by
  have h := deg_smul deg D hpoly (0 : R) 0
  rw [zero_smul, Int.cast_zero, zero_pow hD, zero_mul] at h
  exact_mod_cast h

include hpoly in

theorem isAddTorsionFree (hD : D ≠ 0) (hsep : ∀ x : R, x ≠ 0 → deg x ≠ 0) :
    IsAddTorsionFree R := by
  refine ⟨fun n hn x y hxy => ?_⟩
  simp only at hxy
  have h0 : (n : ℤ) • (x - y) = 0 := by
    rw [natCast_zsmul, smul_sub, hxy, sub_self]
  by_contra hne
  have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
  have h1 := deg_smul deg D hpoly (x - y) n
  rw [h0, deg_zero deg D hpoly hD, Int.cast_zero] at h1
  have h2 : ((n : ℤ) : ℚ) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn)
  have h3 : (deg (x - y) : ℚ) = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd h h2
    · exact h
  exact hsep _ hne' (by exact_mod_cast h3)

end Setting

section Saturation

variable {R : Type*} [AddCommGroup R]

def sat (M : AddSubgroup R) : AddSubgroup R where
  carrier := {x | ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro x y ⟨k, hk, hkx⟩ ⟨k', hk', hk'y⟩
    refine ⟨k * k', mul_ne_zero hk hk', ?_⟩
    rw [smul_add, mul_comm k k', mul_smul, mul_smul]
    exact M.add_mem (M.zsmul_mem hkx _) (by rw [← mul_smul, mul_comm, mul_smul]; exact M.zsmul_mem hk'y _)
  neg_mem' := by
    rintro x ⟨k, hk, hkx⟩
    exact ⟨k, hk, by rw [smul_neg]; exact M.neg_mem hkx⟩

theorem mem_sat {M : AddSubgroup R} {x : R} : x ∈ sat M ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M :=
  Iff.rfl

theorem le_sat (M : AddSubgroup R) : M ≤ sat M := fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩

end Saturation

section Coordinates

variable {R : Type*} [AddCommGroup R]
variable {M : AddSubgroup R} {r : ℕ} (b : Basis (Fin r) ℤ M)

noncomputable def icoord (y : M) : Fin r → ℚ := fun i => ((b.repr y) i : ℚ)

theorem icoord_add (y z : M) : icoord b (y + z) = icoord b y + icoord b z := by
  funext i; simp [icoord]

theorem icoord_zsmul (k : ℤ) (y : M) : icoord b (k • y) = (k : ℚ) • icoord b y := by
  funext i; simp [icoord]

theorem icoord_eq_zero_iff (y : M) : icoord b y = 0 ↔ y = 0 := by
  constructor
  · intro h
    have : b.repr y = 0 := by
      ext i
      have := congrFun h i
      simp only [icoord, Pi.zero_apply, Int.cast_eq_zero] at this
      simpa using this
    simpa using this
  · rintro rfl; funext i; simp [icoord]

noncomputable def coord (x : sat M) : Fin r → ℚ :=
  ((x.2.choose : ℤ) : ℚ)⁻¹ • icoord b ⟨x.2.choose • (x : R), x.2.choose_spec.2⟩

private theorem smul_mk_eq (k k' : ℤ) (x : R) (hk : k • x ∈ M) (hk' : k' • x ∈ M) :
    k' • (⟨k • x, hk⟩ : M) = k • (⟨k' • x, hk'⟩ : M) := by
  apply Subtype.ext
  change k' • (k • x) = k • (k' • x)
  rw [smul_comm]

theorem coord_eq (x : sat M) (k : ℤ) (hk : k ≠ 0) (hkx : k • (x : R) ∈ M) :
    coord b x = ((k : ℤ) : ℚ)⁻¹ • icoord b ⟨k • (x : R), hkx⟩ := by
  set k₀ : ℤ := x.2.choose with hk₀def
  have hk₀ : k₀ ≠ 0 := x.2.choose_spec.1
  have hk₀x : k₀ • (x : R) ∈ M := x.2.choose_spec.2
  change ((k₀ : ℤ) : ℚ)⁻¹ • icoord b ⟨k₀ • (x : R), hk₀x⟩ = _
  have key : (k : ℚ) • icoord b ⟨k₀ • (x : R), hk₀x⟩ = (k₀ : ℚ) • icoord b ⟨k • (x : R), hkx⟩ := by
    rw [← icoord_zsmul, ← icoord_zsmul, smul_mk_eq]
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hk₀q : (k₀ : ℚ) ≠ 0 := by exact_mod_cast hk₀
  rw [inv_smul_eq_iff₀ hk₀q, smul_comm, ← key, smul_smul, inv_mul_cancel₀ hkq, one_smul]

theorem coord_of_mem (x : sat M) (hx : (x : R) ∈ M) : coord b x = icoord b ⟨x, hx⟩ := by
  rw [coord_eq b x 1 one_ne_zero (by simpa using hx)]
  simp

theorem coord_smul_eq (x : sat M) (k : ℤ) (hk : k ≠ 0) (hkx : k • (x : R) ∈ M) :
    (k : ℚ) • coord b x = icoord b ⟨k • (x : R), hkx⟩ := by
  rw [coord_eq b x k hk hkx, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hk), one_smul]

noncomputable def coordHom : sat M →+ (Fin r → ℚ) where
  toFun := coord b
  map_zero' := by
    rw [coord_of_mem b 0 (by simp)]
    exact (icoord_eq_zero_iff b _).mpr (by simp)
  map_add' x y := by
    obtain ⟨k, hk, hkx⟩ := x.2
    obtain ⟨k', hk', hk'y⟩ := y.2
    have hkk : k * k' ≠ 0 := mul_ne_zero hk hk'
    have h1 : (k * k') • (x : R) ∈ M := by rw [mul_comm, mul_smul]; exact M.zsmul_mem hkx _
    have h2 : (k * k') • (y : R) ∈ M := by rw [mul_smul]; exact M.zsmul_mem hk'y _
    have h3 : (k * k') • ((x + y : sat M) : R) ∈ M := by
      rw [AddSubgroup.coe_add, smul_add]; exact M.add_mem h1 h2
    have hq : ((k * k' : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hkk
    apply smul_right_injective (Fin r → ℚ) hq
    simp only [smul_add]
    rw [coord_smul_eq b _ _ hkk h3, coord_smul_eq b _ _ hkk h1, coord_smul_eq b _ _ hkk h2,
      ← icoord_add]
    congr 1
    apply Subtype.ext
    simp [smul_add]

theorem coordHom_apply (x : sat M) : coordHom b x = coord b x := rfl

theorem coordHom_injective [IsAddTorsionFree R] : Function.Injective (coordHom b) := by
  intro x y hxy
  have h : coordHom b (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨k, hk, hkz⟩ := (x - y).2
  rw [coordHom_apply] at h
  have h2 := coord_smul_eq b (x - y) k hk hkz
  rw [h, smul_zero] at h2
  have h3 := (icoord_eq_zero_iff b _).mp h2.symm
  have h4 : k • ((x - y : sat M) : R) = 0 := congrArg Subtype.val h3
  have h5 : ((x - y : sat M) : R) = 0 := (IsAddTorsionFree.zsmul_eq_zero_iff_right hk).mp h4
  have h6 : x - y = 0 := Subtype.ext h5
  exact sub_eq_zero.mp h6

end Coordinates

section DegreeFormula

variable {R : Type*} [AddCommGroup R] (deg : R → ℤ) (D : ℕ)
  (hpoly : ∀ (m : ℕ) (α : Fin m → R), ∃ P : MvPolynomial (Fin m) ℚ, P.IsHomogeneous D ∧
    ∀ n : Fin m → ℤ, (deg (∑ i, n i • α i) : ℚ) = MvPolynomial.eval (fun i => (n i : ℚ)) P)
variable {M : AddSubgroup R} {r : ℕ} (b : Basis (Fin r) ℤ M)

theorem coe_eq_sum (y : M) : (y : R) = ∑ i, (b.repr y) i • ((b i : M) : R) := by
  conv_lhs => rw [← b.sum_repr y]
  rw [AddSubgroup.val_finsetSum]
  simp

include hpoly in

theorem deg_eq_eval (P : MvPolynomial (Fin r) ℚ) (hP : P.IsHomogeneous D)
    (hev : ∀ n : Fin r → ℤ,
      (deg (∑ i, n i • ((b i : M) : R)) : ℚ) = MvPolynomial.eval (fun i => (n i : ℚ)) P)
    (x : sat M) : (deg (x : R) : ℚ) = MvPolynomial.eval (coord b x) P := by
  obtain ⟨k, hk, hkx⟩ := x.2

  have hsum : k • (x : R) = ∑ i, (b.repr ⟨k • (x : R), hkx⟩) i • ((b i : M) : R) :=
    coe_eq_sum b ⟨k • (x : R), hkx⟩
  have h1 : (deg (k • (x : R)) : ℚ) = MvPolynomial.eval (icoord b ⟨k • (x : R), hkx⟩) P := by
    have h := hev (fun i => (b.repr ⟨k • (x : R), hkx⟩) i)
    rw [← hsum] at h
    exact h
  rw [deg_smul deg D hpoly, ← coord_smul_eq b x k hk hkx, eval_smul_of_isHomogeneous hP] at h1
  have hkq : ((k : ℤ) : ℚ) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast hk)
  exact mul_left_cancel₀ hkq h1

end DegreeFormula

section Discrete

theorem discreteTopology_of_separator {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] (L : AddSubgroup E) (P : E → ℝ)
    (hP : Continuous P) (hP0 : P 0 = 0) (hsep : ∀ s ∈ L, s ≠ 0 → 1 ≤ |P s|) :
    DiscreteTopology L := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hopen : IsOpen {x : E | |P x| < 1} :=
    isOpen_lt (continuous_abs.comp hP) continuous_const
  have hopenL : IsOpen {x : L | |P (x : E)| < 1} := hopen.preimage continuous_subtype_val
  have hset : {x : L | |P (x : E)| < 1} = ({0} : Set L) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hne
      have hne' : (x : E) ≠ 0 := fun h => hne (Subtype.ext h)
      exact absurd hx (not_lt.mpr (hsep x x.2 hne'))
    · intro hx
      rw [hx, ZeroMemClass.coe_zero, hP0, abs_zero]
      exact one_pos
  exact hset ▸ hopenL

variable {r : ℕ}

def castVec : (Fin r → ℚ) →+ (Fin r → ℝ) where
  toFun v i := (v i : ℝ)
  map_zero' := by funext i; simp
  map_add' a c := by funext i; simp

theorem castVec_apply (v : Fin r → ℚ) (i : Fin r) : castVec v i = (v i : ℝ) := rfl

theorem castVec_injective : Function.Injective (castVec (r := r)) := by
  intro a c h; funext i
  have := congrFun h i
  simp only [castVec_apply, Rat.cast_inj] at this
  exact this

theorem eval_castVec (P : MvPolynomial (Fin r) ℚ) (v : Fin r → ℚ) :
    MvPolynomial.eval (castVec v) (MvPolynomial.map (Rat.castHom ℝ) P) =
      ((MvPolynomial.eval v P : ℚ) : ℝ) := by
  rw [MvPolynomial.eval_map, ← Rat.coe_castHom, MvPolynomial.eval₂_comp]
  rfl

end Discrete

section Main

variable {R : Type*} [AddCommGroup R]

theorem main (deg : R → ℤ) (D : ℕ) (hD : D ≠ 0)
    (hpoly : ∀ (m : ℕ) (α : Fin m → R), ∃ P : MvPolynomial (Fin m) ℚ, P.IsHomogeneous D ∧
      ∀ n : Fin m → ℤ, (deg (∑ i, n i • α i) : ℚ) = MvPolynomial.eval (fun i => (n i : ℚ)) P)
    (hsep : ∀ x : R, x ≠ 0 → deg x ≠ 0)
    (M : AddSubgroup R) (hM : M.FG) :
    ∃ M' : AddSubgroup R, M'.FG ∧ ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M := by
  haveI : IsAddTorsionFree R := isAddTorsionFree deg D hpoly hD hsep
  refine ⟨sat M, ?_, fun x => mem_sat⟩

  haveI : Module.Finite ℤ M :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg M).mpr hM)
  haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  set r := finrank ℤ M
  let b : Basis (Fin r) ℤ M := Module.finBasis ℤ M

  obtain ⟨P, hP, hev⟩ := hpoly r (fun i => ((b i : M) : R))

  let cR : sat M →+ (Fin r → ℝ) := castVec.comp (coordHom b)
  have hcR_inj : Function.Injective cR := castVec_injective.comp (coordHom_injective b)
  have hcR_eval : ∀ x : sat M,
      MvPolynomial.eval (cR x) (MvPolynomial.map (Rat.castHom ℝ) P) = (deg (x : R) : ℝ) := by
    intro x
    change MvPolynomial.eval (castVec (coordHom b x)) _ = _
    rw [eval_castVec, coordHom_apply, ← deg_eq_eval deg D hpoly b P hP hev x]
    exact_mod_cast rfl
  let L : Submodule ℤ (Fin r → ℝ) := LinearMap.range cR.toIntLinearMap

  haveI : DiscreteTopology L := by
    refine discreteTopology_of_separator L.toAddSubgroup
      (fun s => MvPolynomial.eval s (MvPolynomial.map (Rat.castHom ℝ) P))
      (MvPolynomial.continuous_eval _) ?_ ?_
    · have h := hcR_eval 0
      rw [map_zero] at h
      change MvPolynomial.eval 0 (MvPolynomial.map (Rat.castHom ℝ) P) = 0
      rw [h]
      have : ((0 : sat M) : R) = 0 := rfl
      rw [this, deg_zero deg D hpoly hD, Int.cast_zero]
    · rintro s ⟨x, rfl⟩ hne
      have hne' : cR x ≠ 0 := hne
      have hx : (x : R) ≠ 0 := by
        intro h0
        apply hne'
        have : x = 0 := Subtype.ext h0
        rw [this, map_zero]
      change 1 ≤ |MvPolynomial.eval (cR x) (MvPolynomial.map (Rat.castHom ℝ) P)|
      rw [hcR_eval]
      have h1 : (1 : ℤ) ≤ |deg (x : R)| := Int.one_le_abs (hsep _ hx)
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|deg (x : R)| : ℤ) : ℝ) := by exact_mod_cast h1
      simpa using h2

  haveI : Module.Finite ℤ L := inferInstance

  haveI : Module.Finite ℤ (sat M) :=
    Module.Finite.of_injective cR.toIntLinearMap.rangeRestrict
      (fun a c h => hcR_inj (congrArg Subtype.val h))
  exact (AddGroup.fg_iff_addSubgroup_fg _).mp (Module.Finite.iff_addGroup_fg.mp inferInstance)

end Main

end P2mEndDisc

theorem solution
    {R : Type*} [AddCommGroup R] (deg : R → ℤ) (D : ℕ) (hD : D ≠ 0)
    (hpoly : ∀ (m : ℕ) (α : Fin m → R), ∃ P : MvPolynomial (Fin m) ℚ, P.IsHomogeneous D ∧
      ∀ n : Fin m → ℤ, (deg (∑ i, n i • α i) : ℚ) = MvPolynomial.eval (fun i => (n i : ℚ)) P)
    (hsep : ∀ x : R, x ≠ 0 → deg x ≠ 0)
    (M : AddSubgroup R) (hM : M.FG) :
    ∃ M' : AddSubgroup R, M'.FG ∧ ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M :=
  P2mEndDisc.main deg D hD hpoly hsep M hM

end S_AddCommGroup_exists_fg_saturation_of_isHomogeneous_degree
end P2MW
export P2MW.S_AddCommGroup_exists_fg_saturation_of_isHomogeneous_degree (solution)
