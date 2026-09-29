-- Prove2me | solution 1 for AlgebraicCurve.RROpens.exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3697f57c-56b8-5193-8e02-8233d94ff59c

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RROpens_exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue

set_option autoImplicit false

universe u v

open AlgebraicCurve IsLocalRing

namespace InterpSol

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem hasValue_zero (v : Place K F) : v.HasValue (0 : F) 0 :=
  ⟨zero_mem _, by rw [map_zero]; exact (map_zero _)⟩

theorem hasValue_add {v : Place K F} {f g : F} {a b : K} (hf : v.HasValue f a) (hg : v.HasValue g b) :
    v.HasValue (f + g) (a + b) := by
  obtain ⟨hfm, hfr⟩ := hf
  obtain ⟨hgm, hgr⟩ := hg
  refine ⟨add_mem hfm hgm, ?_⟩
  have : (⟨f + g, add_mem hfm hgm⟩ : v.toValuationSubring) = ⟨f, hfm⟩ + ⟨g, hgm⟩ := rfl
  rw [this, map_add, hfr, hgr, map_add]

theorem hasValue_const_mul {v : Place K F} {f : F} {a : K} (hf : v.HasValue f a) (c : K) :
    v.HasValue (algebraMap K F c * f) (c * a) :=
  (v.hasValue_algebraMap c).mul hf

theorem hasValue_sum {ι : Type*} (v : Place K F) (s : Finset ι) (f : ι → F) (a : ι → K)
    (h : ∀ i ∈ s, v.HasValue (f i) (a i)) : v.HasValue (∑ i ∈ s, f i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasValue_zero v
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact hasValue_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem hasValue_zero_of_one_le_ord (v : Place K F) {f : F} (hf : f ≠ 0) (h : 1 ≤ v.ord f) : v.HasValue f 0 := by
  have hmem : f ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hf (by omega)
  refine ⟨hmem, ?_⟩
  rw [map_zero, residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h0 := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at h0
  have h0' : v.ord f = 0 := h0
  omega

theorem exists_hasValue_ne_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    ∃ a : K, a ≠ 0 ∧ v.HasValue f a := by
  obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf h
  obtain ⟨a, ha, hne⟩ := v.exists_hasValue_of_surjective hv hm
  exact ⟨a, hne hu, ha⟩

theorem isRational_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem ord_ge_of_mem_lSpace {D : Divisor K F} {f : F} (hf : f ∈ LSpace D) (hf0 : f ≠ 0) (v : Place K F) :
    -D v ≤ v.ord f := by
  rcases mem_lSpace_iff_ord.mp hf with h | h
  · exact absurd h hf0
  · exact h v

theorem ne_zero_of_notMem {D : Divisor K F} {f : F} (hf : f ∉ LSpace D) : f ≠ 0 := by
  rintro rfl; exact hf (LSpace D).zero_mem

theorem ord_eq_of_mem_of_notMem [DecidableEq (Place K F)] {D : Divisor K F} {P : Place K F} {f : F}
    (hf : f ∈ LSpace D) (hf' : f ∉ LSpace (D - Finsupp.single P 1)) : P.ord f = -D P := by
  have hf0 : f ≠ 0 := ne_zero_of_notMem hf'
  have hge := ord_ge_of_mem_lSpace hf hf0
  rw [mem_lSpace_iff_ord, not_or, not_forall] at hf'
  obtain ⟨-, v, hv⟩ := hf'
  rw [not_le, Finsupp.sub_apply, Finsupp.single_apply] at hv
  by_cases hPv : P = v
  · subst hPv
    rw [if_pos rfl] at hv
    have := hge P
    omega
  · rw [if_neg hPv, sub_zero] at hv
    exact absurd (hge v) (not_le.mpr hv)

end InterpSol

open InterpSol

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (D : Divisor K F)
    (Z : Finset (Place K F)) (hZ : ∀ z ∈ Z, D z = 0) (c : Place K F → K)
    (P₀ : Place K F) (hP₀Z : P₀ ∉ Z) (hP₀D : D P₀ = 0)
    (x : F) (hx : P₀.ord x = 1) (m : ℕ) (c₀ : K)
    (hdeg : 2 * (g : ℤ) + m + Z.card ≤ Divisor.degree D) :
    ∃ f : F, f ∈ riemannRochSpace (D - Finsupp.single P₀ (m : ℤ)) ∧
      P₀.HasValue (f * x ^ (-(m : ℤ))) c₀ ∧ ∀ z ∈ Z, z.HasValue f (c z) := by
  classical

  have hrat : ∀ v : Place K F, v.IsRational := isRational_of_isAlgClosed
  have hdeg1 : ∀ v : Place K F, (v.deg : ℤ) = 1 := fun v => by
    rw [Place.deg_eq_one_of_isRational (hrat v)]; rfl
  have hdegs : ∀ (v : Place K F) (n : ℤ), Divisor.degree (Finsupp.single v n) = n := fun v n => by
    rw [Divisor.degree_single, hdeg1, mul_one]
  have hKc : Divisor.degree Kc = 2 * (g : ℤ) - 2 := by
    have h0 := hRR 0
    have h1 := hRR Kc
    rw [sub_zero, map_zero] at h0
    rw [sub_self] at h1
    omega

  have hell : ∀ D' : Divisor K F, 2 * (g : ℤ) - 1 ≤ Divisor.degree D' → (ell D' : ℤ) = Divisor.degree D' + 1 - g := by
    intro D' hD'
    have hneg : Divisor.degree (Kc - D') < 0 := by rw [map_sub, hKc]; omega
    have h0 : ell (Kc - D') = 0 := AlgebraicCurve.ell_eq_zero_of_degree_neg hneg
    have := hRR D'
    rw [h0] at this
    push_cast at this
    omega

  have hstep : ∀ (D' : Divisor K F) (P : Place K F), 2 * (g : ℤ) ≤ Divisor.degree D' →
      ∃ f : F, f ∈ LSpace D' ∧ f ∉ LSpace (D' - Finsupp.single P 1) := by
    intro D' P hD'
    have h1 : (ell D' : ℤ) = Divisor.degree D' + 1 - g := hell D' (by omega)
    have h2 : (ell (D' - Finsupp.single P 1) : ℤ) = Divisor.degree D' - 1 + 1 - g := by
      have := hell (D' - Finsupp.single P 1) (by rw [map_sub, hdegs]; omega)
      rw [this, map_sub, hdegs]
    have hle : LSpace (D' - Finsupp.single P 1) ≤ LSpace D' := by
      apply lSpace_mono
      intro v
      rw [Finsupp.sub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    have hne : LSpace (D' - Finsupp.single P 1) ≠ LSpace D' := by
      intro heq
      have : ell (D' - Finsupp.single P 1) = ell D' := by
        show Module.finrank K (LSpace (D' - Finsupp.single P 1)) = Module.finrank K (LSpace D')
        rw [heq]
      omega
    obtain ⟨f, hf, hf'⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
    exact ⟨f, hf, hf'⟩

  set SZ : Divisor K F := ∑ z ∈ Z, Finsupp.single z (1 : ℤ) with hSZ
  have hSZ_apply : ∀ v, SZ v = if v ∈ Z then 1 else 0 := by
    intro v
    rw [hSZ, Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq' Z v (fun _ => (1 : ℤ))]
  have hSZ_deg : Divisor.degree SZ = Z.card := by
    rw [hSZ, map_sum]
    simp only [hdegs]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  set D₁ : Divisor K F := D - Finsupp.single P₀ (m : ℤ) - SZ with hD₁
  have hD₁deg : 2 * (g : ℤ) ≤ Divisor.degree D₁ := by
    rw [hD₁, map_sub, map_sub, hdegs, hSZ_deg]; omega
  have hD₁P₀ : D₁ P₀ = -(m : ℤ) := by
    rw [hD₁, Finsupp.sub_apply, Finsupp.sub_apply, hP₀D, Finsupp.single_apply, if_pos rfl, hSZ_apply, if_neg hP₀Z]
    ring
  have hD₁z : ∀ z ∈ Z, D₁ z = -1 := by
    intro z hz
    have hzP : P₀ ≠ z := fun h => hP₀Z (h ▸ hz)
    rw [hD₁, Finsupp.sub_apply, Finsupp.sub_apply, hZ z hz, Finsupp.single_apply, if_neg hzP, hSZ_apply, if_pos hz]
    ring

  obtain ⟨f₀, hf₀mem, hf₀not⟩ := hstep D₁ P₀ hD₁deg
  have hf₀0 : f₀ ≠ 0 := ne_zero_of_notMem hf₀not
  have hordf₀ : P₀.ord f₀ = m := by rw [ord_eq_of_mem_of_notMem hf₀mem hf₀not, hD₁P₀, neg_neg]
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [P₀.ord_zero] at hx; exact zero_ne_one hx
  have hxm0 : x ^ (-(m : ℤ)) ≠ 0 := zpow_ne_zero _ hx0
  have hordxm : P₀.ord (x ^ (-(m : ℤ))) = -(m : ℤ) := by rw [P₀.ord_zpow, hx, mul_one]
  have hy₀ : P₀.ord (f₀ * x ^ (-(m : ℤ))) = 0 := by
    rw [P₀.ord_mul hf₀0 hxm0, hordf₀, hordxm]; ring
  obtain ⟨a₀, ha₀0, ha₀⟩ := exists_hasValue_ne_zero P₀ (hrat P₀) (mul_ne_zero hf₀0 hxm0) hy₀
  set f₁ : F := algebraMap K F (c₀ * a₀⁻¹) * f₀ with hf₁
  have hf₁mem : f₁ ∈ LSpace D₁ := (LSpace D₁).smul_mem (c₀ * a₀⁻¹) hf₀mem |> fun h => by
    rw [hf₁, ← Algebra.smul_def]; exact h
  have hf₁lead : P₀.HasValue (f₁ * x ^ (-(m : ℤ))) c₀ := by
    have h := hasValue_const_mul ha₀ (c₀ * a₀⁻¹)
    rw [mul_assoc, inv_mul_cancel₀ ha₀0, mul_one] at h
    rw [hf₁, mul_assoc]
    exact h
  have hf₁Z : ∀ z ∈ Z, z.HasValue f₁ 0 := by
    intro z hz
    have h0 : z.HasValue f₀ 0 :=
      hasValue_zero_of_one_le_ord z hf₀0 (by have := ord_ge_of_mem_lSpace hf₀mem hf₀0 z; rw [hD₁z z hz] at this; omega)
    have h := hasValue_const_mul h0 (c₀ * a₀⁻¹)
    rw [mul_zero] at h
    rw [hf₁]; exact h

  have hcorr : ∀ z : Place K F, ∃ (h : F) (b : K), z ∈ Z →
      (h ∈ LSpace (D - Finsupp.single P₀ (m : ℤ)) ∧ b ≠ 0 ∧ z.HasValue h b ∧
        (∀ z' ∈ Z, z' ≠ z → z'.HasValue h 0) ∧ P₀.HasValue (h * x ^ (-(m : ℤ))) 0) := by
    intro z
    by_cases hz : z ∈ Z
    · have hzP : P₀ ≠ z := fun h => hP₀Z (h ▸ hz)
      set SZ' : Divisor K F := ∑ z' ∈ Z.erase z, Finsupp.single z' (1 : ℤ) with hSZ'
      have hSZ'_apply : ∀ v, SZ' v = if v ∈ Z.erase z then 1 else 0 := by
        intro v
        rw [hSZ', Finsupp.finsetSum_apply]
        simp only [Finsupp.single_apply]
        rw [Finset.sum_ite_eq' (Z.erase z) v (fun _ => (1 : ℤ))]
      have hSZ'_deg : Divisor.degree SZ' = (Z.erase z).card := by
        rw [hSZ', map_sum]
        simp only [hdegs]
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      set D₂ : Divisor K F := D - Finsupp.single P₀ ((m : ℤ) + 1) - SZ' with hD₂
      have hcard : ((Z.erase z).card : ℤ) = Z.card - 1 := by
        rw [Finset.card_erase_of_mem hz]
        have : 1 ≤ Z.card := Finset.card_pos.mpr ⟨z, hz⟩
        omega
      have hD₂deg : 2 * (g : ℤ) ≤ Divisor.degree D₂ := by
        rw [hD₂, map_sub, map_sub, hdegs, hSZ'_deg, hcard]; omega
      have hD₂z : D₂ z = 0 := by
        rw [hD₂, Finsupp.sub_apply, Finsupp.sub_apply, hZ z hz, Finsupp.single_apply, if_neg hzP, hSZ'_apply,
          if_neg (Finset.notMem_erase z Z)]
        ring
      have hD₂z' : ∀ z' ∈ Z, z' ≠ z → D₂ z' = -1 := by
        intro z' hz' hne
        have hzP' : P₀ ≠ z' := fun h => hP₀Z (h ▸ hz')
        rw [hD₂, Finsupp.sub_apply, Finsupp.sub_apply, hZ z' hz', Finsupp.single_apply, if_neg hzP', hSZ'_apply,
          if_pos (Finset.mem_erase.mpr ⟨hne, hz'⟩)]
        ring
      have hD₂P₀ : D₂ P₀ = -((m : ℤ) + 1) := by
        rw [hD₂, Finsupp.sub_apply, Finsupp.sub_apply, hP₀D, Finsupp.single_apply, if_pos rfl, hSZ'_apply, if_neg]
        · ring
        · intro h; exact hP₀Z (Finset.mem_of_mem_erase h)
      obtain ⟨h, hhmem, hhnot⟩ := hstep D₂ z hD₂deg
      have hh0 : h ≠ 0 := ne_zero_of_notMem hhnot
      have hordz : z.ord h = 0 := by rw [ord_eq_of_mem_of_notMem hhmem hhnot, hD₂z, neg_zero]
      obtain ⟨b, hb0, hb⟩ := exists_hasValue_ne_zero z (hrat z) hh0 hordz
      have hle : LSpace D₂ ≤ LSpace (D - Finsupp.single P₀ (m : ℤ)) := by
        apply lSpace_mono
        intro v
        rw [hD₂, Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.sub_apply, hSZ'_apply, Finsupp.single_apply,
          Finsupp.single_apply]
        split_ifs <;> omega
      refine ⟨h, b, fun _ => ⟨hle hhmem, hb0, hb, ?_, ?_⟩⟩
      · intro z' hz' hne
        exact hasValue_zero_of_one_le_ord z' hh0
          (by have := ord_ge_of_mem_lSpace hhmem hh0 z'; rw [hD₂z' z' hz' hne] at this; omega)
      · apply hasValue_zero_of_one_le_ord P₀ (mul_ne_zero hh0 hxm0)
        rw [P₀.ord_mul hh0 hxm0, hordxm]
        have := ord_ge_of_mem_lSpace hhmem hh0 P₀
        rw [hD₂P₀] at this
        omega
    · exact ⟨0, 0, fun h => absurd h hz⟩
  choose hz bz hspec using hcorr

  have hD₁le : LSpace D₁ ≤ LSpace (D - Finsupp.single P₀ (m : ℤ)) := by
    apply lSpace_mono
    intro v
    rw [hD₁, Finsupp.sub_apply, hSZ_apply]
    split_ifs <;> omega
  refine ⟨f₁ + ∑ z ∈ Z, algebraMap K F (c z * (bz z)⁻¹) * hz z, ?_, ?_, ?_⟩
  ·
    refine (LSpace _).add_mem (hD₁le hf₁mem) ((LSpace _).sum_mem fun z hzZ => ?_)
    rw [← Algebra.smul_def]
    exact (LSpace _).smul_mem _ (hspec z hzZ).1
  ·
    have hsum : P₀.HasValue ((∑ z ∈ Z, algebraMap K F (c z * (bz z)⁻¹) * hz z) * x ^ (-(m : ℤ)))
        (∑ z ∈ Z, c z * (bz z)⁻¹ * 0) := by
      rw [Finset.sum_mul]
      refine hasValue_sum P₀ Z _ _ fun z hzZ => ?_
      rw [mul_assoc]
      exact hasValue_const_mul (hspec z hzZ).2.2.2.2 _
    have h := hasValue_add hf₁lead hsum
    rw [add_mul]
    simpa using h
  ·
    intro z hzZ
    have hsum : z.HasValue (∑ z' ∈ Z, algebraMap K F (c z' * (bz z')⁻¹) * hz z')
        (∑ z' ∈ Z, c z' * (bz z')⁻¹ * (if z' = z then bz z else 0)) := by
      refine hasValue_sum z Z _ _ fun z' hz'Z => hasValue_const_mul ?_ _
      split_ifs with hzz
      · subst hzz; exact (hspec z' hz'Z).2.2.1
      · exact (hspec z' hz'Z).2.2.2.1 z hzZ (Ne.symm hzz)
    have h := hasValue_add (hf₁Z z hzZ) hsum
    have hval : (0 : K) + ∑ z' ∈ Z, c z' * (bz z')⁻¹ * (if z' = z then bz z else 0) = c z := by
      rw [zero_add]
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Z z, if_pos hzZ, mul_assoc, inv_mul_cancel₀ (hspec z hzZ).2.1, mul_one]
    rw [hval] at h
    exact h

end S_AlgebraicCurve_RROpens_exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue
end P2MW
export P2MW.S_AlgebraicCurve_RROpens_exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue (solution)
