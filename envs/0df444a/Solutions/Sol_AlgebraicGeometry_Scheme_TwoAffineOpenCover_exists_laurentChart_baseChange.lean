-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/25001354-6ce2-5d8c-a87f-d0e1306725b2

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange

set_option autoImplicit false

universe u

open HahnSeries
open scoped TensorProduct

p2m_attr_erase "instance" "HahnSeries.powerSeriesAlgebra"

namespace ChartBC

variable {R : Type u} {A : Type u} [CommRing R] [CommRing A]

theorem map_toNonUnitalRingHom (τ : R →+* A) (x : LaurentSeries R) : x.map τ.toNonUnitalRingHom = x.map τ := by
  ext g; simp only [HahnSeries.map_coeff]; rfl

theorem map_toAddMonoidHom (τ : R →+* A) (x : LaurentSeries R) : x.map τ.toAddMonoidHom = x.map τ := by
  ext g; simp only [HahnSeries.map_coeff]; rfl

noncomputable def mapRingHom (τ : R →+* A) : LaurentSeries R →+* LaurentSeries A where
  toFun x := x.map τ
  map_one' := by
    rw [show (1 : LaurentSeries R) = C (1 : R) from (map_one C).symm, HahnSeries.map_C, map_one, map_one]
  map_mul' x y := by
    rw [← map_toNonUnitalRingHom, HahnSeries.map_mul, map_toNonUnitalRingHom, map_toNonUnitalRingHom]
  map_zero' := by
    ext g; simp [HahnSeries.map_coeff]
  map_add' x y := by
    rw [← map_toAddMonoidHom, HahnSeries.map_add, map_toAddMonoidHom, map_toAddMonoidHom]

@[scoped simp] theorem mapRingHom_apply (τ : R →+* A) (x : LaurentSeries R) : mapRingHom τ x = x.map τ := rfl

variable [Algebra R A] {B : Type u} [CommRing B] [Algebra R B]

theorem algebraMap_laurentSeries_eq_C (a : A) : algebraMap A (LaurentSeries A) a = C a := by rfl

theorem algebraMap_R_laurentSeries_eq_C (r : R) : algebraMap R (LaurentSeries A) r = C (algebraMap R A r) := by rfl

noncomputable def expandMapAlgHom (φ : B →+* LaurentSeries R) (hφ : ∀ r : R, φ (algebraMap R B r) = C r) : B →ₐ[R] LaurentSeries A :=
  { (mapRingHom (algebraMap R A)).comp φ with
    commutes' := fun r => by
      change ((φ (algebraMap R B r)).map (algebraMap R A)) = algebraMap R (LaurentSeries A) r
      rw [hφ, HahnSeries.map_C, algebraMap_R_laurentSeries_eq_C] }

noncomputable def expandTensor (φ : B →+* LaurentSeries R) (hφ : ∀ r : R, φ (algebraMap R B r) = C r) :
    A ⊗[R] B →ₐ[A] LaurentSeries A :=
  Algebra.TensorProduct.lift (Algebra.ofId A (LaurentSeries A)) (expandMapAlgHom φ hφ) (fun _ _ => Commute.all _ _)

theorem expandTensor_tmul (φ : B →+* LaurentSeries R) (hφ : ∀ r : R, φ (algebraMap R B r) = C r) (a : A) (b : B) :
    expandTensor φ hφ (a ⊗ₜ[R] b) = C a * (φ b).map (algebraMap R A) := by
  rw [expandTensor, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, algebraMap_laurentSeries_eq_C]
  rfl

end ChartBC
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange.ChartBC"

namespace ChartBC

open HahnSeries AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u'

theorem map_single_ringHom {R A : Type u'} [CommRing R] [CommRing A] (τ : R →+* A) (a : ℤ) (r : R) :
    (single a r : LaurentSeries R).map τ = single a (τ r) := by
  ext n
  rw [HahnSeries.map_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs
  · rfl
  · exact map_zero τ

theorem map_mem_range_ofPowerSeries {R A : Type u'} [CommRing R] [CommRing A] (τ : R →+* A)
    {x : LaurentSeries R} (hx : x ∈ (ofPowerSeries ℤ R).range) : x.map τ ∈ (ofPowerSeries ℤ A).range := by
  obtain ⟨p, rfl⟩ := hx
  refine ⟨p.map τ, ?_⟩
  ext n
  rw [HahnSeries.map_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [HahnSeries.ofPowerSeries_apply, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range,
      HahnSeries.embDomain_notin_range, map_zero]
    · rintro ⟨m, hm⟩; simp at hm; omega
    · rintro ⟨m, hm⟩; simp at hm; omega
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A]

theorem baseChange_map0_apply (s : (𝒱.cover c).A0) :
    (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map0 s =
      ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app 𝒱.U0).hom s := by
  rw [Scheme.TwoAffineOpenCover.HomOver.map0_apply, Scheme.Hom.app_eq_appLE]
  rfl

theorem baseChange_map1_apply (s : (𝒱.cover c).A1) :
    (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map1 s =
      ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app 𝒱.U1).hom s := by
  rw [Scheme.TwoAffineOpenCover.HomOver.map1_apply, Scheme.Hom.app_eq_appLE]
  rfl

set_option maxHeartbeats 4000000 in
theorem main (Λ : (𝒱.cover c).LaurentChart) :
    ∃ ΛA : ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).LaurentChart,
      (∀ y : (𝒱.cover c).A01,
        ΛA.expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 y) = (Λ.expand y).map (algebraMap R A)) ∧
      (∀ Λ' : ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).LaurentChart,
        (∀ y : (𝒱.cover c).A01,
          Λ'.expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 y) = (Λ.expand y).map (algebraMap R A)) →
        Λ' = ΛA) ∧
      (Λ.IsRegular (𝒱.cover c).ρ0 →
        ΛA.IsRegular ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ0) ∧
      (Λ.IsRegular (𝒱.cover c).ρ1 →
        ΛA.IsRegular ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ1) ∧
      (Λ.HasParameter (𝒱.cover c).ρ0 →
        ΛA.HasParameter ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ0) ∧
      (Λ.HasParameter (𝒱.cover c).ρ1 →
        ΛA.HasParameter ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ1) := by
  classical
  obtain ⟨e0, e1, e01, -, -, he0, he1, he01, -, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf 𝒱 c A

  have he0' : ∀ s, e0 ((1 : A) ⊗ₜ[R] s) = (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map0 s := fun s => by rw [he0, baseChange_map0_apply]
  have he1' : ∀ s, e1 ((1 : A) ⊗ₜ[R] s) = (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map1 s := fun s => by rw [he1, baseChange_map1_apply]
  have he01' : ∀ s, e01 ((1 : A) ⊗ₜ[R] s) = (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 s := fun s => by
    rw [he01, Scheme.TwoAffineOpenCover.baseChange_map01_apply]
  have htmul : ∀ (a : A) (s : (𝒱.cover c).A01), e01 (a ⊗ₜ[R] s) = algebraMap A ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01 a * (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 s := fun a s => by
    rw [show a ⊗ₜ[R] s = a • ((1 : A) ⊗ₜ[R] s) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, he01', Algebra.smul_def]
  have htmul0 : ∀ (a : A) (s : (𝒱.cover c).A0), e0 (a ⊗ₜ[R] s) = algebraMap A ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A0 a * (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map0 s := fun a s => by
    rw [show a ⊗ₜ[R] s = a • ((1 : A) ⊗ₜ[R] s) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, he0', Algebra.smul_def]
  have htmul1 : ∀ (a : A) (s : (𝒱.cover c).A1), e1 (a ⊗ₜ[R] s) = algebraMap A ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A1 a * (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map1 s := fun a s => by
    rw [show a ⊗ₜ[R] s = a • ((1 : A) ⊗ₜ[R] s) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, he1', Algebra.smul_def]

  let T : A ⊗[R] (𝒱.cover c).A01 →ₐ[A] LaurentSeries A := expandTensor Λ.expand Λ.expand_algebraMap
  let expandA : ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01 →+* LaurentSeries A := T.toRingHom.comp e01.symm.toAlgHom.toRingHom
  have hexpandA : ∀ x, expandA x = T (e01.symm x) := fun x => rfl
  have hexpandA_e01 : ∀ z, expandA (e01 z) = T z := fun z => by rw [hexpandA, AlgEquiv.symm_apply_apply]
  have hT : ∀ (a : A) (s : (𝒱.cover c).A01), T (a ⊗ₜ[R] s) = C a * (Λ.expand s).map (algebraMap R A) := fun a s =>
    expandTensor_tmul Λ.expand Λ.expand_algebraMap a s
  have hΛA_alg : ∀ a : A, expandA (algebraMap A ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01 a) = C a := fun a => by
    rw [hexpandA, AlgEquiv.commutes, AlgHom.commutes, algebraMap_laurentSeries_eq_C]
  let ΛA : ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).LaurentChart := ⟨expandA, hΛA_alg⟩
  have hΛA : ∀ y : (𝒱.cover c).A01, ΛA.expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 y) = (Λ.expand y).map (algebraMap R A) := fun y => by
    change expandA ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 y) = _
    rw [← he01', hexpandA_e01, hT, map_one, one_mul]

  have hprod : ∀ (a : A) (s : (𝒱.cover c).A01), expandA (algebraMap A ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01 a * (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 s) = C a * (Λ.expand s).map (algebraMap R A) :=
    fun a s => by rw [map_mul, hΛA_alg]; exact congrArg _ (hΛA s)
  refine ⟨ΛA, hΛA, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro Λ' hΛ'
    have hprod' : ∀ (a : A) (s : (𝒱.cover c).A01), Λ'.expand (algebraMap A ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01 a * (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 s) = C a * (Λ.expand s).map (algebraMap R A) :=
      fun a s => by rw [map_mul, Λ'.expand_algebraMap, hΛ']
    have hext : Λ'.expand = expandA := by
      refine RingHom.ext fun x => ?_
      obtain ⟨z, rfl⟩ := e01.surjective x
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero]
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
      | tmul a s => rw [htmul, hprod, hprod']
    obtain ⟨exp', h'⟩ := Λ'
    change exp' = expandA at hext
    subst hext
    rfl
  ·
    intro h b
    change expandA (((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ0 b) ∈ _
    obtain ⟨z, rfl⟩ := e0.surjective b
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add, map_add, map_add]; exact add_mem hx hy
    | tmul a s =>
      rw [htmul0, map_mul, AlgHom.commutes, ← Scheme.TwoAffineOpenCover.HomOver.map01_ρ0, hprod]
      exact mul_mem ⟨PowerSeries.C a, by rw [HahnSeries.ofPowerSeries_C]⟩ (map_mem_range_ofPowerSeries (algebraMap R A) (h s))
  ·
    intro h b
    change expandA (((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ1 b) ∈ _
    obtain ⟨z, rfl⟩ := e1.surjective b
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add, map_add, map_add]; exact add_mem hx hy
    | tmul a s =>
      rw [htmul1, map_mul, AlgHom.commutes, ← Scheme.TwoAffineOpenCover.HomOver.map01_ρ1, hprod]
      exact mul_mem ⟨PowerSeries.C a, by rw [HahnSeries.ofPowerSeries_C]⟩ (map_mem_range_ofPowerSeries (algebraMap R A) (h s))
  ·
    rintro ⟨b, hb⟩
    refine ⟨(Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map0 b, ?_⟩
    change expandA (((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ0 ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map0 b)) = _
    rw [← Scheme.TwoAffineOpenCover.HomOver.map01_ρ0]
    change ΛA.expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 ((𝒱.cover c).ρ0 b)) = _
    rw [hΛA, hb, map_single_ringHom, map_one]
  ·
    rintro ⟨b, hb⟩
    refine ⟨(Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map1 b, ?_⟩
    change expandA (((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ1 ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map1 b)) = _
    rw [← Scheme.TwoAffineOpenCover.HomOver.map01_ρ1]
    change ΛA.expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 ((𝒱.cover c).ρ1 b)) = _
    rw [hΛA, hb, map_single_ringHom, map_one]

end ChartBC
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange.ChartBC"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (Λ : (𝒱.cover c).LaurentChart) :
    ∃ ΛA : ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).LaurentChart,
      (∀ y : (𝒱.cover c).A01,
        ΛA.expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 y) = (Λ.expand y).map (algebraMap R A)) ∧
      (∀ Λ' : ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).LaurentChart,
        (∀ y : (𝒱.cover c).A01,
          Λ'.expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 y) = (Λ.expand y).map (algebraMap R A)) →
        Λ' = ΛA) ∧
      (Λ.IsRegular (𝒱.cover c).ρ0 →
        ΛA.IsRegular ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ0) ∧
      (Λ.IsRegular (𝒱.cover c).ρ1 →
        ΛA.IsRegular ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ1) ∧
      (Λ.HasParameter (𝒱.cover c).ρ0 →
        ΛA.HasParameter ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ0) ∧
      (Λ.HasParameter (𝒱.cover c).ρ1 →
        ΛA.HasParameter ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ1) :=
  ChartBC.main 𝒱 c A Λ

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange (solution)
