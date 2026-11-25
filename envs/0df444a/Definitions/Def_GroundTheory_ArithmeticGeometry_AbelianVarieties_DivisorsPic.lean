-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsPic
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsPic
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:32.30294+00:00
-- url     : https://prove2.me/theorems/ca7c0e39-154b-4b97-a039-583ce4950fd4
-- title:
--   Divisors Pic
-- statement:
--   Definitions and structural lemmas for Divisors Pic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsPic.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Theorems.Thm_GroundTheory_Arith_Abelian_affinePointEquiv_apply_asIdeal
import Theorems.Thm_GroundTheory_Arith_Abelian_finite_support_count
import Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_norm_eq_finsum_count
import Theorems.Thm_GroundTheory_Arith_Abelian_ordAtIdeal_algebraMap
import Theorems.Thm_GroundTheory_Arith_Abelian_ordAtIdeal_mul
import Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_algebraMap
import Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_mul
import Theorems.Thm_GroundTheory_Arith_Abelian_ordPoint_mul
import Theorems.Thm_GroundTheory_Arith_Abelian_ordPoint_some
import Theorems.Thm_GroundTheory_Arith_Abelian_spanSingleton_ne_zero
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some


set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
section Divisor
abbrev CurveDivisor : Type u := W.toAffine.Point →₀ ℤ
noncomputable def divisorDegree : CurveDivisor W →+ ℤ :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ
noncomputable def divisorSum : CurveDivisor W →+ W.toAffine.Point :=
  Finsupp.liftAddHom fun P => zmultiplesHom W.toAffine.Point P
omit [DecidableEq F] in
@[simp]
theorem divisorDegree_single (P : W.toAffine.Point) (n : ℤ) :
    divisorDegree W (Finsupp.single P n) = n := by
  simp [divisorDegree]
@[simp]
theorem divisorSum_single (P : W.toAffine.Point) (n : ℤ) :
    divisorSum W (Finsupp.single P n) = n • P := by
  simp [divisorSum]
end Divisor
section AlgClosed
variable [IsAlgClosed F] [W.IsElliptic]
noncomputable def pointOfIdeal (v : HeightOneSpectrum W.toAffine.CoordinateRing) :
    W.toAffine.Point :=
  .some _ _ ((affinePointEquiv W).symm v).2
omit [DecidableEq F] in
theorem pointOfIdeal_affinePointEquiv (p : {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2}) :
    pointOfIdeal W (affinePointEquiv W p) = .some _ _ p.2 := by
  simp only [pointOfIdeal, Equiv.symm_apply_apply]
omit [DecidableEq F] in
theorem pointOfIdeal_heightOneOfNonsingular {x y : F} (h : W.toAffine.Nonsingular x y) :
    pointOfIdeal W (heightOneOfNonsingular h) = .some x y h :=
  pointOfIdeal_affinePointEquiv W ⟨(x, y), h⟩
omit [DecidableEq F] in
theorem pointOfIdeal_injective : Function.Injective (pointOfIdeal W) := by
  intro v w h
  simp only [pointOfIdeal, Point.some.injEq] at h
  exact (affinePointEquiv W).symm.injective (Subtype.ext (Prod.ext h.1 h.2))
omit [DecidableEq F] in
theorem pointOfIdeal_ne_zero (v : HeightOneSpectrum W.toAffine.CoordinateRing) :
    pointOfIdeal W v ≠ 0 :=
  Point.some_ne_zero _
omit [DecidableEq F] in
theorem exists_pointOfIdeal_eq {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ v, pointOfIdeal W v = P := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact ⟨_, pointOfIdeal_heightOneOfNonsingular W h⟩
noncomputable def affinePart (D : CurveDivisor W) :
    HeightOneSpectrum W.toAffine.CoordinateRing →₀ ℤ :=
  Finsupp.comapDomain (pointOfIdeal W) D (pointOfIdeal_injective W).injOn
omit [DecidableEq F] in
theorem affinePart_apply (D : CurveDivisor W) (v : HeightOneSpectrum W.toAffine.CoordinateRing) :
    affinePart W D v = D (pointOfIdeal W v) :=
  Finsupp.comapDomain_apply _ _ _ _
theorem eq_mapDomain_affinePart_add (D : CurveDivisor W) :
    D = Finsupp.mapDomain (pointOfIdeal W) (affinePart W D) + Finsupp.single 0 (D 0) := by
  ext P
  rw [Finsupp.add_apply]
  rcases eq_or_ne P 0 with rfl | hP
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (fun ⟨v, hv⟩ => pointOfIdeal_ne_zero W v hv),
      Finsupp.single_eq_same, zero_add]
  · obtain ⟨v, rfl⟩ := exists_pointOfIdeal_eq W hP
    rw [Finsupp.mapDomain_apply (pointOfIdeal_injective W), affinePart_apply, Finsupp.single_apply,
      if_neg (pointOfIdeal_ne_zero W v).symm, add_zero]
theorem divisorDegree_eq (D : CurveDivisor W) :
    divisorDegree W D = (affinePart W D).sum (fun _ n => n) + D 0 := by
  conv_lhs => rw [eq_mapDomain_affinePart_add W D]
  rw [map_add, divisorDegree_single, divisorDegree, Finsupp.liftAddHom_apply,
    Finsupp.sum_mapDomain_index_addMonoidHom]
  rfl
theorem divisorSum_eq (D : CurveDivisor W) :
    divisorSum W D = (affinePart W D).sum (fun v n => n • pointOfIdeal W v) := by
  conv_lhs => rw [eq_mapDomain_affinePart_add W D]
  rw [map_add, divisorSum_single, smul_zero, add_zero, divisorSum, Finsupp.liftAddHom_apply,
    Finsupp.sum_mapDomain_index_addMonoidHom]
  simp
noncomputable def unitOfIdeal (v : HeightOneSpectrum W.toAffine.CoordinateRing) :
    (FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField)
    (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
noncomputable def idealOfExps (D : HeightOneSpectrum W.toAffine.CoordinateRing →₀ ℤ) :
    (FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField)ˣ :=
  D.prod fun v n => unitOfIdeal W v ^ n
omit [DecidableEq F] in
theorem val_idealOfExps (D : HeightOneSpectrum W.toAffine.CoordinateRing →₀ ℤ) :
    ((idealOfExps W D : (FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField)ˣ) :
      FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) =
      D.prod (fun v n => (v.asIdeal :
        FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) ^ n) := by
  rw [idealOfExps, Finsupp.prod, Units.coe_prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Units.val_zpow_eq_zpow_val, unitOfIdeal, Units.val_mk0]
omit [DecidableEq F] in
theorem count_idealOfExps (D : HeightOneSpectrum W.toAffine.CoordinateRing →₀ ℤ)
    (v : HeightOneSpectrum W.toAffine.CoordinateRing) :
    FractionalIdeal.count W.toAffine.FunctionField v (idealOfExps W D :
      FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) = D v := by
  rw [val_idealOfExps]
  exact FractionalIdeal.count_finsuppProd _ v D
theorem toClass_pointOfIdeal (v : HeightOneSpectrum W.toAffine.CoordinateRing) :
    Point.toClass (W := W.toAffine) (pointOfIdeal W v) =
      Additive.ofMul (ClassGroup.mk W.toAffine.FunctionField (unitOfIdeal W v)) := by
  have hu : CoordinateRing.XYIdeal' (W := W.toAffine) ((affinePointEquiv W).symm v).2 =
      unitOfIdeal W v := by
    refine Units.ext ?_
    rw [CoordinateRing.XYIdeal'_eq, unitOfIdeal, Units.val_mk0, ← affinePointEquiv_apply_asIdeal,
      Equiv.apply_symm_apply]
  rw [pointOfIdeal, Point.toClass_some, hu]
  rfl
theorem toClass_sum (D : HeightOneSpectrum W.toAffine.CoordinateRing →₀ ℤ) :
    Point.toClass (W := W.toAffine) (D.sum fun v n => n • pointOfIdeal W v) =
      Additive.ofMul (ClassGroup.mk W.toAffine.FunctionField (idealOfExps W D)) := by
  rw [Finsupp.sum, map_sum, idealOfExps, Finsupp.prod, map_prod, ofMul_prod]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_zsmul, toClass_pointOfIdeal, map_zpow, ofMul_zpow]
omit [DecidableEq F] in

theorem fractionalIdeal_eq_of_count_eq
    {I J : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField} (hI : I ≠ 0)
    (hJ : J ≠ 0) (h : ∀ v, FractionalIdeal.count W.toAffine.FunctionField v I =
      FractionalIdeal.count W.toAffine.FunctionField v J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' W.toAffine.FunctionField hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' W.toAffine.FunctionField hJ]
  simp_rw [h]
omit [DecidableEq F] in
theorem classGroup_mk_eq_one_iff
    (I : (FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField)ˣ) :
    ClassGroup.mk W.toAffine.FunctionField I = 1 ↔
      ∃ f : W.toAffine.FunctionField, f ≠ 0 ∧
        (I : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) =
          FractionalIdeal.spanSingleton _ f := by
  rw [ClassGroup.mk_eq_one_iff]
  constructor
  · rintro ⟨f, hf⟩
    have hI : (I : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) =
        FractionalIdeal.spanSingleton _ f := by
      rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_spanSingleton]
      exact hf
    refine ⟨f, ?_, hI⟩
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hI
    exact I.ne_zero hI
  · rintro ⟨f, -, hf⟩
    refine ⟨f, ?_⟩
    rw [hf, FractionalIdeal.coe_spanSingleton]
noncomputable def affineDivisorOf (f : W.toAffine.FunctionField) :
    HeightOneSpectrum W.toAffine.CoordinateRing →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => ordAtIdeal W v f) (finite_support_count W _)
omit [DecidableEq F] in
theorem affineDivisorOf_apply (f : W.toAffine.FunctionField)
    (v : HeightOneSpectrum W.toAffine.CoordinateRing) :
    affineDivisorOf W f v = ordAtIdeal W v f := rfl
noncomputable def divisorOf (f : W.toAffine.FunctionField) : CurveDivisor W :=
  Finsupp.mapDomain (pointOfIdeal W) (affineDivisorOf W f) + Finsupp.single 0 (ordInfty W f)
theorem divisorOf_pointOfIdeal (f : W.toAffine.FunctionField)
    (v : HeightOneSpectrum W.toAffine.CoordinateRing) :
    divisorOf W f (pointOfIdeal W v) = ordAtIdeal W v f := by
  rw [divisorOf, Finsupp.add_apply, Finsupp.mapDomain_apply (pointOfIdeal_injective W),
    Finsupp.single_apply, if_neg (pointOfIdeal_ne_zero W v).symm, add_zero, affineDivisorOf_apply]
omit [DecidableEq F] in
theorem divisorOf_zero_apply (f : W.toAffine.FunctionField) :
    divisorOf W f 0 = ordInfty W f := by
  rw [divisorOf, Finsupp.add_apply,
    Finsupp.mapDomain_of_notMem_range _ _ (fun ⟨v, hv⟩ => pointOfIdeal_ne_zero W v hv),
    Finsupp.single_eq_same, zero_add]
theorem divisorOf_apply (f : W.toAffine.FunctionField) (P : W.toAffine.Point) :
    divisorOf W f P = ordPoint W P f := by
  cases P with
  | zero => exact divisorOf_zero_apply W f
  | some x y h =>
    rw [ordPoint_some, ← pointOfIdeal_heightOneOfNonsingular W h, divisorOf_pointOfIdeal]
theorem affinePart_divisorOf (f : W.toAffine.FunctionField) :
    affinePart W (divisorOf W f) = affineDivisorOf W f := by
  ext v
  rw [affinePart_apply, divisorOf_pointOfIdeal, affineDivisorOf_apply]
theorem divisorOf_mul {f g : W.toAffine.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisorOf W (f * g) = divisorOf W f + divisorOf W g := by
  ext P
  rw [Finsupp.add_apply, divisorOf_apply, divisorOf_apply, divisorOf_apply, ordPoint_mul W P hf hg]
theorem divisorOf_one : divisorOf W 1 = 0 := by
  have h := divisorOf_mul W (one_ne_zero (α := W.toAffine.FunctionField)) one_ne_zero
  rw [mul_one] at h
  exact (add_eq_left.mp h.symm)
omit [DecidableEq F] in
theorem sum_affineDivisorOf (f : W.toAffine.FunctionField) :
    (affineDivisorOf W f).sum (fun _ n => n) = ∑ᶠ v, ordAtIdeal W v f := by
  rw [finsum_eq_sum_of_support_subset _ (s := (affineDivisorOf W f).support)
    (by rw [← Finsupp.fun_support_eq]; rfl), Finsupp.sum]
  rfl
omit [DecidableEq F] in
theorem finite_support_ordAtIdeal (f : W.toAffine.FunctionField) :
    (Function.support fun v => ordAtIdeal W v f).Finite :=
  finite_support_count W _
omit [DecidableEq F] in
theorem finsum_ordAtIdeal_algebraMap {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    ∑ᶠ v, ordAtIdeal W v (algebraMap _ W.toAffine.FunctionField a) =
      ((Algebra.norm F[X] a).natDegree : ℤ) := by
  simp_rw [ordAtIdeal_algebraMap]
  exact (natDegree_norm_eq_finsum_count W ha).symm
omit [DecidableEq F] in

theorem finsum_ordAtIdeal_add_ordInfty {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    ∑ᶠ v, ordAtIdeal W v f + ordInfty W f = 0 := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.toAffine.CoordinateRing⁰ f
  dsimp only at hf ⊢
  have ha : a ≠ 0 := by
    rintro rfl
    exact hf (IsLocalization.mk'_zero _)
  have hs : (s : W.toAffine.CoordinateRing) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hs' : algebraMap _ W.toAffine.FunctionField (s : W.toAffine.CoordinateRing) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ W.toAffine.FunctionField)).mpr hs
  have hsa := IsLocalization.mk'_spec W.toAffine.FunctionField a s
  have h1 : ∀ v, ordAtIdeal W v (algebraMap _ W.toAffine.FunctionField a) =
      ordAtIdeal W v (IsLocalization.mk' W.toAffine.FunctionField a s) +
        ordAtIdeal W v (algebraMap _ W.toAffine.FunctionField (s : W.toAffine.CoordinateRing)) :=
    fun v => by rw [← hsa, ordAtIdeal_mul W v hf hs']
  have h2 : ordInfty W (algebraMap _ W.toAffine.FunctionField a) =
      ordInfty W (IsLocalization.mk' W.toAffine.FunctionField a s) +
        ordInfty W (algebraMap _ W.toAffine.FunctionField (s : W.toAffine.CoordinateRing)) := by
    rw [← hsa, ordInfty_mul W hf hs']
  have e1 := finsum_ordAtIdeal_algebraMap W ha
  have e2 := finsum_ordAtIdeal_algebraMap W hs
  simp_rw [h1] at e1
  rw [finsum_add_distrib (finite_support_ordAtIdeal W _) (finite_support_ordAtIdeal W _)] at e1
  rw [ordInfty_algebraMap W ha, ordInfty_algebraMap W hs] at h2
  linarith
theorem divisorDegree_divisorOf {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    divisorDegree W (divisorOf W f) = 0 := by
  rw [divisorDegree_eq, affinePart_divisorOf, sum_affineDivisorOf, divisorOf_zero_apply]
  exact finsum_ordAtIdeal_add_ordInfty W hf
omit [DecidableEq F] in
theorem val_idealOfExps_affineDivisorOf {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    ((idealOfExps W (affineDivisorOf W f) :
      (FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField)ˣ) :
        FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) =
      FractionalIdeal.spanSingleton _ f :=
  fractionalIdeal_eq_of_count_eq W (Units.ne_zero _) (spanSingleton_ne_zero W hf)
    fun v => by rw [count_idealOfExps, affineDivisorOf_apply, ordAtIdeal]
theorem divisorSum_divisorOf {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    divisorSum W (divisorOf W f) = 0 := by
  rw [divisorSum_eq, affinePart_divisorOf, ← Point.toClass_eq_zero, toClass_sum, ofMul_eq_zero,
    classGroup_mk_eq_one_iff]
  exact ⟨f, hf, val_idealOfExps_affineDivisorOf W hf⟩
theorem exists_divisorOf_eq {D : CurveDivisor W} (hdeg : divisorDegree W D = 0)
    (hsum : divisorSum W D = 0) :
    ∃ f : W.toAffine.FunctionField, f ≠ 0 ∧ divisorOf W f = D := by
  have hc : ClassGroup.mk W.toAffine.FunctionField (idealOfExps W (affinePart W D)) = 1 := by
    have h := toClass_sum W (affinePart W D)
    rw [← divisorSum_eq, hsum, map_zero] at h
    exact ofMul_eq_zero.mp h.symm
  obtain ⟨f, hf, hI⟩ := (classGroup_mk_eq_one_iff W _).mp hc
  refine ⟨f, hf, ?_⟩
  have haff : affineDivisorOf W f = affinePart W D := by
    ext v
    rw [affineDivisorOf_apply, ordAtIdeal, ← hI, count_idealOfExps]
  have hinf : ordInfty W f = D 0 := by
    have h1 := finsum_ordAtIdeal_add_ordInfty W hf
    have h2 := divisorDegree_eq W D
    rw [hdeg, ← haff, sum_affineDivisorOf] at h2
    linarith
  rw [divisorOf, haff, hinf]
  exact (eq_mapDomain_affinePart_add W D).symm
theorem exists_divisorOf_eq_iff (D : CurveDivisor W) :
    (∃ f : W.toAffine.FunctionField, f ≠ 0 ∧ divisorOf W f = D) ↔
      divisorDegree W D = 0 ∧ divisorSum W D = 0 := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨divisorDegree_divisorOf W hf, divisorSum_divisorOf W hf⟩
  · rintro ⟨h1, h2⟩
    exact exists_divisorOf_eq W h1 h2
noncomputable def divisorHom : Additive W.toAffine.FunctionFieldˣ →+ CurveDivisor W where
  toFun u := divisorOf W (u.toMul : W.toAffine.FunctionFieldˣ)
  map_zero' := by simp [divisorOf_one]
  map_add' u v := by
    simp only [toMul_add, Units.val_mul]
    exact divisorOf_mul W u.toMul.ne_zero v.toMul.ne_zero
noncomputable def principalDivisors : AddSubgroup (CurveDivisor W) := (divisorHom W).range
theorem mem_principalDivisors_iff (D : CurveDivisor W) :
    D ∈ principalDivisors W ↔ ∃ f : W.toAffine.FunctionField, f ≠ 0 ∧ divisorOf W f = D := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, u.toMul.ne_zero, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨Additive.ofMul (Units.mk0 f hf), rfl⟩
noncomputable def degreeZeroDivisors : AddSubgroup (CurveDivisor W) := (divisorDegree W).ker
abbrev PicZero : Type u :=
  degreeZeroDivisors W ⧸ (principalDivisors W).addSubgroupOf (degreeZeroDivisors W)
noncomputable def divisorSumDegreeZero : degreeZeroDivisors W →+ W.toAffine.Point :=
  (divisorSum W).comp (degreeZeroDivisors W).subtype
omit [IsAlgClosed F] [W.IsElliptic] [DecidableEq F] in
theorem single_sub_single_zero_mem (P : W.toAffine.Point) :
    Finsupp.single P 1 - Finsupp.single 0 1 ∈ degreeZeroDivisors W := by
  change divisorDegree W _ = 0
  simp
omit [IsAlgClosed F] [W.IsElliptic] in
theorem divisorSumDegreeZero_surjective : Function.Surjective (divisorSumDegreeZero W) := by
  intro P
  refine ⟨⟨_, single_sub_single_zero_mem W P⟩, ?_⟩
  simp [divisorSumDegreeZero]
theorem ker_divisorSumDegreeZero :
    (divisorSumDegreeZero W).ker = (principalDivisors W).addSubgroupOf (degreeZeroDivisors W) := by
  ext ⟨D, hD⟩
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_principalDivisors_iff,
    exists_divisorOf_eq_iff]
  exact ⟨fun h => ⟨hD, h⟩, fun h => h.2⟩
noncomputable def picZeroEquiv : PicZero W ≃+ W.toAffine.Point :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_divisorSumDegreeZero W).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (divisorSumDegreeZero_surjective W))
end AlgClosed
end GroundTheory.Arith.Abelian


