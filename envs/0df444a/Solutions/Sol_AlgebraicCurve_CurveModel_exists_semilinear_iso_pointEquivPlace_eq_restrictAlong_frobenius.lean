-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.exists_semilinear_iso_pointEquivPlace_eq_restrictAlong_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a2b80268-7dd2-5eff-91e3-dc6cbea56960

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import Definitions.Def_AlgebraicCurve_FrobeniusEndoPic0
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Theorems.Thm_AlgebraicCurve_isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_exists_semilinear_iso_pointEquivPlace_eq_restrictAlong_frobenius

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

namespace P2mFrobCurve

section Twist

variable {K : Type u} [Field K] (F : Type v) [Field F] [Algebra K F] (σ : K ≃+* K)

def Twist (_σ : K ≃+* K) : Type v := F

scoped instance : Field (Twist F σ) := ‹Field F›

scoped instance : Algebra K (Twist F σ) := ((algebraMap K F).comp σ.toRingHom).toAlgebra

theorem algebraMap_twist (c : K) : algebraMap K (Twist F σ) c = (algebraMap K F (σ c) : F) := rfl

variable {F}

def twistPlace (v : Place K F) : Place K (Twist F σ) where
  toValuationSubring := (v.toValuationSubring : ValuationSubring F)
  algebraMap_mem' a := v.algebraMap_mem' (σ a)
  ne_top' := v.ne_top'
  isPrincipalIdealRing' := v.isPrincipalIdealRing'

def untwistPlace (v : Place K (Twist F σ)) : Place K F where
  toValuationSubring := (v.toValuationSubring : ValuationSubring F)
  algebraMap_mem' a := by
    have := v.algebraMap_mem' (σ.symm a)
    rwa [algebraMap_twist, RingEquiv.apply_symm_apply] at this
  ne_top' := v.ne_top'
  isPrincipalIdealRing' := v.isPrincipalIdealRing'

def twistPlaceEquiv : Place K F ≃ Place K (Twist F σ) where
  toFun := twistPlace σ
  invFun := untwistPlace σ
  left_inv v := Place.ext rfl
  right_inv v := Place.ext rfl

@[scoped simp] theorem twistPlace_toValuationSubring (v : Place K F) :
    ((twistPlace σ v).toValuationSubring : ValuationSubring F) = v.toValuationSubring := rfl

end Twist

section TwistModel

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F) (σ : K ≃+* K)

theorem baseToFunctionField_comp_SpecMap {C : Scheme.{u}} [IsIntegral C] (c : C ⟶ Spec (CommRingCat.of K))
    (a : K) :
    baseToFunctionField (c ≫ Spec.map σ.toCommRingCatIso.hom) a = baseToFunctionField c (σ a) := by
  unfold baseToFunctionField
  simp only [RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  congr 1
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality σ.toCommRingCatIso.hom)) a
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [← h]
  rfl

def twistModel : CurveModel K (Twist F σ) where
  C := M.C
  toBase := M.toBase ≫ Spec.map σ.toCommRingCatIso.hom
  isIntegral := M.isIntegral
  isProper := inferInstance
  smooth := by
    have : SmoothOfRelativeDimension (1 + 0) (M.toBase ≫ Spec.map σ.toCommRingCatIso.hom) := inferInstance
    simpa using this
  ffEquiv := (M.ffEquiv : F ≃+* M.C.functionField)
  ffEquiv_algebraMap a := by
    rw [baseToFunctionField_comp_SpecMap]
    exact M.ffEquiv_algebraMap (σ a)
  placeOfPoint x := twistPlace σ (M.placeOfPoint x)
  placeOfPoint_bijective := (twistPlaceEquiv σ).bijective.comp M.placeOfPoint_bijective
  range_stalk_eq x := M.range_stalk_eq x
  finset_subset_affineOpen := M.finset_subset_affineOpen

@[scoped simp] theorem twistModel_C : (twistModel M σ).C = M.C := rfl
@[scoped simp] theorem twistModel_toBase : (twistModel M σ).toBase = M.toBase ≫ Spec.map σ.toCommRingCatIso.hom := rfl
theorem twistModel_placeOfPoint (x : closedPoints M.C) :
    ((twistModel M σ).placeOfPoint x).toValuationSubring = ((M.placeOfPoint x).toValuationSubring : ValuationSubring F) :=
  rfl

end TwistModel

section Root

variable {k K F₀ F : Type*} [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]

theorem char_data (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F] :
    ∃ p r : ℕ, p.Prime ∧ Nat.card k = p ^ r ∧ CharP F p ∧ CharP K p := by
  letI := Fintype.ofFinite k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k (ringChar k)
  haveI : CharP F₀ (ringChar k) := charP_of_injective_algebraMap (algebraMap k F₀).injective _
  haveI hF : CharP F (ringChar k) := charP_of_injective_algebraMap (algebraMap F₀ F).injective _
  haveI : CharP K (ringChar k) := ((algebraMap K F).charP_iff_charP (ringChar k)).mpr hF
  exact ⟨ringChar k, n, hp, by rw [Nat.card_eq_fintype_card, hcard], hF, inferInstance⟩

variable (φ : F →ₐ[K] F)

theorem card_ne_zero {p r : ℕ} [Fact p.Prime] (hq : Nat.card k = p ^ r) : Nat.card k ≠ 0 := by
  rw [hq]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero

theorem add_pow_card {p r : ℕ} [Fact p.Prime] [CharP F p] (hq : Nat.card k = p ^ r) (x y : F) :
    (x + y) ^ Nat.card k = x ^ Nat.card k + y ^ Nat.card k := by
  rw [hq]; exact add_pow_char_pow x y p r

theorem pow_card_injective {p r : ℕ} [Fact p.Prime] [CharP F p] (hq : Nat.card k = p ^ r) :
    Function.Injective fun x : F => x ^ Nat.card k := by
  intro x y hxy
  have : (x - y) ^ Nat.card k = 0 := by
    simp only at hxy
    rw [hq, sub_pow_char_pow, ← hq, hxy, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (card_ne_zero (k := k) hq) |>.mp this)

def rootTwist (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    (hq : Nat.card k = p ^ r) : F →+* F where
  toFun y := (h.mem_range_pow y).choose
  map_one' := by
    apply pow_card_injective (k := k) hq
    simp only
    rw [← (h.mem_range_pow 1).choose_spec, map_one, one_pow]
  map_mul' a b := by
    apply pow_card_injective (k := k) hq
    simp only
    rw [← (h.mem_range_pow (a * b)).choose_spec, map_mul, mul_pow,
      ← (h.mem_range_pow a).choose_spec, ← (h.mem_range_pow b).choose_spec]
  map_zero' := by
    apply pow_card_injective (k := k) hq
    simp only
    rw [← (h.mem_range_pow 0).choose_spec, map_zero, zero_pow (card_ne_zero (k := k) hq)]
  map_add' a b := by
    apply pow_card_injective (k := k) hq
    simp only
    rw [← (h.mem_range_pow (a + b)).choose_spec, map_add, add_pow_card (k := k) hq,
      ← (h.mem_range_pow a).choose_spec, ← (h.mem_range_pow b).choose_spec]

theorem rootTwist_pow (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    (hq : Nat.card k = p ^ r) (y : F) : (rootTwist φ h hq y) ^ Nat.card k = φ y :=
  (h.mem_range_pow y).choose_spec.symm

theorem rootTwist_bijective (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime]
    [CharP F p] (hq : Nat.card k = p ^ r) : Function.Bijective (rootTwist φ h hq) := by
  constructor
  · exact (rootTwist φ h hq).injective
  · intro z
    obtain ⟨y, hy⟩ := h.pow_mem_range z
    refine ⟨y, pow_card_injective (k := k) hq ?_⟩
    simp only
    rw [rootTwist_pow, hy]

def rootTwistEquiv (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    (hq : Nat.card k = p ^ r) : F ≃+* F :=
  RingEquiv.ofBijective (rootTwist φ h hq) (rootTwist_bijective φ h hq)

theorem rootTwistEquiv_apply (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime]
    [CharP F p] (hq : Nat.card k = p ^ r) (y : F) : rootTwistEquiv φ h hq y = rootTwist φ h hq y :=
  rfl

def basePow {p r : ℕ} [Fact p.Prime] [CharP K p] (_hq : Nat.card k = p ^ r) : K ≃+* K :=
  haveI : ExpChar K p := ExpChar.prime Fact.out
  RingEquiv.ofBijective (iterateFrobenius K p r) ⟨(iterateFrobenius K p r).injective, fun x => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x (pow_pos (Fact.out : p.Prime).pos r)
    exact ⟨z, by rw [iterateFrobenius_def, hz]⟩⟩

theorem basePow_apply {p r : ℕ} [Fact p.Prime] [CharP K p] (hq : Nat.card k = p ^ r) (x : K) :
    basePow (k := k) (K := K) hq x = x ^ Nat.card k := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  rw [hq]
  exact iterateFrobenius_def p r x

theorem rootTwist_algebraMap_pow (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    (hq : Nat.card k = p ^ r) (c : K) :
    rootTwist φ h hq (algebraMap K F (c ^ Nat.card k)) = algebraMap K F c := by
  apply pow_card_injective (k := k) hq
  simp only
  rw [rootTwist_pow, AlgHom.commutes, map_pow]

def theta (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p] [CharP K p]
    (hq : Nat.card k = p ^ r) : F ≃ₐ[K] Twist F (basePow (k := k) (K := K) hq) :=
  AlgEquiv.ofRingEquiv (f := ((rootTwistEquiv φ h hq).symm : F ≃+* F)) (fun c => by
    show (rootTwistEquiv φ h hq).symm (algebraMap K F c) = algebraMap K F (basePow (k := k) hq c)
    rw [RingEquiv.symm_apply_eq, rootTwistEquiv_apply, basePow_apply, rootTwist_algebraMap_pow])

theorem theta_symm_apply (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p] [CharP K p]
    (hq : Nat.card k = p ^ r) (y : F) :
    ((theta φ h hq).toRingEquiv.symm y : F) = rootTwist φ h hq y := by
  show ((rootTwistEquiv φ h hq).symm).symm y = _
  rw [RingEquiv.symm_symm, rootTwistEquiv_apply]

end Root

theorem main
    (k : Type*) (K : Type u) (F₀ : Type*) (F : Type v) [Field k] [Finite k] [Field K] [IsAlgClosed K]
    [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [AlgebraicCurve.IsCurveOver K F]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (M : CurveModel K F) :
    ∃ σ : K →+* K, (∀ c : K, σ c = c ^ Nat.card k) ∧
      ∃ B : M.C ≅ M.C, B.hom ≫ M.toBase ≫ Spec.map (CommRingCat.ofHom σ) = M.toBase ∧
        ∀ y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
          ∃ hy : (Spec.map (CommRingCat.ofHom σ) ≫ y.1 ≫ B.hom) ≫ M.toBase = 𝟙 _,
            M.pointEquivPlace ⟨Spec.map (CommRingCat.ofHom σ) ≫ y.1 ≫ B.hom, hy⟩ =
              AlgebraicCurve.Place.restrictAlong φ hφi (M.pointEquivPlace y) := by
  obtain ⟨p, r, hp, hq, hFp, hKp⟩ := char_data k K F₀ F
  haveI := Fact.mk hp
  haveI := hFp
  haveI := hKp
  obtain ⟨hFE, -, -⟩ :=
    AlgebraicCurve.isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card
      k K F₀ F hgen φ hφi hφ
  let σe : K ≃+* K := basePow (k := k) (K := K) hq
  obtain ⟨e, he, hplace⟩ :=
    AlgebraicCurve.CurveModel.exists_iso_comp_toBase_eq_placeOfPoint_congr_eq (theta φ hFE hq) M (twistModel M σe)
  have hσS : Spec.map (CommRingCat.ofHom (σe : K →+* K)) = Spec.map σe.toCommRingCatIso.hom := rfl
  haveI : IsIso (Spec.map (CommRingCat.ofHom (σe : K →+* K))) := by rw [hσS]; infer_instance
  have hB : e.hom ≫ M.toBase ≫ Spec.map (CommRingCat.ofHom (σe : K →+* K)) = M.toBase := he
  refine ⟨(σe : K →+* K), fun c => basePow_apply hq c, e, hB, fun y => ?_⟩
  have hB' : e.hom ≫ M.toBase = M.toBase ≫ inv (Spec.map (CommRingCat.ofHom (σe : K →+* K))) :=
    (IsIso.eq_comp_inv _).mpr (by simpa only [Category.assoc] using hB)
  have hy : (Spec.map (CommRingCat.ofHom (σe : K →+* K)) ≫ y.1 ≫ e.hom) ≫ M.toBase = 𝟙 _ := by
    simp only [Category.assoc]
    rw [hB', reassoc_of% y.2, IsIso.hom_inv_id]
  refine ⟨hy, ?_⟩
  rw [CurveModel.pointEquivPlace_apply, CurveModel.pointEquivPlace_apply]
  set x₀ := pointEquivClosedPoint M.toBase y with hx₀
  set x₁ := pointEquivClosedPoint M.toBase
    ⟨Spec.map (CommRingCat.ofHom (σe : K →+* K)) ≫ y.1 ≫ e.hom, hy⟩ with hx₁
  have hval : x₁.1 = e.hom.base x₀.1 := by
    simp only [hx₁, hx₀, pointEquivClosedPoint_apply_coe, Scheme.Hom.comp_apply]
    congr 2
    exact Subsingleton.elim _ _
  have hx : x₁ = ⟨e.hom.base x₀.1, hval ▸ x₁.2⟩ := Subtype.ext hval
  rw [hx]
  apply Place.ext
  have key := congrArg (fun P : Place K (Twist F σe) => (P.toValuationSubring : ValuationSubring F)) (hplace x₀)
  refine key.trans ?_
  ext z
  change (theta φ hFE hq).toRingEquiv.symm z ∈ (M.placeOfPoint x₀).toValuationSubring ↔
    φ z ∈ (M.placeOfPoint x₀).toValuationSubring
  rw [theta_symm_apply, ← rootTwist_pow φ hFE hq z]
  exact ((M.placeOfPoint x₀).toValuationSubring.pow_mem_iff (card_ne_zero (k := k) hq) _).symm

end P2mFrobCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_exists_semilinear_iso_pointEquivPlace_eq_restrictAlong_frobenius.P2mFrobCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_exists_semilinear_iso_pointEquivPlace_eq_restrictAlong_frobenius.P2mFrobCurve"

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem solution
    (k : Type*) (K : Type u) (F₀ : Type*) (F : Type v) [Field k] [Finite k] [Field K] [IsAlgClosed K]
    [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [AlgebraicCurve.IsCurveOver K F]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (M : CurveModel K F) :
    ∃ σ : K →+* K, (∀ c : K, σ c = c ^ Nat.card k) ∧
      ∃ B : M.C ≅ M.C, B.hom ≫ M.toBase ≫ Spec.map (CommRingCat.ofHom σ) = M.toBase ∧
        ∀ y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
          ∃ hy : (Spec.map (CommRingCat.ofHom σ) ≫ y.1 ≫ B.hom) ≫ M.toBase = 𝟙 _,
            M.pointEquivPlace ⟨Spec.map (CommRingCat.ofHom σ) ≫ y.1 ≫ B.hom, hy⟩ =
              AlgebraicCurve.Place.restrictAlong φ hφi (M.pointEquivPlace y) :=
  P2mFrobCurve.main k K F₀ F hgen φ hφi hφ M

end S_AlgebraicCurve_CurveModel_exists_semilinear_iso_pointEquivPlace_eq_restrictAlong_frobenius
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_exists_semilinear_iso_pointEquivPlace_eq_restrictAlong_frobenius (solution)
