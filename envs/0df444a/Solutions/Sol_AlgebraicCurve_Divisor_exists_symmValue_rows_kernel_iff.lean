-- Prove2me | solution 1 for AlgebraicCurve.Divisor.exists_symmValue_rows_kernel_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/993a6c36-ef05-5b87-a021-8ce4462d1f57

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_neg_log_of_valuationSubring_eq
import Theorems.Thm_AlgebraicCurve_Place_exists_gram_denominator_of_mulTable
import Theorems.Thm_AlgebraicCurve_Place_exists_uniformizing_separating_form
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_exists_symmValue_rows_kernel_iff
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_exists_symmValue_rows_kernel_iff.AlgebraicCurve Polynomial"

namespace mwALGMdev

section pinpack

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

private theorem mwALGM_ord_algebraMap (v : Place k F) (c : k) :
    v.ord (algebraMap k F c) = 0 := by
  have h1 : 0 ≤ v.ord (algebraMap k F c) :=
    v.ord_nonneg_of_mem (v.algebraMap_mem' c)
  have h2 : 0 ≤ v.ord (algebraMap k F c)⁻¹ := by
    rw [← map_inv₀]
    exact v.ord_nonneg_of_mem (v.algebraMap_mem' c⁻¹)
  rw [v.ord_inv] at h2
  omega

private theorem mwALGM_ord_neg (v : Place k F) (x : F) : v.ord (-x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [neg_zero]
  · have hm : (-x : F) = algebraMap k F (-1) * x := by
      rw [map_neg, map_one, neg_one_mul]
    have h1 : algebraMap k F (-1 : k) ≠ 0 := by
      rw [map_neg, map_one]
      exact neg_ne_zero.mpr one_ne_zero
    rw [hm, v.ord_mul h1 hx, mwALGM_ord_algebraMap v (-1), zero_add]

private theorem mwALGM_pin_unique (v : Place k F) {x : F} {c c' : k}
    (h : x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c))
    (h' : x = algebraMap k F c' ∨ 0 < v.ord (x - algebraMap k F c')) : c = c' := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact (algebraMap k F).injective (h.symm.trans h')
  · exfalso
    rw [h, ← map_sub] at h'
    rw [mwALGM_ord_algebraMap v (c - c')] at h'
    exact lt_irrefl 0 h'
  · exfalso
    rw [h', ← map_sub] at h
    rw [mwALGM_ord_algebraMap v (c' - c)] at h
    exact lt_irrefl 0 h
  · by_contra hne
    have hxc : x - algebraMap k F c ≠ 0 := by
      intro h0; rw [h0, v.ord_zero] at h; exact lt_irrefl 0 h
    have hxc' : -(x - algebraMap k F c') ≠ 0 := by
      intro h0
      rw [neg_eq_zero] at h0
      rw [h0, v.ord_zero] at h'
      exact lt_irrefl 0 h'
    have hsum : (x - algebraMap k F c) + -(x - algebraMap k F c')
        = algebraMap k F (c' - c) := by
      rw [map_sub]; ring
    have hne' : algebraMap k F (c' - c) ≠ 0 := by
      intro h0
      have hcc := (algebraMap k F).injective (h0.trans (map_zero (algebraMap k F)).symm)
      exact hne (sub_eq_zero.mp hcc).symm
    have hmin := v.min_ord_le_ord_add hxc hxc' (by rw [hsum]; exact hne')
    rw [hsum, mwALGM_ord_algebraMap v (c' - c), mwALGM_ord_neg] at hmin
    exact absurd hmin (not_le.mpr (lt_min h h'))

private theorem mwALGM_ord_add_min (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (v.ord x) (v.ord y) ≤ v.ord (x + y) :=
  v.min_ord_le_ord_add hx hy hxy

private theorem mwALGM_pin_add (v : Place k F) {x y : F} {c e : k}
    (hc : x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c))
    (he : y = algebraMap k F e ∨ 0 < v.ord (y - algebraMap k F e)) :
    x + y = algebraMap k F (c + e) ∨ 0 < v.ord (x + y - algebraMap k F (c + e)) := by
  rcases hc with hc | hc <;> rcases he with he | he
  · left; rw [hc, he, map_add]
  · right
    have heq : x + y - algebraMap k F (c + e) = y - algebraMap k F e := by
      rw [hc, map_add]; ring
    rw [heq]; exact he
  · right
    have heq : x + y - algebraMap k F (c + e) = x - algebraMap k F c := by
      rw [he, map_add]; ring
    rw [heq]; exact hc
  · by_cases hz : x + y - algebraMap k F (c + e) = 0
    · left; exact sub_eq_zero.mp hz
    · right
      have hxc : x - algebraMap k F c ≠ 0 := by
        intro h0; rw [h0, v.ord_zero] at hc; exact lt_irrefl 0 hc
      have hye : y - algebraMap k F e ≠ 0 := by
        intro h0; rw [h0, v.ord_zero] at he; exact lt_irrefl 0 he
      have hsplit : x + y - algebraMap k F (c + e)
          = (x - algebraMap k F c) + (y - algebraMap k F e) := by
        rw [map_add]; ring
      have hmin := mwALGM_ord_add_min v hxc hye (by rw [← hsplit]; exact hz)
      rw [← hsplit] at hmin
      exact lt_of_lt_of_le (lt_min hc he) hmin

private theorem mwALGM_pin_mul (v : Place k F) {x y : F} {c e : k}
    (hx : x ∈ v.toValuationSubring)
    (hc : x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c))
    (he : y = algebraMap k F e ∨ 0 < v.ord (y - algebraMap k F e)) :
    x * y = algebraMap k F (c * e) ∨ 0 < v.ord (x * y - algebraMap k F (c * e)) := by
  have hinj : ∀ {a : k}, algebraMap k F a = 0 → a = 0 := fun {a} h0 =>
    (algebraMap k F).injective (h0.trans (map_zero (algebraMap k F)).symm)
  rcases hc with hc | hc
  · rcases he with he | he
    · left; rw [hc, he, ← map_mul]
    · by_cases hc0 : c = 0
      · left
        rw [hc, hc0, map_zero, zero_mul, zero_mul, map_zero]
      · right
        have hfac : x * y - algebraMap k F (c * e)
            = algebraMap k F c * (y - algebraMap k F e) := by
          rw [hc, map_mul]; ring
        have hye : y - algebraMap k F e ≠ 0 := by
          intro h0; rw [h0, v.ord_zero] at he; exact lt_irrefl 0 he
        rw [hfac, v.ord_mul (fun h0 => hc0 (hinj h0)) hye,
          mwALGM_ord_algebraMap v c, zero_add]
        exact he
  · rcases he with he | he
    · by_cases he0 : e = 0
      · left; rw [he, he0, map_zero, mul_zero, mul_zero, map_zero]
      · right
        have hfac : x * y - algebraMap k F (c * e)
            = algebraMap k F e * (x - algebraMap k F c) := by
          rw [he, map_mul]; ring
        have hxc : x - algebraMap k F c ≠ 0 := by
          intro h0; rw [h0, v.ord_zero] at hc; exact lt_irrefl 0 hc
        rw [hfac, v.ord_mul (fun h0 => he0 (hinj h0)) hxc,
          mwALGM_ord_algebraMap v e, zero_add]
        exact hc
    · have hxc : x - algebraMap k F c ≠ 0 := by
        intro h0; rw [h0, v.ord_zero] at hc; exact lt_irrefl 0 hc
      have hye : y - algebraMap k F e ≠ 0 := by
        intro h0; rw [h0, v.ord_zero] at he; exact lt_irrefl 0 he
      have hsplit : x * y - algebraMap k F (c * e)
          = x * (y - algebraMap k F e) + algebraMap k F e * (x - algebraMap k F c) := by
        rw [map_mul]; ring
      by_cases hz : x * y - algebraMap k F (c * e) = 0
      · left; exact sub_eq_zero.mp hz
      right
      by_cases hx0 : x = 0
      · have heq : x * y - algebraMap k F (c * e)
            = algebraMap k F e * (x - algebraMap k F c) := by
          rw [hsplit, hx0, zero_mul, zero_add]
        by_cases he0 : e = 0
        · exact absurd (by rw [heq, he0, map_zero, zero_mul]) hz
        · rw [heq, v.ord_mul (fun h0 => he0 (hinj h0)) hxc,
            mwALGM_ord_algebraMap v e, zero_add]
          exact hc
      · by_cases he0 : e = 0
        · have heq : x * y - algebraMap k F (c * e) = x * (y - algebraMap k F e) := by
            rw [hsplit, he0, map_zero, zero_mul, add_zero]
          rw [heq, v.ord_mul hx0 hye]
          have h1 := v.ord_nonneg_of_mem hx
          linarith
        · have ht1 : x * (y - algebraMap k F e) ≠ 0 := mul_ne_zero hx0 hye
          have ht2 : algebraMap k F e * (x - algebraMap k F c) ≠ 0 :=
            mul_ne_zero (fun h0 => he0 (hinj h0)) hxc
          have hb1 : 0 < v.ord (x * (y - algebraMap k F e)) := by
            rw [v.ord_mul hx0 hye]
            have h1 := v.ord_nonneg_of_mem hx
            linarith
          have hb2 : 0 < v.ord (algebraMap k F e * (x - algebraMap k F c)) := by
            rw [v.ord_mul (fun h0 => he0 (hinj h0)) hxc,
              mwALGM_ord_algebraMap v e, zero_add]
            exact hc
          have hmin := mwALGM_ord_add_min v ht1 ht2 (by rw [← hsplit]; exact hz)
          rw [← hsplit] at hmin
          exact lt_of_lt_of_le (lt_min hb1 hb2) hmin

private theorem mwALGM_pin_pow (v : Place k F) {x : F} {c : k}
    (hx : x ∈ v.toValuationSubring)
    (hc : x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c)) (m : ℕ) :
    x ^ m = algebraMap k F (c ^ m) ∨ 0 < v.ord (x ^ m - algebraMap k F (c ^ m)) := by
  induction m with
  | zero => left; rw [pow_zero, pow_zero, map_one]
  | succ t ih =>
    have hstep := mwALGM_pin_mul v (pow_mem hx t) ih hc
    rw [← pow_succ, ← pow_succ] at hstep
    exact hstep

private theorem mwALGM_pin_sum {ι : Type*} (v : Place k F) (s : Finset ι)
    (f : ι → F) (g : ι → k)
    (h : ∀ i ∈ s, f i = algebraMap k F (g i) ∨ 0 < v.ord (f i - algebraMap k F (g i))) :
    (∑ i ∈ s, f i) = algebraMap k F (∑ i ∈ s, g i)
      ∨ 0 < v.ord ((∑ i ∈ s, f i) - algebraMap k F (∑ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => left; rw [Finset.sum_empty, Finset.sum_empty, map_zero]
  | @insert a s' ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact mwALGM_pin_add v (h a (Finset.mem_insert_self a s'))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem mwALGM_aeval_mem (v : Place k F) {x : F} (hx : x ∈ v.toValuationSubring)
    (p : Polynomial k) : Polynomial.aeval x p ∈ v.toValuationSubring := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact mul_mem (v.algebraMap_mem' a) (pow_mem hx n)

private theorem mwALGM_pin_aeval (v : Place k F) {x : F} {c : k}
    (hx : x ∈ v.toValuationSubring)
    (hc : x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c))
    (p : Polynomial k) :
    Polynomial.aeval x p = algebraMap k F (Polynomial.eval c p)
      ∨ 0 < v.ord (Polynomial.aeval x p - algebraMap k F (Polynomial.eval c p)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Polynomial.eval_add]
    exact mwALGM_pin_add v hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial]
    exact mwALGM_pin_mul v (v.algebraMap_mem' a)
      (Or.inl rfl) (mwALGM_pin_pow v hx hc n)

private theorem mwALGM_pin_eval₂ {K₀ : Type*} [Field K₀] [Algebra K₀ k] (v : Place k F)
    {x y : F} {c e : k}
    (hx : x ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (hc : x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c))
    (he : y = algebraMap k F e ∨ 0 < v.ord (y - algebraMap k F e))
    (χ : Polynomial (Polynomial K₀)) :
    Polynomial.eval₂ ((Polynomial.aeval x).toRingHom.comp (Polynomial.mapRingHom (algebraMap K₀ k)))
        y χ
      = algebraMap k F (Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ k) c) e χ)
    ∨ 0 < v.ord (Polynomial.eval₂
        ((Polynomial.aeval x).toRingHom.comp (Polynomial.mapRingHom (algebraMap K₀ k))) y χ
      - algebraMap k F (Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ k) c) e χ)) := by
  induction χ using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval₂_add, Polynomial.eval₂_add]
    exact mwALGM_pin_add v hp hq
  | monomial m q =>
    rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial]
    have h1 : ((Polynomial.aeval x).toRingHom.comp
        (Polynomial.mapRingHom (algebraMap K₀ k))) q
        = Polynomial.aeval x (q.map (algebraMap K₀ k)) := rfl
    have h2 : (Polynomial.eval₂RingHom (algebraMap K₀ k) c) q
        = Polynomial.eval₂ (algebraMap K₀ k) c q := rfl
    rw [h1, h2, ← Polynomial.eval_map]
    exact mwALGM_pin_mul v (mwALGM_aeval_mem v hx _)
      (mwALGM_pin_aeval v hx hc _) (mwALGM_pin_pow v hy he m)

private theorem mwALGM_pin_eval₂_eq_zero {K₀ : Type*} [Field K₀] [Algebra K₀ k] (v : Place k F)
    {x y : F} {c e : k}
    (hx : x ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (hc : x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c))
    (he : y = algebraMap k F e ∨ 0 < v.ord (y - algebraMap k F e))
    (χ : Polynomial (Polynomial K₀))
    (hkill : Polynomial.eval₂
      ((Polynomial.aeval x).toRingHom.comp (Polynomial.mapRingHom (algebraMap K₀ k))) y χ = 0) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ k) c) e (χ) = 0 := by
  have hpin := mwALGM_pin_eval₂ v hx hy hc he χ
  rw [hkill] at hpin
  have h0 : (0 : F) = algebraMap k F 0 ∨ 0 < v.ord ((0 : F) - algebraMap k F 0) :=
    Or.inl (map_zero (algebraMap k F)).symm
  exact mwALGM_pin_unique v hpin h0

end pinpack

section chilane

variable {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]

private theorem mwALGM_exists_mulMatrix_chi {j : F} (hj : Transcendental k j)
    (n : ℕ) (b : Fin n → F)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'')
    (c₀ : Polynomial K₀) (cc : Fin n → Polynomial K₀) :
    ∃ (M : Matrix (Fin n) (Fin n) (Polynomial K₀)) (χ : Polynomial (Polynomial K₀)),
      χ.Monic ∧
      (∀ (m : ℕ) (i : Fin n),
        (Polynomial.aeval j (c₀.map (algebraMap K₀ k))
            + ∑ i' : Fin n, Polynomial.aeval j ((cc i' * d).map (algebraMap K₀ k)) * b i') ^ m
          * (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i)
        = ∑ i' : Fin n, Polynomial.aeval j (((M ^ m) i' i).map (algebraMap K₀ k))
            * (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i')) ∧
      Polynomial.eval₂
        ((Polynomial.aeval j).toRingHom.comp (Polynomial.mapRingHom (algebraMap K₀ k)))
        (Polynomial.aeval j (c₀.map (algebraMap K₀ k))
          + ∑ i' : Fin n, Polynomial.aeval j ((cc i' * d).map (algebraMap K₀ k)) * b i') χ
      = 0 := by
  classical
  set φ : K₀ →+* k := algebraMap K₀ k with hφ
  set dj : F := Polynomial.aeval j (d.map φ) with hdjdef
  set L : F := Polynomial.aeval j (c₀.map φ)
    + ∑ i' : Fin n, Polynomial.aeval j ((cc i' * d).map φ) * b i' with hLdef
  set M : Matrix (Fin n) (Fin n) (Polynomial K₀) :=
    Matrix.of fun i'' i' => (if i'' = i' then c₀ else 0) + ∑ t, cc t * A t i'' i' with hMdef

  have hbase : ∀ i' : Fin n,
      L * (dj * b i') = ∑ i'' : Fin n,
        Polynomial.aeval j ((M i'' i').map φ) * (dj * b i'') := by
    intro i'
    have hexp : L * (dj * b i')
        = Polynomial.aeval j (c₀.map φ) * (dj * b i')
          + ∑ t, Polynomial.aeval j ((cc t).map φ) * dj * (b t * b i' * dj) := by
      rw [hLdef, add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Polynomial.map_mul, map_mul]
      rw [← hdjdef]
      ring
    rw [hexp]
    have hmid : (∑ t, Polynomial.aeval j ((cc t).map φ) * dj * (b t * b i' * dj))
        = ∑ i'' : Fin n, (∑ t, Polynomial.aeval j ((cc t).map φ)
            * Polynomial.aeval j ((A t i'' i').map φ)) * (dj * b i'') := by
      calc ∑ t, Polynomial.aeval j ((cc t).map φ) * dj * (b t * b i' * dj)
          = ∑ t, ∑ i'', Polynomial.aeval j ((cc t).map φ)
              * Polynomial.aeval j ((A t i'' i').map φ) * (dj * b i'') := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [hmul t i', Finset.mul_sum]
            refine Finset.sum_congr rfl fun i'' _ => ?_
            ring
        _ = ∑ i'', ∑ t, Polynomial.aeval j ((cc t).map φ)
              * Polynomial.aeval j ((A t i'' i').map φ) * (dj * b i'') := Finset.sum_comm
        _ = ∑ i'', (∑ t, Polynomial.aeval j ((cc t).map φ)
              * Polynomial.aeval j ((A t i'' i').map φ)) * (dj * b i'') := by
            refine Finset.sum_congr rfl fun i'' _ => ?_
            rw [Finset.sum_mul]
    have hdelta : Polynomial.aeval j (c₀.map φ) * (dj * b i')
        = ∑ i'' : Fin n, (if i'' = i' then Polynomial.aeval j (c₀.map φ) else 0)
            * (dj * b i'') := by
      symm
      calc ∑ i'' : Fin n, (if i'' = i' then Polynomial.aeval j (c₀.map φ) else 0) * (dj * b i'')
          = ∑ i'' : Fin n, (if i'' = i' then Polynomial.aeval j (c₀.map φ) * (dj * b i'') else 0) := by
            refine Finset.sum_congr rfl fun i'' _ => ?_
            rw [ite_mul, zero_mul]
        _ = Polynomial.aeval j (c₀.map φ) * (dj * b i') := by
            rw [Finset.sum_ite_eq' Finset.univ i']
            simp
    rw [hmid, hdelta, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i'' _ => ?_
    rw [hMdef, Matrix.of_apply, Polynomial.map_add, map_add, add_mul]
    congr 1
    · congr 1
      split_ifs with h
      · rfl
      · rw [Polynomial.map_zero, map_zero]
    · congr 1
      rw [Polynomial.map_sum, map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Polynomial.map_mul, map_mul]

  have hpow : ∀ (m : ℕ) (i : Fin n), L ^ m * (dj * b i)
      = ∑ i' : Fin n, Polynomial.aeval j (((M ^ m) i' i).map φ) * (dj * b i') := by
    intro m
    induction m with
    | zero =>
      intro i
      rw [pow_zero, one_mul, pow_zero]
      symm
      calc ∑ i' : Fin n,
            Polynomial.aeval j (((1 : Matrix (Fin n) (Fin n) (Polynomial K₀)) i' i).map φ)
              * (dj * b i')
          = ∑ i' : Fin n, (if i' = i then dj * b i' else 0) := by
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [Matrix.one_apply]
            split_ifs with h
            · rw [Polynomial.map_one, map_one, one_mul]
            · rw [Polynomial.map_zero, map_zero, zero_mul]
        _ = dj * b i := by
            rw [Finset.sum_ite_eq' Finset.univ i]
            simp
    | succ m ih =>
      intro i
      rw [pow_succ', mul_assoc, ih i, Finset.mul_sum]
      calc ∑ i' : Fin n, L * (Polynomial.aeval j (((M ^ m) i' i).map φ) * (dj * b i'))
          = ∑ i' : Fin n, Polynomial.aeval j (((M ^ m) i' i).map φ) * (L * (dj * b i')) := by
            refine Finset.sum_congr rfl fun i' _ => ?_
            ring
        _ = ∑ i' : Fin n, Polynomial.aeval j (((M ^ m) i' i).map φ)
              * (∑ i'' : Fin n, Polynomial.aeval j ((M i'' i').map φ) * (dj * b i'')) := by
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [hbase i']
        _ = ∑ i' : Fin n, ∑ i'' : Fin n, Polynomial.aeval j ((M i'' i').map φ)
              * Polynomial.aeval j (((M ^ m) i' i).map φ) * (dj * b i'') := by
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i'' _ => ?_
            ring
        _ = ∑ i'' : Fin n, ∑ i' : Fin n, Polynomial.aeval j ((M i'' i').map φ)
              * Polynomial.aeval j (((M ^ m) i' i).map φ) * (dj * b i'') := Finset.sum_comm
        _ = ∑ i'' : Fin n, Polynomial.aeval j (((M ^ (m + 1)) i'' i).map φ) * (dj * b i'') := by
            refine Finset.sum_congr rfl fun i'' _ => ?_
            rw [← Finset.sum_mul]
            congr 1
            rw [pow_succ' M m, Matrix.mul_apply, Polynomial.map_sum, map_sum]
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [Polynomial.map_mul, map_mul]

  have htrans : ∀ (χp : Polynomial (Polynomial K₀)) (i : Fin n),
      Polynomial.eval₂ ((Polynomial.aeval j).toRingHom.comp (Polynomial.mapRingHom φ)) L χp
          * (dj * b i)
        = ∑ i' : Fin n,
            Polynomial.aeval j (((Polynomial.aeval M χp) i' i).map φ) * (dj * b i') := by
    intro χp
    induction χp using Polynomial.induction_on' with
    | add p q hp hq =>
      intro i
      rw [Polynomial.eval₂_add, map_add, add_mul, hp i, hq i, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Matrix.add_apply, Polynomial.map_add, map_add, add_mul]
    | monomial m q =>
      intro i
      rw [Polynomial.eval₂_monomial, Polynomial.aeval_monomial, mul_assoc, hpow m i,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      have halg : (algebraMap (Polynomial K₀) (Matrix (Fin n) (Fin n) (Polynomial K₀)) q
          * M ^ m) i' i = q * (M ^ m) i' i := by
        rw [← Algebra.smul_def, Matrix.smul_apply, smul_eq_mul]
      rw [halg, Polynomial.map_mul, map_mul]
      have h1 : ((Polynomial.aeval j).toRingHom.comp (Polynomial.mapRingHom φ)) q
          = Polynomial.aeval j (q.map φ) := rfl
      rw [h1]
      ring

  have hbex : ∃ i, b i ≠ 0 := by
    obtain ⟨q, c, hq, hqe⟩ := hbsp 1
    by_contra hall
    have hall' : ∀ i, b i = 0 := fun i => by
      by_contra hbi
      exact hall ⟨i, hbi⟩
    rw [Finset.sum_eq_zero fun i _ => by rw [hall' i, mul_zero], one_mul] at hqe
    exact hj ⟨q, hq, hqe⟩
  have hdj : dj ≠ 0 := by
    rw [hdjdef]
    intro h0
    exact hj ⟨d.map φ, (Polynomial.map_ne_zero_iff (algebraMap K₀ k).injective).mpr hd, h0⟩

  refine ⟨M, M.charpoly, Matrix.charpoly_monic M, hpow, ?_⟩
  obtain ⟨i₀, hb0⟩ := hbex
  have h0 := htrans M.charpoly i₀
  rw [Matrix.aeval_self_charpoly] at h0
  simp only [Matrix.zero_apply, Polynomial.map_zero, map_zero, zero_mul,
    Finset.sum_const_zero] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd h (mul_ne_zero hdj hb0)

private theorem mwALGM_isIntegral_form {j : F} (hj : Transcendental k j)
    (n : ℕ) (b : Fin n → F)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'')
    (c₀ : Polynomial K₀) (cc : Fin n → Polynomial K₀) :
    IsIntegral (Algebra.adjoin k ({j} : Set F))
      (Polynomial.aeval j (c₀.map (algebraMap K₀ k))
        + ∑ i' : Fin n, Polynomial.aeval j ((cc i' * d).map (algebraMap K₀ k)) * b i') := by
  classical
  obtain ⟨M, χ, hmonic, hpow, hkill⟩ :=
    mwALGM_exists_mulMatrix_chi hj n b hbsp d hd A hmul c₀ cc
  have hmem : ∀ q : Polynomial K₀,
      ((Polynomial.aeval j).toRingHom.comp
        (Polynomial.mapRingHom (algebraMap K₀ k))) q ∈ Algebra.adjoin k ({j} : Set F) := by
    intro q
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q.map (algebraMap K₀ k), rfl⟩
  set ψ : Polynomial K₀ →+* (Algebra.adjoin k ({j} : Set F)) :=
    ((Polynomial.aeval j).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap K₀ k))).codRestrict
      (Algebra.adjoin k ({j} : Set F)) hmem with hψ
  refine ⟨χ.map ψ, hmonic.map ψ, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap (Algebra.adjoin k ({j} : Set F)) F).comp ψ
      = (Polynomial.aeval j).toRingHom.comp (Polynomial.mapRingHom (algebraMap K₀ k)) :=
    RingHom.ext fun q => rfl
  rw [hcomp]
  exact hkill

private theorem mwALGM_isIntegral_j {j : F} :
    IsIntegral (Algebra.adjoin k ({j} : Set F)) j := by
  have hmem : j ∈ Algebra.adjoin k ({j} : Set F) := Algebra.self_mem_adjoin_singleton k j
  exact isIntegral_algebraMap (x := (⟨j, hmem⟩ : Algebra.adjoin k ({j} : Set F)))

private theorem mwALGM_isIntegral_db {j : F} (hj : Transcendental k j)
    (n : ℕ) (b : Fin n → F)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'') :
    ∀ i : Fin n, IsIntegral (Algebra.adjoin k ({j} : Set F))
      (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i) := by
  classical
  intro i
  have h := mwALGM_isIntegral_form hj n b hbsp d hd A hmul 0 (Pi.single i 1)
  have heq : Polynomial.aeval j ((0 : Polynomial K₀).map (algebraMap K₀ k))
      + ∑ i' : Fin n, Polynomial.aeval j
          (((Pi.single i 1 : Fin n → Polynomial K₀) i' * d).map (algebraMap K₀ k)) * b i'
      = Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i := by
    rw [Polynomial.map_zero, map_zero, zero_add]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_mul]
    · intro i' _ hne
      rw [Pi.single_eq_of_ne hne, zero_mul, Polynomial.map_zero, map_zero, zero_mul]
    · intro habs
      exact absurd (Finset.mem_univ i) habs
  rw [← heq]
  exact h

end chilane

section gstar

open IsDedekindDomain

open scoped IntermediateField.algebraAdjoinAdjoin

variable {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]

private theorem mwALGM_isPrincipalIdealRing_adjoin (j : F) :
    IsPrincipalIdealRing (Algebra.adjoin k ({j} : Set F)) := by
  let e : (Polynomial.aeval j : Polynomial k →ₐ[k] F).range ≃ₐ[k] Algebra.adjoin k ({j} : Set F) :=
    Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval k j).symm
  let f : Polynomial k →ₐ[k] Algebra.adjoin k ({j} : Set F) :=
    e.toAlgHom.comp (Polynomial.aeval j).rangeRestrict
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨p, hp⟩ : ∃ p : Polynomial k, (Polynomial.aeval j).rangeRestrict p = e.symm y := by
      obtain ⟨p, hp⟩ := (e.symm y).2
      exact ⟨p, Subtype.ext hp⟩
    refine ⟨p, ?_⟩
    show e ((Polynomial.aeval j).rangeRestrict p) = y
    rw [hp]
    exact e.apply_symm_apply y
  exact IsPrincipalIdealRing.of_surjective f.toRingHom hf

private theorem mwALGM_isIntegral_adjoin_of_forall_mem {j : F}
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F]
    {x : F} (hx : ∀ v : Place k F, j ∈ v.toValuationSubring → x ∈ v.toValuationSubring) :
    IsIntegral (Algebra.adjoin k ({j} : Set F)) x := by
  set A : Subalgebra k F := Algebra.adjoin k ({j} : Set F) with hA
  haveI : IsPrincipalIdealRing A := mwALGM_isPrincipalIdealRing_adjoin j
  haveI : IsDedekindDomain A := inferInstance
  haveI : IsDedekindDomain (integralClosure A F) :=
    integralClosure.isDedekindDomain A (IntermediateField.adjoin k ({j} : Set F)) F
  haveI : IsFractionRing (integralClosure A F) F :=
    integralClosure.isFractionRing_of_finite_extension (IntermediateField.adjoin k ({j} : Set F)) F
  have hmem : x ∈ (⨅ 𝔭 : HeightOneSpectrum (integralClosure A F),
      Localization.subalgebra.ofField F _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors) := by
    rw [Algebra.mem_iInf]
    intro 𝔭
    let v : Place k F := Place.ofHeightOneSpectrum (K := k) (R := integralClosure A F) (F := F) 𝔭
    have hjC : j ∈ integralClosure A F := by
      have hjA : j ∈ A := Algebra.self_mem_adjoin_singleton k j
      exact (mem_integralClosure_iff A F).mpr (isIntegral_algebraMap (R := A) (x := ⟨j, hjA⟩))
    have hjv : j ∈ v.toValuationSubring := by
      show j ∈ ((𝔭.valuation F).valuationSubring : ValuationSubring F)
      rw [Valuation.mem_valuationSubring_iff]
      exact 𝔭.valuation_le_one ⟨j, hjC⟩
    have hxv := hx v hjv
    change x ∈ ((𝔭.valuation F).valuationSubring : ValuationSubring F) at hxv
    rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hxv
    exact hxv
  rw [HeightOneSpectrum.iInf_localization_eq_bot (integralClosure A F) (K := F), Algebra.mem_bot]
    at hmem
  obtain ⟨c, rfl⟩ := hmem
  exact (mem_integralClosure_iff A F).mp c.2

private theorem mwALGM_exists_aeval_eq_trace_of_isIntegral {j : F}
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F]
    {x : F} (hint : IsIntegral (Algebra.adjoin k ({j} : Set F)) x) :
    ∃ p : Polynomial k, Polynomial.aeval j p =
      ((Algebra.trace (IntermediateField.adjoin k ({j} : Set F)) F x :
        IntermediateField.adjoin k ({j} : Set F)) : F) := by
  haveI : IsPrincipalIdealRing (Algebra.adjoin k ({j} : Set F)) :=
    mwALGM_isPrincipalIdealRing_adjoin j
  have htr := Algebra.isIntegral_trace (L := IntermediateField.adjoin k ({j} : Set F)) hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral htr
  have hmem : ((Algebra.trace (IntermediateField.adjoin k ({j} : Set F)) F x :
      IntermediateField.adjoin k ({j} : Set F)) : F) ∈ Algebra.adjoin k ({j} : Set F) := by
    rw [← hy, IntermediateField.algebraAdjoinAdjoin.coe_algebraMap]
    exact y.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  exact hmem

private theorem mwALGM_exists_basis {j : F} (hj : Transcendental k j) (n : ℕ) (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i) :
    ∃ bE : Module.Basis (Fin n) (IntermediateField.adjoin k ({j} : Set F)) F, ⇑bE = b := by
  classical
  have haev : ∀ p : Polynomial k,
      Polynomial.aeval j p ∈ IntermediateField.adjoin k ({j} : Set F) := by
    intro p
    have h1 : Polynomial.aeval j p ∈ Algebra.adjoin k ({j} : Set F) := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨p, rfl⟩
    exact IntermediateField.algebra_adjoin_le_adjoin k _ h1
  have hane : ∀ {p : Polynomial k}, p ≠ 0 → Polynomial.aeval j p ≠ 0 :=
    fun {p} hp h => hj ⟨p, hp, h⟩
  have hli : LinearIndependent (IntermediateField.adjoin k ({j} : Set F)) b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hrep : ∀ i, ∃ (r s : Polynomial k), s ≠ 0 ∧
        (g i : F) * Polynomial.aeval j s = Polynomial.aeval j r := by
      intro i
      obtain ⟨r, s, hrs⟩ :=
        (IntermediateField.mem_adjoin_simple_iff k (α := j) ((g i : F))).mp (g i).2
      by_cases hs : Polynomial.aeval j s = 0
      · exact ⟨0, 1, one_ne_zero, by rw [hrs, hs, div_zero, zero_mul, map_zero]⟩
      · exact ⟨r, s, fun h => hs (by rw [h, map_zero]), by rw [hrs, div_mul_cancel₀ _ hs]⟩
    choose r s hs0 hcl using hrep
    simp only [IntermediateField.smul_def, smul_eq_mul] at hg
    have hsum : (∑ i : Fin n,
        Polynomial.aeval j (r i * ∏ l ∈ Finset.univ.erase i, s l) * b i) = 0 := by
      calc ∑ i : Fin n, Polynomial.aeval j (r i * ∏ l ∈ Finset.univ.erase i, s l) * b i
          = ∑ i : Fin n, ((g i : F) * b i) * ∏ l : Fin n, Polynomial.aeval j (s l) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_mul, map_prod, ← hcl i,
              ← Finset.mul_prod_erase Finset.univ (fun l => Polynomial.aeval j (s l))
                (Finset.mem_univ i)]
            ring
        _ = (∑ i : Fin n, (g i : F) * b i) * ∏ l : Fin n, Polynomial.aeval j (s l) := by
            rw [Finset.sum_mul]
        _ = 0 := by rw [hg, zero_mul]
    intro i
    have hri := hbli _ hsum i
    have hprodne : (∏ l ∈ Finset.univ.erase i, s l) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun l _ => hs0 l
    have hr0 : r i = 0 := by
      rcases mul_eq_zero.mp hri with h | h
      · exact h
      · exact absurd h hprodne
    have hcli := hcl i
    rw [hr0, map_zero] at hcli
    rcases mul_eq_zero.mp hcli with h | h
    · exact Subtype.ext (by simpa using h)
    · exact absurd h (hane (hs0 i))
  have hsp : ⊤ ≤ Submodule.span (IntermediateField.adjoin k ({j} : Set F)) (Set.range b) := by
    intro x _
    obtain ⟨q, c, hq, heq⟩ := hbsp x
    have hQ : Polynomial.aeval j q ≠ 0 := hane hq
    have hx : x = ∑ i : Fin n,
        ((⟨Polynomial.aeval j (c i) * (Polynomial.aeval j q)⁻¹,
          mul_mem (haev (c i)) (inv_mem (haev q))⟩ :
            IntermediateField.adjoin k ({j} : Set F)) • b i) := by
      simp only [IntermediateField.smul_def, smul_eq_mul]
      calc x = (x * Polynomial.aeval j q) * (Polynomial.aeval j q)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hQ, mul_one]
        _ = (∑ i : Fin n, Polynomial.aeval j (c i) * b i) * (Polynomial.aeval j q)⁻¹ := by
              rw [heq]
        _ = ∑ i : Fin n, Polynomial.aeval j (c i) * (Polynomial.aeval j q)⁻¹ * b i := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ => by ring
    rw [hx]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, funext fun i => by rw [Module.Basis.coe_mk]⟩

private theorem mwALGM_gram_denom {j : F} (hj : Transcendental k j)
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F]
    (n : ℕ) (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'') :
    ∃ Δ : Polynomial K₀, Δ ≠ 0 ∧ ∀ x : F, IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ c : Fin n → Polynomial k,
        Polynomial.aeval j (Δ.map (algebraMap K₀ k)) * x
          = ∑ i : Fin n, Polynomial.aeval j (c i)
              * (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i) := by
  exact AlgebraicCurve.Place.exists_gram_denominator_of_mulTable hj n b hbli hbsp d hd A hmul

end gstar

section enum

variable {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]

private theorem mwALGM_isIntegral_aeval (j : F) (p : Polynomial k) :
    IsIntegral (Algebra.adjoin k ({j} : Set F)) (Polynomial.aeval j p) := by
  have hmem : Polynomial.aeval j p ∈ Algebra.adjoin k ({j} : Set F) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  exact isIntegral_algebraMap (x := (⟨_, hmem⟩ : Algebra.adjoin k ({j} : Set F)))

open scoped Classical in

private theorem mwALGM_exists_enum (S : Finset (Place k F)) (m : Place k F → ℕ) :
    ∃ (r : ℕ) (pt : Fin r → Place k F),
      (∀ t, pt t ∈ S) ∧
      (∀ v : Place k F, ((∑ t, Finsupp.single (pt t) (1 : ℤ) : Divisor k F) v)
        = if v ∈ S then (m v : ℤ) else 0) ∧
      r = ∑ v ∈ S, m v := by
  classical
  induction S using Finset.induction with
  | empty =>
    refine ⟨0, Fin.elim0, fun t => t.elim0, fun v => ?_, by simp⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, if_neg (Finset.notMem_empty v)]
    simp
  | insert a s ha ih =>
    obtain ⟨r, pt, hmem, hcount, hr⟩ := ih
    refine ⟨m a + r, Fin.append (fun _ => a) pt, ?_, ?_, ?_⟩
    · intro t
      refine Fin.addCases (fun i => ?_) (fun i => ?_) t
      · rw [Fin.append_left]
        exact Finset.mem_insert_self a s
      · rw [Fin.append_right]
        exact Finset.mem_insert_of_mem (hmem i)
    · intro v
      have hsplit : (∑ t : Fin (m a + r), Finsupp.single (Fin.append (fun _ => a) pt t) (1 : ℤ)
          : Divisor k F)
          = (Finsupp.single a (m a : ℤ) : Divisor k F)
            + ∑ t : Fin r, Finsupp.single (pt t) (1 : ℤ) := by
        rw [Fin.sum_univ_add]
        congr 1
        · have h1 : ∀ i : Fin (m a), Finsupp.single
              (Fin.append (fun _ => a) pt (Fin.castAdd r i)) (1 : ℤ) = Finsupp.single a 1 := by
            intro i
            rw [Fin.append_left]
          rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, Finsupp.smul_single, nsmul_eq_mul, mul_one]
        · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_right]
      rw [hsplit, Finsupp.add_apply, hcount v, Finsupp.single_apply]
      by_cases hv : v = a
      · subst hv
        rw [if_pos rfl, if_pos (Finset.mem_insert_self v s), if_neg ha, add_zero]
      · rw [if_neg fun h => hv h.symm, zero_add]
        by_cases hvs : v ∈ s
        · rw [if_pos hvs, if_pos (Finset.mem_insert_of_mem hvs)]
        · rw [if_neg hvs, if_neg fun h => (Finset.mem_insert.mp h).elim hv hvs]
    · rw [hr, Finset.sum_insert ha]

private theorem mwALGM_enum {j : F} (hj : Transcendental k j)
    (hrat : ∀ (v : Place k F) (x : F), j ∈ v.toValuationSubring →
      IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ c : k, x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c))
    (n : ℕ) (b : Fin n → F)
    (d : Polynomial K₀) (hd : d ≠ 0)
    (hIdb : ∀ i : Fin n, IsIntegral (Algebra.adjoin k ({j} : Set F))
      (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i))
    (Θ : Polynomial K₀) (hΘ : Θ ≠ 0) (hdΘ : d ∣ Θ)
    (a : ℕ) (cL₀ : Fin a → Polynomial K₀) (cL : Fin a → Fin n → Polynomial K₀)
    (hcLd : ∀ s i, d ∣ cL s i)
    (hLnc : ∀ (s : Fin a) (c : k), (Polynomial.aeval j ((cL₀ s).map (algebraMap K₀ k))
      + ∑ i : Fin n, Polynomial.aeval j ((cL s i).map (algebraMap K₀ k)) * b i)
        ≠ algebraMap k F c)
    (hdegnz : ∀ v : Place k F, v.deg ≠ 0)
    (g : ℕ) (D : Divisor k F) (heff : ∀ v, 0 ≤ D v)
    (hdeg : Divisor.degree D = (g : ℤ)) :
    ∃ (r : ℕ) (_ : r ≤ g) (pt : Fin r → Place k F)
      (val : Fin r × Fin (a + 1) → k) (βpt : Fin r → Fin n → k)
      (r' : ℕ) (pt' : Fin r' → Place k F) (jv' : Fin r' → k),
      (∀ t, 0 ≤ (pt t).ord j ∧
        (pt t).ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) = 0) ∧
      (∀ t', 0 < (pt' t').ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k)))) ∧
      (∀ v : Place k F, 0 ≤ v.ord j → D v =
        ((∑ t, Finsupp.single (pt t) (1 : ℤ))
          + ∑ t', Finsupp.single (pt' t') (1 : ℤ) : Divisor k F) v) ∧
      (∀ t, 0 < (pt t).ord (j - algebraMap k F (val (t, 0)))) ∧
      (∀ t (s : Fin a), 0 < (pt t).ord
        ((Polynomial.aeval j ((cL₀ s).map (algebraMap K₀ k))
          + ∑ i : Fin n, Polynomial.aeval j ((cL s i).map (algebraMap K₀ k)) * b i)
          - algebraMap k F (val (t, s.succ)))) ∧
      (∀ t', 0 < (pt' t').ord (j - algebraMap k F (jv' t'))) ∧
      (∀ t i, Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i = algebraMap k F (βpt t i) ∨
        0 < (pt t).ord (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i
          - algebraMap k F (βpt t i))) ∧
      (∀ t, (pt t).ord (Polynomial.aeval j (d.map (algebraMap K₀ k))) = 0) := by
  classical
  set φ : K₀ →+* k := algebraMap K₀ k with hφ
  set ΘF : F := Polynomial.aeval j (Θ.map φ) with hΘF
  have hjne : j ≠ 0 := fun h0 => hj (h0 ▸ isAlgebraic_zero)

  have hmemj : ∀ v : Place k F, 0 ≤ v.ord j → j ∈ v.toValuationSubring :=
    fun v hv => v.mem_of_ord_nonneg hjne hv
  have hΘreg : ∀ v : Place k F, 0 ≤ v.ord j → 0 ≤ v.ord ΘF := by
    intro v hv
    exact v.ord_nonneg_of_mem (mwALGM_aeval_mem v (hmemj v hv) _)

  set Sg : Finset (Place k F) :=
    D.support.filter (fun v => 0 ≤ v.ord j ∧ v.ord ΘF = 0) with hSg
  set Sb : Finset (Place k F) :=
    D.support.filter (fun v => 0 ≤ v.ord j ∧ 0 < v.ord ΘF) with hSb
  obtain ⟨r, pt, hptS, hptc, hrsum⟩ := mwALGM_exists_enum Sg (fun v => (D v).toNat)
  obtain ⟨r', pt', hptS', hptc', -⟩ := mwALGM_exists_enum Sb (fun v => (D v).toNat)

  have hptg : ∀ t, 0 ≤ (pt t).ord j ∧ (pt t).ord ΘF = 0 :=
    fun t => (Finset.mem_filter.mp (hptS t)).2
  have hptb : ∀ t', 0 ≤ (pt' t').ord j ∧ 0 < (pt' t').ord ΘF :=
    fun t' => (Finset.mem_filter.mp (hptS' t')).2

  have hrle : r ≤ g := by
    have h1 : (∑ v ∈ Sg, ((D v).toNat : ℤ)) ≤ (g : ℤ) := by
      rw [← hdeg]
      have hdegsum : Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := rfl
      rw [hdegsum]
      calc ∑ v ∈ Sg, ((D v).toNat : ℤ)
          = ∑ v ∈ Sg, D v := Finset.sum_congr rfl fun v _ =>
            Int.toNat_of_nonneg (heff v)
        _ ≤ ∑ v ∈ D.support, D v :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun v _ _ => heff v)
        _ ≤ ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
            refine Finset.sum_le_sum fun v _ => ?_
            refine le_mul_of_one_le_right (heff v) ?_
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hdegnz v)
    rw [hrsum]
    exact_mod_cast (by push_cast at h1 ⊢; exact h1 :
      ((∑ v ∈ Sg, (D v).toNat : ℕ) : ℤ) ≤ (g : ℤ))

  have hjint : IsIntegral (Algebra.adjoin k ({j} : Set F)) j := mwALGM_isIntegral_j
  have hLint : ∀ s : Fin a, IsIntegral (Algebra.adjoin k ({j} : Set F))
      (Polynomial.aeval j ((cL₀ s).map φ)
        + ∑ i : Fin n, Polynomial.aeval j ((cL s i).map φ) * b i) := by
    intro s
    refine (mwALGM_isIntegral_aeval j _).add (IsIntegral.sum _ fun i _ => ?_)
    obtain ⟨e, he⟩ := hcLd s i
    rw [he, Polynomial.map_mul, map_mul]
    rw [show Polynomial.aeval j (d.map φ) * Polynomial.aeval j (e.map φ) * b i
        = Polynomial.aeval j (e.map φ) * (Polynomial.aeval j (d.map φ) * b i) from by ring]
    exact (mwALGM_isIntegral_aeval j _).mul (hIdb i)
  have hjpin : ∀ t, ∃ c : k, 0 < (pt t).ord (j - algebraMap k F c) := by
    intro t
    obtain ⟨c, hc⟩ := hrat (pt t) j (hmemj _ (hptg t).1) hjint
    exact ⟨c, hc.resolve_left fun h => hj (h ▸ isAlgebraic_algebraMap c)⟩
  have hLpin : ∀ (t : Fin r) (s : Fin a), ∃ c : k,
      0 < (pt t).ord ((Polynomial.aeval j ((cL₀ s).map φ)
        + ∑ i : Fin n, Polynomial.aeval j ((cL s i).map φ) * b i) - algebraMap k F c) := by
    intro t s
    obtain ⟨c, hc⟩ := hrat (pt t) _ (hmemj _ (hptg t).1) (hLint s)
    exact ⟨c, hc.resolve_left (hLnc s c)⟩
  have hβpin : ∀ (t : Fin r) (i : Fin n), ∃ c : k,
      Polynomial.aeval j (d.map φ) * b i = algebraMap k F c ∨
        0 < (pt t).ord (Polynomial.aeval j (d.map φ) * b i - algebraMap k F c) :=
    fun t i => hrat (pt t) _ (hmemj _ (hptg t).1) (hIdb i)
  have hjpin' : ∀ t', ∃ c : k, 0 < (pt' t').ord (j - algebraMap k F c) := by
    intro t'
    obtain ⟨c, hc⟩ := hrat (pt' t') j (hmemj _ (hptb t').1) hjint
    exact ⟨c, hc.resolve_left fun h => hj (h ▸ isAlgebraic_algebraMap c)⟩
  choose jc hjc using hjpin
  choose Lc hLc using hLpin
  choose βc hβc using hβpin
  choose jc' hjc' using hjpin'

  have hdunit : ∀ t, (pt t).ord (Polynomial.aeval j (d.map φ)) = 0 := by
    intro t
    obtain ⟨h, hΘeq⟩ := hdΘ
    have hh0 : h ≠ 0 := fun h0 => hΘ (by rw [hΘeq, h0, mul_zero])
    have hdj0 : Polynomial.aeval j (d.map φ) ≠ 0 := fun h0 =>
      hj ⟨d.map φ, (Polynomial.map_ne_zero_iff φ.injective).mpr hd, h0⟩
    have hhj0 : Polynomial.aeval j (h.map φ) ≠ 0 := fun h0 =>
      hj ⟨h.map φ, (Polynomial.map_ne_zero_iff φ.injective).mpr hh0, h0⟩
    have hsplit : (pt t).ord ΘF
        = (pt t).ord (Polynomial.aeval j (d.map φ)) + (pt t).ord (Polynomial.aeval j (h.map φ)) := by
      rw [hΘF, hΘeq, Polynomial.map_mul, map_mul]
      exact (pt t).ord_mul hdj0 hhj0
    have h1 : 0 ≤ (pt t).ord (Polynomial.aeval j (d.map φ)) :=
      (pt t).ord_nonneg_of_mem (mwALGM_aeval_mem _ (hmemj _ (hptg t).1) _)
    have h2 : 0 ≤ (pt t).ord (Polynomial.aeval j (h.map φ)) :=
      (pt t).ord_nonneg_of_mem (mwALGM_aeval_mem _ (hmemj _ (hptg t).1) _)
    have h3 := (hptg t).2
    omega

  refine ⟨r, hrle, pt, fun ts => Fin.cases (jc ts.1) (fun s => Lc ts.1 s) ts.2, βc,
    r', pt', jc', hptg, fun t' => (hptb t').2, ?_, ?_, ?_, hjc', hβc, hdunit⟩
  ·
    intro v hv
    rw [Finsupp.add_apply, hptc v, hptc' v]
    by_cases hvD : D v = 0
    · have hg : v ∉ Sg := fun hmem => by
        have := (Finset.mem_filter.mp hmem).1
        rw [Finsupp.mem_support_iff] at this
        exact this hvD
      have hb : v ∉ Sb := fun hmem => by
        have := (Finset.mem_filter.mp hmem).1
        rw [Finsupp.mem_support_iff] at this
        exact this hvD
      rw [if_neg hg, if_neg hb, add_zero, hvD]
    · have hsupp : v ∈ D.support := Finsupp.mem_support_iff.mpr hvD
      rcases lt_or_eq_of_le (hΘreg v hv) with hpos | hzero
      · have hg : v ∉ Sg := fun hmem => by
          have := (Finset.mem_filter.mp hmem).2.2
          omega
        have hb : v ∈ Sb := Finset.mem_filter.mpr ⟨hsupp, hv, hpos⟩
        rw [if_neg hg, if_pos hb, Int.toNat_of_nonneg (heff v), zero_add]
      · have hg : v ∈ Sg := Finset.mem_filter.mpr ⟨hsupp, hv, hzero.symm⟩
        have hb : v ∉ Sb := fun hmem => by
          have := (Finset.mem_filter.mp hmem).2.2
          omega
        rw [if_pos hg, if_neg hb, Int.toNat_of_nonneg (heff v), add_zero]
  ·
    intro t
    exact hjc t
  ·
    intro t s
    exact hLc t s

end enum

section eexpand

variable {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]

private theorem mwALGM_Eexpand {j : F}
    (n : ℕ) (b : Fin n → F) (dj : F) (hdj : dj ≠ 0)
    (mdeg r : ℕ) (L : F) (Mp : Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hpow : ∀ (m : ℕ) (i : Fin n), L ^ m * (dj * b i)
      = ∑ i' : Fin n, Polynomial.aeval j (((Mp ^ m) i' i).map (algebraMap K₀ k)) * (dj * b i'))
    (w : Fin r → k) (u : Fin n × Fin (mdeg + 1) → k) :
    (∏ t : Fin r, (L - algebraMap k F (w t)))
      * (∑ i : Fin n, Polynomial.aeval j
          (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
    = ∑ i' : Fin n, Polynomial.aeval j
        (∑ col : Fin n × Fin (mdeg + 1), Polynomial.C (u col)
          * ((∑ m : Fin (r + 1),
                Polynomial.C ((∏ t : Fin r, (Polynomial.X - Polynomial.C (w t))).coeff (m : ℕ))
                * ((Mp ^ (m : ℕ)) i' col.1).map (algebraMap K₀ k))
              * Polynomial.X ^ ((col.2 : Fin (mdeg + 1)) : ℕ))) * b i' := by
  classical
  set φ : K₀ →+* k := algebraMap K₀ k with hφ
  set P : Polynomial k := ∏ t : Fin r, (Polynomial.X - Polynomial.C (w t)) with hPdef

  have hLmb : ∀ (m : ℕ) (i : Fin n), L ^ m * b i
      = ∑ i' : Fin n, Polynomial.aeval j (((Mp ^ m) i' i).map φ) * b i' := by
    intro m i
    have h' : dj * (L ^ m * b i)
        = dj * (∑ i' : Fin n, Polynomial.aeval j (((Mp ^ m) i' i).map φ) * b i') := by
      rw [show dj * (L ^ m * b i) = L ^ m * (dj * b i) from by ring, hpow m i, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i' _ => by ring
    exact mul_left_cancel₀ hdj h'

  have hdegP : P.natDegree < r + 1 := by
    rw [hPdef]
    refine Nat.lt_succ_of_le (le_trans (Polynomial.natDegree_prod_le _ _) ?_)
    refine le_trans (Finset.sum_le_sum fun t _ => Polynomial.natDegree_X_sub_C_le (w t)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hprod : (∏ t : Fin r, (L - algebraMap k F (w t)))
      = ∑ m : Fin (r + 1), algebraMap k F (P.coeff (m : ℕ)) * L ^ (m : ℕ) := by
    have h1 : (∏ t : Fin r, (L - algebraMap k F (w t))) = Polynomial.aeval L P := by
      rw [hPdef, map_prod]
      exact Finset.prod_congr rfl fun t _ => by
        rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [h1, Polynomial.aeval_eq_sum_range' hdegP, Fin.sum_univ_eq_sum_range
      (fun m => algebraMap k F (P.coeff m) * L ^ m)]
    exact Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _

  rw [hprod, Finset.sum_mul]
  have hterm : ∀ m : Fin (r + 1),
      (algebraMap k F (P.coeff (m : ℕ)) * L ^ (m : ℕ))
        * (∑ i : Fin n, Polynomial.aeval j
            (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
      = ∑ i' : Fin n, ∑ i : Fin n, ∑ dd : Fin (mdeg + 1),
          algebraMap k F (u (i, dd)) * (j ^ (dd : ℕ)
            * (algebraMap k F (P.coeff (m : ℕ))
              * (Polynomial.aeval j (((Mp ^ (m : ℕ)) i' i).map φ) * b i'))) := by
    intro m
    rw [Finset.mul_sum]
    have hswap : ∀ i : Fin n,
        (algebraMap k F (P.coeff (m : ℕ)) * L ^ (m : ℕ))
          * (Polynomial.aeval j
              (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
        = ∑ i' : Fin n, ∑ dd : Fin (mdeg + 1),
            algebraMap k F (u (i, dd)) * (j ^ (dd : ℕ)
              * (algebraMap k F (P.coeff (m : ℕ))
                * (Polynomial.aeval j (((Mp ^ (m : ℕ)) i' i).map φ) * b i'))) := by
      intro i
      have haev : Polynomial.aeval j
          (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ))
          = ∑ dd : Fin (mdeg + 1), algebraMap k F (u (i, dd)) * j ^ (dd : ℕ) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun dd _ => by
          rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      calc (algebraMap k F (P.coeff (m : ℕ)) * L ^ (m : ℕ))
            * (Polynomial.aeval j
                (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
          = Polynomial.aeval j
                (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ))
              * (algebraMap k F (P.coeff (m : ℕ)) * (L ^ (m : ℕ) * b i)) := by ring
        _ = (∑ dd : Fin (mdeg + 1), algebraMap k F (u (i, dd)) * j ^ (dd : ℕ))
              * (algebraMap k F (P.coeff (m : ℕ))
                * (∑ i' : Fin n, Polynomial.aeval j (((Mp ^ (m : ℕ)) i' i).map φ) * b i')) := by
            rw [haev, hLmb m i]
        _ = ∑ dd : Fin (mdeg + 1), ∑ i' : Fin n,
              algebraMap k F (u (i, dd)) * (j ^ (dd : ℕ)
                * (algebraMap k F (P.coeff (m : ℕ))
                  * (Polynomial.aeval j (((Mp ^ (m : ℕ)) i' i).map φ) * b i'))) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun dd _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i' _ => ?_
            ring
        _ = ∑ i' : Fin n, ∑ dd : Fin (mdeg + 1),
              algebraMap k F (u (i, dd)) * (j ^ (dd : ℕ)
                * (algebraMap k F (P.coeff (m : ℕ))
                  * (Polynomial.aeval j (((Mp ^ (m : ℕ)) i' i).map φ) * b i'))) :=
            Finset.sum_comm
    rw [Finset.sum_congr rfl fun i _ => hswap i]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun m _ => hterm m]

  have hrhs : ∀ i' : Fin n,
      Polynomial.aeval j
        (∑ col : Fin n × Fin (mdeg + 1), Polynomial.C (u col)
          * ((∑ m : Fin (r + 1),
                Polynomial.C (P.coeff (m : ℕ)) * ((Mp ^ (m : ℕ)) i' col.1).map φ)
              * Polynomial.X ^ (col.2 : ℕ))) * b i'
      = ∑ m : Fin (r + 1), ∑ i : Fin n, ∑ dd : Fin (mdeg + 1),
          algebraMap k F (u (i, dd)) * (j ^ (dd : ℕ)
            * (algebraMap k F (P.coeff (m : ℕ))
              * (Polynomial.aeval j (((Mp ^ (m : ℕ)) i' i).map φ) * b i'))) := by
    intro i'
    rw [map_sum, Finset.sum_mul]
    have hcol : ∀ col : Fin n × Fin (mdeg + 1),
        Polynomial.aeval j (Polynomial.C (u col)
          * ((∑ m : Fin (r + 1),
                Polynomial.C (P.coeff (m : ℕ)) * ((Mp ^ (m : ℕ)) i' col.1).map φ)
              * Polynomial.X ^ (col.2 : ℕ))) * b i'
        = ∑ m : Fin (r + 1),
            algebraMap k F (u (col.1, col.2)) * (j ^ (col.2 : ℕ)
              * (algebraMap k F (P.coeff (m : ℕ))
                * (Polynomial.aeval j (((Mp ^ (m : ℕ)) i' col.1).map φ) * b i'))) := by
      intro col
      have hS : Polynomial.aeval j
          (∑ m : Fin (r + 1), Polynomial.C (P.coeff (m : ℕ)) * ((Mp ^ (m : ℕ)) i' col.1).map φ)
          = ∑ m : Fin (r + 1),
              algebraMap k F (P.coeff (m : ℕ))
                * Polynomial.aeval j (((Mp ^ (m : ℕ)) i' col.1).map φ) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun m _ => by rw [map_mul, Polynomial.aeval_C]
      rw [map_mul, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, hS,
        Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [Finset.sum_congr rfl fun col _ => hcol col, Fintype.sum_prod_type]
    exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
  rw [Finset.sum_congr rfl fun i' _ => hrhs i']
  exact Finset.sum_comm

end eexpand

section kerchow

variable {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]

private theorem mwALGM_ord_prod (v : Place k F) {ι : Type*} (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i ≠ 0) : v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, v.ord_one]
  | cons a t ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      v.ord_mul (hf a (Finset.mem_cons_self a t))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_cons_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_cons_of_mem hi)]

open scoped Classical in

private theorem mwALGM_sum_single_apply {m : ℕ} (p : Fin m → Place k F) (w : Place k F) :
    ((∑ t, Finsupp.single (p t) (1 : ℤ) : Divisor k F)) w
      = ∑ t, if p t = w then (1 : ℤ) else 0 := by
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun t _ => Finsupp.single_apply

private theorem mwALGM_ker_chow {j : F} (hj : Transcendental k j)
    (n : ℕ) (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (d : Polynomial K₀) (hd : d ≠ 0) (Δ : Polynomial K₀) (hΔ : Δ ≠ 0)
    (q₀ : Polynomial K₀) (hq₀ : q₀ ≠ 0) (Θ : Polynomial K₀) (hΘ : Θ = Δ * d * q₀)
    (v₀ : Place k F) (e : ℕ) (D : Divisor k F)
    (a : ℕ) {r : ℕ} (pt : Fin r → Place k F) (val : Fin r × Fin (a + 1) → k)
    {r' : ℕ} (pt' : Fin r' → Place k F) (jv' : Fin r' → k)
    (hpt : ∀ t, 0 ≤ (pt t).ord j ∧
      (pt t).ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) = 0)
    (henum : ∀ v : Place k F, 0 ≤ v.ord j → D v =
      ((∑ t, Finsupp.single (pt t) (1 : ℤ))
        + ∑ t', Finsupp.single (pt' t') (1 : ℤ) : Divisor k F) v)
    (hval0 : ∀ t, 0 < (pt t).ord (j - algebraMap k F (val (t, 0))))
    (L : Fin a → F)
    (hLreg : ∀ (s : Fin a) (v : Place k F), j ∈ v.toValuationSubring →
      L s ∈ v.toValuationSubring)
    (hvalL : ∀ t (s : Fin a), 0 < (pt t).ord (L s - algebraMap k F (val (t, s.succ))))
    (hjv' : ∀ t', 0 < (pt' t').ord (j - algebraMap k F (jv' t')))
    (gU : F) (E : Fin a → Fin n → Polynomial k)
    (hE : ∀ s : Fin a, (∏ t : Fin r, (L s - algebraMap k F (val (t, s.succ)))) * gU
      = ∑ i' : Fin n, Polynomial.aeval j (E s i') * b i')
    (hord : ∀ v : Place k F,
      0 ≤ (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v
        + v.ord (gU * (Polynomial.aeval j
            ((∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))))
              * (∏ t', (Polynomial.X - Polynomial.C (jv' t')))
              * q₀.map (algebraMap K₀ k)))⁻¹))
    (hNB : ∀ S : Polynomial k, S ≠ 0 → IsCoprime S (Δ.map (algebraMap K₀ k)) →
      ∀ (N g : F) (E' : Fin n → Polynomial k),
        N * g = ∑ i : Fin n, Polynomial.aeval j (E' i) * b i →
        (∀ v : Place k F, j ∈ v.toValuationSubring →
          Polynomial.aeval j (d.map (algebraMap K₀ k)) * N * g
            * (Polynomial.aeval j S)⁻¹ ∈ v.toValuationSubring) →
        ∃ q : Fin n → Polynomial k, ∀ i, E' i = S * q i) :
    ∀ (s : Fin a) (i' : Fin n),
      (∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0)))) ∣ E s i' := by
  classical
  intro s i'
  rcases eq_or_ne gU 0 with hgU | hgU
  · have h0 : (∑ i'' : Fin n, Polynomial.aeval j (E s i'') * b i'') = 0 := by
      rw [← hE s, hgU, mul_zero]
    rw [hbli (E s) h0 i']
    exact dvd_zero _
  set φk : K₀ →+* k := algebraMap K₀ k with hφk
  have hane : ∀ {p : Polynomial k}, p ≠ 0 → Polynomial.aeval j p ≠ 0 :=
    fun {p} hp h => hj ⟨p, hp, h⟩
  have hφinj : Function.Injective φk := (algebraMap K₀ k).injective
  have hj0 : j ≠ 0 := fun h =>
    hj (h ▸ ((map_zero (algebraMap k F)) ▸ isAlgebraic_algebraMap (0 : k)))
  have hdm : d.map φk ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hd
  have hΔm : Δ.map φk ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hΔ
  have hq₀m : q₀.map φk ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hq₀
  set S : Polynomial k := ∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))) with hSdef
  set S' : Polynomial k := ∏ t', (Polynomial.X - Polynomial.C (jv' t')) with hS'def
  have hS0 : S ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => Polynomial.X_sub_C_ne_zero _
  have hS'0 : S' ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t' _ => Polynomial.X_sub_C_ne_zero _
  have hfne : ∀ t : Fin r, L s - algebraMap k F (val (t, s.succ)) ≠ 0 := by
    intro t h0
    have h1 := hvalL t s
    rw [h0, (pt t).ord_zero] at h1
    exact lt_irrefl 0 h1
  have hNts : (∏ t : Fin r, (L s - algebraMap k F (val (t, s.succ)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun t _ => hfne t

  have hcop : IsCoprime S (Δ.map φk) := by
    rw [hSdef]
    refine IsCoprime.prod_left fun t _ => ?_
    refine (Polynomial.irreducible_X_sub_C (val (t, 0))).coprime_iff_not_dvd.mpr ?_
    intro hdvd
    obtain ⟨h, hh⟩ := hdvd
    have hh0 : h ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hh; exact hΔm hh
    have hjmem : j ∈ (pt t).toValuationSubring :=
      (pt t).mem_of_ord_nonneg hj0 (hpt t).1
    have hsubne : j - algebraMap k F (val (t, 0)) ≠ 0 := by
      intro h0
      have h1 := hval0 t
      rw [h0, (pt t).ord_zero] at h1
      exact lt_irrefl 0 h1
    have hordΔ : 0 < (pt t).ord (Polynomial.aeval j (Δ.map φk)) := by
      have hΔj : Polynomial.aeval j (Δ.map φk)
          = (j - algebraMap k F (val (t, 0))) * Polynomial.aeval j h := by
        rw [hh, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [hΔj, (pt t).ord_mul hsubne (hane hh0)]
      have h2 : (0 : ℤ) ≤ (pt t).ord (Polynomial.aeval j h) :=
        (pt t).ord_nonneg_of_mem (mwALGM_aeval_mem (pt t) hjmem h)
      have h3 := hval0 t
      linarith
    have hΘm : Polynomial.aeval j (Θ.map φk)
        = Polynomial.aeval j (Δ.map φk) * Polynomial.aeval j (d.map φk)
          * Polynomial.aeval j (q₀.map φk) := by
      rw [hΘ, Polynomial.map_mul, Polynomial.map_mul, map_mul, map_mul]
    have hd0 : (0 : ℤ) ≤ (pt t).ord (Polynomial.aeval j (d.map φk)) :=
      (pt t).ord_nonneg_of_mem (mwALGM_aeval_mem (pt t) hjmem _)
    have hq0 : (0 : ℤ) ≤ (pt t).ord (Polynomial.aeval j (q₀.map φk)) :=
      (pt t).ord_nonneg_of_mem (mwALGM_aeval_mem (pt t) hjmem _)
    have hsplit : (pt t).ord (Polynomial.aeval j (Θ.map φk))
        = (pt t).ord (Polynomial.aeval j (Δ.map φk))
          + (pt t).ord (Polynomial.aeval j (d.map φk))
          + (pt t).ord (Polynomial.aeval j (q₀.map φk)) := by
      rw [hΘm, (pt t).ord_mul (mul_ne_zero (hane hΔm) (hane hdm)) (hane hq₀m),
        (pt t).ord_mul (hane hΔm) (hane hdm)]
    have hΘ0 := (hpt t).2
    linarith

  have hx : ∀ v : Place k F, j ∈ v.toValuationSubring →
      Polynomial.aeval j (d.map φk)
        * (∏ t : Fin r, (L s - algebraMap k F (val (t, s.succ)))) * gU
        * (Polynomial.aeval j S)⁻¹ ∈ v.toValuationSubring := by
    intro v hjv
    have hordj : (0 : ℤ) ≤ v.ord j := v.ord_nonneg_of_mem hjv
    have hDv := henum v hordj
    rw [Finsupp.add_apply, mwALGM_sum_single_apply pt v, mwALGM_sum_single_apply pt' v] at hDv

    have hbN : (∑ t : Fin r, if pt t = v then (1 : ℤ) else 0)
        ≤ v.ord (∏ t : Fin r, (L s - algebraMap k F (val (t, s.succ)))) := by
      rw [mwALGM_ord_prod v Finset.univ _ fun t _ => hfne t]
      refine Finset.sum_le_sum fun t _ => ?_
      by_cases h : pt t = v
      · rw [if_pos h]
        have h1 := hvalL t s
        rw [h] at h1
        omega
      · rw [if_neg h]
        exact v.ord_nonneg_of_mem (sub_mem (hLreg s v hjv) (v.algebraMap_mem' _))

    have hfne' : ∀ t' : Fin r', j - algebraMap k F (jv' t') ≠ 0 := by
      intro t' h0
      have h1 := hjv' t'
      rw [h0, (pt' t').ord_zero] at h1
      exact lt_irrefl 0 h1
    have hS'j : Polynomial.aeval j S' = ∏ t', (j - algebraMap k F (jv' t')) := by
      rw [hS'def, map_prod]
      exact Finset.prod_congr rfl fun t' _ => by
        rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    have hbS' : (∑ t' : Fin r', if pt' t' = v then (1 : ℤ) else 0)
        ≤ v.ord (Polynomial.aeval j S') := by
      rw [hS'j, mwALGM_ord_prod v Finset.univ _ fun t' _ => hfne' t']
      refine Finset.sum_le_sum fun t' _ => ?_
      by_cases h : pt' t' = v
      · rw [if_pos h]
        have h1 := hjv' t'
        rw [h] at h1
        omega
      · rw [if_neg h]
        exact v.ord_nonneg_of_mem (sub_mem hjv (v.algebraMap_mem' _))

    have hordv := hord v
    rw [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] at hordv
    have haS : Polynomial.aeval j (S * S' * q₀.map φk)
        = Polynomial.aeval j S * Polynomial.aeval j S' * Polynomial.aeval j (q₀.map φk) := by
      rw [map_mul, map_mul]
    have hsplit2 : v.ord (gU * (Polynomial.aeval j (S * S' * q₀.map φk))⁻¹)
        = v.ord gU - v.ord (Polynomial.aeval j S) - v.ord (Polynomial.aeval j S')
          - v.ord (Polynomial.aeval j (q₀.map φk)) := by
      rw [v.ord_mul hgU
          (inv_ne_zero (hane (mul_ne_zero (mul_ne_zero hS0 hS'0) hq₀m))),
        v.ord_inv, haS,
        v.ord_mul (mul_ne_zero (hane hS0) (hane hS'0)) (hane hq₀m),
        v.ord_mul (hane hS0) (hane hS'0)]
      ring
    rw [hsplit2] at hordv
    have hd0 : (0 : ℤ) ≤ v.ord (Polynomial.aeval j (d.map φk)) :=
      v.ord_nonneg_of_mem (mwALGM_aeval_mem v hjv _)
    have hq0 : (0 : ℤ) ≤ v.ord (Polynomial.aeval j (q₀.map φk)) :=
      v.ord_nonneg_of_mem (mwALGM_aeval_mem v hjv _)
    have hδe : (0 : ℤ) ≤ (e : ℤ) * (if v₀ = v then (1 : ℤ) else 0) := by
      split_ifs with h
      · simp
      · simp
    refine v.mem_of_ord_nonneg
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (hane hdm) hNts) hgU)
        (inv_ne_zero (hane hS0))) ?_
    have htgt : v.ord (Polynomial.aeval j (d.map φk)
          * (∏ t : Fin r, (L s - algebraMap k F (val (t, s.succ)))) * gU
          * (Polynomial.aeval j S)⁻¹)
        = v.ord (Polynomial.aeval j (d.map φk))
          + v.ord (∏ t : Fin r, (L s - algebraMap k F (val (t, s.succ)))) + v.ord gU
          - v.ord (Polynomial.aeval j S) := by
      rw [v.ord_mul (mul_ne_zero (mul_ne_zero (hane hdm) hNts) hgU)
          (inv_ne_zero (hane hS0)),
        v.ord_mul (mul_ne_zero (hane hdm) hNts) hgU,
        v.ord_mul (hane hdm) hNts, v.ord_inv]
      ring
    rw [htgt]
    linarith
  obtain ⟨q, hq⟩ := hNB S hS0 hcop
    (∏ t : Fin r, (L s - algebraMap k F (val (t, s.succ)))) gU (E s) (hE s) hx
  exact ⟨q i', hq i'⟩

end kerchow

section theta

variable {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]

private theorem mwALGM_theta_choice {j : F} (hchar : CharZero K₀)
    (n : ℕ) (b : Fin n → F) (d : Polynomial K₀) (g : ℕ)
    (hNC : ∀ (β : Fin n → F) (θc : Fin (n + 1) → k), Function.Injective θc →
      ∃ s, ∀ c : k, (j + ∑ i : Fin n, algebraMap k F (θc s ^ (i.val + 1)) * β i)
        ≠ algebraMap k F c) :
    ∃ (θ : Fin (n * (g + 1) + 1) → K₀), Function.Injective θ ∧
      ∀ (s : Fin (n * (g + 1) + 1)) (c : k),
        (Polynomial.aeval j (Polynomial.X.map (algebraMap K₀ k))
          + ∑ i : Fin n, Polynomial.aeval j ((Polynomial.C (θ s ^ (i.val + 1)) * d).map
              (algebraMap K₀ k)) * b i)
          ≠ algebraMap k F c := by
  classical
  haveI : CharZero K₀ := hchar
  have hφinj : Function.Injective (algebraMap K₀ k) := (algebraMap K₀ k).injective
  have hpick : ∀ m : Fin (n * (g + 1) + 1), ∃ l : Fin (n + 1),
      ∀ c : k, (Polynomial.aeval j (Polynomial.X.map (algebraMap K₀ k))
        + ∑ i : Fin n, Polynomial.aeval j
            ((Polynomial.C (((((n + 1) * (m : ℕ) + (l : ℕ) : ℕ) : K₀)) ^ (i.val + 1)) * d).map
              (algebraMap K₀ k)) * b i)
        ≠ algebraMap k F c := by
    intro m
    have hcand : Function.Injective (fun l : Fin (n + 1) =>
        (algebraMap K₀ k) ((((n + 1) * (m : ℕ) + (l : ℕ) : ℕ) : K₀))) := by
      intro l l' h
      have h1 : (((n + 1) * (m : ℕ) + (l : ℕ) : ℕ) : K₀)
          = (((n + 1) * (m : ℕ) + (l' : ℕ) : ℕ) : K₀) := hφinj h
      have h2 : (n + 1) * (m : ℕ) + (l : ℕ) = (n + 1) * (m : ℕ) + (l' : ℕ) :=
        Nat.cast_injective h1
      exact Fin.ext (Nat.add_left_cancel h2)
    obtain ⟨l, hl⟩ := hNC (fun i => Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i) _ hcand
    refine ⟨l, fun c => ?_⟩
    have hform : (Polynomial.aeval j (Polynomial.X.map (algebraMap K₀ k))
        + ∑ i : Fin n, Polynomial.aeval j
            ((Polynomial.C (((((n + 1) * (m : ℕ) + (l : ℕ) : ℕ) : K₀)) ^ (i.val + 1)) * d).map
              (algebraMap K₀ k)) * b i)
        = (j + ∑ i : Fin n, algebraMap k F
            ((algebraMap K₀ k) ((((n + 1) * (m : ℕ) + (l : ℕ) : ℕ) : K₀)) ^ (i.val + 1))
              * (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i)) := by
      rw [Polynomial.map_X, Polynomial.aeval_X]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.map_mul, Polynomial.map_C, map_mul, Polynomial.aeval_C, map_pow, mul_assoc]
    rw [hform]
    exact hl c
  choose sel hsel using hpick
  refine ⟨fun m => ((((n + 1) * (m : ℕ) + (sel m : ℕ) : ℕ) : K₀)), ?_, ?_⟩
  · intro m m' h
    have h1 : (n + 1) * (m : ℕ) + (sel m : ℕ) = (n + 1) * (m' : ℕ) + (sel m' : ℕ) :=
      Nat.cast_injective h
    have key : ∀ mm : Fin (n * (g + 1) + 1),
        ((n + 1) * (mm : ℕ) + (sel mm : ℕ)) / (n + 1) = (mm : ℕ) := by
      intro mm
      rw [Nat.mul_add_div (Nat.succ_pos n), Nat.div_eq_of_lt (sel mm).isLt, add_zero]
    have h2 : (m : ℕ) = (m' : ℕ) := by
      rw [← key m, ← key m', h1]
    exact Fin.ext h2
  · intro s c
    exact hsel s c

end theta

end mwALGMdev

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.ord_zero Divisor Divisor.degree Place.ofHeightOneSpectrum Place.center Place.mem_center_iff_ord_pos Place.center_ne_bot Place.centerHeightOneSpectrum Place.deg_ne_zero_of_finiteDimensional_adjoin Place.exists_gram_denominator_of_mulTable Place.exists_uniformizing_separating_form"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap deg adicValuation ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_zpow ofHeightOneSpectrum algebraMap_mem' toValuationSubring mk ord_neg center mem_center_iff_ord_pos center_ne_bot centerHeightOneSpectrum toValuationSubring_eq_of_forall_mem mem_of_ord_nonneg ord_nonneg_of_mem min_ord_le_ord_add mem_toValuationSubring_of_isIntegral_adjoin deg_ne_zero_of_finiteDimensional_adjoin ord_eq_neg_log_of_valuationSubring_eq exists_gram_denominator_of_mulTable exists_uniformizing_separating_form"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem mwALGN_aeval_mem (v : Place k F) {j : F} (hjv : j ∈ v.toValuationSubring)
    (p : Polynomial k) : Polynomial.aeval j p ∈ v.toValuationSubring := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | monomial m c =>
    rw [Polynomial.aeval_monomial]
    exact mul_mem (v.algebraMap_mem' c) (pow_mem hjv m)

theorem mwALGN_ord_algebraMap (v : Place k F) {c : k} (hc : c ≠ 0) :
    v.ord (algebraMap k F c) = 0 := by
  have hu : IsUnit (⟨algebraMap k F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) := by
    refine IsUnit.of_mul_eq_one ⟨algebraMap k F c⁻¹, v.algebraMap_mem' _⟩ (Subtype.ext ?_)
    change algebraMap k F c * algebraMap k F c⁻¹ = 1
    rw [← (algebraMap k F).map_mul, mul_inv_cancel₀ hc, (algebraMap k F).map_one]
  have h := v.ord_coe_unit hu.unit
  rwa [IsUnit.unit_spec] at h

theorem mwALGN_ord_add_eq_of_lt (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hlt : v.ord x < v.ord y) : v.ord (x + y) = v.ord x := by
  have hxy : x + y ≠ 0 := by
    intro h
    have : y = -x := by
      have := eq_neg_of_add_eq_zero_right h
      simpa using this
    rw [this, ord_neg] at hlt
    exact lt_irrefl _ hlt
  have h1 := v.min_ord_le_ord_add hx hy hxy
  have hx' : x = (x + y) + (-y) := by ring
  have h2 := v.min_ord_le_ord_add hxy (neg_ne_zero.mpr hy) (by rw [← hx']; exact hx)
  rw [ord_neg, ← hx'] at h2
  omega

theorem mwALGN_ord_finset_prod (v : Place k F) {ι : Type*} (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i ≠ 0) : v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem mwALGN_ord_aeval_of_ord_neg (w : Place k F) {j : F} (hw : w.ord j < 0)
    (p : Polynomial k) (hp : p ≠ 0) :
    Polynomial.aeval j p ≠ 0 ∧ w.ord (Polynomial.aeval j p) = (p.natDegree : ℤ) * w.ord j := by
  induction hN : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ N ih =>
    have hj0 : j ≠ 0 := by
      intro h
      rw [h, ord_zero] at hw
      exact lt_irrefl _ hw
    have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hlc' : algebraMap k F p.leadingCoeff ≠ 0 := (_root_.map_ne_zero _).mpr hlc
    have hlead0 : algebraMap k F p.leadingCoeff * j ^ N ≠ 0 := mul_ne_zero hlc' (pow_ne_zero _ hj0)
    have hlead : w.ord (algebraMap k F p.leadingCoeff * j ^ N) = (N : ℤ) * w.ord j := by
      rw [w.ord_mul hlc' (pow_ne_zero _ hj0), mwALGN_ord_algebraMap w hlc, zero_add,
        ← zpow_natCast, ord_zpow]
    have hdecomp : Polynomial.aeval j p
        = Polynomial.aeval j p.eraseLead + algebraMap k F p.leadingCoeff * j ^ N := by
      conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow p]
      rw [map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, hN]
    rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero p with hlt | he
    · rw [hN] at hlt
      by_cases he : p.eraseLead = 0
      · rw [hdecomp, he, map_zero, zero_add]
        exact ⟨hlead0, hlead⟩
      obtain ⟨hne, hord⟩ := ih _ hlt p.eraseLead he rfl
      have hgt : w.ord (algebraMap k F p.leadingCoeff * j ^ N)
          < w.ord (Polynomial.aeval j p.eraseLead) := by
        rw [hlead, hord]
        have hlt' : (p.eraseLead.natDegree : ℤ) < N := by exact_mod_cast hlt
        nlinarith
      have hsum0 : algebraMap k F p.leadingCoeff * j ^ N + Polynomial.aeval j p.eraseLead ≠ 0 := by
        intro h0
        have h1 : Polynomial.aeval j p.eraseLead = -(algebraMap k F p.leadingCoeff * j ^ N) :=
          (neg_eq_of_add_eq_zero_right h0).symm
        rw [h1, ord_neg] at hgt
        exact lt_irrefl _ hgt
      refine ⟨by rwa [hdecomp, add_comm], ?_⟩
      rw [hdecomp, add_comm, mwALGN_ord_add_eq_of_lt w hlead0 hne hgt, hlead]
    · rw [hdecomp, he, map_zero, zero_add]
      exact ⟨hlead0, hlead⟩

open scoped Classical in

theorem mwALGN_ord_prod_sub_eq_card_mul (w : Place k F) {L : F} (c : k)
    (hLc : 0 < w.ord (L - algebraMap k F c)) {r : ℕ} (wv : Fin r → k) :
    w.ord (∏ t, (L - algebraMap k F (wv t)))
      = ((Finset.univ.filter fun t => wv t = c).card : ℤ) * w.ord (L - algebraMap k F c) := by
  have hLc0 : L - algebraMap k F c ≠ 0 := by
    intro h
    rw [h, ord_zero] at hLc
    exact lt_irrefl _ hLc

  have hfac : ∀ t, (L - algebraMap k F (wv t)) ≠ 0 ∧
      w.ord (L - algebraMap k F (wv t))
        = if wv t = c then w.ord (L - algebraMap k F c) else 0 := by
    intro t
    by_cases ht : wv t = c
    · rw [if_pos ht, ht]
      exact ⟨hLc0, rfl⟩
    · rw [if_neg ht]
      have hsplit : L - algebraMap k F (wv t)
          = algebraMap k F (c - wv t) + (L - algebraMap k F c) := by
        rw [map_sub]
        ring
      have hc0 : c - wv t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
      have hc0' : algebraMap k F (c - wv t) ≠ 0 := (_root_.map_ne_zero _).mpr hc0
      have hlt : w.ord (algebraMap k F (c - wv t)) < w.ord (L - algebraMap k F c) := by
        rw [mwALGN_ord_algebraMap w hc0]
        exact hLc
      have hne : L - algebraMap k F (wv t) ≠ 0 := by
        rw [hsplit]
        intro h0
        have h1 : L - algebraMap k F c = -algebraMap k F (c - wv t) :=
          (neg_eq_of_add_eq_zero_right h0).symm
        rw [h1, ord_neg] at hlt
        exact lt_irrefl _ hlt
      refine ⟨hne, ?_⟩
      rw [hsplit, mwALGN_ord_add_eq_of_lt w hc0' hLc0 hlt, mwALGN_ord_algebraMap w hc0]
  rw [mwALGN_ord_finset_prod w _ _ fun t _ => (hfac t).1]
  simp_rw [(hfac _).2]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

theorem mwALGN_ord_aeval_le_of_mul_eq (v : Place k F) {j : F} (hjv : j ∈ v.toValuationSubring)
    {n : ℕ} (b : Fin n → F) (hb : ∀ i, b i ∈ v.toValuationSubring)
    (S : Polynomial k) {N g : F} (hN0 : N ≠ 0) (hg0 : g ≠ 0) {d : ℤ} (hN : v.ord N = d)
    (q : Fin n → Polynomial k)
    (hq : N * g = Polynomial.aeval j S * ∑ i, Polynomial.aeval j (q i) * b i) :
    v.ord (Polynomial.aeval j S) ≤ d + v.ord g := by
  have hT : (∑ i, Polynomial.aeval j (q i) * b i) ∈ v.toValuationSubring :=
    sum_mem fun i _ => mul_mem (mwALGN_aeval_mem v hjv _) (hb i)
  have hNg : N * g ≠ 0 := mul_ne_zero hN0 hg0
  have hS0 : Polynomial.aeval j S ≠ 0 := by
    intro h
    rw [h, zero_mul] at hq
    exact hNg hq
  have hT0 : (∑ i, Polynomial.aeval j (q i) * b i) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hq
    exact hNg hq
  have h1 : v.ord (N * g) = d + v.ord g := by rw [v.ord_mul hN0 hg0, hN]
  have h2 : v.ord (N * g) = v.ord (Polynomial.aeval j S)
      + v.ord (∑ i, Polynomial.aeval j (q i) * b i) := by rw [hq, v.ord_mul hS0 hT0]
  have h3 := v.ord_nonneg_of_mem hT
  omega

open scoped Classical in

theorem mwALGN_ord_prod_sub_eq_card (v : Place k F) {r : ℕ} (pt : Fin r → Place k F)
    {L : F} (hL : L ∈ v.toValuationSubring) {c : k} (hLc : v.ord (L - algebraMap k F c) = 1)
    (w : Fin r → k) (hw : ∀ t, pt t = v → w t = c) (hsep : ∀ t, pt t ≠ v → w t ≠ c) :
    v.ord (∏ t, (L - algebraMap k F (w t)))
      = ((Finset.univ.filter fun t => pt t = v).card : ℤ) := by
  classical
  have _ := hL
  have hLc0 : L - algebraMap k F c ≠ 0 := by
    intro h
    rw [h, ord_zero] at hLc
    exact zero_ne_one hLc
  have hfac : ∀ t, L - algebraMap k F (w t) ≠ 0 ∧
      v.ord (L - algebraMap k F (w t)) = if pt t = v then 1 else 0 := by
    intro t
    by_cases ht : pt t = v
    · rw [if_pos ht, hw t ht]
      exact ⟨hLc0, hLc⟩
    · rw [if_neg ht]
      have hne : c - w t ≠ 0 := sub_ne_zero.mpr (Ne.symm (hsep t ht))
      have hc0 : algebraMap k F (c - w t) ≠ 0 := (_root_.map_ne_zero _).mpr hne
      have hordc : v.ord (algebraMap k F (c - w t)) = 0 := mwALGN_ord_algebraMap v hne
      have hsplit : L - algebraMap k F (w t)
          = algebraMap k F (c - w t) + (L - algebraMap k F c) := by
        rw [map_sub]
        ring
      have hlt : v.ord (algebraMap k F (c - w t)) < v.ord (L - algebraMap k F c) := by
        rw [hordc, hLc]
        exact zero_lt_one
      have h := mwALGN_ord_add_eq_of_lt v hc0 hLc0 hlt
      rw [← hsplit] at h
      refine ⟨fun h0 => ?_, by rw [h, hordc]⟩
      rw [h0, ord_zero, hordc] at h

      have : v.ord (L - algebraMap k F c) = v.ord (-(algebraMap k F (c - w t))) := by
        have hL' : L - algebraMap k F c = -(algebraMap k F (c - w t)) := by
          have := hsplit
          rw [h0] at this
          linear_combination -this
        rw [hL']
      rw [ord_neg, hordc, hLc] at this
      exact one_ne_zero this
  rw [mwALGN_ord_finset_prod v _ _ fun t _ => (hfac t).1]
  simp_rw [fun t => (hfac t).2]
  rw [Finset.sum_boole]

def mwALGN_ordGe (v : Place k F) (m : ℤ) : Submodule k F where
  carrier := {x | x = 0 ∨ m ≤ v.ord x}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    by_cases hx0 : x = 0
    · subst hx0
      simpa using hy
    by_cases hy0 : y = 0
    · subst hy0
      simpa using hx
    by_cases hxy : x + y = 0
    · exact Or.inl hxy
    right
    have hx' : m ≤ v.ord x := hx.resolve_left hx0
    have hy' : m ≤ v.ord y := hy.resolve_left hy0
    have h := v.min_ord_le_ord_add hx0 hy0 hxy
    omega
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_cases hc : c = 0
    · subst hc
      simp
    by_cases hx0 : x = 0
    · subst hx0
      simp
    right
    rw [Algebra.smul_def, v.ord_mul ((_root_.map_ne_zero _).mpr hc) hx0,
      mwALGN_ord_algebraMap v hc, zero_add]
    exact hx.resolve_left hx0

theorem mwALGN_mem_ordGe_iff (v : Place k F) (m : ℤ) (x : F) :
    x ∈ mwALGN_ordGe v m ↔ x = 0 ∨ m ≤ v.ord x := Iff.rfl

theorem mwALGN_mem_of_forall_sum_pow_smul_mem (W : Submodule k F) {m : ℕ}
    (z : Fin (m + 1) → F) (θ : Fin (m + 1) → k) (hθ : Function.Injective θ)
    (h : ∀ l, (∑ i : Fin (m + 1), θ l ^ (i : ℕ) • z i) ∈ W) (i : Fin (m + 1)) : z i ∈ W := by
  classical
  set B : Fin (m + 1) → Polynomial k := fun l => Lagrange.basis Finset.univ θ l with hB
  have hvs : Set.InjOn θ (Finset.univ : Finset (Fin (m + 1))) := hθ.injOn
  have hid : ∀ i' : Fin (m + 1),
      (X ^ (i' : ℕ) : Polynomial k) = ∑ l, C (θ l ^ (i' : ℕ)) * B l := by
    intro i'
    have hdeg : (X ^ (i' : ℕ) : Polynomial k).degree
        < (Finset.univ : Finset (Fin (m + 1))).card := by
      rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
      exact_mod_cast i'.2
    have h1 := Lagrange.eq_interpolate hvs hdeg
    rw [Lagrange.interpolate_apply] at h1
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using h1
  have hδ : ∀ i' : Fin (m + 1),
      (∑ l, (B l).coeff i * θ l ^ (i' : ℕ)) = if i = i' then 1 else 0 := by
    intro i'
    have h1 := congrArg (fun p : Polynomial k => p.coeff i) (hid i')
    simp only [Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] at h1
    have h2 : (∑ l, (B l).coeff i * θ l ^ (i' : ℕ)) = ∑ l, θ l ^ (i' : ℕ) * (B l).coeff i :=
      Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [h2, ← h1]
    by_cases hii : i = i'
    · rw [if_pos hii, if_pos (congrArg Fin.val hii)]
    · rw [if_neg hii, if_neg fun h => hii (Fin.ext h)]
  have hcomb : ∑ l, (B l).coeff i • (∑ i' : Fin (m + 1), θ l ^ (i' : ℕ) • z i') = z i := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hδ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [← hcomb]
  exact W.sum_mem fun l _ => W.smul_mem _ (h l)

theorem mwALGN_exists_exact_form (v : Place k F) {j : F} {n : ℕ} (β : Fin n → F)
    (cv : k) (hcv : 0 < v.ord (j - algebraMap k F cv))
    (βv : Fin n → k) (hβv : ∀ i, β i = algebraMap k F (βv i) ∨ 0 < v.ord (β i - algebraMap k F (βv i)))
    (hU1 : v.ord (j - algebraMap k F cv) = 1 ∨ ∃ i, v.ord (β i - algebraMap k F (βv i)) = 1)
    {r : ℕ} (pt : Fin r → Place k F) (cpt : Fin r → k) (βpt : Fin r → Fin n → k)
    (hS1 : ∀ t, pt t ≠ v → cpt t ≠ cv ∨ βpt t ≠ βv)
    {a : ℕ} (θ : Fin a → k) (hθ : Function.Injective θ) (ha : n * (r + 1) < a) :
    ∃ s : Fin a,
      v.ord ((j + ∑ i : Fin n, algebraMap k F (θ s ^ (i.val + 1)) * β i)
          - algebraMap k F (cv + ∑ i : Fin n, θ s ^ (i.val + 1) * βv i)) = 1 ∧
      ∀ t, pt t ≠ v →
        cpt t + ∑ i : Fin n, θ s ^ (i.val + 1) * βpt t i ≠ cv + ∑ i : Fin n, θ s ^ (i.val + 1) * βv i := by
  exact AlgebraicCurve.Place.exists_uniformizing_separating_form v β cv hcv βv hβv hU1
    pt cpt βpt hS1 θ hθ ha

theorem mwALGN_dvd_of_forall_mem {j : F} (hj : Transcendental k j)
    {n : ℕ} (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (Δ d : Polynomial k) (hd : d ≠ 0)
    (hG : ∀ x : F, IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ ρ : Fin n → Polynomial k, Polynomial.aeval j Δ * x
        = ∑ i, Polynomial.aeval j (ρ i) * (Polynomial.aeval j d * b i))
    (hint : ∀ x : F, (∀ v : Place k F, j ∈ v.toValuationSubring → x ∈ v.toValuationSubring) →
      IsIntegral (Algebra.adjoin k ({j} : Set F)) x)
    (S : Polynomial k) (hS : S ≠ 0) (hSΔ : IsCoprime S Δ) {N g : F} (E : Fin n → Polynomial k)
    (hE : N * g = ∑ i, Polynomial.aeval j (E i) * b i)
    (hx : ∀ v : Place k F, j ∈ v.toValuationSubring →
      Polynomial.aeval j d * N * g * (Polynomial.aeval j S)⁻¹ ∈ v.toValuationSubring) :
    ∃ q : Fin n → Polynomial k, ∀ i, E i = S * q i := by
  classical
  have hS0 : (Polynomial.aeval j S : F) ≠ 0 := fun h => hj ⟨S, hS, h⟩
  set y := Polynomial.aeval j d * N * g * (Polynomial.aeval j S)⁻¹ with hy
  obtain ⟨ρ, hρ⟩ := hG y (hint y hx)
  have hy' : Polynomial.aeval j d * N * g = y * Polynomial.aeval j S := by
    rw [hy, inv_mul_cancel_right₀ hS0]
  have key : ∑ i, Polynomial.aeval j (Δ * d * E i) * b i
      = ∑ i, Polynomial.aeval j (S * d * ρ i) * b i := by
    calc ∑ i, Polynomial.aeval j (Δ * d * E i) * b i
        = Polynomial.aeval j Δ * Polynomial.aeval j d * (N * g) := by
          rw [hE, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [map_mul]
          ring
      _ = Polynomial.aeval j Δ * (Polynomial.aeval j d * N * g) := by ring
      _ = Polynomial.aeval j Δ * (y * Polynomial.aeval j S) := by rw [hy']
      _ = (∑ i, Polynomial.aeval j (ρ i) * (Polynomial.aeval j d * b i))
            * Polynomial.aeval j S := by rw [← mul_assoc, hρ]
      _ = ∑ i, Polynomial.aeval j (S * d * ρ i) * b i := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [map_mul]
          ring
  have hcoef : ∀ i, Δ * d * E i = S * d * ρ i := by
    have hzero : ∑ i, Polynomial.aeval j (Δ * d * E i - S * d * ρ i) * b i = 0 := by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib, key, sub_self]
    intro i
    exact sub_eq_zero.mp (hbli _ hzero i)
  have hdvd : ∀ i, S ∣ E i := by
    intro i
    have h2 : d * (Δ * E i) = d * (S * ρ i) := by
      calc d * (Δ * E i) = Δ * d * E i := by ring
        _ = S * d * ρ i := hcoef i
        _ = d * (S * ρ i) := by ring
    have h1 : Δ * E i = S * ρ i := mul_left_cancel₀ hd h2
    exact hSΔ.dvd_of_dvd_mul_left ⟨ρ i, h1⟩
  choose q hq using hdvd
  exact ⟨q, hq⟩

theorem mwALGN_exists_nonconst_form {j : F} (hj : Transcendental k j) {n : ℕ} (β : Fin n → F)
    (θ : Fin (n + 1) → k) (hθ : Function.Injective θ) :
    ∃ s, ∀ c : k, (j + ∑ i : Fin n, algebraMap k F (θ s ^ (i.val + 1)) * β i)
      ≠ algebraMap k F c := by
  classical
  by_contra hcon
  push Not at hcon
  let W : Submodule k F := LinearMap.range (Algebra.linearMap k F)
  let z : Fin (n + 1) → F := Fin.cons j β
  have hform : ∀ s, (∑ i : Fin (n + 1), θ s ^ (i : ℕ) • z i)
      = j + ∑ i : Fin n, algebraMap k F (θ s ^ (i.val + 1)) * β i := by
    intro s
    simp only [z, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero,
      Fin.val_succ, Algebra.smul_def, map_pow, one_mul]
  have hall : ∀ s, (∑ i : Fin (n + 1), θ s ^ (i : ℕ) • z i) ∈ W := by
    intro s
    obtain ⟨c, hc⟩ := hcon s
    rw [hform, hc]
    exact ⟨c, rfl⟩
  have hj0 : z 0 ∈ W := mwALGN_mem_of_forall_sum_pow_smul_mem W z θ hθ hall 0
  obtain ⟨c, hc⟩ := hj0
  simp only [z, Fin.cons_zero, Algebra.linearMap_apply] at hc
  exact hj (hc ▸ isAlgebraic_algebraMap c)

theorem mwALGN_pin_iff (v : Place k F) (x : F) (c : k) :
    (x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c))
      ↔ x - algebraMap k F c ∈ mwALGN_ordGe v 1 := by
  rw [mwALGN_mem_ordGe_iff, sub_eq_zero]
  rfl

theorem mwALGN_ordGe_mul_mem (v : Place k F) (m : ℤ) {x y : F} (hx : x ∈ mwALGN_ordGe v m)
    (hy : y ∈ v.toValuationSubring) : x * y ∈ mwALGN_ordGe v m := by
  rw [mwALGN_mem_ordGe_iff] at hx ⊢
  by_cases hx0 : x = 0
  · exact Or.inl (by rw [hx0, zero_mul])
  by_cases hy0 : y = 0
  · exact Or.inl (by rw [hy0, mul_zero])
  right
  rw [v.ord_mul hx0 hy0]
  have h1 := hx.resolve_left hx0
  have h2 := v.ord_nonneg_of_mem hy
  omega

theorem mwALGN_ordGe_mul_mem' (v : Place k F) (m : ℤ) {x y : F} (hx : x ∈ v.toValuationSubring)
    (hy : y ∈ mwALGN_ordGe v m) : x * y ∈ mwALGN_ordGe v m := by
  rw [mul_comm]
  exact mwALGN_ordGe_mul_mem v m hy hx

theorem mwALGN_eq_zero_of_algebraMap_mem_ordGe (v : Place k F) {m : ℤ} (hm : 0 < m) {c : k}
    (hc : algebraMap k F c ∈ mwALGN_ordGe v m) : c = 0 := by
  by_contra hne
  rcases hc with h | h
  · exact hne ((_root_.map_eq_zero _).mp h)
  · rw [mwALGN_ord_algebraMap v hne] at h
    omega

theorem mwALGN_aeval_sub_algebraMap_eval_mem (v : Place k F) (m : ℤ) {j : F}
    (hjv : j ∈ v.toValuationSubring) {c : k} (hjc : j - algebraMap k F c ∈ mwALGN_ordGe v m)
    (ρ : Polynomial k) :
    Polynomial.aeval j ρ - algebraMap k F (ρ.eval c) ∈ mwALGN_ordGe v m := by
  obtain ⟨q, hq⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := ρ) (a := c)
  have h : Polynomial.aeval j ρ - algebraMap k F (ρ.eval c)
      = (j - algebraMap k F c) * Polynomial.aeval j q := by
    have h1 := congrArg (Polynomial.aeval j) hq
    simp only [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X] at h1
    exact h1
  rw [h]
  exact mwALGN_ordGe_mul_mem v m hjc (mwALGN_aeval_mem v hjv q)

theorem mwALGN_sum_aeval_mul_sub_mem (v : Place k F) (m : ℤ) {j : F}
    (hjv : j ∈ v.toValuationSubring) {c : k} (hjc : j - algebraMap k F c ∈ mwALGN_ordGe v m)
    {n : ℕ} (β : Fin n → F) (hβ : ∀ i, β i ∈ v.toValuationSubring) (βv : Fin n → k)
    (hβv : ∀ i, β i - algebraMap k F (βv i) ∈ mwALGN_ordGe v m) (ρ : Fin n → Polynomial k) :
    (∑ i, Polynomial.aeval j (ρ i) * β i) - algebraMap k F (∑ i, (ρ i).eval c * βv i)
      ∈ mwALGN_ordGe v m := by
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hsplit : Polynomial.aeval j (ρ i) * β i - algebraMap k F ((ρ i).eval c * βv i)
      = (Polynomial.aeval j (ρ i) - algebraMap k F ((ρ i).eval c)) * β i
        + algebraMap k F ((ρ i).eval c) * (β i - algebraMap k F (βv i)) := by
    rw [map_mul]
    ring
  rw [hsplit]
  exact add_mem (mwALGN_ordGe_mul_mem v m (mwALGN_aeval_sub_algebraMap_eval_mem v m hjv hjc _) (hβ i))
    (mwALGN_ordGe_mul_mem' v m (v.algebraMap_mem' _) (hβv i))

theorem mwALGN_exists_rows_of_submodule {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Submodule k (ι → k)) :
    ∃ (R : ℕ) (Y : Fin R → ι → k), ∀ u : ι → k, (∀ ρ, ∑ c, Y ρ c * u c = 0) ↔ u ∈ W := by
  classical
  let φ : (ι → k) →ₗ[k] (Fin (Module.finrank k ((ι → k) ⧸ W)) → k) :=
    (Module.finBasis k ((ι → k) ⧸ W)).equivFun.toLinearMap.comp W.mkQ
  refine ⟨Module.finrank k ((ι → k) ⧸ W), fun ρ c => φ (Pi.single c 1) ρ, fun u => ?_⟩
  have hu : u = ∑ c, u c • (Pi.single c (1 : k) : ι → k) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  have hφu : ∀ ρ, ∑ c, φ (Pi.single c 1) ρ * u c = φ u ρ := by
    intro ρ
    conv_rhs => rw [hu]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  simp_rw [hφu]
  have hφ : φ u = 0 ↔ u ∈ W := by
    rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply]
    constructor
    · intro h
      apply (Module.finBasis k ((ι → k) ⧸ W)).equivFun.injective
      rw [map_zero]
      exact h
    · intro h
      show (Module.finBasis k ((ι → k) ⧸ W)).equivFun (W.mkQ u) = 0
      rw [h, map_zero]
  rw [← hφ]
  exact ⟨fun h => funext h, fun h ρ => by rw [h]; rfl⟩

theorem mwALGN_exists_menu {ι : Type*} [Fintype ι] [DecidableEq ι] (gmap : (ι → k) →ₗ[k] F)
    {Z : Type*} [Fintype Z] (plc : Z → Place k F) {T : Type*} [Fintype T] (μ : T → Z → ℤ) :
    ∃ (M : ℕ) (eT : T ≃ Fin M) (Rm : Fin M → ℕ) (Y : (l : Fin M) → Fin (Rm l) → ι → k),
      ∀ (τ : T) (u : ι → k),
        (∀ ρ : Fin (Rm (eT τ)), ∑ c, Y (eT τ) ρ c * u c = 0)
          ↔ (gmap u = 0 ∨ ∀ z, μ τ z ≤ (plc z).ord (gmap u)) := by
  classical
  let W : T → Submodule k (ι → k) := fun τ => ⨅ z, (mwALGN_ordGe (plc z) (μ τ z)).comap gmap
  have hW : ∀ τ u, u ∈ W τ ↔ (gmap u = 0 ∨ ∀ z, μ τ z ≤ (plc z).ord (gmap u)) := by
    intro τ u
    simp only [W, Submodule.mem_iInf, Submodule.mem_comap, mwALGN_mem_ordGe_iff]
    constructor
    · intro h
      by_cases h0 : gmap u = 0
      · exact Or.inl h0
      · exact Or.inr fun z => (h z).resolve_left h0
    · rintro (h | h) z
      · exact Or.inl h
      · exact Or.inr (h z)
  choose R Y hY using fun W' : Submodule k (ι → k) => mwALGN_exists_rows_of_submodule W'
  refine ⟨Fintype.card T, Fintype.equivFin T, fun l => R (W ((Fintype.equivFin T).symm l)),
    fun l => Y (W ((Fintype.equivFin T).symm l)), fun τ u => ?_⟩
  rw [hY, Equiv.symm_apply_apply, hW]

section cfin

open scoped IntermediateField.algebraAdjoinAdjoin

theorem mwALGN_isPrincipalIdealRing_adjoin (j : F) :
    IsPrincipalIdealRing (Algebra.adjoin k ({j} : Set F)) := by
  let e : (Polynomial.aeval j : Polynomial k →ₐ[k] F).range ≃ₐ[k] Algebra.adjoin k ({j} : Set F) :=
    Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval k j).symm
  let f : Polynomial k →ₐ[k] Algebra.adjoin k ({j} : Set F) :=
    e.toAlgHom.comp (Polynomial.aeval j).rangeRestrict
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨p, hp⟩ : ∃ p : Polynomial k, (Polynomial.aeval j).rangeRestrict p = e.symm y := by
      obtain ⟨p, hp⟩ := (e.symm y).2
      exact ⟨p, Subtype.ext hp⟩
    refine ⟨p, ?_⟩
    show e ((Polynomial.aeval j).rangeRestrict p) = y
    rw [hp]
    exact e.apply_symm_apply y
  exact IsPrincipalIdealRing.of_surjective f.toRingHom hf

theorem mwALGN_exists_isIntegral_ord_eq_one {j : F}
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F]
    (v : Place k F) (hjv : j ∈ v.toValuationSubring) :
    ∃ π : F, IsIntegral (Algebra.adjoin k ({j} : Set F)) π ∧ v.ord π = 1 := by
  classical
  haveI : IsPrincipalIdealRing (Algebra.adjoin k ({j} : Set F)) :=
    mwALGN_isPrincipalIdealRing_adjoin j
  haveI : IsDedekindDomain (integralClosure (Algebra.adjoin k ({j} : Set F)) F) :=
    integralClosure.isDedekindDomain (Algebra.adjoin k ({j} : Set F))
      (IntermediateField.adjoin k ({j} : Set F)) F
  haveI : IsFractionRing (integralClosure (Algebra.adjoin k ({j} : Set F)) F) F :=
    integralClosure.isFractionRing_of_finite_extension
      (A := Algebra.adjoin k ({j} : Set F)) (IntermediateField.adjoin k ({j} : Set F)) F
  have hw : ∀ r : integralClosure (Algebra.adjoin k ({j} : Set F)) F,
      algebraMap _ F r ∈ v.toValuationSubring := fun r =>
    v.mem_toValuationSubring_of_isIntegral_adjoin hjv r.2
  set P := Place.centerHeightOneSpectrum (integralClosure (Algebra.adjoin k ({j} : Set F)) F) v hw
    with hP
  have hOv : (P.valuation F).valuationSubring = v.toValuationSubring := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
      (K := F) P]
    exact (v.toValuationSubring_eq_of_forall_mem hw).symm
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer' F
  have hπ' : P.valuation F (algebraMap _ F π) = WithZero.exp (-1 : ℤ) := hπ
  have hπ0 : (algebraMap _ F π : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  refine ⟨algebraMap _ F π, π.2, ?_⟩
  rw [v.ord_eq_neg_log_of_valuationSubring_eq (P.valuation F) hOv hπ' hπ0, hπ',
    WithZero.log_exp, neg_neg]

theorem mwALGN_U1 (v : Place k F) {j : F} (hj : Transcendental k j)
    (hjv : j ∈ v.toValuationSubring) {n : ℕ} (β : Fin n → F)
    (hβ : ∀ i, β i ∈ v.toValuationSubring)
    (Δ : Polynomial k) (hΔ0 : Δ ≠ 0) (hΔv : v.ord (Polynomial.aeval j Δ) = 0)
    (hG : ∀ x : F, IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ ρ : Fin n → Polynomial k, Polynomial.aeval j Δ * x
        = ∑ i, Polynomial.aeval j (ρ i) * β i)
    {π : F} (hπ : IsIntegral (Algebra.adjoin k ({j} : Set F)) π) (hπ1 : v.ord π = 1)
    (cv : k) (hcv : 0 < v.ord (j - algebraMap k F cv))
    (βv : Fin n → k)
    (hβv : ∀ i, β i = algebraMap k F (βv i) ∨ 0 < v.ord (β i - algebraMap k F (βv i))) :
    v.ord (j - algebraMap k F cv) = 1 ∨ ∃ i, v.ord (β i - algebraMap k F (βv i)) = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, hi⟩ := hcon
  have hz0 : j - algebraMap k F cv ∈ mwALGN_ordGe v 2 := Or.inr (by omega)
  have hzi : ∀ i, β i - algebraMap k F (βv i) ∈ mwALGN_ordGe v 2 := by
    intro i
    rcases hβv i with h | h
    · exact Or.inl (by rw [h, sub_self])
    · right
      have := hi i
      omega
  obtain ⟨ρ, hρ⟩ := hG π hπ
  have hmain : Polynomial.aeval j Δ * π - algebraMap k F (∑ i, (ρ i).eval cv * βv i)
      ∈ mwALGN_ordGe v 2 := by
    rw [hρ]
    exact mwALGN_sum_aeval_mul_sub_mem v 2 hjv hz0 β hβ βv hzi ρ
  have hΔ0' : (Polynomial.aeval j Δ : F) ≠ 0 := fun h => hj ⟨Δ, hΔ0, h⟩
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, ord_zero] at hπ1
    exact zero_ne_one hπ1
  have hord : v.ord (Polynomial.aeval j Δ * π) = 1 := by
    rw [v.ord_mul hΔ0' hπ0, hΔv, hπ1, zero_add]
  set c₀ := ∑ i, (ρ i).eval cv * βv i with hc₀
  by_cases hc : c₀ = 0
  · rw [hc, map_zero, sub_zero] at hmain
    rcases hmain with h | h
    · exact mul_ne_zero hΔ0' hπ0 h
    · omega
  · set w₂ := Polynomial.aeval j Δ * π - algebraMap k F c₀ with hw₂
    have hsum : Polynomial.aeval j Δ * π = algebraMap k F c₀ + w₂ := by rw [hw₂]; ring
    by_cases hw0 : w₂ = 0
    · rw [hw0, add_zero] at hsum
      rw [hsum, mwALGN_ord_algebraMap v hc] at hord
      exact zero_ne_one hord
    · have hw2 : 2 ≤ v.ord w₂ := hmain.resolve_left hw0
      have hc0' : algebraMap k F c₀ ≠ 0 := (_root_.map_ne_zero _).mpr hc
      have hlt : v.ord (algebraMap k F c₀) < v.ord w₂ := by
        rw [mwALGN_ord_algebraMap v hc]
        omega
      have h := mwALGN_ord_add_eq_of_lt v hc0' hw0 hlt
      rw [← hsum, hord, mwALGN_ord_algebraMap v hc] at h
      exact one_ne_zero h

theorem mwALGN_S1 {j : F} (hj : Transcendental k j)
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F]
    (v w : Place k F) (hjv : j ∈ v.toValuationSubring) (hjw : j ∈ w.toValuationSubring)
    (hne : v ≠ w) {n : ℕ} (β : Fin n → F)
    (hβv : ∀ i, β i ∈ v.toValuationSubring) (hβw : ∀ i, β i ∈ w.toValuationSubring)
    (Δ : Polynomial k) (hΔ0 : Δ ≠ 0) (hΔv : v.ord (Polynomial.aeval j Δ) = 0)
    (hG : ∀ x : F, IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ ρ : Fin n → Polynomial k, Polynomial.aeval j Δ * x
        = ∑ i, Polynomial.aeval j (ρ i) * β i)
    (cv cw : k) (hcv : 0 < v.ord (j - algebraMap k F cv))
    (hcw : 0 < w.ord (j - algebraMap k F cw))
    (βvv βww : Fin n → k)
    (hβvv : ∀ i, β i = algebraMap k F (βvv i) ∨ 0 < v.ord (β i - algebraMap k F (βvv i)))
    (hβww : ∀ i, β i = algebraMap k F (βww i) ∨ 0 < w.ord (β i - algebraMap k F (βww i))) :
    cv ≠ cw ∨ βvv ≠ βww := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hc, hb⟩ := hcon

  haveI : IsPrincipalIdealRing (Algebra.adjoin k ({j} : Set F)) :=
    mwALGN_isPrincipalIdealRing_adjoin j
  haveI : IsDedekindDomain (integralClosure (Algebra.adjoin k ({j} : Set F)) F) :=
    integralClosure.isDedekindDomain (Algebra.adjoin k ({j} : Set F))
      (IntermediateField.adjoin k ({j} : Set F)) F
  haveI : IsFractionRing (integralClosure (Algebra.adjoin k ({j} : Set F)) F) F :=
    integralClosure.isFractionRing_of_finite_extension
      (A := Algebra.adjoin k ({j} : Set F)) (IntermediateField.adjoin k ({j} : Set F)) F
  set C := integralClosure (Algebra.adjoin k ({j} : Set F)) F with hCdef
  have hwv : ∀ r : C, algebraMap C F r ∈ v.toValuationSubring := fun r =>
    v.mem_toValuationSubring_of_isIntegral_adjoin hjv r.2
  have hww : ∀ r : C, algebraMap C F r ∈ w.toValuationSubring := fun r =>
    w.mem_toValuationSubring_of_isIntegral_adjoin hjw r.2
  have hmax : ∀ (u : Place k F) (hu : ∀ r : C, algebraMap C F r ∈ u.toValuationSubring),
      (Place.center C u hu).IsMaximal := fun u hu =>
    Ring.DimensionLEOne.maximalOfPrime (Place.center_ne_bot u hu) inferInstance
  have hPne : Place.center C v hwv ≠ Place.center C w hww := by
    intro h
    apply hne
    refine Place.ext ?_
    rw [v.toValuationSubring_eq_of_forall_mem hwv, w.toValuationSubring_eq_of_forall_mem hww]
    have : Place.centerHeightOneSpectrum C v hwv = Place.centerHeightOneSpectrum C w hww :=
      IsDedekindDomain.HeightOneSpectrum.ext h
    rw [this]
  have htop : Place.center C v hwv ⊔ Place.center C w hww = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne (hmax v hwv) (hmax w hww) hPne
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp
    (show (1 : C) ∈ Place.center C v hwv ⊔ Place.center C w hww from htop ▸ Submodule.mem_top)

  have hx1v : (algebraMap C F x : F) - algebraMap k F 0 ∈ mwALGN_ordGe v 1 := by
    rw [(algebraMap k F).map_zero, sub_zero, mwALGN_mem_ordGe_iff]
    by_cases hx0 : x = 0
    · exact Or.inl (by rw [hx0, (algebraMap C F).map_zero])
    · exact Or.inr ((Place.mem_center_iff_ord_pos v hwv hx0).mp hx)
  have hx1w : (algebraMap C F x : F) - algebraMap k F 1 ∈ mwALGN_ordGe w 1 := by
    have hxy' : (algebraMap C F x : F) - algebraMap k F 1 = -(algebraMap C F y) := by
      have hsum : (algebraMap C F x : F) + algebraMap C F y = 1 := by
        rw [← (algebraMap C F).map_add, hxy, (algebraMap C F).map_one]
      rw [(algebraMap k F).map_one, ← hsum]
      ring
    rw [hxy', mwALGN_mem_ordGe_iff, neg_eq_zero, ord_neg]
    by_cases hy0 : y = 0
    · exact Or.inl (by rw [hy0, (algebraMap C F).map_zero])
    · exact Or.inr ((Place.mem_center_iff_ord_pos w hww hy0).mp hy)
  obtain ⟨ρ, hρ⟩ := hG (algebraMap C F x) x.2
  have hΔ0' : (Polynomial.aeval j Δ : F) ≠ 0 := fun h => hj ⟨Δ, hΔ0, h⟩

  have hjcv : j - algebraMap k F cv ∈ mwALGN_ordGe v 1 := Or.inr hcv
  have hjcw : j - algebraMap k F cw ∈ mwALGN_ordGe w 1 := Or.inr hcw
  have hβv1 : ∀ i, β i - algebraMap k F (βvv i) ∈ mwALGN_ordGe v 1 := fun i =>
    (mwALGN_pin_iff v _ _).mp (hβvv i)
  have hβw1 : ∀ i, β i - algebraMap k F (βww i) ∈ mwALGN_ordGe w 1 := fun i =>
    (mwALGN_pin_iff w _ _).mp (hβww i)
  have hv1 : Polynomial.aeval j Δ * algebraMap C F x ∈ mwALGN_ordGe v 1 := by
    have := mwALGN_ordGe_mul_mem' v 1 (mwALGN_aeval_mem v hjv Δ) hx1v
    rwa [(algebraMap k F).map_zero, sub_zero] at this
  have hv2 : Polynomial.aeval j Δ * algebraMap C F x
      - algebraMap k F (∑ i, (ρ i).eval cv * βvv i) ∈ mwALGN_ordGe v 1 := by
    rw [hρ]
    exact mwALGN_sum_aeval_mul_sub_mem v 1 hjv hjcv β hβv βvv hβv1 ρ
  have hcv0 : ∑ i, (ρ i).eval cv * βvv i = 0 := by
    have h := Submodule.sub_mem _ hv1 hv2
    rw [sub_sub_cancel] at h
    exact mwALGN_eq_zero_of_algebraMap_mem_ordGe v one_pos h

  have hw1 : Polynomial.aeval j Δ * algebraMap C F x - algebraMap k F (Δ.eval cw * 1)
      ∈ mwALGN_ordGe w 1 := by
    have hsplit : Polynomial.aeval j Δ * algebraMap C F x - algebraMap k F (Δ.eval cw * 1)
        = (Polynomial.aeval j Δ - algebraMap k F (Δ.eval cw)) * algebraMap C F x
          + algebraMap k F (Δ.eval cw) * (algebraMap C F x - algebraMap k F 1) := by
      rw [(algebraMap k F).map_mul]
      ring
    rw [hsplit]
    exact add_mem (mwALGN_ordGe_mul_mem w 1 (mwALGN_aeval_sub_algebraMap_eval_mem w 1 hjw hjcw Δ)
      (hww x)) (mwALGN_ordGe_mul_mem' w 1 (w.algebraMap_mem' _) hx1w)
  have hw2 : Polynomial.aeval j Δ * algebraMap C F x
      - algebraMap k F (∑ i, (ρ i).eval cw * βww i) ∈ mwALGN_ordGe w 1 := by
    rw [hρ]
    exact mwALGN_sum_aeval_mul_sub_mem w 1 hjw hjcw β hβw βww hβw1 ρ
  have hcw0 : Δ.eval cw = 0 := by
    have h := Submodule.sub_mem _ hw2 hw1
    rw [sub_sub_sub_cancel_left, ← (algebraMap k F).map_sub] at h
    have h2 := mwALGN_eq_zero_of_algebraMap_mem_ordGe w one_pos h
    rw [mul_one, ← hc, ← hb, hcv0, sub_zero] at h2
    rw [← hc]
    exact h2

  have hΔ1 : Polynomial.aeval j Δ - algebraMap k F (Δ.eval cv) ∈ mwALGN_ordGe v 1 :=
    mwALGN_aeval_sub_algebraMap_eval_mem v 1 hjv hjcv Δ
  rw [hc, hcw0, (algebraMap k F).map_zero, sub_zero] at hΔ1
  rcases hΔ1 with h | h
  · exact hΔ0' h
  · omega

theorem mwALGN_ker_good {K₀ : Type*} [Field K₀] [Algebra K₀ k] {j : F} (hj : Transcendental k j)
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F]
    (hrat : ∀ (v : Place k F) (x : F), j ∈ v.toValuationSubring →
      IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ c : k, x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c))
    (n : ℕ) (b : Fin n → F) (d : Polynomial K₀) (hd : d ≠ 0)
    (hIdb : ∀ i : Fin n, IsIntegral (Algebra.adjoin k ({j} : Set F))
      (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i))
    (Δ : Polynomial K₀) (hΔ : Δ ≠ 0)
    (hG : ∀ x : F, IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ c : Fin n → Polynomial k,
        Polynomial.aeval j (Δ.map (algebraMap K₀ k)) * x
          = ∑ i : Fin n, Polynomial.aeval j (c i)
              * (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i))
    (q₀ : Polynomial K₀) (hq₀ : q₀ ≠ 0) (Θ : Polynomial K₀) (hΘ : Θ = Δ * d * q₀)
    (v₀ : Place k F) (e : ℕ)
    (a : ℕ) (θ : Fin a → K₀) (hθ : Function.Injective θ) (g : ℕ) (ha : n * (g + 1) < a)
    (D : Divisor k F) {r : ℕ} (hrle : r ≤ g) (pt : Fin r → Place k F)
    (val : Fin r × Fin (a + 1) → k) (βpt : Fin r → Fin n → k)
    {r' : ℕ} (pt' : Fin r' → Place k F) (jv' : Fin r' → k)
    (hpt : ∀ t, 0 ≤ (pt t).ord j ∧
      (pt t).ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) = 0)
    (hpt' : ∀ t', 0 < (pt' t').ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))))
    (henum : ∀ v : Place k F, 0 ≤ v.ord j → D v =
      ((∑ t, Finsupp.single (pt t) (1 : ℤ))
        + ∑ t', Finsupp.single (pt' t') (1 : ℤ) : Divisor k F) v)
    (hval0 : ∀ t, 0 < (pt t).ord (j - algebraMap k F (val (t, 0))))
    (hvalL : ∀ t (s : Fin a), 0 < (pt t).ord
      ((Polynomial.aeval j ((Polynomial.X : Polynomial K₀).map (algebraMap K₀ k))
        + ∑ i : Fin n, Polynomial.aeval j
            ((Polynomial.C (θ s ^ (i.val + 1)) * d).map (algebraMap K₀ k)) * b i)
        - algebraMap k F (val (t, s.succ))))
    (hjv' : ∀ t', 0 < (pt' t').ord (j - algebraMap k F (jv' t')))
    (hβpt : ∀ t i, Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i
        = algebraMap k F (βpt t i) ∨
      0 < (pt t).ord (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i
        - algebraMap k F (βpt t i)))
    {gU : F} (hgU0 : gU ≠ 0) (E : Fin a → Fin n → Polynomial k)
    (hE : ∀ s : Fin a,
      (∏ t : Fin r, ((Polynomial.aeval j ((Polynomial.X : Polynomial K₀).map (algebraMap K₀ k))
          + ∑ i : Fin n, Polynomial.aeval j
              ((Polynomial.C (θ s ^ (i.val + 1)) * d).map (algebraMap K₀ k)) * b i)
          - algebraMap k F (val (t, s.succ)))) * gU
        = ∑ i' : Fin n, Polynomial.aeval j (E s i') * b i')
    (hdvd : ∀ (s : Fin a) (i' : Fin n),
      (∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0)))) ∣ E s i')
    (v : Place k F) (hvj : 0 ≤ v.ord j)
    (hvΘ : v.ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) = 0) (hv₀ : v ≠ v₀) :
    0 ≤ (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v
      + v.ord (gU * (Polynomial.aeval j
          ((∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))))
            * (∏ t', (Polynomial.X - Polynomial.C (jv' t')))
            * q₀.map (algebraMap K₀ k)))⁻¹) := by
  classical

  set φ : K₀ →+* k := algebraMap K₀ k with hφ
  set β : Fin n → F := fun i => Polynomial.aeval j (d.map φ) * b i with hβdef
  set S : Polynomial k := ∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))) with hSdef
  set S' : Polynomial k := ∏ t', (Polynomial.X - Polynomial.C (jv' t')) with hS'def
  have hjne : j ≠ 0 := fun h0 => hj (h0 ▸ isAlgebraic_zero)
  have hjmem : j ∈ v.toValuationSubring := v.mem_of_ord_nonneg hjne hvj
  have hjmem_t : ∀ t, j ∈ (pt t).toValuationSubring :=
    fun t => (pt t).mem_of_ord_nonneg hjne (hpt t).1
  have hnz : ∀ p : Polynomial K₀, p ≠ 0 → (Polynomial.aeval j (p.map φ) : F) ≠ 0 := by
    intro p hp h0
    apply hp
    have hmap0 : p.map φ = 0 := by
      by_contra hne
      exact hj ⟨p.map φ, hne, h0⟩
    exact Polynomial.map_injective φ φ.injective (hmap0.trans (Polynomial.map_zero φ).symm)
  have hjint : IsIntegral (Algebra.adjoin k ({j} : Set F)) j := by
    have h : (algebraMap (Algebra.adjoin k ({j} : Set F)) F)
        ⟨j, Algebra.self_mem_adjoin_singleton k j⟩ = j := rfl
    rw [← h]
    exact isIntegral_algebraMap
  have hβmem : ∀ (w : Place k F), j ∈ w.toValuationSubring → ∀ i, β i ∈ w.toValuationSubring :=
    fun w hw i => w.mem_toValuationSubring_of_isIntegral_adjoin hw (hIdb i)

  have hΔ' := hnz Δ hΔ
  have hd' := hnz d hd
  have hq₀' := hnz q₀ hq₀
  have hΘmap : Polynomial.aeval j (Θ.map φ)
      = Polynomial.aeval j (Δ.map φ) * Polynomial.aeval j (d.map φ)
        * Polynomial.aeval j (q₀.map φ) := by
    rw [hΘ, Polynomial.map_mul, Polynomial.map_mul, map_mul, map_mul]
  have hords : v.ord (Polynomial.aeval j (Δ.map φ)) = 0 ∧ v.ord (Polynomial.aeval j (d.map φ)) = 0
      ∧ v.ord (Polynomial.aeval j (q₀.map φ)) = 0 := by
    have h := hvΘ
    rw [hΘmap, v.ord_mul (mul_ne_zero hΔ' hd') hq₀', v.ord_mul hΔ' hd'] at h
    have h1 := v.ord_nonneg_of_mem (mwALGN_aeval_mem v hjmem (Δ.map φ))
    have h2 := v.ord_nonneg_of_mem (mwALGN_aeval_mem v hjmem (d.map φ))
    have h3 := v.ord_nonneg_of_mem (mwALGN_aeval_mem v hjmem (q₀.map φ))
    omega
  obtain ⟨hordΔ, hordd, hordq₀⟩ := hords

  have hb : ∀ i, b i ∈ v.toValuationSubring := by
    intro i
    have hinv : (Polynomial.aeval j (d.map φ) : F)⁻¹ ∈ v.toValuationSubring :=
      v.mem_of_ord_nonneg (inv_ne_zero hd') (by rw [v.ord_inv, hordd, neg_zero])
    have h : b i = (Polynomial.aeval j (d.map φ))⁻¹ * β i := by
      rw [hβdef]
      field_simp
    rw [h]
    exact mul_mem hinv (hβmem v hjmem i)

  obtain ⟨cv, hcv⟩ := hrat v j hjmem hjint
  have hcv' : 0 < v.ord (j - algebraMap k F cv) := by
    rcases hcv with h | h
    · exact absurd (h ▸ isAlgebraic_algebraMap cv) hj
    · exact h
  have hrat' : ∀ i, ∃ c : k, β i = algebraMap k F c ∨ 0 < v.ord (β i - algebraMap k F c) :=
    fun i => hrat v (β i) hjmem (hIdb i)
  choose βv hβv using hrat'
  have hΔk0 : (Δ.map φ) ≠ 0 := fun h0 => hΔ' (by rw [h0, map_zero])
  obtain ⟨π, hπ, hπ1⟩ := mwALGN_exists_isIntegral_ord_eq_one v hjmem
  have hU1 : v.ord (j - algebraMap k F cv) = 1 ∨ ∃ i, v.ord (β i - algebraMap k F (βv i)) = 1 :=
    mwALGN_U1 v hj hjmem β (hβmem v hjmem) (Δ.map φ) hΔk0 hordΔ hG hπ hπ1 cv hcv' βv hβv
  have hS1 : ∀ t, pt t ≠ v → val (t, 0) ≠ cv ∨ βpt t ≠ βv := fun t ht =>
    (mwALGN_S1 hj v (pt t) hjmem (hjmem_t t) (Ne.symm ht) β (hβmem v hjmem)
      (hβmem (pt t) (hjmem_t t)) (Δ.map φ) hΔk0 hordΔ hG cv (val (t, 0)) hcv' (hval0 t)
      βv (βpt t) hβv (hβpt t)).imp Ne.symm Ne.symm

  have ha' : n * (r + 1) < a := lt_of_le_of_lt (Nat.mul_le_mul_left n (by omega)) ha
  obtain ⟨s, hs1, hs2⟩ := mwALGN_exists_exact_form v β cv hcv' βv hβv hU1 pt
    (fun t => val (t, 0)) βpt hS1 (fun s => φ (θ s)) (φ.injective.comp hθ) ha'

  set Ls : F := Polynomial.aeval j ((Polynomial.X : Polynomial K₀).map φ)
      + ∑ i : Fin n, Polynomial.aeval j ((Polynomial.C (θ s ^ (i.val + 1)) * d).map φ) * b i
    with hLsdef
  have hLs : Ls = j + ∑ i : Fin n, algebraMap k F (φ (θ s) ^ (i.val + 1)) * β i := by
    rw [hLsdef, Polynomial.map_X, Polynomial.aeval_X]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, map_mul, Polynomial.aeval_C, map_pow, hβdef,
      mul_assoc]
  set cs : k := cv + ∑ i : Fin n, φ (θ s) ^ (i.val + 1) * βv i with hcsdef
  have hs1' : v.ord (Ls - algebraMap k F cs) = 1 := by rw [hLs]; exact hs1
  have hLsmem : ∀ (w : Place k F), j ∈ w.toValuationSubring → Ls ∈ w.toValuationSubring := by
    intro w hw
    rw [hLs]
    exact add_mem hw (sum_mem fun i _ => mul_mem (w.algebraMap_mem' _) (hβmem w hw i))

  have hpinL : ∀ (w : Place k F) (hw : j ∈ w.toValuationSubring) (c0 : k)
      (hc0 : 0 < w.ord (j - algebraMap k F c0)) (βw : Fin n → k)
      (hβw : ∀ i, β i = algebraMap k F (βw i) ∨ 0 < w.ord (β i - algebraMap k F (βw i))),
      Ls - algebraMap k F (c0 + ∑ i : Fin n, φ (θ s) ^ (i.val + 1) * βw i)
        ∈ mwALGN_ordGe w 1 := by
    intro w hw c0 hc0 βw hβw
    have h1 : j - algebraMap k F c0 ∈ mwALGN_ordGe w 1 := Or.inr hc0
    have h2 := mwALGN_sum_aeval_mul_sub_mem w 1 hw h1 β (hβmem w hw) βw
      (fun i => (mwALGN_pin_iff w _ _).mp (hβw i)) (fun i => Polynomial.C (φ (θ s) ^ (i.val + 1)))
    simp only [Polynomial.aeval_C, Polynomial.eval_C] at h2
    have hsplit : Ls - algebraMap k F (c0 + ∑ i : Fin n, φ (θ s) ^ (i.val + 1) * βw i)
        = (j - algebraMap k F c0)
          + ((∑ i : Fin n, algebraMap k F (φ (θ s) ^ (i.val + 1)) * β i)
            - algebraMap k F (∑ i : Fin n, φ (θ s) ^ (i.val + 1) * βw i)) := by
      rw [hLs, map_add]
      ring
    rw [hsplit]
    exact add_mem h1 h2
  have hpin_unique : ∀ (w : Place k F) (x : F) (c c' : k), x - algebraMap k F c ∈ mwALGN_ordGe w 1 →
      x - algebraMap k F c' ∈ mwALGN_ordGe w 1 → c = c' := by
    intro w x c c' h h'
    have hsub := Submodule.sub_mem _ h' h
    rw [sub_sub_sub_cancel_left, ← map_sub] at hsub
    exact sub_eq_zero.mp (mwALGN_eq_zero_of_algebraMap_mem_ordGe w one_pos hsub)
  have hvalS : ∀ t, val (t, s.succ) = val (t, 0) + ∑ i : Fin n, φ (θ s) ^ (i.val + 1) * βpt t i := by
    intro t
    refine hpin_unique (pt t) Ls _ _ (Or.inr ?_) (hpinL (pt t) (hjmem_t t) _ (hval0 t) _ (hβpt t))
    exact hvalL t s

  have hNN : v.ord (∏ t, (Ls - algebraMap k F (val (t, s.succ))))
      = ((Finset.univ.filter fun t => pt t = v).card : ℤ) := by
    refine mwALGN_ord_prod_sub_eq_card v pt (hLsmem v hjmem) hs1' (fun t => val (t, s.succ))
      (fun t ht => ?_) (fun t ht => ?_)
    ·
      refine hpin_unique v Ls _ _ (Or.inr ?_) (Or.inr (by omega))
      have := hvalL t s
      rwa [ht] at this
    · show val (t, s.succ) ≠ cs
      rw [hvalS t]
      exact hs2 t ht

  have hN0 : (∏ t, (Ls - algebraMap k F (val (t, s.succ)))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro t _ h0
    have h := hvalL t s
    rw [show Polynomial.aeval j ((Polynomial.X : Polynomial K₀).map φ)
      + ∑ i : Fin n, Polynomial.aeval j ((Polynomial.C (θ s ^ (i.val + 1)) * d).map φ) * b i = Ls
      from rfl, h0, ord_zero] at h
    exact lt_irrefl _ h
  choose q hq using hdvd s
  have hq' : (∏ t, (Ls - algebraMap k F (val (t, s.succ)))) * gU
      = Polynomial.aeval j S * ∑ i', Polynomial.aeval j (q i') * b i' := by
    rw [show (∏ t, (Ls - algebraMap k F (val (t, s.succ)))) * gU
      = ∑ i' : Fin n, Polynomial.aeval j (E s i') * b i' from hE s, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [hq i', map_mul, mul_assoc]
  have hNA : v.ord (Polynomial.aeval j S)
      ≤ ((Finset.univ.filter fun t => pt t = v).card : ℤ) + v.ord gU :=
    mwALGN_ord_aeval_le_of_mul_eq v hjmem b hb S hN0 hgU0 hNN q hq'

  have hΘk : ∀ (w : Place k F), j ∈ w.toValuationSubring → ∀ c0 : k,
      0 < w.ord (j - algebraMap k F c0) →
      Polynomial.aeval j (Θ.map φ) - algebraMap k F ((Θ.map φ).eval c0) ∈ mwALGN_ordGe w 1 :=
    fun w hw c0 hc0 => mwALGN_aeval_sub_algebraMap_eval_mem w 1 hw (Or.inr hc0) (Θ.map φ)
  have hΘcv : (Θ.map φ).eval cv ≠ 0 := by
    intro h0
    have h := hΘk v hjmem cv hcv'
    rw [h0, map_zero, sub_zero] at h
    rcases h with h | h
    · exact hnz Θ (by rw [hΘ]; exact mul_ne_zero (mul_ne_zero hΔ hd) hq₀) h
    · omega
  have hcvjv : ∀ t', cv ≠ jv' t' := by
    intro t' heq
    apply hΘcv
    have hw : j ∈ (pt' t').toValuationSubring := by
      refine (pt' t').mem_of_ord_nonneg hjne ?_
      by_contra hneg
      push Not at hneg

      have h := hjv' t'
      by_cases hc : jv' t' = 0
      · rw [hc, map_zero, sub_zero] at h
        omega
      · have hlt : (pt' t').ord j < (pt' t').ord (-(algebraMap k F (jv' t'))) := by
          rw [ord_neg, mwALGN_ord_algebraMap (pt' t') hc]
          exact hneg
        have h2 := mwALGN_ord_add_eq_of_lt (pt' t') hjne (neg_ne_zero.mpr
          ((_root_.map_ne_zero _).mpr hc)) hlt
        rw [← sub_eq_add_neg] at h2
        omega
    have h := hΘk (pt' t') hw (jv' t') (hjv' t')
    have h2 : Polynomial.aeval j (Θ.map φ) ∈ mwALGN_ordGe (pt' t') 1 := Or.inr (hpt' t')
    have h3 := Submodule.sub_mem _ h2 h
    rw [sub_sub_cancel] at h3
    rw [heq]
    exact mwALGN_eq_zero_of_algebraMap_mem_ordGe (pt' t') one_pos h3
  have hS'0 : Polynomial.aeval j S' ≠ 0 ∧ v.ord (Polynomial.aeval j S') = 0 := by
    have hfac : ∀ t', (j - algebraMap k F (jv' t')) ≠ 0 ∧ v.ord (j - algebraMap k F (jv' t')) = 0 := by
      intro t'
      have hsplit : j - algebraMap k F (jv' t') = algebraMap k F (cv - jv' t') + (j - algebraMap k F cv) := by
        rw [map_sub]
        ring
      have hc0 : cv - jv' t' ≠ 0 := sub_ne_zero.mpr (hcvjv t')
      have hc0' : algebraMap k F (cv - jv' t') ≠ 0 := (_root_.map_ne_zero _).mpr hc0
      have hjcv0 : j - algebraMap k F cv ≠ 0 := by
        intro h0
        rw [h0, ord_zero] at hcv'
        exact lt_irrefl _ hcv'
      have hlt : v.ord (algebraMap k F (cv - jv' t')) < v.ord (j - algebraMap k F cv) := by
        rw [mwALGN_ord_algebraMap v hc0]
        exact hcv'
      have hne : j - algebraMap k F (jv' t') ≠ 0 := by
        rw [hsplit]
        intro h0
        have h1 : j - algebraMap k F cv = -algebraMap k F (cv - jv' t') :=
          (neg_eq_of_add_eq_zero_right h0).symm
        rw [h1, ord_neg] at hlt
        exact lt_irrefl _ hlt
      refine ⟨hne, ?_⟩
      rw [hsplit, mwALGN_ord_add_eq_of_lt v hc0' hjcv0 hlt, mwALGN_ord_algebraMap v hc0]
    have hprod : Polynomial.aeval j S' = ∏ t', (j - algebraMap k F (jv' t')) := by
      rw [hS'def, map_prod]
      refine Finset.prod_congr rfl fun t' _ => ?_
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [hprod]
    refine ⟨Finset.prod_ne_zero_iff.mpr fun t' _ => (hfac t').1, ?_⟩
    rw [mwALGN_ord_finset_prod v _ _ fun t' _ => (hfac t').1]
    exact Finset.sum_eq_zero fun t' _ => (hfac t').2

  have hS0 : Polynomial.aeval j S ≠ 0 := by
    intro h0
    have h := congrArg (v.ord) hq'
    rw [h0, zero_mul] at hq'
    exact mul_ne_zero hN0 hgU0 hq'
  have hden0 : Polynomial.aeval j (S * S' * q₀.map φ) ≠ 0 := by
    rw [map_mul, map_mul]
    exact mul_ne_zero (mul_ne_zero hS0 hS'0.1) hq₀'
  have hordden : v.ord (Polynomial.aeval j (S * S' * q₀.map φ)) = v.ord (Polynomial.aeval j S) := by
    rw [map_mul, map_mul, v.ord_mul (mul_ne_zero hS0 hS'0.1) hq₀', v.ord_mul hS0 hS'0.1, hS'0.2,
      hordq₀, add_zero, add_zero]
  have hordf : v.ord (gU * (Polynomial.aeval j (S * S' * q₀.map φ))⁻¹)
      = v.ord gU - v.ord (Polynomial.aeval j S) := by
    rw [v.ord_mul hgU0 (inv_ne_zero hden0), v.ord_inv, hordden]
    ring

  have hDv : D v = ((Finset.univ.filter fun t => pt t = v).card : ℤ) := by
    rw [henum v hvj, Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
    have h1 : (∑ t, (Finsupp.single (pt t) (1 : ℤ) : Divisor k F) v)
        = ((Finset.univ.filter fun t => pt t = v).card : ℤ) := by
      simp only [Finsupp.single_apply]
      exact Finset.sum_boole _ _
    have h2 : (∑ t', (Finsupp.single (pt' t') (1 : ℤ) : Divisor k F) v) = 0 := by
      refine Finset.sum_eq_zero fun t' _ => ?_
      rw [Finsupp.single_apply, if_neg]
      intro heq
      have h := hpt' t'
      rw [heq, hvΘ] at h
      exact lt_irrefl _ h
    rw [h1, h2, add_zero]
  have htwist : (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v = D v := by
    rw [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hv₀),
      smul_zero, sub_zero]
  rw [htwist, hordf, hDv]
  omega

end cfin

open scoped Classical in

theorem mwALGN_exists_pinData (j : F) (w : Place k F) :
    ∃ (cw : k) (εw : ℤ), ∀ c : k, j ∈ w.toValuationSubring →
      w.ord (j - algebraMap k F c) = if c = cw then εw else 0 := by
  classical
  by_cases h : ∃ c : k, 0 < w.ord (j - algebraMap k F c)
  · obtain ⟨cw, hcw⟩ := h
    refine ⟨cw, w.ord (j - algebraMap k F cw), fun c hj => ?_⟩
    by_cases hc : c = cw
    · rw [if_pos hc, hc]
    · rw [if_neg hc]
      have hmem : j - algebraMap k F c ∈ w.toValuationSubring := sub_mem hj (w.algebraMap_mem' c)
      have h0 := w.ord_nonneg_of_mem hmem
      by_contra hne
      have hpos : 0 < w.ord (j - algebraMap k F c) := lt_of_le_of_ne h0 (Ne.symm hne)
      have hne0 : cw - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
      have hx0 : j - algebraMap k F c ≠ 0 := by
        intro h0'
        rw [h0', ord_zero] at hpos
        exact lt_irrefl _ hpos
      have hy0 : j - algebraMap k F cw ≠ 0 := by
        intro h0'
        rw [h0', ord_zero] at hcw
        exact lt_irrefl _ hcw
      have hcc : (j - algebraMap k F c) + -(j - algebraMap k F cw) = algebraMap k F (cw - c) := by
        rw [map_sub]
        ring
      have hd0 : (j - algebraMap k F c) + -(j - algebraMap k F cw) ≠ 0 := by
        rw [hcc]
        exact (_root_.map_ne_zero _).mpr hne0
      have hmin := w.min_ord_le_ord_add hx0 (neg_ne_zero.mpr hy0) hd0
      rw [ord_neg, hcc, mwALGN_ord_algebraMap w hne0] at hmin
      have : 0 < min (w.ord (j - algebraMap k F c)) (w.ord (j - algebraMap k F cw)) := lt_min hpos hcw
      omega
  · push Not at h
    refine ⟨0, w.ord (j - algebraMap k F 0), fun c hj => ?_⟩
    by_cases hc : c = 0
    · rw [if_pos hc, hc]
    · rw [if_neg hc]
      have hmem : j - algebraMap k F c ∈ w.toValuationSubring := sub_mem hj (w.algebraMap_mem' c)
      have h0 := w.ord_nonneg_of_mem hmem
      have h1 := h c
      omega

open scoped Classical in

theorem mwALGN_ord_aeval_prod_X_sub_C (w : Place k F) {j : F} (hj : Transcendental k j)
    {cw : k} {εw : ℤ} (hpin : ∀ c : k, w.ord (j - algebraMap k F c) = if c = cw then εw else 0)
    {r : ℕ} (c : Fin r → k) :
    Polynomial.aeval j (∏ t, (Polynomial.X - Polynomial.C (c t))) ≠ 0 ∧
      w.ord (Polynomial.aeval j (∏ t, (Polynomial.X - Polynomial.C (c t))))
        = ((Finset.univ.filter fun t => c t = cw).card : ℤ) * εw := by
  classical
  have hfac0 : ∀ t, j - algebraMap k F (c t) ≠ 0 := by
    intro t h0
    apply hj
    rw [sub_eq_zero.mp h0]
    exact isAlgebraic_algebraMap _
  have hprod : Polynomial.aeval j (∏ t, (Polynomial.X - Polynomial.C (c t)))
      = ∏ t, (j - algebraMap k F (c t)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [hprod]
  refine ⟨Finset.prod_ne_zero_iff.mpr fun t _ => hfac0 t, ?_⟩
  rw [mwALGN_ord_finset_prod w _ _ fun t _ => hfac0 t]
  simp_rw [hpin]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

theorem mwALGN_ord_nonneg_of_ord_sub_pos (w : Place k F) {j : F} (hj : j ≠ 0) {c : k}
    (h : 0 < w.ord (j - algebraMap k F c)) : 0 ≤ w.ord j := by
  by_contra hneg
  push Not at hneg
  by_cases hc : c = 0
  · rw [hc, map_zero, sub_zero] at h
    omega
  · have hlt : w.ord j < w.ord (-(algebraMap k F c)) := by
      rw [ord_neg, mwALGN_ord_algebraMap w hc]
      exact hneg
    have h2 := mwALGN_ord_add_eq_of_lt w hj (neg_ne_zero.mpr ((_root_.map_ne_zero _).mpr hc)) hlt
    rw [← sub_eq_add_neg] at h2
    omega

theorem mwALGN_sum_le_degree (D : Divisor k F) (heff : ∀ v, 0 ≤ D v)
    (hdeg1 : ∀ v : Place k F, v.deg ≠ 0) (A : Finset (Place k F)) :
    (∑ v ∈ A, D v) ≤ Divisor.degree D := by
  classical
  have hdegsum : Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
    rfl
  rw [hdegsum]
  have hterm : ∀ v, D v ≤ D v * (v.deg : ℤ) := by
    intro v
    have h1 : (1 : ℤ) ≤ v.deg := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hdeg1 v)
    nlinarith [heff v]
  calc (∑ v ∈ A, D v) ≤ ∑ v ∈ A, D v * (v.deg : ℤ) := Finset.sum_le_sum fun v _ => hterm v
    _ ≤ ∑ v ∈ A ∪ D.support, D v * (v.deg : ℤ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          fun v _ _ => mul_nonneg (heff v) (by exact_mod_cast Nat.zero_le _)
    _ = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
        refine (Finset.sum_subset Finset.subset_union_right fun v _ hv => ?_).symm
        rw [Finsupp.notMem_support_iff.mp hv, zero_mul]

open scoped Classical in

theorem mwALGN_card_le_degree (D : Divisor k F) (heff : ∀ v, 0 ≤ D v)
    (hdeg1 : ∀ v : Place k F, v.deg ≠ 0) {r : ℕ} (pt : Fin r → Place k F)
    (hcount : ∀ t, ((Finset.univ.filter fun t₁ => pt t₁ = pt t).card : ℤ) ≤ D (pt t)) :
    (r : ℤ) ≤ Divisor.degree D := by
  classical
  have h1 : (r : ℤ) = ∑ v ∈ Finset.univ.image pt,
      ((Finset.univ.filter fun t => pt t = v).card : ℤ) := by
    have h := Finset.card_eq_sum_card_image pt Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact_mod_cast h
  rw [h1]
  refine le_trans (Finset.sum_le_sum fun v hv => ?_) (mwALGN_sum_le_degree D heff hdeg1 _)
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hv
  exact hcount t

theorem mwALGN_menu_inst {K₀ : Type*} [Field K₀] [Algebra K₀ k] {j : F} (hj : Transcendental k j)
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    (hfin : ∀ x : F, x ≠ 0 → {v : Place k F | x ∉ v.toValuationSubring}.Finite)
    (n : ℕ) (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (Θ : Polynomial K₀) (hΘ : Θ ≠ 0)
    (q₀ : Polynomial K₀) (hq₀ : q₀ ≠ 0) (v₀ : Place k F) (g e mdeg : ℕ) :
    ∃ (M : ℕ) (Rm : Fin M → ℕ) (Y : (l : Fin M) → Fin (Rm l) → Fin n × Fin (mdeg + 1) → k),
      ∀ (D : Divisor k F), (∀ v, 0 ≤ D v) → Divisor.degree D = (g : ℤ) →
      ∀ (r : ℕ) (pt : Fin r → Place k F) (r' : ℕ) (pt' : Fin r' → Place k F)
        (val0 : Fin r → k) (jv' : Fin r' → k),
      (∀ t, 0 ≤ (pt t).ord j ∧
        (pt t).ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) = 0) →
      (∀ t', 0 < (pt' t').ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k)))) →
      (∀ v : Place k F, 0 ≤ v.ord j → D v =
        ((∑ t, Finsupp.single (pt t) (1 : ℤ))
          + ∑ t', Finsupp.single (pt' t') (1 : ℤ) : Divisor k F) v) →
      (∀ t, 0 < (pt t).ord (j - algebraMap k F (val0 t))) →
      (∀ t', 0 < (pt' t').ord (j - algebraMap k F (jv' t'))) →
      ∃ l : Fin M, ∀ u : Fin n × Fin (mdeg + 1) → k, u ≠ 0 →
        ((∀ ρ : Fin (Rm l), ∑ col, Y l ρ col * u col = 0) ↔
          ∀ v : Place k F,
            (v.ord j < 0 ∨ 0 < v.ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) ∨ v = v₀) →
            0 ≤ (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v
              + v.ord ((∑ i : Fin n, Polynomial.aeval j
                    (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
                  * (Polynomial.aeval j
                      ((∏ t, (Polynomial.X - Polynomial.C (val0 t)))
                        * (∏ t', (Polynomial.X - Polynomial.C (jv' t')))
                        * q₀.map (algebraMap K₀ k)))⁻¹)) := by
  classical
  have _ := hbsp

  set φ : K₀ →+* k := algebraMap K₀ k with hφ
  set ΘF : F := Polynomial.aeval j (Θ.map φ) with hΘF
  have hjne : j ≠ 0 := fun h0 => hj (h0 ▸ isAlgebraic_zero)
  have hnzk : ∀ p : Polynomial k, p ≠ 0 → (Polynomial.aeval j p : F) ≠ 0 := fun p hp h0 => hj ⟨p, hp, h0⟩
  have hnz : ∀ p : Polynomial K₀, p ≠ 0 → (Polynomial.aeval j (p.map φ) : F) ≠ 0 := by
    intro p hp
    refine hnzk _ fun hmap0 => hp ?_
    exact Polynomial.map_injective φ φ.injective (hmap0.trans (Polynomial.map_zero φ).symm)
  have hΘF0 : ΘF ≠ 0 := hnz Θ hΘ
  have hq₀' : (Polynomial.aeval j (q₀.map φ) : F) ≠ 0 := hnz q₀ hq₀
  have hq₀k : q₀.map φ ≠ 0 := fun h0 => hq₀' (by rw [h0, map_zero])
  have hdegnz : ∀ v : Place k F, v.deg ≠ 0 :=
    fun v => Place.deg_ne_zero_of_finiteDimensional_adjoin j hj v

  have hZfin : {v : Place k F | v.ord j < 0 ∨ 0 < v.ord ΘF ∨ v = v₀}.Finite := by
    refine ((hfin j hjne).union ((hfin ΘF⁻¹ (inv_ne_zero hΘF0)).union
      (Set.finite_singleton v₀))).subset ?_
    rintro v (hv | hv | hv)
    · exact Or.inl fun hmem => absurd (v.ord_nonneg_of_mem hmem) (not_le.mpr hv)
    · refine Or.inr (Or.inl fun hmem => ?_)
      have h := v.ord_nonneg_of_mem hmem
      rw [ord_inv] at h
      omega
    · exact Or.inr (Or.inr hv)
  set ZF : Finset (Place k F) := hZfin.toFinset with hZF
  have hmemZ : ∀ v, v ∈ ZF ↔ (v.ord j < 0 ∨ 0 < v.ord ΘF ∨ v = v₀) := fun v => by
    rw [hZF, Set.Finite.mem_toFinset]
    rfl

  choose cz εz hcz using fun w : Place k F => mwALGN_exists_pinData j w
  obtain ⟨κ, hκ⟩ : ∃ κ : Place k F → ℤ, ∀ w, κ w = w.ord (Polynomial.aeval j (q₀.map φ)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨tw, htw⟩ : ∃ tw : Place k F → ℤ, ∀ w, tw w = if w = v₀ then (e : ℤ) else 0 :=
    ⟨_, fun _ => rfl⟩

  set gmap : (Fin n × Fin (mdeg + 1) → k) →ₗ[k] F :=
    Fintype.linearCombination k (fun col : Fin n × Fin (mdeg + 1) => j ^ (col.2 : ℕ) * b col.1)
    with hgmap
  have hg : ∀ u : Fin n × Fin (mdeg + 1) → k, gmap u
      = ∑ i : Fin n, Polynomial.aeval j
          (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i := by
    intro u
    rw [hgmap, Fintype.linearCombination_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun dd _ => ?_
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, Algebra.smul_def, mul_assoc]
  have hg0 : ∀ u : Fin n × Fin (mdeg + 1) → k, u ≠ 0 → gmap u ≠ 0 := by
    intro u hu h0
    apply hu
    rw [hg] at h0
    have h1 := hbli (fun i => ∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) h0
    funext ⟨i, dd⟩
    have h2 := congrArg (fun p : Polynomial k => p.coeff (dd : ℕ)) (h1 i)
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero, mul_ite, mul_one, mul_zero] at h2
    rw [Finset.sum_eq_single dd (fun dd' _ hne => by rw [if_neg (fun h => hne (Fin.ext h).symm)])
      (fun h => absurd (Finset.mem_univ dd) h), if_pos rfl] at h2
    exact h2

  obtain ⟨μ, hμ⟩ : ∃ μ : (Fin (g + 1) × Fin (g + 1) × (ZF → Fin (g + 1) × Fin (g + 1) × Fin (g + 1)))
      → ZF → ℤ, ∀ τ z, μ τ z =
        (if (z : Place k F).ord j < 0
          then ((τ.1 : ℕ) + (τ.2.1 : ℕ) + (q₀.natDegree : ℤ)) * (z : Place k F).ord j
          else (((τ.2.2 z).2.1 : ℕ) + ((τ.2.2 z).2.2 : ℕ) : ℤ) * εz z + κ z)
        - ((τ.2.2 z).1 : ℕ) + tw z := ⟨_, fun _ _ => rfl⟩
  obtain ⟨M, eT, Rm, Y, hY⟩ := mwALGN_exists_menu gmap (fun z : ZF => (z : Place k F)) μ
  refine ⟨M, Rm, Y, ?_⟩

  intro D heff hdeg r pt r' pt' val0 jv' hpt hpt' henum hval0 hjv'

  have hsum1 : ∀ (w : Place k F) {m : ℕ} (p : Fin m → Place k F),
      (∑ t, (Finsupp.single (p t) (1 : ℤ) : Divisor k F) w)
        = ((Finset.univ.filter fun t => p t = w).card : ℤ) := by
    intro w m p
    simp only [Finsupp.single_apply]
    exact Finset.sum_boole _ _
  have hcount : ∀ (w : Place k F), 0 ≤ w.ord j →
      ((Finset.univ.filter fun t => pt t = w).card : ℤ)
        + ((Finset.univ.filter fun t' => pt' t' = w).card : ℤ) = D w := by
    intro w hw
    rw [henum w hw, Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply,
      hsum1, hsum1]
  have hjpt' : ∀ t', 0 ≤ (pt' t').ord j :=
    fun t' => mwALGN_ord_nonneg_of_ord_sub_pos (pt' t') hjne (hjv' t')
  have hr : r ≤ g := by
    have h := mwALGN_card_le_degree D heff hdegnz pt fun t => by
      have := hcount (pt t) (hpt t).1
      have h0 : (0 : ℤ) ≤ ((Finset.univ.filter fun t' => pt' t' = pt t).card : ℤ) := by
        exact_mod_cast Nat.zero_le _
      omega
    rw [hdeg] at h
    exact_mod_cast h
  have hr' : r' ≤ g := by
    have h := mwALGN_card_le_degree D heff hdegnz pt' fun t' => by
      have := hcount (pt' t') (hjpt' t')
      have h0 : (0 : ℤ) ≤ ((Finset.univ.filter fun t => pt t = pt' t').card : ℤ) := by
        exact_mod_cast Nat.zero_le _
      omega
    rw [hdeg] at h
    exact_mod_cast h
  have hDz : ∀ z : ZF, (D z).toNat ≤ g := by
    intro z
    have h := mwALGN_sum_le_degree D heff hdegnz {(z : Place k F)}
    rw [Finset.sum_singleton, hdeg] at h
    exact Int.toNat_le.mpr h

  obtain ⟨τ, hτ1, hτ2, hτ3, hτ4, hτ5⟩ :
      ∃ τ : Fin (g + 1) × Fin (g + 1) × (ZF → Fin (g + 1) × Fin (g + 1) × Fin (g + 1)),
        (τ.1 : ℕ) = r ∧ (τ.2.1 : ℕ) = r' ∧ (∀ z, ((τ.2.2 z).1 : ℕ) = (D z).toNat) ∧
        (∀ z, ((τ.2.2 z).2.1 : ℕ) = (Finset.univ.filter fun t => val0 t = cz z).card) ∧
        (∀ z, ((τ.2.2 z).2.2 : ℕ) = (Finset.univ.filter fun t' => jv' t' = cz z).card) := by
    refine ⟨(⟨r, by omega⟩, ⟨r', by omega⟩, fun z => (⟨(D z).toNat, by have := hDz z; omega⟩,
      ⟨(Finset.univ.filter fun t => val0 t = cz z).card, ?_⟩,
      ⟨(Finset.univ.filter fun t' => jv' t' = cz z).card, ?_⟩)),
      rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    · have h := Finset.card_filter_le (Finset.univ : Finset (Fin r)) (fun t => val0 t = cz z)
      rw [Finset.card_univ, Fintype.card_fin] at h
      omega
    · have h := Finset.card_filter_le (Finset.univ : Finset (Fin r')) (fun t' => jv' t' = cz z)
      rw [Finset.card_univ, Fintype.card_fin] at h
      omega
  refine ⟨eT τ, fun u hu => ?_⟩
  rw [hY τ u, or_iff_right (hg0 u hu), hg u]

  set S : Polynomial k := ∏ t, (Polynomial.X - Polynomial.C (val0 t)) with hSdef
  set S' : Polynomial k := ∏ t', (Polynomial.X - Polynomial.C (jv' t')) with hS'def
  have hSm : S.Monic := Polynomial.monic_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _
  have hS'm : S'.Monic := Polynomial.monic_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _
  have hSd : S.natDegree = r := by
    rw [hSdef, Polynomial.natDegree_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _]
    simp
  have hS'd : S'.natDegree = r' := by
    rw [hS'def, Polynomial.natDegree_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _]
    simp
  have hq₀d : (q₀.map φ).natDegree = q₀.natDegree := Polynomial.natDegree_map_eq_of_injective φ.injective q₀
  have hden0 : (Polynomial.aeval j (S * S' * q₀.map φ) : F) ≠ 0 :=
    hnzk _ (mul_ne_zero (mul_ne_zero hSm.ne_zero hS'm.ne_zero) hq₀k)
  have hgu0 : (∑ i : Fin n, Polynomial.aeval j
      (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i) ≠ 0 := by
    rw [← hg]
    exact hg0 u hu
  have hμz : ∀ z : ZF, μ τ z = (z : Place k F).ord (Polynomial.aeval j (S * S' * q₀.map φ))
      - (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) z := by
    intro z
    have htwist : (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) z = D z - tw z := by
      rw [htw, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases h0 : (z : Place k F) = v₀
      · rw [if_pos h0.symm, if_pos h0, mul_one]
      · rw [if_neg (Ne.symm h0), if_neg h0, mul_zero]
    have hDz' : (((D z).toNat : ℕ) : ℤ) = D z := Int.toNat_of_nonneg (heff z)
    rw [hμ, hτ1, hτ2, hτ3, hτ4, hτ5, htwist, hDz', map_mul, map_mul,
      (z : Place k F).ord_mul (mul_ne_zero (hnzk S hSm.ne_zero) (hnzk S' hS'm.ne_zero)) hq₀',
      (z : Place k F).ord_mul (hnzk S hSm.ne_zero) (hnzk S' hS'm.ne_zero)]
    by_cases hzj : (z : Place k F).ord j < 0
    · rw [if_pos hzj, (mwALGN_ord_aeval_of_ord_neg _ hzj S hSm.ne_zero).2,
        (mwALGN_ord_aeval_of_ord_neg _ hzj S' hS'm.ne_zero).2,
        (mwALGN_ord_aeval_of_ord_neg _ hzj (q₀.map φ) hq₀k).2, hSd, hS'd, hq₀d]
      ring
    · have hjz : j ∈ (z : Place k F).toValuationSubring :=
        (z : Place k F).mem_of_ord_nonneg hjne (not_lt.mp hzj)
      rw [if_neg hzj, hSdef, hS'def,
        (mwALGN_ord_aeval_prod_X_sub_C _ hj (fun c => hcz z c hjz) val0).2,
        (mwALGN_ord_aeval_prod_X_sub_C _ hj (fun c => hcz z c hjz) jv').2, hκ]
      ring

  constructor
  · intro h v hv
    have hz : v ∈ ZF := (hmemZ v).mpr hv
    have h1 := h ⟨v, hz⟩
    rw [hμz ⟨v, hz⟩] at h1
    have h2 : v.ord ((∑ i : Fin n, Polynomial.aeval j
        (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
        * (Polynomial.aeval j (S * S' * q₀.map φ))⁻¹)
        = v.ord (∑ i : Fin n, Polynomial.aeval j
          (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
          - v.ord (Polynomial.aeval j (S * S' * q₀.map φ)) := by
      rw [v.ord_mul hgu0 (inv_ne_zero hden0), ord_inv]
      ring
    rw [h2]
    have h3 : ((⟨v, hz⟩ : ZF) : Place k F) = v := rfl
    rw [h3] at h1
    omega
  · intro h z
    have h1 := h z ((hmemZ z).mp z.2)
    rw [(z : Place k F).ord_mul hgu0 (inv_ne_zero hden0), ord_inv] at h1
    rw [hμz z]
    omega

end AlgebraicCurve.Place

namespace mwALGCdev

private def mwALGC_heqvN (a n r : ℕ) : Fin (a * n * r) ≃ (Fin a × Fin n × Fin r) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongrLeft fun _ => finProdFinEquiv.symm).trans (Equiv.prodAssoc _ _ _))
section rows

variable {K₀ : Type*} [CommRing K₀]

private def mwALGC_Suniv (a r : ℕ) : Polynomial (MvPolynomial (Fin (a + 1) × Fin (r + 1)) K₀) :=
  Polynomial.X ^ r
    + ∑ m : Fin r, Polynomial.C (MvPolynomial.X ((0 : Fin (a + 1)), m.castSucc)) * Polynomial.X ^ (m : ℕ)

private theorem mwALGC_Suniv_monic (a r : ℕ) :
    (mwALGC_Suniv a r : Polynomial (MvPolynomial (Fin (a + 1) × Fin (r + 1)) K₀)).Monic := by
  nontriviality MvPolynomial (Fin (a + 1) × Fin (r + 1)) K₀
  unfold mwALGC_Suniv
  refine Polynomial.monic_X_pow_add ((Polynomial.degree_sum_le _ _).trans_lt ?_)
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe r)).mpr fun m _ => ?_
  exact (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt (WithBot.coe_lt_coe.mpr m.2)

private def mwALGC_Euniv (a n mdeg : ℕ) (Ms : Fin a → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (r : ℕ) (s : Fin a) (i' i : Fin n) (dd : Fin (mdeg + 1)) :
    Polynomial (MvPolynomial (Fin (a + 1) × Fin (r + 1)) K₀) :=
  (∑ m : Fin (r + 1), Polynomial.C (MvPolynomial.X (s.succ, m))
      * ((Ms s ^ (m : ℕ)) i' i).map (algebraMap K₀ (MvPolynomial (Fin (a + 1) × Fin (r + 1)) K₀)))
    * Polynomial.X ^ (dd : ℕ)

private def mwALGC_chowFamily (a n mdeg : ℕ) (Ms : Fin a → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (r : ℕ) (ρ : Fin a × Fin n × Fin r) (col : Fin n × Fin (mdeg + 1)) :
    MvPolynomial (Fin (a + 1) × Fin (r + 1)) K₀ :=
  (mwALGC_Euniv a n mdeg Ms r ρ.1 ρ.2.1 col.1 col.2 %ₘ mwALGC_Suniv a r).coeff ρ.2.2

variable {k : Type*} [CommRing k] [Algebra K₀ k]

private def mwALGC_Ek (a n mdeg : ℕ) (Ms : Fin a → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (r : ℕ) (val : Fin r × Fin (a + 1) → k) (s : Fin a) (i' i : Fin n) (dd : Fin (mdeg + 1)) :
    Polynomial k :=
  (∑ m : Fin (r + 1),
      Polynomial.C ((∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, s.succ)))).coeff (m : ℕ))
      * ((Ms s ^ (m : ℕ)) i' i).map (algebraMap K₀ k))
    * Polynomial.X ^ (dd : ℕ)

private theorem mwALGC_aeval_chowFamily (a n mdeg : ℕ)
    (Ms : Fin a → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (r : ℕ) (val : Fin r × Fin (a + 1) → k) (ρ : Fin a × Fin n × Fin r)
    (col : Fin n × Fin (mdeg + 1)) :
    MvPolynomial.aeval
        (fun ak : Fin (a + 1) × Fin (r + 1) =>
          (∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, ak.1)))).coeff (ak.2 : ℕ))
        (mwALGC_chowFamily a n mdeg Ms r ρ col)
      = (mwALGC_Ek a n mdeg Ms r val ρ.1 ρ.2.1 col.1 col.2
          %ₘ (∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))))).coeff (ρ.2.2 : ℕ) := by
  classical
  set f : MvPolynomial (Fin (a + 1) × Fin (r + 1)) K₀ →ₐ[K₀] k := MvPolynomial.aeval
    (fun ak : Fin (a + 1) × Fin (r + 1) =>
      (∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, ak.1)))).coeff (ak.2 : ℕ)) with hf
  set S : Polynomial k := ∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))) with hSdef
  have hSm : S.Monic := Polynomial.monic_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _

  have hS : (mwALGC_Suniv a r).map (f : MvPolynomial (Fin (a + 1) × Fin (r + 1)) K₀ →+* k) = S := by
    nontriviality k
    have hSd : S.natDegree = r := by
      rw [hSdef, Polynomial.natDegree_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _]
      simp
    unfold mwALGC_Suniv
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    conv_rhs => rw [hSm.as_sum, hSd, Finset.sum_range (fun i => Polynomial.C (S.coeff i) * Polynomial.X ^ i)]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hf,
      AlgHom.coe_toRingHom, MvPolynomial.aeval_X]
    rfl

  have hE : (mwALGC_Euniv a n mdeg Ms r ρ.1 ρ.2.1 col.1 col.2).map
      (f : MvPolynomial (Fin (a + 1) × Fin (r + 1)) K₀ →+* k)
      = mwALGC_Ek a n mdeg Ms r val ρ.1 ρ.2.1 col.1 col.2 := by
    unfold mwALGC_Euniv mwALGC_Ek
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, AlgHom.comp_algebraMap, hf,
      AlgHom.coe_toRingHom, MvPolynomial.aeval_X]
  show (f : MvPolynomial (Fin (a + 1) × Fin (r + 1)) K₀ →+* k)
      ((mwALGC_Euniv a n mdeg Ms r ρ.1 ρ.2.1 col.1 col.2 %ₘ mwALGC_Suniv a r).coeff (ρ.2.2 : ℕ)) = _
  rw [← Polynomial.coeff_map, Polynomial.map_modByMonic _ (mwALGC_Suniv_monic a r), hE, hS]

private theorem mwALGC_rows_iff_dvd (a n mdeg : ℕ)
    (Ms : Fin a → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (r : ℕ) (val : Fin r × Fin (a + 1) → k) (u : Fin n × Fin (mdeg + 1) → k) :
    (∀ ρ : Fin a × Fin n × Fin r, ∑ col, MvPolynomial.aeval
        (fun ak : Fin (a + 1) × Fin (r + 1) =>
          (∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, ak.1)))).coeff (ak.2 : ℕ))
        (mwALGC_chowFamily a n mdeg Ms r ρ col) * u col = 0)
      ↔ (∀ (s : Fin a) (i' : Fin n),
        (∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))))
          ∣ ∑ col, Polynomial.C (u col) * mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2) := by
  classical
  simp_rw [mwALGC_aeval_chowFamily]
  set S : Polynomial k := ∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))) with hSdef
  have hSm : S.Monic := Polynomial.monic_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _

  have hlin : ∀ (s : Fin a) (i' : Fin n),
      (∑ col, Polynomial.C (u col) * mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2) %ₘ S
        = ∑ col, u col • (mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2 %ₘ S) := by
    intro s i'
    have happ : ∀ p : Polynomial k, Polynomial.modByMonicHom S p = p %ₘ S := fun p => rfl
    rw [← happ, map_sum]
    refine Finset.sum_congr rfl fun col _ => ?_
    rw [happ, Polynomial.C_mul', Polynomial.smul_modByMonic]

  have hcoeff : ∀ (s : Fin a) (i' : Fin n) (m : ℕ),
      (∑ col, u col • (mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2 %ₘ S)).coeff m
        = ∑ col, (mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2 %ₘ S).coeff m * u col := by
    intro s i' m
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun col _ => ?_
    rw [Polynomial.coeff_smul, smul_eq_mul, mul_comm]
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact ⟨fun _ s i' => ⟨0, Subsingleton.elim _ _⟩, fun _ ρ => Subsingleton.elim _ _⟩
  by_cases hr : r = 0
  · subst hr
    refine ⟨fun _ s i' => ?_, fun _ ρ => Fin.elim0 ρ.2.2⟩
    rw [show S = 1 from by rw [hSdef]; exact Finset.prod_of_isEmpty _]
    exact one_dvd _
  have hS1 : S ≠ 1 := by
    intro h1
    have hSd : S.natDegree = r := by
      rw [hSdef, Polynomial.natDegree_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _]
      simp
    rw [h1, Polynomial.natDegree_one] at hSd
    exact hr hSd.symm
  constructor
  · intro h s i'
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd hSm, hlin]
    refine Polynomial.ext fun m => ?_
    rw [Polynomial.coeff_zero]
    by_cases hm : m < r
    · rw [hcoeff]
      exact h (s, i', ⟨m, hm⟩)
    · refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le ?_ (not_lt.mp hm))
      rw [← hlin]
      have hSd : S.natDegree = r := by
        rw [hSdef, Polynomial.natDegree_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _]
        simp
      have := Polynomial.natDegree_modByMonic_lt
        (∑ col, Polynomial.C (u col) * mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2) hSm hS1
      rwa [hSd] at this
  · rintro h ⟨s, i', ρ₀⟩
    have h1 := h s i'
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd hSm, hlin] at h1
    have h2 := congrArg (fun p : Polynomial k => p.coeff (ρ₀ : ℕ)) h1
    simp only [Polynomial.coeff_zero] at h2
    rw [hcoeff] at h2
    exact h2

end rows

section enumeration

variable {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]

private theorem mwALGC_menu {j : F} (hj : Transcendental k j)
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    (hfin : ∀ x : F, x ≠ 0 → {v : Place k F | x ∉ v.toValuationSubring}.Finite)
    (n : ℕ) (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (Θ : Polynomial K₀) (hΘ : Θ ≠ 0)
    (q₀ : Polynomial K₀) (hq₀ : q₀ ≠ 0) (v₀ : Place k F) (g e mdeg : ℕ) :
    ∃ (M : ℕ) (Rm : Fin M → ℕ) (Y : (l : Fin M) → Fin (Rm l) → Fin n × Fin (mdeg + 1) → k),
      ∀ (D : Divisor k F), (∀ v, 0 ≤ D v) → Divisor.degree D = (g : ℤ) →
      ∀ (r : ℕ) (pt : Fin r → Place k F) (r' : ℕ) (pt' : Fin r' → Place k F)
        (val0 : Fin r → k) (jv' : Fin r' → k),
      (∀ t, 0 ≤ (pt t).ord j ∧
        (pt t).ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) = 0) →
      (∀ t', 0 < (pt' t').ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k)))) →
      (∀ v : Place k F, 0 ≤ v.ord j → D v =
        ((∑ t, Finsupp.single (pt t) (1 : ℤ))
          + ∑ t', Finsupp.single (pt' t') (1 : ℤ) : Divisor k F) v) →
      (∀ t, 0 < (pt t).ord (j - algebraMap k F (val0 t))) →
      (∀ t', 0 < (pt' t').ord (j - algebraMap k F (jv' t'))) →
      ∃ l : Fin M, ∀ u : Fin n × Fin (mdeg + 1) → k, u ≠ 0 →
        ((∀ ρ : Fin (Rm l), ∑ col, Y l ρ col * u col = 0) ↔
          ∀ v : Place k F,
            (v.ord j < 0 ∨ 0 < v.ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) ∨ v = v₀) →
            0 ≤ (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v
              + v.ord ((∑ i : Fin n, Polynomial.aeval j
                    (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
                  * (Polynomial.aeval j
                      ((∏ t, (Polynomial.X - Polynomial.C (val0 t)))
                        * (∏ t', (Polynomial.X - Polynomial.C (jv' t')))
                        * q₀.map (algebraMap K₀ k)))⁻¹)) :=
  AlgebraicCurve.Place.mwALGN_menu_inst hj hfin n b hbli hbsp Θ hΘ q₀ hq₀ v₀ g e mdeg

end enumeration

section ker

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_exists_symmValue_rows_kernel_iff.AlgebraicCurve Polynomial"

variable {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]

private theorem mwALGC_ker {j : F}
    (n : ℕ) (b : Fin n → F)
    (q₀ : Polynomial K₀) (v₀ : Place k F) (e mdeg : ℕ)
    (Θ : Polynomial K₀) (a : ℕ)
    (Ms : Fin a → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (Rml : ℕ) (Yl : Fin Rml → Fin n × Fin (mdeg + 1) → k)
    (D : Divisor k F)
    (r : ℕ) (val : Fin r × Fin (a + 1) → k)
    (r' : ℕ) (jv' : Fin r' → k)

    (hMenuD : ∀ u : Fin n × Fin (mdeg + 1) → k, u ≠ 0 →
      ((∀ ρ : Fin Rml, ∑ col, Yl ρ col * u col = 0) ↔
        ∀ v : Place k F, (v.ord j < 0 ∨
          0 < v.ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) ∨ v = v₀) →
          0 ≤ (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v
            + v.ord ((∑ i : Fin n, Polynomial.aeval j
                  (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
                * (Polynomial.aeval j
                    ((∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))))
                      * (∏ t', (Polynomial.X - Polynomial.C (jv' t')))
                      * q₀.map (algebraMap K₀ k)))⁻¹)))

    (hKERgood : ∀ u : Fin n × Fin (mdeg + 1) → k, u ≠ 0 →
      (∀ (s : Fin a) (i' : Fin n), (∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))))
        ∣ ∑ col : Fin n × Fin (mdeg + 1),
            Polynomial.C (u col) * mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2) →
      ∀ v : Place k F, ¬ (v.ord j < 0 ∨
          0 < v.ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) ∨ v = v₀) →
        0 ≤ (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v
          + v.ord ((∑ i : Fin n, Polynomial.aeval j
                (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
              * (Polynomial.aeval j
                  ((∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))))
                    * (∏ t', (Polynomial.X - Polynomial.C (jv' t')))
                    * q₀.map (algebraMap K₀ k)))⁻¹))

    (hKERchow : ∀ u : Fin n × Fin (mdeg + 1) → k, u ≠ 0 →
      (∀ v : Place k F,
        0 ≤ (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v
          + v.ord ((∑ i : Fin n, Polynomial.aeval j
                (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
              * (Polynomial.aeval j
                  ((∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))))
                    * (∏ t', (Polynomial.X - Polynomial.C (jv' t')))
                    * q₀.map (algebraMap K₀ k)))⁻¹)) →
      ∀ (s : Fin a) (i' : Fin n), (∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))))
        ∣ ∑ col : Fin n × Fin (mdeg + 1),
            Polynomial.C (u col) * mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2) :
    ∀ u : Fin n × Fin (mdeg + 1) → k,
      ((∀ ρ : Fin (a * n * r), ∑ col, MvPolynomial.aeval
            (fun ak : Fin (a + 1) × Fin (r + 1) =>
              (∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, ak.1)))).coeff ak.2)
            (mwALGC_chowFamily a n mdeg Ms r (mwALGC_heqvN a n r ρ) col) * u col = 0) ∧
        (∀ ρ : Fin Rml, ∑ col, Yl ρ col * u col = 0)) ↔
      (u = 0 ∨ ∀ v : Place k F,
        0 ≤ (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v
          + v.ord ((∑ i : Fin n, Polynomial.aeval j
                (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
              * (Polynomial.aeval j
                  ((∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))))
                    * (∏ t', (Polynomial.X - Polynomial.C (jv' t')))
                    * q₀.map (algebraMap K₀ k)))⁻¹)) := by
  intro u
  set S : Polynomial k := ∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, 0))) with hSdef

  have hrows_iff :
      (∀ ρ : Fin (a * n * r), ∑ col, MvPolynomial.aeval
          (fun ak : Fin (a + 1) × Fin (r + 1) =>
            (∏ t : Fin r, (Polynomial.X - Polynomial.C (val (t, ak.1)))).coeff ak.2)
          (mwALGC_chowFamily a n mdeg Ms r (mwALGC_heqvN a n r ρ) col) * u col = 0)
      ↔ (∀ (s : Fin a) (i' : Fin n), S
          ∣ ∑ col : Fin n × Fin (mdeg + 1),
            Polynomial.C (u col) * mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2) := by
    rw [Equiv.forall_congr_left (mwALGC_heqvN a n r)]
    refine Iff.trans ?_ (mwALGC_rows_iff_dvd a n mdeg Ms r val u)
    simp only [Equiv.apply_symm_apply, Prod.forall]

  rcases eq_or_ne u 0 with hu0 | hu
  · subst hu0
    refine ⟨fun _ => Or.inl rfl, fun _ => ⟨fun _ => ?_, fun _ => ?_⟩⟩ <;>
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]

  constructor
  · rintro ⟨hchow, hY⟩
    right
    intro v
    by_cases hvbad : v.ord j < 0 ∨
        0 < v.ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) ∨ v = v₀
    · exact (hMenuD u hu).mp hY v hvbad
    · exact hKERgood u hu (hrows_iff.mp hchow) v hvbad
  · rintro (hu0' | hord)
    · exact absurd hu0' hu
    refine ⟨?_, ?_⟩
    · exact hrows_iff.mpr (hKERchow u hu hord)
    · exact (hMenuD u hu).mpr (fun v _ => hord v)

end ker
end mwALGCdev

theorem solution
    {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]
    {j : F} (hj : Transcendental k j)
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F] [CharZero k]
    (hfin : ∀ x : F, x ≠ 0 → {v : Place k F | x ∉ v.toValuationSubring}.Finite)
    (hrat : ∀ (v : Place k F) (x : F), j ∈ v.toValuationSubring →
      IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ c : k, x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c))
    (n : ℕ) (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'')
    (q₀ : Polynomial K₀) (v₀ : Place k F) (g e mdeg : ℕ) :
    ∃ (Θ : Polynomial K₀) (a : ℕ) (cL₀ : Fin a → Polynomial K₀) (cL : Fin a → Fin n → Polynomial K₀)
      (χ : Fin a → Polynomial (Polynomial K₀))
      (M : ℕ) (Rm : Fin M → ℕ) (Y : (l : Fin M) → Fin (Rm l) → Fin n × Fin (mdeg + 1) → k)
      (R : Fin (g + 1) → ℕ)
      (P : (r : Fin (g + 1)) → Fin (R r) → Fin n × Fin (mdeg + 1) →
        MvPolynomial (Fin (a + 1) × Fin ((r : ℕ) + 1)) K₀),
      (∀ s, (χ s).Monic) ∧
      ∀ (D : Divisor k F), (∀ v, 0 ≤ D v) → Divisor.degree D = (g : ℤ) →
        ∃ (r : Fin (g + 1)) (l : Fin M) (pt : Fin (r : ℕ) → Place k F)
          (val : Fin (r : ℕ) × Fin (a + 1) → k)
          (r' : ℕ) (pt' : Fin r' → Place k F) (jv' : Fin r' → k),
          (∀ t, 0 ≤ (pt t).ord j ∧
            (pt t).ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) = 0) ∧
          (∀ t', 0 < (pt' t').ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k)))) ∧
          (∀ v : Place k F, 0 ≤ v.ord j → D v =
            ((∑ t, Finsupp.single (pt t) (1 : ℤ))
              + ∑ t', Finsupp.single (pt' t') (1 : ℤ) : Divisor k F) v) ∧
          (∀ t, 0 < (pt t).ord (j - algebraMap k F (val (t, 0)))) ∧
          (∀ t (s : Fin a), 0 < (pt t).ord
            ((Polynomial.aeval j ((cL₀ s).map (algebraMap K₀ k))
              + ∑ i : Fin n, Polynomial.aeval j ((cL s i).map (algebraMap K₀ k)) * b i)
              - algebraMap k F (val (t, s.succ)))) ∧
          (∀ t', 0 < (pt' t').ord (j - algebraMap k F (jv' t'))) ∧
          (∀ t (s : Fin a), Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ k) (val (t, 0)))
              (val (t, s.succ)) (χ s) = 0) ∧
          ∀ u : Fin n × Fin (mdeg + 1) → k,
            ((∀ ρ : Fin (R r), ∑ col, MvPolynomial.aeval
                  (fun ak : Fin (a + 1) × Fin ((r : ℕ) + 1) =>
                    (∏ t : Fin (r : ℕ), (Polynomial.X - Polynomial.C (val (t, ak.1)))).coeff ak.2)
                  (P r ρ col) * u col = 0) ∧
              (∀ ρ : Fin (Rm l), ∑ col, Y l ρ col * u col = 0)) ↔
            (u = 0 ∨ ∀ v : Place k F,
              0 ≤ (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v
                + v.ord ((∑ i : Fin n, Polynomial.aeval j
                      (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
                    * (Polynomial.aeval j
                        ((∏ t : Fin (r : ℕ), (Polynomial.X - Polynomial.C (val (t, 0))))
                          * (∏ t', (Polynomial.X - Polynomial.C (jv' t')))
                          * q₀.map (algebraMap K₀ k)))⁻¹)) := by
  classical
  have hjne : j ≠ 0 := fun h => hj (h ▸ isAlgebraic_zero)

  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    exfalso
    obtain ⟨q, c, hq, hqe⟩ := hbsp 1
    rw [Finset.univ_eq_empty, Finset.sum_empty, one_mul] at hqe
    exact hj ⟨q, hq, hqe⟩

  rcases eq_or_ne q₀ 0 with hq₀0 | hq₀
  · subst hq₀0

    have hIdb₀ := mwALGMdev.mwALGM_isIntegral_db hj n b hbsp d hd A hmul
    have hdegnz₀ : ∀ v : Place k F, v.deg ≠ 0 :=
      fun v => Place.deg_ne_zero_of_finiteDimensional_adjoin j hj v
    let ncol : ℕ := n * (mdeg + 1)
    let ec : Fin n × Fin (mdeg + 1) ≃ Fin ncol := finProdFinEquiv
    refine ⟨d, 0, Fin.elim0, Fin.elim0, Fin.elim0, 2, fun _ => ncol,
      fun l ρ col => if (l : ℕ) = 0 then 0 else (if ρ = ec col then 1 else 0),
      fun _ => 0, fun _ => Fin.elim0, fun s => s.elim0, ?_⟩
    intro D heff hdeg
    obtain ⟨r, hrle, pt, val, βpt, r', pt', jv', hpt, hpt', henum, hval0, hvalL, hjv', hβpt,
      hdord⟩ := mwALGMdev.mwALGM_enum hj hrat n b d hd hIdb₀ d hd (dvd_refl d) 0 Fin.elim0
        Fin.elim0 (fun s => s.elim0) (fun s => s.elim0) hdegnz₀ g D heff hdeg
    have hfeq0 : ∀ (gU : F) (p : Polynomial k) (v : Place k F),
        v.ord (gU * (Polynomial.aeval j
          (p * (0 : Polynomial K₀).map (algebraMap K₀ k)))⁻¹) = 0 := by
      intro gU p v
      simp only [Polynomial.map_zero, mul_zero, map_zero, inv_zero, Place.ord_zero]
    by_cases heffv : ∀ v, 0 ≤ (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v
    ·
      refine ⟨⟨r, Nat.lt_succ_of_le hrle⟩, 0, pt, val, r', pt', jv',
        hpt, hpt', henum, hval0, fun t s => s.elim0, hjv', fun t s => s.elim0, fun u => ?_⟩
      refine ⟨fun _ => Or.inr fun v => ?_,
        fun _ => ⟨fun ρ => ρ.elim0, fun ρ => by
          simp only [Fin.val_zero, if_true, zero_mul, Finset.sum_const_zero]⟩⟩
      rw [hfeq0 _ _ v, add_zero]; exact heffv v
    ·
      refine ⟨⟨r, Nat.lt_succ_of_le hrle⟩, 1, pt, val, r', pt', jv',
        hpt, hpt', henum, hval0, fun t s => s.elim0, hjv', fun t s => s.elim0, fun u => ?_⟩
      have hl1 : ((1 : Fin 2) : ℕ) ≠ 0 := one_ne_zero
      constructor
      · rintro ⟨_, hY⟩
        left
        funext col
        have h := hY (ec col)
        simp only [if_neg hl1, ite_mul, one_mul, zero_mul, ← ec.eq_symm_apply,
          Finset.sum_ite_eq, Finset.mem_univ, if_true, Equiv.symm_apply_apply] at h
        exact h
      · rintro (hu0 | hord)
        · subst hu0
          exact ⟨fun ρ => ρ.elim0, fun ρ => by
            simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]⟩
        · exact absurd (fun v => by
            have h := hord v; rw [hfeq0 _ _ v, add_zero] at h; exact h) heffv

  have hIdb := mwALGMdev.mwALGM_isIntegral_db hj n b hbsp d hd A hmul
  obtain ⟨Δ, hΔ, hG⟩ :=
    mwALGMdev.mwALGM_gram_denom hj n b hbli hbsp d hd A hmul

  set Θ : Polynomial K₀ := Δ * d * q₀ with hΘdef
  have hΘ : Θ ≠ 0 := mul_ne_zero (mul_ne_zero hΔ hd) hq₀
  have hdΘ : d ∣ Θ := (Dvd.intro_left Δ rfl).mul_right q₀

  have hK₀char : CharZero K₀ :=
    (RingHom.charZero_iff (algebraMap K₀ k).injective).mpr inferInstance

  have hθchoice : ∃ (θ : Fin (n * (g + 1) + 1) → K₀), Function.Injective θ ∧
      ∀ (s : Fin (n * (g + 1) + 1)) (c : k),
        (Polynomial.aeval j (Polynomial.X.map (algebraMap K₀ k))
          + ∑ i : Fin n, Polynomial.aeval j ((Polynomial.C (θ s ^ (i.val + 1)) * d).map
              (algebraMap K₀ k)) * b i)
          ≠ algebraMap k F c :=
    mwALGMdev.mwALGM_theta_choice hK₀char n b d g
      (fun β θc hθc => Place.mwALGN_exists_nonconst_form hj β θc hθc)
  let a : ℕ := n * (g + 1) + 1
  obtain ⟨θ, hθinj, hLnc⟩ := hθchoice
  let cL₀ : Fin a → Polynomial K₀ := fun _ => Polynomial.X
  let cL : Fin a → Fin n → Polynomial K₀ := fun s i => Polynomial.C (θ s ^ (i.val + 1)) * d
  have hcLd : ∀ s i, d ∣ cL s i := fun s i => Dvd.intro_left _ rfl

  have hχlane : ∀ s : Fin a, ∃ (M : Matrix (Fin n) (Fin n) (Polynomial K₀))
      (χ : Polynomial (Polynomial K₀)), χ.Monic ∧
      (∀ (m : ℕ) (i : Fin n),
        (Polynomial.aeval j ((cL₀ s).map (algebraMap K₀ k))
            + ∑ i' : Fin n, Polynomial.aeval j (((fun i => Polynomial.C (θ s ^ (i.val + 1))) i'
                * d).map (algebraMap K₀ k)) * b i') ^ m
          * (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i)
        = ∑ i' : Fin n, Polynomial.aeval j (((M ^ m) i' i).map (algebraMap K₀ k))
            * (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i')) ∧
      Polynomial.eval₂
        ((Polynomial.aeval j).toRingHom.comp (Polynomial.mapRingHom (algebraMap K₀ k)))
        (Polynomial.aeval j ((cL₀ s).map (algebraMap K₀ k))
          + ∑ i' : Fin n, Polynomial.aeval j (((fun i => Polynomial.C (θ s ^ (i.val + 1))) i'
              * d).map (algebraMap K₀ k)) * b i')
        χ = 0 := by
    intro s
    exact mwALGMdev.mwALGM_exists_mulMatrix_chi hj n b hbsp d hd A hmul
      (cL₀ s) (fun i => Polynomial.C (θ s ^ (i.val + 1)))
  choose Ms χ hχmon hpow hkill using hχlane

  obtain ⟨M, Rm, Y, hMenu⟩ :=
    mwALGCdev.mwALGC_menu hj hfin n b hbli hbsp Θ hΘ q₀ hq₀ v₀ g e mdeg

  refine ⟨Θ, a, cL₀, cL, χ, M, Rm, Y, fun r => a * n * (r : ℕ),
    fun r ρ col => mwALGCdev.mwALGC_chowFamily a n mdeg Ms (r : ℕ)
      (mwALGCdev.mwALGC_heqvN a n (r : ℕ) ρ) col, hχmon, ?_⟩

  intro D heff hdeg
  have hdegnz : ∀ v : Place k F, v.deg ≠ 0 :=
    fun v => Place.deg_ne_zero_of_finiteDimensional_adjoin j hj v
  obtain ⟨r, hrle, pt, val, βpt, r', pt', jv', hpt, hpt', henum, hval0, hvalL, hjv', hβpt, hdord⟩ :=
    mwALGMdev.mwALGM_enum hj hrat n b d hd hIdb Θ hΘ hdΘ a cL₀ cL hcLd hLnc hdegnz g D heff hdeg
  obtain ⟨l, hMenuD⟩ := hMenu D heff hdeg r pt r' pt' (fun t => val (t, 0)) jv'
    hpt hpt' henum hval0 hjv'
  have hrlt : r < g + 1 := Nat.lt_succ_of_le hrle
  refine ⟨⟨r, hrlt⟩, l, pt, val, r', pt', jv', hpt, hpt', henum, hval0, hvalL, hjv', ?_, ?_⟩
  ·
    intro t s
    have hjmem : j ∈ (pt t).toValuationSubring := (pt t).mem_of_ord_nonneg hjne (hpt t).1
    have hIform := mwALGMdev.mwALGM_isIntegral_form hj n b hbsp d hd A hmul
      (cL₀ s) (fun i => Polynomial.C (θ s ^ (i.val + 1)))
    have hLsmem : (Polynomial.aeval j ((cL₀ s).map (algebraMap K₀ k))
          + ∑ i' : Fin n, Polynomial.aeval j
              (((fun i => Polynomial.C (θ s ^ (i.val + 1))) i' * d).map (algebraMap K₀ k)) * b i')
        ∈ (pt t).toValuationSubring :=
      (pt t).mem_toValuationSubring_of_isIntegral_adjoin hjmem hIform
    exact mwALGMdev.mwALGM_pin_eval₂_eq_zero (pt t) hjmem hLsmem (Or.inr (hval0 t))
      (Or.inr (hvalL t s)) (χ s) (hkill s)
  ·

    have hdj0 : Polynomial.aeval j (d.map (algebraMap K₀ k)) ≠ 0 := fun h0 =>
      hj ⟨d.map (algebraMap K₀ k),
        (Polynomial.map_ne_zero_iff (algebraMap K₀ k).injective).mpr hd, h0⟩
    set L : Fin a → F := fun s =>
      Polynomial.aeval j ((Polynomial.X : Polynomial K₀).map (algebraMap K₀ k))
        + ∑ i : Fin n, Polynomial.aeval j
            ((Polynomial.C (θ s ^ (i.val + 1)) * d).map (algebraMap K₀ k)) * b i with hLdef
    have hLreg : ∀ (s : Fin a) (v : Place k F), j ∈ v.toValuationSubring →
        L s ∈ v.toValuationSubring := fun s v hjv =>
      v.mem_toValuationSubring_of_isIntegral_adjoin hjv
        (mwALGMdev.mwALGM_isIntegral_form hj n b hbsp d hd A hmul
          Polynomial.X (fun i => Polynomial.C (θ s ^ (i.val + 1))))
    refine mwALGCdev.mwALGC_ker n b q₀ v₀ e mdeg Θ a Ms (Rm l) (Y l) D r val r' jv' hMenuD ?_ ?_
    ·
      intro u hu hdvd v hvbad

      rw [not_or, not_or, not_lt, not_lt] at hvbad
      obtain ⟨hvj, hvΘ', hvne⟩ := hvbad
      have hjmemv : j ∈ v.toValuationSubring := v.mem_of_ord_nonneg hjne hvj
      have hvΘ : v.ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) = 0 :=
        le_antisymm hvΘ' (v.ord_nonneg_of_mem (mwALGMdev.mwALGM_aeval_mem v hjmemv _))

      set gU : F := ∑ i : Fin n, Polynomial.aeval j
          (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i
        with hgUdef
      have hgU0 : gU ≠ 0 := by
        rintro hgU0
        apply hu
        funext ⟨i, dd⟩
        show u (i, dd) = 0
        have h := hbli _ hgU0 i
        have hcoeff : (∑ dd : Fin (mdeg + 1),
            Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)).coeff (dd : ℕ) = 0 := by
          rw [h]; exact Polynomial.coeff_zero _
        simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          mul_ite, mul_one, mul_zero, Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ,
          if_true] using hcoeff

      have hE : ∀ s : Fin a,
          (∏ t : Fin r, ((Polynomial.aeval j ((Polynomial.X : Polynomial K₀).map (algebraMap K₀ k))
              + ∑ i : Fin n, Polynomial.aeval j
                  ((Polynomial.C (θ s ^ (i.val + 1)) * d).map (algebraMap K₀ k)) * b i)
            - algebraMap k F (val (t, s.succ)))) * gU
          = ∑ i' : Fin n, Polynomial.aeval j (∑ col : Fin n × Fin (mdeg + 1),
              Polynomial.C (u col) * mwALGCdev.mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2)
              * b i' := by
        intro s
        have hEe := mwALGMdev.mwALGM_Eexpand n b (Polynomial.aeval j (d.map (algebraMap K₀ k))) hdj0
          mdeg r (Polynomial.aeval j ((Polynomial.X : Polynomial K₀).map (algebraMap K₀ k))
            + ∑ i : Fin n, Polynomial.aeval j
                ((Polynomial.C (θ s ^ (i.val + 1)) * d).map (algebraMap K₀ k)) * b i)
          (Ms s) (hpow s) (fun t => val (t, s.succ)) u
        simp only [mwALGCdev.mwALGC_Ek]
        exact hEe
      exact Place.mwALGN_ker_good hj hrat n b d hd hIdb Δ hΔ hG q₀ hq₀ Θ hΘdef v₀ e a θ hθinj g
        (Nat.lt_succ_self _) D hrle pt val βpt pt' jv' hpt hpt' henum hval0 hvalL hjv' hβpt hgU0
        (fun s i' => ∑ col : Fin n × Fin (mdeg + 1),
          Polynomial.C (u col) * mwALGCdev.mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2)
        hE hdvd v hvj hvΘ hvne
    ·
      intro u hu hord
      set gU : F := ∑ i : Fin n, Polynomial.aeval j
          (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i
        with hgUdef
      have hE : ∀ s : Fin a, (∏ t : Fin r, (L s - algebraMap k F (val (t, s.succ)))) * gU
          = ∑ i' : Fin n, Polynomial.aeval j (∑ col : Fin n × Fin (mdeg + 1),
              Polynomial.C (u col) * mwALGCdev.mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2)
              * b i' := by
        intro s
        have hEe := mwALGMdev.mwALGM_Eexpand n b (Polynomial.aeval j (d.map (algebraMap K₀ k)))
          hdj0 mdeg r (L s) (Ms s) (hpow s) (fun t => val (t, s.succ)) u
        simp only [mwALGCdev.mwALGC_Ek]
        exact hEe
      refine mwALGMdev.mwALGM_ker_chow hj n b hbli d hd Δ hΔ q₀ hq₀ Θ hΘdef v₀ e D a pt val pt'
        jv' hpt henum hval0 L hLreg hvalL hjv' gU
        (fun s i' => ∑ col : Fin n × Fin (mdeg + 1),
          Polynomial.C (u col) * mwALGCdev.mwALGC_Ek a n mdeg Ms r val s i' col.1 col.2)
        hE hord ?_

      intro S hS hSΔ N gg E' hE' hx
      exact Place.mwALGN_dvd_of_forall_mem hj b hbli (Δ.map (algebraMap K₀ k))
        (d.map (algebraMap K₀ k))
        ((Polynomial.map_ne_zero_iff (algebraMap K₀ k).injective).mpr hd)
        hG (fun x hxmem => mwALGMdev.mwALGM_isIntegral_adjoin_of_forall_mem hxmem)
        S hS hSΔ E' hE' hx

end

end S_AlgebraicCurve_Divisor_exists_symmValue_rows_kernel_iff
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_exists_symmValue_rows_kernel_iff (solution)
