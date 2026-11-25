-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:25:21.514252+00:00
-- url     : https://prove2.me/theorems/83e2cd6f-5ffe-5a48-8f47-669d419b69e2
-- title:
--   Mem MCoord Ideal Iff Of Is Weighted Homogeneous
-- statement:
--   Definitions and structural lemmas for Mem MCoord Ideal Iff Of Is Weighted Homogeneous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mem_mcPts_iff_497efdbb0f6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_toGeo_a_e5f916118ff1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralSection_value_mem_chartLat_a828c5da8776
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartSection_supNormLE_aa7598e7119d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_map_flatCone_f6bc8e6a8518
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
theorem mConeMap_monomial {Ω : Type*} [Field Ω] (y : Coord n → Ω) (d : Coord n →₀ ℕ) (c : ℤ) :
    Geo.mConeMap (ι := blockIdx n) y (monomial d c) =
      monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (coordDeg n) d))
        (aeval y (monomial d c)) := by
  rw [Geo.mConeMap, aeval_monomial, aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ d p =
      monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (coordDeg n) d)) 1 := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ d ⟨k, i⟩ = _
    show _ = (X k : MvPolynomial ι Ω) ^ (Finsupp.weight (coordDeg n) d k)
    rw [Finset.prod_pow_eq_pow_sum, weight_coordDeg_apply]
  rw [hX, MvPolynomial.algebraMap_apply, ← mul_assoc, ← map_mul, C_mul_monomial, mul_one]
theorem mConeMap_of_isWeightedHomogeneous {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    Geo.mConeMap (ι := blockIdx n) y g =
      monomial (Finsupp.equivFunOnFinite.symm m) (aeval y g) := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [mConeMap_monomial, hg (mem_support_iff.mp hd)]
theorem mem_mCoordIdeal_iff_of_isWeightedHomogeneous {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    g ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ aeval y g = 0 := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isWeightedHomogeneous y hg, monomial_eq_zero]
def compDegs (f : MvPolynomial (Coord n) ℤ) : Finset (ι → ℕ) :=
  (weightedHomogeneousComponent_finsupp (w := coordDeg n) f).toFinset
omit [Fintype ι] in

theorem sum_compDegs (f : MvPolynomial (Coord n) ℤ) :
    ∑ m ∈ compDegs f, weightedHomogeneousComponent (coordDeg n) m f = f := by
  rw [compDegs, ← finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f),
    sum_weightedHomogeneousComponent]
omit [Fintype ι] [DecidableEq ι] in

theorem aeval_eq_zero_of_mem_mCoordIdeal {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ Geo.mCoordIdeal (ι := blockIdx n) y) :
    aeval y f = 0 := by
  have key : ∀ g : MvPolynomial (Coord n) ℤ,
      eval (fun _ ↦ (1 : Ω)) (Geo.mConeMap (ι := blockIdx n) y g) = aeval y g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p v hp =>
      rw [map_mul, map_mul, hp, map_mul]
      simp [Geo.mConeMap]
  rw [← key, Geo.mCoordIdeal, RingHom.mem_ker] at *
  rw [hf, map_zero]
theorem mem_mCoordIdeal_iff {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    (f : MvPolynomial (Coord n) ℤ) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔
      ∀ m, aeval y (weightedHomogeneousComponent (coordDeg n) m f) = 0 := by
  classical
  constructor
  · intro hf m₀
    by_cases h0 : weightedHomogeneousComponent (coordDeg n) m₀ f = 0
    · rw [h0, map_zero]
    have hm₀ : m₀ ∈ compDegs f := (Set.Finite.mem_toFinset _).mpr h0
    have hk := congrArg (coeff (Finsupp.equivFunOnFinite.symm m₀))
      (show Geo.mConeMap (ι := blockIdx n) y f = 0 from hf)
    rw [← sum_compDegs f, map_sum, coeff_sum, coeff_zero,
      Finset.sum_eq_single m₀] at hk
    · rwa [mConeMap_of_isWeightedHomogeneous y
        (weightedHomogeneousComponent_isWeightedHomogeneous m₀ f), coeff_monomial, if_pos rfl] at hk
    · intro m _ hm
      rw [mConeMap_of_isWeightedHomogeneous y
        (weightedHomogeneousComponent_isWeightedHomogeneous m f), coeff_monomial, if_neg]
      exact fun h ↦ hm (Finsupp.equivFunOnFinite.symm.injective h)
    · exact fun h ↦ absurd hm₀ h
  · intro h
    rw [← sum_compDegs f]
    refine Ideal.sum_mem _ fun m _ ↦ ?_
    exact (mem_mCoordIdeal_iff_of_isWeightedHomogeneous y
      (weightedHomogeneousComponent_isWeightedHomogeneous m f)).mpr (h m)
def ArithVariety.genericPt (P : ArithVariety n) : Coord n → P.FunField :=
  fun v ↦ P.mkF (X v)
omit [Fintype ι] [DecidableEq ι] in

theorem aeval_eq_eval₂_int {Ω : Type*} [Field Ω] (y : Coord n → Ω) (f : MvPolynomial (Coord n) ℤ) :
    aeval y f = eval₂ (Int.castRingHom Ω) y f := by
  rw [aeval_def, algebraMap_int_eq]
omit [Fintype ι] in

theorem ArithVariety.eval₂_genericPt (P : ArithVariety n) (f : MvPolynomial (Coord n) ℤ) :
    eval₂ (Int.castRingHom P.FunField) P.genericPt f = P.mkF f := by
  have : eval₂Hom (Int.castRingHom P.FunField) P.genericPt = P.mkF :=
    MvPolynomial.ringHom_ext
      (fun a ↦ DFunLike.congr_fun
        (RingHom.ext_int ((eval₂Hom (Int.castRingHom P.FunField) P.genericPt).comp C)
          (P.mkF.comp C)) a)
      (fun p ↦ eval₂_X _ _ _)
  exact DFunLike.congr_fun this f
omit [Fintype ι] in

theorem ArithVariety.eval₂_genericPt_eq_zero_iff (P : ArithVariety n)
    (f : MvPolynomial (Coord n) ℤ) :
    eval₂ (Int.castRingHom P.FunField) P.genericPt f = 0 ↔ f ∈ P.ideal := by
  rw [P.eval₂_genericPt, P.mkF_eq_zero_iff]
theorem ArithVariety.mCoordIdeal_genericPt (P : ArithVariety n) :
    Geo.mCoordIdeal (ι := blockIdx n) P.genericPt = P.ideal := by
  ext f
  rw [mem_mCoordIdeal_iff]
  constructor
  · intro h
    rw [← sum_compDegs f]
    exact Ideal.sum_mem _ fun m _ ↦
      (P.eval₂_genericPt_eq_zero_iff _).mp (by rw [← aeval_eq_eval₂_int]; exact h m)
  · intro hf m
    rw [aeval_eq_eval₂_int]
    exact (P.eval₂_genericPt_eq_zero_iff _).mpr (P.homogeneous f hf m)
namespace HermLine
theorem ofGeo_toGeo_metric (A : HermLine n) {z : Cone n ℂ} (hz : BlockNonzero z) :
    (ofGeo A.toGeo A.isSmoothHerm_toGeo).metric z = A.metric z :=
  toGeo_h_of_blockNonzero A (w := flatCone z) hz
end HermLine
section Curves
variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
end Curves
section Sections
variable {Ω : Type*} [Field Ω]
theorem ArithVariety.mem_iff_aeval_eq_zero (P : ArithVariety n) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) {g : MvPolynomial (Coord n) ℤ}
    {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    g ∈ P.ideal ↔ aeval y g = 0 := by
  rw [← hy]
  exact mem_mCoordIdeal_iff_of_isWeightedHomogeneous y hg
omit [Fintype ι] in

theorem ArithVariety.aeval_eq_zero_of_mem (P : ArithVariety n) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) {f : MvPolynomial (Coord n) ℤ}
    (hf : f ∈ P.ideal) : aeval y f = 0 :=
  aeval_eq_zero_of_mem_mCoordIdeal y (by rw [hy]; exact hf)
omit [Fintype ι] in

theorem ArithVariety.X_notMem_of_mem_points (P : ArithVariety n) {F : Type*} [CommRing F]
    {z : Cone n F} (hz : z ∈ P.points F) {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0)
    (k : ι) : (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal :=
  fun h ↦ hc k (by simpa [evalCone] using hz.2 _ h)
def algClosureEmbedding : AlgebraicClosure ℚ →+* ℂ :=
  let _ : Algebra.IsAlgebraic ℤ (AlgebraicClosure ℚ) := ⟨fun r ↦
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic r)⟩
  (IsAlgClosed.lift (R := ℤ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom
namespace IntegralSection
variable {P : ArithVariety n} {a : ι → ℤ}
omit [Fintype ι] [DecidableEq ι] in

def valueAt (s : IntegralSection P a) (y : Coord n → Ω) : Ω :=
  aeval y s.num / aeval y s.den
theorem aeval_den_ne_zero (s : IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) : aeval y s.den ≠ 0 :=
  fun h ↦ s.den_not_mem ((P.mem_iff_aeval_eq_zero hy s.den_isHomogeneous).mpr h)
theorem valueAt_mem_chartLat (s : IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) :
    s.valueAt y ∈ Geo.chartLat (ι := blockIdx n) y a 1 :=
  s.value_mem_chartLat y (fun _ hf ↦ P.aeval_eq_zero_of_mem hy hf) (s.aeval_den_ne_zero hy)
theorem aeval_chartForm (s : IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) {c : (k : ι) → Fin (n k + 1)}
    {d : ι → ℕ} {e : MvPolynomial (Coord n) ℤ} (hce : IsChartForm P a s.num s.den c d e) :
    aeval y e = s.valueAt y * aeval y (chartMonomial c d) := by
  have h := P.aeval_eq_zero_of_mem hy hce.2
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  rw [valueAt, div_mul_eq_mul_div, eq_div_iff (s.aeval_den_ne_zero hy), ← h]
  ring
theorem sub_mem_of_chartForm (s : IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) {dg dh : ι → ℕ}
    {g h : MvPolynomial (Coord n) ℤ} (hg : IsWeightedHomogeneous (coordDeg n) g dg)
    (hh : IsWeightedHomogeneous (coordDeg n) h dh) (hd : ∀ k, (dg k : ℤ) = dh k + a k)
    (hgh : aeval y g = s.valueAt y * aeval y h) {c : (k : ι) → Fin (n k + 1)} {d : ι → ℕ}
    {e : MvPolynomial (Coord n) ℤ} (hce : IsChartForm P a s.num s.den c d e) :
    g * chartMonomial c d - h * e ∈ P.ideal := by
  obtain ⟨δ, he, hδ⟩ := hce.1
  have hdeg : dh + δ = dg + d := by
    funext k
    have h1 := hd k
    have h2 := hδ k
    simp only [Pi.add_apply]
    omega
  have h1 := hg.mul (isWeightedHomogeneous_chartMonomial c d)
  have h2 := hh.mul he
  rw [hdeg] at h2
  have hhom : IsWeightedHomogeneous (coordDeg n) (g * chartMonomial c d - h * e) (dg + d) :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sub_mem _
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1)
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
  rw [P.mem_iff_aeval_eq_zero hy hhom, map_sub, map_mul, map_mul, hgh, s.aeval_chartForm hy hce]
  ring
omit [Fintype ι] in

theorem evalCone_rel {F : Type*} [CommRing F] {z : Cone n F} (hz : z ∈ P.points F)
    {g h m e : MvPolynomial (Coord n) ℤ} (hq : g * m - h * e ∈ P.ideal) :
    evalCone z g * evalCone z m = evalCone z h * evalCone z e := by
  have := hz.2 _ hq
  simp only [evalCone, eval₂_sub, eval₂_mul] at this ⊢
  exact sub_eq_zero.mp this
theorem isSectionBounded_iff_supNormLE (A : HermLine n) (s : IntegralSection P A.deg)
    {y : Coord n → Ω} (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) (C : ℝ) :
    IndefiniteRowSideFullHecke.HeightsSet.IsSectionBounded (ι := blockIdx n) P.ideal y A.toGeo (s.valueAt y)
      (Real.exp C) ↔ s.SupNormLE A C := by
  constructor
  · intro hb z hz c d e hce hc
    obtain ⟨δ, he, hδ⟩ := hce.1
    have hmon : evalCone z (chartMonomial c d) ≠ 0 := by
      rw [evalCone_chartMonomial]
      exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
    have hbd := hb δ d e (chartMonomial c d) (flatCone z) ((geoMultiHomog_iff e δ).mpr he)
      ((geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d))
      (fun k ↦ by rw [HermLine.toGeo_a]; have := hδ k; omega) (s.aeval_chartForm hy hce)
      ((P.mem_mcPts_iff _).mpr hz)
    rw [eval_map_flatCone, eval_map_flatCone,
      HermLine.toGeo_h_of_blockNonzero A (w := flatCone z) hz.1] at hbd
    rw [div_le_iff₀ (mul_pos (norm_pos_iff.mpr hmon) (A.metric_pos z hz.1))]
    calc ‖evalCone z e‖ ≤ Real.exp C * ‖evalCone z (chartMonomial c d)‖ * A.metric z := hbd
      _ = _ := by ring
  · intro hs dg dh g h w hg hh hd hgh hw
    have hz : unflatCone w ∈ P.points ℂ := (P.mem_mcPts_iff w).mp hw
    obtain ⟨c, hc⟩ := exists_chart hz.1
    obtain ⟨d, e, hce⟩ := s.regular c (P.X_notMem_of_mem_points hz hc)
    have hrel := evalCone_rel hz (s.sub_mem_of_chartForm hy ((geoMultiHomog_iff g dg).mp hg)
      ((geoMultiHomog_iff h dh).mp hh) hd hgh hce)
    have hmon : evalCone (unflatCone w) (chartMonomial c d) ≠ 0 := by
      rw [evalCone_chartMonomial]
      exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
    have hsup := hs (unflatCone w) hz c d e hce hc
    rw [show eval w (map (Int.castRingHom ℂ) g) = evalCone (unflatCone w) g from
        eval_map_flatCone (unflatCone w) g,
      show eval w (map (Int.castRingHom ℂ) h) = evalCone (unflatCone w) h from
        eval_map_flatCone (unflatCone w) h,
      HermLine.toGeo_h_of_blockNonzero A hz.1]
    rw [div_le_iff₀ (mul_pos (norm_pos_iff.mpr hmon) (A.metric_pos _ hz.1))] at hsup
    have hkey : ‖evalCone (unflatCone w) g‖ * ‖evalCone (unflatCone w) (chartMonomial c d)‖ ≤
        (Real.exp C * ‖evalCone (unflatCone w) h‖ * A.metric (unflatCone w)) *
          ‖evalCone (unflatCone w) (chartMonomial c d)‖ := by
      rw [← norm_mul, hrel, norm_mul]
      calc ‖evalCone (unflatCone w) h‖ * ‖evalCone (unflatCone w) e‖ ≤
          ‖evalCone (unflatCone w) h‖ * (Real.exp C *
            (‖evalCone (unflatCone w) (chartMonomial c d)‖ * A.metric (unflatCone w))) :=
            mul_le_mul_of_nonneg_left hsup (norm_nonneg _)
        _ = _ := by ring
    exact le_of_mul_le_mul_right hkey (norm_pos_iff.mpr hmon)
end IntegralSection
end Sections
example : Geo.mCoordIdeal (ι := blockIdx (fun _ : Unit ↦ 1)) (ArithVariety.whole _).genericPt = ⊥ :=
  (ArithVariety.whole _).mCoordIdeal_genericPt
example : (HermLine.ofGeo (HermLine.standard (fun _ : Unit ↦ 1)).toGeo
      (HermLine.isSmoothHerm_toGeo _)).deg = (fun _ ↦ 1) ∧
    (HermLine.ofGeo (HermLine.standard (fun _ : Unit ↦ 1)).toGeo
      (HermLine.isSmoothHerm_toGeo _)).metric (fun _ ↦ ![1, 2]) =
    (HermLine.standard (fun _ : Unit ↦ 1)).metric (fun _ ↦ ![1, 2]) := by
  refine ⟨rfl, HermLine.ofGeo_toGeo_metric _ fun _ h ↦ ?_⟩
  have := congrFun h 0
  simp at this
example : (IntegralSection.chartSection (ArithVariety.whole (fun _ : Unit ↦ 1)) (fun _ ↦ 0)).valueAt
      (ArithVariety.whole _).genericPt ∈
      Geo.chartLat (ι := blockIdx (fun _ : Unit ↦ 1)) (ArithVariety.whole _).genericPt
        (fun _ ↦ 1) 1 ∧
    IndefiniteRowSideFullHecke.HeightsSet.IsSectionBounded (ι := blockIdx (fun _ : Unit ↦ 1)) (ArithVariety.whole _).ideal
      (ArithVariety.whole _).genericPt (HermLine.standard _).toGeo
      ((IntegralSection.chartSection (ArithVariety.whole (fun _ : Unit ↦ 1)) (fun _ ↦ 0)).valueAt
        (ArithVariety.whole _).genericPt) (Real.exp 0) :=
  ⟨IntegralSection.valueAt_mem_chartLat _ (ArithVariety.whole _).mCoordIdeal_genericPt,
    (IntegralSection.isSectionBounded_iff_supNormLE _ _
      (ArithVariety.whole _).mCoordIdeal_genericPt 0).mpr (chartSection_supNormLE _ _)⟩
end
end GroundTheory.Heights₂.Heights


