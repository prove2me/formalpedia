-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0130_parallel1
-- name    : PNT_ZeroFree_433_0130_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:44:23.657242+00:00
-- url     : https://prove2.me/theorems/ffc06805-ddce-46c3-b091-79b5d6924adf
-- title:
--   Zero-free region foundations: CubicSieve.ArithmeticBins [0130_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.ArithmeticBins
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ArithmeticBins.lean#L246-L674

import Definitions.Def_PNT_ZeroFree_433_0079_1
import Definitions.Def_PNT_ZeroFree_433_0167
import Definitions.Def_PNT_ZeroFree_433_0327
import Definitions.Def_PNT_ZeroFree_433_0505

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ArithmeticBins.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

namespace SecondPassArithmetic


open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)

def fixedDepthRank (Z K : ℝ) : ℕ := ⌈1000*Real.log K/Real.log Z⌉₊

theorem fixedDepthRank_initial (Z K : ℝ) (hZ : 1 < Z) (hK : 0 < K)
    (hstart : K ≤ Z^3) : fixedDepthRank Z K ≤ 3000 := by
  have hz := Real.log_pos hZ
  have hl := Real.log_le_log hK hstart
  rw [Real.log_pow] at hl
  apply Nat.ceil_le.mpr
  change 1000*Real.log K/Real.log Z ≤ (3000:ℝ)
  apply (div_le_iff₀ hz).mpr
  norm_num at hl
  linarith

theorem fixedDepthRank_step (Z K K' : ℝ) (hZ : 1 < Z) (hK : 0 < K)
    (hK' : 1 ≤ K') (hstep : K' ≤ K/Z^((1:ℝ)/1000)) :
    fixedDepthRank Z K'+1 ≤ fixedDepthRank Z K := by
  have hz0 : 0 < Z := lt_trans zero_lt_one hZ
  have hz := Real.log_pos hZ
  have hk0 : 0 < K' := lt_of_lt_of_le zero_lt_one hK'
  have hl := Real.log_le_log hk0 hstep
  rw [Real.log_div hK.ne' (Real.rpow_pos_of_pos hz0 _).ne',Real.log_rpow hz0] at hl
  have ha : 0 ≤ 1000*Real.log K'/Real.log Z := by
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hK')) hz.le
  have hb : 1000*Real.log K'/Real.log Z+1 ≤ 1000*Real.log K/Real.log Z := by
    apply (le_div_iff₀ hz).mpr
    field_simp
    nlinarith
  have hn := Nat.ceil_mono hb
  rw [Nat.ceil_add_one ha] at hn
  exact hn

theorem fixedDepthRank_path (Z : ℝ) (hZ : 1 < Z) (K : ℕ → ℝ) (n : ℕ)
    (hK : ∀ i,i ≤ n → 1 ≤ K i) (hstart : K 0 ≤ Z^3)
    (hstep : ∀ i,i < n → K (i+1) ≤ K i/Z^((1:ℝ)/1000)) : n+1 ≤ 3001 := by
  have hiter : ∀ i,i ≤ n → fixedDepthRank Z (K i)+i ≤ fixedDepthRank Z (K 0) := by
    intro i
    induction i with
    | zero => simp
    | succ i hi =>
      intro hin
      have hip : i ≤ n := by omega
      have hil : i < n := by omega
      have hprev := hi hip
      have hs := fixedDepthRank_step Z (K i) (K (i+1)) hZ
        (lt_of_lt_of_le zero_lt_one (hK i hip)) (hK (i+1) hin) (hstep i hil)
      omega
  have ht := hiter n le_rfl
  have hb := fixedDepthRank_initial Z (K 0) hZ
    (lt_of_lt_of_le zero_lt_one (hK 0 (Nat.zero_le _))) hstart
  omega


variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]


end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve


def selectedPoissonT (C M X η : ℝ) : ℝ := C*(M*X)^η
def selectedPoissonK (C M X η : ℝ) : ℝ := selectedPoissonT C M X η*X^2/M

theorem selectedPoisson_bounds (C M X η : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hMX : M≤X^2) (hη : 0≤η) :
    4≤selectedPoissonT C M X η ∧ 1≤selectedPoissonK C M X η ∧
      selectedPoissonK C M X η≤C*(M*X)^(η+2) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hprod : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hprod hη
  have hT : 4≤selectedPoissonT C M X η := by
    unfold selectedPoissonT
    nlinarith
  have hfrac : 1≤X^2/M := (le_div_iff₀ hM0).mpr (by simpa using hMX)
  have hK : 1≤selectedPoissonK C M X η := by
    unfold selectedPoissonK
    rw [mul_div_assoc]
    nlinarith
  refine ⟨hT,hK,?_⟩
  have hXprod : X≤M*X := by nlinarith
  have hfracup : X^2/M≤(M*X)^2 :=
    (div_le_self (sq_nonneg X) hM).trans (pow_le_pow_left₀ hX0.le hXprod 2)
  unfold selectedPoissonK selectedPoissonT
  rw [mul_div_assoc,Real.rpow_add (by positivity : 0<M*X),Real.rpow_two]
  calc
    _ ≤ (C*(M*X)^η)*(M*X)^2 := mul_le_mul_of_nonneg_left hfracup (by positivity)
    _ = _ := by ring

theorem selectedPoisson_radial_identity (C B M X q η : ℝ)
    (hM : 0<M) (hX : 0<X) (hq : 0<q) (hB : 0<B) :
    (M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η =
      selectedPoissonT C M X η*q/B := by
  unfold selectedPoissonK
  field_simp

theorem cutoff_middle_identity (M X T α : ℝ) (hM : 0<M) (hX : 0<X) (hT : 0<T) :
    T*Real.sqrt M*(T*X^2/M)^(α-1/2) =
      T^(α+1/2)*X^(2*α-1)*M^(1-α) := by
  rw [Real.div_rpow (by positivity : 0≤T*X^2) hM.le,
    Real.mul_rpow hT.le (sq_nonneg X),←Real.rpow_two,←Real.rpow_mul hX.le]
  have hx : 2*(α-1/2)=2*α-1 := by ring
  have hm : 1-α=1/2-(α-1/2) := by ring
  have ht : α+1/2=1+(α-1/2) := by ring
  have hmPow : M^(1-α)=M^(1/2:ℝ)/M^(α-1/2) := by
    calc
      _ = M^((1/2:ℝ)-(α-1/2)) := by rw [hm]
      _ = _ := Real.rpow_sub hM _ _
  have htPow : T^(α+1/2)=T*T^(α-1/2) := by
    calc
      _ = T^(1+(α-1/2)) := by rw [ht]
      _ = _ := by rw [Real.rpow_add hT,Real.rpow_one]
  rw [hx,hmPow,htPow,Real.sqrt_eq_rpow]
  ring

theorem selectedPoisson_middle_bound (C M X η α : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hη : 0≤η) (hα : α≤2) :
    selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) ≤
      4*C^3*(M*X)^(3*η)*(X^(2*α-1)*M^(1-α)) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 0<M*X := by positivity
  have hP1 : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hP1 hη
  have hT : 1≤selectedPoissonT C M X η := by unfold selectedPoissonT; nlinarith
  have hT0 : 0<selectedPoissonT C M X η := by linarith
  have hK0 : 0<selectedPoissonK C M X η := by unfold selectedPoissonK; positivity
  have htwo : (2:ℝ)^(α-1/2)≤4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have hp3 : ((M*X)^η)^3 = (M*X)^(3*η) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hP.le]
    congr 1
    ring
  have hT3 : (selectedPoissonT C M X η)^(α+1/2)≤C^3*(M*X)^(3*η) := by
    calc
      _ ≤ (selectedPoissonT C M X η)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = C^3*(M*X)^(3*η) := by norm_num only [selectedPoissonT,Real.rpow_ofNat,mul_pow,hp3]
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hK0.le]
  calc
    _ ≤ 4*(selectedPoissonT C M X η*Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2)) := by
      have hh := mul_le_mul_of_nonneg_right htwo
        (show 0≤selectedPoissonT C M X η*Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) by positivity)
      nlinarith [hh]
    _ = 4*((selectedPoissonT C M X η)^(α+1/2)*X^(2*α-1)*M^(1-α)) := by
      rw [selectedPoissonK,cutoff_middle_identity M X _ α hM0 hX0 hT0]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hT3
        (show 0≤X^(2*α-1)*M^(1-α) by positivity)
      nlinarith [hh]

end CanonicalQuadraticSieve

open Filter MeasureTheory EuclideanGeometry
open scoped BigOperators Classical Topology InnerProductSpace ENNReal

namespace CubicEisenstein

abbrev EuclideanSpatial := EuclideanSpace ℝ (Fin 3)

def euclideanUpperHalf : Set EuclideanSpatial := {p | 0<p 2}
def hyperbolicDensity (p : EuclideanSpatial) : ℝ≥0∞ := ENNReal.ofReal ((p 2)^3)⁻¹

def hyperbolicEuclideanVolume : Measure EuclideanSpatial :=
  (volume.restrict euclideanUpperHalf).withDensity hyperbolicDensity

lemma euclideanUpperHalf_measurable : MeasurableSet euclideanUpperHalf := by
  exact measurableSet_lt measurable_const (by fun_prop)

lemma hyperbolicDensity_measurable : Measurable hyperbolicDensity := by
  unfold hyperbolicDensity
  fun_prop

lemma hyperbolic_volume_map_of_jacobian
    (f : EuclideanSpatial → EuclideanSpatial)
    (df : EuclideanSpatial → EuclideanSpatial →L[ℝ] EuclideanSpatial)
    (hf : Measurable f) (hderiv : ∀p∈euclideanUpperHalf,HasFDerivAt f (df p) p)
    (hinj : Set.InjOn f euclideanUpperHalf) (himage : f '' euclideanUpperHalf=euclideanUpperHalf)
    (hjac : ∀p∈euclideanUpperHalf,
      ENNReal.ofReal |(df p).det| *hyperbolicDensity (f p)=hyperbolicDensity p) :
    Measure.map f hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs]
  unfold hyperbolicEuclideanVolume
  rw [withDensity_apply _ (hs.preimage hf),withDensity_apply _ hs]
  rw [←lintegral_indicator (hs.preimage hf),←lintegral_indicator hs]
  have hc := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    euclideanUpperHalf_measurable (fun p hp => (hderiv p hp).hasFDerivWithinAt) hinj
    (s.indicator hyperbolicDensity)
  rw [himage] at hc
  rw [hc]
  apply setLIntegral_congr_fun euclideanUpperHalf_measurable
  intro p hp
  by_cases hsfp : f p∈s
  · simp only [Set.indicator_of_mem hsfp,Set.mem_preimage,hsfp,Set.indicator_of_mem]
    exact (hjac p hp).symm
  · simp only [Set.indicator_of_notMem hsfp,mul_zero]
    have hpnot : p∉f ⁻¹' s := hsfp
    exact Set.indicator_of_notMem hpnot hyperbolicDensity

def euclideanInversion : EuclideanSpatial → EuclideanSpatial := inversion 0 1

def euclideanInversionDeriv (p : EuclideanSpatial) : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  (1/‖p‖)^2 • (((ℝ ∙ p)ᗮ).reflection : EuclideanSpatial →L[ℝ] EuclideanSpatial)

lemma euclideanInversion_apply (p : EuclideanSpatial) (j : Fin 3) :
    euclideanInversion p j=(1/‖p‖)^2*p j := by
  simp [euclideanInversion,inversion,dist_zero_right]

lemma euclideanInversion_measurable : Measurable euclideanInversion := by
  simp +unfoldPartialApp only [euclideanInversion,inversion,dist_zero_right,vsub_eq_sub,sub_zero,vadd_eq_add,add_zero]
  fun_prop

lemma euclideanUpperHalf_ne_zero (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) : p≠0 := by
  intro he
  simp [euclideanUpperHalf,he] at hp

lemma euclideanInversion_mem (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) :
    euclideanInversion p∈euclideanUpperHalf := by
  change 0<euclideanInversion p 2
  rw [euclideanInversion_apply]
  exact mul_pos (sq_pos_of_pos (one_div_pos.mpr (norm_pos_iff.mpr (euclideanUpperHalf_ne_zero p hp)))) hp

lemma euclideanInversion_image : euclideanInversion '' euclideanUpperHalf=euclideanUpperHalf := by
  apply Set.Subset.antisymm
  · rintro p ⟨q,hq,rfl⟩
    exact euclideanInversion_mem q hq
  · intro p hp
    exact ⟨euclideanInversion p,euclideanInversion_mem p hp,
      inversion_inversion 0 (by norm_num) p⟩

lemma euclideanInversion_hasFDerivAt (p : EuclideanSpatial) (hp : p≠0) :
    HasFDerivAt euclideanInversion (euclideanInversionDeriv p) p := by
  simpa [euclideanInversion,euclideanInversionDeriv,dist_zero_right] using
    (hasFDerivAt_inversion (R := (1:ℝ)) hp)

lemma euclideanInversion_abs_det (p : EuclideanSpatial) :
    |(euclideanInversionDeriv p).det|=((1/‖p‖)^2)^3 := by
  unfold euclideanInversionDeriv
  change |LinearMap.det ((1/‖p‖)^2 • ((ℝ ∙ p)ᗮ).reflection.toLinearMap)|=_
  rw [LinearMap.det_smul]
  rw [Submodule.det_reflection]
  simp only [finrank_euclideanSpace,Fintype.card_fin,abs_mul,abs_pow,abs_neg,abs_one,
    one_pow,mul_one]
  rw [abs_of_nonneg (one_div_nonneg.mpr (norm_nonneg p))]

lemma euclideanInversion_jacobian_density (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) :
    ENNReal.ofReal |(euclideanInversionDeriv p).det| *
      hyperbolicDensity (euclideanInversion p)=hyperbolicDensity p := by
  rw [euclideanInversion_abs_det,hyperbolicDensity,hyperbolicDensity,euclideanInversion_apply]
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hn : ‖p‖≠0 := norm_ne_zero_iff.mpr (euclideanUpperHalf_ne_zero p hp)
  field_simp

theorem euclideanInversion_preserves_hyperbolicVolume :
    Measure.map euclideanInversion hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply hyperbolic_volume_map_of_jacobian euclideanInversion euclideanInversionDeriv
    euclideanInversion_measurable
  · exact fun p hp => euclideanInversion_hasFDerivAt p (euclideanUpperHalf_ne_zero p hp)
  · exact (inversion_injective 0 (by norm_num : (1:ℝ)≠0)).injOn
  · exact euclideanInversion_image
  · exact euclideanInversion_jacobian_density

end CubicEisenstein

end

end OAI

end


