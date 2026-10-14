-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0126_parallel2
-- name    : PNT_ZeroFree_433_0126_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:31:01.551212+00:00
-- url     : https://prove2.me/theorems/142e23c0-f419-4ebb-bf99-a516a04b7f5d
-- title:
--   Zero-free region foundations: QuadraticSieve.CuspCoercivity [0126_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.CuspCoercivity
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CuspCoercivity.lean#L311-L601

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0065_1
import Definitions.Def_PNT_ZeroFree_433_0082
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0090
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0092
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0109
import Definitions.Def_PNT_ZeroFree_433_0112
import Definitions.Def_PNT_ZeroFree_433_0113
import Definitions.Def_PNT_ZeroFree_433_0114
import Definitions.Def_PNT_ZeroFree_433_0126_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148
import Definitions.Def_PNT_ZeroFree_433_0173_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2
import Definitions.Def_PNT_ZeroFree_433_0265_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CuspCoercivity.lean
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

open scoped BigOperators Classical


open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

namespace CubicEisenstein

section


open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal


def cuspBaseArea : Measure (ℝ×ℝ) := volume.restrict cuspRectangle
instance cuspBaseArea_sFinite : SFinite cuspBaseArea := by unfold cuspBaseArea; infer_instance

def cuspChartVolume (a : ℝ) : Measure CuspChartCoordinates :=
  (cuspBaseArea.prod (volume.restrict (Set.Ioi a))).withDensity
    (fun q => ENNReal.ofReal ((q.2^3)⁻¹))

abbrev CuspChartL2 (a : ℝ) := Lp ℂ 2 (cuspChartVolume a)


theorem cusp_chart_vertical_coercivity (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v) :
    (∫⁻q,ENNReal.ofReal (‖F q‖^2) ∂cuspChartVolume a)≤
      ∫⁻q,ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2) ∂cuspChartVolume a := by
  have hw : Measurable (fun q : CuspChartCoordinates => ENNReal.ofReal ((q.2^3)⁻¹)) := by
    fun_prop
  have hFm : Measurable (fun q : CuspChartCoordinates => ENNReal.ofReal (‖F q‖^2)) := by fun_prop
  have hVm : Measurable (fun q : CuspChartCoordinates => ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2)) := by
    unfold cuspVerticalVelocity
    fun_prop
  unfold cuspChartVolume
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hFm,
    lintegral_withDensity_eq_lintegral_mul _ hw hVm,
    lintegral_prod _ ((hw.mul hFm).aemeasurable),
    lintegral_prod _ ((hw.mul hVm).aemeasurable)]
  apply lintegral_mono
  intro z
  calc
    _ = ∫⁻v in Set.Ioi a,ENNReal.ofReal (‖F (z,v)‖^2/v^3) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact cusp_weight_mass_identity _ _ (ha.trans hv)
    _ ≤ ∫⁻v in Set.Ioi a,ENNReal.ofReal (‖deriv (fun t => F (z,t)) v‖^2/v) := by
      apply cusp_hardy_halfline_lintegral _ a ha (hFa z) (hDiff z)
      exact (hD.comp (continuous_const.prodMk continuous_id)).continuousOn
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact (cusp_weight_velocity_identity _ _ (ha.trans hv)).symm

theorem cusp_chart_normalized_vertical_coercivity (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v) :
    (1/2:ℝ≥0∞)*(∫⁻q,ENNReal.ofReal (‖F q‖^2) ∂cuspChartVolume a)≤
      (1/2:ℝ≥0∞)*(∫⁻q,ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2) ∂cuspChartVolume a) :=
by
  exact mul_le_mul_of_nonneg_left
    (cusp_chart_vertical_coercivity F a ha hF hD hFa hDiff) (by positivity)

theorem cusp_chart_memLp_of_vertical (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v)
    (hEnergy : MemLp (cuspVerticalVelocity F) 2 (cuspChartVolume a)) :
    MemLp F 2 (cuspChartVolume a) := by
  have hV : Continuous (cuspVerticalVelocity F) := by
    unfold cuspVerticalVelocity
    fun_prop
  have hEi := (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hEnergy
  have hEfin := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun q => sq_nonneg ‖cuspVerticalVelocity F q‖))).mp hEi.2
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
  refine ⟨(hF.norm.pow 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun q => sq_nonneg ‖F q‖))).mpr
  exact (cusp_chart_vertical_coercivity F a ha hF hD hFa hDiff).trans_lt hEfin


def cuspDirichletEnergy (F : CuspChartCoordinates → ℂ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻q,∑j : Fin 3,ENNReal.ofReal (‖cuspCoordinateVelocity F q j‖^2) ∂cuspChartVolume a

lemma cusp_vertical_energy_le (F : CuspChartCoordinates → ℂ) (a : ℝ) :
    (∫⁻q,ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2) ∂cuspChartVolume a)≤
      cuspDirichletEnergy F a := by
  apply lintegral_mono
  intro q
  change ENNReal.ofReal (‖cuspCoordinateVelocity F q 2‖^2)≤_
  exact Finset.single_le_sum (fun j hj => (zero_le : (0:ℝ≥0∞)≤ENNReal.ofReal (‖cuspCoordinateVelocity F q j‖^2))) (Finset.mem_univ (2:Fin 3))

theorem cusp_chart_dirichlet_coercivity (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v) :
    (∫⁻q,ENNReal.ofReal (‖F q‖^2) ∂cuspChartVolume a)≤cuspDirichletEnergy F a :=
  (cusp_chart_vertical_coercivity F a ha hF hD hFa hDiff).trans (cusp_vertical_energy_le F a)

theorem cusp_chart_memLp_of_energy (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v)
    (hEnergy : cuspDirichletEnergy F a<(∞ : ℝ≥0∞)) : MemLp F 2 (cuspChartVolume a) := by
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
  refine ⟨(hF.norm.pow 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun q => sq_nonneg ‖F q‖))).mpr
  exact (cusp_chart_dirichlet_coercivity F a ha hF hD hFa hDiff).trans_lt hEnergy

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal


theorem cuspChartVolume_univ (a : ℝ) (ha : 0<a) :
    cuspChartVolume a Set.univ=ENNReal.ofReal (9*Real.sqrt 3/(2*a^2)) := by
  unfold cuspChartVolume
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [lintegral_prod _ (by fun_prop)]
  simp only [cusp_height_volume a ha,lintegral_const]
  rw [cuspBaseArea,Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter,cuspRectangle_volume]
  rw [←ENNReal.ofReal_mul (by positivity : (0:ℝ)≤1/(2*a^2))]
  congr 1
  ring

lemma cuspChartVolume_finite (a : ℝ) (ha : 0<a) : IsFiniteMeasure (cuspChartVolume a) :=
  ⟨by rw [cuspChartVolume_univ a ha]; exact ENNReal.ofReal_lt_top⟩

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal ContDiff


lemma cusp_compact_smooth_memLp (F : CuspChartCoordinates → ℂ)
    (hF : ContDiff ℝ ∞ F) (hC : HasCompactSupport F) (a : ℝ) (ha : 0<a) :
    MemLp F 2 (cuspChartVolume a) ∧
      ∀j : Fin 3,MemLp (fun q => cuspCoordinateVelocity F q j) 2 (cuspChartVolume a) := by
  let : IsFiniteMeasure (cuspChartVolume a) := cuspChartVolume_finite a ha
  refine ⟨hF.continuous.memLp_of_hasCompactSupport hC,fun j => ?_⟩
  obtain ⟨hc,hs⟩ := cuspCoordinateVelocity_continuous_compact F hF hC j
  exact hc.memLp_of_hasCompactSupport hs

theorem cuspChartL2_dense_smooth_energy (a : ℝ) (ha : 0<a) :
    Dense {f : CuspChartL2 a | ∃g : CuspChartCoordinates → ℂ,
      f=ᵐ[cuspChartVolume a] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      ∀j : Fin 3,MemLp (fun q => cuspCoordinateVelocity g q j) 2 (cuspChartVolume a)} := by
  let : IsFiniteMeasure (cuspChartVolume a) := cuspChartVolume_finite a ha
  apply (Lp.dense_hasCompactSupport_contDiff («μ» := cuspChartVolume a)
    (F := ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)).mono
  rintro f ⟨g,hg,hC,hgD⟩
  exact ⟨g,hg,hC,hgD,(cusp_compact_smooth_memLp g hgD hC a ha).2⟩

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex IdealMobiusDivisorSum

theorem commonMaskIdeal_primeSupport (D : Ideal O) :
    IdealMobiusDivisorSum.primeSupport (commonMaskIdeal D) = gcdMaskPrimes D := by
  have hp : ∀ P ∈ (gcdMaskPrimes D).val, Prime P := by
    intro P hP
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P,hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have hf : UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) = (gcdMaskPrimes D).val := by
    simpa [commonMaskIdeal] using UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hp
  rw [IdealMobiusDivisorSum.primeSupport,hf,Finset.val_toFinset]

theorem commonMask_subset_sum_eq_divisors (D : Ideal O) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      f (∏ P ∈ E, P.val)) = ∑ q ∈ idealDivisors (commonMaskIdeal D), f q := by
  rw [sum_subtype_powerset_products,← commonMaskIdeal_primeSupport D]
  exact (squarefree_divisor_sum_eq_support _ (commonMaskIdeal_squarefree D) f).symm


def maskedPairIdealDualKernel (G I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
    ∑ q ∈ idealDivisors G,
      ((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
      ∑' B : NonzeroIdeal, unrestrictedPairCharacter I J B.val*paperRadialFourier W
        ((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ))

theorem originalPairIdealDualKernel_eq_divisors
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (W : ℝ → ℂ) (M : ℝ) :
    originalPairIdealDualKernel D I J W M =
      maskedPairIdealDualKernel (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M := by
  let Q := idealQuotient D I
  let T := idealQuotient D J
  have hQ : Admissible Q := admissible_idealQuotient hI hDI
  have hT : Admissible T := admissible_idealQuotient hJ hDJ
  have hn := primaryProduct_norm Q T hQ hT
  have hnonneg : 0 ≤ (Ideal.absNorm Q:ℝ)*(Ideal.absNorm T:ℝ) := by positivity
  unfold originalPairIdealDualKernel maskedPairIdealDualKernel
  change ((M:ℂ)/(‖eisEmbedding (primaryGenerator Q*primaryGenerator T)‖:ℂ))*_ =
    ((M:ℂ)/(Real.sqrt ((Ideal.absNorm Q:ℝ)*(Ideal.absNorm T:ℝ)):ℂ))*_
  rw [hn]
  congr 1
  rw [← commonMask_subset_sum_eq_divisors D]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Real.sq_sqrt hnonneg,primeSubsetGenerator,unrestrictedPairCharacter,
    idealGenerator_norm_sq,Complex.ofReal_natCast]
  congr 1
  apply tsum_congr
  intro B
  congr 2
  ring

theorem originalPairDualKernel_eq_divisors
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : I ≠ J) (hray : columnRay I=columnRay J)
    (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0<M) :
    originalPairDualKernel D I J W M =
      maskedPairIdealDualKernel (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M := by
  rw [originalPairDualKernel_eq_ideal D I J hI hJ hDI hDJ hIJ hray W M hM]
  exact originalPairIdealDualKernel_eq_divisors D I J hI hJ hDI hDJ W M

end CanonicalQuadraticSieve

end

end OAI

end


