-- Prove2me | Definitions.Def_OAIHecke78B015
-- name    : OAIHecke78B015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T01:25:47.389612+00:00
-- url     : https://prove2.me/theorems/556efb69-ac0c-48f2-b371-9c24cba62cc1
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 16 of 29
-- statement:
--   Definitions bundle 16 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B014` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Eisenstein.TranslatedFourierResidues`, `Eisenstein.PrimePowerGaussSums`, `Eisenstein.BesselDerivatives`, `Eisenstein.SourceBesselExpansion`, `Eisenstein.ReflectedCuspMellin`, `Cusp.ResiduesModThree`, `Descent.RootWindows`, `Detector.GaussianDerivative`, `Detector.GaussianLogWindow`, `Detector.GramJointConstruction`, `Hecke.IdealBridge`, `Hecke.ZeroSupremum`, `Hecke.Reciprocal`, `Hecke.PrimitiveSupremum`, `Inversion.ClippingProfiles`, `Moments.Fourier`, `Moments.FirstReduced`, `Moments.SectorLocalization`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B014

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B015

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Eisenstein.TranslatedFourierResidues
  Eisenstein.PrimePowerGaussSums
  Eisenstein.BesselDerivatives
  Eisenstein.SourceBesselExpansion
  Eisenstein.ReflectedCuspMellin
  Cusp.ResiduesModThree
  Descent.RootWindows
  Detector.GaussianDerivative
  Detector.GaussianLogWindow
  Detector.GramJointConstruction
  Hecke.IdealBridge
  Hecke.ZeroSupremum
  Hecke.Reciprocal
  Hecke.PrimitiveSupremum
  Inversion.ClippingProfiles
  Moments.Fourier
  Moments.FirstReduced
  Moments.SectorLocalization
-/

section

namespace OAI

noncomputable section

namespace CubicEisenstein

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma period_integral_fourier_translation (f:ℂ→ℂ)
    (hp:∀(n:Eis)(z:ℂ),f (z+3*eisEmbedding n)=f z) (h:Eis) (b:ℂ) :
    (∫z in periodDomain,f (z+b)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ShortDraftTrace.breveE (cuspFrequency h*b)*
        ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  let g : ℂ→ℂ := fun z=>f z*ShortDraftTrace.breveE (-cuspFrequency h*z)
  have hg : ∀(n:Eis)(z:ℂ),g (z+3*eisEmbedding n)=g z := by
    intro n z
    dsimp only [g]
    rw [hp,cuspFrequency_negative_period]
  have he (z:ℂ) : f (z+b)*ShortDraftTrace.breveE (-cuspFrequency h*z)=
      ShortDraftTrace.breveE (cuspFrequency h*b)*g (b+z) := by
    dsimp only [g]
    rw [mul_left_comm,←AddChar.map_add_eq_mul]
    congr 1
    · rw [add_comm]
    · congr 1
      ring
  simp_rw [he]
  rw [integral_const_mul,period_integral_translation g hg b]

theorem rational_cusp_fourier_right_T (r:SL(2,ℤ)) (n:ℕ) (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)*
        cuspFourierPhase h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*
        ∫w in cuspPeriodStrip 5 6,
          hyperbolicEisenstein s (rationalComplex r • w)*cuspFourierPhase h w∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex (r*ModularGroup.T^n) • w)*cuspFourierPhase h w
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex r • w)*cuspFourierPhase h w
  have hf : Continuous f := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  have hg : Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  change (∫w in cuspPeriodStrip 5 6,f w∂hyperbolicVolume)=
    ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates f hf.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable f hf),
    cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg),
    ←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  dsimp only
  simp_rw [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper,
    cuspFourierPhase,hyperbolicHorizontal_upperPoint]
  rw [period_integral_fourier_translation
    (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0))
    (fun a z=>hyperbolicEisenstein_rational_periodic r a s hs z v hv0) h (n:ℂ)]
  ring

lemma translatedCuspFourier_residue_scaled_of_initial (h:Eis) (M N:levelTwo) (c:ℂ)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspFourierPhase h w∂hyperbolicVolume)=
      c*∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix N • w)*cuspFourierPhase h w∂hyperbolicVolume) :
    translatedCuspFourier h M cubicEisensteinResidue=
      c*translatedCuspFourier h N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedCuspFamily h M 2 3 (by norm_num) (by norm_num)
  let g : ℂ→ℂ := fun s=>c*translatedCuspFamily h N 2 3 (by norm_num) (by norm_num) s
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal h M 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>analyticAt_const.mul
    (translatedCuspFamily_analyticAt_nonreal h N 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedCuspFamily_initial h M 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      translatedCuspFamily_initial h N 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedCuspFamily_residue_limit h M 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  have hr := ((translatedCuspFamily_residue_limit h N 2 3 (by norm_num) (by norm_num)).const_mul c).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    · simpa using ht)
  dsimp only [f,g] at hv
  dsimp only [Function.comp_def]
  linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*hv

lemma translatedCuspFourier_one (h:Eis) (F:KernelQuotientL2) :
    translatedCuspFourier h 1 F=kernelCuspFourier h F := by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one]

def sourceRayPhaseSum (h:Eis) : ℂ :=
  ∑ b:Fin 3,ShortDraftTrace.breveE (cuspFrequency h*(b.val:ℂ))

end

section
open CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceRayPhase_cube (h:Eis) :
    ShortDraftTrace.breveE (cuspFrequency h)^3=1 := by
  rw [←AddChar.map_nsmul_eq_pow,nsmul_eq_mul]
  have hp:=cuspFrequency_period h (1:Eis)
  simpa only [map_one,mul_one,one_mul,Nat.cast_ofNat,mul_comm] using hp

lemma sourceRayPhaseSum_formula (h:Eis) :
    sourceRayPhaseSum h=1+ShortDraftTrace.breveE (cuspFrequency h)+
      ShortDraftTrace.breveE (cuspFrequency h)^2 := by
  unfold sourceRayPhaseSum
  simp only [Fin.sum_univ_succ,Fin.val_zero,Nat.cast_zero,mul_zero,AddChar.map_zero_eq_one,
    Fin.val_succ,Nat.cast_add,Nat.cast_one,zero_add,mul_one,Fin.sum_univ_zero,add_zero]
  have he : ShortDraftTrace.breveE (cuspFrequency h*(1+1))=
      ShortDraftTrace.breveE (cuspFrequency h)^2 := by
    rw [mul_add,mul_one,AddChar.map_add_eq_mul,pow_two]
  rw [he]
  ring

lemma sourceRayPhaseSum_eq (h:Eis) :
    sourceRayPhaseSum h=if ShortDraftTrace.breveE (cuspFrequency h)=1 then 3 else 0 := by
  rw [sourceRayPhaseSum_formula]
  split_ifs with he
  · rw [he]
    norm_num
  · have hc:=sourceRayPhase_cube h
    have hz : (ShortDraftTrace.breveE (cuspFrequency h)-1)*
        (1+ShortDraftTrace.breveE (cuspFrequency h)+ShortDraftTrace.breveE (cuspFrequency h)^2)=0 := by
      linear_combination hc
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr he)

lemma kernelCuspFourier_residue_horizontal (h:Eis) :
    kernelCuspFourier h cubicEisensteinResidue=
      ShortDraftTrace.breveE (cuspFrequency h)*kernelCuspFourier h cubicEisensteinResidue := by
  have hh:=translatedCuspFourier_residue_scaled_of_initial h 1 1
    (ShortDraftTrace.breveE (cuspFrequency h)) (by
      intro s hs hi
      have he:=rational_cusp_fourier_right_T (1:SL(2,ℤ)) 1 h s (by linarith)
      have hT (w:HyperbolicSpace) : hyperbolicEisenstein s (rationalComplex ModularGroup.T • w)=hyperbolicEisenstein s w := by
        simpa only [pow_one] using hyperbolicEisenstein_T_pow s 1 w
      simpa only [one_mul,pow_one,map_one,one_smul,Nat.cast_one,mul_one,hT] using he)
  simpa only [translatedCuspFourier_one] using hh

lemma kernelCuspFourier_residue_eq_zero_of_not_horizontal (h:Eis)
    (hh:ShortDraftTrace.breveE (cuspFrequency h)≠1) :
    kernelCuspFourier h cubicEisensteinResidue=0 := by
  have he:=kernelCuspFourier_residue_horizontal h
  have hz : (ShortDraftTrace.breveE (cuspFrequency h)-1)*
      kernelCuspFourier h cubicEisensteinResidue=0 := by linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hh)

end

open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma oppositeFrequency_cross_identity (h:Eis) :
    Set.EqOn (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s (3*(9*h)))
      (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s h) {s:ℂ|1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily h oppositeSource 2 3
      (by norm_num) (by norm_num) s*cuspWhittakerHeightFactor s (3*(9*h))) domain := by
    intro s hs
    exact (translatedCuspFamily_analyticAt_nonreal h oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt (3*(9*h)) s hs.1)
  have hg : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (translatedCuspFamily_analyticAt_nonreal (3*(9*h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
      cuspWhittakerHeightFactor s (3*(9*h)))=ᶠ[𝓝 (5+Complex.I:ℂ)]
      (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [translatedCuspFamily_initial h oppositeSource 2 3 (by norm_num) (by norm_num)
      (by norm_num) s hs.1 hs.2,opposite_cusp_fourier_average s (by linarith [hs.1]),
      translatedCuspFamily_opposite_initial (9*h) s hs.1 hs.2]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev

theorem translatedCuspFourier_unramified_residue (h:Eis) :
    translatedCuspFourier h oppositeSource cubicEisensteinResidue=
      unramifiedGaussResidue (9*h)*cuspWhittakerHeightFactor (4/3:ℂ) h := by
  have hh (k:Eis) : Tendsto (fun s:ℂ=>cuspWhittakerHeightFactor s k)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) k)) :=
    (cuspWhittakerHeightFactor_analyticAt k (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hl := ((translatedCuspFamily_residue_limit h oppositeSource 2 3
    (by norm_num) (by norm_num)).mul (hh (3*(9*h)))).comp upperVertical_tendsto_cubic_punctured
  have hr := ((translatedCuspFamily_residue_limit (3*(9*h)) oppositeSource 2 3
    (by norm_num) (by norm_num)).mul (hh h)).comp upperVertical_tendsto_cubic_punctured
  have hev : (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) (3*(9*h)))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=oppositeFrequency_cross_identity h (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      · simpa using ht)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : translatedCuspFourier h oppositeSource cubicEisensteinResidue*
      cuspWhittakerHeightFactor (4/3:ℂ) (3*(9*h))=
      translatedCuspFourier (3*(9*h)) oppositeSource cubicEisensteinResidue*
        cuspWhittakerHeightFactor (4/3:ℂ) h := tendsto_nhds_unique_of_eventuallyEq hl hr hev
  unfold unramifiedGaussResidue
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff (cuspWhittakerHeightFactor_center_ne_zero (3*(9*h)))).mpr heq

def principalArithmeticResidue (h:Eis) : ℂ :=
  if h=0 then constantArithmeticResidue else nonzeroScatteringResidue h

lemma kernelCuspFourier_principal_residue (h:Eis) :
    kernelCuspFourier h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*principalArithmeticResidue h*
        cuspWhittakerHeightFactor (4/3:ℂ) h := by
  by_cases hh:h=0
  · subst h
    rw [kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average,principalArithmeticResidue,if_pos rfl,
      cuspWhittakerHeightFactor_zero (4/3) (by norm_num),cuspConstantAverageResidue]
    ring
  · rw [principalArithmeticResidue,if_neg hh,nonzeroScatteringResidue]
    field_simp [cusp_volume_ne_zero,cuspWhittakerHeightFactor_center_ne_zero h]

def sourceArithmeticResidue (h:Eis) : ℂ :=
  if ShortDraftTrace.breveE (cuspFrequency h)=1 then
    (4:ℂ)⁻¹*(principalArithmeticResidue h+
      3*unramifiedGaussResidue (9*h)/((9*Real.sqrt 3/2:ℝ):ℂ))
  else 0

lemma unramifiedGaussResidue_zero :
    unramifiedGaussResidue 0=((9*Real.sqrt 3/2:ℝ):ℂ)*constantArithmeticResidue := by
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero (0:Eis))
  have ht:=translatedCuspFourier_unramified_residue (0:Eis)
  simp only [mul_zero] at ht
  rw [←ht,translatedCuspFourier_opposite_zero_residue]
  have hp:=kernelCuspFourier_principal_residue (0:Eis)
  rw [kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average] at hp
  simpa [principalArithmeticResidue] using hp

lemma sourceArithmeticResidue_zero : sourceArithmeticResidue 0=constantArithmeticResidue := by
  rw [sourceArithmeticResidue]
  simp only [cuspFrequency,map_zero,zero_div,AddChar.map_zero_eq_one,
    principalArithmeticResidue,mul_zero,unramifiedGaussResidue_zero,ite_true]
  field_simp [cusp_volume_ne_zero]
  ; ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

def horizontalPhaseMultiplier (freq direction : ℂ) : ℂ :=
  (2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))

lemma norm_mul_exp_neg_bound (a r : ℝ) (ha : 0<a) :
    r*Real.exp (-a*r)≤(2/a)*Real.exp (-(a/2)*r) := by
  have hbase := Real.add_one_le_exp ((a/2)*r)
  have hr : r≤(2/a)*Real.exp ((a/2)*r) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    nlinarith
  calc
    _ ≤ ((2/a)*Real.exp ((a/2)*r))*Real.exp (-a*r) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring

local notation "O" => ActualEisensteinCubic.O

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def horizontalWirtingerBar (f : ℂ→ℂ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*(deriv (fun t : ℝ => f (z+(t:ℂ))) 0+
    Complex.I*deriv (fun t : ℝ => f (z+(t:ℂ)*Complex.I)) 0)

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

@[simp] lemma cubicUnitGaussSum_one (h:Eis):cubicUnitGaussSum h 1=1:=by
  let:Subsingleton (Eis⧸Ideal.span {(1:Eis)}):=
    Ideal.Quotient.subsingleton_iff.mpr (by simp)
  let r:CubicUnitResidue (1:Eis):=⟨1,isUnit_one⟩
  rw [cubicUnitGaussSum,tsum_eq_single r (fun b hb=>False.elim (hb (Subsingleton.elim b r)))]
  rw [symbol_one,map_one,one_mul,
    residueAdditive_three_congr h 1 _ 0 one_ne_zero (one_dvd _)]
  simp only [residueAdditive,map_zero,mul_zero,zero_div,AddChar.map_zero_eq_one]

lemma cubicUnitGaussSum_frequency_dvd (h c:Eis) (hc:c≠0) (hch:c∣h):
    cubicUnitGaussSum h c=cubicUnitGaussSum 0 c:=
  cubicUnitGaussSum_frequency_congr h 0 c hc (by simpa only [sub_zero] using hch)

lemma cubicUnitGaussSum_prime_power_zero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (n:ℕ):
    cubicUnitGaussSum 0 (p^(n+1))=
      if 3∣n+1 then (Ideal.absNorm (Ideal.span {p}):ℂ)^n*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)-1) else 0:=by
  have he:=cubicUnitGaussSum_prime_power_lift p hp hprimary n 0
  simp only [mul_zero] at he
  rw [he,primeCubicGauss_of_dvd p hp hprimary (n+1) 0 (dvd_zero _)]
  split_ifs <;>ring

lemma cubicUnitGaussSum_prime_power_too_large (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (a k:ℕ) (hk:a+1<k):
    cubicUnitGaussSum (h*p^a) (p^k)=0:=by
  by_contra hG
  cases k with
  | zero=>omega
  | succ n=>
    have hd:=cubicUnitGaussSum_prime_power_support p hp hprimary n (h*p^a) hG
    have hd':p^(a+1)∣p^a*h:=by
      rw [mul_comm]
      exact (pow_dvd_pow p (by omega:a+1≤n)).trans hd
    rw [pow_succ] at hd'
    exact hph ((mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)).mp hd')

lemma unramifiedPrimeDeletedSeries_pow_mod (p:Eis) (hp:Prime p) (s:ℂ) (h:Eis) (n:ℕ):
    unramifiedPrimeDeletedSeries p s (h*p^n)=
      unramifiedPrimeDeletedSeries p s (h*p^(n%3)):=by
  apply tsum_congr
  intro I
  congr 1
  have he:p^n=p^(n%3)*(p^(n/3))^3:=by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  rw [he,←mul_assoc]
  exact cubicUnitGaussSum_cube_shift _ _ _ I.val.2
    (primaryGenerator_spec I.val.val I.val.2).2
    (primeDeleted_generator_coprime p hp I).symm.pow_right

theorem unramifiedCubicGaussSeries_prime_finite (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedCubicGaussSeries s (h*p^a)=
      ∑k∈Finset.range (a+2),((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^k*
        cubicUnitGaussSum (h*p^a) (p^k)*unramifiedPrimeDeletedSeries p s (h*p^a*p^k):=by
  rw [unramifiedCubicGaussSeries_prime_reindex p hp hprimary s hs]
  apply tsum_eq_sum
  intro k hk
  have hk':a+1<k:=by
    have hh: a+2≤k:=by simpa only [Finset.mem_range,not_lt] using hk
    omega
  rw [cubicUnitGaussSum_prime_power_too_large p hp hprimary h hph a k hk',mul_zero,zero_mul]

lemma unramifiedCubicGaussSeries_prime_zero_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s h=unramifiedPrimeDeletedSeries p s h+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h*
        unramifiedPrimeDeletedSeries p s (h*p):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 0
  simpa only [pow_zero,pow_one,mul_one,cubicUnitGaussSum_one,
    Finset.sum_range_succ,Finset.sum_range_zero,zero_add,one_mul,
    primeCubicGauss_one_eq] using he

lemma unramifiedCubicGaussSeries_prime_one_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p)=unramifiedPrimeDeletedSeries p s (h*p)+
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^2*(Ideal.absNorm (Ideal.span {p}):ℂ)*
        primeCubicGauss p hp hprimary 2 h*unramifiedPrimeDeletedSeries p s h:=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 1
  have hg1:cubicUnitGaussSum (h*p) p=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero (dvd_mul_left p h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p) (p^2)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)*primeCubicGauss p hp hprimary 2 h:=by
    simpa only [pow_one,mul_comm p h] using cubicUnitGaussSum_prime_power_lift p hp hprimary 1 h
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,mul_zero,zero_mul,add_zero,hg2] at he
  have hr:h*p*p^2=h*p^3:=by ring
  rw [hr,unramifiedPrimeDeletedSeries_cube_shift p hp] at he
  exact he.trans (by ring)

lemma unramifiedCubicGaussSeries_prime_three_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p^3)=
      (1+((Ideal.absNorm (Ideal.span {p}):ℂ)^3-(Ideal.absNorm (Ideal.span {p}):ℂ)^2)*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*unramifiedPrimeDeletedSeries p s h+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^4*
        primeCubicGauss p hp hprimary 1 h*unramifiedPrimeDeletedSeries p s (h*p):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 3
  have hg0 (k:ℕ) (hk:k≤3):cubicUnitGaussSum (h*p^3) (p^k)=cubicUnitGaussSum 0 (p^k):=
    cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      ((pow_dvd_pow p hk).trans (dvd_mul_left (p^3) h))
  have hg1:cubicUnitGaussSum (h*p^3) p=0:=by
    have hh:=hg0 1 (by omega)
    simp only [pow_one] at hh
    rw [hh]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p^3) (p^2)=0:=by
    rw [hg0 2 (by omega)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3:cubicUnitGaussSum (h*p^3) (p^3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1):=by
    rw [hg0 3 le_rfl]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 2
  have hg4:cubicUnitGaussSum (h*p^3) (p^4)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*primeCubicGauss p hp hprimary 1 h:=by
    have hh:=cubicUnitGaussSum_prime_power_lift p hp hprimary 3 h
    rw [primeCubicGauss_mod_three p hp hprimary 4] at hh
    simpa only [mul_comm (p^3) h,Nat.reduceMod] using hh
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,hg2,hg3,hg4,mul_zero,zero_mul,add_zero] at he
  have hr6:h*p^3*p^3=h*p^6:=by ring
  have hr7:h*p^3*p^4=h*p^7:=by ring
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp,hr6,hr7,
    unramifiedPrimeDeletedSeries_pow_mod p hp s h 6,
    unramifiedPrimeDeletedSeries_pow_mod p hp s h 7] at he
  norm_num only [Nat.reduceMod,pow_zero,pow_one,mul_one] at he
  exact he.trans (by ring)

theorem unramifiedCubicGaussSeries_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h*
        unramifiedCubicGaussSeries s (h*p):=by
  rw [unramifiedCubicGaussSeries_prime_three_power p hp hprimary s hs h hph,
    unramifiedCubicGaussSeries_prime_zero_power p hp hprimary s hs h hph,
    unramifiedCubicGaussSeries_prime_one_power p hp hprimary s hs h hph]
  have hg:=primeCubicGauss_one_mul_two p hp hprimary h hph
  linear_combination ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
    (Ideal.absNorm (Ideal.span {p}):ℂ)*unramifiedPrimeDeletedSeries p s h*hg

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

structure SubexponentialBesselCoefficients where
  value : ActualEisensteinCubic.O→ℂ
  growth : ∀epsilon : ℝ,0<epsilon → ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
    ‖value h‖≤C*Real.exp (epsilon*‖cuspFrequency h‖)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def term (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : ℂ :=
  if h=0 then 0 else (coeff.value h/cubicBesselNormalizer h)*(p.1:ℂ)^(2/3:ℂ)*
    sourceFourierKernel (4/3) (cuspFrequency h*p.1)*ShortDraftTrace.breveE (cuspFrequency h*p.2)

def amplitude (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else coeff.value h*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma term_bessel (h : ActualEisensteinCubic.O) (hh : h≠0) (v : ℝ) (hv : 0<v) (z : ℂ) :
    coeff.term h (v,z)=coeff.value h*(v:ℂ)*
      schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [term,if_neg hh]
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hn := cubicBesselNormalizer_ne_zero h hh
  have hp : (v:ℂ)^3*(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ) := by
    rw [←Complex.cpow_ofNat (v:ℂ) 3,←Complex.cpow_add _ _ hv0]
    congr 1
    ring
  calc
    _ = (coeff.value h/cubicBesselNormalizer h)*(v:ℂ)^3*
        ((v:ℂ)^(-(4/3:ℂ)-1)*sourceFourierKernel (4/3) (cuspFrequency h*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z) := by rw [←hp];ring
    _ = _ := by
      rw [sourceFourierKernel_cubic_height h hh v hv]
      field_simp

lemma term_eq_amplitude (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (z : ℂ) :
    coeff.term h (v,z)=coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  by_cases hh : h=0
  · simp only [term,amplitude,if_pos hh,zero_mul]
  · rw [coeff.term_bessel h hh v hv z,amplitude,if_neg hh]

lemma term_continuousOn (h : ActualEisensteinCubic.O) :
    ContinuousOn (coeff.term h) {p : ℝ × ℂ | 0<p.1} := by
  unfold term
  by_cases hh : h=0
  · simp only [if_pos hh]
    exact continuousOn_const
  simp only [if_neg hh]
  intro p hp
  change 0<p.1 at hp
  have hpow : ContinuousAt (fun q : ℝ × ℂ => (q.1:ℂ)^(2/3:ℂ)) p :=
    (Complex.continuousAt_ofReal_cpow_const p.1 (2/3:ℂ) (Or.inr hp.ne')).comp continuousAt_fst
  have hsource : ContinuousAt (fun q : ℝ × ℂ => sourceFourierKernel (4/3) (cuspFrequency h*q.1)) p :=
    (sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp (by fun_prop)
  have hphase : Continuous (fun q : ℝ × ℂ => ShortDraftTrace.breveE (cuspFrequency h*q.2)) := by
    change Continuous (fun q : ℝ × ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((cuspFrequency h*q.2)+starRingEnd ℂ (cuspFrequency h*q.2))))
    fun_prop
  exact (((continuousAt_const.mul hpow).mul hsource).mul hphase.continuousAt).continuousWithinAt

lemma slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖coeff.term h p‖≤C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hb : 0<b := ha.trans_le hab
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hCu := cubicBesselUpperAway_pos delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := coeff.growth (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*b*cubicBesselUpperAway delta,by positivity,?_⟩
  intro h p hp
  have hv : 0<p.1 := ha.trans_le hp.1
  by_cases hh : h=0
  · simp only [term,if_pos hh,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*p.1 := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hp.1 ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  rw [show p=(p.1,p.2) from rfl,coeff.term_bessel h hh _ hv,
    norm_mul,norm_mul,norm_mul,breveE_norm,mul_one,Complex.norm_of_nonneg hv.le]
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*b*
        (cubicBesselUpperAway delta*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*p.1)/2)) :=
      mul_le_mul (mul_le_mul (hcoeff h hh) hp.2 hv.le (by positivity))
        (schlafliBesselK_cubic_upper_away delta _ hdelta hx) (norm_nonneg _) (by positivity)
    _ = (C*b*cubicBesselUpperAway delta)*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*p.1)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*p.1)/2=
        -(4*Real.pi*‖cuspFrequency h‖*p.1/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hp.1 (mul_pos Real.pi_pos hr).le]

lemma summable (p : ℝ × ℂ) (hp : 0<p.1) : Summable (fun h : ActualEisensteinCubic.O => coeff.term h p) := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound p.1 p.1 hp le_rfl
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h p ⟨le_rfl,le_rfl⟩)
    ((summable_exp_neg_cuspFrequency_norm (Real.pi*p.1) (mul_pos Real.pi_pos hp)).mul_left C)

def series (p : ℝ × ℂ) : ℂ := ∑'h : ActualEisensteinCubic.O,coeff.term h p

lemma series_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn coeff.series {p : ℝ × ℂ | p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound a b ha hab
  apply continuousOn_tsum (u := fun h : ActualEisensteinCubic.O => C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖))
  · intro h
    exact (coeff.term_continuousOn h).mono (fun p hp => ha.trans_le hp.1)
  · exact (summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · exact hbound

lemma series_continuousOn : ContinuousOn coeff.series {p : ℝ × ℂ | 0<p.1} := by
  intro p hp
  change 0<p.1 at hp
  have hclosed := coeff.series_continuousOn_slab (p.1/2) (2*p.1) (by linarith) (by linarith)
  have hnb : {q : ℝ × ℂ | q.1∈Set.Icc (p.1/2) (2*p.1)}∈𝓝 p :=
    continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by linarith) (by linarith))
  exact (hclosed.continuousAt hnb).continuousWithinAt

lemma series_period (v : ℝ) (z : ℂ) (n : ActualEisensteinCubic.O) :
    coeff.series (v,z+3*ConcreteTraceCRT.eisEmbedding n)=coeff.series (v,z) := by
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · simp only [term,if_pos hh]
  simp only [term,if_neg hh]
  rw [mul_add,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

def function (w : HyperbolicSpace) : ℂ := coeff.series (hyperbolicHeight w,hyperbolicHorizontal w)

lemma function_continuous : Continuous coeff.function := by
  apply continuous_iff_continuousAt.mpr
  intro w
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  have hp : (hyperbolicHeight w,hyperbolicHorizontal w)∈{p : ℝ × ℂ | 0<p.1} := hyperbolicHeight_pos w
  exact (coeff.series_continuousOn.continuousAt (hopen.mem_nhds hp)).comp
    (f := fun u : HyperbolicSpace => (hyperbolicHeight u,hyperbolicHorizontal u))
    (hyperbolicHeight_continuous.prodMk hyperbolicHorizontal_continuous).continuousAt

end SubexponentialBesselCoefficients
end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma series_fourier (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,coeff.series (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v k := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : ActualEisensteinCubic.O→ℂ→ℂ := fun h z => coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z)*
    ShortDraftTrace.breveE (-cuspFrequency k*z)
  have hc (h : ActualEisensteinCubic.O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => coeff.amplitude v h*
      Complex.exp (2*Real.pi*Complex.I*((cuspFrequency h*z)+starRingEnd ℂ (cuspFrequency h*z)))*
      Complex.exp (2*Real.pi*Complex.I*((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound v v hv le_rfl
  have hfbound (h : ActualEisensteinCubic.O) (z : ℂ) : ‖f h z‖≤C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) := by
    change ‖(coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z))*
      ShortDraftTrace.breveE (-cuspFrequency k*z)‖≤_
    rw [←coeff.term_eq_amplitude v hv h z,norm_mul,breveE_norm,mul_one]
    exact hbound h (v,z) ⟨le_rfl,le_rfl⟩
  have hi (h : ActualEisensteinCubic.O) : IntegrableOn (f h) periodDomain volume :=
    (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖))).mono'
      (hc h).aestronglyMeasurable (Eventually.of_forall (hfbound h))
  have hnorm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,‖f h z‖)≤
      volume.real periodDomain*(C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) := by
    have hh := integral_mono_ae (hi h).norm (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)))
      (Eventually.of_forall (hfbound h))
    simpa only [setIntegral_const,smul_eq_mul] using hh
  have hs : Summable (fun h : ActualEisensteinCubic.O => ∫z in periodDomain,‖f h z‖) := by
    apply Summable.of_nonneg_of_le (fun h => integral_nonneg (fun z => norm_nonneg _)) hnorm
    exact ((summable_exp_neg_cuspFrequency_norm (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C).mul_left
      (volume.real periodDomain)
  have hterm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,f h z)=
      if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v h else 0 := by
    change (∫z in periodDomain,coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=_
    simp_rw [mul_assoc]
    rw [integral_const_mul,integral_cusp_character_product]
    split_ifs <;> ring
  calc
    _ = ∫z in periodDomain,∑'h : ActualEisensteinCubic.O,f h z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        change (∑'h : ActualEisensteinCubic.O,coeff.term h (v,z))*ShortDraftTrace.breveE (-cuspFrequency k*z)=_
        rw [←tsum_mul_right]
        apply tsum_congr
        intro h
        rw [coeff.term_eq_amplitude v hv h z])
    _ = ∑'h : ActualEisensteinCubic.O,∫z in periodDomain,f h z := (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = ∑'h : ActualEisensteinCubic.O,if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v h else 0 := tsum_congr hterm
    _ = _ := by simp

lemma series_height_continuous (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => coeff.series (v,z)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  exact (coeff.series_continuousOn.continuousAt (hopen.mem_nhds hv)).comp
    (f := fun z : ℂ => (v,z)) (by fun_prop)

def fullFunction (constant : ℂ) (w : HyperbolicSpace) : ℂ :=
  constant*(hyperbolicHeight w:ℂ)^(2/3:ℂ)+coeff.function w

lemma fullFunction_continuous (constant : ℂ) : Continuous (coeff.fullFunction constant) := by
  have hp : Continuous (fun w : HyperbolicSpace => (hyperbolicHeight w:ℂ)^(2/3:ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (Complex.continuousAt_ofReal_cpow_const (hyperbolicHeight w) (2/3:ℂ)
      (Or.inr (hyperbolicHeight_pos w).ne')).comp (f := hyperbolicHeight) hyperbolicHeight_continuous.continuousAt
  exact (continuous_const.mul hp).add coeff.function_continuous

lemma fullFunction_fourier (constant : ℂ) (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,coeff.fullFunction constant (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(if k=0 then constant*(v:ℂ)^(2/3:ℂ) else coeff.amplitude v k) := by
  have hphase : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-cuspFrequency k*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  have hc0 := periodDomain_integrable_of_continuous
    (fun z => (constant*(v:ℂ)^(2/3:ℂ))*ShortDraftTrace.breveE (-cuspFrequency k*z))
    (continuous_const.mul hphase)
  have hcn := periodDomain_integrable_of_continuous
    (fun z => coeff.series (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))
    ((coeff.series_height_continuous v hv).mul hphase)
  simp_rw [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,add_mul]
  rw [integral_add hc0 hcn,integral_const_mul,integral_cusp_character,coeff.series_fourier v hv k]
  by_cases hk : k=0
  · simp only [if_pos hk,amplitude,mul_zero]
    ring
  · simp only [if_neg hk,mul_zero,zero_add]

lemma fullFunction_period (constant : ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) (n : ActualEisensteinCubic.O) :
    coeff.fullFunction constant (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      coeff.fullFunction constant (upperPoint z v hv) := by
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    coeff.series_period]

lemma fullFunction_height_continuous (constant : ℂ) (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => coeff.fullFunction constant (upperPoint z v hv)) := by
  have hc := coeff.series_height_continuous v hv
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  fun_prop

lemma fullFunction_height_memLp (constant : ℂ) (v : ℝ) (hv : 0<v) :
    MemLp (fun z : ℂ => coeff.fullFunction constant (cuspCoordinateLift (v,z))) 2
      (volume.restrict periodDomain) := by
  simp_rw [cuspCoordinateLift_positive v _ hv]
  have hc := coeff.fullFunction_height_continuous constant v hv
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hn : Continuous (fun z : ℂ => ‖coeff.fullFunction constant (upperPoint z v hv)‖^2) := by
    fun_prop
  apply (hn.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

end SubexponentialBesselCoefficients
end CubicEisenstein

open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def translatedHeightCompact (M:levelTwo) (a b:ℝ) : Set KernelQuotient :=
  kernelSourceAction M '' cuspHeightQuotientCompact a b

lemma translatedHeightCompact_isCompact (M:levelTwo) (a b:ℝ) (ha:0<a) :
    IsCompact (translatedHeightCompact M a b) :=
  (cuspHeightQuotientCompact_isCompact a b ha).image (kernelSourceAction_continuous M)

def translatedHeightFourier (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) : KernelQuotientL2→L[ℂ]ℂ :=
  (kernelCuspHeightFourier a b ha ρ h).comp (kernelSourcePullback M).toContinuousLinearMap

lemma translatedHeightFourier_integral (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h M F=
      ∫w in cuspPeriodStrip a b,F (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  rw [translatedHeightFourier,ContinuousLinearMap.comp_apply,kernelCuspHeightFourier_integral]
  have he:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp (kernelSourcePullback_ae_eq M F)
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspWeightedFourierPhase ρ h w) hw

lemma translatedHeightFourier_restrict (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h M
      (kernelMassRestrictionCLM (translatedHeightCompact M a b)
        (translatedHeightCompact_isCompact M a b ha).measurableSet F)=translatedHeightFourier a b ha ρ h M F := by
  rw [translatedHeightFourier_integral,translatedHeightFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelMassRestriction_coe (translatedHeightCompact M a b)
      (translatedHeightCompact_isCompact M a b ha).measurableSet F)
  have he:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp hsource
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  have hm:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedHeightCompact M a b :=
    ⟨_,cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩,rfl⟩
  exact congrArg (fun z:ℂ=>z*cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem hm _))

def translatedHeightFamily (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) : ℂ :=
  translatedHeightFourier a b ha ρ h M
    (kernelLocalCorrectedSeed (translatedHeightCompact M a b)
      (translatedHeightCompact_isCompact M a b ha) 2 3 (by norm_num) (by norm_num) s)

lemma translatedHeightFamily_analyticAt (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) (hs:s.re≠1) (hi:s.im≠0) :
    AnalyticAt ℂ (translatedHeightFamily a b ha ρ h M) s :=
  (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (translatedHeightFourier a b ha ρ h M) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (translatedHeightCompact_isCompact M a b ha)
        2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma translatedHeightFamily_residue_limit (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) :
    Tendsto (fun s:ℂ=>(s-4/3)*translatedHeightFamily a b ha ρ h M s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (translatedHeightFourier a b ha ρ h M cubicEisensteinResidue)) := by
  have hh:=(translatedHeightFourier a b ha ρ h M).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit _ (translatedHeightCompact_isCompact M a b ha))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,translatedHeightFourier_restrict,
    translatedHeightFamily] using hh

lemma translatedHeightFamily_initial (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) (hs:4<s.re) (hi:0<s.im) :
    translatedHeightFamily a b ha ρ h M s=
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix M • w)*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  have hcorrected:kernelCorrectedSeed 2 3 (by norm_num) (by norm_num) s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s (by linarith) := by
    filter_upwards [kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi] with q hq
    change kernelQuotientSeed 2 3 s q+kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s q=_
    rw [hq]
    ring
  have hlocal:=kernelLocalCorrectedSeed_ae_eq _ (translatedHeightCompact_isCompact M a b ha)
    2 3 (by norm_num) (by norm_num) s
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hlocal
  have hE:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hcorrected
  have hp:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp hsource
  have hpE:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp hE
  rw [translatedHeightFamily,translatedHeightFourier_integral]
  apply integral_congr_ae
  filter_upwards [hp,hpE,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwe hwm
  have hm:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedHeightCompact M a b :=
    ⟨_,cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩,rfl⟩
  dsimp only [Function.comp_def] at hw hwe
  rw [hw,Set.indicator_of_mem hm,hwe,kernelSourceAction_mk,kernelQuotientEisenstein_mk]

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CubicEisenstein

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

def cubicBesselDensityDeriv (x t : ℝ) : ℝ := -(x/(2*t))*cubicBesselDensity x t

def cubicBesselRealDeriv (x : ℝ) : ℝ :=
  (-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)+
    (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t)

def schlafliBesselK_cubic_derivative (x : ℝ) : ℂ := (cubicBesselRealDeriv x:ℂ)

def cubicBesselDerivativeUpper (delta : ℝ) : ℝ :=
  ((1/12:ℝ)*(delta/2)^(-(4:ℝ)/3)+
    (1/2:ℝ)*(delta/2)^(-(1:ℝ)/3)*(4/delta))*
      ((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def primeExpansionTerm (p:Eis) (s:ℂ) (h:Eis) (k:ℕ):ℂ:=
  ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^k*cubicUnitGaussSum h (p^k)*
    unramifiedPrimeDeletedSeries p s (h*p^k)

end

section

open scoped BigOperators Classical Topology
open Filter Set
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem unramifiedGaussResidue_of_initial_relation (h0 h1 h2:Eis) (A B:ℂ→ℂ)
    (hA:AnalyticOnNhd ℂ A {s:ℂ|1<s.re ∧ 0<s.im})
    (hB:AnalyticOnNhd ℂ B {s:ℂ|1<s.re ∧ 0<s.im})
    (hAc:ContinuousAt A (4/3:ℂ)) (hBc:ContinuousAt B (4/3:ℂ))
    (hrel:∀s:ℂ,4<s.re→0<s.im→unramifiedCubicGaussSeries s h0=
      A s*unramifiedCubicGaussSeries s h1+B s*unramifiedCubicGaussSeries s h2):
    unramifiedGaussResidue h0=A (4/3)*unramifiedGaussResidue h1+
      B (4/3)*unramifiedGaussResidue h2:=by
  let T (h:Eis):ℂ→ℂ:=translatedCuspFamily (3*h) oppositeSource 2 3 (by norm_num) (by norm_num)
  let H (h:Eis):ℂ→ℂ:=fun s=>cuspWhittakerHeightFactor s (3*h)
  let D:Set ℂ:={s|1<s.re ∧ 0<s.im}
  let f:ℂ→ℂ:=fun s=>T h0 s*H h1 s*H h2 s
  let g:ℂ→ℂ:=fun s=>A s*T h1 s*H h0 s*H h2 s+B s*T h2 s*H h0 s*H h1 s
  have hT (h:Eis):AnalyticOnNhd ℂ (T h) D:=fun s hs=>
    translatedCuspFamily_analyticAt_nonreal (3*h) oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hH (h:Eis):AnalyticOnNhd ℂ (H h) D:=fun s hs=>
    cuspWhittakerHeightFactor_analyticAt (3*h) s hs.1
  have hf:AnalyticOnNhd ℂ f D:=fun s hs=>((hT h0 s hs).mul (hH h1 s hs)).mul (hH h2 s hs)
  have hg:AnalyticOnNhd ℂ g D:=fun s hs=>
    (((hA s hs).mul (hT h1 s hs)).mul (hH h0 s hs)).mul (hH h2 s hs) |>.add
      ((((hB s hs).mul (hT h2 s hs)).mul (hH h0 s hs)).mul (hH h1 s hs))
  have hconvex:Convex ℝ D:=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hstart:(5+Complex.I:ℂ)∈D:=by norm_num [D]
  have hopen:IsOpen {s:ℂ|4<s.re ∧ 0<s.im}:=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev:f=ᶠ[𝓝 (5+Complex.I:ℂ)]g:=by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g,T,H]
    rw [translatedCuspFamily_opposite_initial h0 s hs.1 hs.2,
      translatedCuspFamily_opposite_initial h1 s hs.1 hs.2,
      translatedCuspFamily_opposite_initial h2 s hs.1 hs.2,hrel s hs.1 hs.2]
    ring
  have heq:=hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hlimH (h:Eis):Tendsto (H h) (𝓝[≠] (4/3:ℂ)) (𝓝 (H h (4/3))):=
    (cuspWhittakerHeightFactor_analyticAt (3*h) (4/3) (by norm_num)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  let R (h:Eis):ℂ:=translatedCuspFourier (3*h) oppositeSource cubicEisensteinResidue
  have hlimT (h:Eis):Tendsto (fun s:ℂ=>(s-4/3)*T h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (R h)):=
    translatedCuspFamily_residue_limit (3*h) oppositeSource 2 3 (by norm_num) (by norm_num)
  have hl:=(((hlimT h0).mul (hlimH h1)).mul (hlimH h2)).comp upperVertical_tendsto_cubic_punctured
  have hr:=((((hAc.tendsto.mono_left nhdsWithin_le_nhds).mul (hlimT h1)).mul (hlimH h0)).mul
    (hlimH h2) |>.add ((((hBc.tendsto.mono_left nhdsWithin_le_nhds).mul (hlimT h2)).mul
      (hlimH h0)).mul (hlimH h1))).comp upperVertical_tendsto_cubic_punctured
  have hcross:R h0*H h1 (4/3)*H h2 (4/3)=
      A (4/3)*R h1*H h0 (4/3)*H h2 (4/3)+B (4/3)*R h2*H h0 (4/3)*H h1 (4/3):=by
    apply tendsto_nhds_unique_of_eventuallyEq hl hr
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have htD:(4/3:ℂ)+(t:ℂ)*Complex.I∈D:=by
      constructor
      · norm_num
      · simpa using ht
    have hc:=heq htD
    dsimp only [Function.comp_def,f,g] at *
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*hc
  change R h0/H h0 (4/3)=A (4/3)*(R h1/H h1 (4/3))+B (4/3)*(R h2/H h2 (4/3))
  have h0ne:H h0 (4/3)≠0:=cuspWhittakerHeightFactor_center_ne_zero (3*h0)
  have h1ne:H h1 (4/3)≠0:=cuspWhittakerHeightFactor_center_ne_zero (3*h1)
  have h2ne:H h2 (4/3)≠0:=cuspWhittakerHeightFactor_center_ne_zero (3*h2)
  field_simp [h0ne,h1ne,h2ne]
  linear_combination hcross

lemma gaussPrimeWeight_analytic (p:Eis) (hp:Prime p) (s:ℂ):
    AnalyticAt ℂ (fun z:ℂ=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-z)) s:=by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Eventually.of_forall fun z=>(differentiableAt_id.neg).const_cpow (Or.inl
    (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))))

lemma gaussPrimeWeight_center (p:Eis) (hp:Prime p):
    (Ideal.absNorm (Ideal.span {p}):ℂ)^3*
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ)))^3=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹:=by
  have hQ:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  rw [←Complex.cpow_nat_mul,←Complex.cpow_natCast _ 3,←Complex.cpow_add _ _ hQ]
  convert (preTransparency := .instances) Complex.cpow_neg_one (Ideal.absNorm (Ideal.span {p}):ℂ) using 1 ;congr 1 ;norm_num

theorem unramifiedGaussResidue_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h):
    unramifiedGaussResidue (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 h*
        unramifiedGaussResidue (h*p):=by
  let A:ℂ→ℂ:=fun s=>1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3
  let B:ℂ→ℂ:=fun s=>-((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h)
  have hA (s:ℂ):AnalyticAt ℂ A s:=analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have hB (s:ℂ):AnalyticAt ℂ B s:=((gaussPrimeWeight_analytic p hp s).mul analyticAt_const).neg
  have he:=unramifiedGaussResidue_of_initial_relation (h*p^3) h (h*p) A B
    (fun s _=>hA s) (fun s _=>hB s) (hA _).continuousAt (hB _).continuousAt
    (fun s hs _=>by
      have hh:=unramifiedCubicGaussSeries_prime_recurrence p hp hprimary s (by linarith) h hph
      simpa only [A,B,neg_mul,sub_eq_add_neg] using hh)
  dsimp only [A,B] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [neg_mul,sub_eq_add_neg] using he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

def inverseCuspPath (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) : ℂ×ℝ :=
  (-d/c-(t:ℂ)*star direction/(c^2*((v^2+t^2*‖direction‖^2:ℝ):ℂ)),
    v/(‖c‖^2*(v^2+t^2*‖direction‖^2)))

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CubicEisenstein

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
local notation "Eis" => ActualEisensteinCubic.O

lemma opposite_height_fourier_average (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
      cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      unramifiedCubicGaussSeries s (9*h)*cuspIntervalWhittakerHeightFactor a b ρ s h := by
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
    cuspWeightedFourierPhase ρ h w
  have hg:Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0:0<v:=ha.trans_le hv.1
  have hvz:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv0.ne'
  have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      ρ v*((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*unramifiedCubicGaussSeries s (9*h) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hv0,hyperbolicEisenstein_opposite_upper,
      cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    have he (z:ℂ) : oppositeEisenstein z v hv0 s*(ρ v*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ρ v*(oppositeEisenstein z v hv0 s*ShortDraftTrace.breveE (-cuspFrequency h*z)) := by ring
    simp_rw [he]
    rw [integral_const_mul,oppositeEisenstein_fourier v hv0 s hs h]
    ring
  have hp:(v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
    rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hvz]
    congr 1
    exact Complex.cpow_natCast _ 3
  dsimp only
  rw [hinner,hp]
  ring

lemma oppositeHeight_cross_identity (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    Set.EqOn (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*cuspWhittakerHeightFactor s h)
      (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) {s:ℂ|1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*
      cuspWhittakerHeightFactor s h) domain := fun s hs=>
    (translatedHeightFamily_analyticAt a b ha ρ h oppositeSource s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hg : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
      cuspIntervalWhittakerHeightFactor a b ρ s h) domain := fun s hs=>
    (translatedCuspFamily_analyticAt_nonreal h oppositeSource 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*cuspWhittakerHeightFactor s h)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [translatedHeightFamily_initial a b ha ρ h oppositeSource s hs.1 hs.2,
      opposite_height_fourier_average a b ha ρ h s (by linarith [hs.1]),
      translatedCuspFamily_initial h oppositeSource 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      opposite_cusp_fourier_average s (by linarith [hs.1])]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev

theorem translatedHeightFourier_opposite_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue=
      unramifiedGaussResidue (9*h)*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  have hfixed := (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hvar := (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h (4/3) (by norm_num)).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hl:=((translatedHeightFamily_residue_limit a b ha ρ h oppositeSource).mul hfixed).comp upperVertical_tendsto_cubic_punctured
  have hr:=((translatedCuspFamily_residue_limit h oppositeSource 2 3 (by norm_num) (by norm_num)).mul hvar).comp
    upperVertical_tendsto_cubic_punctured
  have hev : (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedHeightFamily a b ha ρ h oppositeSource ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h)
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspIntervalWhittakerHeightFactor a b ρ ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=oppositeHeight_cross_identity a b ha ρ h (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      · simpa using ht)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue*cuspWhittakerHeightFactor (4/3:ℂ) h=
      translatedCuspFourier h oppositeSource cubicEisensteinResidue*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h :=
    tendsto_nhds_unique_of_eventuallyEq hl hr hev
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero h)
  rw [heq,translatedCuspFourier_unramified_residue]
  ring

end

open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma rational_height_fourier_right_T (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (r:SL(2,ℤ)) (n:ℕ) (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*
        ∫w in cuspPeriodStrip a b,
          hyperbolicEisenstein s (rationalComplex r • w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex (r*ModularGroup.T^n) • w)*cuspWeightedFourierPhase ρ h w
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex r • w)*cuspWeightedFourierPhase ρ h w
  have hf : Continuous f := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  have hg : Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  change (∫w in cuspPeriodStrip a b,f w∂hyperbolicVolume)=
    ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫w in cuspPeriodStrip a b,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha f hf.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha f hf),
    cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg),←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0:0<v:=ha.trans_le hv.1
  have hslice : (∫z in periodDomain,f (cuspCoordinateLift (v,z)))=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫z in periodDomain,g (cuspCoordinateLift (v,z)) := by
    simp only [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper,
      cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    simpa only [mul_assoc] using period_integral_fourier_translation
      (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0)*ρ v)
      (fun m z=>congrArg (fun q:ℂ=>q*ρ v) (hyperbolicEisenstein_rational_periodic r m s hs z v hv0)) h (n:ℂ)
  dsimp only
  rw [hslice]
  ring

lemma translatedHeightFourier_residue_scaled_of_initial (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (M N:levelTwo) (c:ℂ)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      c*∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix N • w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume) :
    translatedHeightFourier a b ha ρ h M cubicEisensteinResidue=
      c*translatedHeightFourier a b ha ρ h N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedHeightFamily a b ha ρ h M
  let g : ℂ→ℂ := fun s=>c*translatedHeightFamily a b ha ρ h N s
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedHeightFamily_analyticAt a b ha ρ h M s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>analyticAt_const.mul
    (translatedHeightFamily_analyticAt a b ha ρ h N s hs.1.ne' hs.2.ne')
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedHeightFamily_initial a b ha ρ h M s hs.1 hs.2,
      translatedHeightFamily_initial a b ha ρ h N s hs.1 hs.2]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedHeightFamily_residue_limit a b ha ρ h M).comp
    upperVertical_tendsto_cubic_punctured
  have hr := ((translatedHeightFamily_residue_limit a b ha ρ h N).const_mul c).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    · simpa using ht)
  dsimp only [f,g] at hv
  dsimp only [Function.comp_def]
  linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*hv

lemma translatedHeightFourier_one (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h 1 F=kernelCuspHeightFourier a b ha ρ h F := by
  rw [translatedHeightFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one]

lemma translatedHeightFourier_bruhat (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (e:Fin 2) (sector:Fin 3⊕(Fin 3×Fin 3)) :
    translatedHeightFourier a b ha ρ h (rationalLift (rationalBruhatRep (e,sector))) cubicEisensteinResidue=
      match sector with
      | Sum.inl _=>kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue
      | Sum.inr ab=>ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
        translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue := by
  cases sector with
  | inl index =>
    rw [←one_mul (kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue),←translatedHeightFourier_one a b ha ρ h]
    apply translatedHeightFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    simp only [map_one,one_smul,one_mul]
  | inr ab =>
    apply translatedHeightFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    change (∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s (rationalComplex ModularGroup.S •
        (rationalComplex (ModularGroup.T^ab.2.val) • w))*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume
    simpa only [map_mul,mul_smul] using
      rational_height_fourier_right_T a b ha ρ ModularGroup.S ab.2.val h s (by linarith)

theorem kernelSourceProjection_height_fourier (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      (4:ℂ)⁻¹*(kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue+
        sourceRayPhaseSum h*translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue) := by
  rw [kernelSourceProjection_eq_twentyFour,map_smul,map_sum]
  change (24:ℂ)⁻¹*(∑i:RationalBruhatIndex,
    translatedHeightFourier a b ha ρ h (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue)=_
  rw [Fintype.sum_prod_type]
  simp_rw [translatedHeightFourier_bruhat]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  rw [←Finset.sum_mul]
  change (24:ℂ)⁻¹*((2:ℂ)*(3*kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue+
    3*(sourceRayPhaseSum h*translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue)))=_
  ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section
local notation "Eis" => ActualEisensteinCubic.O

lemma cuspIntervalWhittakerHeightFactor_zero_center (a b:ℝ) (_ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) 0=
      (3*(Real.pi:ℂ))*∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ)) := by
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  dsimp only
  simp only [cuspFrequency,map_zero,zero_div,zero_mul,sourceFourierKernel_zero (4/3) (by norm_num)]
  have he : -(4/3:ℂ)-1=-(7/3:ℂ) := by ring
  rw [he]
  ring

lemma kernelCuspHeightFourier_principal_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*principalArithmeticResidue h*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  by_cases hh:h=0
  · subst h
    rw [kernelCuspHeightFourier_zero_residue_seven_thirds,cuspIntervalWhittakerHeightFactor_zero_center a b ha ρ]
    simp only [principalArithmeticResidue,ite_true]
    ring
  · simpa only [principalArithmeticResidue,if_neg hh] using kernelCuspHeightFourier_residue_factor a b ha ρ h hh

lemma principalArithmeticResidue_not_horizontal (h:Eis) (hh:ShortDraftTrace.breveE (cuspFrequency h)≠1) :
    principalArithmeticResidue h=0 := by
  have h0:h≠0 := by intro he;subst h;simp [cuspFrequency] at hh
  rw [principalArithmeticResidue,if_neg h0,nonzeroScatteringResidue,
    kernelCuspFourier_residue_eq_zero_of_not_horizontal h hh,zero_div]

theorem kernelSourceProjection_height_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceArithmeticResidue h*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  rw [kernelSourceProjection_height_fourier,kernelCuspHeightFourier_principal_residue,
    translatedHeightFourier_opposite_residue,sourceRayPhaseSum_eq,sourceArithmeticResidue]
  split_ifs with hh
  · field_simp [cusp_volume_ne_zero]

  · rw [principalArithmeticResidue_not_horizontal h hh]
    ring

def sourceResidualFourierCoefficient (h:Eis) : ℂ := cubicBesselNormalizer h*sourceArithmeticResidue h

def sourceResidualFullModeAmplitude (v:ℝ) (h:Eis) : ℂ :=
  if h=0 then (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)
  else sourceResidualFourierCoefficient h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma sourceResidualFullModeAmplitude_zero_density (v:ℝ) (hv:0<v) :
    sourceResidualFullModeAmplitude v 0/(v:ℂ)^3=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)) := by
  simpa [sourceResidualFullModeAmplitude,cubicResidualFullModeAmplitude] using
    cubicResidualFullModeAmplitude_zero_density v hv

lemma sourceResidualFullModeAmplitude_nonzero_density (v:ℝ) (hv:0<v) (h:Eis) (hh:h≠0) :
    sourceResidualFullModeAmplitude v h/(v:ℂ)^3=sourceResidualFourierCoefficient h*
      (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [sourceResidualFullModeAmplitude,if_neg hh]
  have hv0:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

lemma kernelSourceProjection_height_bessel (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (hh:h≠0) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFourierCoefficient h*
        ∫v in Set.Icc a b,ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [kernelSourceProjection_height_residue,cuspIntervalWhittakerHeightFactor_center_bessel a b ha ρ h hh,
    sourceResidualFourierCoefficient]
  ring

theorem kernelSourceProjection_height_full (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  by_cases hh:h=0
  · subst h
    rw [kernelSourceProjection_height_residue,sourceArithmeticResidue_zero,
      cuspIntervalWhittakerHeightFactor_zero_center a b ha ρ]
    have he : (∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v 0/(v:ℂ)^3))=
        ((3*(Real.pi:ℂ))*constantArithmeticResidue)*∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ)) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [sourceResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)]
      ring
    rw [he]
    ring
  · rw [kernelSourceProjection_height_bessel a b ha ρ h hh]
    have he : (∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3))=
        sourceResidualFourierCoefficient h*∫v in Set.Icc a b,
          ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [sourceResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh]
      ring
    rw [he]
    ring

end

local notation "O" => ActualEisensteinCubic.O

lemma sourceResidualFourierCoefficient_interval_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖sourceResidualFourierCoefficient h‖*
        ‖∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2‖≤C := by
  obtain ⟨C,hC,hbound⟩ := kernelCuspHeightFourier_uniform_bound a b ha
  let area : ℂ := ((9*Real.sqrt 3/2:ℝ):ℂ)
  have harea : 0<‖area‖ := norm_pos_iff.mpr cusp_volume_ne_zero
  refine ⟨C*‖(kernelSourceProjection cubicEisensteinResidue)‖/‖area‖,div_nonneg (mul_nonneg hC (norm_nonneg _)) harea.le,?_⟩
  intro h hh
  have heq := kernelSourceProjection_height_bessel a b ha (BoundedContinuousFunction.const ℝ (1:ℂ)) h hh
  have hhbound := hbound (BoundedContinuousFunction.const ℝ (1:ℂ)) h (kernelSourceProjection cubicEisensteinResidue)
  rw [heq] at hhbound
  simp only [BoundedContinuousFunction.const_apply,one_mul,BoundedContinuousFunction.norm_const_eq,
    norm_one,mul_one,norm_mul,mul_assoc] at hhbound
  apply (le_div_iff₀ harea).mpr
  simpa only [area,mul_assoc,mul_comm,mul_left_comm] using hhbound

lemma sourceResidualFourierCoefficient_subexponential (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖sourceResidualFourierCoefficient h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  let b : ℝ := ε/(9*Real.pi)
  let a : ℝ := b/2
  have hb : 0<b := div_pos hε (by positivity)
  have ha : 0<a := half_pos hb
  have hab : a<b := by dsimp [a]; linarith
  obtain ⟨C,hC,hbound⟩ := sourceResidualFourierCoefficient_interval_bound a b ha
  let D : ℝ := (b-a)*cubicBesselLowerConstant/b^2
  have hD : 0<D := div_pos (mul_pos (sub_pos.mpr hab) cubicBesselLowerConstant_pos) (sq_pos_of_pos hb)
  refine ⟨C/D,div_nonneg hC hD.le,?_⟩
  intro h hh
  have hlow := cubicBesselHeight_average_lower a b ha hab h hh
  have hscale : -9*Real.pi*b*‖cuspFrequency h‖=-(ε*‖cuspFrequency h‖) := by
    dsimp [b]
    field_simp
  rw [hscale] at hlow
  have hmul := (mul_le_mul_of_nonneg_left hlow (norm_nonneg (sourceResidualFourierCoefficient h))).trans
    (hbound h hh)
  have he : 0<Real.exp (-(ε*‖cuspFrequency h‖)) := Real.exp_pos _
  apply (le_div_iff₀ (mul_pos hD he)).mpr at hmul
  calc
    _ ≤ C/(D*Real.exp (-(ε*‖cuspFrequency h‖))) := hmul
    _ = (C/D)*Real.exp (ε*‖cuspFrequency h‖) := by rw [Real.exp_neg]; field_simp

def sourceBesselCoefficients : SubexponentialBesselCoefficients where
  value := sourceResidualFourierCoefficient
  growth := sourceResidualFourierCoefficient_subexponential

def sourceBesselFunction : HyperbolicSpace→ℂ :=
  sourceBesselCoefficients.fullFunction ((3*(Real.pi:ℂ))*constantArithmeticResidue)

lemma sourceBesselFunction_continuous : Continuous sourceBesselFunction :=
  sourceBesselCoefficients.fullFunction_continuous _

lemma sourceBesselFunction_fourier (v:ℝ) (hv:0<v) (h:ActualEisensteinCubic.O) :
    (∫z in periodDomain,sourceBesselFunction (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by
  rw [sourceBesselFunction,sourceBesselCoefficients.fullFunction_fourier]
  by_cases hh:h=0
  · simp [sourceResidualFullModeAmplitude,hh]
  · simp only [if_neg hh,SubexponentialBesselCoefficients.amplitude,sourceResidualFullModeAmplitude]
    rfl

lemma sourceBesselFunction_period (v:ℝ) (hv:0<v) (z:ℂ) (n:ActualEisensteinCubic.O) :
    sourceBesselFunction (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      sourceBesselFunction (upperPoint z v hv) :=
  sourceBesselCoefficients.fullFunction_period _ v hv z n

lemma sourceBesselFunction_height_memLp (v:ℝ) (hv:0<v) :
    MemLp (fun z:ℂ=>sourceBesselFunction (cuspCoordinateLift (v,z))) 2 (volume.restrict periodDomain) :=
  sourceBesselCoefficients.fullFunction_height_memLp _ v hv

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O

lemma sourceResidualFullMode_density_integrable (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => sourceResidualFullModeAmplitude v h/(v:ℂ)^3)
      (Set.Icc a b) volume := by
  by_cases hh : h=0
  · subst h
    have hi : IntegrableOn (fun v : ℝ =>
        (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)))
        (Set.Icc a b) volume := by
      apply ContinuousOn.integrableOn_Icc
      intro v hv
      exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const v
        (-(7/3:ℂ)) (Or.inr (ha.trans_le hv.1).ne'))).continuousWithinAt
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (sourceResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)).symm
  · apply ((cubicBesselHeight_integrable a b ha h hh).const_mul
      (sourceResidualFourierCoefficient h)).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (sourceResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh).symm

lemma projectedResidue_slice_coefficient_ae (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    kernelCuspSliceCoefficient (kernelSourceProjection cubicEisensteinResidue) h =ᵐ[volume.restrict (Set.Icc a b)]
      (fun v => ((9*Real.sqrt 3/2:ℝ):ℂ)*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3)) := by
  apply interval_ae_eq_of_boundedContinuous_height_tests a b _ _
    (kernelCuspSliceCoefficient_integrable a b ha h (kernelSourceProjection cubicEisensteinResidue))
    ((sourceResidualFullMode_density_integrable a b ha h).const_mul _)
  intro ρ
  rw [←kernelCuspHeightFourier_eq_slice_integral a b ha ρ h (kernelSourceProjection cubicEisensteinResidue),
    kernelSourceProjection_height_full a b ha ρ h,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by ring)

lemma projectedResidue_all_slice_coefficients_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      kernelCuspSliceCoefficient (kernelSourceProjection cubicEisensteinResidue) h v =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  exact ae_all_iff.mpr (fun h => projectedResidue_slice_coefficient_ae a b ha h)

lemma projectedResidue_all_fourier_integrals_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain,
        (kernelSourceProjection cubicEisensteinResidue) (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))*
          ShortDraftTrace.breveE (-cuspFrequency h*z)) =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by
  filter_upwards [projectedResidue_all_slice_coefficients_ae a b ha,
    ae_restrict_mem measurableSet_Icc] with v hv hvmem
  intro h
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hvmem.1).ne'
  have he := hv h
  unfold kernelCuspSliceCoefficient at he
  rw [←mul_div_assoc] at he
  exact (div_left_inj' (pow_ne_zero 3 hv0)).mp he

theorem projectedResidue_cell_slices_ae (a b:ℝ) (ha:0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b),
      (fun z:ℂ=>kernelSourceProjection cubicEisensteinResidue
        (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z))))
      =ᵐ[volume.restrict periodDomain] (fun z=>sourceBesselFunction (cuspCoordinateLift (v,z))) := by
  filter_upwards [projectedResidue_all_fourier_integrals_ae a b ha,
    kernelCuspSections_memLp a b ha (kernelSourceProjection cubicEisensteinResidue),
    ae_restrict_mem measurableSet_Icc] with v hfour hL hv
  have hpos:0<v:=ha.trans_le hv.1
  apply periodDomain_L2_ext _ _ hL (sourceBesselFunction_height_memLp v hpos)
  intro h
  rw [hfour h]
  symm
  simpa only [cuspCoordinateLift_positive v _ hpos] using sourceBesselFunction_fourier v hpos h

theorem sourceBesselFunction_represents_projection :
    (fun w=>kernelSourceProjection cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] sourceBesselFunction := by
  apply hyperbolic_eq_ae_of_period_cells _ _
    ((MeasureTheory.Lp.stronglyMeasurable (kernelSourceProjection cubicEisensteinResidue)).measurable.comp
      (measurable_integralOrbitProjection _)) sourceBesselFunction_continuous.measurable
  · intro v hv z n
    exact congrArg (kernelSourceProjection cubicEisensteinResidue) (kernelProjection_upper_period v hv z n)
  · exact sourceBesselFunction_period
  · exact projectedResidue_cell_slices_ae

theorem cubicSourceResidualFunction_eq_bessel : cubicSourceResidualFunction=sourceBesselFunction := by
  have he : cubicSourceResidualFunction=ᵐ[hyperbolicVolume]sourceBesselFunction := by
    filter_upwards [cubicSourceResidualFunction_represents_projection,sourceBesselFunction_represents_projection]
      with w hw hs
    exact hw.symm.trans hs
  exact Measure.eq_of_ae_eq he cubicSourceResidualFunction_continuous sourceBesselFunction_continuous

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CubicEisenstein

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

def reflectedCuspProfile (A : ℂ) (Q : ℝ) (g : ℝ→ℂ) (v : ℝ) : ℂ :=
  A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def directionalTerm (h : ActualEisensteinCubic.O) (v : ℝ) (z direction : ℂ) : ℂ :=
  horizontalPhaseMultiplier (cuspFrequency h) direction*coeff.term h (v,z)

end SubexponentialBesselCoefficients
end

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma term_cusp_bound (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖coeff.term h (v,z)‖≤C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hCu := cubicBesselUpperAway_pos delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := coeff.growth (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*cubicBesselUpperAway delta,mul_nonneg hC (cubicBesselUpperAway_pos delta hdelta).le,?_⟩
  intro h v z hav
  have hv : 0<v := ha.trans_le hav
  by_cases hh : h=0
  · simp only [term,if_pos hh,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*v := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hav ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  rw [coeff.term_bessel h hh v hv z,norm_mul,norm_mul,norm_mul,
    breveE_norm,mul_one,Complex.norm_of_nonneg hv.le]
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*v*
        (cubicBesselUpperAway delta*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hcoeff h hh) hv.le)
        (schlafliBesselK_cubic_upper_away delta _ hdelta hx) (norm_nonneg _) (by positivity)
    _ = (C*cubicBesselUpperAway delta)*v*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*v)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*v)/2=
        -(4*Real.pi*‖cuspFrequency h‖*v/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hav (mul_pos Real.pi_pos hr).le]

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def cubicSourceConjugateFunction (w : HyperbolicSpace) : ℂ := star (cubicSourceResidualFunction w)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped Classical MatrixGroups

namespace EisensteinCuspModThree

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCoordinates (eval coords eval_coords unique_coordinates eval_mul)

abbrev Pair := ZMod 3 × ZMod 3
def add (x y : Pair) : Pair := (x.1+y.1,x.2+y.2)
def neg (x : Pair) : Pair := (-x.1,-x.2)
def sub (x y : Pair) : Pair := add x (neg y)
def mul (x y : Pair) : Pair := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1-x.2*y.2)
def scalar (a : ZMod 3) (x : Pair) : Pair := (a*x.1,a*x.2)
def residue (x : ActualEisensteinCubic.O) : Pair := ((coords x).1,(coords x).2)

lemma residue_eval (a b : ℤ) : residue (eval a b)=((a:ZMod 3),(b:ZMod 3)) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext (congrArg (fun n : ℤ => (n:ZMod 3)) h.1)
    (congrArg (fun n : ℤ => (n:ZMod 3)) h.2)

lemma residue_intCast (a : ℤ) : residue (a:ActualEisensteinCubic.O)=((a:ZMod 3),0) := by
  simpa [eval] using residue_eval a 0

lemma residue_zero : residue (0:ActualEisensteinCubic.O)=(0,0) := by simpa using residue_intCast 0
lemma residue_one : residue (1:ActualEisensteinCubic.O)=(1,0) := by simpa using residue_intCast 1

lemma residue_add (x y : ActualEisensteinCubic.O) : residue (x+y)=add (residue x) (residue y) := by
  have he : x+y=eval ((coords x).1+(coords y).1) ((coords x).2+(coords y).2) := by
    nth_rw 1 [←eval_coords x,←eval_coords y]
    simp only [eval,Int.cast_add]
    ring
  rw [he,residue_eval]
  simp [residue,add]

lemma residue_neg (x : ActualEisensteinCubic.O) : residue (-x)=neg (residue x) := by
  have he : -x=eval (-(coords x).1) (-(coords x).2) := by
    nth_rw 1 [←eval_coords x]
    simp only [eval,Int.cast_neg]
    ring
  rw [he,residue_eval]
  simp [residue,neg]

lemma residue_sub (x y : ActualEisensteinCubic.O) : residue (x-y)=sub (residue x) (residue y) := by
  rw [sub_eq_add_neg,residue_add,residue_neg]
  rfl

lemma residue_mul (x y : ActualEisensteinCubic.O) : residue (x*y)=mul (residue x) (residue y) := by
  calc
    residue (x*y)=residue (eval (coords x).1 (coords x).2*eval (coords y).1 (coords y).2) := by
      rw [eval_coords,eval_coords]
    _ = _ := by rw [eval_mul,residue_eval]; simp [residue,mul]

lemma residue_eq_implies_three_dvd {x y : ActualEisensteinCubic.O} (h : residue x=residue y) : (3:ActualEisensteinCubic.O)∣x-y := by
  have h1 : (3:ℤ)∣(coords x).1-(coords y).1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (coords y).1 (coords x).1 3).mp
      (congrArg Prod.fst h).symm
  have h2 : (3:ℤ)∣(coords x).2-(coords y).2 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (coords y).2 (coords x).2 3).mp
      (congrArg Prod.snd h).symm
  obtain ⟨a,ha⟩ := h1
  obtain ⟨b,hb⟩ := h2
  refine ⟨eval a b,?_⟩
  nth_rw 1 [←eval_coords x,←eval_coords y]
  have he1 : (coords x).1=(coords y).1+3*a := by omega
  have he2 : (coords x).2=(coords y).2+3*b := by omega
  simp only [eval,he1,he2]
  push_cast
  ring

lemma residue_mul_intCast (a : ℤ) (x : ActualEisensteinCubic.O) : residue ((a:ActualEisensteinCubic.O)*x)=scalar (a:ZMod 3) (residue x) := by
  rw [residue_mul,residue_intCast]
  simp [mul,scalar]

def primitive (a c : Pair) : Prop := ¬(a.1+a.2=0 ∧ c.1+c.2=0)
instance primitive_decidable (a c : Pair) : Decidable (primitive a c) := inferInstanceAs
  (Decidable (¬(a.1+a.2=0 ∧ c.1+c.2=0)))

lemma primitive_of_determinant : ∀a b c d : Pair,sub (mul a d) (mul b c)=(1,0) → primitive a c := by
  decide +kernel

lemma first_column_primitive (M : SL(2,ActualEisensteinCubic.O)) : primitive (residue (M 0 0)) (residue (M 1 0)) := by
  have hd : M 0 0*M 1 1-M 0 1*M 1 0=1 := by simpa only [Matrix.det_fin_two] using M.property
  have hh := congrArg residue hd
  rw [residue_sub,residue_mul,residue_mul,residue_one] at hh
  exact primitive_of_determinant _ _ _ _ hh

def omegaPower (k : Fin 3) : Pair := if k=0 then (1,0) else if k=1 then (0,1) else (-1,-1)
def unitPair (u : Fin 2 × Fin 3) : Pair := scalar ((-1:ZMod 3)^u.1.val) (omegaPower u.2)
def cuspPair (j : Fin 3) : Pair := if j=0 then (0,0) else if j=1 then (0,1) else (-1,-1)

def columnTop (g : SL(2,ZMod 3)) (j : Fin 3) (u : Fin 2 × Fin 3) : Pair :=
  mul (add (g 0 0,0) (scalar (g 0 1) (cuspPair j))) (unitPair u)
def columnBottom (g : SL(2,ZMod 3)) (j : Fin 3) (u : Fin 2 × Fin 3) : Pair :=
  mul (add (g 1 0,0) (scalar (g 1 1) (cuspPair j))) (unitPair u)

theorem primitive_column_three_cusps : ∀a c : Pair, primitive a c →
    ∃g : SL(2,ZMod 3), ∃j : Fin 3, ∃u : Fin 2 × Fin 3,
      columnTop g j u=a ∧ columnBottom g j u=c := by
  decide +kernel

end

open scoped Classical MatrixGroups Matrix

local notation "O" => ActualEisensteinCubic.O
local notation "ζ" => ActualEisensteinCubic.omega
open CubicKubota CubicEisenstein

def unitRepresentative (u : Fin 2 × Fin 3) : ActualEisensteinCubic.Oˣ :=
  (-1:ActualEisensteinCubic.Oˣ)^u.1.val*CubicRamified.omega_isUnit.unit^u.2.val

lemma unitRepresentative_value (u : Fin 2 × Fin 3) :
    (unitRepresentative u:ActualEisensteinCubic.O)=(-1:ActualEisensteinCubic.O)^u.1.val*ζ^u.2.val := by
  simp [unitRepresentative]

lemma residue_omega : residue ζ=(0,1) := by
  have he : ActualEisensteinCoordinates.eval 0 1=ζ := by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [←he]
  exact residue_eval 0 1

lemma residue_omega_sq : residue (ζ^2)=(-1,-1) := by
  rw [pow_two,residue_mul,residue_omega]
  norm_num [mul]

lemma unitRepresentative_residue (u : Fin 2 × Fin 3) :
    residue (unitRepresentative u:ActualEisensteinCubic.O)=unitPair u := by
  rw [unitRepresentative_value]
  rcases u with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [unitPair,omegaPower,scalar,residue_one,residue_neg,residue_omega,residue_omega_sq,neg]

def cuspParameter (j : Fin 3) : ActualEisensteinCubic.O := if j=0 then 0 else if j=1 then ζ else ζ^2
def cuspRepresentative (j : Fin 3) : SL(2,ActualEisensteinCubic.O) := lowerCuspMatrix (cuspParameter j)

lemma cuspParameter_residue (j : Fin 3) : residue (cuspParameter j)=cuspPair j := by
  fin_cases j <;> simp [cuspParameter,cuspPair,residue_zero,residue_omega,residue_omega_sq]

def unitDiagonal (u : ActualEisensteinCubic.Oˣ) : SL(2,ActualEisensteinCubic.O) :=
  ⟨!![(u:ActualEisensteinCubic.O),0;0,(↑u⁻¹:ActualEisensteinCubic.O)],by simp [Matrix.det_fin_two]⟩

def columnRepresentative (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) : SL(2,ActualEisensteinCubic.O) :=
  rationalEmbedding r*cuspRepresentative j*unitDiagonal (unitRepresentative u)

lemma columnRepresentative_entry (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) (i : Fin 2) :
    columnRepresentative r j u i 0=
      ((r i 0:ActualEisensteinCubic.O)+(r i 1:ActualEisensteinCubic.O)*cuspParameter j)*(unitRepresentative u:ActualEisensteinCubic.O) := by
  change (((r : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom O) *
    !![1, 0; cuspParameter j, 1]) *
    !![(unitRepresentative u : O), 0; 0, (↑(unitRepresentative u)⁻¹ : O)]) i 0 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma columnRepresentative_top_residue (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) :
    residue (columnRepresentative r j u 0 0)=columnTop (rationalReductionThree r) j u := by
  rw [columnRepresentative_entry,residue_mul,residue_add,residue_intCast,
    residue_mul_intCast,cuspParameter_residue,unitRepresentative_residue]
  rfl

lemma columnRepresentative_bottom_residue (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) :
    residue (columnRepresentative r j u 1 0)=columnBottom (rationalReductionThree r) j u := by
  rw [columnRepresentative_entry,residue_mul,residue_add,residue_intCast,
    residue_mul_intCast,cuspParameter_residue,unitRepresentative_residue]
  rfl

lemma same_column_quotient_lower_zero (M N : SL(2,ActualEisensteinCubic.O))
    (h0 : N 0 0=M 0 0) (h1 : N 1 0=M 1 0) : (N⁻¹*M) 1 0=0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,]
  rw [h0,h1]
  ring

theorem three_cusp_decomposition (M : SL(2,ActualEisensteinCubic.O)) :
    ∃G : levelTwo, ∃j : Fin 3, ∃T : SL(2,ActualEisensteinCubic.O),
      T 1 0=0 ∧ IsUnit (T 0 0) ∧ IsUnit (T 1 1) ∧
        M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T := by
  obtain ⟨g,j,u,ht,hb⟩ := primitive_column_three_cusps _ _ (first_column_primitive M)
  obtain ⟨r,hr⟩ := rationalReductionThree_surjective g
  let B := columnRepresentative r j u
  have hB0 : residue (B 0 0)=residue (M 0 0) := by
    dsimp only [B]
    rw [columnRepresentative_top_residue,hr]
    exact ht
  have hB1 : residue (B 1 0)=residue (M 1 0) := by
    dsimp only [B]
    rw [columnRepresentative_bottom_residue,hr]
    exact hb
  have hxy : IsCoprime (M 0 0) (M 1 0) := by
    refine ⟨M 1 1,-M 0 1,?_⟩
    have hd := M.property
    rw [Matrix.det_fin_two] at hd
    linear_combination hd
  obtain ⟨N,hN0,hN1,hNB⟩ := exists_congruent_cusp_completion B (M 0 0) (M 1 0) hxy
    (residue_eq_implies_three_dvd hB0.symm) (residue_eq_implies_three_dvd hB1.symm)
  let G : levelTwo := ⟨(N*B⁻¹)*rationalEmbedding r,⟨⟨N*B⁻¹,hNB⟩,r,rfl⟩⟩
  let T : SL(2,ActualEisensteinCubic.O) := unitDiagonal (unitRepresentative u)*(N⁻¹*M)
  have hT : T 1 0=0 := by
    have hz := same_column_quotient_lower_zero M N hN0 hN1
    change (∑k : Fin 2,(unitDiagonal (unitRepresentative u)) 1 k*(N⁻¹*M) k 0)=0
    rw [Fin.sum_univ_two]
    change 0*(N⁻¹*M) 0 0+(↑(unitRepresentative u)⁻¹:ActualEisensteinCubic.O)*(N⁻¹*M) 1 0=0
    rw [hz]
    ring
  have hdet : T 0 0*T 1 1=1 := by
    have hd := T.property
    simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using hd
  refine ⟨G,j,T,hT,?_,?_,?_⟩
  · exact IsUnit.of_mul_eq_one _ hdet
  · exact IsUnit.of_mul_eq_one _ (show T 1 1*T 0 0=1 by simpa only [mul_comm] using hdet)
  · dsimp [G,T,B,columnRepresentative]
    group

end EisensteinCuspModThree

namespace CubicEisenstein
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
abbrev PrimaryCoprimeDenominator (a : PrimaryLower) := {d:PrimaryLower//IsCoprime a.val d.val}

def primaryDenominatorFromCoprime (a : PrimaryLower) (x : CoprimeElement a.val) :
    PrimaryCoprimeDenominator a := by
  refine ⟨⟨a.val+3*x.val,?_⟩,?_⟩
  · convert (preTransparency := .instances) dvd_add a.2 (dvd_mul_right (3:Eis) x.val) using 1 ;ring
  · apply (isCoprime_right_congr_of_dvd a.val (a.val+3*x.val) (3*x.val) ⟨1,by ring⟩).mpr
    exact (primary_coprime_three a.val (primaryLower_primary a)).mul_right x.2

lemma primaryDenominatorFromCoprime_bijective (a : PrimaryLower) :
    Function.Bijective (primaryDenominatorFromCoprime a) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have he := congrArg (fun d : PrimaryCoprimeDenominator a => d.val.val) h
    change a.val+3*x.val=a.val+3*y.val at he
    exact mul_left_cancel₀ (by norm_num : (3:Eis)≠0) (add_left_cancel he)
  · intro d
    have hdiv : (3:Eis)∣d.val.val-a.val := by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub d.val.2 a.2
    obtain ⟨x,hx⟩ := hdiv
    have hd : d.val.val=a.val+3*x := by linear_combination hx
    have hcop : IsCoprime a.val x := by
      have hc : IsCoprime a.val (3*x) :=
        (isCoprime_right_congr_of_dvd a.val d.val.val (3*x) ⟨1,by rw [hd];ring⟩).mp d.2
      exact hc.of_isCoprime_of_dvd_right (dvd_mul_left x 3)
    refine ⟨⟨x,hcop⟩,Subtype.ext (Subtype.ext ?_)⟩
    exact hd.symm

def primaryDenominatorEquiv (a : PrimaryLower) : CoprimeElement a.val≃PrimaryCoprimeDenominator a :=
  Equiv.ofBijective _ (primaryDenominatorFromCoprime_bijective a)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical

open scoped Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma levelTwo_entry_integer (g : levelTwo) (i j : Fin 2) :
    (3:Eis)∣((g:SL(2,Eis)) i j-((levelTwoRight g) i j:ℤ)) := by
  have he : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (g:SL(2,Eis)) =
      Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (rationalEmbedding (levelTwoRight g)) := by
    rw [←levelTwo_product g,map_mul]
    have hn : Matrix.SpecialLinearGroup.map (n:=Fin 2)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (levelTwoLeft g:SL(2,Eis))=1 := (levelTwoLeft g).property
    rw [hn,one_mul]
  have h := congrArg (fun A : SL(2,Eis⧸Ideal.span {(3:Eis)})=>A i j) he
  exact Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h)

def integerUpper (b : ℤ) : SL(2,ℤ) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two_of]⟩
def integerLower (c : ℤ) : SL(2,ℤ) := ⟨!![1,0;c,1],by simp [Matrix.det_fin_two_of]⟩

lemma levelTwoComplexCharacter_primary (g : levelTwo)
    (ha : lambda^2∣((g:SL(2,Eis)) 0 0)-1) :
    levelTwoComplexCharacter g =
      eisEmbedding (symbol ((g:SL(2,Eis)) 1 0) ((g:SL(2,Eis)) 0 0)) := by
  let A : SL(2,Eis) := g
  let b : ℤ := levelTwoRight g 0 1
  let c : ℤ := levelTwoRight g 1 0
  have hA : (3:Eis)∣A 0 0-1 := three_dvd_primary_sub_one _ ha
  have hB : (3:Eis)∣A 0 1-(b:Eis) := levelTwo_entry_integer g 0 1
  have hC : (3:Eis)∣A 1 0-(c:Eis) := levelTwo_entry_integer g 1 0
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hD : (3:Eis)∣A 1 1-(1+(b:Eis)*(c:Eis)) := by
    have hh := dvd_add (dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_left hA (A 1 1)))
      (dvd_mul_of_dvd_left hB (A 1 0))) (dvd_mul_of_dvd_right hC (b:Eis))
    convert (preTransparency := .instances) hh using 1 ; linear_combination hdet
  let N : SL(2,Eis) := ⟨!![A 0 0,A 0 1-(b:Eis)*A 0 0;
    A 1 0-(c:Eis)*A 0 0,A 1 1-(c:Eis)*A 0 1-(b:Eis)*(A 1 0-(c:Eis)*A 0 0)],by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet⟩
  have hN : N∈levelThree := by
    apply (mem_levelThree_iff_entries N).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact hA
    · have hh:=dvd_sub hB (dvd_mul_of_dvd_right hA (b:Eis))
      convert (preTransparency := .instances) hh using 1 ; dsimp [N] ; ring
    · have hh:=dvd_sub hC (dvd_mul_of_dvd_right hA (c:Eis))
      convert (preTransparency := .instances) hh using 1 ; dsimp [N] ; ring
    · have hh:=dvd_add (dvd_sub (dvd_sub hD (dvd_mul_of_dvd_right hB (c:Eis)))
        (dvd_mul_of_dvd_right hC (b:Eis))) (dvd_mul_of_dvd_right hA ((b:Eis)*(c:Eis)))
      convert (preTransparency := .instances) hh using 1 ; dsimp [N] ; ring
  let lengthScale : levelTwo := ⟨rationalEmbedding (integerLower c),rational_mem_levelTwo _⟩
  let U : levelTwo := ⟨rationalEmbedding (integerUpper b),rational_mem_levelTwo _⟩
  let n : levelThree := ⟨N,hN⟩
  let n2 : levelTwo := ⟨N,levelThree_le_levelTwo hN⟩
  have he : g=lengthScale*n2*U := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change A i j = (((!![(1 : ℤ), 0; c, 1]).map (Int.castRingHom Eis) *
      (N : Matrix (Fin 2) (Fin 2) Eis)) *
      (!![(1 : ℤ), b; 0, 1]).map (Int.castRingHom Eis)) i j
    fin_cases i <;> fin_cases j <;>
      norm_num [N, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  conv_lhs => rw [he,map_mul,map_mul]
  have hL : levelTwoComplexCharacter lengthScale=1 := levelTwoComplexCharacter_rational _
  have hU : levelTwoComplexCharacter U=1 := levelTwoComplexCharacter_rational _
  rw [hL,hU,one_mul,mul_one]
  change levelTwoComplexCharacter ⟨(n:SL(2,Eis)),levelThree_le_levelTwo n.property⟩=_
  rw [levelTwoComplexCharacter_restrict]
  change eisEmbedding (symbol (A 1 0-(c:Eis)*A 0 0) (A 0 0))=_
  congr 1
  exact symbol_congr (x:=A 1 0-(c:Eis)*A 0 0) (y:=A 1 0) (d:=A 0 0) ⟨-(c:Eis),by ring⟩

end CubicKubota

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

theorem inverseNormWindow_contDiff (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (inverseNormWindow V) := by
  unfold inverseNormWindow
  have hn : ∀ y : ℝ, (Real.exp y : ℂ) ≠ 0 := by
    intro y
    exact_mod_cast Real.exp_ne_zero y
  simpa only [div_eq_mul_inv, Pi.inv_apply, Function.comp_apply, Complex.ofRealCLM_apply] using
    hV.mul ((Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).inv hn)

theorem inverseRootWindow_contDiff (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (inverseRootWindow V) := by
  unfold inverseRootWindow
  have hs : ContDiff ℝ ∞ (fun y : ℝ => Real.sqrt (Real.exp y)) :=
    Real.contDiff_exp.sqrt Real.exp_ne_zero
  have hn : ∀ y : ℝ, (Real.sqrt (Real.exp y) : ℂ) ≠ 0 := by
    intro y
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (Real.exp_pos y))
  simpa only [div_eq_mul_inv, Pi.inv_apply, Function.comp_apply, Complex.ofRealCLM_apply] using
    hV.mul ((Complex.ofRealCLM.contDiff.comp hs).inv hn)

theorem inverseNormWindow_compact (V : ℝ → ℂ) (hV : HasCompactSupport V) :
    HasCompactSupport (inverseNormWindow V) := by
  apply hV.mono
  intro y hy
  exact (div_ne_zero_iff.mp hy).1

theorem inverseRootWindow_compact (V : ℝ → ℂ) (hV : HasCompactSupport V) :
    HasCompactSupport (inverseRootWindow V) := by
  apply hV.mono
  intro y hy
  exact (div_ne_zero_iff.mp hy).1

theorem secondRootWindows_smooth_compact (V : Fin 6 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    ∀ i, ContDiff ℝ ∞ (secondRootWindows V i) ∧ HasCompactSupport (secondRootWindows V i) := by
  intro i
  fin_cases i <;> first
    | exact ⟨hV _, hS _⟩
    | exact ⟨inverseNormWindow_contDiff _ (hV _), inverseNormWindow_compact _ (hS _)⟩
    | exact ⟨inverseRootWindow_contDiff _ (hV _), inverseRootWindow_compact _ (hS _)⟩

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace SevenEighths.ProbePhysical

def gaussianLog (z : ℂ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*Complex.exp (-(Complex.log z)^2/4)

lemma gaussianLog_ofReal (y : ℝ) : gaussianLog (y:ℂ)=gaussianMellinProfile y := rfl

lemma gaussianLog_analytic (z : ℂ) (hz : 0<z.re) : AnalyticAt ℂ gaussianLog z := by
  have hl := analyticAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl hz))
  unfold gaussianLog
  exact analyticAt_const.mul (((hl.pow 2).neg.div_const (c:=4)).cexp)

lemma gaussianLog_scaled_analytic (r : ℝ) (hr : 0< r) (z : ℂ) (hz : 0<z.re) :
    AnalyticAt ℂ (fun w : ℂ=>gaussianLog ((r:ℂ)*w)) z := by
  have h : 0<((r:ℂ)*z).re := by simpa using mul_pos hr hz
  exact (gaussianLog_analytic _ h).comp (analyticAt_const.mul analyticAt_id)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open Filter Set MeasureTheory
namespace SevenEighths.ProbePhysical

lemma gaussianFlow_real_smooth (R : ℝ) : ContDiff ℝ ∞ (fun s : ℝ=>gaussianFlow R (s:ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  have hf : ContDiffAt ℂ ∞ (gaussianFlow R) (s:ℂ) := (gaussianFlow_analytic R _).contDiffAt
  exact (hf.restrict_scalars ℝ).comp s Complex.ofRealCLM.contDiff.contDiffAt

def gaussianLogWindow (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) : SchwartzMap ℝ ℂ :=
  (hV.mul_right (f':=fun s : ℝ=>gaussianFlow R (s:ℂ))).toSchwartzMap
    (V.smooth'.mul (gaussianFlow_real_smooth R))
@[simp] lemma gaussianLogWindow_apply (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (R s : ℝ) : gaussianLogWindow V hV R s=V s*gaussianFlow R (s:ℂ) := rfl

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open Filter Set
open scoped Classical SchwartzMap ContDiff Topology

namespace ProbeGramJointConstruction
open ProbeGramLatticeDecay EisensteinSchwartzPoisson

def q1 (z : Joint) : ℝ := ‖z.fst‖^2
def q2 (z : Joint) : ℝ := ‖z.snd‖^2

lemma q1_smooth : ContDiff ℝ ∞ q1 :=
  (WithLp.fstL 2 ℝ ℂ ℂ).contDiff.norm_sq ℂ
lemma q2_smooth : ContDiff ℝ ∞ q2 :=
  (WithLp.sndL 2 ℝ ℂ ℂ).contDiff.norm_sq ℂ

lemma norm_sq_eq (z : Joint) : ‖z‖^2 = q1 z + q2 z :=
  WithLp.prod_norm_sq_eq_of_L2 z

def log1 (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  CompletedHeight.patchedLog a b ha (q1 z)
def log2 (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  CompletedHeight.patchedLog a b ha (q2 z)
def phase (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  log1 a b ha z - log2 a b ha z
def rootScale (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  Real.exp (-(log1 a b ha z + log2 a b ha z)/2)
def amplitude (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (z : Joint) : ℂ :=
  W (q1 z)*star (W (q2 z))*Complex.exp (-((log1 a b ha z+log2 a b ha z):ℂ))

lemma patchedLog_smooth (a b : ℝ) (ha : 0<a) :
    ContDiff ℝ ∞ (CompletedHeight.patchedLog a b ha) :=
  contDiff_id.add (CompletedHeight.logCorrection_smooth a b ha)
lemma log1_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (log1 a b ha) :=
  (patchedLog_smooth a b ha).comp q1_smooth
lemma log2_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (log2 a b ha) :=
  (patchedLog_smooth a b ha).comp q2_smooth
lemma phase_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (phase a b ha) :=
  (log1_smooth a b ha).sub (log2_smooth a b ha)
lemma rootScale_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (rootScale a b ha) :=
  (((log1_smooth a b ha).add (log2_smooth a b ha)).neg.div_const 2).exp
lemma amplitude_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (a b : ℝ) (ha : 0<a) :
    ContDiff ℝ ∞ (amplitude W a b ha) := by
  unfold amplitude
  have h1 := hW.comp q1_smooth
  have h2 := hW.comp q2_smooth
  have hl := (log1_smooth a b ha).add (log2_smooth a b ha)
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_add, Complex.conjCLE_apply, Complex.star_def] using
    (h1.mul (Complex.conjCLE.contDiff.comp h2)).mul
      ((Complex.ofRealCLM.contDiff.comp hl).neg.cexp)

def rawProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint) : ℂ :=
  (W (q1 z)*(q1 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
    star (W (q2 z)*(q2 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
    paperRadialFourier U (T/(q1 z*q2 z))

def patchedProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (v T : ℝ) (z : Joint) : ℂ :=
  amplitude W a b ha z * FourierBridge.logPhase (v/(2*Real.pi)) (phase a b ha z) *
    paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z)

lemma patchedProfile_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (v T : ℝ) :
    ContDiff ℝ ∞ (patchedProfile W U a b ha v T) := by
  have h1 := amplitude_smooth W hW a b ha
  have h2 := phase_smooth a b ha
  have h3 := rootScale_smooth a b ha
  have h4 := (paperFourierRayCLM U).smooth (⊤ : ℕ∞)
  have hp : ContDiff ℝ ∞ (fun z => FourierBridge.logPhase (v/(2*Real.pi)) (phase a b ha z)) := by
    unfold FourierBridge.logPhase
    exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul h2)).mul contDiff_const).cexp
  exact (h1.mul hp).mul (h4.comp (contDiff_const.mul h3))

lemma rawProfile_zero_left (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint)
    (hz : W (q1 z)=0) : rawProfile W U v T z=0 := by simp [rawProfile,hz]
lemma rawProfile_zero_right (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint)
    (hz : W (q2 z)=0) : rawProfile W U v T z=0 := by simp [rawProfile,hz]
lemma patchedProfile_zero_left (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (v T : ℝ) (z : Joint) (hz : W (q1 z)=0) : patchedProfile W U a b ha v T z=0 := by
  simp [patchedProfile,amplitude,hz]
lemma patchedProfile_zero_right (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (v T : ℝ) (z : Joint) (hz : W (q2 z)=0) : patchedProfile W U a b ha v T z=0 := by
  simp [patchedProfile,amplitude,hz]

def sourceCompact (b : ℝ) : Set Joint := Metric.closedBall 0 (1+2*b)
lemma sourceCompact_isCompact (b : ℝ) : IsCompact (sourceCompact b) :=
  isCompact_closedBall _ _

lemma support_amplitude (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) :
    Function.support (amplitude W a b ha)⊆{z | a≤q1 z ∧ q1 z≤b ∧ a≤q2 z ∧ q2 z≤b} := by
  intro z hz
  have h1 : W (q1 z)≠0 := fun h => hz (by simp [amplitude,h])
  have h2 : W (q2 z)≠0 := fun h => hz (by simp [amplitude,h])
  exact ⟨(hs h1).1,(hs h1).2,(hs h2).1,(hs h2).2⟩

lemma annulus_subset_sourceCompact (a b : ℝ) (ha : 0<a) (hab : a<b) :
    {z : Joint | a≤q1 z ∧ q1 z≤b ∧ a≤q2 z ∧ q2 z≤b}⊆sourceCompact b := by
  intro z hz
  change dist z 0≤1+2*b
  rw [dist_zero_right]
  have hn := norm_sq_eq z
  have hb : 0<b := ha.trans hab
  nlinarith [norm_nonneg z, sq_nonneg (‖z‖-1),hz.2.1,hz.2.2.2]

lemma amplitude_hasCompactSupport (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) : HasCompactSupport (amplitude W a b ha) :=
  HasCompactSupport.of_support_subset_isCompact (sourceCompact_isCompact b)
    ((support_amplitude W a b ha hs).trans (annulus_subset_sourceCompact a b ha hab))

lemma norm_power_pair (v x y : ℝ) (hx : 0<x) (hy : 0<y) :
    (x:ℂ)^(-1+(v:ℂ)*Complex.I)*star ((y:ℂ)^(-1+(v:ℂ)*Complex.I)) =
      Complex.exp (-((Real.log x+Real.log y):ℂ))*
        FourierBridge.logPhase (v/(2*Real.pi)) (Real.log x-Real.log y) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
  rw [←Complex.ofReal_log hx.le,←Complex.ofReal_log hy.le]
  simp only [Complex.star_def,←Complex.exp_conj,map_mul,map_add,map_neg,map_one,
    Complex.conj_ofReal,Complex.conj_I]
  unfold FourierBridge.logPhase
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

lemma sqrt_reciprocal_product (T x y : ℝ) (hT : 0≤T) (hx : 0<x) (hy : 0<y) :
    Real.sqrt (T/(x*y))=Real.sqrt T*Real.exp (-(Real.log x+Real.log y)/2) := by
  have he : Real.exp (-(Real.log x+Real.log y)/2)^2=(x*y)⁻¹ := by
    rw [←Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(-(Real.log x+Real.log y)/2)=-(Real.log x+Real.log y) by ring,
      Real.exp_neg,Real.exp_add,Real.exp_log hx,Real.exp_log hy]
  have hl := Real.sq_sqrt (div_nonneg hT (mul_pos hx hy).le)
  have hr : (Real.sqrt T*Real.exp (-(Real.log x+Real.log y)/2))^2=T/(x*y) := by
    rw [mul_pow,Real.sq_sqrt hT,he,div_eq_mul_inv]
  nlinarith [Real.sqrt_nonneg (T/(x*y)),Real.sqrt_nonneg T,
    Real.exp_pos (-(Real.log x+Real.log y)/2),mul_nonneg (Real.sqrt_nonneg T)
      (Real.exp_pos (-(Real.log x+Real.log y)/2)).le]

theorem rawProfile_eq_patchedProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Icc a b)
    (v T : ℝ) (hT : 0≤T) (z : Joint) :
    rawProfile W U v T z=patchedProfile W U a b ha v T z := by
  by_cases h1 : W (q1 z)=0
  · rw [rawProfile_zero_left W U v T z h1,patchedProfile_zero_left W U a b ha v T z h1]
  by_cases h2 : W (q2 z)=0
  · rw [rawProfile_zero_right W U v T z h2,patchedProfile_zero_right W U a b ha v T z h2]
  have hx := ha.trans_le (hs h1).1
  have hy := ha.trans_le (hs h2).1
  have hl1 : log1 a b ha z=Real.log (q1 z) := CompletedHeight.patchedLog_eq_log a b ha _ (hs h1)
  have hl2 : log2 a b ha z=Real.log (q2 z) := CompletedHeight.patchedLog_eq_log a b ha _ (hs h2)
  have hker : paperRadialFourier U (T/(q1 z*q2 z)) =
      paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) := by
    rw [paperRadialFourier_eq_ray]
    change paperFourierRayCLM U (Real.sqrt (T/(q1 z*q2 z))) = _
    rw [sqrt_reciprocal_product T _ _ hT hx hy]
    simp only [rootScale,hl1,hl2]
  unfold rawProfile patchedProfile amplitude phase
  rw [hker,hl1,hl2]
  simp only [star_mul]
  calc
    _ = (W (q1 z)*star (W (q2 z)))*
        ((q1 z:ℂ)^(-1+(v:ℂ)*Complex.I)*star ((q2 z:ℂ)^(-1+(v:ℂ)*Complex.I)))*
        paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) := by ring
    _ = _ := by rw [norm_power_pair v _ _ hx hy];ring

def amplitudeSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(Joint,ℂ) :=
  (amplitude_hasCompactSupport W a b ha hab hs).toSchwartzMap (amplitude_smooth W hW a b ha)

@[simp] lemma amplitudeSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (z : Joint) :
    amplitudeSchwartz W a b ha hab hs hW z=amplitude W a b ha z := rfl

lemma rawProfile_smooth (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) : ContDiff ℝ ∞ (rawProfile W U v T) := by
  have he : rawProfile W U v T=patchedProfile W U a b ha v T :=
    funext (rawProfile_eq_patchedProfile W U a b ha hs v T hT)
  rw [he]
  exact patchedProfile_smooth W hW U a b ha v T

lemma support_rawProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    Function.support (rawProfile W U v T)⊆{z | a≤q1 z ∧ q1 z≤b ∧ a≤q2 z ∧ q2 z≤b} := by
  intro z hz
  have h1 : W (q1 z)≠0 := fun h => hz (rawProfile_zero_left W U v T z h)
  have h2 : W (q2 z)≠0 := fun h => hz (rawProfile_zero_right W U v T z h)
  exact ⟨(hs h1).1,(hs h1).2,(hs h2).1,(hs h2).2⟩

lemma rawProfile_hasCompactSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    HasCompactSupport (rawProfile W U v T) :=
  HasCompactSupport.of_support_subset_isCompact (sourceCompact_isCompact b)
    ((support_rawProfile W U a b hs v T).trans (annulus_subset_sourceCompact a b ha hab))

def jointProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) : 𝓢(Joint,ℂ) :=
  (rawProfile_hasCompactSupport W U a b ha hab hs v T).toSchwartzMap
    (rawProfile_smooth W U a b ha hs hW v T hT)

@[simp] theorem jointProfile_apply (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) :
    jointProfile W U a b ha hab hs hW v T hT z=rawProfile W U v T z := rfl

end ProbeGramJointConstruction

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeFamily

instance instIsPrincipalIdealRingO_solutions_p1 : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def idealCoeff (χ : Character) : Ideal O →*₀ ℂ :=
  IdealCharacter.ofResidue χ.modulus χ.residue χ.unit_trivial

@[simp] theorem idealCoeff_zero (χ : Character) : idealCoeff χ 0 = 0 := map_zero _

theorem idealCoeff_span (χ : Character) {z : O} (hz : z ≠ 0) :
    idealCoeff χ (Ideal.span {z}) = elementCoeff χ z :=
  IdealCharacter.ofResidue_span χ.modulus χ.residue χ.unit_trivial hz

theorem coordinateElement_eq_baseline (a b : ℤ) :
    coordinateElement a b = ActualEisensteinCoordinates.eval a b := rfl

def coordinateEquiv : (ℤ × ℤ) ≃ O :=
  Equiv.ofBijective (fun n => coordinateElement n.1 n.2)
    ⟨fun _ _ h => Prod.ext
      (ActualEisensteinCoordinates.unique_coordinates h).1
      (ActualEisensteinCoordinates.unique_coordinates h).2,
      HeckeCoordinates.coordinateElement_surjective⟩

theorem normForm_eq_absNorm_span (n : ℤ × ℤ) :
    EisensteinTheta.normForm n.1 n.2 =
      (Ideal.absNorm (Ideal.span {coordinateElement n.1 n.2}) : ℝ) := by
  rw [coordinateElement_eq_baseline,
    ← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    ActualEisensteinCubic.eisEmbedding_eval_norm_sq]
  simp only [EisensteinTheta.normForm, Int.cast_add, Int.cast_sub, Int.cast_mul, pow_two]

def elementTerm (χ : Character) (s : ℂ) (z : O) : ℂ :=
  elementCoeff χ z / (Ideal.absNorm (Ideal.span {z}) : ℂ) ^ s

def idealTerm (χ : Character) (s : ℂ) (I : Ideal O) : ℂ :=
  idealCoeff χ I / (Ideal.absNorm I : ℂ) ^ s

theorem elementTerm_coordinate (χ : Character) (s : ℂ) (n : ℤ × ℤ) :
    elementTerm χ s (coordinateEquiv n) =
      elementCoeff χ (coordinateElement n.1 n.2) /
        (EisensteinTheta.normForm n.1 n.2 : ℂ) ^ s := by
  change elementCoeff χ (coordinateElement n.1 n.2) /
    (Ideal.absNorm (Ideal.span {coordinateElement n.1 n.2}) : ℂ) ^ s = _
  rw [normForm_eq_absNorm_span]
  rw [Complex.ofReal_natCast]

theorem elementTerm_hasSum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    HasSum (elementTerm χ s) (continuedLattice χ s) := by
  apply coordinateEquiv.hasSum_iff.mp
  change HasSum (fun n => elementTerm χ s (coordinateEquiv n)) _
  simpa only [elementTerm_coordinate] using continuedLattice_hasSum χ hs

theorem elementTerm_zero (χ : Character) {s : ℂ} (hs : s ≠ 0) :
    elementTerm χ s 0 = 0 := by
  simp [elementTerm, Complex.zero_cpow hs]

theorem elementTerm_unit_mul (χ : Character) (s : ℂ) (u : Oˣ) (z : O) :
    elementTerm χ s ((u : O) * z) = elementTerm χ s z := by
  unfold elementTerm
  rw [elementCoeff_unit_mul, Ideal.span_singleton_mul_left_unit u.isUnit]

theorem elementTerm_idealGenerator (χ : Character) (s : ℂ)
    (I : UnrestrictedIdealReindex.NonzeroIdeal) :
    elementTerm χ s (ConcretePrimeRowBridge.idealGenerator I.val) = idealTerm χ s I.val := by
  unfold elementTerm idealTerm
  rw [ConcretePrimeRowBridge.span_idealGenerator]
  congr 1
  exact (IdealCharacter.ofResidue_of_generator χ.modulus χ.residue χ.unit_trivial
    I.property (ConcretePrimeRowBridge.span_idealGenerator I.val)).symm

theorem continuedLattice_eq_six_ideal_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    continuedLattice χ s = 6 * ∑' I : Ideal O, idealTerm χ s I := by
  have hs₀ : s ≠ 0 := by intro h; norm_num [h] at hs
  have h := UnrestrictedIdealReindex.tsum_unit_invariant_of_zero (elementTerm χ s)
    (elementTerm_hasSum χ hs).summable (elementTerm_zero χ hs₀)
    (elementTerm_unit_mul χ s)
  rw [(elementTerm_hasSum χ hs).tsum_eq] at h
  simp_rw [elementTerm_idealGenerator] at h
  have hsum : (∑' I : UnrestrictedIdealReindex.NonzeroIdeal, idealTerm χ s I.val) =
      ∑' I : Ideal O, idealTerm χ s I := by
    apply tsum_subtype_eq_of_support_subset
    intro I hI hzero
    exact hI (by rw [hzero]; unfold idealTerm; rw [map_zero]; exact zero_div _)
  rwa [hsum] at h

theorem LFunction_eq_ideal_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = ∑' I : Ideal O, idealTerm χ s I := by
  rw [LFunction, continuedLattice_eq_six_ideal_tsum χ hs]
  ring

theorem LFunction_entire_nonprincipal (χ : Character) (hχ : χ.residue ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  (HeckeCharacterAnalytic.continuedLattice_entire_nonprincipal χ hχ).div_const 6

end SevenEighths.HeckeFamily

end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeZeroSupremum
open HeckeFamily

def zeroRealParts : Set ℝ :=
  {x | ∃ (χ : Character) (s : ℂ), 0 < s.re ∧
    (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0 ∧ s.re = x}

def zeroSetWithSentinel : Set ℝ := insert (1 / 2) zeroRealParts

def beta : ℝ := sSup zeroSetWithSentinel

end SevenEighths.HeckeZeroSupremum

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeReciprocal
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem coefficients_sum_ne_zero_of_principal (χ : Character) (hχ : χ.residue = 1) :
    (∑ a, coefficients χ a) ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  let e := Equiv.prodCongr (finCastEquiv χ.period) (finCastEquiv χ.period)
  have heq : (∑ a, coefficients χ a) =
      (Nat.card (coordinateQuotientHom χ).ker : ℂ) *
        (Fintype.card (O ⧸ χ.modulus)ˣ : ℂ) := by
    calc
      _ = ∑ a, χ.residue (coordinateQuotientHom χ (e a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact coefficients_eq_quotient_character χ a
      _ = ∑ a : ZMod χ.period × ZMod χ.period,
          χ.residue (coordinateQuotientHom χ a) :=
        e.bijective.sum_comp (fun a => χ.residue (coordinateQuotientHom χ a))
      _ = _ := by
        rw [sum_comp_additiveHom _ (coordinateQuotientHom_surjective χ), hχ,
          MulChar.sum_one_eq_card_units]
  rw [heq]
  apply mul_ne_zero
  · exact_mod_cast (Nat.card_pos (α := (coordinateQuotientHom χ).ker)).ne'
  · exact_mod_cast (Fintype.card_pos (α := (O ⧸ χ.modulus)ˣ)).ne'

theorem dualScalar_ne_zero (N : ℕ) [NeZero N] : HeckeTheta.dualScalar N ≠ 0 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  unfold HeckeTheta.dualScalar
  apply mul_ne_zero <;> apply Complex.ofReal_ne_zero.mpr
  · exact (Real.rpow_pos_of_pos (sq_pos_of_pos hN) _).ne'
  · exact (Real.rpow_pos_of_pos (mul_pos (by norm_num) (sq_pos_of_pos hN)) _).ne'

theorem principal_dual_constant_ne_zero (χ : Character) (hχ : χ.residue = 1) :
    (HeckeTheta.pair (coefficients χ)).g₀ ≠ 0 := by
  rw [HeckeTheta.pair_g₀]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (dualScalar_ne_zero χ.period))
    (coefficients_sum_ne_zero_of_principal χ hχ)

def regularizedL (χ : Character) (s : ℂ) : ℂ :=
  HeckeTheta.regularizedLatticeL (coefficients χ) s / 6

theorem regularizedL_at_one (χ : Character) :
    regularizedL χ 1 = (Real.pi : ℂ) * (HeckeTheta.pair (coefficients χ)).g₀ / 6 := by
  simp [regularizedL, HeckeTheta.regularizedLatticeL, HeckeTheta.regularizedCompleted]

theorem regularizedL_ne_zero_at_one (χ : Character) (hχ : χ.residue = 1) :
    regularizedL χ 1 ≠ 0 := by
  rw [regularizedL_at_one]
  exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (principal_dual_constant_ne_zero χ hχ)) (by norm_num)

def reciprocal (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then (s - 1) / regularizedL χ s else (LFunction χ s)⁻¹

end SevenEighths.HeckeReciprocal

end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckePrimitiveSupremum
open HeckeFamily HeckeZeroSupremum

def primitiveZeroRealParts : Set ℝ :=
  {x | ∃ (χ : Character) (s : ℂ), FiniteFourier.IsPrimitiveOnIdeals χ.residue ∧
    (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧
    LFunction χ s = 0 ∧ s.re = x}

def primitiveSetWithSentinel : Set ℝ := insert (1 / 2) primitiveZeroRealParts

end SevenEighths.HeckePrimitiveSupremum

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
namespace SevenEighths.InverseClippingProfiles

def logWindow (v : ℝ → ℂ) (L ρ : ℝ) (y : ℝ) : ℂ := v ((y + ρ) / L)

def rootedWindow (v : ℝ → ℂ) (L ρ a H : ℝ) (y : ℝ) : ℂ :=
  (Real.exp (a * y - H * L) : ℂ) * logWindow v L ρ y

lemma logWindow_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (L ρ : ℝ) :
    ContDiff ℝ ∞ (logWindow v L ρ) := by
  exact hv.comp ((contDiff_id.add contDiff_const).div_const L)

lemma rootedWindow_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (L ρ a H : ℝ) :
    ContDiff ℝ ∞ (rootedWindow v L ρ a H) := by
  apply ContDiff.mul _ (logWindow_contDiff v hv L ρ)
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

lemma logWindow_support (v : ℝ → ℂ) (M B L ρ : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    Function.support (logWindow v L ρ) ⊆ Set.Icc (-(M+B)*L) ((M+B)*L) := by
  intro y hy
  have hy' := hv hy
  change -M ≤ (y+ρ)/L ∧ (y+ρ)/L ≤ M at hy'
  have hl := (le_div_iff₀ hL).mp hy'.1
  have hu := (div_le_iff₀ hL).mp hy'.2
  have hr := abs_le.mp hρ
  constructor <;> nlinarith

lemma rootedWindow_compact (v : ℝ → ℂ) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    HasCompactSupport (rootedWindow v L ρ a H) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro y hy
  apply logWindow_support v M B L ρ hL hρ hv
  exact (mul_ne_zero_iff.mp hy).2

def rootSchwartz (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  (rootedWindow_compact v M B L ρ a H hL hρ hv).toSchwartzMap
    (rootedWindow_contDiff v (v.smooth ⊤) L ρ a H)

@[simp] lemma rootSchwartz_apply (v : 𝓢(ℝ, ℂ)) (M B L ρ a H y : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    rootSchwartz v M B L ρ a H hL hρ hv y = rootedWindow v L ρ a H y := rfl

def momentOrder (J : ℕ) : ℕ := J + (volume : Measure ℝ).integrablePower

open InverseMoment

def firstRootExponent (y : Fin 9 → ℝ) : ℝ :=
  -y 3-y 4/2-y 5-(y 7+y 8)/2

def secondRootExponent (y : Fin 6 → ℝ) : ℝ :=
  -y 1-y 2-(y 4+y 5)/2

def firstRootSlope : Fin 9 → ℝ := ![0,0,0,-1,-(1/2),-1,0,-(1/2),-(1/2)]
def secondRootSlope : Fin 6 → ℝ := ![0,-1,-1,0,-(1/2),-(1/2)]

def firstBalancedSlope : Fin 9 → ℝ := ![1/2,1/2,1,-1,-(1/2),0,0,0,0]
def secondBalancedSlope : Fin 6 → ℝ := ![1,-1,0,0,0,0]

end SevenEighths.InverseClippingProfiles

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFourier
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport

def frequencyReduction (d m : O) (h : d ∣ m) : Residue m →+* Residue d :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr h)

@[simp] theorem frequencyReduction_mk (d m : O) (h : d ∣ m) (x : O) :
    frequencyReduction d m h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

def residueGauss (d : O) (hd : d ≠ 0) (χ : MulChar (Residue d) ℂ)
    (h : Residue d) : ℂ :=
  ∑' x : Residue d, χ x * quotientTrace d hd (h * x)

def normalizedResidueGauss (d : O) (hd : d ≠ 0) (χ : MulChar (Residue d) ℂ)
    (h : Residue d) : ℂ :=
  residueGauss d hd χ h / (Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) : ℂ)

end SevenEighths.CenteredMomentFourier
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstReduced
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentActive
local notation "O" => ActualEisensteinCubic.O

def tripleRow (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (z : O) : ℂ :=
  χa (Ideal.Quotient.mk _ z)*χb (Ideal.Quotient.mk _ z)*G (Ideal.Quotient.mk _ z)

def tripleResidue (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (x : Residue (a*(b*r))) : ℂ :=
  χa (frequencyReduction a _ (dvd_mul_right _ _) x)*
    χb (frequencyReduction b _ (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
    G (frequencyReduction r _ (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)

@[simp] theorem tripleResidue_mk (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (z : O) :
    tripleResidue a b r χa χb G (Ideal.Quotient.mk _ z)=tripleRow a b r χa χb G z := by
  simp only [tripleResidue,tripleRow,frequencyReduction_mk]

def tripleFourier (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (h : O) : ℂ :=
  ∑' x : Residue (a*(b*r)),tripleResidue a b r χa χb G x*
    quotientTrace (a*(b*r)) (mul_ne_zero ha (mul_ne_zero hb hr)) (Ideal.Quotient.mk _ h*x)

end SevenEighths.CenteredMomentFirstReduced

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

def cutoff (x : ℝ) : ℝ := Real.smoothTransition (2-2*x)

theorem cutoff_one (x : ℝ) (hx : x ≤ 1/2) : cutoff x=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoff_zero (x : ℝ) (hx : 1 ≤ x) : cutoff x=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

def annulus (x : ℝ) : ℝ := cutoff x-cutoff (2*x)

theorem annulus_zero_low (x : ℝ) (hx : x ≤ 1/4) : annulus x=0 := by
  rw [annulus, cutoff_one x (by linarith),cutoff_one (2*x) (by linarith),sub_self]

theorem annulus_zero_high (x : ℝ) (hx : 1 ≤ x) : annulus x=0 := by
  rw [annulus,cutoff_zero x hx,cutoff_zero (2*x) (by linarith),sub_self]

theorem annulus_smooth : ContDiff ℝ ∞ annulus := by
  have hc : ContDiff ℝ ∞ cutoff :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  exact hc.sub (hc.comp (contDiff_const.mul contDiff_id))

def dyadicScale (n : ℤ) : ℝ := (2:ℝ)^n

theorem dyadicScale_pos (n : ℤ) : 0 < dyadicScale n := by
  unfold dyadicScale
  positivity

def dyadicWeight (n : ℤ) (q : ℝ) : ℝ := annulus (q/dyadicScale n)

theorem dyadicWeight_zero_low (n : ℤ) (q : ℝ) (hq : q ≤ dyadicScale n/4) :
    dyadicWeight n q=0 := by
  apply annulus_zero_low
  apply (div_le_iff₀ (dyadicScale_pos n)).mpr
  linarith

theorem dyadicWeight_zero_high (n : ℤ) (q : ℝ) (hq : dyadicScale n ≤ q) :
    dyadicWeight n q=0 := by
  apply annulus_zero_high
  exact (le_div_iff₀ (dyadicScale_pos n)).mpr (by simpa using hq)

theorem dyadicWeight_support (n : ℤ) :
    Function.support (dyadicWeight n) ⊆ Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  intro q hq
  constructor
  · exact lt_of_not_ge (fun h => hq (dyadicWeight_zero_low n q h))
  · exact lt_of_not_ge (fun h => hq (dyadicWeight_zero_high n q h))

theorem dyadicWeight_tsupport (n : ℤ) :
    tsupport (dyadicWeight n) ⊆ Set.Icc (dyadicScale n/4) (dyadicScale n) :=
  closure_minimal (fun _ h => Set.Ioo_subset_Icc_self (dyadicWeight_support n h)) isClosed_Icc

def Retained (R : ℝ) (n : ℤ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q ≤ R ∧ q ∈ tsupport (dyadicWeight n)

def retainedWeight (R q : ℝ) : ℝ := ∑' n : ℤ, if Retained R n then dyadicWeight n q else 0

def discardedWeight (R q : ℝ) : ℝ := ∑' n : ℤ, if Retained R n then 0 else dyadicWeight n q

theorem retained_scale_le (R : ℝ) (n : ℤ) (hn : Retained R n) : dyadicScale n ≤ 4*R := by
  obtain ⟨q,hq,hqR,hs⟩ := hn
  have hb := (dyadicWeight_tsupport n hs).1
  linarith

theorem finite_retained_integral_dyads (R : ℝ) :
    {n : ℤ | Retained R n ∧ ∃ q : ℝ, 1 ≤ q ∧ dyadicWeight n q ≠ 0}.Finite := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (4*R) (by norm_num : (1:ℝ) < 2)
  apply (Set.finite_Icc (1:ℤ) (k:ℤ)).subset
  intro n hn
  obtain ⟨hr,q,hq,hne⟩ := hn
  have hu := retained_scale_le R n hr
  have hs := (dyadicWeight_support n hne).2
  constructor
  · have : (2:ℝ)^(0:ℤ) < (2:ℝ)^n := by simpa [dyadicScale] using hq.trans_lt hs
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp this
    omega
  · have h : (2:ℝ)^n < (2:ℝ)^(k:ℤ) := by
      simpa only [zpow_natCast,dyadicScale] using hu.trans_lt hk
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h
    omega

def normValue (h : O) : ℝ := Ideal.absNorm (Ideal.span {h})

theorem normValue_eq_embedding (h : O) : normValue h=‖eisEmbedding h‖^2 :=
  (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span h).symm

def frequencyRadius (Tsec Z ξ : ℝ) : ℝ := Tsec*Z^(ξ/2)

def frequencyLoss (Z Csec ξ : ℝ) : ℝ := ξ/2+Real.logb Z (4*Csec)

def kernelReference (Tsec H : ℝ) : ℝ := Real.exp (-2*H)/Tsec

theorem finite_retained_above (R a : ℝ) (ha : 0 < a) :
    {n : ℤ | Retained R n ∧ ∃ q : ℝ, a ≤ q ∧ dyadicWeight n q ≠ 0}.Finite := by
  obtain ⟨k,hk,_⟩ := exists_mem_Ico_zpow ha (by norm_num : (1:ℝ) < 2)
  obtain ⟨l,hl⟩ := pow_unbounded_of_one_lt (4*R) (by norm_num : (1:ℝ) < 2)
  apply (Set.finite_Icc k (l:ℤ)).subset
  intro n hn
  obtain ⟨hr,q,hq,hne⟩ := hn
  have hu := retained_scale_le R n hr
  have hs := (dyadicWeight_support n hne).2
  constructor
  · have h : (2:ℝ)^k < (2:ℝ)^n := hk.trans_lt (hq.trans_lt hs)
    exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h).le
  · have h : (2:ℝ)^n < (2:ℝ)^(l:ℤ) := by
      simpa only [zpow_natCast,dyadicScale] using hu.trans_lt hl
    exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h).le

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end


