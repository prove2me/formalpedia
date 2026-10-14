-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0264_parallel2
-- name    : PNT_ZeroFree_433_0264_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:33:13.509086+00:00
-- url     : https://prove2.me/theorems/32b1486a-294c-47a6-8bf4-43b8dd6299dd
-- title:
--   Zero-free region foundations: GaussSum.FiniteTranslations [0264_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.FiniteTranslations
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/FiniteTranslations.lean#L88-L367

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0052
import Definitions.Def_PNT_ZeroFree_433_0057
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0131
import Definitions.Def_PNT_ZeroFree_433_0132
import Definitions.Def_PNT_ZeroFree_433_0159_parallel1
import Definitions.Def_PNT_ZeroFree_433_0178_parallel1
import Definitions.Def_PNT_ZeroFree_433_0189_parallel1
import Definitions.Def_PNT_ZeroFree_433_0194_parallel1
import Definitions.Def_PNT_ZeroFree_433_0196_parallel1
import Definitions.Def_PNT_ZeroFree_433_0199_parallel1
import Definitions.Def_PNT_ZeroFree_433_0215_parallel2
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0227_parallel2
import Definitions.Def_PNT_ZeroFree_433_0230_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0236_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel2
import Definitions.Def_PNT_ZeroFree_433_0248_parallel1
import Definitions.Def_PNT_ZeroFree_433_0253_parallel1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel1
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel2
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0266_parallel1
import Definitions.Def_PNT_ZeroFree_433_0270_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/FiniteTranslations.lean
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CompletedGauss
open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

open CubicEisenstein


theorem besselSmoothingIntegrand_reflected_integrable {α : Type*} [Countable α]
    (F : ℝ→ℂ) (r : α→ℝ) (hr : ∀i,0<r i) (a : α→ℂ)
    (q d Q : ℝ) (hq : 0<q) (hd : 0<d) (hQ : 0<Q) (A : ℂ)
    (hreflect : ∀v : ℝ,0<v→F v=
      A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has : Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V : ℝ→ℂ) (v0 v1 : ℝ) (hv0 : 0<v0)
    (hVs : Function.support V⊆Set.Icc v0 v1) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)) := by
  let P : ℝ→ℂ := fun t=>
    A*(Q:ℂ)^(2-2*((-1:ℂ)+t*Complex.I))*
      besselReflectionFactor q d ((-1:ℂ)+t*Complex.I)*
        (X:ℂ)^(((-1:ℂ)+t*Complex.I)-1/2)
  let D : ℝ→ℂ := fun t=>∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+(-t)*Complex.I))
  let K : ℝ→ℂ := fun t=>CubicReflectionKernel.mellinEulerData V 0 ((3/2:ℂ)+(-t)*Complex.I)
  have hK : Integrable K := by
    have hh := CubicReflectionKernel.mellinEulerData_vertical_integrable V v0 v1 hv0 hVs hV
      2 0 (3/2) (by norm_num)
    simpa only [K,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using hh.comp_neg
  have hD : Continuous D := by
    have hh := (weighted_vertical_series_continuous r hr a (3/2) has).comp continuous_neg
    simpa only [D,Function.comp_def,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using hh
  have hDb (t : ℝ) : ‖D t‖≤∑'i,‖a i‖*(r i)^(-(3/2:ℝ)) := by
    simpa only [D,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using
      weighted_vertical_series_norm r hr a (3/2) has (-t)
  have hP : Continuous P := by
    have h1 := positive_cpow_comp_continuous Q hQ
      (fun t : ℝ=>2-2*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h2 := positive_cpow_comp_continuous (4*Real.pi*q) (by positivity)
      (fun t : ℝ=>2*((-1:ℂ)+t*Complex.I)+1) (by fun_prop)
    have h3 := positive_cpow_comp_continuous 2 (by norm_num)
      (fun t : ℝ=>2-4*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h4 := positive_cpow_comp_continuous (4*Real.pi*d) (by positivity)
      (fun t : ℝ=>3-2*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h5 := positive_cpow_comp_continuous X hX
      (fun t : ℝ=>((-1:ℂ)+t*Complex.I)-1/2) (by fun_prop)
    have hn (t : ℝ) : (((4*Real.pi*d:ℝ):ℂ)^(3-2*((-1:ℂ)+t*Complex.I)))≠0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
    convert! (((continuous_const (y:=A)).mul h1).mul ((h2.mul h3).div h4 hn)).mul h5 using 1 <;>
      (ext t; simp only [P,besselReflectionFactor,Pi.mul_apply,Pi.div_apply,Complex.ofReal_ofNat])
  have hPn (t : ℝ) : ‖P t‖=‖P 0‖ := by
    simp only [P,norm_mul,besselReflectionFactor_norm q d hq hd,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ,Complex.norm_cpow_eq_rpow_re_of_pos hX]
    norm_num
  have hi := (hK.mul_bdd hP.aestronglyMeasurable
    (Eventually.of_forall (fun t=>(hPn t).le))).mul_bdd hD.aestronglyMeasurable
      (Eventually.of_forall hDb)
  apply hi.congr
  filter_upwards with t
  have he : ((-1:ℂ)+t*Complex.I).re-1/2=-(3/2:ℝ) := by norm_num
  have hsum : Summable (fun i=>‖a i‖*(r i)^(((-1:ℂ)+t*Complex.I).re-1/2)) := by
    simpa only [he] using has
  have href := continuedBesselDirichlet_reflection F r hr a q d Q hd hQ A hreflect
    ((-1:ℂ)+t*Complex.I) (by norm_num) hsum
  change K t*P t*D t=besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)
  rw [besselSmoothingIntegrand,href]
  dsimp only [K,P,D]
  unfold CubicReflectionKernel.mellinEulerData CubicReflectionKernel.mellinData
  simp only [pow_zero,one_mul]
  have he1 : (1/2:ℂ)-((-1:ℂ)+t*Complex.I)=(3/2:ℂ)+(-t)*Complex.I := by ring
  have he2 : ((-1:ℂ)+t*Complex.I)-1/2=-((3/2:ℂ)+(-t)*Complex.I) := by ring
  rw [he1,he2]
  ring

end CompletedGauss

namespace CubicEisenstein

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O


namespace SubexponentialBesselCoefficients

def finiteTranslate {ι : Type*} [Fintype ι] (coeff : SubexponentialBesselCoefficients)
    (shift weight : ι→ℂ) : SubexponentialBesselCoefficients where
  value h := finiteTranslationMultiplier shift weight h*coeff.value h
  growth epsilon he := by
    obtain ⟨C,hC,hbound⟩:=coeff.growth epsilon he
    refine ⟨(∑i,‖weight i‖)*C,by positivity,?_⟩
    intro h hh
    rw [norm_mul]
    calc
      _ ≤ (∑i,‖weight i‖)*(C*Real.exp (epsilon*‖cuspFrequency h‖)) :=
        mul_le_mul (finiteTranslationMultiplier_norm shift weight h) (hbound h hh)
          (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
      _ = _ := by ring

lemma term_horizontal_translate (coeff : SubexponentialBesselCoefficients)
    (h : Eis) (v : ℝ) (z a : ℂ) :
    coeff.term h (v,z+a)=ShortDraftTrace.breveE (cuspFrequency h*a)*coeff.term h (v,z) := by
  by_cases hh:h=0
  · simp only [term,if_pos hh,mul_zero]
  · simp only [term,if_neg hh,mul_add,AddChar.map_add_eq_mul]
    ring

lemma finiteTranslate_term {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (h : Eis) (v : ℝ) (z : ℂ) :
    (coeff.finiteTranslate shift weight).term h (v,z)=
      ∑i,weight i*coeff.term h (v,z+shift i) := by
  simp_rw [term_horizontal_translate]
  rw [show (∑i,weight i*(ShortDraftTrace.breveE (cuspFrequency h*shift i)*coeff.term h (v,z)))=
      finiteTranslationMultiplier shift weight h*coeff.term h (v,z) by
    simp only [finiteTranslationMultiplier,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  by_cases hh:h=0
  · simp only [term,if_pos hh,mul_zero]
  · simp only [term,if_neg hh,finiteTranslate]
    ring


end SubexponentialBesselCoefficients


end


section
local notation "Eis" => ActualEisensteinCubic.O


lemma finiteTranslate_term_multiplier {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (h : Eis) (v : ℝ) (z : ℂ) :
    (coeff.finiteTranslate shift weight).term h (v,z)=
      finiteTranslationMultiplier shift weight h*coeff.term h (v,z) := by
  by_cases hh:h=0
  · simp only [SubexponentialBesselCoefficients.term,if_pos hh,mul_zero]
  · simp only [SubexponentialBesselCoefficients.term,if_neg hh,
      SubexponentialBesselCoefficients.finiteTranslate]
    ring


end


end


end CubicEisenstein

end

end OAI

end


