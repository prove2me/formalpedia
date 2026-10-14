-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0223_parallel1
-- name    : PNT_ZeroFree_433_0223_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:23:15.165068+00:00
-- url     : https://prove2.me/theorems/d125f029-c7cd-44ea-9698-c043ebb24877
-- title:
--   Zero-free region foundations: Eisenstein.ResidualFourierSeries [0223_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierSeries
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ResidualFourierSeries.lean#L85-L586

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0124
import Definitions.Def_PNT_ZeroFree_433_0126
import Definitions.Def_PNT_ZeroFree_433_0127
import Definitions.Def_PNT_ZeroFree_433_0129_parallel2
import Definitions.Def_PNT_ZeroFree_433_0211_parallel1
import Definitions.Def_PNT_ZeroFree_433_0213_parallel1
import Definitions.Def_PNT_ZeroFree_433_0219_parallel1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1
import Definitions.Def_PNT_ZeroFree_433_0273_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ResidualFourierSeries.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspFrequency_norm_lower (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹≤‖cuspFrequency h‖ := by
  have hn : 1≤‖ConcreteTraceCRT.eisEmbedding h‖^2 := by
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hh))
  have hnorm : 1≤‖ConcreteTraceCRT.eisEmbedding h‖ := by nlinarith [norm_nonneg (ConcreteTraceCRT.eisEmbedding h)]
  rw [cuspFrequency,norm_div,inv_eq_one_div]
  exact div_le_div_of_nonneg_right hnorm (norm_nonneg _)

def cubicBesselUpperAway (deltaLoss : ℝ) : ℝ :=
  (1/2:ℝ)*(deltaLoss/2)^(-(1:ℝ)/3)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))

lemma cubicBesselUpperAway_pos (deltaLoss : ℝ) (hδ : 0<deltaLoss) : 0<cubicBesselUpperAway deltaLoss := by
  unfold cubicBesselUpperAway
  positivity

lemma schlafliBesselK_cubic_upper_away (deltaLoss x : ℝ) (hδ : 0<deltaLoss) (hx : deltaLoss≤x) :
    ‖schlafliBesselK (1/3:ℂ) x‖≤cubicBesselUpperAway deltaLoss*Real.exp (-x/2) := by
  have hxp := hδ.trans_le hx
  rw [schlafliBesselK_cubic_norm_re x hxp,schlafliBesselK_cubic_real x hxp,Complex.ofReal_re]
  have hp : (x/2)^(-(1:ℝ)/3)≤(deltaLoss/2)^(-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  calc
    _ ≤ (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) :=
      mul_le_mul_of_nonneg_left (cubicBesselIntegral_upper x) (by positivity)
    _ ≤ (1/2:ℝ)*(deltaLoss/2)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ = _ := by unfold cubicBesselUpperAway;ring


end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O


lemma integral_cusp_character_product (h k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0 := by
  have hphase (z : ℂ) : ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z)=ShortDraftTrace.breveE (-cuspFrequency (k-h)*z) := by
    rw [←AddChar.map_add_eq_mul]
    congr 1
    unfold cuspFrequency
    rw [map_sub]
    ring
  simp_rw [hphase]
  simpa only [sub_eq_zero,eq_comm] using integral_cusp_character (k-h)


end


section
open Filter MeasureTheory
open scoped Classical Topology

lemma ae_eq_of_boundedContinuous_height_tests («μ» : Measure ℝ) (f g : ℝ→ℂ)
    (hf : Integrable f «μ») (hg : Integrable g «μ»)
    (heq : ∀ρ : BoundedContinuousFunction ℝ ℂ,
      (∫x,ρ x*f x∂«μ»)=(∫x,ρ x*g x∂«μ»)) : f=ᵐ[«μ»]g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable
  intro test htest hsupp
  obtain ⟨C,hC⟩ := hsupp.exists_bound_of_continuous htest.continuous
  let ρ : BoundedContinuousFunction ℝ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (test x:ℂ))
      (Complex.continuous_ofReal.comp htest.continuous) C (fun x => by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using hC x)
  have hh := heq ρ
  change (∫x,(test x:ℂ)*f x∂«μ»)=(∫x,(test x:ℂ)*g x∂«μ») at hh
  simpa only [Complex.real_smul] using hh

lemma interval_ae_eq_of_boundedContinuous_height_tests (a b : ℝ) (f g : ℝ→ℂ)
    (hf : IntegrableOn f (Set.Icc a b)) (hg : IntegrableOn g (Set.Icc a b))
    (heq : ∀ρ : BoundedContinuousFunction ℝ ℂ,
      (∫x in Set.Icc a b,ρ x*f x)=(∫x in Set.Icc a b,ρ x*g x)) :
    f=ᵐ[volume.restrict (Set.Icc a b)]g :=
  ae_eq_of_boundedContinuous_height_tests (volume.restrict (Set.Icc a b)) f g hf hg heq

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

def compactHeightMellin (a b : ℝ) (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  ∫v in Set.Icc a b,ρ v*(v:ℂ)^s

lemma compactHeightMellin_integrable (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) :
    IntegrableOn (fun v : ℝ => ρ v*(v:ℂ)^s) (Set.Icc a b) := by
  apply ContinuousOn.integrableOn_Icc
  apply ρ.continuous.continuousOn.mul
  intro v hv
  exact (Complex.continuousAt_ofReal_cpow_const v s
    (Or.inr (ha.trans_le hv.1).ne')).continuousWithinAt

theorem compactHeightMellin_differentiable (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) : Differentiable ℂ (compactHeightMellin a b ρ) := by
  let heightLog : ℝ→ℂ := fun v => (Real.log (max a v):ℂ)
  have hl : Continuous heightLog := Complex.continuous_ofReal.comp
    ((continuous_const.max continuous_id).log (fun v => (ha.trans_le (le_max_left a v)).ne'))
  let F : ℂ→ℝ→ℂ := fun s v => ρ v*Complex.exp (heightLog v*s)
  let F' : ℂ→ℝ→ℂ := fun s v => ρ v*(Complex.exp (heightLog v*s)*heightLog v)
  have hF : ∀s,Continuous (F s) := fun s => ρ.continuous.mul ((hl.mul_const s).cexp)
  have hF' : Continuous (fun p : ℂ×ℝ => F' p.1 p.2) := by
    exact (ρ.continuous.comp continuous_snd).mul
      ((((hl.comp continuous_snd).mul continuous_fst).cexp).mul (hl.comp continuous_snd))
  have hder : ∀s v,HasDerivAt (fun w => F w v) (F' s v) s := by
    intro s v
    simpa only [F,F',id_eq,mul_one] using
      (((hasDerivAt_id s).const_mul (heightLog v)).cexp).const_mul (ρ v)
  have heq : compactHeightMellin a b ρ=(fun s => ∫v in Set.Icc a b,F s v) := by
    funext s
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    dsimp only [compactHeightMellin,F,heightLog]
    rw [max_eq_right hv.1,Complex.ofReal_log (ha.trans_le hv.1).le,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ha.trans_le hv.1).ne')]
  rw [heq]
  intro s
  obtain ⟨C,hC⟩ := ((isCompact_closedBall s (1:ℝ)).prod (isCompact_Icc : IsCompact (Set.Icc a b))).exists_bound_of_continuousOn hF'.continuousOn
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ»:=volume.restrict (Set.Icc a b)) (F:=F) (F':=F')
    (bound:=fun _ => C) (Metric.ball_mem_nhds s (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall (fun w => (hF w).aestronglyMeasurable))
    ((hF s).continuousOn.integrableOn_Icc)
    ((hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv w hw
      exact hC (w,v) ⟨Metric.ball_subset_closedBall hw,hv⟩)
    (integrable_const C)
    (Eventually.of_forall (fun v w _ => hder w v))
  exact hd.2.differentiableAt

lemma compactHeightMellin_analyticAt (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) :
    AnalyticAt ℂ (compactHeightMellin a b ρ) s :=
  (compactHeightMellin_differentiable a b ha ρ).analyticAt s

open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O

def cuspHeightConstantAverage (a b : ℝ) (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(compactHeightMellin a b ρ (s-3)+
    ((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0*compactHeightMellin a b ρ (-s-1))


lemma cuspScatterHeightFactor_analyticAt (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ cuspScatterHeightFactor s := by
  have hne : s≠0 := by intro he; subst s; norm_num at hs
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds hne] with z hz
  exact cuspScatterHeightFactor_differentiableAt z hz


end CubicEisenstein

end

end OAI

end


