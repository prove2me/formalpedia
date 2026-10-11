-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0184_parallel1
-- name    : PNT_ZeroFree_433_0184_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:55:43.915084+00:00
-- url     : https://prove2.me/theorems/48affc43-44fb-4e70-9013-cd2ba58ee25b
-- title:
--   Zero-free region foundations: CubicSieve.ReopeningSeparation [0184_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.ReopeningSeparation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ReopeningSeparation.lean#L84-L606

import Definitions.Def_PNT_ZeroFree_433_0003
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0012
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0049
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0065_1
import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0069
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0073
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0079
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0188_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0228_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel1
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1
import Definitions.Def_PNT_ZeroFree_433_0303_parallel1
import Definitions.Def_PNT_ZeroFree_433_0329_parallel1
import Definitions.Def_PNT_ZeroFree_433_0330_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ReopeningSeparation.lean
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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (columnLog primeProductNorm)
open FourierBridge (logPhase)
open JointLogSeparation (frequencyTwist)

def normPhase (t : ℝ) : ActualEisensteinCubic.O →* ℂ where
  toFun z := if z=0 then 0 else logPhase t (Real.log (‖eisEmbedding z‖^2))
  map_one' := by simp [FourierBridge.logPhase_zero]
  map_mul' a b := by
    by_cases ha : a=0
    · simp [ha]
    by_cases hb : b=0
    · simp [hb]
    simp only [if_neg ha,if_neg hb,if_neg (mul_ne_zero ha hb),map_mul,norm_mul,mul_pow]
    rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha)))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hb))),FourierBridge.logPhase_add]

@[simp] theorem normPhase_zero (t : ℝ) : normPhase t 0=0 := by simp [normPhase]

theorem normPhase_of_ne_zero (t : ℝ) (z : ActualEisensteinCubic.O) (hz : z≠0) :
    normPhase t z=logPhase t (Real.log (‖eisEmbedding z‖^2)) := by simp [normPhase,hz]

theorem normPhase_norm (t : ℝ) (z : ActualEisensteinCubic.O) (hz : z≠0) : ‖normPhase t z‖=1 := by
  rw [normPhase_of_ne_zero t z hz,FourierBridge.logPhase_norm]

theorem normPhase_norm_le_one (t : ℝ) (z : ActualEisensteinCubic.O) : ‖normPhase t z‖≤1 := by
  by_cases hz : z=0
  · simp [hz]
  · rw [normPhase_norm t z hz]

theorem normPhase_add (s t : ℝ) : normPhase (s+t)=normPhase s*normPhase t := by
  ext z
  by_cases hz : z=0
  · simp [hz]
  · simp only [MonoidHom.mul_apply,normPhase_of_ne_zero _ z hz,JointLogSeparation.logPhase_add_frequency]


def normHeightTwist (Ψ : ActualEisensteinCubic.O →* ℂ) (t : ℝ) : ActualEisensteinCubic.O →* ℂ := Ψ*normPhase t

theorem normHeightTwist_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (t : ℝ) (z : ActualEisensteinCubic.O) :
    ‖normHeightTwist Ψ t z‖≤‖Ψ z‖ := by
  simp only [normHeightTwist,MonoidHom.mul_apply,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (normPhase_norm_le_one t z)

theorem normHeightTwist_twice (Ψ : ActualEisensteinCubic.O →* ℂ) (s t : ℝ) :
    normHeightTwist (normHeightTwist Ψ s) t=normHeightTwist Ψ (s+t) := by
  simp only [normHeightTwist,normPhase_add,mul_assoc]

theorem normHeightTwist_mul (Ψ Ξ : ActualEisensteinCubic.O →* ℂ) (t : ℝ) :
    normHeightTwist (Ψ*Ξ) t=normHeightTwist Ψ t*Ξ := by
  unfold normHeightTwist
  ac_rfl

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)

include hp in
omit [DecidableEq ι] in
theorem logPhase_columnLog (X t : ℝ) (hX : 0<X) (S : Finset ι) :
    logPhase t (columnLog p X S)=
      logPhase t (-Real.log X)*normPhase t (∏i∈S,p i) := by
  rw [normPhase_of_ne_zero t _ (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))]
  rw [columnLog,Real.log_div (FirstPassCubeLabels.primeProductNorm_pos p hp S).ne' hX.ne']
  rw [sub_eq_add_neg,FourierBridge.logPhase_add]
  exact mul_comm _ _

variable [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem canonicalSourceCoefficient_frequencyTwist (Ψ : ActualEisensteinCubic.O →* ℂ) (m f : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) (S : Finset ι) :
    canonicalSourceCoefficient p hp hcop hg Ψ m f
      (fun U=>frequencyTwist g t (columnLog p X U)) S=
    logPhase t (-Real.log X)*canonicalSourceCoefficient p hp hcop hg (normHeightTwist Ψ t) m f
      (fun U=>g (columnLog p X U)) S := by
  simp only [canonicalSourceCoefficient,JointLogSeparation.frequencyTwist_apply,
    logPhase_columnLog p hp X t hX S,normHeightTwist,MonoidHom.mul_apply]
  ring

theorem fixedChildRow_frequencyTwist (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f y : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) :
    fixedChildRow p hp hcop hg pool Ψ m (fun U=>frequencyTwist g t (columnLog p X U)) f y=
    logPhase t (-Real.log X)*fixedChildRow p hp hcop hg pool (normHeightTwist Ψ t) m
      (fun U=>g (columnLog p X U)) f y := by
  unfold fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,JointLogSeparation.frequencyTwist_apply,
    logPhase_columnLog p hp X t hX S,normHeightTwist,MonoidHom.mul_apply]
  ring

theorem fixedChildRow_frequencyTwist_norm (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f y : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) :
    ‖fixedChildRow p hp hcop hg pool Ψ m (fun U=>frequencyTwist g t (columnLog p X U)) f y‖=
    ‖fixedChildRow p hp hcop hg pool (normHeightTwist Ψ t) m
      (fun U=>g (columnLog p X U)) f y‖ := by
  rw [fixedChildRow_frequencyTwist p hp hcop hg pool Ψ m f y g X t hX,norm_mul,FourierBridge.logPhase_norm,one_mul]

end SecondPassArithmetic

section

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FourierBridge (logPhase)
open FirstPassCubeLabels (columnLog)

def secondSignedHeight (negative : Bool) (a b : ℝ) : ℝ :=
  if negative then b-a else a-b

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)


variable [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})


end SecondPassArithmetic


open scoped BigOperators Classical
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic

theorem firstCoreTwist_normHeight (negative : Bool) (χ : RayFourExpansion.RayCharacter)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (r : FirstCoreIndex) (t : ℝ) :
    firstCoreTwist negative χ (normHeightTwist Ψ t) r=
      normHeightTwist (firstCoreTwist negative χ Ψ r) t := by
  unfold firstCoreTwist normHeightTwist
  ac_rfl

theorem secondRayMinus_normHeight (Ψ : ActualEisensteinCubic.O →* ℂ) (r : SecondRayIndex) (t : ℝ) :
    secondRayMinus (normHeightTwist Ψ t) r=normHeightTwist (secondRayMinus Ψ r) t := by
  unfold secondRayMinus normHeightTwist
  ac_rfl

theorem secondRayPlus_normHeight (Ψ : ActualEisensteinCubic.O →* ℂ) (r : SecondRayIndex) (t : ℝ) :
    secondRayPlus (normHeightTwist Ψ t) r=normHeightTwist (secondRayPlus Ψ r) t := by
  unfold secondRayPlus normHeightTwist
  ac_rfl

end SecondPassArithmetic


end

open scoped BigOperators Classical SchwartzMap


open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

namespace CanonicalCubeSeparation
open FourierBridge JointLogSeparation FirstPassCubeLabels

def columnWindowRadius (a b : ℝ) : ℝ := |Real.log a| + |Real.log b| + 3

lemma columnWindowRadius_nonneg (a b : ℝ) : 0 ≤ columnWindowRadius a b := by
  unfold columnWindowRadius
  positivity

def sourceLogProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) := by
  have hc : HasCompactSupport (fun u : ℝ => W (Real.exp u)) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (Real.log a) (Real.log b)) isCompact_Icc
    intro u hu
    have hm := hs hu
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log ha hm.1
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hm.2
  exact hc.toSchwartzMap (hW.comp Real.contDiff_exp)

@[simp] lemma sourceLogProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (u : ℝ) :
    sourceLogProfile W a b ha hs hW u = W (Real.exp u) := rfl

def reopeningCoefficient (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  𝓕 (sourceLogProfile W a b ha hs hW)

def cubeFrequencyFactor (t ξ : ℝ) : ℂ :=
  (Real.exp (t/2) : ℂ) * logPhase ξ (3*t)

@[simp] lemma cubeFrequencyFactor_norm (t ξ : ℝ) :
    ‖cubeFrequencyFactor t ξ‖ = Real.exp (t/2) := by
  simp only [cubeFrequencyFactor, norm_mul, logPhase_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma cubeFrequencyFactor_bound (t ξ : ℝ) (ht : t ≤ 1) :
    ‖cubeFrequencyFactor t ξ‖ ≤ Real.exp (1/2) := by
  rw [cubeFrequencyFactor_norm]
  exact Real.exp_le_exp.mpr (by linarith)

lemma active_column_window (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (t u : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hWu : W (Real.exp (u+3*t)) ≠ 0) :
    |u| ≤ columnWindowRadius a b := by
  have hab := hs hWu
  have hlo : Real.log a ≤ u+3*t := by
    simpa only [Real.log_exp] using Real.log_le_log ha hab.1
  have hhi : u+3*t ≤ Real.log b := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hab.2
  unfold columnWindowRadius
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b),
    abs_nonneg (Real.log a), abs_nonneg (Real.log b), ht.1, ht.2]

lemma reopening_integrable (b V : 𝓢(ℝ,ℂ)) (t u : ℝ) :
    Integrable (fun ξ : ℝ => b ξ * cubeFrequencyFactor t ξ * frequencyTwist V ξ u) := by
  have hi : Integrable (fun ξ : ℝ =>
      b ξ * ((Real.exp (t/2) : ℂ) * logPhase ξ (3*t) * (logPhase ξ u * V u))) := by
    apply b.integrable.mul_bdd (c := Real.exp (t/2) * ‖V u‖)
    · exact (((logPhase_continuous_left (3*t)).const_mul _).mul
        ((logPhase_continuous_left u).mul_const _)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ξ => by
        simp only [norm_mul, logPhase_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), one_mul, mul_one, le_refl])
  convert! hi using 1
  funext ξ
  rw [frequencyTwist_apply]
  unfold cubeFrequencyFactor
  ring

theorem reopening_separation_with_window (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (t u : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (Real.exp (t/2) : ℂ) * W (Real.exp (u+3*t)) =
      ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
        cubeFrequencyFactor t ξ * frequencyTwist V ξ u := by
  have hwindow : V u * W (Real.exp (u+3*t)) = W (Real.exp (u+3*t)) := by
    by_cases hz : W (Real.exp (u+3*t)) = 0
    · simp [hz]
    · rw [hV u (active_column_window W a b ha hs t u ht hz), one_mul]
  have hinv := schwartz_phase_inversion
    (sourceLogProfile W a b ha hs hW) (u+3*t)
  change W (Real.exp (u+3*t)) =
    ∫ ξ : ℝ, logPhase ξ (u+3*t) * reopeningCoefficient W a b ha hs hW ξ at hinv
  calc
    _ = ((Real.exp (t/2) : ℂ) * V u) * W (Real.exp (u+3*t)) := by
      rw [mul_assoc, hwindow]
    _ = ∫ ξ : ℝ, ((Real.exp (t/2) : ℂ) * V u) *
        (logPhase ξ (u+3*t) * reopeningCoefficient W a b ha hs hW ξ) := by
      rw [hinv, integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [logPhase_add, frequencyTwist_apply]
      unfold cubeFrequencyFactor
      ring

theorem exists_reopening_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ V : 𝓢(ℝ,ℂ), HasCompactSupport V ∧
      (∀ u, |u| ≤ columnWindowRadius a b → V u = 1) ∧
      (∀ u, V u ≠ 0 → |u| ≤ columnWindowRadius a b + 1) ∧
      (∀ t u : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
        (Real.exp (t/2) : ℂ) * W (Real.exp (u+3*t)) =
          ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
            cubeFrequencyFactor t ξ * frequencyTwist V ξ u) ∧
      (∀ t u : ℝ, Integrable (fun ξ : ℝ => reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor t ξ * frequencyTwist V ξ u)) ∧
      (∀ J : ℕ, ∃ C : ℝ, 0 < C ∧
        Integrable (fun ξ : ℝ => (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖) ∧
        (∫ ξ : ℝ, (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖) ≤ C ∧
        ∀ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖ ≤ C * firstLogDensity J ξ) := by
  obtain ⟨v,hvc,hvs,hvone,hvsupp,_⟩ := exists_complex_smooth_cutoff
    (columnWindowRadius a b) (columnWindowRadius_nonneg a b)
  let V : 𝓢(ℝ,ℂ) := hvc.toSchwartzMap hvs
  have hVone : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1 := hvone
  refine ⟨V,hvc,hVone,?_,?_,reopening_integrable _ V,?_⟩
  · intro u hu
    have hmem := hvsupp (subset_tsupport v hu)
    exact abs_le.mpr hmem
  · exact fun t u ht => reopening_separation_with_window W a b ha hs hW V hVone t u ht
  · intro J
    let g := sourceLogProfile W a b ha hs hW
    let c := fourierPointBound (J+2) (profileSourceBound g (J+2))
    let m := ∫ ξ : ℝ, (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖
    have hc : 0 ≤ c := fourierPointBound_nonneg _ _ (profileSourceBound_nonneg _ _)
    have hm : 0 ≤ m := integral_nonneg (fun ξ => by positivity)
    refine ⟨1+c+m,by positivity,weighted_schwartz_integrable _ J,by dsimp [m]; linarith,?_⟩
    intro ξ
    exact (profile_fourier_envelope g J ξ).trans
      (mul_le_mul_of_nonneg_right (by linarith : c ≤ 1+c+m) (firstLogDensity_nonneg J ξ))

end CanonicalCubeSeparation

end

end OAI

end


