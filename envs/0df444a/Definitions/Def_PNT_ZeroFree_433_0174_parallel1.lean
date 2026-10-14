-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0174_parallel1
-- name    : PNT_ZeroFree_433_0174_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:24:01.617734+00:00
-- url     : https://prove2.me/theorems/fd2d28ff-a444-4756-a4ba-c5db322e8600
-- title:
--   Zero-free region foundations: MeanSquare.HighRadialBounds [0174_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.HighRadialBounds
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/HighRadialBounds.lean#L178-L567

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0109_1
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0135_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel2
import Definitions.Def_PNT_ZeroFree_433_0149_parallel2
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/HighRadialBounds.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace InitialMeanSquare

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

open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

lemma initial_bin_row_scale_le (U K : ℝ) (hK : 1 ≤ K) (j : SecondLogIndex)
    (hj : j ∈ secondLogBinBox U K) : secondLogK j ≤ K := by
  have hj' : j.1 < normLogBin U+1 ∧ j.2.1 < normLogBin U+1 ∧ j.2.2 < normLogBin K+1 := by
    simpa only [secondLogBinBox,Finset.mem_product,Finset.mem_range] using hj
  have hscale : secondLogK j ≤ normLogScale (normLogBin K) := by
    unfold secondLogK normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.2.2
  exact hscale.trans (normLogBin_scale_bounds K hK).1


end

open ActualEisensteinCubic ConcretePrimeRowBridge


end

section

open MeasureTheory
open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialElementaryConstant (A V : ℝ) : ℝ := 6*128^4*(Real.exp A*V)^2

lemma initialElementaryConstant_nonneg (A V : ℝ) : 0 ≤ initialElementaryConstant A V := by
  unfold initialElementaryConstant
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_child_energy_elementary (F : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (T : Finset (Ideal O × O)) (V : ℝ → ℂ)
    (X lengthScale K A Vmax a b : ℝ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV : ∀ t,‖V t‖ ≤ Vmax) (hs : ∀ t,V t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) (tn rn : Bool) :
    childEnergy p hp hcop hg F Ψ m T V X tn rn a b ≤
      initialElementaryConstant A Vmax*K*X^2*lengthScale := by
  by_cases hscale : 1 ≤ X*Real.exp A
  · have hb := childEnergy_elementary_normalized p hp hcop hg hc hinj F Ψ hΨ m T V
      X lengthScale K A Vmax a b hX hL hK hA hVmax hV hs hT tn rn
    have hXL : 0 < X*lengthScale := mul_pos hX (zero_lt_one.trans_le hL)
    have hb' := (div_le_iff₀ hXL).mp hb
    rw [max_eq_right hscale] at hb'
    convert! hb' using 1
    unfold initialElementaryConstant
    field_simp

  · rw [childEnergy_subunit p hp hcop hg F Ψ m T V X A hX hs
      (lt_of_not_ge hscale) a b tn rn]
    exact mul_nonneg (mul_nonneg (mul_nonneg (initialElementaryConstant_nonneg A Vmax)
      (zero_le_one.trans hK)) (sq_nonneg X)) (zero_le_one.trans hL)

include hc hinj in

theorem initial_child_geometric_elementary (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X lengthScale K A Vmax : ℝ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) (q : Frequency) :
    childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X X q ≤
      initialElementaryConstant A Vmax*K*(X*lengthScale)^2 := by
  let E := initialElementaryConstant A Vmax*K*X^2*lengthScale
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (mul_nonneg (initialElementaryConstant_nonneg A Vmax)
      (zero_le_one.trans hK)) (sq_nonneg X)) (zero_le_one.trans hL)
  have he₁ := initial_child_energy_elementary p hp hcop hg hc hinj F Ψ₁ hΨ₁ m T V₁
    X lengthScale K A Vmax q.1 q.2.2 hX hL hK hA hVmax hV₁ hs₁ hT true false
  have he₂ := initial_child_energy_elementary p hp hcop hg hc hinj F Ψ₂ hΨ₂ m T V₂
    X lengthScale K A Vmax q.2.1 q.2.2 hX hL hK hA hVmax hV₂ hs₂ hT false true
  have hb : childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X X q ≤ E := by
    calc
      _ ≤ Real.sqrt E*Real.sqrt E := mul_le_mul (Real.sqrt_le_sqrt he₁)
        (Real.sqrt_le_sqrt he₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = E := Real.mul_self_sqrt hE
  apply hb.trans
  calc
    E ≤ E*lengthScale := le_mul_of_one_le_right hE hL
    _ = _ := by dsimp only [E]; ring


end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialRestrictedBinCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (Z H ε : ℝ) (j : SecondLogIndex)
    (V₁ V₂ : ℝ → ℂ) (B : Frequency → ℝ) : ℝ :=
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
    (∫ t₁ : ℝ,∫ t₂ : ℝ,∫ t₃ : ℝ,B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) V₁ V₂ X X (t₁,t₂,t₃))


variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))


end

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialRadial (Z H R : ℝ) (j : SecondLogIndex) : ℝ :=
  H*secondLogK j*R^2/Z^2

theorem initial_radial_absorbs_rows (Z H R k : ℝ) (N : ℕ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hR : 1 ≤ R) (hk : 0 ≤ k) :
    H*k^2/(1+H*k*R^2/Z^2)^(N+2) ≤ Z^4/(1+H*k*R^2/Z^2)^N := by
  let r := H*k*R^2/Z^2
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have h1 : 0 < 1+r := by linarith
  have hHR : 1 ≤ H*R^4 := one_le_mul_of_one_le_of_one_le hH (one_le_pow₀ hR)
  have he : Z^4*r^2=(H*k^2)*(H*R^4) := by
    dsimp [r]
    field_simp

  have hnum : H*k^2 ≤ Z^4*r^2 := by
    rw [he]
    exact le_mul_of_one_le_right (mul_nonneg hH0 (sq_nonneg k)) hHR
  change H*k^2/(1+r)^(N+2) ≤ Z^4/(1+r)^N
  calc
    _ ≤ Z^4*r^2/(1+r)^(N+2) := div_le_div_of_nonneg_right hnum (pow_nonneg h1.le _)
    _ ≤ Z^4*(1+r)^2/(1+r)^(N+2) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg h1.le _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr (by linarith) 2) (by positivity)
    _ = _ := by rw [pow_add]; field_simp

def initialHighRadialConstant (A Vmax Cs : ℝ) : ℝ :=
  Real.exp 8*initialElementaryConstant A Vmax*Cs*(∫ t : ℝ,firstLogDensity 0 t)^3

lemma initialHighRadialConstant_nonneg (A Vmax Cs : ℝ) (hCs : 0 ≤ Cs) :
    0 ≤ initialHighRadialConstant A Vmax Cs := by
  have hi : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hc := initialElementaryConstant_nonneg A Vmax
  unfold initialHighRadialConstant
  positivity


end InitialMeanSquare

end

end OAI

end


