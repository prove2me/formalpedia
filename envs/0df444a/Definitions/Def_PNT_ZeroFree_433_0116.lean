-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0116
-- name    : PNT_ZeroFree_433_0116
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:31:07.395112+00:00
-- url     : https://prove2.me/theorems/e53713df-d9d3-49ac-90db-ad80b4406dd1
-- title:
--   Zero-free region foundations: CubicSieve.SquarefreeTransfer [0116]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.SquarefreeTransfer
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/SquarefreeTransfer.lean#L87-L617

import Definitions.Def_PNT_ZeroFree_433_0115

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/SquarefreeTransfer.lean#L87-L617
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.SquarefreeTransfer
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

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (densityChildEnergy childGeometricMean childEnergy)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondSquarefreeLogNormalizedEnergy (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) : ℝ :=
  densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m
    (secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) V₁ V₂
    (secondLogX p R X j) (secondLogX p R X j) J /
  (secondLogX p R X j * secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j)

lemma secondSquarefreeLogNormalizedEnergy_nonneg
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) :
    0 ≤ secondSquarefreeLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J := by
  apply div_nonneg
  · apply integral_nonneg
    intro t₁
    apply integral_nonneg
    intro t₂
    apply integral_nonneg
    intro t₃
    exact mul_nonneg (JointLogSeparation.tripleLogDensity_nonneg _ _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · exact mul_nonneg (secondLogX_pos p hp R X hX j).le
      (zero_le_one.trans (secondLogLabelBound_ge_one p hp B C v₁ v₂ ε₁ ε₂ j))

lemma secondSquarefreeLogNormalizedEnergy_empty
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ)
    (hT : secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j = ∅) :
    secondSquarefreeLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J = 0 := by
  simp only [secondSquarefreeLogNormalizedEnergy, hT, densityChildEnergy, childGeometricMean, childEnergy,
    Finset.sum_empty, Finset.sum_const_zero, Real.sqrt_zero, mul_zero, integral_zero, zero_div]

theorem secondSquarefreeLog_normalized_cost
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X Y M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) :
    (Y*primeProductNorm p R/X^2) *
      densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m
        (secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) V₁ V₂
        (secondLogX p R X j) (secondLogX p R X j) J =
    (Y*‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2*Real.exp 2/X) *
      secondSquarefreeLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J := by
  unfold secondSquarefreeLogNormalizedEnergy
  rw [secondLogX_label_cost]
  have hR := (FirstPassCubeLabels.primeProductNorm_pos p hp R).ne'
  have hc := (zero_lt_one.trans_le (element_norm_ge_one _ (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂))).ne'
  have hcn : ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖ ≠ 0 := by
    intro h; apply hc; rw [h]; norm_num
  field_simp

end SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter crossCoeff)
open SecondPassIntegration (densityChildEnergy)

def firstCoreSquarefreeBudget
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (M ε : ℝ) (tailOrder decayOrder J : ℕ)
    (Y : ℝ) (A₀ B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (χ : RayCharacter) (Ψ : O →* ℂ) (m : O) (r₁ : FirstCoreIndex) (X Z : ℝ) : ℝ :=
  let v := fun i => v₁ i + v₂ i
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  let Ψ' := firstCoreTwist negative χ Ψ r₁
  let m' := m * b0Label p B v ε₁ ε₂
  let c' := c * jLabel p B v ε₁ ε₂
  let X' := X / primeProductNorm p A₀
  let Usupp := X' * Real.exp M
  let K := firstCoreSecondCutoff p A₀ X Y M Z
  let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
  let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
  (primeProductNorm p A₀)⁻¹ *
    (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
        (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2) +
      (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
        ∑ j ∈ secondLogBinBox Usupp Kmax,
        (Y * primeProductNorm p R / X'^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
            Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
        (Cₛ /
          (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
        densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
          (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (secondSquarefreeLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
          (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J) +
      Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder)

theorem firstInputFamilyEnergy_squarefree_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (tailOrder decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧ 0 < Ctail ∧
      ∀ (Y : ℝ), 0 < Y →
      ∀ (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (X Z : ℝ) (Srows : Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ Z →
        (∀ z ∈ Srows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
        (∀ z ∈ Srows, z ≠ 0) →
        firstInputFamilyEnergy p hg F B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative Ψ m
          (fun S => g (columnLog p X S)) V X
          (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) (2*(J+2)) Srows ≤
        (∫ t : ℝ, firstLogDensity 0 t) *
          ∑ a : RayCharacter × RayCharacter, ∑ A₀ ∈ F.powerset,
            ‖crossCoeff a.1 a.2‖ * ∑ r : FirstCoreIndex,
              ‖firstCoreOuter p hg B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative Ψ m A₀ r‖ *
                firstCoreSquarefreeBudget p hp hcop hg windows Cₐ Cₛ Cw Ctail
                  g V negative M ε tailOrder decayOrder J Y A₀ B C D F v₁ v₂ ε₁ ε₂
                  (if negative then a.1 else a.2) Ψ m r X Z := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,hbound⟩ :=
    firstCoreInputRow_squarefree_binned_integrated_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g V negative hU M hM hgM ε hε tailOrder decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro Y hY B C D F v₁ v₂ ε₁ ε₂ Ψ m X Z Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  unfold firstInputFamilyEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro A₀ hA₀
  apply Finset.sum_le_sum
  intro r hr
  have hb := hbound Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ (if negative then a.1 else a.2)
    Ψ m r X Z Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  have he : (∫ t : ℝ, firstLogDensity (2*(J+2)) t *
      ∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative
        (if negative then a.1 else a.2) Ψ m (normalizedColumn p (fun S => g (columnLog p X S)))
        V (columnLog p X) (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) D) r t z‖^2) ≤
      (∫ t : ℝ, firstLogDensity 0 t) *
        firstCoreSquarefreeBudget p hp hcop hg windows Cₐ Cₛ Cw Ctail
          g V negative M ε tailOrder decayOrder J Y A₀ B C D F v₁ v₂ ε₁ ε₂
          (if negative then a.1 else a.2) Ψ m r X Z := by
    simpa only [firstCoreSquarefreeBudget, mul_assoc] using hb
  have hw := mul_le_mul_of_nonneg_left he (mul_nonneg (norm_nonneg (crossCoeff a.1 a.2))
    (norm_nonneg (firstCoreOuter p hg B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative Ψ m A₀ r)))
  convert! hw using 1 <;> (try simp only [Finset.mul_sum]) <;> ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity
  actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)

structure SquarefreeBudgetData where
  windows : Fin 7 → ℝ → ℂ
  arithmetic : ℝ
  smooth : ℝ
  windowBound : ℝ
  tail : ℝ
  arithmetic_pos : 0 < arithmetic
  smooth_nonneg : 0 ≤ smooth
  windowBound_nonneg : 0 ≤ windowBound
  tail_pos : 0 < tail

def firstSquarefreeFamilyBudget {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (data : SquarefreeBudgetData)
    (g V : 𝓢(ℝ,ℂ)) (negative : Bool) (M ε : ℝ) (tailOrder decayOrder J : ℕ)
    (Y : ℝ) (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (Ψ : O →* ℂ) (m : O) (X Z : ℝ) : ℝ :=
  ∑ a : RayCharacter × RayCharacter, ∑ A₀ ∈ F.powerset,
    ‖crossCoeff a.1 a.2‖ * ∑ r : FirstCoreIndex,
      ‖firstCoreOuter p hg B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative Ψ m A₀ r‖ *
        firstCoreSquarefreeBudget p hp hcop hg data.windows data.arithmetic data.smooth data.windowBound data.tail
          g V negative M ε tailOrder decayOrder J Y A₀ B C D F v₁ v₂ ε₁ ε₂
          (if negative then a.1 else a.2) Ψ m r X Z

theorem first_passage_squarefree_child_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F B C D : Finset ι) (hFB : Disjoint F B) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O)
    (hΨ₁ : ∀ a, ‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a, ‖Ψ₂ a‖ ≤ 1)
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ))
    (U₁ U₂ : ℝ → ℂ) (hUc₁ : HasCompactSupport U₁) (hUs₁ : ContDiff ℝ ∞ U₁)
    (hUc₂ : HasCompactSupport U₂) (hUs₂ : ContDiff ℝ ∞ U₂)
    (hU₁ : ∀ t, g₁ t ≠ 0 → U₁ t=1) (hU₂ : ∀ t, g₂ t ≠ 0 → U₂ t=1)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ N₁ N₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ M₁) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ M₂)
    (hV₁ : ∀ t, V₁ t ≠ 0 → |t| ≤ N₁) (hV₂ : ∀ t, V₂ t ≠ 0 → |t| ≤ N₂)
    (ε deltaLoss : ℝ) (hε : 0 < ε) (hδ : 0 < deltaLoss) (tailOrder decayOrder J : ℕ) :
    ∃ (data₁ data₂ : SquarefreeBudgetData) (K₀ : ℝ), 0 ≤ K₀ ∧
      ∀ (lengthScale : ℝ), 0 < lengthScale → ∀ (s : Finset (Ideal O × O)) (T : Finset O)
        (w : Ideal O × O → ℂ) (M Y Z : ℝ),
      0 ≤ M → 0 < Y → 0 ≤ Z →
      (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B (fun i => v₁ i+v₂ i) ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true
          (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S)))
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false
          (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S)))
          c (ConcretePrimeRowBridge.idealGenerator x.1)) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
        (M*K₀*Y^deltaLoss) *
        Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
        Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by
  obtain ⟨windows₁,A₁,S₁,H₁,Q₁,hA₁,hS₁,hH₁,hQ₁,hleft⟩ :=
    firstInputFamilyEnergy_squarefree_transfer p hp hcop hg hinj hc hpr U₁ hUc₁ hUs₁
      g₁ V₁ true hU₁ M₁ hM₁ hg₁ ε hε tailOrder decayOrder J
  obtain ⟨windows₂,A₂,S₂,H₂,Q₂,hA₂,hS₂,hH₂,hQ₂,hright⟩ :=
    firstInputFamilyEnergy_squarefree_transfer p hp hcop hg hinj hc hpr U₂ hUc₂ hUs₂
      g₂ V₂ false hU₂ M₂ hM₂ hg₂ ε hε tailOrder decayOrder J
  let data₁ : SquarefreeBudgetData := ⟨windows₁,A₁,S₁,H₁,Q₁,hA₁,hS₁,hH₁,hQ₁⟩
  let data₂ : SquarefreeBudgetData := ⟨windows₂,A₂,S₂,H₂,Q₂,hA₂,hS₂,hH₂,hQ₂⟩
  obtain ⟨K₀,hK₀,hfirst⟩ := first_passage_transfer_input_family p hp hinj hcop hg hc hpr
    F B hFB (fun i => v₁ i+v₂ i) ε₁ ε₂ hv Ψ₁ Ψ₂ m₁ m₂
    (fun S => g₁ (columnLog p X₁ S)) (fun S => g₂ (columnLog p X₂ S))
    (fun G hG => hΨ₁ _) (fun G hG => hΨ₂ _) W V₁ V₂ X₁ X₂ hX₁ hX₂
    N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  let I₀ : ℝ := ∫ t, firstLogDensity 0 t
  have hI₀ : 0 ≤ I₀ := integral_nonneg (FirstPassCubeLabels.firstLogDensity_nonneg 0)
  refine ⟨data₁,data₂,K₀*I₀,mul_nonneg hK₀ hI₀,?_⟩
  intro lengthScale hL s T w M Y Z hM hY hZ hs hs0 hmap hT0 hT hw
  dsimp only
  have h₁ := hleft Y hY B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z T hv hCB hD hΨ₁ hX₁ hZ hT hT0
  have h₂ := hright Y hY B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z T hv hCB hD hΨ₂ hX₂ hZ hT hT0
  change _ ≤ I₀*firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
    tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z at h₁
  change _ ≤ I₀*firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
    tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z at h₂
  have hb := hfirst lengthScale hL (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) (primeSubsetGenerator_ne_zero _ _)
    s T w M Y hM hY.le hs hs0 hmap hT0 hT hw
  apply hb.trans
  calc
    _ ≤ (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
        (M*K₀*Y^deltaLoss) *
        Real.sqrt (I₀*firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
        Real.sqrt (I₀*firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul hI₀, Real.sqrt_mul hI₀]
      calc
        _ = (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
          (M*K₀*Y^deltaLoss) * (Real.sqrt I₀)^2 *
          Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
            tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
          Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
            tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by ring
        _ = _ := by rw [Real.sq_sqrt hI₀]; ring

end SecondPassArithmetic

namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

theorem actual_first_kernel_full_uniform_envelope
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (_hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
      (X₁ X₂ : ℝ) (_hX₁ : 0 < X₁) (_hX₂ : 0 < X₂),
      ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ∀ C₁ C₂ : Finset ι → ℂ,
        ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h‖ ≤
        (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ d h b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ d h b) := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_envelope W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ X₁ X₂ hX₁ hX₂ lengthScale hL d h hd hh
  have hR : 0 < firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h := by
    unfold firstDualScale
    exact div_pos (mul_pos hL (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hsep, hb⟩ := hs _ hR
  refine ⟨b, hb, ?_⟩
  intro C₁ C₂
  rw [actualFirstKernel_eq_separated p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂
    C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ lengthScale d h b hsep, norm_mul]
  have hi := cube_integral_norm_le_energy p hg F
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
      (normalizedColumn p C₁) V₁ (columnLog p X₁) t d)
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
      (normalizedColumn p C₂) V₂ (columnLog p X₂) t d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ true _ _ _ d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ false _ _ _ d)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ true _ _ _ t d S)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ false _ _ _ t d S)
    h b (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL.le,
    abs_of_nonneg (norm_nonneg _)]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hi (div_nonneg hL.le (norm_nonneg _))

end

open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)

theorem first_passage_full_uniform_transfer
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (_hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (C₁ C₂ : Finset ι → ℂ) (X₁ X₂ : ℝ) (_hX₁ : 0 < X₁) (_hX₂ : 0 < X₂),
      ∀ lengthScale : ℝ, 0 < lengthScale → ∀ c d : O, d ≠ 0 →
      ∀ (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true C₁ c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false C₂ c (ConcretePrimeRowBridge.idealGenerator x.1))
        W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T) *
        Real.sqrt (firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T) := by
  obtain ⟨H, hH, hsep⟩ := actual_first_kernel_full_uniform_envelope
    W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ 0 J
  obtain ⟨K, hK, hpush⟩ := first_column_energy_integral deltaLoss hδ
  refine ⟨H * K, mul_nonneg hH hK.le, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ hv C₁ C₂ X₁ X₂ hX₁ hX₂
  have hsep := hsep p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂ X₁ X₂ hX₁ hX₂
  intro lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  let A₁ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ true C₁ c (ConcretePrimeRowBridge.idealGenerator x.1)
  let A₂ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ false C₂ c (ConcretePrimeRowBridge.idealGenerator x.1)
  let q := lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖
  have hq : 0 ≤ q := div_nonneg hL.le (norm_nonneg _)
  have hfam : ∀ x : Ideal O × O, ∃ b : 𝓢(ℝ, ℂ), x ∈ s →
      (∀ t : ℝ, ‖b t‖ ≤ H * firstLogDensity J t) ∧
      ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
        q * Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 b) := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨b, hb, hk⟩ := hsep lengthScale hL d x.2 hd (hnonzero x hx)
      refine ⟨b, fun _ => ⟨?_, hk (A₁ x) (A₂ x)⟩⟩
      simpa only [pow_zero, one_mul] using hb
    · exact ⟨0, fun hx' => (hx hx').elim⟩
  choose b hb using hfam
  let E₁ := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 (b x)
  let E₂ := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 (b x)
  let O₁ := firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T
  let O₂ := firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T
  let P := M * H * K * Y ^ deltaLoss
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg (mul_nonneg hM hH) hK.le) (Real.rpow_nonneg hY deltaLoss)
  have hE₁ (x) : 0 ≤ E₁ x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ true _ _ _ _ _ _
  have hE₂ (x) : 0 ≤ E₂ x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ false _ _ _ _ _ _
  have hdom : ∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t := fun x hx => (hb x hx).1
  have hsum₁ : (∑ x ∈ s, ‖w x‖ * E₁ x) ≤ P * O₁ :=
    hpush p hp hinj hcop hg hc F B v ε₁ ε₂ hv true C₁ V₁ X₁ c d s T w b J M H Y
      hM hH hY hs hmap hT hnorm hw hdom
  have hsum₂ : (∑ x ∈ s, ‖w x‖ * E₂ x) ≤ P * O₂ :=
    hpush p hp hinj hcop hg hc F B v ε₁ ε₂ hv false C₂ V₂ X₂ c d s T w b J M H Y
      hM hH hY hs hmap hT hnorm hw hdom
  have hterm (x) : ‖w x‖ * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) =
      Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x) := by
    rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul (norm_nonneg _)]
    calc
      _ = (Real.sqrt ‖w x‖) ^ 2 * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) := by
        rw [Real.sq_sqrt (norm_nonneg _)]
      _ = _ := by ring
  calc
    _ ≤ ∑ x ∈ s, ‖w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ s, q * (Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, ← hterm]
      calc
        _ ≤ ‖w x‖ * (q * Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) :=
          mul_le_mul_of_nonneg_left (hb x hx).2 (norm_nonneg _)
        _ = _ := by ring
    _ = q * (∑ x ∈ s, Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ q * (Real.sqrt (∑ x ∈ s, ‖w x‖ * E₁ x) * Real.sqrt (∑ x ∈ s, ‖w x‖ * E₂ x)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le s
        (fun x => mul_nonneg (norm_nonneg _) (hE₁ x))
        (fun x => mul_nonneg (norm_nonneg _) (hE₂ x))) hq
    _ ≤ q * (Real.sqrt (P * O₁) * Real.sqrt (P * O₂)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hsum₁) (Real.sqrt_le_sqrt hsum₂)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hq
    _ = _ := by
      rw [Real.sqrt_mul hP, Real.sqrt_mul hP]
      calc
        _ = q * (Real.sqrt P)^2 * Real.sqrt O₁ * Real.sqrt O₂ := by ring
        _ = _ := by rw [Real.sq_sqrt hP]; dsimp only [P]; ring

end FirstPassCubeLabels
end

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem first_passage_full_uniform_input_family
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (_hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (H₁ H₂ : Finset ι → ℂ)
      (_hΨ₁ : ∀ D ∈ F.powerset, ‖Ψ₁ (∏ i ∈ D, p i)‖ ≤ 1)
      (_hΨ₂ : ∀ D ∈ F.powerset, ‖Ψ₂ (∏ i ∈ D, p i)‖ ≤ 1)
      (X₁ X₂ : ℝ) (_hX₁ : 0 < X₁) (_hX₂ : 0 < X₂),
      ∀ lengthScale : ℝ, 0 < lengthScale → ∀ c d : O, d ≠ 0 →
      ∀ (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true (multiplicativeCoreColumn p Ψ₁ m₁ H₁)
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false (multiplicativeCoreColumn p Ψ₂ m₂ H₂)
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
        Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by
  obtain ⟨K, hK, hb⟩ := FirstPassCubeLabels.first_passage_full_uniform_transfer
    W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨(32 * 512) * K, mul_nonneg (by norm_num) hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ hv Ψ₁ Ψ₂ m₁ m₂ H₁ H₂ hΨ₁ hΨ₂ X₁ X₂ hX₁ hX₂
  have hb := hb p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂ hv
    (multiplicativeCoreColumn p Ψ₁ m₁ H₁) (multiplicativeCoreColumn p Ψ₂ m₂ H₂)
    X₁ X₂ hX₁ hX₂
  intro lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  have hf := hb lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  have h₁ := firstOutputEnergy_le_input_family p hp hcop hg hc hpr F B v ε₁ ε₂ true
    Ψ₁ m₁ H₁ V₁ X₁ c d J T hΨ₁
  have h₂ := firstOutputEnergy_le_input_family p hp hcop hg hc hpr F B v ε₁ ε₂ false
    Ψ₂ m₂ H₂ V₂ X₂ c d J T hΨ₂
  have hq : 0 ≤ lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ :=
    div_nonneg hL.le (norm_nonneg _)
  have hfactor : 0 ≤ M * K * Y ^ deltaLoss :=
    mul_nonneg (mul_nonneg hM hK) (Real.rpow_nonneg hY deltaLoss)
  calc
    _ ≤ (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (FirstPassCubeLabels.firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true
          (multiplicativeCoreColumn p Ψ₁ m₁ H₁) V₁ X₁ c d J T) *
        Real.sqrt (FirstPassCubeLabels.firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false
          (multiplicativeCoreColumn p Ψ₂ m₂ H₂) V₂ X₂ c d J T) := hf
    _ ≤ (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt ((32 * 512) * firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
        Real.sqrt ((32 * 512) * firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32 * 512),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32 * 512)]
      calc
        _ = (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
            (Real.sqrt (32 * 512)) ^ 2 *
            Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
            Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 32 * 512)]; ring

end SecondPassArithmetic

end

end OAI

end


