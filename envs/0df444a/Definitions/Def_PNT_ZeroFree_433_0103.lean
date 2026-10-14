-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0103
-- name    : PNT_ZeroFree_433_0103
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:46:37.322266+00:00
-- url     : https://prove2.me/theorems/469286c0-6ea8-430f-80e3-7697301afdea
-- title:
--   Zero-free region foundations: CubicSieve.FirstCoreCutoff [0103]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.FirstCoreCutoff
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/FirstCoreCutoff.lean#L82-L626

import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0101

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/FirstCoreCutoff.lean#L82-L626
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.FirstCoreCutoff
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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def firstCoreSecondCutoff {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : Finset ι) (X Y A H : ℝ) (G E : Finset ι) : Finset O :=
  secondFrequencyCutoff
    (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
      (((X / primeProductNorm p D) / primeProductNorm p G) * Real.exp A)^2)) H

theorem firstCoreSecondCutoff_zero {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : Finset ι) (X Y A H : ℝ) (G E : Finset ι) :
    (0 : O) ∈ firstCoreSecondCutoff p D X Y A H G E :=
  secondFrequencyCutoff_zero _ _

theorem firstCoreSecondCutoff_uniform {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t A : ℝ)
    (hgA : ∀ s, g s ≠ 0 → |s| ≤ A)
    (D G E S T : Finset ι) (hGS : Disjoint G S) (hGT : Disjoint G T) (hST : Disjoint S T)
    (X Y H : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (hS : normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A)) (G∪S) ≠ 0)
    (hT : normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A)) (G∪T) ≠ 0)
    (k : O) (hk : k ∉ firstCoreSecondCutoff p D X Y A H G E) :
    H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
      ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2 := by
  have hXD : 0 < X / primeProductNorm p D := div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp D)
  have hXG : 0 < (X / primeProductNorm p D) / primeProductNorm p G :=
    div_pos hXD (FirstPassCubeLabels.primeProductNorm_pos p hp G)
  have hSup (S : Finset ι) (hGS : Disjoint G S)
      (hS : normalizedColumn p (fun A => firstCoreModeProfile g V negative t
        (columnLog p (X / primeProductNorm p D) A)) (G∪S) ≠ 0) :
      columnLog p ((X / primeProductNorm p D) / primeProductNorm p G) S ≤ A := by
    have hs : firstCoreModeProfile g V negative t (columnLog p (X / primeProductNorm p D) (G∪S)) ≠ 0 := by
      intro hz
      apply hS
      simp only [normalizedColumn, hz, zero_div]
    have ha := hgA _ (firstCoreModeProfile_support g V negative t _ hs).1
    rw [SecondPassIntegration.columnLog_extract_common p hp G S hGS _ hXD] at ha
    exact le_trans (le_abs_self _) ha
  exact secondFrequencyCutoff_uniform p hp ((X / primeProductNorm p D) / primeProductNorm p G)
    Y A H hXG hY (primeSubsetGenerator (fun i => Ideal.span {p i}) E)
    (primeSubsetGenerator_ne_zero _ _) S T hST (hSup S hGS hS) (hSup T hGT hT) k hk

theorem first_second_normalization_factor {ι : Type*}
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (D : Finset ι) (X Y R : ℝ) (hX : 0 < X) :
    (primeProductNorm p D)⁻¹ * (Y * R / (X / primeProductNorm p D)^2) =
      Y * primeProductNorm p D * R / X^2 := by
  have hn := (FirstPassCubeLabels.primeProductNorm_pos p hp D).ne'
  have hx := hX.ne'
  field_simp

end
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (halfNormalizationCLM halfNormalizationCLM_apply halfNormalization_twist
  frequencyTwist frequencyTwist_apply outerWindow tripleCoefficient)
open SecondPassIntegration (childGeometricMean)

theorem normalized_twisted_second_sector_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ t, g₁ t ≠ 0 → U t = 1)
    (hU₂ : ∀ t, g₂ t ≠ 0 → U t = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ D₀ E₀ V₀ X₀ K₀ Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X₀ → 0 < K₀ → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ t₁ t₂ t₃ : ℝ,
        (1+Y*K₀/(D₀*E₀^2*V₀^2*X₀^2))^decayOrder * ‖(𝓕 (frequencyTwist A₁ (-θ₁))) t₁*(𝓕 (frequencyTwist A₂ θ₂)) t₂*b t₃‖ ≤
          Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*firstLogDensity J t₁*firstLogDensity J t₂*firstLogDensity J t₃) ∧
      ∀ (B C D R F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (s : Finset (SecondExpansionData ι))
        (T : Finset (Ideal O × O)) (X lengthScale : ℝ),
        s ⊆ secondExpansionSector F (fun G E => (K G E).erase 0) R →
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ lengthScale →
        (∀ x ∈ s, |secondSectorZ p
          (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
            (expansionSupportData C D x)) X₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
          secondSupportRow p (expansionSupportData C D x)) ∈ T) →
        (∀ t ∈ T, t.1 ≠ ⊥) → (∀ t ∈ T, (Ideal.absNorm t.1 : ℝ) ≤ lengthScale) →
        ‖secondExpansionSource p hp hcop hg F Ψ m
          (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
            jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) z s
          (fun S => normalizedColumn p (fun A => (frequencyTwist g₁ θ₁) (columnLog p X A)) S)
          (fun S => normalizedColumn p (fun A => (frequencyTwist g₂ θ₂) (columnLog p X A)) S) W Y‖ ≤
        (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
            X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 (frequencyTwist A₁ (-θ₁))) (𝓕 (frequencyTwist A₂ θ₂)) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
              (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
              (windows 5) (windows 6) X₀ X₀ (t₁,t₂,t₃)) := by
  have hn₁ : ∀ t, halfNormalizationCLM U g₁ t ≠ 0 → |t| ≤ A := by
    intro t ht
    apply hg₁ t
    intro h
    apply ht
    rw [halfNormalizationCLM_apply U hUc hUs, h, mul_zero]
  have hn₂ : ∀ t, halfNormalizationCLM U g₂ t ≠ 0 → |t| ≤ A := by
    intro t ht
    apply hg₂ t
    intro h
    apply ht
    rw [halfNormalizationCLM_apply U hUc hUs, h, mul_zero]
  obtain ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hW,htrans⟩ :=
    actual_raw_twisted_sector_transfer p hp hcop hg hinj
      (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A H hA hH hn₁ hn₂ ε hε decayOrder J
  refine ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  obtain ⟨b,hb⟩ := htrans D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  refine ⟨b,?_⟩
  intro θ₁ θ₂
  obtain ⟨hb',hbound⟩ := hb θ₁ θ₂
  refine ⟨hb',?_⟩
  intro B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K s T X lengthScale hs hv hCB hD hΨ hX hL hz hud hue huv hkap hmap hT hnorm
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
    jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  have hsector : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x (hs hx)
  have hU₁' : ∀ s, frequencyTwist g₁ θ₁ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₁ s
    intro hz
    apply hs
    simp only [frequencyTwist_apply, hz, mul_zero]
  have hU₂' : ∀ s, frequencyTwist g₂ θ₂ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₂ s
    intro hz
    apply hs
    simp only [frequencyTwist_apply, hz, mul_zero]
  rw [secondExpansionSource_eq_raw_variable_sector p hp hcop hg hinj hpr B C D F v₁ v₂ ε₁ ε₂
    Ψ m r z s hsector X Y hX U hUc hUs (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W hU₁' hU₂']
  simp only [halfNormalization_twist U hUc hUs]
  have hrow : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact secondExpansionSector_frequency_ne_zero F K R x (hs hx)
  have liftP : ∀ P : SecondSupportData ι → Prop,
      (∀ x ∈ s, P (expansionSupportData C D x)) →
      ∀ y ∈ s.image (expansionSupportData C D), P y := by
    intro P hP y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hP x hx
  have hxscale : ∀ y : SecondSupportData ι, 0 < secondExpansionScale p X r y := by
    intro y
    exact div_pos hX (mul_pos
      (SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _))
      (SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _)))
  have hw : ∀ y ∈ s.image (expansionSupportData C D),
      ‖secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y) y *
        (secondExpansionScale p X r y : ℂ)⁻¹‖ *
      ‖outerWindow windows (secondSectorZ p (secondExpansionScale p X r y) X₀ y)
        (secondSectorUd p D₀ y) (secondSectorUe p E₀ y) (secondSectorUv p V₀ y)
        (secondSectorKap p K₀ y)‖ ≤
      Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ * Cw := by
    intro y hy
    exact mul_le_mul (secondNormalizedPushWeight_norm_le p hp hcop hg hinj hc C D Ψ m c d r z
      X Y hX hY.le s hsector (fun x hx => hΨ _) (fun x hx => hΨ _) y hy)
      (hW _ _ _ _ _) (norm_nonneg _) (by positivity)
  exact hbound B v₁ v₂ ε₁ ε₂ (s.image (expansionSupportData C D)) T
    (secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y))
    (Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ * Cw) lengthScale F
    (secondRayMinus Ψ z) (secondRayPlus Ψ z) m r (secondExpansionScale p X r)
    hv (liftP _ (fun x hx => hCB)) (liftP _ (fun x hx => hD))
    (fun y hy => hxscale y) (liftP _ hrow) (liftP _ hz) (liftP _ hud)
    (liftP _ hue) (liftP _ huv) (liftP _ hkap) (by positivity) hL
    (liftP _ hmap) hT hnorm hw

end

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (halfNormalizationCLM halfNormalizationCLM_apply halfNormalization_twist
  frequencyTwist frequencyTwist_apply outerWindow tripleCoefficient)
open SecondPassIntegration (childGeometricMean densityChildEnergy child_coefficient_density_bound)

theorem normalized_twisted_second_sector_density_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ t, g₁ t ≠ 0 → U t = 1)
    (hU₂ : ∀ t, g₂ t ≠ 0 → U t = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ D₀ E₀ V₀ X₀ K₀ Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X₀ → 0 < K₀ → 0 < Y →
      ∀ θ₁ θ₂ : ℝ,
      ∀ (B C D R F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (s : Finset (SecondExpansionData ι))
        (T : Finset (Ideal O × O)) (X lengthScale : ℝ),
        s ⊆ secondExpansionSector F (fun G E => (K G E).erase 0) R →
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ lengthScale →
        (∀ x ∈ s, |secondSectorZ p
          (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
            (expansionSupportData C D x)) X₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
          secondSupportRow p (expansionSupportData C D x)) ∈ T) →
        (∀ t ∈ T, t.1 ≠ ⊥) → (∀ t ∈ T, (Ideal.absNorm t.1 : ℝ) ≤ lengthScale) →
        ‖secondExpansionSource p hp hcop hg F Ψ m
          (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
            jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) z s
          (fun S => normalizedColumn p (fun A => (frequencyTwist g₁ θ₁) (columnLog p X A)) S)
          (fun S => normalizedColumn p (fun A => (frequencyTwist g₂ θ₂) (columnLog p X A)) S) W Y‖ ≤
        (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
            X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
        (Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2) /
          (1+Y*K₀/(D₀*E₀^2*V₀^2*X₀^2))^decayOrder) *
        densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
          (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
          (windows 5) (windows 6) X₀ X₀ J := by
  obtain ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,htrans⟩ :=
    normalized_twisted_second_sector_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g₁ g₂ W hU₁ hU₂ A H hA hH hg₁ hg₂ ε hε decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY θ₁ θ₂
  obtain ⟨b,hb⟩ := htrans D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  obtain ⟨hpoint,hbound⟩ := hb θ₁ θ₂
  intro B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K s T X lengthScale hs hv hCB hD hΨ hX hL
    hz hud hue huv hkap hmap hT hnorm
  have hh := hbound B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K s T X lengthScale hs hv hCB hD hΨ hX hL
    hz hud hue huv hkap hmap hT hnorm
  let scale := (1+Y*K₀/(D₀*E₀^2*V₀^2*X₀^2))^decayOrder
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hd := child_coefficient_density_bound p hp hcop hg F
    (secondRayMinus Ψ z) (secondRayPlus Ψ z)
    (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
    (windows 5) (windows 6) X₀ X₀
    (𝓕 (frequencyTwist A₁ (-θ₁))) (𝓕 (frequencyTwist A₂ θ₂)) b J scale
    (Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)) hpoint
  have hi := (le_div_iff₀' hscale).2 hd
  apply hh.trans
  calc
    _ ≤ (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
            X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
        ((Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2) *
          densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
            (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
            (windows 5) (windows 6) X₀ X₀ J) / scale) := by
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by dsimp [scale]; ring

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (tripleCoefficient frequencyTwist frequencyTwist_apply)
open SecondPassIntegration (childGeometricMean densityChildEnergy)

theorem secondInputCoefficient_frequencyTwist_norm {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (Ψ : O →* ℂ) (m c d : O)
    (g : 𝓢(ℝ, ℂ)) (θ X : ℝ) (G : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d
      (fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S) G‖ =
    ‖secondInputCoefficient p hg Ψ m c d
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) G‖ := by
  simp only [secondInputCoefficient, normalizedColumn, frequencyTwist_apply, norm_mul, norm_div,
    FourierBridge.logPhase_norm, one_mul]

theorem normalized_truncated_second_density_transfer
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ, ℂ)) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ (D₀ E₀ V₀ X₀ K₀ : Finset ι → κ → ℝ) (Y : ℝ),
        (∀ R j, 0 < D₀ R j) → (∀ R j, 0 < E₀ R j) → (∀ R j, 0 < V₀ R j) →
        (∀ R j, 0 < X₀ R j) → (∀ R j, 0 < K₀ R j) → 0 < Y → ∀ θ : ℝ,
      ∀ (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (X : ℝ) (K : Finset ι → Finset ι → Finset O)
        (label : Finset ι → SecondExpansionData ι → κ)
        (T : Finset ι → κ → Finset (Ideal O × O)) (lengthScale : Finset ι → κ → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X →
        (∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) →
        (∀ R ∈ F.powerset, ∀ j, 0 ≤ lengthScale R j) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorZ p
            (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
              (expansionSupportData C D x)) (X₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorUd p (D₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorUe p (E₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorUv p (V₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorKap p (K₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
            secondSupportRow p (expansionSupportData C D x)) ∈ T R j) →
        (∀ R ∈ F.powerset, ∀ j, ∀ t ∈ T R j, t.1 ≠ ⊥) →
        (∀ R ∈ F.powerset, ∀ j, ∀ t ∈ T R j, (Ideal.absNorm t.1 : ℝ) ≤ lengthScale R j) →
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
          jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Hcol := fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S
        ‖truncatedSecondSource p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
          |Y| * ‖paperRadialFourier W 0‖ *
            (∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d
              (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) G‖ ^ 2) +
          ∑ z : SecondRayIndex, ∑ R ∈ F.powerset, ∑ j : κ,
            (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
                X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
              (lengthScale R j * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
            (Cₛ*(1+‖θ‖)^(J+2)*(1+‖θ‖)^(J+2) /
              (1+Y*K₀ R j/(D₀ R j*(E₀ R j)^2*(V₀ R j)^2*(X₀ R j)^2))^decayOrder) *
            densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
              (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) (T R j)
              (windows 5) (windows 6) (X₀ R j) (X₀ R j) J := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hbound⟩ :=
    normalized_twisted_second_sector_density_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g g W hU hU A H hA hH hgA hgA ε hε decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY θ
    B C D F v₁ v₂ ε₁ ε₂ Ψ m X K label T lengthScale hv hCB hD hΨ hX hzero hL
    hz hud hue huv hkap hmap hT hnorm
  dsimp only
  apply (truncatedSecondSource_norm_le_zero_add_dyadic p hp hcop hg hinj hc hpr F Ψ m
    _ _ _ W Y K label).trans
  apply add_le_add
  · have hd := truncatedSecondZero_norm_le p hg hinj F Ψ m
      (primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) D)
      (fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S) W Y K hzero
    simpa only [secondInputCoefficient_frequencyTwist_norm] using hd
  · apply Finset.sum_le_sum
    intro z hz'
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    exact hbound (D₀ R j) (E₀ R j) (V₀ R j) (X₀ R j) (K₀ R j) Y
      (hD₀ R j) (hE₀ R j) (hV₀ R j) (hX₀ R j) (hK₀ R j) hY θ θ
      B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K
      (secondDyadicSector F K R label j) (T R j) X (lengthScale R j)
      (secondDyadicSector_subset F K R label j) hv hCB hD hΨ hX (hL R hR j)
      (hz R hR j) (hud R hR j) (hue R hR j) (huv R hR j) (hkap R hR j)
      (hmap R hR j) (hT R hR j) (hnorm R hR j)

end

open JointLogSeparation (frequencyTwist frequencyTwist_apply)

theorem firstCoreBaseProfile_frequencyTwist (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (θ : ℝ) :
    firstCoreBaseProfile (frequencyTwist g θ) V negative =
      frequencyTwist (firstCoreBaseProfile g V negative) θ := by
  ext s
  simp only [firstCoreBaseProfile_apply, frequencyTwist_apply]
  ring

theorem firstCoreModeProfile_frequencyTwist (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (θ t : ℝ) :
    firstCoreModeProfile (frequencyTwist g θ) V negative t =
      frequencyTwist (firstCoreBaseProfile g V negative) (θ + firstCoreModeHeight negative t) := by
  rw [firstCoreModeProfile, firstCoreBaseProfile_frequencyTwist,
    JointLogSeparation.frequencyTwist_twice]

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

def HasSieveExponent (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    sieveNorm M N ≤ C * (M * N) ^ ε * (M + N ^ α)

theorem hasSieveExponent_two : HasSieveExponent 2 := by
  intro ε hε
  let C := QuadraticInitialBound.initialSieveConstant
  have hC : 0 < C := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨4 * C, by positivity, ?_⟩
  intro M N hM hN
  have hc : (⌈N⌉₊ : ℝ) ≤ 2 * N := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ N by linarith)
    linarith
  have hc2 : (⌈N⌉₊ : ℝ) ^ 2 ≤ 4 * N ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) ⌈N⌉₊]
  have hmn : 1 ≤ M * N := by nlinarith [mul_le_mul hM hN (by norm_num : (0 : ℝ) ≤ 1) (show 0 ≤ M by linarith)]
  have he : 1 ≤ (M * N) ^ ε := Real.one_le_rpow hmn hε.le
  rw [Real.rpow_two]
  calc
    _ ≤ C * (M + (⌈N⌉₊ : ℝ) ^ 2) := sieveNorm_initial M N hM hN
    _ ≤ 4 * C * (M + N ^ 2) := by nlinarith
    _ ≤ (4 * C) * (M * N) ^ ε * (M + N ^ 2) := by
      nlinarith [show 0 ≤ (4 * C) * (M + N ^ 2) by positivity]

theorem HasSieveExponent.reverse {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C * (M * N) ^ ε * (N + M ^ α) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨262144 * C, by positivity, ?_⟩
  intro M N hM hN
  calc
    _ ≤ 262144 * sieveNorm N M := sieveNorm_reverse_le M N
    _ ≤ 262144 * (C * (N * M) ^ ε * (N + M ^ α)) :=
      mul_le_mul_of_nonneg_left (hb N M hN hM) (by norm_num)
    _ = _ := by rw [mul_comm N M]; ring

theorem sqrt_divisor_sieve_pair_le (M N D₁ D₂ Q C : ℝ)
    (hN : 0 ≤ N) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (h₁ : sieveNorm M (N / D₁) ≤ C * (N / D₁ + Q))
    (h₂ : sieveNorm M (N / D₂) ≤ C * (N / D₂ + Q)) :
    Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) ≤
      C * (N + Q * (D₁ * D₂)) := by
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hD₁le : D₁ ≤ D₁ * D₂ := by nlinarith
  have hD₂le : D₂ ≤ D₁ * D₂ := by nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ D₁ * D₂ * (C * (N / D₁ + Q)) * (C * (N / D₂ + Q)) := by
      gcongr
      exact sieveNorm_nonneg _ _
    _ = C ^ 2 * ((N + Q * D₁) * (N + Q * D₂)) := by field_simp
    _ ≤ C ^ 2 * ((N + Q * (D₁ * D₂)) * (N + Q * (D₁ * D₂))) := by gcongr
    _ = _ := by ring

theorem HasSieveExponent.divisor_pair {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N D₁ D₂ : ℝ,
      1 ≤ M → 1 ≤ N → 1 ≤ D₁ → 1 ≤ D₂ → D₁ ≤ N → D₂ ≤ N →
      Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) ≤
        C * (M * N) ^ ε * (N + M ^ α * (D₁ * D₂)) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h.reverse ε hε
  refine ⟨C, hC, ?_⟩
  intro M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N
  have hbound (D : ℝ) (hD : 1 ≤ D) (hDN : D ≤ N) :
      sieveNorm M (N / D) ≤ (C * (M * N) ^ ε) * (N / D + M ^ α) := by
    have hD0 : 0 < D := by linarith
    have hND : 1 ≤ N / D := (le_div_iff₀ hD0).mpr (by simpa using hDN)
    apply (hb M (N / D) hM hND).trans
    have hprod : M * (N / D) ≤ M * N := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact div_le_self (by linarith) hD
    gcongr
  exact sqrt_divisor_sieve_pair_le M N D₁ D₂ (M ^ α) (C * (M * N) ^ ε)
    (by linarith) hD₁ hD₂ (Real.rpow_nonneg (by linarith) _) (by positivity)
    (hbound D₁ hD₁ hD₁N) (hbound D₂ hD₂ hD₂N)

open IdealCoprimeSieveOperator DivisorBlockCauchy

variable {n p : Type*} [Fintype n] [Fintype p]

def divisorEnergyFactor (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  256 * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2 *
    Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ k, ‖b k‖ ^ 2)

theorem divisorEnergyFactor_nonneg (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) (b : p → ℂ) :
    0 ≤ divisorEnergyFactor ε hε N a b := by
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  unfold divisorEnergyFactor
  positivity

theorem divisorBlockCost_sqrt (ε : ℝ) (hε : 0 < ε) (D₁ D₂ M N : ℝ)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (a : n → ℂ) (b : p → ℂ) :
    Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) =
      divisorEnergyFactor ε hε N a b *
        Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) := by
  have hA := sieveNorm_nonneg M (N / D₁)
  have hB := sieveNorm_nonneg M (N / D₂)
  have hp : 0 ≤ D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) := by positivity
  have ha : 0 ≤ ∑ j, ‖a j‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : 0 ≤ ∑ k, ‖b k‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : 0 ≤ divisorBlockCost ε hε D₁ D₂ M N a b := by
    unfold divisorBlockCost
    positivity
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (divisorEnergyFactor_nonneg ε hε N a b) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt hc]
  simp only [divisorEnergyFactor, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hp]
  unfold divisorBlockCost
  ring

theorem HasSieveExponent.divisor_cost {α : ℝ} (h : HasSieveExponent α) :
    ∀ deltaLoss : ℝ, 0 < deltaLoss → ∃ C : ℝ, 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (M N D₁ D₂ : ℝ),
        1 ≤ M → 1 ≤ N → 1 ≤ D₁ → 1 ≤ D₂ → D₁ ≤ N → D₂ ≤ N →
        ∀ (a : n → ℂ) (b : p → ℂ),
        Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) ≤
          divisorEnergyFactor ε hε N a b * (C * (M * N) ^ deltaLoss * (N + M ^ α * (D₁ * D₂))) := by
  intro deltaLoss hδ
  obtain ⟨C, hC, hc⟩ := h.divisor_pair deltaLoss hδ
  refine ⟨C, hC, ?_⟩
  intro ε hε M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N a b
  rw [divisorBlockCost_sqrt ε hε D₁ D₂ M N (by linarith) (by linarith) a b]
  exact mul_le_mul_of_nonneg_left (hc M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N)
    (divisorEnergyFactor_nonneg ε hε N a b)

end CanonicalQuadraticSieve

end

end OAI

end


