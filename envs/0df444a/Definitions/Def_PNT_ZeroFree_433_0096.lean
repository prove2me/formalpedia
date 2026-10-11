-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0096
-- name    : PNT_ZeroFree_433_0096
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:30:57.926538+00:00
-- url     : https://prove2.me/theorems/d0a88812-f654-48e0-a16c-a393d97746e0
-- title:
--   Zero-free region foundations: CubicSieve.FrequencyCutoffs [0096]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.FrequencyCutoffs
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/FrequencyCutoffs.lean#L81-L609

import Definitions.Def_PNT_ZeroFree_433_0095

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/FrequencyCutoffs.lean#L81-L609
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.FrequencyCutoffs
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
open FirstPassCubeLabels (columnLog primeProductNorm primeProductNorm_pos)
open ConcreteTraceCRT (eisEmbedding)

theorem columnLog_norm_upper {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (X M : ℝ) (hX : 0 < X) (S : Finset ι) (hS : columnLog p X S ≤ M) :
    primeProductNorm p S ≤ X * Real.exp M := by
  have he := Real.exp_le_exp.mpr hS
  rw [columnLog, Real.exp_log (div_pos (primeProductNorm_pos p hp S) hX)] at he
  exact (div_le_iff₀ hX).mp he |>.trans_eq (mul_comm _ _)

def secondFrequencyCutoff (scale H : ℝ) : Finset O :=
  ShortDraftLatticeCount.rowNormBall ⌈H/scale⌉₊

theorem mem_secondFrequencyCutoff (scale H : ℝ) (k : O)
    (hk : ‖eisEmbedding k‖^2 ≤ H/scale) : k ∈ secondFrequencyCutoff scale H := by
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hk
  exact_mod_cast hk.trans (Nat.le_ceil (H/scale))

theorem secondFrequencyCutoff_zero (scale H : ℝ) : (0 : O) ∈ secondFrequencyCutoff scale H := by
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  simp

theorem outside_secondFrequencyCutoff (scale H : ℝ) (hs : 0 < scale) (k : O)
    (hk : k ∉ secondFrequencyCutoff scale H) : H < scale * ‖eisEmbedding k‖^2 := by
  have hnorm : H/scale < ‖eisEmbedding k‖^2 := lt_of_not_ge (fun h => hk (mem_secondFrequencyCutoff scale H k h))
  have h := (div_lt_iff₀ hs).mp hnorm
  simpa only [mul_comm] using h

theorem active_norm_sq_disjoint {ι : Type*} [DecidableEq ι] (p : ι → O)
    (S T : Finset ι) (hd : Disjoint S T) :
    ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 =
      primeProductNorm p S * primeProductNorm p T := by
  rw [Finset.prod_coe_sort]
  simp only [activeSupport, Finset.sdiff_eq_self_of_disjoint hd,
    Finset.sdiff_eq_self_of_disjoint hd.symm, Finset.prod_union hd.symm, map_mul, norm_mul, mul_pow]
  simp only [primeProductNorm]
  ring

theorem secondFrequencyCutoff_uniform {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (X Y M H : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (e : O) (he : e ≠ 0)
    (S T : Finset ι) (hd : Disjoint S T)
    (hS : columnLog p X S ≤ M) (hT : columnLog p X T ≤ M) (k : O)
    (hk : k ∉ secondFrequencyCutoff (Y/(‖eisEmbedding e‖^2*(X*Real.exp M)^2)) H) :
    H ≤ (Y/(‖eisEmbedding e‖^2*‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) *
      ‖eisEmbedding k‖^2 := by
  have hNe : 0 < ‖eisEmbedding e‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero he))
  have hU : 0 < X*Real.exp M := mul_pos hX (Real.exp_pos M)
  have hslow : 0 < Y/(‖eisEmbedding e‖^2*(X*Real.exp M)^2) :=
    div_pos hY (mul_pos hNe (sq_pos_of_pos hU))
  have hbS := columnLog_norm_upper p hp X M hX S hS
  have hbT := columnLog_norm_upper p hp X M hX T hT
  have hprod : primeProductNorm p S * primeProductNorm p T ≤ (X*Real.exp M)^2 := by
    simpa only [pow_two] using mul_le_mul hbS hbT (primeProductNorm_pos p hp T).le hU.le
  have hscale : Y/(‖eisEmbedding e‖^2*(X*Real.exp M)^2) ≤
      Y/(‖eisEmbedding e‖^2*‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2) := by
    rw [active_norm_sq_disjoint p S T hd]
    exact div_le_div_of_nonneg_left hY.le
      (mul_pos hNe (mul_pos (primeProductNorm_pos p hp S) (primeProductNorm_pos p hp T)))
      (mul_le_mul_of_nonneg_left hprod hNe.le)
  exact (outside_secondFrequencyCutoff _ H hslow k hk).le.trans
    (mul_le_mul_of_nonneg_right hscale (sq_nonneg _))

end
section

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def truncatedSecondZero (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (K : Finset ι → Finset ι → Finset O) : ℂ :=
  (Y : ℂ) * paperRadialFourier W 0 *
    ∑ G ∈ F.powerset,
      (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) * star (H G) * H G *
      ∑ E : G.powerset, if 0 ∈ K G E.val then
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)
        else 0

theorem truncatedSecondSource_eq_nonzero_add_zero
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      truncatedSecondSource p hp hg hinj F Ψ m c d H W Y (fun G E => (K G E).erase 0) +
        truncatedSecondZero p hg F Ψ m c d H W Y K := by
  unfold truncatedSecondSource truncatedSecondZero
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro G hG
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  by_cases h0 : 0 ∈ K G E.val
  · rw [← Finset.sum_erase_add _ _ h0]
    congr 1
    simp only [if_pos h0, secondFrequencyKernel_zero, Finset.union_empty,
      secondSourceCommonCoefficient]
    ring
  · simp only [Finset.erase_eq_of_notMem h0, if_neg h0, mul_zero, add_zero]

theorem secondExpansionSector_frequency_ne_zero
    (F : Finset ι) (K : Finset ι → Finset ι → Finset O) (R : Finset ι)
    (x : SecondExpansionData ι)
    (hx : x ∈ secondExpansionSector F (fun G E => (K G E).erase 0) R) :
    x.frequency ≠ 0 := by
  have h := (mem_secondExpansionPool F (fun G E => (K G E).erase 0) x).mp
    (Finset.mem_filter.mp hx).1
  exact (Finset.mem_erase.mp h.2.2.2).1

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (halfNormalizationCLM halfNormalizationCLM_apply outerWindow tripleCoefficient)
open SecondPassIntegration (childGeometricMean)

theorem normalized_second_sector_transfer {ι : Type*} [DecidableEq ι]
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
      ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ,
        (1+Y*K₀/(D₀*E₀^2*V₀^2*X₀^2))^decayOrder * ‖(𝓕 A₁) t₁*(𝓕 A₂) t₂*b t₃‖ ≤
          Cₛ*firstLogDensity J t₁*firstLogDensity J t₂*firstLogDensity J t₃) ∧
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
          (fun S => normalizedColumn p (fun A => g₁ (columnLog p X A)) S)
          (fun S => normalizedColumn p (fun A => g₂ (columnLog p X A)) S) W Y‖ ≤
        (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
            X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
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
    actual_raw_variable_sector_transfer p hp hcop hg hinj
      (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A H hA hH hn₁ hn₂ ε hε decayOrder J
  refine ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  obtain ⟨b,hb,hbound⟩ := htrans D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  refine ⟨b,hb,?_⟩
  intro B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K s T X lengthScale hs hv hCB hD hΨ hX hL hz hud hue huv hkap hmap hT hnorm
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
    jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  have hsector : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x (hs hx)
  rw [secondExpansionSource_eq_raw_variable_sector p hp hcop hg hinj hpr B C D F v₁ v₂ ε₁ ε₂
    Ψ m r z s hsector X Y hX U hUc hUs g₁ g₂ W hU₁ hU₂]
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

end SecondPassArithmetic

open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)

def ramifiedIdeal : Ideal O := Ideal.span {lambda}

lemma ramifiedIdeal_prime : Prime ramifiedIdeal := by
  exact Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr residue_lambda_prime.ne_zero)
    ((Ideal.span_singleton_prime residue_lambda_prime.ne_zero).mpr residue_lambda_prime)

lemma goodIdeal_iff_not_ramified (I : Ideal O) :
    primaryGenerator I ≠ 0 ↔ ¬ ramifiedIdeal ∣ I := by
  rw [← ConcretePrimeRowBridge.span_idealGenerator I,
    PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff,
    Ideal.dvd_iff_le,ramifiedIdeal,Ideal.span_singleton_le_span_singleton]

lemma ramifiedIdeal_absNorm : Ideal.absNorm ramifiedIdeal=3 := absNorm_span_lambda

lemma prime_power_remainder_multiplicity {R : Type*} [CommMonoidWithZero R]
    [IsCancelMulZero R] {p a : R} (hp : Prime p) (ha : ¬ p ∣ a) (n : ℕ) :
    multiplicity p (p^n*a)=n := by
  apply multiplicity_eq_of_dvd_of_not_dvd ⟨a,rfl⟩
  intro hd
  rw [pow_succ] at hd
  exact ha ((mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero)).mp hd)

abbrev NonzeroIdeal := {I : Ideal O // I ≠ 0}

def lambdaFactorMap (p : ℕ × GoodIdeal) : NonzeroIdeal :=
  ⟨ramifiedIdeal^p.1*p.2.1,mul_ne_zero (pow_ne_zero _ ramifiedIdeal_prime.ne_zero)
    (primaryGenerator_ne_zero_ideal _ p.2.2)⟩

lemma lambdaFactorMap_bijective : Function.Bijective lambdaFactorMap := by
  constructor
  · rintro ⟨n,I⟩ ⟨m,J⟩ heq
    have hh : ramifiedIdeal^n*I.1=ramifiedIdeal^m*J.1 := congrArg Subtype.val heq
    have hn : n=m := by
      have hm := congrArg (multiplicity ramifiedIdeal) hh
      rw [prime_power_remainder_multiplicity ramifiedIdeal_prime
        ((goodIdeal_iff_not_ramified I.1).mp I.2),
        prime_power_remainder_multiplicity ramifiedIdeal_prime
        ((goodIdeal_iff_not_ramified J.1).mp J.2)] at hm
      exact hm
    subst m
    have hIJ : I=J := Subtype.ext (mul_left_cancel₀ (pow_ne_zero n ramifiedIdeal_prime.ne_zero) hh)
    subst J
    rfl
  · intro I
    obtain ⟨J,hJ,hnot⟩ := (FiniteMultiplicity.of_prime_left ramifiedIdeal_prime I.2).exists_eq_pow_mul_and_not_dvd
    refine ⟨(multiplicity ramifiedIdeal I.1,⟨J,(goodIdeal_iff_not_ramified J).mpr hnot⟩), ?_⟩
    exact Subtype.ext hJ.symm

def lambdaFactorEquiv : ℕ × GoodIdeal ≃ NonzeroIdeal :=
  Equiv.ofBijective lambdaFactorMap lambdaFactorMap_bijective

lemma ideal_pow_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun I : Ideal O => I^n) := by
  intro I J h
  dsimp only at h
  apply le_antisymm
  · apply Ideal.dvd_iff_le.mp
    apply (pow_dvd_pow_iff_dvd hn).mp
    rw [h]
  · apply Ideal.dvd_iff_le.mp
    apply (pow_dvd_pow_iff_dvd hn).mp
    rw [h]

lemma lambdaFactor_generator_span (n : ℕ) (I : GoodIdeal) :
    Ideal.span {lambda^n*primaryGenerator I.1}=ramifiedIdeal^n*I.1 := by
  rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
    (primaryGenerator_spec I.1 I.2).1]
  rfl

lemma three_dvd_lambda_sq : (3:O) ∣ lambda^2 := by
  have h := three_dvd_primary_sub_one (lambda^2+1) (show lambda^2 ∣ lambda^2+1-1 by simp)
  simpa only [add_sub_cancel_right] using h

lemma unit_cube_eq_sign (u : Oˣ) : (u:O)^3=1 ∨ (u:O)^3= -1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ ActualEisensteinCubic.K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η:O)=omega := rfl
  have hlist : u ∈ ([1,-1,η,-η,η^2,-η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h | h | h | h | h | h
  · left; simp [h]
  · right; norm_num [h]
  · left; simpa only [h,hη] using omega_primitive.pow_eq_one
  · right
    rw [h,Units.val_neg,hη]
    have hh := omega_primitive.pow_eq_one
    linear_combination -hh
  · left
    rw [h,Units.val_pow_eq_pow_val,hη,show (omega^2)^3=(omega^3)^2 by ring,omega_primitive.pow_eq_one]
    simp
  · right
    rw [h,Units.val_neg,Units.val_pow_eq_pow_val,hη]
    simp only [neg_pow,show (-1:O)^3= -1 by norm_num,
      show (omega^2)^3=(omega^3)^2 by ring,omega_primitive.pow_eq_one,one_pow,mul_one]

def cubeSign : Bool → O
  | false => 1
  | true => -1

lemma cubeSign_isUnit (b : Bool) : IsUnit (cubeSign b) := by
  cases b <;> simp [cubeSign]

lemma cubeSign_cube (b : Bool) : (cubeSign b)^3=cubeSign b := by
  cases b <;> norm_num [cubeSign]

lemma cubeSign_injective : Function.Injective cubeSign := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals norm_num [cubeSign] at h

def cubeBase (n : ℕ) (I : GoodIdeal) : O := lambda^(n+1)*primaryGenerator I.1

def cubeColumn (b : Bool) (n : ℕ) (I : GoodIdeal) : O := cubeSign b*(cubeBase n I)^3

lemma cubeBase_ne_zero (n : ℕ) (I : GoodIdeal) : cubeBase n I ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ residue_lambda_prime.ne_zero) I.2

lemma cubeColumn_ne_zero (b : Bool) (n : ℕ) (I : GoodIdeal) : cubeColumn b n I ≠ 0 :=
  mul_ne_zero (cubeSign_isUnit b).ne_zero (pow_ne_zero 3 (cubeBase_ne_zero n I))

lemma cubeColumn_cube (b : Bool) (n : ℕ) (I : GoodIdeal) :
    cubeColumn b n I=(cubeSign b*cubeBase n I)^3 := by
  rw [mul_pow,cubeSign_cube]
  rfl

lemma cubeColumn_level (b : Bool) (n : ℕ) (I : GoodIdeal) : (3:O) ∣ cubeColumn b n I := by
  have h3 : (3:O) ∣ lambda^(3*(n+1)) := three_dvd_lambda_sq.trans (pow_dvd_pow lambda (by omega))
  have heq : cubeColumn b n I=cubeSign b*(lambda^(3*(n+1))*(primaryGenerator I.1)^3) := by
    simp only [cubeColumn,cubeBase,mul_pow,← pow_mul]
    congr 2
    ring
  rw [heq]
  exact (h3.mul_right _).mul_left _

lemma cubeColumn_span (b : Bool) (n : ℕ) (I : GoodIdeal) :
    Ideal.span {cubeColumn b n I}=(ramifiedIdeal^(n+1)*I.1)^3 := by
  rw [cubeColumn,Ideal.span_singleton_mul_left_unit (cubeSign_isUnit b),
    ← Ideal.span_singleton_pow]
  change (Ideal.span {lambda^(n+1)*primaryGenerator I.1})^3=_
  rw [lambdaFactor_generator_span]

abbrev CubeLower := {c : LevelLower // c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3}

def cubeColumnMap (p : Bool × ℕ × GoodIdeal) : CubeLower :=
  ⟨⟨cubeColumn p.1 p.2.1 p.2.2,cubeColumn_level p.1 p.2.1 p.2.2⟩,
    cubeColumn_ne_zero p.1 p.2.1 p.2.2,⟨cubeSign p.1*cubeBase p.2.1 p.2.2,
      cubeColumn_cube p.1 p.2.1 p.2.2⟩⟩

lemma cubeColumnMap_injective : Function.Injective cubeColumnMap := by
  rintro ⟨b,n,I⟩ ⟨d,m,J⟩ h
  have hc : cubeColumn b n I=cubeColumn d m J := congrArg (fun c : CubeLower => c.1.1) h
  have hs := congrArg (fun a : O => Ideal.span {a}) hc
  rw [cubeColumn_span,cubeColumn_span] at hs
  have hr := ideal_pow_injective (by decide : (3:ℕ) ≠ 0) hs
  have hp : lambdaFactorMap (n+1,I)=lambdaFactorMap (m+1,J) := Subtype.ext hr
  have he := lambdaFactorMap_bijective.1 hp
  have hnm : n=m := Nat.succ.inj (congrArg Prod.fst he)
  have hIJ : I=J := congrArg Prod.snd he
  subst m; subst J
  have hbd : b=d := cubeSign_injective (mul_right_cancel₀
    (pow_ne_zero 3 (cubeBase_ne_zero n I)) hc)
  subst d
  rfl

lemma cubeColumnMap_surjective : Function.Surjective cubeColumnMap := by
  intro c
  obtain ⟨a,ha⟩ := c.2.2
  have ha0 : a ≠ 0 := by intro h; rw [h,zero_pow (by decide)] at ha; exact c.2.1 ha
  let A : NonzeroIdeal := ⟨Ideal.span {a},Ideal.span_singleton_eq_bot.not.mpr ha0⟩
  obtain ⟨⟨k,I⟩,hAI⟩ := lambdaFactorMap_bijective.2 A
  have hfact : ramifiedIdeal^k*I.1=Ideal.span {a} := congrArg Subtype.val hAI
  have hla : lambda ∣ a := by
    apply residue_lambda_prime.dvd_of_dvd_pow
    have hlam3 : lambda ∣ (3:O) :=
      (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
    rw [← ha]
    exact hlam3.trans c.1.2
  have hk : k ≠ 0 := by
    intro hk
    have hIeq : I.1=Ideal.span {a} := by simpa only [hk,pow_zero,one_mul] using hfact
    apply (goodIdeal_iff_not_ramified I.1).mp I.2
    rw [hIeq,Ideal.dvd_iff_le,ramifiedIdeal,Ideal.span_singleton_le_span_singleton]
    exact hla
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hspan : Ideal.span {cubeBase n I}=Ideal.span {a} :=
    (lambdaFactor_generator_span (n+1) I).trans hfact
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  rcases unit_cube_eq_sign u with hu1 | hum1
  · refine ⟨(false,n,I),Subtype.ext (Subtype.ext ?_)⟩
    change cubeColumn false n I=c.1.1
    rw [ha,← hu,mul_pow,hu1,mul_one]
    simp only [cubeColumn,cubeSign,one_mul]
  · refine ⟨(true,n,I),Subtype.ext (Subtype.ext ?_)⟩
    change cubeColumn true n I=c.1.1
    rw [ha,← hu,mul_pow,hum1]
    simp only [cubeColumn,cubeSign]
    ring

def cubeColumnEquiv : Bool × ℕ × GoodIdeal ≃ CubeLower :=
  Equiv.ofBijective cubeColumnMap ⟨cubeColumnMap_injective,cubeColumnMap_surjective⟩

lemma cubeColumn_expanded (b : Bool) (n : ℕ) (I : GoodIdeal) :
    cubeColumn b n I=lambda^(3*(n+1))*(cubeSign b*primaryGenerator I.1)^3 := by
  simp only [cubeColumn,cubeBase,mul_pow,cubeSign_cube,← pow_mul]
  rw [Nat.mul_comm (n+1) 3]
  ring

lemma cubeColumn_arithmetic_sum (b : Bool) (n : ℕ) (I : GoodIdeal) :
    arithmeticResidueSum 0 (cubeColumn b n I)=
      (3^(3*(n+1))*Ideal.absNorm I.1^2*idealTotient I.1:ℕ) := by
  have ha : cubeSign b*cubeBase n I ≠ 0 :=
    mul_ne_zero (cubeSign_isUnit b).ne_zero (cubeBase_ne_zero n I)
  have hA := arithmeticResidueSum_cube _ ha
  rw [← cubeColumn_cube] at hA
  rw [hA,cubeColumn_expanded]
  have hc : IsCoprime (cubeSign b*primaryGenerator I.1) (3:O) :=
    (isCoprime_mul_unit_left_left (cubeSign_isUnit b) _ _).mpr
      (primary_coprime_three _ (primaryGenerator_spec I.1 I.2).2)
  have hs : Ideal.span {cubeSign b*primaryGenerator I.1}=I.1 := by
    rw [Ideal.span_singleton_mul_left_unit (cubeSign_isUnit b),(primaryGenerator_spec I.1 I.2).1]
  rw [card_admissible_cube_product (n+1) _ (mul_ne_zero (cubeSign_isUnit b).ne_zero I.2) hc,hs]

lemma cubeColumn_norm (b : Bool) (n : ℕ) (I : GoodIdeal) :
    Ideal.absNorm (Ideal.span {cubeColumn b n I})=3^(3*(n+1))*Ideal.absNorm I.1^3 := by
  rw [cubeColumn_span,map_pow,map_mul,map_pow,ramifiedIdeal_absNorm,mul_pow,← pow_mul]
  rw [Nat.mul_comm (n+1) 3]

def ramifiedRatio (s : ℂ) : ℂ := (3:ℂ)^(3-3*s)

lemma cube_norm_weight_algebra (s : ℂ) (n N : ℕ) (hN : N ≠ 0) :
    ((3^(3*(n+1))*N^3:ℕ):ℂ)^(-s) * (3^(3*(n+1))*N^2:ℕ) =
      ramifiedRatio s^(n+1) * (N:ℂ)^(-(3*s-2)) := by
  have hNc : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hsplit : ((3:ℂ)^(3*(n+1):ℕ)*(N:ℂ)^3)^(-s)=
      (3:ℂ)^((3*(n+1):ℕ)*(-s))*(N:ℂ)^(3*(-s)) := by
    have hm := Complex.natCast_mul_natCast_cpow (3^(3*(n+1))) (N^3) (-s)
    simp only [Nat.cast_pow,Nat.cast_ofNat] at hm
    rw [hm]
    have h3 : ((3:ℂ)^(3*(n+1):ℕ))^(-s)=(3:ℂ)^((3*(n+1):ℕ)*(-s)) := by
      simpa only [Nat.cast_ofNat] using
        (Complex.natCast_cpow_natCast_mul 3 (3*(n+1)) (-s)).symm
    have hN' : ((N:ℂ)^3)^(-s)=(N:ℂ)^(3*(-s)) := by
      simpa only [Nat.cast_ofNat] using (Complex.natCast_cpow_natCast_mul N 3 (-s)).symm
    rw [h3,hN']
  rw [hsplit]
  have hpoly : (3:ℂ)^(3*(n+1):ℕ)*(N:ℂ)^2 =
      (3:ℂ)^((3*(n+1):ℕ):ℂ)*(N:ℂ)^(2:ℂ) := by
    norm_num only [Complex.cpow_natCast,Complex.cpow_ofNat]
  rw [hpoly]
  calc
    _ = ((3:ℂ)^((3*(n+1):ℕ)*(-s))*(3:ℂ)^((3*(n+1):ℕ):ℂ))*
        ((N:ℂ)^(3*(-s))*(N:ℂ)^(2:ℂ)) := by ring
    _ = (3:ℂ)^((3*(n+1):ℕ)*(-s)+(3*(n+1):ℕ)) * (N:ℂ)^(3*(-s)+2) := by
      rw [← Complex.cpow_add _ _ (by norm_num : (3:ℂ) ≠ 0),← Complex.cpow_add _ _ hNc]
    _ = ramifiedRatio s^(n+1) * (N:ℂ)^(-(3*s-2)) := by
      unfold ramifiedRatio
      rw [← Complex.cpow_mul_nat]
      congr 1 <;> congr 1 <;> push_cast <;> ring

lemma cubeColumn_dirichletTerm (s : ℂ) (b : Bool) (n : ℕ) (I : GoodIdeal) :
    arithmeticDirichletTerm s 0 (cubeColumnMap (b,n,I)).1 =
      ramifiedRatio s^(n+1) * ((idealTotient I.1:ℂ)*unramifiedNormWeight (3*s-2) I.1) := by
  have hI : Ideal.absNorm I.1 ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I.1 I.2)
  change (if cubeColumn b n I=0 then 0 else
    ((‖eisEmbedding (cubeColumn b n I)‖^2:ℝ):ℂ)^(-s)*
      arithmeticResidueSum 0 (cubeColumn b n I)) = _
  rw [if_neg (cubeColumn_ne_zero b n I),eisEmbedding_norm_sq_eq_absNorm_span,
    Complex.ofReal_natCast,cubeColumn_norm,cubeColumn_arithmetic_sum,
    unramifiedNormWeight_of_good _ _ I.2]
  calc
    _ = (((3^(3*(n+1))*Ideal.absNorm I.1^3:ℕ):ℂ)^(-s) *
        (3^(3*(n+1))*Ideal.absNorm I.1^2:ℕ))*(idealTotient I.1:ℂ) := by
      push_cast
      ring
    _ = (ramifiedRatio s^(n+1)*(Ideal.absNorm I.1:ℂ)^(-(3*s-2)))*(idealTotient I.1:ℂ) := by
      rw [cube_norm_weight_algebra s n (Ideal.absNorm I.1) hI]
    _ = _ := by ring

end CubicEisenstein

end

end OAI

end


