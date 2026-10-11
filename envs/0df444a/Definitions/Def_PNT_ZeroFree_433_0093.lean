-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0093
-- name    : PNT_ZeroFree_433_0093
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:16:22.703213+00:00
-- url     : https://prove2.me/theorems/1c6b5ba0-4faf-438b-a7c8-55e3a8f0459e
-- title:
--   Zero-free region foundations: CubicSieve.ConjugateProfiles [0093]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.ConjugateProfiles
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ConjugateProfiles.lean#L77-L741

import Definitions.Def_PNT_ZeroFree_433_0092

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ConjugateProfiles.lean#L77-L741
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.ConjugateProfiles
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

open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
namespace SecondPassIntegration
open JointLogSeparation FourierBridge

lemma logPhase_conjugate (t x : ℝ) : star (logPhase t x) = logPhase (-t) x := by
  unfold logPhase
  simp only [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1
  push_cast
  ring

theorem conjugateProfile_frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    conjugateProfile (frequencyTwist g t) = frequencyTwist (conjugateProfile g) (-t) := by
  ext x
  simp only [conjugateProfile_apply, frequencyTwist_apply, star_mul, logPhase_conjugate]
  ring

theorem normalized_conjugate_frequencyTwist (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    conjugateProfile (halfNormalizationCLM U (frequencyTwist g t)) =
      frequencyTwist (conjugateProfile (halfNormalizationCLM U g)) (-t) := by
  rw [halfNormalization_twist U hUc hUs, conjugateProfile_frequencyTwist]

theorem normalized_conjugate_profile_envelope (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (t s : ℝ) (J : ℕ) :
    ‖(𝓕 (conjugateProfile (halfNormalizationCLM U (frequencyTwist g t)))) s‖ ≤
      fourierPointBound (J+2)
        (twistSourceBound (conjugateProfile (halfNormalizationCLM U g)) (J+2)) *
          (1 + ‖t‖)^(J+2) * FirstPassCubeLabels.firstLogDensity J s := by
  rw [normalized_conjugate_frequencyTwist U hUc hUs]
  simpa only [norm_neg] using
    twisted_profile_fourier_envelope (conjugateProfile (halfNormalizationCLM U g)) (-t) s J

end SecondPassIntegration

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge FirstPassCubeLabels

theorem seven_kernel_twisted_profiles (g₁ g₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ z ud ue uv kap x₁ x₂ : ℝ,
        outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂ * (frequencyTwist g₁ θ₁) (z + x₁) * (frequencyTwist g₂ θ₂) (z + x₂) *
          EisensteinSchwartzPoisson.paperRadialFourier W
            (R * Real.exp (kap - ud - 2 * ue - 2 * uv - x₁ - x₂)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          outerWindow V z ud ue uv kap * logPhase (t₁ + t₂) z *
            logPhase t₃ (kap - ud - 2 * ue - 2 * uv) *
            fixedColumnTest (V 5) (t₁ - t₃) x₁ * fixedColumnTest (V 6) (t₂ - t₃) x₂ *
            ((𝓕 (frequencyTwist g₁ θ₁)) t₁ * (𝓕 (frequencyTwist g₂ θ₂)) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 (frequencyTwist g₁ θ₁)) t₁ * (𝓕 (frequencyTwist g₂ θ₂)) t₂ * b t₃‖ ≤
        C * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2) *
          firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  let a₁ : Fin 7 → ℝ := ![1, 0, 0, 0, 0, 1, 0]
  let a₂ : Fin 7 → ℝ := ![1, 0, 0, 0, 0, 0, 1]
  let a₃ : Fin 7 → ℝ := ![0, -1, -2, -2, 1, -1, -1]
  obtain ⟨C, hC, hsep⟩ := joint_separation_twisted_profiles g₁ g₂ W V a₁ a₂ a₃ M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb⟩ := hsep R hR
  refine ⟨b, ?_⟩
  intro θ₁ θ₂
  obtain ⟨hb, hpoint, hint⟩ := hb θ₁ θ₂
  refine ⟨?_, hpoint, hint⟩
  intro z ud ue uv kap x₁ x₂
  let y : Fin 7 → ℝ := ![z, ud, ue, uv, kap, x₁, x₂]
  have h₁ : (∑ j, a₁ j * y j) = z + x₁ := by
    simp [a₁, y, Fin.sum_univ_succ]
  have h₂ : (∑ j, a₂ j * y j) = z + x₂ := by
    simp [a₂, y, Fin.sum_univ_succ]
  have h₃ : (∑ j, a₃ j * y j) = kap - ud - 2 * ue - 2 * uv - x₁ - x₂ := by
    simp [a₃, y, Fin.sum_univ_succ]
    ring
  have hp : (∏ j, V j (y j)) = outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂ := by
    simp [outerWindow, y, Fin.prod_univ_succ, mul_assoc]
  have h := hb y
  rw [h₁, h₂, h₃, hp] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with t₁
  apply integral_congr_ae
  filter_upwards [] with t₂
  apply integral_congr_ae
  filter_upwards [] with t₃
  have heq := seven_phase_factor z ud ue uv kap x₁ x₂ t₁ t₂ t₃
  unfold fixedColumnTest
  calc
    _ = (outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂) *
      (logPhase t₁ (z + x₁) * logPhase t₂ (z + x₂) *
      logPhase t₃ (kap - ud - 2 * ue - 2 * uv - x₁ - x₂)) *
      ((𝓕 (frequencyTwist g₁ θ₁)) t₁ * (𝓕 (frequencyTwist g₂ θ₂)) t₂ * b t₃) := by ring
    _ = _ := by rw [heq]; ring

end JointLogSeparation

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem secondPreColumn_zero_of_common_overlap
    (Ψ : O →* ℂ) (m c d e k : O) (H : Finset ι → ℂ) (G S : Finset ι)
    (hSG : ¬ Disjoint S G) :
    secondPreColumn p hp hcop hg Ψ (m * ∏ i ∈ G, p i) c d e k H S = 0 := by
  have hm : rowCoprimeMask (fun i => Ideal.span {p i}) S (m * ∏ i ∈ G, p i) = 0 := by
    rw [FirstPassCubeLabels.mask_mul _ hg S,
      commonProduct_mask p hg hinj S G, if_neg hSG, mul_zero]
  simp only [secondPreColumn, hm, mul_zero, zero_mul]

theorem weighted_secondChildKernelPair_congr_off_common
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k₁ k₂ : O)
    (K lengthScale : Finset ι → Finset ι → ℂ)
    (hKL : ∀ S T, Disjoint G S → Disjoint G T → K S T = lengthScale S T) :
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let r := secondMaskQuotient p E G hEG
    secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
      secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
    secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
      secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ lengthScale := by
  dsimp only
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
  let r := secondMaskQuotient p E G hEG
  let w := secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V
  unfold secondChildKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hVM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  have hcoeff :
      w * (star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₁) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₂) (fun _ => 1) M) =
      supportMobius (fun i => Ideal.span {p i}) V *
        star (secondPreColumn p hp hcop hg Ψ₁ (m*(e*r)) c d e k₁ (fun _ => 1) (V∪N)) *
        secondPreColumn p hp hcop hg Ψ₂ (m*(e*r)) c d e k₂ (fun _ => 1) (V∪M) := by
    rw [secondPreColumn_union p hp hcop hg hpr Ψ₁ m r c d e k₁ (fun _ => 1) V N hVN,
      secondPreColumn_union p hp hcop hg hpr Ψ₂ m r c d e k₂ (fun _ => 1) V M hVM]
    simp only [w, secondCommonWeight, star_mul]
    ring
  change w * (_ * K (V∪N) (V∪M)) = w * (_ * lengthScale (V∪N) (V∪M))
  conv_lhs => rw [← mul_assoc w, hcoeff]
  conv_rhs => rw [← mul_assoc w, hcoeff]
  by_cases hGN : Disjoint G (V∪N)
  · by_cases hGM : Disjoint G (V∪M)
    · rw [hKL _ _ hGN hGM]
    · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj Ψ₂ m c d e k₂
        (fun _ => 1) G (V∪M) (fun h => hGM h.symm)
      rw [secondMaskQuotient_spec p E G hEG] at hz
      change secondPreColumn p hp hcop hg Ψ₂ (m*(e*r)) c d e k₂ (fun _ => 1) (V∪M) = 0 at hz
      rw [hz]
      ring
  · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj Ψ₁ m c d e k₁
      (fun _ => 1) G (V∪N) (fun h => hGN h.symm)
    rw [secondMaskQuotient_spec p E G hEG] at hz
    change secondPreColumn p hp hcop hg Ψ₁ (m*(e*r)) c d e k₁ (fun _ => 1) (V∪N) = 0 at hz
    rw [hz, star_zero]
    ring

theorem weighted_secondRayChild_congr_off_common
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k : O) (z : SecondRayIndex)
    (K lengthScale : Finset ι → Finset ι → ℂ)
    (hKL : ∀ S T, Disjoint G S → Disjoint G T → K S T = lengthScale S T) :
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let r := secondMaskQuotient p E G hEG
    secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
      secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m r c d e k (-k) K =
    secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
      secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m r c d e k (-k) lengthScale := by
  dsimp only
  simp only [secondTotalWeight, mul_assoc]
  congr 1
  exact weighted_secondChildKernelPair_congr_off_common p hp hcop hg hinj hpr G E hEG F V
    (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z) m c d k (-k) K lengthScale hKL

end
section

open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildKernelPair_eq_of_quotient_span
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r r' c d e k₁ k₂ : O)
    (hr : Ideal.span {r} = Ideal.span {r'}) (K : Finset ι → Finset ι → ℂ) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
      secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r' c d e k₁ k₂ K := by
  have hc (Ψ : O →* ℂ) (y : O) (N : Finset ι) :
      secondChildColumn p hp hcop hg Ψ (m*r) (c*e*∏ i ∈ V, p i) y (fun _ => 1) N =
        secondChildColumn p hp hcop hg Ψ (m*r') (c*e*∏ i ∈ V, p i) y (fun _ => 1) N := by
    simp only [secondChildColumn, rowCoprimeMask_mul_eq_of_span_eq (fun i => Ideal.span {p i}) N m hr]
  simp only [secondChildKernelPair, hc]

theorem secondChildKernelPair_const_kernel
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (a : ℂ) (K : Finset ι → Finset ι → ℂ) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ (fun S T => a * K S T) =
      a * secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K := by
  simp only [secondChildKernelPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  ring

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open JointLogSeparation (halfNormalizationCLM)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem weighted_secondRayChild_normalized
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k r : O) (z : SecondRayIndex)
    (hr : Ideal.span {secondMaskQuotient p E G hEG} = Ideal.span {r})
    (X Y : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ t, g₁ t ≠ 0 → U t = 1)
    (hU₂ : ∀ t, g₂ t ≠ 0 → U t = 1) :
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let q := secondMaskQuotient p E G hEG
    let X' := X / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding r‖ ^ 2)
    secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m q c d e k (z,V) *
      secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m q c d e k (-k)
        (secondSourcePairKernel p e k
          (fun A => normalizedColumn p (fun B => g₁ (columnLog p X B)) (G∪A))
          (fun A => normalizedColumn p (fun B => g₂ (columnLog p X B)) (G∪A)) W Y) =
    ((X : ℂ)⁻¹ * secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m q c d e k (z,V)) *
      secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m r c d e k (-k)
        (radialPairKernel p e k W (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂)
          X' X' Y) := by
  dsimp only
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
  let q := secondMaskQuotient p E G hEG
  let K := secondSourcePairKernel p e k
    (fun A => normalizedColumn p (fun B => g₁ (columnLog p X B)) (G∪A))
    (fun A => normalizedColumn p (fun B => g₂ (columnLog p X B)) (G∪A)) W Y
  let lengthScale := radialPairKernel p e k W (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂)
    (X / primeProductNorm p G) (X / primeProductNorm p G) Y
  have hn := weighted_secondRayChild_congr_off_common p hp hcop hg hinj hpr
    G E hEG F V Ψ₁ Ψ₂ m c d k z K (fun S T => (X : ℂ)⁻¹ * lengthScale S T)
    (fun S T hGS hGT => secondSourcePairKernel_normalized_shift p hp G S T hGS hGT
      e k X Y hX U hUc hUs g₁ g₂ W hU₁ hU₂)
  dsimp only at hn
  rw [secondChildKernelPair_const_kernel] at hn
  rw [secondChildKernelPair_eq_of_quotient_span p hp hcop hg F V
    (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z) m q r c d e k (-k) hr lengthScale] at hn
  dsimp only [K, lengthScale, e, q] at hn
  rw [residual_scale_quotient_sector p X E G hEG r hr] at hn
  simpa only [mul_left_comm, mul_assoc] using hn

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm jLabel)
open JointLogSeparation (halfNormalizationCLM)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondExpansionQuotient (x : SecondExpansionData ι) : O :=
  if h : x.divisor ⊆ x.sourceCommon then
    secondMaskQuotient p x.divisor x.sourceCommon h else 0

omit [∀ (i : ι), (span {p i}).IsMaximal] in
@[simp] theorem secondExpansionQuotient_of_subset (x : SecondExpansionData ι)
    (h : x.divisor ⊆ x.sourceCommon) :
    secondExpansionQuotient p x = secondMaskQuotient p x.divisor x.sourceCommon h := by
  simp [secondExpansionQuotient, h]

def secondExpansionScale (X : ℝ) (r : O) (x : SecondSupportData ι) : ℝ :=
  X / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)‖ ^ 2 *
    ‖eisEmbedding r‖ ^ 2)

end

def secondExpansionPushWeight {ι : Type*} [DecidableEq ι]
    (C D : Finset ι) (s : Finset (SecondExpansionData ι))
    (w : SecondExpansionData ι → ℂ) (y : SecondSupportData ι) : ℂ :=
  ∑ x ∈ s, if expansionSupportData C D x = y then w x else 0

theorem secondExpansionPushWeight_sum {ι : Type*} [DecidableEq ι]
    (C D : Finset ι) (s : Finset (SecondExpansionData ι))
    (w : SecondExpansionData ι → ℂ) (H : SecondSupportData ι → ℂ) :
    (∑ y ∈ s.image (expansionSupportData C D), secondExpansionPushWeight C D s w y * H y) =
      ∑ x ∈ s, w x * H (expansionSupportData C D x) := by
  unfold secondExpansionPushWeight
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single_of_mem (expansionSupportData C D x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)]
  · simp
  · intro y hy hne
    simp [Ne.symm hne]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem secondExpansionPushWeight_at_source
    (C D : Finset ι) (r : O) (s : Finset (SecondExpansionData ι))
    (hs : ∀ x ∈ s, InSecondQuotientSector p r x)
    (w : SecondExpansionData ι → ℂ) (x : SecondExpansionData ι) (hx : x ∈ s) :
    secondExpansionPushWeight C D s w (expansionSupportData C D x) = w x := by
  unfold secondExpansionPushWeight
  rw [Finset.sum_eq_single_of_mem x hx]
  · simp
  · intro y hy hne
    have hf : expansionSupportData C D y ≠ expansionSupportData C D x := by
      intro h
      exact hne (expansionSupportData_injOn p hinj C D r (hs y hy) (hs x hx) h)
    simp [hf]

def secondExpansionSource
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ x ∈ s,
    ((Y : ℂ) * secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor) *
    (secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap) *
    secondChildKernelPair p hp hcop hg F x.overlap (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (-x.frequency)
      (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
        x.frequency (fun A => H₁ (x.sourceCommon∪A)) (fun A => H₂ (x.sourceCommon∪A)) W Y))

def secondNormalizedExpansionWeight
    (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex) (X Y : ℝ)
    (x : SecondExpansionData ι) : ℂ :=
  ((Y : ℂ) * secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor) *
    ((X : ℂ)⁻¹ * secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap))

include hinj in

theorem secondExpansionSource_eq_raw_variable_sector
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (Ψ : O →* ℂ) (m r : O) (z : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (hs : ∀ x ∈ s, InSecondQuotientSector p r x)
    (X Y : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ t, g₁ t ≠ 0 → U t = 1)
    (hU₂ : ∀ t, g₂ t ≠ 0 → U t = 1) :
    let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
    secondExpansionSource p hp hcop hg F Ψ m c d z s
      (fun A => normalizedColumn p (fun B => g₁ (columnLog p X B)) A)
      (fun A => normalizedColumn p (fun B => g₂ (columnLog p X B)) A) W Y =
    actualSecondRawVariableSector p hp hcop hg B v₁ v₂ ε₁ ε₂
      (s.image (expansionSupportData C D))
      (secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y))
      F (secondRayMinus Ψ z) (secondRayPlus Ψ z) m r
      (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W (secondExpansionScale p X r) Y := by
  dsimp only
  unfold actualSecondRawVariableSector
  rw [secondExpansionPushWeight_sum]
  unfold secondExpansionSource
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hE,hr⟩ := hs x hx
  simp only [secondExpansionQuotient_of_subset p x hE, expansionSupportData,
    secondNormalizedExpansionWeight, secondExpansionScale]
  rw [weighted_secondRayChild_normalized p hp hcop hg hinj hpr x.sourceCommon x.divisor hE
    F x.overlap Ψ Ψ m _ _ x.frequency r z hr X Y hX U hUc hUs g₁ g₂ W hU₁ hU₂]
  simp only [mul_assoc]

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] in
theorem secondInputCoefficient_norm_le (Ψ : O →* ℂ) (m c d : O) (G : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ≤ ‖Ψ (∏ i ∈ G, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) G m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondInputCoefficient, norm_mul, norm_pow,  mul_one]
  calc
    _ ≤ ‖Ψ (∏ i ∈ G, p i)‖ * 1 * 1 ^ 4 * 1 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one _ hg G _
    _ = _ := by ring

theorem secondNormalizedExpansionWeight_after_scale
    (C D : Finset ι) (Ψ : O →* ℂ) (m c d r : O) (z : SecondRayIndex)
    (X Y : ℝ) (hX : 0 < X) (x : SecondExpansionData ι) :
    secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y x *
      (secondExpansionScale p X r (expansionSupportData C D x) : ℂ)⁻¹ =
      ((Y : ℂ) * (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖ ^ 2 : ℝ) *
        (UniqueFactorizationMonoid.moebius (∏ i ∈ x.divisor, Ideal.span {p i}) : ℂ) *
        (‖eisEmbedding r‖ ^ 2 : ℝ) / (X : ℂ) ^ 2) *
      secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
        (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap) := by
  have hNe : (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)‖ ^ 2 : ℝ) ≠ 0 := by
    exact ne_of_gt (SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _))
  have hNec : ((‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hNe
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hX
  simp only [secondNormalizedExpansionWeight, secondSourceCommonCoefficient, secondExpansionScale,
    expansionSupportData, Complex.ofReal_div, Complex.ofReal_mul]
  field_simp

include hinj in

theorem secondNormalizedExpansionWeight_norm_le
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (C D : Finset ι) (Ψ : O →* ℂ) (m c d r : O) (z : SecondRayIndex)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 ≤ Y) (x : SecondExpansionData ι)
    (hΨG : ‖Ψ (∏ i ∈ x.sourceCommon, p i)‖ ≤ 1)
    (hΨV : ‖Ψ (∏ i ∈ x.overlap, p i)‖ ≤ 1) :
    ‖secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y x *
      (secondExpansionScale p X r (expansionSupportData C D x) : ℂ)⁻¹‖ ≤
      Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ := by
  have hA := (secondInputCoefficient_norm_le p hg Ψ m c d x.sourceCommon).trans hΨG
  have hA2 : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖ ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hT := secondTotalWeight_norm_le p hp hcop hg hinj hc Ψ Ψ m (secondExpansionQuotient p x)
    c d (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency z x.overlap hΨV hΨV
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hmu : ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ x.divisor, Ideal.span {p i}) : ℂ)‖ = 1 := by
    have hm := congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj x.divisor)
    simp only [norm_mul, norm_one] at hm
    change ‖supportMobius (fun i => Ideal.span {p i}) x.divisor‖ = 1
    nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) x.divisor)]
  rw [secondNormalizedExpansionWeight_after_scale p hp hcop hg C D Ψ m c d r z X Y hX x]
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_of_nonneg hY,
    Complex.norm_of_nonneg (sq_nonneg _), Complex.norm_of_nonneg (le_of_lt hX), hmu, mul_one]
  calc
    _ ≤ Y * 1 * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ := by gcongr
    _ = _ := by ring

include hinj in

theorem secondNormalizedPushWeight_norm_le
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (C D : Finset ι) (Ψ : O →* ℂ) (m c d r : O) (z : SecondRayIndex)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 ≤ Y)
    (s : Finset (SecondExpansionData ι)) (hs : ∀ x ∈ s, InSecondQuotientSector p r x)
    (hΨG : ∀ x ∈ s, ‖Ψ (∏ i ∈ x.sourceCommon, p i)‖ ≤ 1)
    (hΨV : ∀ x ∈ s, ‖Ψ (∏ i ∈ x.overlap, p i)‖ ≤ 1)
    (y : SecondSupportData ι) (hy : y ∈ s.image (expansionSupportData C D)) :
    ‖secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y) y *
      (secondExpansionScale p X r y : ℂ)⁻¹‖ ≤
      Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  rw [secondExpansionPushWeight_at_source p hinj C D r s hs _ x hx]
  exact secondNormalizedExpansionWeight_norm_le p hp hcop hg hinj hc C D Ψ m c d r z X Y hX hY
    x (hΨG x hx) (hΨV x hx)

end SecondPassArithmetic

open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma isUnit_quotient_span_iff (c d : O) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {c}) d) ↔ IsCoprime c d := by
  constructor
  · intro hd
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hd
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hdiv : c ∣ d*b-1 := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_sub,map_mul,map_one,sub_eq_zero] using hb
    obtain ⟨k,hk⟩ := hdiv
    exact ⟨-k,b,by linear_combination hk⟩
  · rintro ⟨a,b,hab⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk (Ideal.span {c}) b, ?_⟩
    have hc : Ideal.Quotient.mk (Ideal.span {c}) c=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have h := congrArg (Ideal.Quotient.mk (Ideal.span {c})) hab
    simpa only [map_add,map_mul,map_one,hc,mul_zero,zero_mul,zero_add,mul_comm] using h

abbrev AffineUnitResidue (c : O) :=
  {u : O ⧸ Ideal.span {c} // IsUnit (1+3*u)}

lemma affine_representative_condition (c : O) (u : AffineUnitResidue c) :
    denominatorCondition c (1+3*GaussianShiftedPartition.representative c u.1) := by
  refine ⟨(isUnit_quotient_span_iff c _).mp ?_, ⟨_,by ring⟩⟩
  simpa only [map_add,map_mul,map_one,map_ofNat,
    GaussianShiftedPartition.representative_spec] using u.2

def affineResidueMap (c : O) (u : AffineUnitResidue c) : AdmissibleResidue c :=
  ⟨Ideal.Quotient.mk (Ideal.span {3*c})
    (1+3*GaussianShiftedPartition.representative c u.1), by
    apply (denominatorCondition_congr c _
      (1+3*GaussianShiftedPartition.representative c u.1) ?_).mpr
      (affine_representative_condition c u)
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    exact denominatorRep_spec c _⟩

lemma affineResidueMap_bijective (c : O) : Function.Bijective (affineResidueMap c) := by
  constructor
  · intro u v huv
    have hdiv : 3*c ∣ (1+3*GaussianShiftedPartition.representative c u.1)-
        (1+3*GaussianShiftedPartition.representative c v.1) := by
      apply Ideal.mem_span_singleton.mp
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (congrArg Subtype.val huv)
    obtain ⟨k,hk⟩ := hdiv
    have hk' : GaussianShiftedPartition.representative c u.1-
        GaussianShiftedPartition.representative c v.1=c*k := by
      have h3 : (3:O) ≠ 0 := by norm_num
      apply mul_left_cancel₀ h3
      linear_combination hk
    apply Subtype.ext
    rw [← GaussianShiftedPartition.representative_spec c u.1,
      ← GaussianShiftedPartition.representative_spec c v.1]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr ⟨k,hk'⟩)
  · intro r
    obtain ⟨u,hu⟩ := r.2.2
    have hd : denominatorRep c r.1=1+3*u := by linear_combination hu
    let q : AffineUnitResidue c := ⟨Ideal.Quotient.mk (Ideal.span {c}) u, by
      have hh := (isUnit_quotient_span_iff c _).mpr r.2.1
      simpa only [hd,map_add,map_one,map_mul,map_ofNat] using hh⟩
    refine ⟨q,Subtype.ext ?_⟩
    change Ideal.Quotient.mk (Ideal.span {3*c})
      (1+3*GaussianShiftedPartition.representative c q.1)=r.1
    rw [← denominatorRep_spec c r.1,hd]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hrep : c ∣ GaussianShiftedPartition.representative c q.1-u := by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact GaussianShiftedPartition.representative_spec c q.1
    obtain ⟨k,hk⟩ := hrep
    exact ⟨k,by linear_combination 3*hk⟩

def affineResidueEquiv (c : O) : AffineUnitResidue c ≃ AdmissibleResidue c :=
  Equiv.ofBijective (affineResidueMap c) (affineResidueMap_bijective c)

def unitsSubtypeEquiv (R : Type*) [Monoid R] : Rˣ ≃ {x : R // IsUnit x} where
  toFun u := ⟨u,u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := Units.ext u.isUnit.unit_spec
  right_inv x := Subtype.ext x.2.unit_spec

def quotientProductEquiv (a b : O) (hab : IsCoprime a b) :
    (O ⧸ Ideal.span {a*b}) ≃+* (O ⧸ Ideal.span {a}) × (O ⧸ Ideal.span {b}) :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm).trans
    (Ideal.quotientMulEquivQuotientProd _ _ ((Ideal.isCoprime_span_singleton_iff a b).mpr hab))

def affineCRTEq (a b : O) (hab : IsCoprime a b) :
    AffineUnitResidue (a*b) ≃ AffineUnitResidue a × AffineUnitResidue b :=
  ((quotientProductEquiv a b hab).toEquiv.subtypeEquiv (fun q => by
    rw [← MulEquiv.isUnit_map (quotientProductEquiv a b hab) (x := 1+3*q)]
    simp only [map_add,map_one,map_mul,map_ofNat,Prod.isUnit_iff]
    rfl)).trans Equiv.subtypeProdEquivProd

lemma affine_ramified_unit (n : ℕ) (q : O ⧸ Ideal.span {lambda^n}) : IsUnit (1+3*q) := by
  obtain ⟨d,rfl⟩ := Ideal.Quotient.mk_surjective q
  have hlam3 : lambda ∣ (3:O) :=
    (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
  have hcop : IsCoprime lambda (1+3*d) :=
    coprime_of_dvd_sub_one _ _ (by convert! hlam3.mul_right d using 1 ; ring)
  have h := (isUnit_quotient_span_iff (lambda^n) (1+3*d)).mpr hcop.pow_left
  simpa only [map_add,map_one,map_mul,map_ofNat] using h

def affineRamifiedEquiv (n : ℕ) : AffineUnitResidue (lambda^n) ≃ (O ⧸ Ideal.span {lambda^n}) :=
  Equiv.subtypeUnivEquiv (affine_ramified_unit n)

def affineUnramifiedEquiv (m : O) (hm : IsCoprime m (3:O)) :
    AffineUnitResidue m ≃ (O ⧸ Ideal.span {m})ˣ := by
  let h3 : IsUnit (3 : O ⧸ Ideal.span {m}) := by
    simpa only [map_ofNat] using (isUnit_quotient_span_iff m 3).mpr hm
  let e : (O ⧸ Ideal.span {m}) ≃ (O ⧸ Ideal.span {m}) :=
    h3.unit.mulLeft.trans (Equiv.addLeft 1)
  refine (e.subtypeEquiv (fun q => ?_)).trans (unitsSubtypeEquiv _).symm
  change IsUnit (1+3*q) ↔ IsUnit (1+(h3.unit : O ⧸ Ideal.span {m})*q)
  rw [h3.unit_spec]

def idealTotient (I : Ideal O) : ℕ := Nat.card (O ⧸ I)ˣ

lemma card_admissible_ramified_product (n : ℕ) (m : O)
    (hm : IsCoprime m (3:O)) (hlamm : IsCoprime lambda m) :
    Nat.card (AdmissibleResidue (lambda^n*m)) =
      Nat.card (O ⧸ Ideal.span {lambda^n}) * idealTotient (Ideal.span {m}) := by
  calc
    _ = Nat.card (AffineUnitResidue (lambda^n*m)) :=
      Nat.card_congr (affineResidueEquiv _).symm
    _ = Nat.card (AffineUnitResidue (lambda^n) × AffineUnitResidue m) :=
      Nat.card_congr (affineCRTEq _ _ hlamm.pow_left)
    _ = Nat.card ((O ⧸ Ideal.span {lambda^n}) × (O ⧸ Ideal.span {m})ˣ) :=
      Nat.card_congr (Equiv.prodCongr (affineRamifiedEquiv n) (affineUnramifiedEquiv m hm))
    _ = _ := Nat.card_prod _ _

lemma absNorm_span_lambda : Ideal.absNorm (Ideal.span {lambda})=3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclotomicExtension {3^(0+1)} ℚ ActualEisensteinCubic.K := by
    simpa using (inferInstance : IsCyclotomicExtension {3} ℚ ActualEisensteinCubic.K)
  exact IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one 3 0
    (IsCyclotomicExtension.zeta_spec 3 ℚ ActualEisensteinCubic.K)

lemma card_quotient_lambda_pow (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {lambda^n})=3^n := by
  change Ideal.absNorm (Ideal.span {lambda^n})=3^n
  rw [← Ideal.span_singleton_pow,map_pow,absNorm_span_lambda]

theorem card_admissible_lambda_pow_mul (n : ℕ) (m : O)
    (hm : IsCoprime m (3:O)) :
    Nat.card (AdmissibleResidue (lambda^n*m)) = 3^n * idealTotient (Ideal.span {m}) := by
  have hlam3 : lambda ∣ (3:O) :=
    (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
  rw [card_admissible_ramified_product n m hm
    (hm.symm.of_isCoprime_of_dvd_left hlam3),card_quotient_lambda_pow]

end CubicEisenstein

end

end OAI

end


