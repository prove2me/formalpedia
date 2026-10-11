-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0101
-- name    : PNT_ZeroFree_433_0101
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:41:28.547845+00:00
-- url     : https://prove2.me/theorems/2c42be41-e73b-4eb3-bc68-ccb3c3b5bf67
-- title:
--   Zero-free region foundations: Fourier.LogDensity [0101]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Fourier.LogDensity
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Fourier/LogDensity.lean#L80-L604

import Definitions.Def_PNT_ZeroFree_433_0099

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Fourier/LogDensity.lean#L80-L604
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Fourier.LogDensity
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

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace JointLogSeparation
open FirstPassCubeLabels

def tripleLogDensity (J : ℕ) (t : Frequency) : ℝ :=
  firstLogDensity J t.1 * (firstLogDensity J t.2.1 * firstLogDensity J t.2.2)

lemma tripleLogDensity_integrable (J : ℕ) : Integrable (tripleLogDensity J) :=
  (firstLogDensity_integrable J).mul_prod
    ((firstLogDensity_integrable J).mul_prod (firstLogDensity_integrable J))

lemma tripleLogDensity_nonneg (J : ℕ) (t : Frequency) : 0 ≤ tripleLogDensity J t :=
  mul_nonneg (firstLogDensity_nonneg _ _) (mul_nonneg
    (firstLogDensity_nonneg _ _) (firstLogDensity_nonneg _ _))

lemma tripleLogDensity_bounded_integrable (J : ℕ) (G : Frequency → ℝ)
    (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) :
    Integrable (fun t => tripleLogDensity J t * G t) :=
  (tripleLogDensity_integrable J).mul_bdd hG.aestronglyMeasurable
    (Filter.Eventually.of_forall hM)

lemma tripleLogDensity_slice_integrable (J : ℕ) (G : Frequency → ℝ)
    (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) (x : ℝ) :
    Integrable (fun yz : ℝ × ℝ => tripleLogDensity J (x,yz) * G (x,yz)) := by
  have hc : Integrable (fun yz : ℝ × ℝ =>
      firstLogDensity J x * (firstLogDensity J yz.1 * firstLogDensity J yz.2)) :=
    ((firstLogDensity_integrable J).mul_prod (firstLogDensity_integrable J)).const_mul _
  apply hc.mul_bdd
  · exact (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => hM (x,t))

theorem triple_coefficient_density_bound (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ)
    (G : Frequency → ℝ) (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (M : ℝ) (hM : ∀ t, G t ≤ M) (S C : ℝ)
    (hpoint : ∀ t₁ t₂ t₃ : ℝ,
      S * ‖b₁ t₁*b₂ t₂*b₃ t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) :
    S * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ * G (t₁,t₂,t₃)) ≤
    C * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleLogDensity J (t₁,t₂,t₃) * G (t₁,t₂,t₃)) := by
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by
    simpa only [Real.norm_of_nonneg (hG0 t)] using hM t
  have hc := tripleCoefficient_norm_bounded_integrable b₁ b₂ b₃ G hG M hGb
  have hd := tripleLogDensity_bounded_integrable J G hG M hGb
  rw [nested_eq_integral _ hc (tripleCoefficient_norm_slice_integrable b₁ b₂ b₃ G hG M hGb),
    nested_eq_integral _ hd (tripleLogDensity_slice_integrable J G hG M hGb),
    ← integral_const_mul, ← integral_const_mul]
  apply integral_mono (hc.const_mul S) (hd.const_mul C)
  intro t
  have hh := mul_le_mul_of_nonneg_right (hpoint t.1 t.2.1 t.2.2) (hG0 t)
  simpa only [tripleCoefficient, tripleLogDensity, mul_assoc] using hh

end JointLogSeparation

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation

def densityChildEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (J : ℕ) : ℝ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
    tripleLogDensity J (t₁,t₂,t₃) *
      childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)

theorem child_coefficient_density_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hpoint : ∀ t₁ t₂ t₃ : ℝ, S * ‖b₁ t₁*b₂ t₂*b₃ t₃‖ ≤
      C * FirstPassCubeLabels.firstLogDensity J t₁ *
        FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) :
    S * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ *
        childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) ≤
    C * densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ J := by
  let G := childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false) *
    Real.sqrt (energyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀ q, G q ≤ M := by
    intro q
    dsimp [G, childGeometricMean, M]
    gcongr
    · exact childEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact childEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  exact triple_coefficient_density_bound b₁ b₂ b₃ J G hG hG0 M hM S C hpoint

end SecondPassIntegration

namespace JointLogSeparation
open FirstPassCubeLabels

lemma one_add_norm_sub_le (x y : ℝ) :
    1 + ‖x-y‖ ≤ (1+‖x‖)*(1+‖y‖) := by
  have hn := norm_sub_le x y
  have hprod := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  nlinarith

theorem difference_height_weight_le (x y z : ℝ) (J : ℕ) :
    (1+‖x-z‖)^J * (1+‖y-z‖)^J ≤
      (1+‖x‖)^(2*J) * (1+‖y‖)^(2*J) * (1+‖z‖)^(2*J) := by
  have hx := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖x-z‖) (one_add_norm_sub_le x z) J
  have hy := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖y-z‖) (one_add_norm_sub_le y z) J
  calc
    _ ≤ ((1+‖x‖)*(1+‖z‖))^J * ((1+‖y‖)*(1+‖z‖))^J :=
      mul_le_mul hx hy (by positivity) (by positivity)
    _ = (1+‖x‖)^J * (1+‖y‖)^J * (1+‖z‖)^(2*J) := by
      rw [mul_pow, mul_pow, two_mul, pow_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul
        (pow_le_pow_right₀ (by linarith [norm_nonneg x] : 1 ≤ 1+‖x‖) (by omega : J ≤ 2*J))
        (pow_le_pow_right₀ (by linarith [norm_nonneg y] : 1 ≤ 1+‖y‖) (by omega : J ≤ 2*J))
        (by positivity) (by positivity)

theorem triple_density_polynomial_bound (G : Frequency → ℝ)
    (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t) (M : ℝ) (hM : ∀ t, G t ≤ M)
    (J : ℕ) (D : ℝ)
    (hbound : ∀ t, G t ≤ D * (1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, tripleLogDensity J (x,y,z) * G (x,y,z)) ≤
      D * (∫ t : ℝ, firstLogDensity 0 t)^3 := by
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by
    simpa only [Real.norm_of_nonneg (hG0 t)] using hM t
  have hi := tripleLogDensity_bounded_integrable J G hG M hGb
  rw [nested_eq_integral _ hi (tripleLogDensity_slice_integrable J G hG M hGb)]
  have hh : ∀ t : Frequency, tripleLogDensity J t * G t ≤ D * tripleLogDensity 0 t := by
    intro t
    calc
      _ ≤ tripleLogDensity J t *
          (D * (1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) :=
        mul_le_mul_of_nonneg_left (hbound t) (tripleLogDensity_nonneg J t)
      _ = _ := by
        dsimp only [tripleLogDensity]
        rw [← density_weight_identity J t.1, ← density_weight_identity J t.2.1,
          ← density_weight_identity J t.2.2]
        ring
  calc
    _ ≤ ∫ t : Frequency, D * tripleLogDensity 0 t :=
      integral_mono hi ((tripleLogDensity_integrable 0).const_mul D) hh
    _ = D * (∫ t : Frequency, tripleLogDensity 0 t) := integral_const_mul _ _
    _ = _ := by
      have hslice (x : ℝ) : Integrable (fun yz : ℝ × ℝ => tripleLogDensity 0 (x,yz)) := by
        simpa only [tripleLogDensity, Measure.volume_eq_prod] using
          ((firstLogDensity_integrable 0).mul_prod (firstLogDensity_integrable 0)).const_mul
            (firstLogDensity 0 x)
      rw [← nested_eq_integral _ (tripleLogDensity_integrable 0) hslice]
      simp only [tripleLogDensity, integral_const_mul, integral_mul_const]
      ring

end JointLogSeparation
end

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

theorem ideals_coprime_of_relprime (A B : Ideal O) (h : IsRelPrime A B) : IsCoprime A B := by
  apply Ideal.isCoprime_iff_gcd.mpr
  simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp (h (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B))

theorem squarefree_quotient_gcd_coprime (B G : Ideal O) (hB : Squarefree B) :
    IsCoprime (idealQuotient (gcd B G) B) G := by
  let D := gcd B G
  have hDB : D ∣ B := GCDMonoid.gcd_dvd_left B G
  have hDG : D ∣ G := GCDMonoid.gcd_dvd_right B G
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hB.ne_zero hDB
  have hc : IsCoprime (idealQuotient D B) (idealQuotient D G) :=
    (gcd_eq_iff_quotient_coprime D B G hD hDB hDG).mp rfl
  have hmul : Squarefree (D * idealQuotient D B) := by rw [idealQuotient_mul hDB]; exact hB
  have hdq : IsCoprime D (idealQuotient D B) :=
    ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp hmul).1
  have hh := hdq.symm.mul_right hc
  rw [idealQuotient_mul hDG] at hh
  exact hh

theorem gcd_mul_of_coprime_divisor (D H G : Ideal O) (hDG : D ∣ G) (hHG : IsCoprime H G) :
    gcd (D * H) G = D := by
  have hleft : D ∣ gcd (D * H) G := GCDMonoid.dvd_gcd (dvd_mul_right D H) hDG
  have hcop : IsCoprime (gcd (D * H) G) H :=
    (hHG.mono (dvd_refl H) (GCDMonoid.gcd_dvd_right (D * H) G)).symm
  have hright : gcd (D * H) G ∣ D := hcop.dvd_of_dvd_mul_right (GCDMonoid.gcd_dvd_left _ _)
  exact associated_iff_eq.mp (associated_of_dvd_dvd hright hleft)

def squarefreeGcdEquiv (G : Ideal O) (hG : Squarefree G) :
    {B : Ideal O // Squarefree B} ≃
      (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G} where
  toFun B := (⟨gcd B.val G, (mem_idealDivisors hG.ne_zero).mpr (GCDMonoid.gcd_dvd_right _ _)⟩,
    ⟨idealQuotient (gcd B.val G) B.val,
      B.property.squarefree_of_dvd (idealQuotient_dvd (GCDMonoid.gcd_dvd_left _ _)),
      squarefree_quotient_gcd_coprime B.val G B.property⟩)
  invFun p := ⟨p.1.val * p.2.val, squarefree_mul_iff.mpr
    ⟨(p.2.property.2.mono (dvd_refl _) ((mem_idealDivisors hG.ne_zero).mp p.1.property)).symm.isRelPrime,
      hG.squarefree_of_dvd ((mem_idealDivisors hG.ne_zero).mp p.1.property), p.2.property.1⟩⟩
  left_inv B := Subtype.ext (idealQuotient_mul (GCDMonoid.gcd_dvd_left B.val G))
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact gcd_mul_of_coprime_divisor p.1.val p.2.val G
        ((mem_idealDivisors hG.ne_zero).mp p.1.property) p.2.property.2
    · apply Subtype.ext
      change idealQuotient (gcd (p.1.val * p.2.val) G) (p.1.val * p.2.val) = p.2.val
      rw [gcd_mul_of_coprime_divisor p.1.val p.2.val G
        ((mem_idealDivisors hG.ne_zero).mp p.1.property) p.2.property.2]
      have hD : p.1.val ≠ 0 := ne_zero_of_dvd_ne_zero hG.ne_zero
        ((mem_idealDivisors hG.ne_zero).mp p.1.property)
      exact mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right p.1.val p.2.val))

theorem squarefree_gcd_tsum (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑' B : {B : Ideal O // Squarefree B}, f B.val) =
      ∑' p : (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        f (p.1.val * p.2.val) :=
  ((squarefreeGcdEquiv G hG).symm.tsum_eq (fun B => f B.val)).symm

def coprimeSquarefreeRange (G : Ideal O) (K : ℝ) : Finset (Ideal O) :=
  (squarefreeIdealRange K).filter (fun H => IsCoprime H G)

theorem squarefree_cutoff_summable (K : ℝ) (f : Ideal O → ℂ) :
    Summable (fun B : {B : Ideal O // Squarefree B} =>
      if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) := by
  let e : squarefreeIdealRange K → {B : Ideal O // Squarefree B} :=
    fun B => ⟨B.val, (mem_squarefreeIdealRange.mp B.property).1⟩
  apply summable_of_hasFiniteSupport
  apply (Set.finite_range e).subset
  intro B hB
  have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
    by_contra hn
    exact hB (if_neg hn)
  exact ⟨⟨B.val, mem_squarefreeIdealRange.mpr ⟨B.property, hN⟩⟩, Subtype.ext rfl⟩

theorem norm_le_mul_of_ne_zero (D H : Ideal O) (hD : D ≠ 0) :
    Ideal.absNorm H ≤ Ideal.absNorm (D * H) := by
  have hD1 : 1 ≤ Ideal.absNorm D := Nat.one_le_iff_ne_zero.mpr
    (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  simpa only [one_mul, map_mul] using Nat.mul_le_mul_right (Ideal.absNorm H) hD1

theorem coprime_squarefree_cutoff (G D : Ideal O) (hD : D ≠ 0) (K : ℝ) (f : Ideal O → ℂ) :
    (∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
      if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then f (D * H.val) else 0) =
      ∑ H : coprimeSquarefreeRange G K,
        if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then f (D * H.val) else 0 := by
  let e : coprimeSquarefreeRange G K → {H : Ideal O // Squarefree H ∧ IsCoprime H G} :=
    fun H => ⟨H.val, (mem_squarefreeIdealRange.mp (Finset.mem_filter.mp H.property).1).1,
      (Finset.mem_filter.mp H.property).2⟩
  have he : Function.Injective e := by
    intro H J h
    apply Subtype.ext
    exact congrArg (fun C : {H : Ideal O // Squarefree H ∧ IsCoprime H G} => C.val) h
  let F : {H : Ideal O // Squarefree H ∧ IsCoprime H G} → ℂ := fun H =>
    if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then f (D * H.val) else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro H hH
    have hN : (Ideal.absNorm (D * H.val) : ℝ) ≤ K := by
      by_contra hn
      exact hH (if_neg hn)
    have hHN : (Ideal.absNorm H.val : ℝ) ≤ K :=
      (Nat.cast_le.mpr (norm_le_mul_of_ne_zero D H.val hD)).trans hN
    exact ⟨⟨H.val, Finset.mem_filter.mpr
      ⟨mem_squarefreeIdealRange.mpr ⟨H.property.1, hHN⟩, H.property.2⟩⟩, Subtype.ext rfl⟩
  simpa only [tsum_fintype, F, e] using (he.tsum_eq hs).symm

theorem squarefree_gcd_finite_sum (G : Ideal O) (hG : Squarefree G) (K : ℝ) (f : Ideal O → ℂ) :
    (∑ B : squarefreeIdealRange K, f B.val) =
      ∑ D : idealDivisors G, ∑ H : coprimeSquarefreeRange G K,
        if (Ideal.absNorm (D.val * H.val) : ℝ) ≤ K then f (D.val * H.val) else 0 := by
  let F : {B : Ideal O // Squarefree B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs := (squarefreeGcdEquiv G hG).symm.summable_iff.mpr (squarefree_cutoff_summable K f)
  have he := ((squarefreeGcdEquiv G hG).symm.tsum_eq F).symm
  calc
    _ = ∑' B : {B : Ideal O // Squarefree B}, F B := (tsum_squarefree_norm_cutoff K f).symm
    _ = ∑' p : (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        F ((squarefreeGcdEquiv G hG).symm p) := he
    _ = ∑' D : idealDivisors G, ∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        F ((squarefreeGcdEquiv G hG).symm (D, H)) := hs.tsum_prod
    _ = _ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro D _
      change (∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        if (Ideal.absNorm (D.val * H.val) : ℝ) ≤ K then f (D.val * H.val) else 0) = _
      exact coprime_squarefree_cutoff G D.val
        (ne_zero_of_dvd_ne_zero hG.ne_zero ((mem_idealDivisors hG.ne_zero).mp D.property)) K f

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum

theorem canonical_quadraticRow_one (I : Ideal O) (hI : Admissible I) : quadraticRow I 1 = 1 := by
  rw [quadraticRow, dif_pos hI]
  simp [idealSexticRow, finiteSquarefreeRow]

theorem unrestrictedPairCharacter_one (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) : unrestrictedPairCharacter I J 1 = 1 := by
  have h := unrestrictedPairCharacter_span I J hI hJ hray 1
  simpa only [Ideal.span_singleton_one, canonical_quadraticRow_one I hI,
    canonical_quadraticRow_one J hJ, one_mul, Ideal.one_eq_top] using h

def normalizedIdealPair (I J lengthScale : Ideal O) : ℂ :=
  unrestrictedPairCharacter I J lengthScale / (Real.sqrt (Ideal.absNorm lengthScale : ℝ) : ℂ)

theorem normalizedIdealPair_mul (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (A B : Ideal O) :
    normalizedIdealPair I J (A * B) = normalizedIdealPair I J A * normalizedIdealPair I J B := by
  simp only [normalizedIdealPair, unrestrictedPairCharacter_mul I J hI hJ hray,
    map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, div_mul_div_comm]

def normalizedIdealPairHom (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) : Ideal O →* ℂ where
  toFun := normalizedIdealPair I J
  map_one' := by
    rw [normalizedIdealPair, unrestrictedPairCharacter_one I J hI hJ hray, map_one]
    norm_num
  map_mul' := normalizedIdealPair_mul I J hI hJ hray

theorem normalizedIdealPair_square (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (lengthScale : Ideal O) :
    normalizedIdealPair I J lengthScale ^ 2 =
      (idealZeroMask I (idealGenerator lengthScale) * idealZeroMask J (idealGenerator lengthScale)) / (Ideal.absNorm lengthScale : ℂ) := by
  have hc : unrestrictedPairCharacter I J lengthScale ^ 2 =
      idealZeroMask I (idealGenerator lengthScale) * idealZeroMask J (idealGenerator lengthScale) := by
    unfold unrestrictedPairCharacter
    calc
      _ = (quadraticRow I (idealGenerator lengthScale) * quadraticRow I (idealGenerator lengthScale)) *
        (quadraticRow J (idealGenerator lengthScale) * quadraticRow J (idealGenerator lengthScale)) := by ring
      _ = _ := by rw [canonical_quadraticRow_squared I hI, canonical_quadraticRow_squared J hJ]
  have hn : (Real.sqrt (Ideal.absNorm lengthScale : ℝ) : ℂ) ^ 2 = (Ideal.absNorm lengthScale : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Ideal.absNorm lengthScale) : (0 : ℝ) ≤ _)
  rw [normalizedIdealPair, div_pow, hc, hn]

theorem squarefree_divisor_sum_eq_support (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors G, f D) =
      ∑ S ∈ (IdealMobiusDivisorSum.primeSupport G).powerset, f (∏ P ∈ S, P) := by
  have hfilter : (idealDivisors G).filter Squarefree = idealDivisors G := by
    apply Finset.filter_eq_self.mpr
    intro D hD
    exact hG.squarefree_of_dvd ((mem_idealDivisors hG.ne_zero).mp hD)
  rw [← hfilter, squarefree_divisors_eq_image G hG.ne_zero, Finset.sum_image]
  intro S hS T hT hST
  exact support_product_injective (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hST

theorem normalizedIdealPair_double_divisor
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (hray : columnRay I = columnRay J)
    (G : Ideal O) (hG : Squarefree G) :
    (∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
      (UniqueFactorizationMonoid.moebius E : ℂ) * normalizedIdealPair I J (D * E)) =
      ∏ P ∈ IdealMobiusDivisorSum.primeSupport G,
        (1 - (idealZeroMask I (idealGenerator P) * idealZeroMask J (idealGenerator P)) /
          (Ideal.absNorm P : ℂ)) := by
  rw [squarefree_divisor_sum_eq_support G hG]
  simp_rw [squarefree_divisor_sum_eq_support G hG]
  have hprod (S : Finset (Ideal O)) : normalizedIdealPair I J (∏ P ∈ S, P) =
      ∏ P ∈ S, normalizedIdealPair I J P := map_prod (normalizedIdealPairHom I J hI hJ hray) (fun P => P) S
  have hm (E : Finset (Ideal O)) (hE : E ∈ (IdealMobiusDivisorSum.primeSupport G).powerset) :
      (UniqueFactorizationMonoid.moebius (∏ P ∈ E, P) : ℂ) = (-1 : ℂ) ^ E.card :=
    moebius_support_product (Finset.mem_powerset.mp hE)
  have heq : (∑ D ∈ (IdealMobiusDivisorSum.primeSupport G).powerset,
      ∑ E ∈ (IdealMobiusDivisorSum.primeSupport G).powerset,
        (UniqueFactorizationMonoid.moebius (∏ P ∈ E, P) : ℂ) *
          normalizedIdealPair I J ((∏ P ∈ D, P) * ∏ P ∈ E, P)) =
      ∑ D ∈ (IdealMobiusDivisorSum.primeSupport G).powerset,
        ∑ E ∈ (IdealMobiusDivisorSum.primeSupport G).powerset,
          (-1 : ℂ) ^ E.card * (∏ P ∈ D, normalizedIdealPair I J P) *
            ∏ P ∈ E, normalizedIdealPair I J P := by
    apply Finset.sum_congr rfl
    intro D hD
    apply Finset.sum_congr rfl
    intro E hE
    rw [hm E hE, normalizedIdealPair_mul I J hI hJ hray, hprod D, hprod E]
    ring
  rw [heq]
  have hh := QuadraticDivisorCancellation.double_divisor_factorization
    (normalizedIdealPair I J) (IdealMobiusDivisorSum.primeSupport G) ∅ (by simp)
  simpa only [Finset.union_empty, Finset.powerset_empty, Finset.sum_singleton,
    Finset.prod_empty, Finset.card_empty, pow_zero, mul_one,
    normalizedIdealPair_square I J hI hJ] using hh

end
section

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open IdealMobiusDivisorSum QuadraticMainBoundary

def idealNormCutoff (K : ℝ) (H : Ideal O) : ℂ := if (Ideal.absNorm H : ℝ) ≤ K then 1 else 0

def normalizedPairPartial (I J : Ideal O) (K : ℝ) : ℂ :=
  ∑ B : squarefreeIdealRange K, normalizedIdealPair I J B.val

def normalizedPairCoprimePartial (I J G : Ideal O) (K : ℝ) : ℂ :=
  ∑ H : coprimeSquarefreeRange G K, normalizedIdealPair I J H.val

def normalizedPairDivisors (I J G : Ideal O) : ℂ :=
  ∑ E ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius E : ℂ) * normalizedIdealPair I J E

def normalizedPairDensity (I J G : Ideal O) : ℂ :=
  ∏ P ∈ IdealMobiusDivisorSum.primeSupport G,
    (1 - (idealZeroMask I (ConcretePrimeRowBridge.idealGenerator P) *
      idealZeroMask J (ConcretePrimeRowBridge.idealGenerator P)) / (Ideal.absNorm P : ℂ))

theorem normalizedPairPartial_split (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (G : Ideal O) (hG : Squarefree G) (K : ℝ) :
    normalizedPairPartial I J K =
      ∑ H : coprimeSquarefreeRange G K, ∑ D ∈ idealDivisors G,
        normalizedIdealPair I J H.val * normalizedIdealPair I J D * idealNormCutoff K (H.val * D) := by
  rw [normalizedPairPartial, squarefree_gcd_finite_sum G hG K]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro H _
  rw [Finset.sum_coe_sort (idealDivisors G)
    (fun D => if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then normalizedIdealPair I J (D * H.val) else 0)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [mul_comm D H.val]
  rw [normalizedIdealPair_mul I J hI hJ hray]
  unfold idealNormCutoff
  split_ifs <;> ring

theorem normalizedPair_main_difference
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (hray : columnRay I = columnRay J)
    (G : Ideal O) (hG : Squarefree G) (K : ℝ) :
    normalizedPairPartial I J K * normalizedPairDivisors I J G -
      normalizedPairCoprimePartial I J G K * normalizedPairDensity I J G =
      ∑ H : coprimeSquarefreeRange G K, ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) * normalizedIdealPair I J (H.val * D * E) *
          (cutoffDifference K H.val D : ℂ) := by
  have hd : normalizedPairDensity I J G =
      ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          (normalizedIdealPair I J D * normalizedIdealPair I J E) := by
    rw [normalizedPairDensity, ← normalizedIdealPair_double_divisor I J hI hJ hray G hG]
    simp only [normalizedIdealPair_mul I J hI hJ hray]
  rw [normalizedPairPartial_split I J hI hJ hray G hG K, hd]
  unfold normalizedPairDivisors normalizedPairCoprimePartial
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro H _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have hHN : (Ideal.absNorm H.val : ℝ) ≤ K :=
    (mem_squarefreeIdealRange.mp (Finset.mem_filter.mp H.property).1).2
  have hc : (cutoffDifference K H.val D : ℂ) = idealNormCutoff K (H.val * D) - 1 := by
    unfold cutoffDifference idealNormCutoff
    rw [if_pos hHN]
    split_ifs <;> norm_num
  rw [hc, normalizedIdealPair_mul I J hI hJ hray,
    normalizedIdealPair_mul I J hI hJ hray]
  ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum

def commonMaskIdeal (D : Ideal O) : Ideal O := ∏ P ∈ gcdMaskPrimes D, P

theorem commonMaskIdeal_squarefree (D : Ideal O) : Squarefree (commonMaskIdeal D) := by
  have hp (P : Ideal O) (hP : P ∈ gcdMaskPrimes D) : Prime P := by
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P, hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro P hP Q hQ hne
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P, hP⟩
    let : Q.IsMaximal := gcdMaskPrimes_maximal D ⟨Q, hQ⟩
    exact (Ideal.isCoprime_of_isMaximal hne).isRelPrime
  · intro P hP
    exact (hp P hP).squarefree

theorem fixedBadPrimes_dvd_commonMaskIdeal (D P : Ideal O) (hP : P ∈ fixedBadPrimes) :
    P ∣ commonMaskIdeal D := by
  apply Finset.dvd_prod_of_mem
  exact Finset.mem_union_left _ hP

theorem admissible_of_squarefree_coprime_bad
    (H G : Ideal O) (hH : Squarefree H) (hc : IsCoprime H G)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) : Admissible H := by
  refine ⟨hH.ne_zero, hH, ?_⟩
  intro P hP
  have hp : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hb
  exact hp.not_isUnit (hc.isRelPrime (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP) (hbad P hb))

theorem coprimeSquarefreeRange_subset_idealRange (G : Ideal O)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) (K : ℝ) :
    coprimeSquarefreeRange G K ⊆ idealRange K := by
  intro H hH
  obtain ⟨hHs, hc⟩ := Finset.mem_filter.mp hH
  obtain ⟨hsf, hN⟩ := mem_squarefreeIdealRange.mp hHs
  exact mem_idealRange.mpr ⟨admissible_of_squarefree_coprime_bad H G hsf hc hbad, hN⟩

theorem commonMask_coprimeSquarefreeRange_subset (D : Ideal O) (K : ℝ) :
    coprimeSquarefreeRange (commonMaskIdeal D) K ⊆ idealRange K :=
  coprimeSquarefreeRange_subset_idealRange _ (fun P hP => fixedBadPrimes_dvd_commonMaskIdeal D P hP) K

theorem commonMaskIdeal_eq_fixed_mul (D : Ideal O) (hD : Admissible D) :
    commonMaskIdeal D = (∏ P ∈ fixedBadPrimes, P) * D := by
  have hd : Disjoint fixedBadPrimes (IdealMobiusDivisorSum.primeSupport D) := by
    apply Finset.disjoint_left.mpr
    intro P hp hP
    have hfac := Multiset.mem_toFinset.mp hP
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hfac
    let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
    exact (prime_good_iff_not_bad P).mp (hD.2.2 P hfac) hp
  change (∏ P ∈ fixedBadPrimes ∪ IdealMobiusDivisorSum.primeSupport D, P) = _
  rw [Finset.prod_union hd, squarefree_support_product_self hD.2.1]

theorem commonMaskIdeal_norm (D : Ideal O) (hD : Admissible D) :
    Ideal.absNorm (commonMaskIdeal D) = Ideal.absNorm (∏ P ∈ fixedBadPrimes, P) * Ideal.absNorm D := by
  rw [commonMaskIdeal_eq_fixed_mul D hD, map_mul]

end CanonicalQuadraticSieve

end

end OAI

end


