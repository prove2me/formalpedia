-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0088
-- name    : PNT_ZeroFree_433_0088
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:53:12.223709+00:00
-- url     : https://prove2.me/theorems/0b497700-485f-4f72-a433-c6b42d8ef878
-- title:
--   Zero-free region foundations: CubicSieve.FixedProfiles [0088]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.FixedProfiles
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/FixedProfiles.lean#L84-L643

import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0087

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/FixedProfiles.lean#L84-L643
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.FixedProfiles
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
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem secondGaussTerm_test_factors (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ S T =
      star (H₁ S) * H₂ T *
        secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T := by
  simp only [secondGaussTerm, secondInputCoefficient, star_mul, mul_one]
  ring

theorem secondFrequencyKernel_log_tests (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) (W : 𝓢(ℝ, ℂ)) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
      (fun S => V₁ (columnLog p X₁ S)) (fun T => V₂ (columnLog p X₂ T)) W Y =
    actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y := by
  unfold secondFrequencyKernel actualSecondKernel
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd]
    rw [secondGaussTerm_test_factors]
    ring
  · simp [hd]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration

section
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0)

include hp in
theorem radialPairKernel_dyadic_normalization
    (V N M : Finset ι) (hVN : Disjoint V N) (hVM : Disjoint V M)
    (d e k : O) (hd : d ≠ 0) (he : e ≠ 0) (hk : k ≠ 0)
    (D E V₀ X X₀ K Y : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hV₀ : 0 < V₀) (hX : 0 < X) (hX₀ : 0 < X₀) (hK : 0 < K)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    radialPairKernel p e k W g₁ g₂ X X Y (V∪N) (V∪M) =
      (X : ℂ)⁻¹ *
      (conjugateProfile (halfNormalizationCLM U g₁)
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) *
      halfNormalizationCLM U g₂
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) *
      EisensteinSchwartzPoisson.paperRadialFourier W
        ((Y * K / (D * E ^ 2 * V₀ ^ 2 * X₀ ^ 2)) * Real.exp
          (Real.log (elementNorm (d*e*k) / K) - Real.log (elementNorm d / D) -
            2*Real.log (elementNorm e / E) - 2*Real.log (primeProductNorm p V / V₀) -
            columnLog p X₀ N - columnLog p X₀ M))) := by
  unfold radialPairKernel
  rw [normalizedColumn_pair_union p hp V N M hVN hVM X X₀ hX hX₀ U hUc hUs g₁ g₂ hU₁ hU₂,
    second_radial_dyadic_argument p hp V N M hVN hVM d e k hd he hk D E V₀ X₀ K Y hD hE hV₀ hX₀ hK]
  ring

variable [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildKernelPair_eq_postCommon
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (hd : d ≠ 0) (he : e ≠ 0) (hk : k ≠ 0)
    (D E V₀ X X₀ K Y : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hV₀ : 0 < V₀) (hX : 0 < X) (hX₀ : 0 < X₀) (hK : 0 < K)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) (windows : Fin 7 → ℝ → ℂ) :
    let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
    let A₂ := halfNormalizationCLM U g₂
    let z := Real.log (primeProductNorm p V * X₀ / X)
    let ud := Real.log (elementNorm d / D)
    let ue := Real.log (elementNorm e / E)
    let uv := Real.log (primeProductNorm p V / V₀)
    let kap := Real.log (elementNorm (d*e*k) / K)
    outerWindow windows z ud ue uv kap = 1 →
    (∀ a : ℝ, A₁ (z+a) ≠ 0 → windows 5 a = 1) →
    (∀ a : ℝ, A₂ (z+a) ≠ 0 → windows 6 a = 1) →
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
      (radialPairKernel p e k W g₁ g₂ X X Y) =
      (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
        (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) A₁ A₂ W windows
        z ud ue uv kap X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  dsimp only
  intro houter hcut₁ hcut₂
  rw [secondChildKernelPair_fixed_pool]
  simp only [postCommonSmoothPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  by_cases hVN : Disjoint V N
  · by_cases hVM : Disjoint V M
    · rw [radialPairKernel_dyadic_normalization p hp V N M hVN hVM d e k hd he hk
        D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs g₁ g₂ W hU₁ hU₂, houter]
      by_cases h₁ : conjugateProfile (halfNormalizationCLM U g₁)
          (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) = 0
      · rw [h₁]; ring
      · by_cases h₂ : halfNormalizationCLM U g₂
            (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) = 0
        · rw [h₂]; ring
        · rw [hcut₁ _ h₁, hcut₂ _ h₂]; ring
    · rw [secondChildColumn_zero_of_overlap p hp hcop hg Ψ₂ (m*r) c e
        (d*e*(-k)) (fun _ => 1) V M hVM]
      ring
  · rw [secondChildColumn_zero_of_overlap p hp hcop hg Ψ₁ (m*r) c e
      (d*e*k) (fun _ => 1) V N hVN, star_zero]
    ring

end

section
open JointLogSeparation

theorem halfNormalization_support_bound (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (A : ℝ)
    (hg : ∀ s, g s ≠ 0 → |s| ≤ A) :
    ∀ s, halfNormalizationCLM U g s ≠ 0 → |s| ≤ A := by
  intro s hs
  apply hg s
  intro hzero
  apply hs
  rw [halfNormalizationCLM_apply U hUc hUs, hzero, mul_zero]

lemma translated_support_bound (g : ℝ → ℂ) (A B z x : ℝ)
    (hg : ∀ s, g s ≠ 0 → |s| ≤ A) (hz : |z| ≤ B) (hx : g (z+x) ≠ 0) :
    |x| ≤ A+B := by
  have ht := hg (z+x) hx
  have ha : |x| ≤ |z+x| + |z| := by
    calc
      |x| = |(z+x)-z| := by congr 1; ring
      _ ≤ |z+x| + |z| := abs_sub _ _
  linarith

theorem exists_fixed_sector_windows (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ windows : Fin 7 → ℝ → ℂ,
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      (∀ z ud ue uv kap : ℝ,
        |z| ≤ B → |ud| ≤ B → |ue| ≤ B → |uv| ≤ B → |kap| ≤ B →
        outerWindow windows z ud ue uv kap = 1) ∧
      (∀ (g : ℝ → ℂ) (z : ℝ), (∀ s, g s ≠ 0 → |s| ≤ A) → |z| ≤ B →
        ∀ j x, g (z+x) ≠ 0 → windows j x = 1) := by
  obtain ⟨w, hwc, hws, hweq, hwsupp, hwzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff (A+B) (add_nonneg hA hB)
  refine ⟨fun _ => w, fun _ => hwc, fun _ => hws, ?_, ?_, ?_⟩
  · intro j s hs
    have hh := hwsupp (subset_closure hs)
    exact abs_le.mpr hh
  · intro z ud ue uv kap hz hd he hv hk
    have heq (s : ℝ) (hs : |s| ≤ B) : w s = 1 := hweq s (by linarith)
    simp only [outerWindow, heq z hz, heq ud hd, heq ue he, heq uv hv, heq kap hk,
      one_mul]
  · intro g z hg hz j x hx
    exact hweq x (translated_support_bound g A B z x hg hz hx)

end

open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic

theorem exists_fixed_normalized_child_tests {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ (D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
          (radialPairKernel p e k W g₁ g₂ X X Y) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) A₁ A₂ W windows
          (Real.log (primeProductNorm p V * X₀ / X)) (Real.log (elementNorm d / D))
          (Real.log (elementNorm e / E)) (Real.log (primeProductNorm p V / V₀))
          (Real.log (elementNorm (d*e*k) / K)) X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  obtain ⟨U, hUc, hUs, hUone, hUsupp, hUzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff A hA
  have hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₁ s hs)
  have hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₂ s hs)
  let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
  let A₂ := halfNormalizationCLM U g₂
  have hA₁ : ∀ s, A₁ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply halfNormalization_support_bound U hUc hUs g₁ A hg₁ s
    intro hz
    exact hs (by simp [A₁, hz])
  have hA₂ : ∀ s, A₂ s ≠ 0 → |s| ≤ A :=
    halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨windows, hwc, hws, hwb, hwo, hwt⟩ := exists_fixed_sector_windows A B hA hB
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k hd he hk hz hud hue huv hkap
  apply secondChildKernelPair_eq_postCommon p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs g₁ g₂ W hU₁ hU₂ windows
  · exact hwo _ _ _ _ _ hz hud hue huv hkap
  · exact fun a ha => hwt A₁ _ hA₁ hz 5 a ha
  · exact fun a ha => hwt A₂ _ hA₂ hz 6 a ha

end SecondPassIntegration

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel)
open SecondPassIntegration (exists_fixed_normalized_child_tests elementNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def actualSecondRawSector
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (X Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x *
    secondChildKernelPair p hp hcop hg F x.overlap Ψ₁ Ψ₂ m r
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
        jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)
      x.frequency (-x.frequency)
      (radialPairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)
        x.frequency W g₁ g₂ X X Y)

theorem actualSecondRawSector_fixed_profiles
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j t, windows j t ≠ 0 → |t| ≤ A+H+1) ∧
      ∀ (D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O),
        (∀ x ∈ s, x.frequency ≠ 0) →
        (∀ x ∈ s, |secondSectorZ p X X₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D x| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E x| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K x| ≤ H) →
        actualSecondRawSector p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r g₁ g₂ W X Y =
          (X : ℂ)⁻¹ * actualSecondSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ (m*r)
            A₁ A₂ W windows D E V₀ X X₀ K Y := by
  obtain ⟨A₁, A₂, windows, hwc, hws, hwb, hid⟩ :=
    exists_fixed_normalized_child_tests p hp hcop hg g₁ g₂ W A H hA hH hg₁ hg₂
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r hk hz hud hue huv hkap
  simp only [actualSecondRawSector, actualSecondSectorSource, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have heq := hid D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F x.overlap Ψ₁ Ψ₂ m r
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor) x.frequency
    (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _) (hk x hx)
    (hz x hx) (hud x hx) (hue x hx) (huv x hx) (hkap x hx)
  rw [heq]
  simp only [secondSupportLabel, secondSupportRow, actualSecondRow,
    secondSectorZ, secondSectorUd, secondSectorUe, secondSectorUv, secondSectorKap,
    elementNorm, mul_neg]
  ring

end

open ActualEisensteinCubic
open FiniteGaussPhase (canonicalProductGauss_cross_factors)
open FirstCauchyArithmetic (activeGaussRowFactor supportMobius)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem activeGaussRowFactor_zero_of_ne (S T : Finset ι) (hne : S ≠ T) (e : O) :
    activeGaussRowFactor p hp hinj hg S T e 0 = 0 := by
  have hs : (activeSupport S T).Nonempty := by
    by_contra hn
    apply hne
    have he : activeSupport S T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [activeSupport, Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
    exact Finset.Subset.antisymm he.1 he.2
  let : Nonempty (activeSupport S T) := hs.to_subtype
  unfold activeGaussRowFactor
  simp only [finiteSexticRow_zero, star_zero, mul_zero]

theorem activeGaussRowFactor_empty (e k : O) :
    activeGaussRowFactor p hp hinj hg ∅ ∅ e k = 1 := by
  have hempty : activeSupport (∅ : Finset ι) ∅ = ∅ := by simp [activeSupport]
  let : IsEmpty (activeSupport (∅ : Finset ι) ∅) := ⟨fun x => Finset.notMem_empty x.val
    ((congrArg (fun S : Finset ι => x.val ∈ S) hempty).mp x.property)⟩
  simp only [activeGaussRowFactor, finiteSexticRow, star_one, mul_one,
    canonicalProductGauss_cross_factors, Fintype.prod_empty]

theorem secondGaussTerm_empty (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ ∅ ∅ =
      star (H₁ ∅) * H₂ ∅ := by
  have hm : supportMobius (fun i => Ideal.span {p i}) ∅ = 1 := by
    change (UniqueFactorizationMonoid.moebius (1 : Ideal O) : ℂ) = 1
    exact_mod_cast UniqueFactorizationMonoid.moebius_one
  simp only [secondGaussTerm, hm, one_mul, secondInputCoefficient, Finset.prod_empty,
    map_one, activeGaussRowFactor_empty, mul_one]
  simp [rowCoprimeMask, finiteSquarefreeRow]

theorem secondFrequencyKernel_zero (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e : O) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e 0 H₁ H₂ W Y =
      (Y : ℂ) * EisensteinSchwartzPoisson.paperRadialFourier W 0 * star (H₁ ∅) * H₂ ∅ := by
  have hz (S T : Finset ι) (hne : S ≠ T) :
      secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e 0 H₁ H₂ S T = 0 := by
    unfold secondGaussTerm
    rw [activeGaussRowFactor_zero_of_ne p hp hg hinj T S (Ne.symm hne) e, mul_zero]
  unfold secondFrequencyKernel
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single ∅]
    · simp [secondGaussTerm_empty, mul_assoc]
    · intro T hT hne
      rw [hz ∅ T (Ne.symm hne)]
      simp
    · simp
  · intro S hS hne
    apply Finset.sum_eq_zero
    intro T hT
    by_cases hd : Disjoint S T
    · have hneq : S ≠ T := by
        intro heq
        subst T
        exact hne ((show S = ∅ by simpa using Finset.disjoint_iff_inter_eq_empty.mp hd))
      rw [hz S T hneq]
      simp
    · simp [hd]
  · simp

end SecondPassArithmetic

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma symbol_cube_numerator (a d : O) (hd : denominatorCondition (a^3) d) :
    symbol (a^3) d=1 := by
  have hprimary : lambda^2 ∣ d-1 := lambda_sq_dvd_three.trans hd.2
  rw [symbol_pow_numerator a d hprimary 3]
  apply symbol_cube_of_isCoprime a d hprimary
  exact hd.1.of_isCoprime_of_dvd_left ⟨a^2,by ring⟩

theorem arithmeticResidueSum_cube (a : O) (ha : a ≠ 0) :
    arithmeticResidueSum 0 (a^3)=(Nat.card (AdmissibleResidue (a^3)):ℂ) := by
  let : Finite (AdmissibleResidue (a^3)) := finite_admissibleResidue _ (pow_ne_zero 3 ha)
  let : Fintype (AdmissibleResidue (a^3)) := Fintype.ofFinite _
  rw [arithmeticResidueSum,tsum_fintype]
  have hterm (r : AdmissibleResidue (a^3)) :
      eisEmbedding (symbol (a^3) (denominatorRep (a^3) r.1))*
        ShortDraftTrace.breveE (cuspFrequency 0*eisEmbedding (denominatorRep (a^3) r.1)/
          eisEmbedding (a^3))=1 := by
    rw [symbol_cube_numerator a _ r.2,map_one]
    simp [cuspFrequency]
  simp only [hterm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.card_eq_fintype_card]

lemma admissibleResidue_nonempty (c : O) (hc : c ≠ 0) : Nonempty (AdmissibleResidue c) := by
  let d : AdmissibleDenominator c := ⟨1,isCoprime_one_right,by simp⟩
  exact ⟨((residueDenominatorEquiv c hc).symm d).1⟩

theorem arithmeticResidueSum_cube_ne_zero (a : O) (ha : a ≠ 0) :
    arithmeticResidueSum 0 (a^3) ≠ 0 := by
  rw [arithmeticResidueSum_cube a ha]
  let : Finite (AdmissibleResidue (a^3)) := finite_admissibleResidue _ (pow_ne_zero 3 ha)
  let : Nonempty (AdmissibleResidue (a^3)) := admissibleResidue_nonempty _ (pow_ne_zero 3 ha)
  exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := AdmissibleResidue (a^3))).ne'

lemma denominatorCondition_congr (c d e : O) (h : 3*c ∣ d-e) :
    denominatorCondition c d ↔ denominatorCondition c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+3*c*n := by linear_combination hn
  rw [hd]
  exact denominatorCondition_shift c e n

lemma denominatorCondition_mul (c d t : O) (hd : denominatorCondition c d)
    (ht : denominatorCondition c t) : denominatorCondition c (d*t) := by
  refine ⟨hd.1.mul_right ht.1,?_⟩
  convert! dvd_add (hd.2.mul_right t) ht.2 using 1 ; ring

lemma row_symbol_congr_modulus (c d e : O) (hlevel : (3:O) ∣ c)
    (he : (3:O) ∣ e-1) (h : 3*c ∣ d-e) : symbol c d=symbol c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+3*c*n := by linear_combination hn
  rw [hd]
  exact row_symbol_shift c e n hlevel he

lemma denominatorRep_product_congr (c t : O) (r : DenominatorResidue c) :
    3*c ∣ denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) t*r)-t*denominatorRep c r := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [denominatorRep_spec,map_mul,denominatorRep_spec]

def residueMultiplication (c t : O) (ht : denominatorCondition c t)
    (r : AdmissibleResidue c) : AdmissibleResidue c :=
  ⟨Ideal.Quotient.mk (Ideal.span {3*c}) t*r.1,
    (denominatorCondition_congr c _ _ (denominatorRep_product_congr c t r.1)).2
      (denominatorCondition_mul c t _ ht r.2)⟩

lemma denominatorCondition_coprime_modulus (c t : O) (ht : denominatorCondition c t) :
    IsCoprime (3*c) t := by
  obtain ⟨n,hn⟩ := ht.2
  have h3 : IsCoprime (3:O) t := ⟨-n,1,by linear_combination hn⟩
  exact h3.mul_left ht.1

lemma residueMultiplication_injective (c t : O) (ht : denominatorCondition c t) :
    Function.Injective (residueMultiplication c t ht) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {3*c}) t) := by
    have hh := (denominatorCondition_coprime_modulus c t ht).map
      (Ideal.Quotient.mk (Ideal.span {3*c}))
    have hz : Ideal.Quotient.mk (Ideal.span {3*c}) (3*c)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simpa only [hz,isCoprime_zero_left] using hh
  intro r q heq
  apply Subtype.ext
  exact hunit.mul_left_cancel (congrArg Subtype.val heq)

def residueMultiplicationEquiv (c : O) (hc : c ≠ 0) (t : O)
    (ht : denominatorCondition c t) : AdmissibleResidue c ≃ AdmissibleResidue c := by
  letI : Finite (AdmissibleResidue c) := finite_admissibleResidue c hc
  exact Equiv.ofBijective (residueMultiplication c t ht)
    ⟨residueMultiplication_injective c t ht,
      Finite.surjective_of_injective (residueMultiplication_injective c t ht)⟩

lemma residueMultiplication_phase (c : O) (hlevel : (3:O) ∣ c) (t : O)
    (ht : denominatorCondition c t) (r : AdmissibleResidue c) :
    symbol c (denominatorRep c (residueMultiplication c t ht r).1)=
      symbol c t*symbol c (denominatorRep c r.1) := by
  change symbol c (denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) t*r.1))=
    symbol c t*symbol c (denominatorRep c r.1)
  rw [row_symbol_congr_modulus c _ (t*denominatorRep c r.1) hlevel
    (denominatorCondition_mul c t _ ht r.2).2 (denominatorRep_product_congr c t r.1)]
  exact symbol_mul_denominator c t (denominatorRep c r.1)

lemma arithmeticResidueSum_zero (c : O) :
    arithmeticResidueSum 0 c=∑' r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c r.1)) := by
  simp only [arithmeticResidueSum,cuspFrequency,map_zero,zero_div,zero_mul,
    AddChar.map_zero_eq_one,mul_one]

theorem arithmeticResidueSum_constant_eigen (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c)
    (t : O) (ht : denominatorCondition c t) :
    eisEmbedding (symbol c t)*arithmeticResidueSum 0 c=arithmeticResidueSum 0 c := by
  rw [arithmeticResidueSum_zero]
  have heq := (residueMultiplicationEquiv c hc t ht).tsum_eq
    (fun r : AdmissibleResidue c => eisEmbedding (symbol c (denominatorRep c r.1)))
  calc
    _ = ∑' r : AdmissibleResidue c,eisEmbedding (symbol c t*symbol c (denominatorRep c r.1)) := by
      simp only [map_mul,tsum_mul_left]
    _ = _ := by
      convert! heq using 1
      apply tsum_congr
      intro r
      exact congrArg eisEmbedding (residueMultiplication_phase c hlevel t ht r).symm

theorem arithmeticResidueSum_ne_zero_forces_trivial (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) :
    ∀ t : O, denominatorCondition c t → symbol c t=1 := by
  intro t ht
  apply eisEmbedding_injective
  rw [map_one]
  apply (mul_right_cancel₀ hA)
  rw [arithmeticResidueSum_constant_eigen c hc hlevel t ht,one_mul]

end CubicEisenstein

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma coprime_of_dvd_sub_one (a b : O) (h : a ∣ b-1) : IsCoprime a b := by
  obtain ⟨r,hr⟩ := h
  exact ⟨-r,1,by linear_combination hr⟩

lemma primary_coprime_three (p : O) (hp : lambda^2 ∣ p-1) : IsCoprime p (3:O) :=
  (coprime_of_dvd_sub_one 3 p (three_dvd_primary_sub_one p hp)).symm

lemma exists_one_mod_and_prescribed (p m x : O) (hpm : IsCoprime p m) :
    ∃ t : O, m ∣ t-1 ∧ p ∣ t-x := by
  obtain ⟨r,u,hu⟩ := hpm
  refine ⟨1+m*u*(x-1),⟨u*(x-1),by ring⟩,⟨-r*(x-1),?_⟩⟩
  linear_combination (x-1)*hu

theorem constant_coefficient_primary_prime_exponent (c p b : O) (n : ℕ)
    (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hp : Prime p) (hprimary : lambda^2 ∣ p-1)
    (hpb : ¬p ∣ b) (hfactor : c=p^n*b) (hA : arithmeticResidueSum 0 c ≠ 0) :
    3 ∣ n := by
  by_contra hn
  let P : Ideal O := Ideal.span {p}
  let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ P := primary_maximal_divisor_good p hprimary P (Ideal.subset_span (by simp []))
  have hchar : (cubicChar P hg)^n ≠ 1 := by
    intro heq
    have hd := orderOf_dvd_of_pow_eq_one heq
    rw [cubicChar_order P hg] at hd
    exact hn hd
  obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp hchar
  rw [MulChar.pow_apply_coe] at hu
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (u : O ⧸ P)
  have hp9 : IsCoprime p (9:O) := by
    simpa only [show (3:O)^2=9 by norm_num] using (primary_coprime_three p hprimary).pow_right (n := 2)
  have hpm : IsCoprime p (9*b) := hp9.mul_right (hp.coprime_iff_not_dvd.mpr hpb)
  obtain ⟨t,htm,htp⟩ := exists_one_mod_and_prescribed p (9*b) x hpm
  have h9 : (9:O) ∣ t-1 := (dvd_mul_right 9 b).trans htm
  have hb : b ∣ t-1 := (dvd_mul_left b 9).trans htm
  have h3 : (3:O) ∣ t-1 := (show (3:O) ∣ 9 from ⟨3,by norm_num⟩).trans h9
  have htprimary : lambda^2 ∣ t-1 := lambda_sq_dvd_three.trans h3
  have htu : Ideal.Quotient.mk P t=(u : O ⧸ P) := by
    rw [← hx]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr htp)
  have hpt : IsCoprime p t := hp.coprime_iff_not_dvd.mpr (by
    intro hdiv
    have hz : Ideal.Quotient.mk P t=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
    rw [htu] at hz
    exact Units.ne_zero u hz)
  have hbt : IsCoprime b t := coprime_of_dvd_sub_one b t hb
  have hct : IsCoprime c t := by
    rw [hfactor]
    exact hpt.pow_left.mul_left hbt
  have htriv := arithmeticResidueSum_ne_zero_forces_trivial c hc hlevel hA t ⟨hct,h3⟩
  have hbsym : symbol b t=1 := by
    have hh := symbol_denominator_congr b t 1 htprimary (by simp) h9 hb
    simpa only [symbol_one] using hh
  have hpsym : symbol p t=cubicChar P hg (u : O ⧸ P) := by
    rw [symbol_reciprocity p t hp.ne_zero (primary_ne_zero t htprimary) hprimary htprimary]
    change idealSymbol P t=_
    rw [idealSymbol_prime P hg,htu]
  rw [hfactor,symbol_mul_numerator _ _ t htprimary,symbol_pow_numerator p t htprimary,
    hbsym,mul_one,hpsym] at htriv
  exact hu htriv

end CubicEisenstein

end

end OAI

end


