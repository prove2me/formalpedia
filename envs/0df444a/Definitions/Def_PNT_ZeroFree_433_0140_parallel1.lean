-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0140_parallel1
-- name    : PNT_ZeroFree_433_0140_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:18:14.770377+00:00
-- url     : https://prove2.me/theorems/b54bf40c-033b-4eb5-85f4-865f0fee7913
-- title:
--   Zero-free region foundations: Eisenstein.CompactProfiles [0140_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CompactProfiles
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CompactProfiles.lean#L98-L470

import Definitions.Def_PNT_ZeroFree_433_0003
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0081
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0088
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0109_1
import Definitions.Def_PNT_ZeroFree_433_0160_parallel1
import Definitions.Def_PNT_ZeroFree_433_0239_parallel1
import Definitions.Def_PNT_ZeroFree_433_0286_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CompactProfiles.lean
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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal


lemma cuspCutoffCorrection_norm_le (F : ℝ → ℂ) (C : ℝ) (hC : 0≤C)
    (hF : ∀v,‖F v‖≤C) (w : HyperbolicSpace) : ‖cuspCutoffCorrection 1 F w‖≤C := by
  by_cases hh : ∃r : CuspCosets,1<cosetHeight r w
  · obtain ⟨r,hr⟩ := hh
    rw [cuspCutoffCorrection_eq 1 le_rfl F w r hr,norm_mul,norm_inv,
      norm_cosetCharacter,inv_one,one_mul]
    exact hF _
  · have hz : cuspCutoffCorrection 1 F w=0 := by
      unfold cuspCutoffCorrection
      have hz : (fun r => cuspCutoffTerm 1 F r w)=(fun _ : CuspCosets => (0:ℂ)) := by
        funext r
        simp [cuspCutoffTerm,show ¬1<cosetHeight r w from fun h => hh ⟨r,h⟩]
      rw [hz,tsum_zero]
    rw [hz,norm_zero]
    exact hC


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal

lemma cuspCutoffCorrection_add (F G : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (F+G) w=cuspCutoffCorrection 1 F w+cuspCutoffCorrection 1 G w := by
  unfold cuspCutoffCorrection
  rw [←(cuspCutoffTerm_summable 1 le_rfl F w).tsum_add (cuspCutoffTerm_summable 1 le_rfl G w)]
  apply tsum_congr
  intro r
  simp only [cuspCutoffTerm,Pi.add_apply]
  split_ifs <;> simp [mul_add]

lemma cuspCutoffCorrection_smul (c : ℂ) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (c • F) w=c • cuspCutoffCorrection 1 F w := by
  unfold cuspCutoffCorrection
  rw [smul_eq_mul,←tsum_mul_left]
  apply tsum_congr
  intro r
  simp only [cuspCutoffTerm,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

def compactHeightProfile (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) : ℝ → ℂ :=
  (Set.Icc a b).indicator (fun v => F (Set.projIcc a b hab v))

lemma compactHeightProfile_measurable (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    Measurable (compactHeightProfile a b hab F) :=
  (F.continuous.comp continuous_projIcc).measurable.indicator measurableSet_Icc

lemma compactHeightProfile_norm_le (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) (v : ℝ) :
    ‖compactHeightProfile a b hab F v‖≤‖F‖ := by
  unfold compactHeightProfile
  by_cases hv : v∈Set.Icc a b
  · rw [Set.indicator_of_mem hv]
    exact F.norm_coe_le_norm _
  · rw [Set.indicator_of_notMem hv,norm_zero]
    exact norm_nonneg _

lemma compactHeightProfile_add (a b : ℝ) (hab : a≤b) (F G : C(Set.Icc a b,ℂ)) :
    compactHeightProfile a b hab (F+G)=compactHeightProfile a b hab F+compactHeightProfile a b hab G := by
  funext v
  simp [compactHeightProfile,Set.indicator_add]

lemma compactHeightProfile_smul (a b : ℝ) (hab : a≤b) (c : ℂ) (F : C(Set.Icc a b,ℂ)) :
    compactHeightProfile a b hab (c • F)=c • compactHeightProfile a b hab F := by
  funext v
  by_cases hv : v∈Set.Icc a b <;> simp [compactHeightProfile,hv]


def compactLogProfile (a b : ℝ) (ha : 0<a) : C(Set.Icc a b,ℂ) :=
  ⟨fun v => (Real.log (v:ℝ):ℂ),Complex.continuous_ofReal.comp
    (continuous_subtype_val.log (fun v => (ha.trans_le v.2.1).ne'))⟩


end CubicEisenstein

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic

theorem full_uniform_normalized_child_tests
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
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
  intro ι _ p hp _ hcop hg
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k hd he hk hz hud hue huv hkap
  apply secondChildKernelPair_eq_postCommon p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs g₁ g₂ W hU₁ hU₂ windows
  · exact hwo _ _ _ _ _ hz hud hue huv hkap
  · exact fun a ha => hwt A₁ _ hA₁ hz 5 a ha
  · exact fun a ha => hwt A₂ _ hA₂ hz 6 a ha

theorem full_uniform_twisted_normalized_child_tests
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (θ₁ θ₂ D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
          (radialPairKernel p e k W (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) X X Y) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows
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
  intro ι _ p hp _ hcop hg
    θ₁ θ₂ D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k hd he hk hz hud hue huv hkap
  have htw₁ : ∀ s, frequencyTwist g₁ θ₁ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₁ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have htw₂ : ∀ s, frequencyTwist g₂ θ₂ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₂ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hsupp₁ : ∀ s, frequencyTwist A₁ (-θ₁) s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply hA₁ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hsupp₂ : ∀ s, frequencyTwist A₂ θ₂ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply hA₂ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hh := secondChildKernelPair_eq_postCommon p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs
    (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W htw₁ htw₂ windows
  dsimp only at hh
  rw [normalized_conjugate_frequencyTwist U hUc hUs,
    halfNormalization_twist U hUc hUs] at hh
  exact hh (hwo _ _ _ _ _ hz hud hue huv hkap)
    (fun a ha => hwt (frequencyTwist A₁ (-θ₁)) _ hsupp₁ hz 5 a ha)
    (fun a ha => hwt (frequencyTwist A₂ θ₂) _ hsupp₂ hz 6 a ha)

end SecondPassIntegration


end

end OAI

end


