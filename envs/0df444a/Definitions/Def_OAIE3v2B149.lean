-- Prove2me | Definitions.Def_OAIE3v2B149
-- name    : OAIE3v2B149
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:23:00.388482+00:00
-- url     : https://prove2.me/theorems/ce7f1113-05fb-4602-9c00-f59efa8c3c4f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 151 of 311
-- statement:
--   Definitions bundle 151 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B128`, `OAIE3v2B129`, `OAIE3v2B130`, `OAIE3v2B131`, `OAIE3v2B132`, `OAIE3v2B133`, `OAIE3v2B134`, `OAIE3v2B136`, `OAIE3v2B137`, `OAIE3v2B138`, `OAIE3v2B139` of this split.
--
--   Modules: `Dynamics/AllocatedIdealCoverRadiusBudget.lean`, `Estimates/AdaptedMarkedMapHeight.lean`, `Estimates/AllocatedFiberCap.lean`, `Estimates/AllocatedPhysicalLongIdealCap.lean`, `Estimates/CenteredFiniteSliceResidualEnvelope.lean`, `Estimates/CyclicMixedReflection.lean`, `Estimates/NativeLocalPivotVerticalPartners.lean`, `Estimates/NativeSlowConstantProduct.lean`, `Estimates/PreparedModularGeneralDetectorNativeBounds.lean`, `Estimates/RelativePatchPositivePowerInduction.lean`, `Estimates/SampledCommonSlice.lean`, `Estimates/SampledNativeModel.lean`, `Fourier/BoundedFrequencyKernel.lean`, `Fourier/QuadraticFrequencyCoordinates.lean`, `Geometry/RelativePatchFiniteCoordinateReduction.lean`, `Geometry/SampledCommonBox.lean`, `Geometry/SampledDenseCommonBox.lean`, `Lattices/AllocatedAffineAnalyticBudget.lean`, `Lattices/RoundedAffineLifts.lean`, `Nilpotent/BoxNiltestDetection.lean`, `Nilpotent/NativeResetBracketGeometry.lean`, `Polynomial/ForecastSlicedEarlyUnrestrictedPolynomialBudget.lean`, `Sampling/AllocatedSlicedGridResourceBudget.lean`, `Sampling/NativeGridRightDictionary.lean`, `Sampling/PrecenterForecastNativePartners.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B128
import Definitions.Def_OAIE3v2B129
import Definitions.Def_OAIE3v2B130
import Definitions.Def_OAIE3v2B131
import Definitions.Def_OAIE3v2B132
import Definitions.Def_OAIE3v2B133
import Definitions.Def_OAIE3v2B134
import Definitions.Def_OAIE3v2B136
import Definitions.Def_OAIE3v2B137
import Definitions.Def_OAIE3v2B138
import Definitions.Def_OAIE3v2B139

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiberCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (V : Fin m → ℝ) (hV : ∀ j, 0 ≤ V j)
variable (hv : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

include hV hv ν hσ1 Cinv hCinv hchart hsmall

theorem allocatedCoefficientDensity_fiber_cap (t : LayerSamplerVariables G I n B → ℤ)
    (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => allocatedCoefficientDensity B U b hb o hR hσ S (coefficientFiberMap U t y x)) μ ∧
      coefficientFiberAverage U μ t (allocatedCoefficientDensity B U b hb o hR hσ S) y ∈
        Set.Icc (0 : ℝ) (∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) := by
  let : ∀ j, BorelSpace (SubspaceArrayTorus Unit (U j)) := fun _ => QuotientAddGroup.borelSpace
  exact canonicalCoefficientDensity_fiber_cap U b hb o _ _ _ μ ν
    (allocatedLayerWidths_pos B U b hR hσ S)
    (allocatedLayerColumns_chart B U b hR hσ S o hσ1 Cinv hCinv hchart hsmall)
    (fun j => earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j))
    (allocatedCoefficientFactor_constant_cap B U b hb o hR hσ S V hV hv) t y

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sampledTestSeminorm_apply {Ω T X : Type*} [Fintype Ω] [Fintype T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (w : ∀ z, J z → T → ℂ) {K : ℝ} (hw : ∀ z j t, ‖w z j t‖ ≤ K) (v : X → ℂ) :
    sampledTestSeminorm p F w v = p.mean (fun z => ⨆ j, ‖𝔼 t, v (F z t) * w z j t‖) := by
  change p.mean _ = p.mean _
  congr 1
  funext z
  rw [Seminorm.iSup_apply (sampledSingleTestSeminorm_bddAbove F w hw z)]
  rfl

theorem sampledTestSeminorm_le_siteLaw {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (w : ∀ z, J z → T → ℂ) {K : ℝ} (hw : ∀ z j t, ‖w z j t‖ ≤ K) (v : X → ℂ) :
    sampledTestSeminorm p F w v ≤ K * (p.siteLaw F).mean (fun x => ‖v x‖) := by
  rw [sampledTestSeminorm_apply p F w hw, p.siteLaw_mean, ← p.mean_const_mul]
  apply p.mean_mono
  intro z
  apply ciSup_le
  intro j
  exact sampledSingleTestSeminorm_le (F z) (w z j) (hw z j) v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem sampledSliceSeminorm_apply {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) {K : ℝ}
    (hS : ∀ z j, (S z j).Nonempty) (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) :
    sampledSliceSeminorm p F S w v =
      p.mean (fun z => ⨆ j, ‖𝔼 t ∈ S z j, v (F z t) * w z j t‖) := by
  rw [sampledSliceSeminorm, sampledTestSeminorm_apply p F _
    (fun z j t => normalizedSliceTest_norm_le (S z j) (w z j) (hsize z j) (hw z j) t)]
  have he (z) (j) := normalizedSliceTest_mean (S z j) (hS z j) (w z j) (fun t => v (F z t))
  simp only [he]

theorem sampledSliceSeminorm_le_siteLaw {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) {K : ℝ}
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) :
    sampledSliceSeminorm p F S w v ≤ K * (p.siteLaw F).mean (fun x => ‖v x‖) :=
  sampledTestSeminorm_le_siteLaw p F _
    (fun z j t => normalizedSliceTest_norm_le (S z j) (w z j) (hsize z j) (hw z j) t) v

end Erdos3

end

section

namespace Erdos3

theorem sampledSliceSeminorm_congr_values {Ω T X Y : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω)
    (F : Ω → T → X) (G : Ω → T → Y)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    {K : ℝ} (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1)
    (f : X → ℂ) (g : Y → ℂ) (hvalue : ∀ z t, f (F z t) = g (G z t)) :
    sampledSliceSeminorm p F S w f = sampledSliceSeminorm p G S w g := by
  have hb (z) (j) (t) := normalizedSliceTest_norm_le (S z j) (w z j) (hsize z j) (hw z j) t
  unfold sampledSliceSeminorm
  rw [sampledTestSeminorm_apply p F _ hb, sampledTestSeminorm_apply p G _ hb]
  simp only [hvalue]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_nearly_maximizing_sampled_slice_tests {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) {K : ℝ}
    (hS : ∀ z j, (S z j).Nonempty) (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ∀ z, J z, sampledSliceSeminorm p F S w v ≤
      p.mean (fun z => ‖𝔼 t ∈ S z (j z), v (F z t) * w z (j z) t‖) + ε := by
  have hchoice (z : Ω) : ∃ j : J z,
      (⨆ i, ‖𝔼 t ∈ S z i, v (F z t) * w z i t‖) - ε <
        ‖𝔼 t ∈ S z j, v (F z t) * w z j t‖ :=
    exists_lt_of_lt_ciSup (sub_lt_self _ hε)
  choose j hj using hchoice
  refine ⟨j, ?_⟩
  rw [sampledSliceSeminorm_apply p F S w hS hsize hw]
  calc
    _ ≤ p.mean (fun z => ‖𝔼 t ∈ S z (j z), v (F z t) * w z (j z) t‖ + ε) :=
      p.mean_mono (fun z => by linarith [hj z])
    _ = _ := by rw [p.mean_add, p.mean_const]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ z, Measurable (fun c => (law c).weight z))

include hweight

theorem centeredFinite_excessMass_integrable (reference : FiniteProbabilityWeights Ω) (cap : ℝ) :
    Integrable (fun c => reference.excessMass (law c) cap) μ := by
  apply integrable_finsetSum
  intro z _
  exact ((centeredFinite_weight_integrable μ law hweight z).sub
    (integrable_const _)).sup (integrable_const 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledCommonSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sampled_normalized_cube_lower_bound {Ω A B : Type*} [Fintype Ω]
    [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (j : ℕ) (f : Ω → A → ℂ)
    {τ a : ℝ} (ha : 0 ≤ a) (hmass : τ ≤ p.mass G)
    (hdetect : ∀ z ∈ G, a ≤ finiteSupportGowersNorm (j + 1) Q (f z)) :
    τ * a ^ (2 ^ (j + 1)) ≤
      (p.complexMean (fun z => normalizedSupportedCubeSum (j + 1) Q (fun _ => f z))).re := by
  rw [p.complexMean_re]
  simp_rw [normalizedSupportedCubeSum_self_re hφ]
  have hn (z) : 0 ≤ finiteSupportGowersNorm (j + 1) Q (f z) := by
    rw [finiteSupportGowersNorm_eq_restricted hφ]
    exact restrictedGowersNorm_nonneg _ _ _
  have hg := p.mass_mul_le_mean_of_lower_bound G
    (fun z => finiteSupportGowersNorm (j + 1) Q (f z) ^ (2 ^ (j + 1)))
    (fun z => pow_nonneg (hn z) _) (fun z hz => pow_le_pow_left₀ ha (hdetect z hz) _)
  exact (mul_le_mul_of_nonneg_right hmass (pow_nonneg ha _)).trans (by simpa [mul_comm] using hg)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_common_inner_sampled_slice {Ω T X : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) {K : ℝ}
    (hS : ∀ z j, (S z j).Nonempty) (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    (C : Finset (Finset T)) {α ε η ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hlarge : ε + η + ρ < α)
    (hcover : ∀ z j, ∃ A ∈ C, A.Nonempty ∧ A ⊆ S z j ∧
      2 * (1 - (A.card : ℝ) / (S z j).card) ≤ η)
    (hmean : α ≤ sampledSliceSeminorm p F S w v) :
    ∃ A ∈ C, A.Nonempty ∧ ∃ G : Finset Ω, ∃ j : ∀ z, J z,
      (α - ε - η - ρ) / C.card ≤ p.mass G ∧
      ∀ z ∈ G, A ⊆ S z (j z) ∧
        2 * (1 - (A.card : ℝ) / (S z (j z)).card) ≤ η ∧
        ρ ≤ ‖𝔼 t ∈ A, v (F z t) * w z (j z) t‖ := by
  obtain ⟨j, hj⟩ := exists_nearly_maximizing_sampled_slice_tests p F S w hS hsize hw v hε
  choose A hAC hAn hAS hAerr using fun z => hcover z (j z)
  let code : Ω → C := fun z => ⟨A z, hAC z⟩
  let _ : Nonempty C := ⟨code (Classical.arbitrary Ω)⟩
  let f : Ω → ℝ := fun z => ‖𝔼 t ∈ A z, v (F z t) * w z (j z) t‖
  have hunit (z : Ω) (t : T) : ‖v (F z t) * w z (j z) t‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hv _)).trans (hw _ _ _)
  have happrox (z : Ω) : ‖𝔼 t ∈ S z (j z), v (F z t) * w z (j z) t‖ ≤ f z + η := by
    have he := (norm_expect_subset_sub_le (A z) (S z (j z)) (hAn z) (hAS z)
      (fun t => v (F z t) * w z (j z) t) (fun t _ => hunit z t)).trans (hAerr z)
    have ht := norm_sub_norm_le (𝔼 t ∈ S z (j z), v (F z t) * w z (j z) t)
      (𝔼 t ∈ A z, v (F z t) * w z (j z) t)
    rw [norm_sub_rev] at he
    dsimp [f]
    linarith
  have hm : α - ε - η ≤ p.mean f := by
    have hm' := p.mean_mono happrox
    rw [p.mean_add, p.mean_const] at hm'
    linarith
  let G := Finset.univ.filter (fun z => ρ ≤ f z)
  have hG : α - ε - η - ρ ≤ p.mass G := by
    simpa only [div_one] using p.mass_superlevel_ge f hρ zero_lt_one
      (fun z => norm_finset_expect_le_one _ _ (fun t _ => hunit z t)) hm
  obtain ⟨c, hc⟩ := p.exists_large_mass_choice_fiber G code
  let H := G.filter (fun z => code z = c)
  have hmass : (α - ε - η - ρ) / C.card ≤ p.mass H := by
    convert (div_le_div_of_nonneg_right hG (Nat.cast_nonneg (Fintype.card C))).trans hc using 1
    all_goals first | rfl | simp only [H, Fintype.card_coe]
    unfold FiniteProbabilityWeights.mass
    apply Finset.sum_congr
    · ext z
      simp only [Finset.mem_filter]
    · intro z _
      rfl
  have hHpos : 0 < p.mass H := lt_of_lt_of_le
    (div_pos (by linarith) (by exact_mod_cast C.card_pos.mpr ⟨c.val, c.property⟩)) hmass
  have hH : H.Nonempty := by
    by_contra h
    have he : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hHpos
    exact lt_irrefl _ hHpos
  have hcode (z : Ω) (hz : z ∈ H) : A z = c.val :=
    congrArg Subtype.val (Finset.mem_filter.mp hz).2
  obtain ⟨z₀, hz₀⟩ := hH
  refine ⟨c.val, c.property, ?_, H, j, hmass, ?_⟩
  · rw [← hcode z₀ hz₀]
    exact hAn z₀
  · intro z hz
    rw [← hcode z hz]
    exact ⟨hAS z, hAerr z, (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NativeGridRightDictionary
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_grid_right_dictionary (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p →
      Nonempty (NativeGridRightDictionary D m (Real.exp ((p + C) ^ C))) := by
  obtain ⟨a, _, hrep⟩ := exists_native_rational_representatives s
  let P : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a + 7) ^ 7
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD m hm hmp
  obtain ⟨q, hq, hqp, hreps⟩ := hrep D p hp hD m hm hmp
  let t := p + (p + a) ^ a
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by
    dsimp [t]
    exact le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hat : (p + a) ^ a ≤ t := by dsimp [t]; linarith
  have htbox : t ≤ (t + 2) ^ 2 := le_power_budget ht (by decide)
  have hboxcount : (t + 2) ^ 2 ≤ (t + 7) ^ 7 :=
    (pow_le_pow_left₀ (by linarith) (by linarith : t + 2 ≤ t + 7) 2).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ t + 7) (by decide : 2 ≤ 7))
  have hcountC : (t + 7) ^ 7 ≤ (p + C) ^ C := by
    simpa [P, t, Polynomial.eval₂_pow] using hbudget p hp
  have hboxC := hboxcount.trans hcountC
  have haC := hat.trans (htbox.trans hboxC)
  obtain ⟨n, hn, hncount, rep, hrepbounds, hcover⟩ :=
    exists_bounded_native_grid_enumeration D q hq (Real.exp_pos ((t + 2) ^ 2)).le
  have hnexp : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    apply (Nat.cast_le.mpr hncount).trans
    have hcount := grid_box_count_le_exp 2 d q (by decide) ht (hD.1.trans hpt)
      (hqp.trans (Real.exp_le_exp.mpr hat))
    norm_num at hcount
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      using hcount.trans (Real.exp_le_exp.mpr hcountC)
  refine ⟨{
    denominator := q
    count := n
    denominator_pos := hq
    count_pos := hn
    denominator_bound := hqp.trans (Real.exp_le_exp.mpr haC)
    count_bound := hnexp
    representative := rep
    representative_bounds := fun j =>
      ⟨fun i => ((hrepbounds j).1 i).trans (Real.exp_le_exp.mpr hboxC), (hrepbounds j).2⟩
    cover := ?_
  }⟩
  intro g hg
  obtain ⟨r, hr, hrgrid, γ, hγ, heq⟩ := (hreps g hg).1
  obtain ⟨j, hj⟩ := hcover r
    (fun i => (hr i).trans (Real.exp_le_exp.mpr (hat.trans htbox))) hrgrid
  exact ⟨j, γ, hγ, by simpa only [hj] using heq⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SampledCommonBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_common_sampled_box {Ω T X I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype T] [Nonempty T] [Fintype I] [DecidableEq I]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    (e : T → I → ℤ) (he : Function.Injective e) {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ)
    (hslice : ∀ z j, IsDenseCommonStrideBox N p ((S z j).image e))
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    {α ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hlarge : ε + Fintype.card I * Real.exp (-p) + ρ < α)
    (hmean : α ≤ sampledSliceSeminorm μ F S w v) :
    ∃ A : Finset T, A.Nonempty ∧
      (∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ),
        0 < m ∧ (∀ i, 0 < H i) ∧ A.image e = commonStrideBox c m H) ∧
      ∃ G : Finset Ω, ∃ j : ∀ z, J z,
        Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) *
          (α - ε - Fintype.card I * Real.exp (-p) - ρ) ≤ μ.mass G ∧
        ∀ z ∈ G, A ⊆ S z (j z) ∧
          2 * (1 - (A.card : ℝ) / (S z (j z)).card) ≤ Fintype.card I * Real.exp (-p) ∧
          ρ ≤ ‖𝔼 t ∈ A, v (F z t) * w z (j z) t‖ := by
  obtain ⟨C, hcount, hshape, hcover⟩ := exists_finite_site_box_inner_family e he hp N
  have hS (z) (j) : (S z j).Nonempty := Finset.image_nonempty.mp (hslice z j).nonempty
  have hsize (z) (j) : (Fintype.card T : ℝ) / (S z j).card ≤ Fintype.card T :=
    div_le_self (Nat.cast_nonneg _) (by exact_mod_cast (hS z j).card_pos)
  obtain ⟨A, hAC, hAn, G, j, hmass, hlocal⟩ := exists_common_inner_sampled_slice μ F S w
    hS hsize hw v hv C hε hρ hlarge (fun z j => hcover (S z j) (hslice z j)) hmean
  refine ⟨A, hAn, hshape A hAC hAn, G, j, ?_, hlocal⟩
  have hcard : (0 : ℝ) < C.card := by exact_mod_cast C.card_pos.mpr ⟨A, hAC⟩
  have hfrac := div_le_div_of_nonneg_left
    (show 0 ≤ α - ε - Fintype.card I * Real.exp (-p) - ρ by linarith) hcard hcount
  have h := hfrac.trans hmass
  simpa only [div_eq_mul_inv, ← Real.exp_neg, mul_comm] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BoundedFrequencyKernel
namespace OAI

section

namespace Erdos3

open Module
open scoped Classical

theorem exists_frequency_kernel_basis_logHeight
    {V : Type*} [AddCommGroup V] [Module ℚ V] {d D : ℕ}
    (b : Basis (Fin d) ℚ V) (P : Submodule ℚ V)
    (vP : Fin d → V) (hP : Submodule.span ℚ (Set.range vP) = P)
    (eta : Fin D → V →ₗ[ℚ] ℚ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hD : (D : ℝ) ≤ p)
    (hvP : ∀ i j, rationalLogHeight (b.repr (vP i) j) ≤ p)
    (heta : ∀ i j, rationalLogHeight (eta i (b j)) ≤ p) :
    ∃ n : ℕ, n ≤ d ∧
      ∃ bk : Basis (Fin n) ℚ (finiteFrequencyKernel P eta (List.finRange D)),
        ∀ i j, rationalLogHeight (b.repr (bk i : V) j) ≤
          ((2 * p + 6) ^ 2 + 2) ^ 63 := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  choose v hv hh using fun i => exists_bounded_frequency_kernel_spanning b (eta i) hH
    (fun j => rationalHeightLE_ceil_exp (heta i j))
  let U : Option (Fin D) → Submodule ℚ V := fun z => z.elim P (fun i => LinearMap.ker (eta i))
  let gen : Option (Fin D) → Fin d → V := fun z => z.elim vP v
  have hgen (z) : Submodule.span ℚ (Set.range (gen z)) = U z := by
    cases z with
    | none => exact hP
    | some i => exact hv i
  have hHmono : H ≤ 2 * H ^ 2 := by nlinarith
  have hHe : ((2 * H ^ 2 : ℕ) : ℝ) ≤ Real.exp (2 * p + 4) := by
    have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    calc
      _ = 2 * (H : ℝ) ^ 2 := by push_cast; rfl
      _ ≤ Real.exp 2 * (Real.exp (p + 1)) ^ 2 := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hheight (z) (i j) : rationalLogHeight (b.repr (gen z i) j) ≤ 2 * p + 4 := by
    apply rationalLogHeight_le_of_height (H := 2 * H ^ 2) _ hHe
    cases z with
    | none => exact (rationalHeightLE_ceil_exp (hvP i j)).mono hHmono
    | some k => exact hh k i j
  have hcount : (Fintype.card (Option (Fin D)) : ℝ) ≤ 2 * p + 4 := by
    simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    linarith
  obtain ⟨n, hn, bk, hbk⟩ := exists_submodule_intersection_basis_logHeight b U gen hgen
    (by linarith : 0 ≤ 2 * p + 4)
    (by simpa only [Fintype.card_fin] using (show (d : ℝ) ≤ 2 * p + 4 by linarith))
    (by simpa only [Fintype.card_fin] using (show (d : ℝ) ≤ 2 * p + 4 by linarith))
    hcount hheight
  have hK : (⨅ z, U z) = finiteFrequencyKernel P eta (List.finRange D) := by
    ext x
    simp only [Submodule.mem_iInf, mem_finiteFrequencyKernel, List.mem_finRange, forall_true_left]
    constructor
    · intro h
      exact ⟨h none, fun i => h (some i)⟩
    · intro h z
      cases z with
      | none => exact h.1
      | some i => exact h.2 i
  refine ⟨n, by simpa only [Fintype.card_fin] using hn,
    bk.map (LinearEquiv.ofEq _ _ hK), ?_⟩
  intro i j
  simpa only [Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    show 2 * p + 4 + 2 = 2 * p + 6 by ring] using hbk i j

theorem exists_frequency_code_kernel_basis_logHeight
    {V J : Type*} [AddCommGroup V] [Module ℚ V] {d D : ℕ}
    (b : Basis (Fin d) ℚ V) (P : Submodule ℚ V)
    (vP : Fin d → V) (hP : Submodule.span ℚ (Set.range vP) = P)
    (eta : J → V →ₗ[ℚ] ℚ) (code : Fin D → Option J) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hD : (D : ℝ) ≤ p)
    (hvP : ∀ i j, rationalLogHeight (b.repr (vP i) j) ≤ p)
    (heta : ∀ i j, rationalLogHeight (eta i (b j)) ≤ p) :
    ∃ n : ℕ, n ≤ d ∧ ∃ bk : Basis (Fin n) ℚ (frequencyCodeKernel P eta code),
      ∀ i j, rationalLogHeight (b.repr (bk i : V) j) ≤ ((2 * p + 6) ^ 2 + 2) ^ 63 := by
  apply exists_frequency_kernel_basis_logHeight b P vP hP
    (fun i => (code i).elim 0 eta) hp hd hD hvP
  intro i j
  cases code i with
  | none => simpa [rationalLogHeight] using hp
  | some k => exact heta k j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem detector_of_unit_detector {X : Type*} [Fintype X]
    (μ : FiniteProbabilityWeights X) (S : Seminorm ℂ (X → ℂ)) (atoms : Set (X → ℂ))
    {R δ β : ℝ} (hR : 0 < R)
    (hdetect : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) → δ / R ≤ S g →
      ∃ Q ∈ atoms, β ≤ ‖μ.correlation g Q‖)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ R) (hS : δ ≤ S f) :
    ∃ Q ∈ atoms, R * β ≤ ‖μ.correlation f Q‖ := by
  let g : X → ℂ := (R : ℂ)⁻¹ • f
  have hg (x : X) : ‖g x‖ ≤ 1 := by
    change ‖(R : ℂ)⁻¹ * f x‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    calc
      R⁻¹ * ‖f x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (hf x) (inv_nonneg.mpr hR.le)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  have hSg : δ / R ≤ S g := by
    dsimp only [g]
    rw [map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr hR.le)
  obtain ⟨Q, hQ, hcorr⟩ := hdetect g hg hSg
  have heq : μ.correlation g Q = (R : ℂ)⁻¹ * μ.correlation f Q := by
    simp only [FiniteProbabilityWeights.correlation, g, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le] at hcorr
  refine ⟨Q, hQ, ?_⟩
  have h := mul_le_mul_of_nonneg_left hcorr hR.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedMarkedMapHeight
namespace OAI

section

namespace Erdos3

namespace RationalFilteredNilmanifold

open Module

theorem markedMap_basisChange_logHeight
    {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hb : ∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p)
    (hc : ∀ i j, rationalLogHeight (E.basis.repr (c i) j) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis i)) j) ≤ p) :
    ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ adaptedMarkedMapHeightBudget p := by
  obtain ⟨_, hinv, _⟩ := E.basis_geometry_of_forward_height c hp hE
    (fun i j => (hc i j).trans (by linarith))
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin] using hD.1
  have he : (Fintype.card (Fin e) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin] using hE.1
  have hnative (i : ι) (j : Fin e) :
      rationalLogHeight (E.basis.repr (φ (b i)) j) ≤ (p + 2) ^ 4 :=
    linearMap_coordinate_logHeight D.basis E.basis φ hp hd hφ (b i) (hb i) j
  let q := p + (p + 4) ^ 5 + (p + 2) ^ 4
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have h5 : 0 ≤ (p + 4) ^ 5 := by positivity
  have h4 : 0 ≤ (p + 2) ^ 4 := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hinvq : (p + 4) ^ 5 ≤ q := by dsimp [q]; linarith
  have hnativeq : (p + 2) ^ 4 ≤ q := by dsimp [q]; linarith
  intro i j
  exact linearMap_coordinate_logHeight E.basis c LinearMap.id hq (he.trans hpq)
    (fun a k => (hinv a k).trans hinvq) (φ (b i))
    (fun k => (hnative i k).trans hnativeq) j

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSlowConstantProduct
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_native_slow_left_constant_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (weight : Fin d → ℕ)
      (_hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ weight i}))
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      ∀ A : σ → ℝ, (∀ i, 0 < A i) → ∀ a : D.RealGroup,
      (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp p) →
      ∀ e : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A (Real.exp p) e →
      D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A (Real.exp ((p + C) ^ C))
        (D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) a * e) := by
  obtain ⟨c, _, hproduct⟩ := exists_polynomial_slow_product_bound s 1 2
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D weight hF p hp hD hσ A hA a ha e he
  have hbound : (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  let cA := D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) a
  have hcA : D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A (Real.exp p) cA :=
    D.filtration.polynomialSlowBound_constant D.basis (fun _ => 1) A hA (Real.exp_nonneg p) a ha
  have hsmall : Real.exp p ≤ Real.exp ((p + 1 + 2) ^ (1 : ℕ)) :=
    Real.exp_le_exp.mpr (by simp only [pow_one]; linarith)
  have hlist : ∀ r ∈ [cA, e], D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A
      (Real.exp ((p + 1 + 2) ^ (1 : ℕ))) r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hA hsmall cA hcA
    · have hr' : r = e := List.mem_singleton.mp hr
      subst r
      exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hA hsmall e he
  have hout := hproduct D.filtration D.basis weight hF (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) ⌈Real.exp p⌉₊ (p + 1) (one_le_ceil_exp p) (by linarith)
    (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1))
    (hσ.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) A hA [cA, e]
    (by simp) hlist
  have hslow : D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A
      (Real.exp ((p + 1 + c) ^ c)) (cA * e) := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hout
  exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hA
    (Real.exp_le_exp.mpr hbound) (cA * e) hslow

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RoundedAffineLifts
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G V : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j) (center : ∀ j, U j)

noncomputable def allocatedAffineDensity
    (frame : Option (LayerSamplerVariables G I n B) → V → ℝ) : ℝ :=
  allocatedCoefficientDensity B U b hb o hR hσ S (centeredAffineCoefficientTorus U p hm center frame)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongIdealCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedIdealCoverRadius_pos (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    0 < allocatedIdealCoverRadius (G := G) B rowSets C j :=
  finiteRowChartRadius_pos _ _ (hC j) (allocatedIdealCoverSupport_nonneg B rowSets j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedIdealCoverRadiusBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedIdealCoverRadius_inv_le_exp {P : ℝ} (hP : 0 ≤ P)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m)
    (hA : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ Real.exp P)
    (hI : partitionedIdealRadius α m + 1 ≤ Real.exp P)
    (hn : (n j : ℝ) ≤ Real.exp P)
    (hW : ∀ i : Fin (n j), allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤ Real.exp P)
    (hr : ((rowSets j).card : ℝ) ≤ Real.exp P)
    (hd : (Fintype.card (I j) : ℝ) ≤ Real.exp P) (hCP : C j ≤ Real.exp P) :
    (allocatedIdealCoverRadius (G := G) B rowSets C j)⁻¹ ≤ Real.exp (8 * P + 14) := by
  have hp : Real.exp P ≤ Real.exp (2 * P + 2) := Real.exp_le_exp.mpr (by linarith)
  have h := finiteRowChartRadius_inv_le_exp (rowSets j).card (Fintype.card (I j))
    (hC j) (allocatedIdealCoverSupport_nonneg B rowSets j) (by positivity : 0 ≤ 2 * P + 2)
    (hr.trans hp) (hd.trans hp) (hCP.trans hp)
    (allocatedIdealCoverSupport_le_exp B rowSets hP j hA hI hn hW)
  have he : 4 * (2 * P + 2) + 6 = 8 * P + 14 := by ring
  simpa only [allocatedIdealCoverRadius, he] using h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeLocalPivotVerticalPartners
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem weighted_fixed_choices {Ω K : Type*} {I : K → Type*}
    [Fintype Ω] [Fintype K] [∀ k, Fintype (I k)]
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (rel : ∀ (_ : Ω) (k : K), I k → Prop)
    (hex : ∀ a ∈ H, ∀ k, ∃ i, rel a k i) {b : ℝ}
    (hcard : ∀ k, (Fintype.card (I k) : ℝ) ≤ Real.exp b) :
    ∃ (choice : ∀ k, I k) (S : Finset Ω), S ⊆ H ∧ 0 < outer.mass S ∧
      Real.exp (-b * Fintype.card K) * outer.mass H ≤ outer.mass S ∧
      ∀ a ∈ S, ∀ k, rel a k (choice k) := by
  classical
  have hHne : H.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he] at hH
    simp only [FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hH
  obtain ⟨a0, ha0⟩ := hHne
  let : ∀ k, Nonempty (I k) := fun k => ⟨(hex a0 ha0 k).choose⟩
  let code : Ω → ∀ k, I k := fun a k =>
    if ha : a ∈ H then (hex a ha k).choose else (hex a0 ha0 k).choose
  have hcode (a : Ω) (ha : a ∈ H) (k : K) : rel a k (code a k) := by
    simpa only [code, dif_pos ha] using (hex a ha k).choose_spec
  have hc : (Fintype.card (∀ k, I k) : ℝ) ≤ Real.exp (b * Fintype.card K) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    calc
      _ ≤ ∏ _k : K, Real.exp b :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun k _ => hcard k)
      _ = (Real.exp b) ^ Fintype.card K := by simp
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨choice, hchoice⟩ := outer.exists_code_fiber_mass H code
  let S := H.filter (fun a => code a = choice)
  have hmass : Real.exp (-b * Fintype.card K) * outer.mass H ≤ outer.mass S := by
    calc
      _ = outer.mass H / Real.exp (b * Fintype.card K) := by
        rw [show -b * (Fintype.card K : ℝ) = -(b * Fintype.card K) by ring,
          Real.exp_neg, div_eq_mul_inv, mul_comm]
      _ ≤ outer.mass H / Fintype.card (∀ k, I k) :=
        div_le_div_of_nonneg_left hH.le (by positivity) hc
      _ ≤ _ := hchoice
      _ = outer.mass S := by
        congr 1
        ext a
        simp only [S, Finset.mem_filter]
  refine ⟨choice, S, Finset.filter_subset _ _, (mul_pos (Real.exp_pos _) hH).trans_le hmass,
    hmass, ?_⟩
  intro a ha k
  obtain ⟨haH, he⟩ := Finset.mem_filter.mp ha
  rw [← he]
  exact hcode a haH k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BoxNiltestDetection
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem boxNiltestDetection_zero.{u,v} : BoxNiltestDetection.{u,v} 0 (fun p => 2 * p) := by
  intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT a lengths _ f hf hc
  have hb := RationalFilteredNilmanifold.Niltest.detection_step_zero_sample
    D T hT (translatedIntegerBox a lengths) id f hc
  have he : Real.exp (-p) / Real.exp p = Real.exp (-(2 * p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he] at hb
  rw [translatedIntegerBox_norm_degree_one]
  exact hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem exists_quadratic_frequency_small_difference {p : ℝ} (hp : 0 ≤ p)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hG : Real.exp (-p) ≤ gowersNorm 3 f) :
    ∃ H : Finset G, H.Nonempty ∧
      Real.exp (-(1024 * (p + 1))) * Fintype.card G ≤ (H.card : ℝ) ∧
      ∃ χ : G → AddChar G ℂ,
        (∀ h ∈ H, Real.exp (-(1024 * (p + 1))) ≤
          ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖) ∧
        ((additiveGraph H χ - additiveGraph H χ).card : ℝ) ≤
          Real.exp (1024 * (p + 1)) * H.card := by
  classical
  obtain ⟨H, hH, hdense, χ, hcorr, henergy⟩ := exists_quadratic_frequency_graph hp f hf hG
  let q := 128 * (p + 1)
  let P := 1024 * (p + 1)
  have hqP : q ≤ P := by dsimp [q, P]; linarith
  have henergy' : (Real.exp q)⁻¹ * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H χ) (additiveGraph H χ) : ℝ) := by
    rw [← Real.exp_neg]
    apply le_trans _ henergy
    gcongr
    exact_mod_cast Finset.card_le_univ H
  obtain ⟨J, hJH, hJ, hsize, hdiff⟩ :=
    exists_large_graph_subset_small_difference H hH χ (Real.exp_pos q) henergy'
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (2 : ℝ) ^ 4 ≤ Real.exp 4 := by
    calc
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) htwo 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hfourteen : (2 : ℝ) ^ 14 ≤ Real.exp 14 := by
    calc
      _ ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) htwo 14
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hnegfour : Real.exp (-4) ≤ ((2 : ℝ) ^ 4)⁻¹ := by
    simpa only [Real.exp_neg, one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 ^ 4) hfour
  have hsize' : Real.exp (-P) * Fintype.card G ≤ (J.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(2 * q + 4)) * Fintype.card G :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by dsimp [q, P]; linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-4) * (Real.exp (-q) * (Real.exp (-q) * Fintype.card G)) := by
        rw [show -(2 * q + 4) = -4 + -q + -q by ring, Real.exp_add, Real.exp_add]
        ring
      _ ≤ ((2 : ℝ) ^ 4)⁻¹ * (Real.exp (-q) * (Real.exp (-q) * Fintype.card G)) :=
        mul_le_mul_of_nonneg_right hnegfour (by positivity)
      _ ≤ ((2 : ℝ) ^ 4)⁻¹ * (Real.exp (-q) * H.card) := by
        gcongr
      _ = ((2 : ℝ) ^ 4)⁻¹ * (Real.exp q)⁻¹ * H.card := by
        rw [Real.exp_neg]
        ring
      _ ≤ _ := hsize
  refine ⟨J, hJ, hsize', χ, ?_, ?_⟩
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqP)).trans (hcorr h (hJH hh))
  · apply hdiff.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    calc
      (2 : ℝ) ^ 14 * Real.exp q ^ 6 ≤ Real.exp 14 * Real.exp q ^ 6 := by gcongr
      _ = Real.exp (6 * q + 14) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp P := Real.exp_le_exp.mpr (by dsimp [q, P]; linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicMixedReflection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_unwrapped_reflected_correlation {N : ℕ} [NeZero N] {p : ℝ}
    (hp : 0 ≤ p) (R S : ℤ → ℤ → ℂ)
    (hR : ∀ x n, ‖R x n‖ ≤ 1) (hS : ∀ y n, ‖S y n‖ ≤ 1)
    (z : ZMod N) (b : ZMod N → ℂ) (hb : ∀ x, ‖b x‖ ≤ 1)
    (hcorr : Real.exp (-p) ≤ ‖𝔼 x : ZMod N, 𝔼 y : ZMod N,
      R x.val (z - x - y).val * star (S y.val (z - x - y).val) * b x * star (b y)‖) :
    ∃ (k : Fin 3) (A B : ℤ → ℂ), (∀ n, ‖A n‖ ≤ 1) ∧ (∀ n, ‖B n‖ ≤ 1) ∧
      Real.exp (-(2 * p + 10)) ≤ ‖𝔼 x : ZMod N, 𝔼 y : ZMod N,
        R x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
          star (S y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) * A x.val * B y.val‖ := by
  let F (k : Fin 3) (x y : ZMod N) :=
    R x.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val) *
      star (S y.val ((z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val)) * b x * star (b y)
  let G (x y : ZMod N) := R x.val (z - x - y).val * star (S y.val (z - x - y).val) * b x * star (b y)
  let D (x y : ZMod N) := tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y
  have hF (k : Fin 3) (x y : ZMod N) : ‖F k x y‖ ≤ 1 := by
    simp only [F, norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb y)
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb x)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hR _ _)).trans (hS _ _)
  have hterm (k : Fin 3) (x y : ZMod N) :
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y) =
        G x y * finiteIndicator (tripleCarryInterval N k) (D x y) := by
    by_cases hk : D x y ∈ tripleCarryInterval N k
    · have hr := tripleCarry_representative z x y k hk
      simp only [finiteIndicator, if_pos hk, mul_one, F, G, hr]
    · simp only [finiteIndicator, if_neg hk, mul_zero]
  have hpoint (x y : ZMod N) :
      (∑ k : Fin 3, F k x y * finiteIndicator (tripleCarryInterval N k) (D x y)) = G x y := by
    simp_rw [hterm]
    rw [← Finset.mul_sum, sum_tripleCarry_indicator, mul_one]
  have hsum : (∑ k : Fin 3, 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y)) = 𝔼 x, 𝔼 y, G x y := by
    rw [← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl
    intro x _
    rw [← Finset.expect_sum_comm]
    exact Finset.expect_congr rfl (fun y _ => hpoint x y)
  obtain ⟨k, hk⟩ := exists_large_weighted_term (fun _ : Fin 3 => (1 : ℂ))
    (fun k => 𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F k x y * finiteIndicator (tripleCarryInterval N k) (D x y))
    (Real.exp_pos (-p)) (by norm_num : (0 : ℝ) < 3) (by norm_num)
    (by simpa only [one_mul, hsum, G] using hcorr)
  have hρ1 : Real.exp (-p) / 3 ≤ 1 := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp)
    linarith
  obtain ⟨χ, hχ⟩ := exists_remove_triple_interval z (tripleCarryStart N k) N (F k) (hF k)
    (by positivity : 0 < Real.exp (-p) / 3) hρ1 hk
  let A (n : ℤ) := b (n : ZMod N) * star (χ (n : ZMod (3 * N)))
  let B (n : ℤ) := star (b (n : ZMod N)) * star (χ (n : ZMod (3 * N)))
  have hA (n : ℤ) : ‖A n‖ ≤ 1 := by
    simpa only [A, norm_mul, norm_star, AddChar.norm_apply, mul_one] using hb (n : ZMod N)
  have hB (n : ℤ) : ‖B n‖ ≤ 1 := by
    simpa only [B, norm_mul, norm_star, AddChar.norm_apply, mul_one] using hb (n : ZMod N)
  have hAe (x : ZMod N) : A (x.val : ℤ) = b x * star (χ (tripleCyclicEmbed x)) := by
    simp [A, tripleCyclicEmbed]
  have hBe (y : ZMod N) : B (y.val : ℤ) = star (b y) * star (χ (tripleCyclicEmbed y)) := by
    simp [B, tripleCyclicEmbed]
  have htwo : Real.exp (-p) ^ 2 = Real.exp (-(2 * p)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hthreshold : (Real.exp (-p) / 3) ^ 2 / 48 = Real.exp (-(2 * p)) / 432 := by
    rw [div_pow, htwo]
    ring
  have h432 : (432 : ℝ) ≤ Real.exp 10 :=
    (by norm_num : (432 : ℝ) ≤ 2 ^ 10).trans (two_pow_le_exp_of_le 10 le_rfl)
  have hsmall : Real.exp (-(2 * p + 10)) ≤ (Real.exp (-p) / 3) ^ 2 / 48 := by
    rw [hthreshold]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 432)).mpr
    calc
      _ ≤ Real.exp (-(2 * p + 10)) * Real.exp 10 :=
        mul_le_mul_of_nonneg_left h432 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨k, A, B, hA, hB, ?_⟩
  simpa only [F, hAe, hBe, mul_assoc, mul_comm, mul_left_comm] using hsmall.trans hχ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SampledDenseCommonBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_dense_common_sampled_box {Ω T X I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype T] [Nonempty T] [Fintype I] [DecidableEq I]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    (e : T → I → ℤ) (he : Function.Injective e) {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ)
    (hslice : ∀ z j, IsDenseCommonStrideBox N p ((S z j).image e))
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    {α ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hlarge : ε + Fintype.card I * Real.exp (-p) + ρ < α)
    (hsmall : Fintype.card I * Real.exp (-p) ≤ 1)
    (hmean : α ≤ sampledSliceSeminorm μ F S w v) :
    ∃ A : Finset T, A.Nonempty ∧ IsDenseCommonStrideBox N (p + 1) (A.image e) ∧
      ∃ G : Finset Ω, ∃ j : ∀ z, J z,
        Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) *
          (α - ε - Fintype.card I * Real.exp (-p) - ρ) ≤ μ.mass G ∧
        ∀ z ∈ G, A ⊆ S z (j z) ∧
          2 * (1 - (A.card : ℝ) / (S z (j z)).card) ≤ Fintype.card I * Real.exp (-p) ∧
          ρ ≤ ‖𝔼 t ∈ A, v (F z t) * w z (j z) t‖ := by
  obtain ⟨A, hAn, hshape, G, j, hmass, hlocal⟩ := exists_common_sampled_box μ F S w e he hp N
    hslice hw v hv hε hρ hlarge hmean
  have hpos : 0 < μ.mass G := lt_of_lt_of_le (mul_pos (Real.exp_pos _) (by linarith)) hmass
  have hGn : G.Nonempty := by
    by_contra h
    have hz : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hz, FiniteProbabilityWeights.mass, Finset.sum_empty] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨z, hz⟩ := hGn
  refine ⟨A, hAn, ?_, G, j, hmass, hlocal⟩
  apply (hslice z (j z)).of_large_subbox hshape (Finset.image_subset_image (hlocal z hz).1)
  simpa only [Finset.card_image_of_injective _ he] using ((hlocal z hz).2.1.trans hsmall)

theorem exists_dense_common_sampled_box_of_seminorm {Ω T X I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype T] [Nonempty T] [Fintype I] [DecidableEq I]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    (e : T → I → ℤ) (he : Function.Injective e) {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ)
    (hslice : ∀ z j, IsDenseCommonStrideBox N p ((S z j).image e))
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    {α : ℝ} (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card I * Real.exp (-p) ≤ α / 8)
    (hmean : α ≤ sampledSliceSeminorm μ F S w v) :
    ∃ A : Finset T, A.Nonempty ∧ IsDenseCommonStrideBox N (p + 1) (A.image e) ∧
      ∃ G : Finset Ω, ∃ j : ∀ z, J z,
        Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) * (α / 2) ≤ μ.mass G ∧
        ∀ z ∈ G, A ⊆ S z (j z) ∧ α / 4 ≤ ‖𝔼 t ∈ A, v (F z t) * w z (j z) t‖ := by
  obtain ⟨A, hAn, hAdense, G, j, hmass, hlocal⟩ := exists_dense_common_sampled_box μ F S w
    e he hp N hslice hw v hv (show 0 < α / 8 by positivity) (show 0 ≤ α / 4 by positivity)
    (show α / 8 + Fintype.card I * Real.exp (-p) + α / 4 < α by linarith)
    (show Fintype.card I * Real.exp (-p) ≤ 1 by linarith) hmean
  refine ⟨A, hAn, hAdense, G, j, ?_, fun z hz => ⟨(hlocal z hz).1, (hlocal z hz).2.2⟩⟩
  exact (mul_le_mul_of_nonneg_left (by linarith : α / 2 ≤
    α - α / 8 - Fintype.card I * Real.exp (-p) - α / 4) (Real.exp_nonneg _)).trans hmass

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorNativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem generalResources_bounds_of_list
    {r : PreparedModularCanonicalDetectorResources ℝ} {budget : ℝ}
    (h : ∀ x ∈ r.toList, x ∈ Set.Icc 0 budget) : r.Bounds budget := by
  constructor <;> apply h <;>
    simp only [PreparedModularCanonicalDetectorResources.toList, List.mem_cons] <;> tauto

theorem natMv_eval_nonneg {ι : Type*} (p : MvPolynomial ι ℕ)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ p.eval₂ (Nat.castRingHom ℝ) x := by
  induction p using MvPolynomial.induction_on with
  | C n => simp only [MvPolynomial.eval₂_C]; exact Nat.cast_nonneg _
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using add_nonneg hp hq
  | mul_X p i hp =>
    simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using mul_nonneg hp (hx i)

theorem natMv_eval_mono {ι : Type*} (p : MvPolynomial ι ℕ)
    {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    p.eval₂ (Nat.castRingHom ℝ) x ≤ p.eval₂ (Nat.castRingHom ℝ) y := by
  have hy (i) : 0 ≤ y i := (hx i).trans (hxy i)
  induction p using MvPolynomial.induction_on with
  | C n => simp only [MvPolynomial.eval₂_C, le_refl]
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using add_le_add hp hq
  | mul_X p i hp =>
    simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using
      mul_le_mul hp (hxy i) (hx i) (natMv_eval_nonneg p hy)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchFiniteCoordinateReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def RelativePatchFinInductionRule (s n₀ stage : ℕ) (τ : ℝ)
    (cutoff cost : ℝ → ℝ) : Prop :=
  ∀ (p a Λ : ℝ) (d₀ : ℕ), 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
    RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
    ∀ (n : ℕ), 0 < n → (n : ℝ) ≤ p →
      ∀ (N : Fin n → ℕ), (∀ i, Real.exp (cutoff p) ≤ (N i : ℝ)) →
      ∀ (f : (Fin n → ℤ) → ℝ),
        (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
        ∀ (d : ℕ) (A : PolynomialPatch (Fin n) s d),
          relativePatchComplexity A ≤ p → relativePatchDistinctWeights A ≤ stage →
          Real.exp (-p) ≤ relativePatchBoxScore N f a A →
          RelativePatchSliceConclusion s N f ((1 - τ) ^ (stage + 1) * Λ)
            (d₀ + s * d) (cost p)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem slicedGridSiteLog_eval (n d ta ti : ℕ) (D p E : Polynomial ℕ) (x : ℝ) :
    (slicedGridSiteLog n d ta ti D p E).eval₂ (Nat.castRingHom ℝ) x =
      slicedGridSiteLog n d ta ti (D.eval₂ (Nat.castRingHom ℝ) x)
        (p.eval₂ (Nat.castRingHom ℝ) x) (E.eval₂ (Nat.castRingHom ℝ) x) := by
  simp [slicedGridSiteLog, positiveRetainedComplexityLog, positiveRetainedDenominatorLog, positiveSpectrumCardLog, positiveRetainedFrequencyLog, positiveRetainedBiasLog, positiveModerateAccuracyLog, positiveModerateSpectrumLog, positiveModerateCoverLog, positiveModerateLengthLog, uniformSpectrumCardLog, uniformRetainedFrequencyLog, uniformRetainedDenominatorLog, uniformRetainedBiasLog, uniformSpectrumSizeLog, uniformBlockAccuracyLog, majorArcSpectrumLog, majorArcCoverLog, majorArcErrorLog, majorArcLengthLog, majorArcLocalizationLog, majorArcBiasLog, Polynomial.eval₂_pow]

theorem exists_slicedGridSiteLog_uniform_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p E : ℝ}, 0 ≤ D → 0 ≤ p → 0 ≤ E → ∀ j : Fin m,
      slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
        ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
        ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) D p E ≤
        (D + p + E + A) ^ A := by
  classical
  let Lj := fun (j : Fin m) (D p E : Polynomial ℕ) => slicedGridSiteLog j.val
    (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
    ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
    ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) D p E
  let poly := ∑ j : Fin m, Lj j Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D p E hD hp hE j
  let R := D + p + E
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply (slicedGridSiteLog_mono _ _ _ _ hD hp hE
    (by dsimp [R]; linarith : D ≤ R) (by dsimp [R]; linarith : p ≤ R)
    (by dsimp [R]; linarith : E ≤ R)).trans
  apply le_trans ?_ (hbound R hR)
  have heval (j : Fin m) : (Lj j Polynomial.X Polynomial.X Polynomial.X).eval₂ (Nat.castRingHom ℝ) R =
      slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
        ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
        ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) R R R := by
    simp only [Lj, slicedGridSiteLog_eval, Polynomial.eval₂_X]
  simp only [poly, Polynomial.eval₂_finsetSum, heval]
  apply Finset.single_le_sum ?_ (Finset.mem_univ j)
  intro i _
  exact (slicedGridSiteLog_bounds _ _ _ _ hR hR hR).1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridResourceBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem exists_allocatedSlicedGridResource_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p v E : ℝ}, 0 ≤ D → 0 ≤ p → 0 ≤ v → 0 ≤ E →
      allocatedSlicedGridResourceLog m dim D p v E ≤ (D + p + v + E + A) ^ A := by
  obtain ⟨b, hb, hsite⟩ := exists_slicedGridSiteLog_uniform_budget m dim
  let X : Polynomial ℕ := Polynomial.X
  let Cp : Polynomial ℕ := (m : Polynomial ℕ) * ((X + Polynomial.C b) ^ b + X * (X + 1))
  let Epoly := uniformProductAccuracyLog X Cp X + X * (X + 1) + 1
  let poly : Polynomial ℕ := (m : Polynomial ℕ) *
    (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) ((2 * X + Epoly + Polynomial.C b) ^ b) + (X + 1) ^ 2)
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D p v E hD hp hv hE
  let R := D + p + v + E
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hER : E ≤ R := by dsimp [R]; linarith
  let L := fun (j : Fin m) (e : ℝ) => slicedGridSiteLog j.val
    (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
    ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
    ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) D p e
  have hL0 (j : Fin m) : L j 0 ≤ (R + b) ^ b :=
    (hsite hD hp (le_refl (0 : ℝ)) j).trans
      (pow_le_pow_left₀ (by positivity) (by dsimp [R]; linarith) b)
  let Cbound := (m : ℝ) * ((R + b) ^ b + R * (R + 1))
  have hCb : 0 ≤ Cbound := by dsimp [Cbound]; positivity
  have hCp0 : 0 ≤ ∑ j : Fin m, (L j 0 + D * (v + 1)) :=
    Finset.sum_nonneg (fun j _ => add_nonneg (slicedGridSiteLog_bounds _ _ _ _ hD hp (le_refl 0)).1 (by positivity))
  have hCp : (∑ j : Fin m, (L j 0 + D * (v + 1))) ≤ Cbound := by
    calc
      _ ≤ ∑ _j : Fin m, ((R + b) ^ b + R * (R + 1)) := Finset.sum_le_sum (fun j _ => by
        apply add_le_add (hL0 j)
        exact mul_le_mul hDR (add_le_add hvR le_rfl) (by positivity) hR)
      _ = _ := by simp [Cbound, mul_add]
  let E' := uniformProductAccuracyLog D (∑ j, (L j 0 + D * (v + 1))) E + D * (v + 1) + 1
  let Ebound := uniformProductAccuracyLog R Cbound R + R * (R + 1) + 1
  have hE' : 0 ≤ E' := by
    dsimp only [E']
    exact add_nonneg (add_nonneg (uniformProductAccuracyLog_nonneg hD hCp0 hE) (by positivity)) zero_le_one
  have hEb : 0 ≤ Ebound := by
    dsimp only [Ebound]
    exact add_nonneg (add_nonneg (uniformProductAccuracyLog_nonneg hR hCb hR) (by positivity)) zero_le_one
  have hEbound : E' ≤ Ebound := by
    dsimp only [E', Ebound, uniformProductAccuracyLog]
    gcongr
  have hL (j : Fin m) : L j E' ≤ (2 * R + Ebound + b) ^ b :=
    (hsite hD hp hE' j).trans (pow_le_pow_left₀ (by positivity)
      (by linarith only [hDR, hpR, hEbound]) b)
  have htotal : allocatedSlicedGridResourceLog m dim D p v E ≤
      (m : ℝ) * (siteExponentialOutputLog (Fintype.card (Finset (Fin dim)))
        ((2 * R + Ebound + b) ^ b) + (R + 1) ^ 2) := by
    change (∑ j : Fin m, (siteExponentialOutputLog _ (L j E') + (D + 1) * (v + 1))) ≤ _
    calc
      _ ≤ ∑ _j : Fin m, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim)))
          ((2 * R + Ebound + b) ^ b) + (R + 1) ^ 2) := Finset.sum_le_sum (fun j _ => by
        apply add_le_add
        · unfold siteExponentialOutputLog
          gcongr
          all_goals exact hL j
        · rw [pow_two]
          exact mul_le_mul (add_le_add hDR le_rfl) (add_le_add hvR le_rfl) (by positivity) (by positivity))
      _ = _ := by simp [mul_add]
  apply htotal.trans
  simpa [poly, X, Epoly, Cp, Ebound, Cbound, uniformProductAccuracyLog,
    siteExponentialOutputLog, Polynomial.eval₂_pow] using hbound R hR

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineAnalyticBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_allocatedAffineModelMass_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p v F Prho Pk target : ℝ},
      0 ≤ D → 0 ≤ p → 0 ≤ v → 0 ≤ F → 0 ≤ Prho → 0 ≤ Pk → 0 ≤ target →
      ∀ (outputs axes gridaxes ambient : ℕ),
      (outputs : ℝ) ≤ D → (axes : ℝ) ≤ D → (gridaxes : ℝ) ≤ D → (ambient : ℝ) ≤ D →
      (dim : ℝ) ≤ D → (probabilityProfileLipschitz : ℝ) ≤ D →
      let Eg := outputs * Prho + (target + F) + 1
      let Op := allocatedSlicedGridResourceLog m dim D p v Eg
      let Plong := ((m : ℝ) + 2) * dim + m + 4 + Prho + axes * max Op 0 + (target + F) + 2
      let Q := idealSiteLogBudget outputs dim Plong
      2 * (2 : ℝ) ^ dim + F + (2 : ℝ) ^ dim * (ambient * ((m + 1 : ℕ) * Pk)) +
        ((2 : ℝ) ^ dim * axes * (4 * Q + 8) + Q) + gridaxes * Op ≤
        (D + p + v + F + Prho + Pk + target + A) ^ A := by
  obtain ⟨b, hb, hgrid⟩ := exists_allocatedSlicedGridResource_budget m dim
  let X : Polynomial ℕ := Polynomial.X
  let O : Polynomial ℕ := (3 * X + (X ^ 2 + 2 * X + 1) + Polynomial.C b) ^ b
  let Pbox : Polynomial ℕ := Polynomial.C ((m + 2) * dim + m + 4)
  let Pl : Polynomial ℕ := Pbox + X + X * O + 2 * X + 2
  let Qp := allocatedFiniteIdealProfileLog X Pl
  let poly : Polynomial ℕ := 2 * (2 : Polynomial ℕ) ^ dim + X + (2 : Polynomial ℕ) ^ dim *
    (X * ((m + 1 : ℕ) * X)) + ((2 : Polynomial ℕ) ^ dim * X * (4 * Qp + 8) + Qp) + X * O
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D p v F Prho Pk target hD hp hv hF hPrho hPk htarget outputs axes gridaxes ambient
    hout haxes hgridaxes hamb hdim hprofile Eg Op Plong Q
  let R := D + p + v + F + Prho + Pk + target
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hFR : F ≤ R := by dsimp [R]; linarith
  have hPrhoR : Prho ≤ R := by dsimp [R]; linarith
  have hPkR : Pk ≤ R := by dsimp [R]; linarith
  have htR : target ≤ R := by dsimp [R]; linarith
  have hEg : 0 ≤ Eg := by dsimp [Eg]; positivity
  have hEgR : Eg ≤ R ^ 2 + 2 * R + 1 := by
    have hprod := mul_le_mul (hout.trans hDR) hPrhoR hPrho hR
    dsimp only [Eg]
    nlinarith only [hprod, htR, hFR]
  let Ob := (3 * R + (R ^ 2 + 2 * R + 1) + b) ^ b
  have hOb : 0 ≤ Ob := by dsimp [Ob]; positivity
  have hOp : 0 ≤ Op := allocatedSlicedGridResourceLog_nonneg m dim hD hp hv hEg
  have hOpR : Op ≤ Ob := (hgrid hD hp hv hEg).trans
    (pow_le_pow_left₀ (by positivity) (by linarith only [hDR, hpR, hvR, hEgR]) b)
  let Plb := (((m + 2) * dim + m + 4 : ℕ) : ℝ) + R + R * Ob + 2 * R + 2
  have hPlb : 0 ≤ Plb := by dsimp [Plb]; positivity
  have hPl : 0 ≤ Plong := by dsimp [Plong]; positivity
  have hPlR : Plong ≤ Plb := by
    have hm : (axes : ℝ) * max Op 0 ≤ R * Ob := by
      rw [max_eq_left hOp]
      exact mul_le_mul (haxes.trans hDR) hOpR hOp hR
    dsimp only [Plong, Plb]
    push_cast
    linarith only [hPrhoR, htR, hFR, hm]
  let Qb := allocatedFiniteIdealProfileLog R Plb
  have hQb : 0 ≤ Qb := (allocatedFiniteIdeal_budget_nonneg m hR hPlb (le_refl (0 : ℝ))).1
  have hQ : 0 ≤ Q := (idealSiteLogBudget_bounds outputs dim hPl).1
  have hQR : Q ≤ Qb := by
    apply (idealSiteLogBudget_le_finite_profile hPl hout hdim hprofile).trans
    change allocatedFiniteIdealProfileLog D Plong ≤ allocatedFiniteIdealProfileLog R Plb
    unfold allocatedFiniteIdealProfileLog
    gcongr
  have hmass : 2 * (2 : ℝ) ^ dim + F + (2 : ℝ) ^ dim * (ambient * ((m + 1 : ℕ) * Pk)) +
      ((2 : ℝ) ^ dim * axes * (4 * Q + 8) + Q) + gridaxes * Op ≤
      2 * (2 : ℝ) ^ dim + R + (2 : ℝ) ^ dim * (R * ((m + 1 : ℕ) * R)) +
      ((2 : ℝ) ^ dim * R * (4 * Qb + 8) + Qb) + R * Ob := by
    gcongr
    · exact hamb.trans hDR
    · exact haxes.trans hDR
    · exact hgridaxes.trans hDR
  apply hmass.trans
  simpa [poly, X, O, Pbox, Pl, Qp, Ob, Plb, Qb, allocatedFiniteIdealProfileLog,
    Polynomial.eval₂_pow] using hbound R hR

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem exists_allocatedAffineAnalytic_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p v F Prho Pk target B : ℝ},
      0 ≤ D → 0 ≤ p → 0 ≤ v → 0 ≤ F → 0 ≤ Prho → 0 ≤ Pk → 0 ≤ target → 0 ≤ B →
      ∀ (outputs axes : ℕ), (outputs : ℝ) ≤ D → (axes : ℝ) ≤ D →
      (dim : ℝ) ≤ D → (probabilityProfileLipschitz : ℝ) ≤ D →
      let Eg := outputs * Prho + (target + F) + 1
      let Op := allocatedSlicedGridResourceLog m dim D p v Eg
      let Plong := ((m : ℝ) + 2) * dim + m + 4 + Prho + axes * max Op 0 + (target + F) + 2
      let Q := idealSiteLogBudget outputs dim Plong
      10 * B + 6 * Q + 2 * ((m + 1 : ℕ) * Pk) + (2 * B + 1) * Op + 19 ≤
        (D + p + v + F + Prho + Pk + target + B + A) ^ A := by
  obtain ⟨b, hb, hgrid⟩ := exists_allocatedSlicedGridResource_budget m dim
  let X : Polynomial ℕ := Polynomial.X
  let O : Polynomial ℕ := (3 * X + (X ^ 2 + 2 * X + 1) + Polynomial.C b) ^ b
  let Pbox : Polynomial ℕ := Polynomial.C ((m + 2) * dim + m + 4)
  let Pl : Polynomial ℕ := Pbox + X + X * O + 2 * X + 2
  let Qp := allocatedFiniteIdealProfileLog X Pl
  let poly : Polynomial ℕ := 10 * X + 6 * Qp + 2 * ((m + 1 : ℕ) * X) + (2 * X + 1) * O + 19
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D p v F Prho Pk target B hD hp hv hF hPrho hPk htarget hB outputs axes
    hout haxes hdim hprofile Eg Op Plong Q
  let R := D + p + v + F + Prho + Pk + target + B
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hBR : B ≤ R := by dsimp [R]; linarith
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hFR : F ≤ R := by dsimp [R]; linarith
  have hPrhoR : Prho ≤ R := by dsimp [R]; linarith
  have hPkR : Pk ≤ R := by dsimp [R]; linarith
  have htR : target ≤ R := by dsimp [R]; linarith
  have hEg : 0 ≤ Eg := by dsimp [Eg]; positivity
  have hEgR : Eg ≤ R ^ 2 + 2 * R + 1 := by
    have hprod := mul_le_mul (hout.trans hDR) hPrhoR hPrho hR
    dsimp only [Eg]
    nlinarith only [hprod, htR, hFR]
  let Ob := (3 * R + (R ^ 2 + 2 * R + 1) + b) ^ b
  have hOb : 0 ≤ Ob := by dsimp [Ob]; positivity
  have hOp : 0 ≤ Op := allocatedSlicedGridResourceLog_nonneg m dim hD hp hv hEg
  have hOpR : Op ≤ Ob := (hgrid hD hp hv hEg).trans
    (pow_le_pow_left₀ (by positivity) (by linarith only [hDR, hpR, hvR, hEgR]) b)
  let Plb := (((m + 2) * dim + m + 4 : ℕ) : ℝ) + R + R * Ob + 2 * R + 2
  have hPlb : 0 ≤ Plb := by dsimp [Plb]; positivity
  have hPl : 0 ≤ Plong := by dsimp [Plong]; positivity
  have hPlR : Plong ≤ Plb := by
    have hm : (axes : ℝ) * max Op 0 ≤ R * Ob := by
      rw [max_eq_left hOp]
      exact mul_le_mul (haxes.trans hDR) hOpR hOp hR
    dsimp only [Plong, Plb]
    push_cast
    linarith only [hPrhoR, htR, hFR, hm]
  let Qb := allocatedFiniteIdealProfileLog R Plb
  have hQb : 0 ≤ Qb := (allocatedFiniteIdeal_budget_nonneg m hR hPlb (le_refl (0 : ℝ))).1
  have hQ : 0 ≤ Q := (idealSiteLogBudget_bounds outputs dim hPl).1
  have hQR : Q ≤ Qb := by
    apply (idealSiteLogBudget_le_finite_profile hPl hout hdim hprofile).trans
    change allocatedFiniteIdealProfileLog D Plong ≤ allocatedFiniteIdealProfileLog R Plb
    unfold allocatedFiniteIdealProfileLog
    gcongr
  have hcost : 10 * B + 6 * Q + 2 * ((m + 1 : ℕ) * Pk) + (2 * B + 1) * Op + 19 ≤
      10 * R + 6 * Qb + 2 * ((m + 1 : ℕ) * R) + (2 * R + 1) * Ob + 19 := by
    gcongr
  apply hcost.trans
  simpa [poly, X, O, Pbox, Pl, Qp, Ob, Plb, Qb, allocatedFiniteIdealProfileLog,
    Polynomial.eval₂_pow] using hbound R hR

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction
namespace OAI

section

namespace Erdos3

open scoped Classical

def RelativePatchFinPowerInductionRule (s n₀ stage : ℕ) (discount : ℝ)
    (power : ℕ) : Prop :=
  RelativePatchFinInductionRule s n₀ stage discount
    (fun p => (p + 2) ^ power) (fun p => (p + 2) ^ power)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeResetBracketGeometry
namespace OAI

section

namespace Erdos3

open Module

namespace RationalFilteredNilmanifold

variable {κ L M : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d f : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (Fmark : RationalFilteredNilmanifold M t f) (c : Basis κ ℚ M)

theorem nativeResetBracketGeometry {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hF : Fmark.GeometryComplexityLE p)
    (hc : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p) :
    (d : ℝ) ≤ p ∧ (Fintype.card κ : ℝ) ≤ p ∧
    (∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k)
      (nativeResetBracketHeight p)) ∧
    (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k)
      (nativeResetBracketHeight p)) := by
  obtain ⟨hdim, _, hbracket⟩ := Fmark.basis_geometry_of_forward_height c hp hF
    (fun i j => (hc i j).trans (by linarith))
  exact ⟨hD.1, hdim,
    fun i j k => rationalHeightLE_ceil_exp
      ((hD.2.2.1 i j k).trans (nativeResetBracketLog_ge_input hp)),
    fun i j k => rationalHeightLE_ceil_exp (hbracket i j k)⟩

theorem nativeResetBracketGeometry_of_height {p : ℝ} {H : ℕ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hF : Fmark.GeometryComplexityLE p)
    (hc : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p)
    (hH : nativeResetBracketHeight p ≤ H) :
    (d : ℝ) ≤ p ∧ (Fintype.card κ : ℝ) ≤ p ∧
    (∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k) H) ∧
    (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) := by
  obtain ⟨hd, hf, hbracketD, hbracketF⟩ := D.nativeResetBracketGeometry Fmark c hp hD hF hc
  exact ⟨hd, hf, fun i j k => (hbracketD i j k).mono hH,
    fun i j k => (hbracketF i j k).mono hH⟩

theorem nativeResetBracketGeometry_of_logBudget {p q : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hF : Fmark.GeometryComplexityLE p)
    (hc : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p)
    (hbudget : (p + 4) ^ 11 ≤ q) :
    1 ≤ ⌈Real.exp q⌉₊ ∧ (⌈Real.exp q⌉₊ : ℝ) ≤ Real.exp (q + 1) ∧
    (d : ℝ) ≤ p ∧ (Fintype.card κ : ℝ) ≤ p ∧
    (∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k) ⌈Real.exp q⌉₊) ∧
    (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) ⌈Real.exp q⌉₊) := by
  refine ⟨one_le_ceil_exp _, ceil_exp_le_exp_add_one ?_,
    D.nativeResetBracketGeometry_of_height Fmark c hp hD hF hc ?_⟩
  · exact (show 0 ≤ (p + 4) ^ 11 by positivity).trans hbudget
  · exact Nat.ceil_mono (Real.exp_le_exp.mpr hbudget)

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PrecenterForecastNativePartners
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_fixed_linear_model_partners_of_pointwise_error
    {Ω K V : Type*} {I : K → Type*}
    [Fintype Ω] [Fintype K] [∀ k, Fintype (I k)] [∀ k, Nonempty (I k)]
    [AddCommGroup V] [Module ℂ V]
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (v e : K → V) (Q : ∀ k, I k → V) (c : ∀ k, I k → ℂ)
    (test : Ω → K → V →ₗ[ℂ] ℂ)
    (hmodel : ∀ k, v k = (∑ i, c k i • Q k i) + e k)
    {delta M : ℝ} (hdelta : 0 < delta) (hM : 0 < M)
    (hc : ∀ k, (∑ i, ‖c k i‖) ≤ M)
    (herr : ∀ a ∈ productive, ∀ k, ‖test a k (e k)‖ ≤ delta / 2)
    (hscore : ∀ a ∈ productive, ∀ k, delta ≤ ‖test a k (v k)‖) :
    ∃ (partner : ∀ k, I k) (retained : Finset Ω),
      retained ⊆ productive ∧
      outer.mass productive / (∏ k, (Fintype.card (I k) : ℝ)) ≤ outer.mass retained ∧
      ∀ a ∈ retained, ∀ k, delta / (2 * M) ≤ ‖test a k (Q k (partner k))‖ := by
  have hex (a : Ω) (ha : a ∈ productive) (k : K) :
      ∃ i, delta / (2 * M) ≤ ‖test a k (Q k i)‖ :=
    exists_linear_model_partner (test a k) (v k) (e k) (Q k) (c k) (hmodel k)
      hdelta hM (hc k) (herr a ha k) (hscore a ha k)
  let choice : Ω → ∀ k, I k := fun a k =>
    if ha : a ∈ productive then Classical.choose (hex a ha k)
    else Classical.choice inferInstance
  have hchoice (a : Ω) (ha : a ∈ productive) (k : K) :
      delta / (2 * M) ≤ ‖test a k (Q k (choice a k))‖ := by
    dsimp only [choice]
    rw [dif_pos ha]
    exact Classical.choose_spec (hex a ha k)
  obtain ⟨partner, hmass⟩ := outer.exists_code_fiber_mass productive choice
  refine ⟨partner, productive.filter (fun a => choice a = partner),
    Finset.filter_subset _ _, ?_, ?_⟩
  · rw [Fintype.card_pi, Nat.cast_prod] at hmass
    convert hmass using 1
    congr 1
    ext a
    simp only [Finset.mem_filter]
  · intro a ha k
    obtain ⟨hap, heq⟩ := Finset.mem_filter.mp ha
    rw [← heq]
    exact hchoice a hap k

end Erdos3

end

end OAI
end


