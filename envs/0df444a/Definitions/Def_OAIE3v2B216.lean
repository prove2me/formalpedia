-- Prove2me | Definitions.Def_OAIE3v2B216
-- name    : OAIE3v2B216
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:28:06.652383+00:00
-- url     : https://prove2.me/theorems/579a087b-750d-4a2d-8b12-8585d9f6e67f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 220 of 311
-- statement:
--   Definitions bundle 220 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B178`, `OAIE3v2B299`, `OAIE3v2B180`, `OAIE3v2B185`, `OAIE3v2B188`, `OAIE3v2B189`, `OAIE3v2B191`, `OAIE3v2B192`, `OAIE3v2B193`, `OAIE3v2B194`, `OAIE3v2B195`, `OAIE3v2B300` of this split.
--
--   Modules: `Dynamics/AllocatedProductRadiusBudget.lean`, `Estimates/AllocatedCanonicalNormalizer.lean`, `Estimates/AllocatedCenteredNarrowAmplitudeNormalization.lean`, `Estimates/AllocatedCenteredNarrowPrescribedMarginal.lean`, `Estimates/AllocatedFixedScaleJointMarginal.lean`, `Estimates/AllocatedProductIdealCutoff.lean`, `Estimates/AllocatedProductPrefactorMasks.lean`, `Estimates/AllocatedProfileDimensions.lean`, `Estimates/AllocatedRecenteredIdealError.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/CorrelatingVerticalPair.lean`, `Estimates/NativeCommonModelQuadruples.lean`, `Estimates/NormalizedTwistSliceVariationPairCorrelation.lean`, `Estimates/PhysicalSingleSiteCommonCover.lean`, `Estimates/PreparedUniformEarlyRadiusWithCutoff.lean`, `Fourier/QuadraticFrequencyCoordinates.lean`, `Fourier/QuadraticLocalFrequency.lean`, `Geometry/AllocatedFullSiteSupport.lean`, `Geometry/AllocatedInactiveSupportBudget.lean`, `Geometry/AllocatedMaskedChartProduct.lean`, `Geometry/AllocatedRowSlicedIdealCoordinates.lean`, `Geometry/SmallDifferenceGraphCoordinates.lean`, `Lattices/SelectedResidueCutoffDomination.lean`, `Linear/AllocatedModularRankCongruenceOutput.lean`, `Linear/VaryingRankFixedPatchFunction.lean`, `Polynomial/OrdinaryPolynomialPhaseAffineInverse.lean`, `Probability/AllocatedZeroLayerLaw.lean`, `Probability/PreparedModularGeneralCenteredLaw.lean`, `Sampling/AllocatedExternalCandidateSamplerFamily.lean`, `Sampling/AllocatedFixedScaleProductiveNarrowSampler.lean`, `Sampling/AllocatedFullGridChartModelMeasurable.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B178
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B185
import Definitions.Def_OAIE3v2B188
import Definitions.Def_OAIE3v2B189
import Definitions.Def_OAIE3v2B191
import Definitions.Def_OAIE3v2B192
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B194
import Definitions.Def_OAIE3v2B195
import Definitions.Def_OAIE3v2B300

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.VaryingRankFixedPatchFunction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_patch_rank_weight_class {X H : Type*} [Fintype H]
    (outer : FiniteProbabilityWeights H) (productive : Finset H)
    {s D : ℕ} (d : H → ℕ) (P : ∀ h, PolynomialPatch X s (d h))
    (hd : ∀ h, d h ≤ D) (hproductive : 0 < outer.mass productive) :
    ∃ (h₀ : H) (retained : Finset H), h₀ ∈ retained ∧ retained ⊆ productive ∧
      outer.mass productive / ((D + 1 : ℕ) * (s + 1) ^ D : ℕ) ≤ outer.mass retained ∧
      ∀ h ∈ retained, ∃ heq : d h = d h₀, ((P h).castRank heq).weight = (P h₀).weight := by
  let code := fun h => (P h).rankWeightCode D (hd h)
  obtain ⟨c, hc⟩ := outer.exists_code_fiber_mass productive code
  let retained := productive.filter (fun h => code h = c)
  have hmass : outer.mass productive / ((D + 1 : ℕ) * (s + 1) ^ D : ℕ) ≤
      outer.mass retained := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at hc
    convert hc using 1
    congr 1
    ext h
    simp only [retained, Finset.mem_filter]
  have hretained : 0 < outer.mass retained :=
    (div_pos hproductive (by positivity)).trans_le hmass
  have hnonempty : retained.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    simp only [hempty, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hretained
  obtain ⟨h₀, hh₀⟩ := hnonempty
  refine ⟨h₀, retained, hh₀, Finset.filter_subset _ _, hmass, ?_⟩
  intro h hh
  apply PolynomialPatch.rankWeightCode_eq (P h) (P h₀) (hd h) (hd h₀)
  exact (Finset.mem_filter.mp hh).2.trans (Finset.mem_filter.mp hh₀).2.symm

theorem exists_common_rank_weight_patch_family {X H : Type*} [Fintype H]
    (outer : FiniteProbabilityWeights H) (productive : Finset H)
    {s D : ℕ} (d : H → ℕ) (P : ∀ h, PolynomialPatch X s (d h))
    (hd : ∀ h, d h ≤ D) (hproductive : 0 < outer.mass productive)
    (L : ℝ) (hL : ∀ h, ((P h).kernel.lip : ℝ) ≤ L) :
    ∃ (d₀ : ℕ) (w : Fin d₀ → ℕ) (A : H → PolynomialSlots X d₀ w)
      (Φ : H → PatchKernel d₀) (retained : Finset H),
      d₀ ≤ D ∧ Monotone w ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
      retained ⊆ productive ∧
      outer.mass productive / ((D + 1 : ℕ) * (s + 1) ^ D : ℕ) ≤ outer.mass retained ∧
      (∀ h, ((Φ h).lip : ℝ) ≤ L) ∧
      (∀ h ∈ retained, (Φ h).lip = (P h).kernel.lip) ∧
      ∀ h ∈ retained, ∀ t : X → ℝ, ((A h).slots t).patchValue (Φ h) = (P h).value t := by
  obtain ⟨h₀, retained, hh₀, hsub, hmass, hshape⟩ :=
    exists_patch_rank_weight_class outer productive d P hd hproductive
  let chooseIndex := fun h => if h ∈ retained then h else h₀
  have hmem (h) : chooseIndex h ∈ retained := by
    dsimp only [chooseIndex]
    split_ifs with hh
    · exact hh
    · exact hh₀
  choose rankEq weightEq using fun h => hshape (chooseIndex h) (hmem h)
  let patch := fun h => (P (chooseIndex h)).castRank (rankEq h)
  let A := fun h => (patch h).formAtWeight (P h₀).weight (weightEq h)
  let Φ := fun h => (patch h).kernel
  have hchoose (h) (hh : h ∈ retained) : chooseIndex h = h := by
    exact if_pos hh
  refine ⟨d h₀, (P h₀).weight, A, Φ, retained, hd h₀, (P h₀).weight_mono,
    (P h₀).weight_pos, (P h₀).weight_le, hsub, hmass, ?_, ?_, ?_⟩
  · intro h
    simpa only [Φ, patch, PolynomialPatch.castRank_kernel_lip] using hL (chooseIndex h)
  · intro h hh
    change ((P (chooseIndex h)).castRank (rankEq h)).kernel.lip = _
    rw [PolynomialPatch.castRank_kernel_lip]
    exact congrArg (fun a => (P a).kernel.lip) (hchoose h hh)
  · intro h hh t
    change (((patch h).formAtWeight _ (weightEq h)).slots t).patchValue (patch h).kernel = _
    rw [PolynomialPatch.formAtWeight_value]
    change ((P (chooseIndex h)).castRank (rankEq h)).value t = _
    rw [PolynomialPatch.castRank_value]
    exact congrArg (fun a => (P a).value t) (hchoose h hh)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

theorem exists_varying_rank_fixed_patch_function (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {X H T : Type*}
      [Fintype X] [Fintype H] [Nonempty H] [Fintype T]
      (outer : FiniteProbabilityWeights H) (productive : Finset H)
      (d : H → ℕ) (patch : ∀ h, PolynomialPatch X s (d h)) (D : ℕ) (p : ℝ),
      (∀ h, d h ≤ D) → 0 < outer.mass productive →
      0 ≤ p → (D : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (∀ h, ((patch h).kernel.lip : ℝ) ≤ Real.exp p) →
      ∀ (localLaw : H → FiniteProbabilityWeights T) (point : H → T → X → ℤ)
        (score : H → T → ℝ), (∀ h t, |score h t| ≤ 1) →
      (∀ h ∈ productive, Real.exp (-p) ≤ (localLaw h).mean
        (fun t => score h t * (patch h).value (fun i => (point h t i : ℝ)))) →
      ∃ (d₀ : ℕ) (w : Fin d₀ → ℕ) (hw : Monotone w) (Ψ : PatchKernel d₀)
        (B : PolynomialSlots X d₀ w) (localForm : H → PolynomialSlots X d₀ w)
        (retained : Finset H),
        d₀ ≤ D ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (p + 2) ^ E) ∧
        retained ⊆ productive ∧
        (outer.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((p + 2) ^ E)) ≤ outer.mass retained ∧
        ∀ h ∈ retained, Real.exp (-((p + 2) ^ E)) ≤ (localLaw h).mean
          (fun t => score h t *
            (B.shearTransformedSlots hw
              ((localForm h).loweringAt (fun i => (point h t i : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hfixed⟩ := exists_unrestricted_fixed_weight_patch_function s
  refine ⟨E, hE, ?_⟩
  intro X H T _ _ _ _ outer productive d patch D p hd hproductive hp hD hX hLip
    localLaw point score hscore hpositive
  obtain ⟨d₀, w, A, Φ, middle, hd₀, hw, hpos, hws, hsub, hmass, hΦ, _, heval⟩ :=
    exists_common_rank_weight_patch_family outer productive d patch hd hproductive (Real.exp p) hLip
  have hmiddle (h) (hh : h ∈ middle) : Real.exp (-p) ≤ (localLaw h).mean (fun t =>
      score h t * ((A h).slots (fun i => (point h t i : ℝ))).patchValue (Φ h)) := by
    simp_rw [heval h hh]
    exact hpositive h (hsub hh)
  have hdreal : (d₀ : ℝ) ≤ p := (Nat.cast_le.mpr hd₀).trans hD
  obtain ⟨Ψ, B, localForm, retained, hΨ, hB, hretained, hmass', hlocal⟩ :=
    hfixed A Φ hw hpos hws p hp hdreal hX hΦ outer middle localLaw point score hscore hmiddle
  refine ⟨d₀, w, hw, Ψ, B, localForm, retained, hd₀, hpos, hws,
    hΨ, hB, hretained.trans hsub, ?_, hlocal⟩
  exact (mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _)).trans hmass'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedComparisonDimensions_of_primitive
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset α) (hq : Fintype.card α ≤ m+1)
    (hinj : ∀ j, Function.Injective (rows j)) {p : ℝ} (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    AllocatedComparisonDimensions (G := G) B α O (allocatedComparisonDimension m p) := by
  obtain ⟨hD, hm, hpD, hqD, hCD, hpaD, haD, hoD, hfD⟩ := allocatedComparisonDimension_bounds m hp
  have hqreal : (Fintype.card α : ℝ) ≤ (m+1 : ℕ) := Nat.cast_le.mpr hq
  have hrow (j : Fin m) : Fintype.card (O j) ≤ 2^(m+1) := by
    have hc := Fintype.card_le_of_injective (rows j) (hinj j)
    rw [Fintype.card_finset] at hc
    exact hc.trans (Nat.pow_le_pow_right (by omega) hq)
  have htuple : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hK
  have haxes := allocatedAxes_card_le (I := I) (n := n) hI hn
  refine ⟨hD, (Nat.cast_le.mpr (Nat.le_succ m)).trans hm,
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hK.trans hpD),
    hqreal.trans hm, haxes.trans haD, htuple.trans hpD, ?_, ?_,
    fun j => (Nat.cast_le.mpr (hrow j)).trans hqD, ?_, ?_⟩
  · rw [allocatedJointParameter_card, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    apply le_trans _ hpaD
    calc
      _ ≤ p*((m+1 : ℕ)+1) :=
        mul_le_mul htuple (by linarith) (by positivity) hp
      _ = _ := by push_cast; ring
  · apply le_trans _ hoD
    calc
      _ = ∑ a : LayerSamplerAxis I n, (Fintype.card (O a.1) : ℝ) := by
        simp only [Fintype.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _ : LayerSamplerAxis I n, ((2^(m+1) : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun a _ => Nat.cast_le.mpr (hrow a.1))
      _ = (Fintype.card (LayerSamplerAxis I n) : ℝ)*(2^(m+1) : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right haxes (Nat.cast_nonneg _)
  · intro j
    exact (boundedCoefficientExponent_card_le_geometricSiteBudget m 0
      (Nat.succ_le_of_lt j.isLt) hp hK).trans hCD
  · apply le_trans _ hfD
    exact (Nat.le_ceil _).trans (by unfold comparisonProfileBound; push_cast; linarith)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmallDifferenceGraphCoordinates
namespace OAI

section

namespace Erdos3

open scoped Pointwise BigOperators
open CyclicCrootSisask

theorem exists_small_difference_graph_coordinates {I : Type*} [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)]
    (H : Finset (ZMod N)) (hH : H.Nonempty) (b : ZMod N → ∀ i, ZMod (M i))
    {p : ℝ} (hp : 0 ≤ p)
    (hsmall : ((additiveGraph H b - additiveGraph H b).card : ℝ) ≤ Real.exp p * H.card) :
    let K := (2 ^ 14 : ℝ) * (Real.exp (p + 13 * Fintype.card I)) ^ 6
    let z := roundedModelLogBudget p (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ J ⊆ H, J.Nonempty ∧ δ * H.card ≤ 16 ^ (Fintype.card I + 2) * (J.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ))
        (base : Option I → ℤ),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
          2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
        Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧
          FreimanModel.variableIntegerGraphLift N M (h, b h) = base + Φ x := by
  intro K z δ
  classical
  let A := additiveGraph H b
  have hK : Real.exp p ≤ K := by
    calc
      _ ≤ Real.exp (6 * (p + 13 * Fintype.card I)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
      _ = Real.exp (p + 13 * Fintype.card I) ^ 6 := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ ≤ K := le_mul_of_one_le_left (by positivity) (by norm_num)
  have hAsmall : ((A - A).card : ℝ) ≤ K * A.card := by
    rw [show A.card = H.card from additiveGraph_card H b]
    exact hsmall.trans (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _))
  obtain ⟨Q, S, B, f, hQ, hS, hSA, hASsize, hB, _, _, hf, hQsize, hdensity⟩ :=
    FreimanModel.exists_variableIntegerGraph_cyclic_model N M A (hH.image _) (by positivity) hAsmall
  let _ : NeZero Q := ⟨hQ.ne'⟩
  have hdensity' : Real.exp (-z) * Q ≤ (B.card : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hQ : (0 : ℝ) < Q)).mp
    exact (exp_neg_roundedModelLogBudget_le_density p (Fintype.card I)).trans hdensity
  obtain ⟨F, hFS, hF, hFsize, r, R, Φ, base, hrank, hbox, hinj, hrepr⟩ :=
    FreimanModel.exists_bounded_affine_box_of_cyclic_model S hS B hB f hf
      (roundedModelLogBudget_nonneg p (Fintype.card I)) hdensity'
  have hboxSize : ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
      2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card := by
    have hcast : ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤ Q := by exact_mod_cast hbox
    exact hcast.trans (by simpa only [A, additiveGraph_card] using hQsize)
  have hFA : F ⊆ A.image (FreimanModel.variableIntegerGraphLift N M) := hFS.trans hSA
  let π : (Option I → ℤ) → ZMod N := fun v => (v none : ZMod N)
  have hback (v : Option I → ℤ) (hv : v ∈ F) :
      π v ∈ H ∧ FreimanModel.variableIntegerGraphLift N M (π v, b (π v)) = v := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hFA hv)
    obtain ⟨hyH, hyb⟩ := (mem_additiveGraph_iff H b y).mp hy
    have hπ : π (FreimanModel.variableIntegerGraphLift N M y) = y.1 := by simp [π]
    rw [hπ]
    exact ⟨hyH, congrArg (FreimanModel.variableIntegerGraphLift N M) (Prod.ext rfl hyb.symm)⟩
  let J := F.image π
  have hπinj : Set.InjOn π (F : Set _) := by
    intro x hx y hy hxy
    calc
      x = FreimanModel.variableIntegerGraphLift N M (π x, b (π x)) := (hback x hx).2.symm
      _ = FreimanModel.variableIntegerGraphLift N M (π y, b (π y)) := by rw [hxy]
      _ = y := (hback y hy).2
  have hFcard : F.card = J.card := (Finset.card_image_of_injOn hπinj).symm
  have hJ : J ⊆ H := by
    intro h hh
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hh
    exact (hback v hv).1
  have hHS : (H.card : ℝ) ≤ 16 ^ (Fintype.card I + 2) * (S.card : ℝ) := by
    exact_mod_cast (show H.card ≤ 16 ^ (Fintype.card I + 2) * S.card by
      simpa only [A, additiveGraph_card] using hASsize)
  have hretain : δ * (S.card : ℝ) ≤ (J.card : ℝ) := by
    simpa only [hFcard] using hFsize
  refine ⟨J, hJ, hF.image _, ?_, r, R, Φ, base, hrank, hboxSize, hinj, ?_⟩
  · calc
      δ * (H.card : ℝ) ≤ δ * (16 ^ (Fintype.card I + 2) * (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hHS (Real.exp_nonneg _)
      _ = 16 ^ (Fintype.card I + 2) * (δ * S.card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hretain (by positivity)
  · intro h hh
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hh
    rw [(hback v hv).2]
    exact hrepr v hv

theorem exists_small_difference_graph_proper_coordinates {I : Type*} [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)]
    (H : Finset (ZMod N)) (hH : H.Nonempty) (b : ZMod N → ∀ i, ZMod (M i))
    {p : ℝ} (hp : 0 ≤ p)
    (hsmall : ((additiveGraph H b - additiveGraph H b).card : ℝ) ≤ Real.exp p * H.card) :
    let K := (2 ^ 14 : ℝ) * (Real.exp (p + 13 * Fintype.card I)) ^ 6
    let z := roundedModelLogBudget p (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ J₀ ⊆ H, J₀.Nonempty ∧ δ * H.card ≤ 16 ^ (Fintype.card I + 2) * (J₀.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ)),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
          2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
        (let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J₀.card + 1
         let reduce := FreimanModel.variableIntegerGraphReduction N M
         let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
         ∃ J ⊆ J₀, J.Nonempty ∧ J₀.card ≤ (4 * k) ^ r * J.card ∧
           ∃ base : Option I → ℤ,
             Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) ∧
             ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i / (2 * k) : ℕ)) ∧
               FreimanModel.variableIntegerGraphLift N M (h, b h) = base + Φ x) := by
  intro K z δ
  classical
  obtain ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, base, hrank, hvolume, _, hrepr⟩ :=
    exists_small_difference_graph_coordinates N M H hH b hp hsmall
  let reduce := FreimanModel.variableIntegerGraphReduction N M
  let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
  have hall (h : {h // h ∈ J₀}) : ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧
      FreimanModel.variableIntegerGraphLift N M (h.val, b h.val) = base + Φ x :=
    hrepr h.val h.property
  choose x hx hgraph using hall
  have hspace (h : {h // h ∈ J₀}) : h.val = (reduce base).1 + η (x h) := by
    change h.val = (reduce base).1 + (reduce (Φ (x h))).1
    have hh := congrArg (fun v => (reduce v).1) (hgraph h)
    simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add,
      Prod.fst_add] using hh
  obtain ⟨J, hJJ₀, hJ, hretain, t, hproper, hsmallBox⟩ :=
    exists_dense_proper_coordinate_restriction J₀ hJ₀ R η (reduce base).1 x hx hspace
  refine ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume, J, hJJ₀,
    hJ, hretain, base + Φ t, hproper, ?_⟩
  intro h hh
  let h₀ : {h // h ∈ J₀} := ⟨h, hJJ₀ hh⟩
  refine ⟨x h₀ - t, hsmallBox ⟨h, hh⟩, ?_⟩
  rw [hgraph h₀, map_sub]
  abel

theorem exists_small_difference_graph_affine_coordinates {I : Type*} [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)]
    (H : Finset (ZMod N)) (hH : H.Nonempty) (b : ZMod N → ∀ i, ZMod (M i))
    {p : ℝ} (hp : 0 ≤ p)
    (hsmall : ((additiveGraph H b - additiveGraph H b).card : ℝ) ≤ Real.exp p * H.card) :
    ∃ J ⊆ H, J.Nonempty ∧
      Real.exp (-properAffineRecoveryLogLoss p (Fintype.card I)) * H.card ≤ (J.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ))
        (base : Option I → ℤ),
        (r : ℝ) ≤ properAffineRankBound p (Fintype.card I) ∧
        (let reduce := FreimanModel.variableIntegerGraphReduction N M
         let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
         Set.InjOn η (centeredIntegerBox R : Set _)) ∧
        ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧
          FreimanModel.variableIntegerGraphLift N M (h, b h) = base + Φ x := by
  classical
  obtain ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume,
      J, hJJ₀, hJ, hretain, base, hproper, hrepr⟩ :=
    exists_small_difference_graph_proper_coordinates N M H hH b hp hsmall
  have hfactor : ((2 : ℝ) ^ 4)⁻¹ * (Real.exp (p + 13 * Fintype.card I))⁻¹ ≤ 1 := by
    calc
      _ ≤ (Real.exp (p + 13 * Fintype.card I))⁻¹ :=
        mul_le_of_le_one_left (by positivity) (by norm_num)
      _ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_exp_iff.mpr (by positivity))
  have hweaker : Real.exp (-(quarticBogolyubovProgressionConstant *
      (roundedModelLogBudget p (Fintype.card I) + 1) ^ 8)) *
      ((2 ^ 4 : ℝ)⁻¹ * (Real.exp (p + 13 * Fintype.card I))⁻¹ * H.card) ≤
      16 ^ (Fintype.card I + 2) * (J₀.card : ℝ) := by
    apply le_trans _ hsize
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) hfactor
  have hdense₀ := exp_neg_affineRecoveryLogLoss_card_le p (Fintype.card I) H.card J₀.card hweaker
  have hcost := properAffineSelection_bounds hp (Fintype.card I) r
    (∏ i, (2 * R i + 1)) H.card J₀.card J.card hJ₀.card_pos hrank hvolume hdense₀ hretain
  exact ⟨J, hJJ₀.trans hJ₀H, hJ, hcost.2, r,
    (fun i => R i / (2 * ((2 ^ r * ∏ j, (2 * R j + 1)) / J₀.card + 1))),
    Φ, base, hrank, hproper, hrepr⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates
namespace OAI

section

namespace Erdos3

open scoped Pointwise

theorem exists_quadratic_affine_frequency_coordinates
    {N : ℕ} [NeZero N] {p : ℝ} (hp : 0 ≤ p) (f : ZMod N → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hG : Real.exp (-p) ≤ gowersNorm 3 f) :
    let P := 1024 * (p + 1)
    ∃ H : Finset (ZMod N), H.Nonempty ∧
      Real.exp (-(P + properAffineRecoveryLogLoss P 1)) * N ≤ (H.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (η ξ : (Fin r → ℤ) →+ ZMod N) (h₀ ξ₀ : ZMod N),
        (r : ℝ) ≤ properAffineRankBound P 1 ∧
        Set.InjOn η (centeredIntegerBox R : Set _) ∧
        ∀ h ∈ H, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x ∧
          Real.exp (-P) ≤ ‖finiteFourierCoeff (multiplicativeDerivative f h)
            (AddChar.zmodAddEquiv (ξ₀ + ξ x))‖ := by
  intro P
  classical
  obtain ⟨H, hH, hdense, χ, hcorr, hsmall⟩ := exists_quadratic_frequency_small_difference hp f hf hG
  let e₀ : AddChar (ZMod N) ℂ ≃+ ZMod N := (AddChar.zmodAddEquiv (n := N)).symm
  let e : AddChar (ZMod N) ℂ →+ (Unit → ZMod N) := {
    toFun := fun c _ => e₀ c
    map_zero' := by ext; simp
    map_add' := by intro c d; ext; simp }
  have he : Function.Injective e := by
    intro c d h
    exact e₀.injective (congrFun h ())
  let b (h : ZMod N) := e (χ h)
  have hsmall' : ((additiveGraph H b - additiveGraph H b).card : ℝ) ≤ Real.exp P * H.card := by
    rw [additiveGraph_difference_card_hom H χ e he]
    exact hsmall
  obtain ⟨J, hJH, hJ, hJdense, r, R, Φ, base, hrank, hproper, hrepr⟩ :=
    exists_small_difference_graph_affine_coordinates N (fun _ : Unit => N) H hH b
      (by dsimp [P]; positivity) hsmall'
  let reduce := FreimanModel.variableIntegerGraphReduction N (fun _ : Unit => N)
  let η := (AddMonoidHom.fst (ZMod N) (Unit → ZMod N)).comp (reduce.comp Φ)
  let ξ : (Fin r → ℤ) →+ ZMod N := {
    toFun := fun x => (reduce (Φ x)).2 ()
    map_zero' := by simp
    map_add' := by intro x y; simp }
  have hdense' : Real.exp (-P) * N ≤ (H.card : ℝ) := by
    simpa only [ZMod.card] using hdense
  have hJdense' : Real.exp (-properAffineRecoveryLogLoss P 1) * H.card ≤ (J.card : ℝ) := by
    simpa only [Fintype.card_unique] using hJdense
  refine ⟨J, hJ, ?_, r, R, η, ξ, (reduce base).1, (reduce base).2 (), ?_, hproper, ?_⟩
  · calc
      _ = Real.exp (-properAffineRecoveryLogLoss P 1) * (Real.exp (-P) * N) := by
        rw [neg_add, Real.exp_add]
        ring
      _ ≤ Real.exp (-properAffineRecoveryLogLoss P 1) * H.card :=
        mul_le_mul_of_nonneg_left hdense' (Real.exp_nonneg _)
      _ ≤ _ := hJdense'
  · simpa only [Fintype.card_unique] using hrank
  · intro h hh
    obtain ⟨x, hx, heq⟩ := hrepr h hh
    have hred : (h, b h) = reduce base + reduce (Φ x) := by
      have h := congrArg reduce heq
      simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add] using h
    have hfreq : AddChar.zmodAddEquiv ((reduce base).2 () + ξ x) = χ h := by
      have hv : e₀ (χ h) = (reduce base).2 () + ξ x := congrArg (fun v => v.2 ()) hred
      rw [← hv]
      exact (AddChar.zmodAddEquiv (n := N)).apply_symm_apply _
    refine ⟨x, hx, congrArg Prod.fst hred, ?_⟩
    rw [hfreq]
    exact hcorr h (hJH hh)

theorem exists_quadratic_affine_frequency_coordinates_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ (r : ℕ) (R : Fin r → ℕ) (η ξ : (Fin r → ℤ) →+ ZMod N) (h₀ ξ₀ : ZMod N),
          (r : ℝ) ≤ (p + C) ^ C ∧ Set.InjOn η (centeredIntegerBox R : Set _) ∧
          ∀ h ∈ H, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x ∧
            Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff (multiplicativeDerivative f h)
              (AddChar.zmodAddEquiv (ξ₀ + ξ x))‖ := by
  obtain ⟨C, hC, hbudget⟩ := exists_quadratic_affine_budget
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  obtain ⟨H, hH, hdense, r, R, η, ξ, h₀, ξ₀, hrank, hproper, hcorr⟩ :=
    exists_quadratic_affine_frequency_coordinates hp f hf hG
  obtain ⟨hcost, hrankCost, hcorrCost⟩ := hbudget p hp
  refine ⟨H, hH, ?_, r, R, η, ξ, h₀, ξ₀, hrank.trans hrankCost, hproper, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    obtain ⟨x, hx, hshift, hlarge⟩ := hcorr h hh
    exact ⟨x, hx, hshift, (Real.exp_le_exp.mpr (neg_le_neg hcorrCost)).trans hlarge⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem exists_quadratic_small_modulus_correlation {N : ℕ} [NeZero N] {p q : ℝ}
    (hN : (N : ℝ) ≤ Real.exp q) (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hGowers : Real.exp (-p) ≤ gowersNorm 3 f) :
    ∃ g ∈ nativeCyclicFunctions 2 N 211,
      Real.exp (-(8 * p + q)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  have hmass : Real.exp (-(8 * p)) ≤ ∑ χ : AddChar (ZMod N) ℂ, ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = Real.exp (-p) ^ 8 := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ gowersNorm 3 f ^ 8 := pow_le_pow_left₀ (Real.exp_nonneg _) hGowers 8
      _ ≤ 𝔼 n, ‖f n‖ := by simpa using gowersNorm_pow_le_mean_norm 2 f hf
      _ ≤ _ := mean_norm_le_fourier_sum f
  obtain ⟨χ, hχ⟩ := exists_large_nonnegative_weighted_term
    (fun _ : AddChar (ZMod N) ℂ => (1 : ℝ)) (fun χ => ‖finiteFourierCoeff f χ‖)
    (fun _ => by norm_num) (fun _ => norm_nonneg _) (Real.exp_pos _) (Real.exp_pos q)
    (by simpa using hN) (by simpa only [one_mul] using hmass)
  have hcorr : Real.exp (-(8 * p + q)) ≤ ‖finiteFourierCoeff f χ‖ := by
    have heq : Real.exp (-(8 * p)) / Real.exp q = Real.exp (-(8 * p + q)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rwa [heq] at hχ
  obtain ⟨T, hTnorm, hT, hTeval⟩ := exists_cyclic_character_niltest χ
  let hdegree : 1 ≤ 2 := by omega
  refine ⟨fun n => χ n, ⟨{
    L := RationalTorus.Algebra 1
    dim := 1
    model := (RationalTorus.nilmanifold 1).raiseStep hdegree
    test := T.raiseStep hdegree
    norm := hTnorm
    complexity := ?_
    eval := ?_ }⟩, hcorr⟩
  · have hh := T.raiseStep_complexity hdegree (by norm_num) hT
    convert hh using 1
    norm_num [raisedNiltestBudget]
  · intro n
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
    exact (hTeval n).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticLocalFrequency
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem exists_quadratic_local_frequency :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ (r : ℕ) (t c b : Fin r → ℝ) (a : ℝ) (h₀ : ZMod N),
          (r : ℝ) ≤ (p + C) ^ C ∧
          (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
          (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
          (∀ i, |c i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∀ h ∈ H, (∀ i, |affineCyclicTorusLocalLift t c h₀ h i| ≤ 1 / 16) ∧
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (CircleFourier.character
                  (((n.val : ℝ) * (a + ∑ i, affineCyclicTorusLocalLift t c h₀ h i * b i) : ℝ) :
                    CircleFourier.Circle))‖ := by
  obtain ⟨A, _, hfrequencies⟩ := exists_quadratic_affine_frequency_coordinates_budget
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + 4) ^ 7 + (P + 4) ^ 5 + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  classical
  obtain ⟨J, hJ, hdense, r, R, η, ξ, h₀, ξ₀, hrank, hproper, hselected⟩ :=
    hfrequencies hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : q + (q + 4) ^ 7 + (q + 4) ^ 5 + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by
    have h₇ : 0 ≤ (q + 4) ^ 7 := by positivity
    have h₅ : 0 ≤ (q + 4) ^ 5 := by positivity
    linarith
  have hchartC : (q + 4) ^ 7 ≤ (p + C) ^ C := by
    have h₅ : 0 ≤ (q + 4) ^ 5 := by positivity
    linarith
  have hcenterC : (q + 4) ^ 5 + 2 ≤ (p + C) ^ C := by
    have h₇ : 0 ≤ (q + 4) ^ 7 := by positivity
    linarith
  choose x hx hrep hlarge using fun h : {h // h ∈ J} => hselected h.val h.property
  let x' (h : ZMod N) : Fin r → ℤ := if hh : h ∈ J then x ⟨h, hh⟩ else 0
  have hx' (h : ZMod N) (hh : h ∈ J) : ∀ i, |x' h i| ≤ (R i : ℤ) := by
    simpa only [x', dif_pos hh] using hx ⟨h, hh⟩
  have hrep' (h : ZMod N) (hh : h ∈ J) : h = h₀ + η (x' h) := by
    simpa only [x', dif_pos hh] using hrep ⟨h, hh⟩
  have hlarge' (h : ZMod N) (hh : h ∈ J) : Real.exp (-q) ≤
      ‖finiteFourierCoeff (multiplicativeDerivative f h) (AddChar.zmodAddEquiv (ξ₀ + ξ (x' h)))‖ := by
    simpa only [x', dif_pos hh] using hlarge ⟨h, hh⟩
  have hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)} := by
    simpa only [Set.InjOn, Finset.mem_coe, mem_centeredIntegerBox, Set.mem_ofPred_eq] using hproper
  obtain ⟨a, b, hphase⟩ := exists_affine_cyclic_character_phase ξ ξ₀
  obtain ⟨K, hKJ, hK, hKsize, t, c, a', b', ht, hperiod, hc, hlocal⟩ :=
    exists_local_affine_scalar_chart hq hrank η R hinj h₀ J hJ hdense x' hx' hrep' a b
  refine ⟨K, hK, ?_, r, t, c, b', a', h₀, hrank.trans hqC, ht, hperiod, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hchartC))
      (Nat.cast_nonneg _)).trans hKsize
  · intro i
    have hcoord := properCyclicCoordinateBound_le_exp hq hrank
    have hE : 1 ≤ Real.exp ((q + 4) ^ 5) := Real.one_le_exp (by positivity)
    calc
      |c i| ≤ properCyclicCoordinateBound r (Real.exp (-q)) + 1 / 16 := hc i
      _ ≤ 2 * Real.exp ((q + 4) ^ 5) := by linarith
      _ ≤ Real.exp 2 * Real.exp ((q + 4) ^ 5) := by
        gcongr
        linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = Real.exp ((q + 4) ^ 5 + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hcenterC
  · intro h hh
    obtain ⟨hsmall, heq⟩ := hlocal h hh
    refine ⟨hsmall, ?_⟩
    have heval (n : ZMod N) : CircleFourier.character
        (((n.val : ℝ) * (a' + ∑ i, affineCyclicTorusLocalLift t c h₀ h i * b' i) : ℝ) :
          CircleFourier.Circle) = AddChar.zmodAddEquiv (ξ₀ + ξ (x' h)) n := by
      rw [← heq]
      exact hphase (x' h) n
    simp only [heval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hlarge' h (hKJ hh))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelatingVerticalPair
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

theorem exists_weighted_common_factor :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} {I J K : Type*}
      [Fintype σ] [Fintype I] [Fintype K] {s N : ℕ} [NeZero N] {p : ℝ},
      2 ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card I : ℝ) ≤ Real.exp p →
      ∀ (w : I → σ → ZMod N → ℝ) (v : I → J → (σ → ℤ) → ℂ)
        (u : K → (σ → ℤ) → ℂ),
        (∀ i a, PositiveCyclicNiltest.{0} s N p (w i a)) →
        (∀ x : σ → ZMod N, ∑ i, ∏ a, w i a (x a) = 1) →
        (∀ i j (x : σ → ZMod N), ‖v i j (fun a => ((x a).val : ℤ))‖ ≤ 1) →
        (∀ k (x : σ → ZMod N), ‖u k (fun a => ((x a).val : ℤ))‖ ≤ 1) →
        (∀ x : σ → ZMod N, ∑ k, ‖u k (fun a => ((x a).val : ℤ))‖ ^ 2 = 1) →
        (∀ i j k, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p
          (fun x => v i j x * star (u k x)))) →
        ∃ F : J → K → (σ → ℤ) → ℂ,
          (∀ j k, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) (F j k))) ∧
          (∀ j k (x : σ → ZMod N), F j k (fun a => ((x a).val : ℤ)) =
            (∑ i, ((∏ a, w i a (x a) : ℝ) : ℂ) * v i j (fun a => ((x a).val : ℤ))) *
              star (u k (fun a => ((x a).val : ℤ)))) ∧
          (∀ j k (x : σ → ZMod N), ‖F j k (fun a => ((x a).val : ℤ))‖ ≤ 1) ∧
          (∀ j (x : σ → ZMod N),
            ∑ k, F j k (fun a => ((x a).val : ℤ)) * u k (fun a => ((x a).val : ℤ)) =
            ∑ i, ((∏ a, w i a (x a) : ℝ) : ℂ) * v i j (fun a => ((x a).val : ℤ))) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  obtain ⟨B, _, hproduct⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + 2) ^ 2 + 3
  let R := (Y + Polynomial.C B) ^ B + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C A) ^ A + X)
  refine ⟨C, hC, ?_⟩
  intro σ I J K _ _ _ s N _ p hp hσ hI w v u hw htotal hv hu hunit hexp
  classical
  have hp0 : 0 ≤ p := by linarith
  have hy : 0 ≤ raisedNiltestBudget p := hp0.trans (le_raisedNiltestBudget p)
  let r := (raisedNiltestBudget p + B) ^ B + p + 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by dsimp [r]; linarith [pow_nonneg (by positivity : 0 ≤ raisedNiltestBudget p + B) B]
  have hwr : productNiltestBudget (raisedNiltestBudget p) ≤ r :=
    (hproduct _ hy).trans (by dsimp [r]; linarith)
  have hcost : (r + A) ^ A + p ≤ (p + C) ^ C := by
    simpa [X, Y, R, r, raisedNiltestBudget, Polynomial.eval₂_pow] using hbudget p hp0
  have hweights (i : I) := exists_positive_coordinate_product hp0 hσ (hw i)
  choose g hgExpansion hg using hweights
  have hproducts (i : I) (j : J) (k : K) :
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((r + A) ^ A)
        (fun x => g i x * (v i j x * star (u k x)))) :=
    hmul hr ((Classical.choice (hgExpansion i)).mono hwr)
      ((Classical.choice (hexp i j k)).mono hpr)
  let E (i : I) (j : J) (k : K) := Classical.choice (hproducts i j k)
  let F (j : J) (k : K) (x : σ → ℤ) := ∑ i, g i x * (v i j x * star (u k x))
  have hF (j : J) (k : K) :
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) (F j k)) := by
    have hc : (∑ _ : I, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hI
    have H := (NativeIntegerExpansion.weightedSum (fun i => E i j k)
      (fun _ => (1 : ℂ)) hp0 hI hc).mono hcost
    exact ⟨by simpa only [one_mul] using H⟩
  have heq (j : J) (k : K) (x : σ → ZMod N) : F j k (fun a => ((x a).val : ℤ)) =
      (∑ i, ((∏ a, w i a (x a) : ℝ) : ℂ) * v i j (fun a => ((x a).val : ℤ))) *
        star (u k (fun a => ((x a).val : ℤ))) := by
    simp only [F, hg, Complex.ofReal_prod, Finset.sum_mul, mul_assoc]
  refine ⟨F, hF, heq, ?_, ?_⟩
  · intro j k x
    rw [heq, norm_mul, norm_star]
    have hsum : ‖∑ i, ((∏ a, w i a (x a) : ℝ) : ℂ) *
        v i j (fun a => ((x a).val : ℤ))‖ ≤ 1 :=
      norm_positive_partition_sum_le_one (fun i => ∏ a, w i a (x a))
        (fun i => v i j (fun a => ((x a).val : ℤ)))
        (fun i => Finset.prod_nonneg (fun a _ => ((hw i a).unit_interval (x a)).1))
        (htotal x) (fun i => hv i j x)
    exact (mul_le_of_le_one_left (norm_nonneg _) hsum).trans (hu k x)
  · intro j x
    simp_rw [heq]
    exact (complex_unit_vector_resolution (fun k => u k (fun a => ((x a).val : ℤ)))
      (hunit x) _).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

section Joint

variable {C B K I : Type*} [MeasurableSpace C] [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

theorem selectedJointFiniteLaw_weight_measurable
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (z : A × rectangularWeightIndices 0 W 1) :
    Measurable (fun c =>
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).weight z) := by
  simp only [selectedJointFiniteLaw_weight]
  exact ((hDm z.1.val z.2.val).const_mul _).div
    (selectedJointDensityMass_measurable A hA modulus T W hW hZ D hDm)

end Joint

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j) (c : ∀ j, U j)

omit [DecidableEq G] [Fintype X] [∀ index, DecidableEq (I index)]
  [∀ axis, DecidableEq (B axis)] in
theorem allocatedJointBaseDensity_subtractConstant_affine (a : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedJointBaseDensity B U b hb o hR hσ S X (fun j => subtractConstant (c j).val (poly j)) (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) a z =
      allocatedAffineDensity B U b hb o hR hσ S poly hmem c
        (fun k i => (jointIntegerFrame (a, z) k i : ℝ)) := by
  unfold allocatedJointBaseDensity
  rw [affineSampleCoefficientTorus_joint_frame U
    (fun j => subtractConstant (c j).val (poly j))
    (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) a z,
    affineSampleCoefficientTorus_subtractConstant U poly hmem c]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

omit [Fintype X] in
theorem allocatedJointBaseDensity_subtractConstant_centered
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1)))) :
    allocatedJointBaseDensity B U b hb o hR hσ S X
      (fun j => subtractConstant (c j).val (poly j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) =
    allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center := by
  funext a z
  rw [allocatedJointBaseDensity_subtractConstant_affine,
    allocatedCenteredJointDensity_eq_affine B U b hb o hR hσ S poly hmem center c hc]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFixedScaleJointMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def AllocatedFixedScaleJointMarginalStatement (m A : ℕ) : Prop :=
    ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P) (_hτhalf : τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    ∃ (_hN : ∀ i, 0 < N i) (hwidths : ∀ z, 0 < widths z)
      (hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z)
      (hD : ∀ center, 0 < selectedJointDensityMass bases stride T widths (density center)),
      (∀ center,
        let Z := selectedJointDensityMass bases stride T widths (density center)
        |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ Z⁻¹ ≤ 2) ∧
      ∀ (root : LayerSamplerVariables G I n B → ℤ),
        (∀ k, |(root k : ℝ)| ≤ Real.exp P) →
        (∑ k, |(root k : ℝ)|) ≤ W →
      ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
        let f := fun center =>
          (selectedJointFiniteLaw bases (trimmedIntegerBox_nonempty N _ hmargin)
            stride T widths hwidths hmass (density center)
            (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
            (hD center)).complexMean
              (fun z => φ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite root z.2.val))
        Integrable f μ ∧
          ‖(∫ center, f center ∂μ) - (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
            12 * positiveProjectionAccuracy P + 2 * (Fintype.card X : ℝ) * τ

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowPrescribedMarginal
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem allocatedCenteredJointFiniteLaw_weight_measurable
    (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
    (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (W : Option (LayerSamplerVariables G I n B) × X → ℝ) (hW : ∀ z, 0 < W z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z)
    (hDcenter : ∀ center, 0 < selectedJointDensityMass bases stride cells W
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center))
    (z : bases × rectangularWeightIndices 0 W 1) :
    Measurable (fun center =>
      (selectedJointFiniteLaw bases hbases stride cells W hW hmass
        (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
        (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center)
        (hDcenter center)).weight z) :=
  selectedJointFiniteLaw_weight_measurable bases hbases stride cells W hW hmass
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem)
    (allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S poly hmem)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem) hDcenter z

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

namespace AllocatedExternalCandidateSamplerFamily

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells}
    (A : AllocatedExternalCandidateSamplerFamily B U b S hb o hR hσ N poly hm τ ξ stride cells)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

noncomputable def law (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    FiniteProbabilityWeights A.Path :=
  (A center).law

end AllocatedExternalCandidateSamplerFamily

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedZeroLayerLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

variable (N : X → ℕ) (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem AllocatedExternalCandidateSampler.law_zero_layers
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hm τ ξ stride cells center) :
    A.law = selectedJointReference (trimmedIntegerBox N (spatialTrimMargin τ N))
      A.bases_nonempty stride cells (allocatedExternalCandidateWidths B U b S N τ ξ)
      A.widths_pos A.smooth_mass_pos := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro z
  rw [AllocatedExternalCandidateSampler.law, selectedJointFiniteLaw,
    FiniteProbabilityWeights.reweightPositive_weight]
  simp only [allocatedCenteredJointDensity_zero_layers, FiniteProbabilityWeights.mean_const,
    mul_one, div_one]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I J : Fin m → Type*} {n : Fin m → ℕ}
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type*)

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}

variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedExternalCandidateWidths_empty_layers
    (N : X → ℕ) (τ ξ : ℝ) :
    allocatedExternalCandidateWidths B U b S N τ ξ =
      trimmedSpatialWidths (K := LayerSamplerVariables G I n B)
        ((Fintype.card G : ℝ) * S.value) τ N := by
  funext z
  rw [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_empty_layers]
  rcases z with ⟨_ | k, x⟩
  · rfl
  · cases k with
    | inl g => rfl
    | inr a => exact Sum.elim isEmptyElim isEmptyElim a.1.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

theorem poly_mem (q : ℕ) (X : Type*) (j : Fin q) (α : X →₀ ℕ) :
    coefficients (poly q X j) α ∈ U q j := by
  have hzero : coefficients (poly q X j) α = 0 := Subsingleton.elim _ _
  rw [hzero]
  exact Submodule.zero_mem _

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedInactiveSupportBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include h

theorem allocatedIntegerBlock_card_le (j : Fin m) (i : Fin (n j)) :
    (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D := by
  have hs : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (h.coefficients j)
  simpa only [layerIntegerPrincipalSlots_card] using hs

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (r : ℝ≥0) (hr : 0 < r) (f : (LayerSamplerAxis I n → ℝ) → ℂ)

noncomputable def allocatedBufferedMixedSiteFactor
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ)) : ℂ :=
  bufferedCoordinateProjection (allocatedGridAxis (I := I) U b S.value) r hr f
    (allocatedFullMixedSiteValue (R := R) U b w)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := Q) U o b d quarter

noncomputable def allocatedBufferedSiteChartFactor (f : (LayerSamplerAxis I n → ℝ) → ℂ) :
    EuclideanJetLayers U single → ℂ :=
  restrictedComplexChartDensity chart region 1 (fun z =>
    allocatedBufferedMixedSiteFactor B U b S r hr f (fun j => mixedArrayRegroup _ _ _ (z.1 j) ()))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))

namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def frozenSingleSiteHaarReference
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) : ℂ :=
  ∫ y, W.frozenTorus residue center
    (fun a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩) ∂haar

omit [∀ j, (ν j).IsAddLeftInvariant] in
theorem frozenSingleSiteHaarReference_integrable
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) :
    Integrable (fun y : EuclideanJetLayers U (fun _ => Unit) =>
      W.frozenTorus residue center
        (fun a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩)) haar := by
  have : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  have : IsProbabilityMeasure haar := Measure.pi.instIsProbabilityMeasure _
  apply Integrable.of_bound _ 1 (ae_of_all _ (fun _ => W.norm_frozenTorus_le _ _ _))
  apply Continuous.aestronglyMeasurable
  apply (W.frozenTorus_lipschitz residue center).continuous.comp
  apply continuous_pi
  intro a
  exact (continuous_apply (⟨a.1, (), a.2⟩ : JetAmbientIndex (fun _ : Fin m => Unit) J)).comp
    (coveredJetAmbientTorus_continuous (O := fun _ : Fin m => Unit) U 1)

omit [∀ j, (ν j).IsAddLeftInvariant] in
theorem frozenSingleSiteHaarReference_lipschitz
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) :
    LipschitzWith L (W.frozenSingleSiteHaarReference U ν residue) := by
  have : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  have : IsProbabilityMeasure haar := Measure.pi.instIsProbabilityMeasure _
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  exact probability_integral_approximation haar _ _
    (W.frozenSingleSiteHaarReference_integrable U ν residue x)
    (W.frozenSingleSiteHaarReference_integrable U ν residue y)
    (fun z => W.frozenTorus_spatial_error residue x y _)

end NormalizedPolynomialTwist

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductIdealCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

noncomputable def allocatedProductSiteCutoff (y : EuclideanJetLayers U rowTypes) : ℂ :=
  ∏ s : Finset α, allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1)
    (coveredRowsSiteValue rowSets U y s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α]
variable (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedProductIdealSiteRadius : ℝ≥0 :=
  ⟨1 + ∑ j : Fin m, (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j,
    add_nonneg zero_le_one (Finset.sum_nonneg (fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (allocatedIdealCoverSupport_nonneg B rowSets j)))⟩

theorem allocatedProductIdealSiteRadius_one_le : 1 ≤ allocatedProductIdealSiteRadius (G := G) B rowSets := by
  change (1 : ℝ) ≤ 1 + ∑ j : Fin m, (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ =>
    mul_nonneg (Nat.cast_nonneg _) (allocatedIdealCoverSupport_nonneg B rowSets j)))

theorem allocatedProductIdealSiteRadius_dominates (j : Fin m) :
    (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j ≤
      allocatedProductIdealSiteRadius (G := G) B rowSets := by
  change (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j ≤
    1 + ∑ k : Fin m, (rowSets k).card * allocatedIdealCoverSupport (G := G) B rowSets k
  exact (Finset.single_le_sum
    (f := fun k : Fin m => (rowSets k).card * allocatedIdealCoverSupport (G := G) B rowSets k)
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (allocatedIdealCoverSupport_nonneg B rowSets k))
    (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedProductRadiusBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedProductGridRadius (C : Fin m → ℝ) (j : Fin m) : ℝ :=
  finiteRowChartRadius (((rowSets j).card + 1) * Fintype.card (Finset α))
    (Fintype.card (I j)) (C j) (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ))

theorem allocatedProductGridRadius_pos (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    0 < allocatedProductGridRadius (G := G) B rowSets C j :=
  finiteRowChartRadius_pos _ _ (hC j)
    (mul_nonneg (by norm_num) (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg)

theorem allocatedProductGridRadius_recovery_budget
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B rowSets C j) (j : Fin m) :
    ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) *
        (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)))) ≤ 1 / 4 := by
  have h := finiteRowChartRadius_budget (((rowSets j).card + 1) * Fintype.card (Finset α))
    (Fintype.card (I j)) (hC j)
    (mul_nonneg (by norm_num) (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg)
    (hR j) (hsmall j)
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using h

theorem allocatedProductGridRadius_source_budget
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B rowSets C j) (j : Fin m) :
    C j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)) ≤ 1 / 4 := by
  have hcard : (1 : ℝ) ≤ Fintype.card (Finset α) := by
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨(∅ : Finset α)⟩)
  have hrow : (0 : ℝ) ≤ (rowSets j).card := Nat.cast_nonneg _
  have hfactor : (1 : ℝ) ≤ ((rowSets j).card + 1 : ℝ) * Fintype.card (Finset α) := by nlinarith
  have hc : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)) :=
    mul_nonneg (hC j) (mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by norm_num) (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg) (hR j)))
  have h := mul_le_mul_of_nonneg_right hfactor hc
  have hb := allocatedProductGridRadius_recovery_budget B rowSets C hC hR hsmall j
  simp only [one_mul, mul_assoc] at h hb ⊢
  exact h.trans hb

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFullGridChartModelMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

noncomputable def allocatedFullGridChartModel
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) : EuclideanJetLayers U rowTypes → ℂ :=
  allocatedComplexGridMultiplier B U b S rowTypes hb o bW d
    (allocatedFullGridSiteApproximation B U b S rowSets e)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductPrefactorMasks
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x y₀
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

noncomputable def allocatedClippedPrefactorSiteMask
    (r : Finset α → (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ :=
  allocatedKernelSiteMask B U b S rowSets x q residue period (fun s => (r s).1) *
    coefficientDeckSiteMask root dirs rows d period (fun s => (r s).2)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedUniformEarlyRadiusWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

section Charts

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedBufferedRadius_inverse_from_primitive {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hq : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g) (j : Fin m) :
    (allocatedBufferedPhysicalChartRadius (G := G) B α C j)⁻¹ ≤
      Real.exp (allocatedBufferedRadiusLog m p g) := by
  have hd := allocatedComparisonDimensions_of_primitive (G := G) (α := α)
    (O := fun _ => Finset α) B
    (fun _ => id) hq (fun _ => Function.injective_id) hp hvars hI hn
  obtain ⟨hP, hDP, hgP, haP⟩ := allocatedBufferedRadiusInput_bounds m hp hg
  have hpD := (allocatedComparisonDimension_bounds m hp).2.2.1
  have hqreal : (Fintype.card α : ℝ) ≤ (m + 1 : ℕ) := Nat.cast_le.mpr hq
  have hPe : allocatedBufferedRadiusInput m p g ≤ Real.exp (allocatedBufferedRadiusInput m p g) := by
    linarith [Real.add_one_le_exp (allocatedBufferedRadiusInput m p g)]
  have hallow : ((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5 ≤
      allocatedBufferedRadiusInput m p g := by
    have hmul := mul_le_mul_of_nonneg_left hqreal
      (show (0 : ℝ) ≤ (2 * m + 5 : ℕ) by positivity)
    push_cast at haP hmul ⊢
    linarith
  have hi := allocatedBufferedPhysicalChartRadius_inv_le_exp_uniform B α C hC hP
    (hd.degree.trans (hDP.trans hPe)) (hd.cube.trans hDP) hallow
    (fun j => (hCg j).trans (Real.exp_le_exp.mpr hgP))
    (fun j => (hd.coefficients j).trans (hDP.trans hPe))
    (fun j => (hI j).trans (hpD.trans (hDP.trans hPe))) j
  apply hi.trans
  apply Real.exp_le_exp.mpr
  unfold allocatedBufferedRadiusLog
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  push_cast at hqreal
  linarith

end Charts

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRowSlicedIdealCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedRowSlicedSiteRadius : ℝ≥0 :=
  ⟨1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1), by
    have := partitionedIdealRadius_nonneg α m
    positivity⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalNormalizer
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

noncomputable def allocatedProductIdealNormalizer : ℝ := baseVolume * (∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

noncomputable def allocatedProductMaskedIdealCoefficient {K : Type*}
    (a : K → ℂ) (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) (k : K) : ℂ :=
  inverseNormalizer * (mask label : ℂ) * a k

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowAmplitudeNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_amplitude_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let pa := fun (base : X → ℤ) j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun (base : X → ℤ) j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    let density := fun base z => allocatedCoefficientDensity B U basis hb o hR hσ S
      (affineSampleCoefficientTorus U (pa base) (hma base) (fun k d => (z (k, d) : ℝ)))
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      (∀ (base : X → ℤ) (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
        (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
          (Lip : ℝ) ≤ Real.exp P →
        ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
          ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (amplitude (fun t => (z t : ℝ) / widths t) * (density base z : ℂ))) -
          ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
            ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
              amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
          3 * positiveProjectionAccuracy P) ∧
      ∀ base, |selectedResidueDensityMass stride T widths (density base) - 1| ≤
          3 * positiveProjectionAccuracy P ∧
        ∃ (hD0 : ∀ z, 0 ≤ density base z)
          (hD : 0 < selectedResidueDensityMass stride T widths (density base)),
          ∀ (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
            (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
              (Lip : ℝ) ≤ Real.exp P →
            ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
              ((selectedResidueDensityPMF stride T widths hwidths hZ
                (density base) hD0 hD z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)) -
              ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
                ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
              6 * positiveProjectionAccuracy P := by
  obtain ⟨A₀, _, hmass⟩ := exists_affine_coefficient_amplitude_density_test m
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m 0
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + 8 * Polynomial.X + 128 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths pa hma density
  have h2P : 0 ≤ 2 * P := mul_nonneg (by norm_num) hP
  have hP2P : P ≤ 2 * P := by linarith
  have hτξ : 0 < ξ * τ := mul_pos hξ hτ
  have hτξP : (ξ * τ)⁻¹ ≤ Real.exp (2 * P) := by
    rw [mul_inv_rev]
    calc
      τ⁻¹ * ξ⁻¹ ≤ Real.exp P * Real.exp P := by gcongr
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
  let Q := positiveComparisonDataBudget m 0 P + spatialSamplingBudget (2 * P)
  have hdata := positiveComparisonDataBudget_bounds m 0 hP
  have hdataQ : positiveComparisonDataBudget m 0 P ≤ Q :=
    le_add_of_nonneg_right (h2P.trans (le_spatialSamplingBudget h2P))
  have hspatialQ : spatialSamplingBudget (2 * P) ≤ Q := le_add_of_nonneg_left hdata.1
  have hPQ : P ≤ Q := hdata.2.1.trans hdataQ
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    have hbase : Q + (A₀ : ℝ) ≤ (P + b) ^ b + 8 * P + 128 + A₀ := by
      have h := hbnd P hP
      dsimp [Q, spatialSamplingBudget]
      linarith
    calc
      _ ≤ ((P + b) ^ b + 8 * P + 128 + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀)) hbase A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨_, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C V hC hV 0
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hmSize hK hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  let _ := inst
  have hspec := allocatedCoefficientDensity_spec B U basis hb o hR hσ S
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hwidths := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  have hwidthLower (z : Option (LayerSamplerVariables G I n B) × X) :
      spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ) ≤ widths z :=
    (spatialWidthFraction_le_allocated_width h2P hW
      (hWP.trans (Real.exp_le_exp.mpr hP2P)) hτξ.le N z).trans
        (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
  have hη : 0 < positiveProjectionAccuracy P := Real.exp_pos _
  have hηQ : 1 / positiveProjectionAccuracy P ≤ Real.exp Q := by
    simp only [one_div, positiveProjectionAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr (hdata.2.2.1.trans hdataQ)
  have hlocal (base : X → ℤ)
      (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ)
      (hamp : ∀ x, ‖amplitude x‖ ≤ 1) {Lip : ℝ≥0}
      (hLip : LipschitzWith Lip amplitude) (hLipP : (Lip : ℝ) ≤ Real.exp P) :
      ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z,
        ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
          ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (amplitude (fun t => (z t : ℝ) / widths t) * (density base z : ℂ))) -
          ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
            ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
              amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
          3 * positiveProjectionAccuracy P := by
    have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa base j) :=
      degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
    have hranka (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa base j) :=
      (hasLayerSamplingRank_translate_iff _ _ _ _ _ _ (hp j)).mpr (hrank j)
    obtain ⟨hZ, hclose⟩ := hmass hQ (hX.trans hPQ) (hdim.trans hPQ) U μ
      (Real.exp_nonneg Q) le_rfl frequency
      (fun t j d hd i => (hfreq t j d hd i).trans (Real.exp_le_exp.mpr hdataQ))
      coeff (Real.exp_nonneg Q) le_rfl (hcoeff.trans (Real.exp_le_exp.mpr hdataQ))
      (pa base) hpa (hma base) stride hs (Real.exp_nonneg Q) le_rfl
      (spatialWidthFraction_pos (2 * P) hτξ) hη
      ((spatialWidthFraction_inv_le h2P hτξ hτξP).trans (Real.exp_le_exp.mpr hspatialQ)) hηQ
      (fun d => (hsP d).trans hExp) (fun d => (N d : ℝ))
      (fun d => (Real.exp_le_exp.mpr hcut).trans (hsize d)) hranka
      ((Real.exp_le_exp.mpr hcut).trans hRank) T hT widths hwidths
      hwidthLower amplitude hamp hLip (hLipP.trans hExp)
      (allocatedCoefficientDensity B U basis hb o hR hσ S) hspec.2.2.1 hspec.2.2.2.1 hη.le happ
    refine ⟨hZ, ?_⟩
    exact hclose.trans_eq (by ring)
  obtain ⟨hZ, _⟩ := hlocal 0 (fun _ => 0) (by simp) (LipschitzWith.const 0)
    (by simpa using (Real.exp_nonneg P))
  refine ⟨hwidths, hZ, ?_, ?_⟩
  · intro base amplitude hamp Lip hLip hLipP
    exact (hlocal base amplitude hamp hLip hLipP).choose_spec
  · intro base
    have hmass := selectedResidueDensityMass_bound_of_constant_test stride T widths hwidths hZ
      (density base) ((hlocal base (fun _ => 1) (by simp) (LipschitzWith.const 1)
        (by simpa using (Real.exp_nonneg P))).choose_spec)
    have hD0 : ∀ z, 0 ≤ density base z := fun _ => hspec.2.1 _
    have hD := (positiveProjectionAccuracy_normalizer hP hmass).2.2.1
    refine ⟨hmass, hD0, hD, ?_⟩
    intro amplitude hamp Lip hLip hLipP
    have htest := (hlocal base amplitude hamp hLip hLipP).choose_spec
    have hn := selectedResidueDensityPMF_error_of_bounded_test stride T widths hwidths hZ
      (density base) hD0 hD (fun z => amplitude (fun t => (z t : ℝ) / widths t))
      (fun z => hamp _) htest hmass
    exact hn.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedMaskedChartProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d quarter

noncomputable def allocatedMaskedSiteChartFactor
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) : EuclideanJetLayers U single → ℂ :=
  restrictedComplexChartDensity chart region 1 (fun w =>
    if mixedCoveredSiteResidue d period w = label then
      allocatedBufferedMixedSiteFactor B U b S r hr f (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())
    else 0)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecenteredIdealError
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

noncomputable def allocatedProductChartIdealApproximation {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (y : EuclideanJetLayers U rowTypes) : ℂ :=
  ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
    allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k *
      ∏ s, allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period (label s) (f k s)
        (coveredRowsSiteValue rowSets U y s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

def AllocatedLongPhysicalExpansionIdentity (gl : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) → T → Finset (Fin dim) → LongSpace → ℂ) : Prop :=
  ∀ (v : X → (Unit ⊕ Fin dim) → ℤ),
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
      (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) =
      ∑ label, ∑ i, ((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) * ∏ s, gl label i s (physicalMaskedFactorInput period p (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)))

def AllocatedGridPhysicalExpansionIdentity (gg : (∀ a, (e a).Term) → Finset (Fin dim) → GridSpace → ℂ) : Prop :=
  ∀ (v : X → (Unit ⊕ Fin dim) → ℤ),
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
      (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) * allocatedFullGridChartModel B U b S rowSets d hb o bW e
      (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) =
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
      (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) * ∑ k, coverSiteCoefficient e k * ∏ s, gg k s (physicalGridFactorInput (commonSitePeriod e k) p (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)))

def AllocatedModelPhysicalExpansionIdentity
    (g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) → T → (∀ a, (e a).Term) → Finset (Fin dim) → LongSpace × GridSpace → ℂ) : Prop :=
  ∀ (v : X → (Unit ⊕ Fin dim) → ℤ),
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
      (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) * allocatedFullGridChartModel B U b S rowSets d hb o bW e
      (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) =
      ∑ label, ∑ i, ∑ k, (((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) * coverSiteCoefficient e k) *
        ∏ s, g label i k s (physicalMaskedFactorInput period p (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)), physicalGridFactorInput (commonSitePeriod e k) p (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistSliceVariationPairCorrelation
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

namespace VectorPolynomial.NormalizedPolynomialTwist

theorem exists_untwisted_subrectangle_of_fullSliceLaw_of_variation
    {K : Type*} [Fintype K] [DecidableEq K]
    {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (hq : 0 < q)
    (hlen : ∀ k, 0 < S.length k) {cost p : ℝ} (hp : 0 ≤ p)
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hP : ∀ k, Real.exp (cost + (3 * p + 16)) ≤ (P k : ℝ))
    {M : ℕ} (hM : 0 < M) (hMexp : (M : ℝ) ≤ Real.exp p)
    (twist : integerBox P → ℂ) (htwist : ∀ t, ‖twist t‖ ≤ 1)
    {ε : ℝ}
    (hvariation : ∀ u v : integerBox P,
      (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
      (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤
        2 * (Real.exp (-(2 * p)) / 4)) → ‖twist u - twist v‖ ≤ ε)
    (signal : integerBox P → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsignal : ∀ t, ‖signal t‖ ≤ 1)
    (hbias : δ ≤ ‖(S.fullSliceLaw hlen).complexMean
      (fun t => star (twist t) * signal t)‖) :
    ∃ T : ResidueBoxSlice P (q * M),
      0 < q * M ∧ (∀ k, 0 < T.length k) ∧
      (∀ k, Real.exp (-(cost + (3 * p + 16))) * (P k : ℝ) ≤ T.length k) ∧
      δ / 2 - ε ≤
        ‖𝔼 t : (∀ k, Fin (T.length k)), signal (T.fullSlicePointInIntegerBox t)‖ := by
  have hSL : ∀ k, Real.exp (3 * p + 16) ≤ (S.length k : ℝ) :=
    fun k => S.length_large_of_cost hS hP k
  have htwo : ∀ k, 2 ≤ S.length k := by
    intro k
    have he := Real.add_one_le_exp (3 * p + 16)
    have hh := hSL k
    have : (2 : ℝ) ≤ S.length k := by linarith
    exact_mod_cast this
  let : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  obtain ⟨Q, hstep, hlength, hlower, _, hnear, _, _⟩ :=
    exists_normalizedTwist_parameter_partition S.length M p hp hM hMexp hSL
  let label := BoxProgressionPartition.cell Q
  let base := fun (c : ∀ k, (Q k).Label) =>
    BoxProgressionPartition.point Q c (fun k => ⟨0, hlength k (c k)⟩)
  let coefficient := fun c => twist (S.fullSlicePointInIntegerBox (base c))
  have herr (c : ∀ k, (Q k).Label) (t : ∀ k, Fin ((Q k).length (c k))) :
      ‖twist (S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c t)) -
        coefficient c‖ ≤ ε := by
    apply hvariation
    · intro k
      simp only [ResidueBoxSlice.fullSlicePointInIntegerBox, ResidueBoxSlice.point,
        BoxProgressionPartition.point, FiniteProgressionPartition.point_val, hstep, base,
        Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, Nat.cast_zero,
        zero_mul, add_zero]
    · exact S.fullSlicePoint_normalized_distance_le htwo _ _
        (fun k => hnear k (c k) (t k) ⟨0, hlength k (c k)⟩)
  let μ := FiniteProbabilityWeights.uniform (∀ k, Fin (S.length k))
  let pulledTwist := fun u => twist (S.fullSlicePointInIntegerBox u)
  let pulledSignal := fun u => signal (S.fullSlicePointInIntegerBox u)
  have hbound : δ ≤ ‖μ.complexMean (fun u => star (pulledTwist u) * pulledSignal u)‖ := by
    rw [S.fullSliceLaw_complexMean] at hbias
    simpa only [μ, pulledTwist, pulledSignal, FiniteProbabilityWeights.uniform_complexMean] using hbias
  let : Nonempty (∀ k, (Q k).Label) := ⟨fun k => (Q k).cell ⟨0, hlen k⟩⟩
  obtain ⟨c, hc, _, hb⟩ := μ.exists_large_correlating_fiber label
    (fun t => star (pulledTwist t) * pulledSignal t) hδ (fun t => by
      rw [norm_mul, norm_star]
      exact (mul_le_mul (htwist _) (hsignal _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1)) hbound
  let ν := μ.condition (Finset.univ.filter (fun t => label t = c)) hc
  have hcorr : δ / 2 - ε ≤ ‖ν.complexMean pulledSignal‖ := by
    apply correlation_after_freezing ν pulledTwist pulledSignal (coefficient c)
      (htwist _) (fun t => hsignal _) ?_ hb
    intro t ht
    have htc : label t = c := by
      by_contra hn
      exact ht (by simp only [ν, FiniteProbabilityWeights.condition,
        Finset.mem_filter, Finset.mem_univ, true_and, hn, ite_false, zero_div])
    have he := herr (label t) (fun k => (Q k).offset (t k))
    have hpoint : BoxProgressionPartition.point Q (label t)
        (fun k => (Q k).offset (t k)) = t := by
      funext k
      exact (Q k).point_cell_offset (t k)
    rw [hpoint, htc] at he
    exact he
  let T₀ := ResidueBoxSlice.parameterCell Q hstep c
  let T := S.composeSlice T₀
  have heval (u : ∀ k, Fin ((Q k).length (c k))) :
      T.fullSlicePointInIntegerBox u =
        S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u) := by
    apply Subtype.ext
    funext k
    change ((S.start k + q * (Q k).start (c k) +
      (q * M) * (u k).val : ℕ) : ℤ) =
        ((S.start k + q * ((Q k).point (c k) (u k)).val : ℕ) : ℤ)
    rw [FiniteProgressionPartition.point_val, hstep]
    push_cast
    ring
  refine ⟨T, mul_pos hq hM, fun k => hlength k (c k), ?_, ?_⟩
  · exact fun k => S.composeSlice_length_lower T₀ hS (fun k => hlower k (c k)) k
  · have hmean : ν.complexMean pulledSignal =
        𝔼 u, signal (S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u)) := by
      dsimp only [ν, μ, pulledSignal]
      rw [FiniteProbabilityWeights.uniform_condition_complexMean]
      have hset : Finset.univ.filter (fun t => label t = c) =
          partitionCell (BoxProgressionPartition.cell Q) c := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_partitionCell, label]
      rw [hset, BoxProgressionPartition.expect_cell_complex]
    rw [hmean] at hcorr
    have hexpect : (𝔼 t : (∀ k, Fin (T.length k)), signal (T.fullSlicePointInIntegerBox t)) =
        𝔼 u : (∀ k, Fin ((Q k).length (c k))),
          signal (S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u)) := by
      change (𝔼 t : (∀ k, Fin ((Q k).length (c k))), signal (T.fullSlicePointInIntegerBox t)) = _
      apply Finset.expect_congr rfl
      intro t _
      rw [heval]
    rwa [hexpect]

end VectorPolynomial.NormalizedPolynomialTwist
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical TensorProduct NNReal

namespace VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel

theorem exists_niltest_pair_correlation_subrectangle_of_variation
    {K : Type*} [Fintype K] [DecidableEq K]
    {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (hq : 0 < q)
    (hlen : ∀ k, 0 < S.length k) {cost p : ℝ} (hp : 0 ≤ p)
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hP : ∀ k, Real.exp (cost + (3 * p + 16)) ≤ (P k : ℝ))
    {M : ℕ} (hM : 0 < M) (hMexp : (M : ℝ) ≤ Real.exp p)
    (twist : integerBox P → ℂ) (htwist : ∀ t, ‖twist t‖ ≤ 1)
    {ε : ℝ}
    (hvariation : ∀ u v : integerBox P,
      (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
      (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤
        2 * (Real.exp (-(2 * p)) / 4)) → ‖twist u - twist v‖ ≤ ε)
    {LG MG : Type*} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
    {s d e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
    {D : RationalFilteredNilmanifold LG s d} {E : RationalFilteredNilmanifold MG s e}
    (V : D.Niltest (fun _ : K => 1)) (Wlocal : E.Niltest (fun _ : K => 1))
    {pLocal : ℝ} (hV : V.ComplexityLE pLocal) (hW : Wlocal.normBound ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
      star (twist t) *
        (V.eval t.val * Wlocal.eval t.val))‖) :
    ∃ T : ResidueBoxSlice P (q * M),
      0 < q * M ∧
      (∀ k, 0 < T.length k) ∧
      (∀ k, Real.exp (-(cost + (3 * p + 16))) * (P k : ℝ) ≤ T.length k) ∧
      δ / 2 - Real.exp pLocal *
          ε ≤
        ‖𝔼 x ∈ translatedIntegerBox (0 : K → ℤ) T.length,
          V.eval (fun k => ((q * M : ℕ) : ℤ) * x k + T.start k) *
          Wlocal.eval (fun k => ((q * M : ℕ) : ℤ) * x k + T.start k)‖ := by
  let signal : integerBox P → ℂ := fun t =>
    (Real.exp (-pLocal) : ℂ) * (V.eval t.val * Wlocal.eval t.val)
  have hsignal : ∀ t, ‖signal t‖ ≤ 1 := by
    intro t
    have hpartner : ‖Wlocal.eval t.val‖ ≤ 1 :=
      (Wlocal.norm_eval_le _).trans (by exact_mod_cast hW)
    have hprod : ‖V.eval t.val * Wlocal.eval t.val‖ ≤ Real.exp pLocal := by
      rw [norm_mul]
      exact (mul_le_mul (V.eval_budget hV _) hpartner (norm_nonneg _)
        (Real.exp_nonneg _)).trans_eq (mul_one _)
    dsimp only [signal]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ Real.exp (-pLocal) * Real.exp pLocal :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hscaled : Real.exp (-pLocal) * δ ≤ ‖(S.fullSliceLaw hlen).complexMean
      (fun t => star (twist t) * signal t)‖ := by
    have heq : (S.fullSliceLaw hlen).complexMean
        (fun t => star (twist t) * signal t) =
        (Real.exp (-pLocal) : ℂ) * (S.fullSliceLaw hlen).complexMean (fun t =>
          star (twist t) *
            (V.eval t.val * Wlocal.eval t.val)) := by
      rw [← FiniteProbabilityWeights.complexMean_mul_left]
      congr 1
      funext t
      dsimp only [signal]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left hbias (Real.exp_nonneg _)
  obtain ⟨T, hTq, hTlen, hTlength, hc⟩ := exists_untwisted_subrectangle_of_fullSliceLaw_of_variation
    S hq hlen hp hS hP hM hMexp twist htwist hvariation signal
    (mul_pos (Real.exp_pos _) hδ) hsignal hscaled
  have hmean : ‖𝔼 t : (∀ k, Fin (T.length k)), signal (T.fullSlicePointInIntegerBox t)‖ =
      Real.exp (-pLocal) *
        ‖𝔼 t : (∀ k, Fin (T.length k)),
          V.eval (T.fullSlicePointInIntegerBox t).val * Wlocal.eval (T.fullSlicePointInIntegerBox t).val‖ := by
    simp only [signal, ← Finset.mul_expect, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _)]
  rw [hmean] at hc
  have he : Real.exp pLocal * Real.exp (-pLocal) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hrestore := mul_le_mul_of_nonneg_left hc (Real.exp_nonneg pLocal)
  have hlhs : Real.exp pLocal * (Real.exp (-pLocal) * δ / 2 -
      ε) =
      δ / 2 - Real.exp pLocal *
        ε := by
    rw [mul_sub, ← mul_div_assoc, ← mul_assoc, he, one_mul]
  have hcancel (x : ℝ) : Real.exp pLocal * (Real.exp (-pLocal) * x) = x := by
    rw [← mul_assoc, he, one_mul]
  rw [hlhs, hcancel] at hrestore
  refine ⟨T, hTq, hTlen, hTlength, ?_⟩
  rwa [T.fin_mean_eq_translated_zero (fun x => V.eval x * Wlocal.eval x)] at hrestore

end VectorPolynomial.NormalizedPolynomialTwist
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueCutoffDomination
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]
variable (q : I → ℕ) (T : Finset (ColumnResiduePattern K I q))
variable (V : K × I → ℝ)

theorem selectedResidueFiniteLaw_normalized_norm_le (hV : ∀ t, 0 < V t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (z : rectangularWeightIndices 0 V 1)
    (hz : 0 < (selectedResidueFiniteLaw q T V hV hZ).weight z) :
    ‖fun t => (z.val t : ℝ) / V t‖ ≤ 1 := by
  apply selectedResidueSmoothWeight_normalized_norm_le q T V z.val
  intro he
  change 0 < selectedResidueSmoothWeight q T V z.val /
    (∑' x, selectedResidueSmoothWeight q T V x) at hz
  rw [he, zero_div] at hz
  exact (lt_irrefl 0) hz

theorem selectedJointFiniteLaw_normalized_norm_le {A : Type*}
    (bases : Finset A) (hbases : bases.Nonempty) (hV : ∀ t, 0 < V t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (D : A → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass bases q T V D)
    (z : bases × rectangularWeightIndices 0 V 1)
    (hz : 0 < (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD).weight z) :
    ‖fun t => (z.2.val t : ℝ) / V t‖ ≤ 1 := by
  apply selectedResidueSmoothWeight_normalized_norm_le q T V z.2.val
  intro he
  rw [selectedJointFiniteLaw_weight, selectedResidueSmoothPMF_toReal, he, zero_div,
    mul_zero, zero_mul, zero_div] at hz
  exact (lt_irrefl 0) hz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

theorem principalCoefficientSlot_eq_block_sum (h : D → ℕ) (d : D) (b : B d) :
    (principalCoefficientSlot (G := G) h d b).val =
      ∑ k ∈ canonicalRankBlock h d b, Finsupp.single k 1 := by
  simp only [principalCoefficientSlot, canonicalPrincipalExponent, productBlockExponent,
    canonicalRankBlock, Finset.sum_map, canonicalRankBlockEmbedding]
  rfl

theorem principalCoefficientSlot_monomial {R : Type*} [CommSemiring R]
    (h : D → ℕ) (d : D) (b : B d) (c : R) :
    MvPolynomial.monomial (principalCoefficientSlot (G := G) h d b).val c =
      MvPolynomial.C c * ∏ k ∈ canonicalRankBlock h d b, MvPolynomial.X k := by
  rw [principalCoefficientSlot_eq_block_sum, MvPolynomial.monomial_sum_index]
  rfl

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators Classical

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

theorem kernelRankCoefficientSlot_degree (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    (kernelRankCoefficientSlot (B := B) degree e a).val.degree = h :=
  productBlockExponent_degree _

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

theorem samplerLongEmbedding_principalExponent (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (b : B d.val) :
    ((principalCoefficientSlot (G := G) (B := fun a : {a // ¬ inactive a} => B a.val)
      (fun a => h a.val) d b).val).mapDomain (samplerLongEmbedding inactive h) =
        (principalCoefficientSlot h d.val b).val := by
  simp only [principalCoefficientSlot, canonicalPrincipalExponent, productBlockExponent,
    Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single, samplerLongEmbedding_dedicated]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

variable {D G R : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R]

omit [Fintype D] [Fintype G] [∀ d, Fintype (B d)] in
theorem canonicalPrincipalSubblockSlot_injective (h : D → ℕ) (d : D) (hd : 0 < h d)
    {J : ℕ} (block : Fin J ↪ B d) :
    Function.Injective (canonicalPrincipalSubblockSlot (G := G) h d block) :=
  (principalCoefficientSlot_injective h d hd).comp block.injective

omit [Fintype D] [Fintype G] [∀ d, Fintype (B d)] in
theorem canonicalPrincipalSubblockSlot_degree (h : D → ℕ) (d : D) {J : ℕ}
    (block : Fin J ↪ B d) (j : Fin J) :
    (canonicalPrincipalSubblockSlot (G := G) h d block j).val.degree = h d :=
  canonicalPrincipalExponent_degree h d (block j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedFiniteForwardDetectorPolynomial_bounds (depth : ℕ)
    {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) :
    p ≤ (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog u p) ∧
    ∀ r ≤ depth, OrdinaryPolynomialPhase.budget r ≤
      (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog u p) := by
  rw [preparedFiniteForwardDetectorPolynomial_eval]
  have hc : 0 ≤ (preparedFiniteForwardDetectorOffset depth : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ allocatedModelTestLog u p := by
    unfold allocatedModelTestLog
    positivity
  constructor
  · unfold allocatedModelTestLog
    linarith only [hu, hp, hc]
  · intro r hr
    exact (preparedFiniteForwardDetectorOffset_phase depth r hr).trans
      (le_add_of_nonneg_left hlog)

theorem preparedFiniteForwardDetectorPolynomial_stage_bounds
    (depth A Cdirect : ℕ) (constants : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    preparedFiniteForwardWork A constants n x ≤
      (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision A Cdirect constants n isDirect x gainLog stageLog)
          (preparedFiniteForwardWork A constants n x)) ∧
    ∀ r ≤ depth, OrdinaryPolynomialPhase.budget r ≤
      (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision A Cdirect constants n isDirect x gainLog stageLog)
          (preparedFiniteForwardWork A constants n x)) :=
  preparedFiniteForwardDetectorPolynomial_bounds depth
    (preparedFiniteForwardPairedSourcePrecision_nonneg A Cdirect constants n isDirect hx hg hs)
    (preparedFiniteForwardWork_nonneg A constants n hx)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFixedScaleProductiveNarrowSampler
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def AllocatedFixedScaleProductiveStatement (m A : ℕ) : Prop :=
    ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P) (_hτhalf : τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    ∃ (_hN : ∀ i, 0 < N i) (hwidths : ∀ z, 0 < widths z)
      (hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z)
      (hD : ∀ center, 0 < selectedJointDensityMass bases stride T widths (density center)),
    let law := fun center => selectedJointFiniteLaw bases
      (trimmedIntegerBox_nonempty N _ hmargin) stride T widths hwidths hmass
      (density center) (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
      (hD center)
    (∀ center,
      let Z := selectedJointDensityMass bases stride T widths (density center)
      |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ Z⁻¹ ≤ 2) ∧
    ∀ {Sites : Type*} [Fintype Sites] [DecidableEq Sites] [Nonempty Sites]
      (site : Sites → LayerSamplerVariables G I n B → ℤ),
      Function.Injective site → (∀ q, (∑ k, |(site q k : ℝ)|) ≤ W) →
    ∀ (test : (X → ℝ) → ℝ), (∀ x, |test x| ≤ 1) →
    ∀ gain : ℝ, 0 < gain → Real.exp (-P) ≤ gain / 16 →
      12 * positiveProjectionAccuracy P + 2 * (Fintype.card X : ℝ) * τ ≤ gain / 8 →
      gain ≤ (𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) →
    let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
      Function.Injective (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) ∧
        gain / 2 ≤ 𝔼 q : Sites, test
          (fun i => (jointIntegerPhysicalSite (site q) (z.1.val,z.2.val) i : ℝ)))
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) | z.2 ∈ productive} ∧
      gain / 4 ≤ joint.real {z | z.2 ∈ productive} ∧
      (∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))) ∧
        allocatedAffineDensity B U basis hb o hR hσ S p hm c
          (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0) ∧
      ∀ z : bases × rectangularWeightIndices 0 widths 1, ∀ q,
        jointIntegerPhysicalSite (site q) (z.1.val,z.2.val) ∈ integerBox N

end Erdos3.VectorPolynomial

end

end OAI
end


