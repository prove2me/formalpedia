-- Prove2me | Definitions.Def_OAIErdos3B185
-- name    : OAIErdos3B185
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T07:03:23.317682+00:00
-- url     : https://prove2.me/theorems/8c33eb28-d759-4f91-a34b-1e0643adfece
-- title:
--   OpenAI Erdős-3 split, definitions bundle 186 of 191
-- statement:
--   Definitions bundle 186 of 191 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B184`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 186 available.
--
--   Modules: `OAI.Erdos3.FreeDegreeRankLieAlgebra.gradingExpansion`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.gradingHom`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.gradingHom_eval_one`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.gradingHom_of`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.gradingHom_tree`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.homogeneousSpan_inter`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.lift_top_frequency_zero`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.lift_top_mem_degreeLengthSpan`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.markedLayer`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.markedLayerIdeal`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.markedLayer_eq_homogeneousSpan`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.markedLayer_inf`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.markedLayer_le_degreeRank`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.markedLayer_lie_mem`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.markedLayer_separate_inter`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.markedLayer_zero`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.topLayer_eq_markedLayer`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.topLayer_inter_markedIdeal`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.lift_layer_mem_degreeLengthSpan`, `OAI.Erdos3.NativePolynomialOrbitFactors.FrozenMiddleRealization.noConfusion`, `OAI.Erdos3.NilpotentLieFiltration.top_rank_map_mem_degreeLengthSpan`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.exists_polynomialOrbit_factorization_rank_two`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.polynomialOrbit_mul_coefficient_sub_mem_rank_two`, `OAI.Erdos3.RationalFilteredNilmanifold.frozen_refiltered_group_action`, `OAI.Erdos3.VectorPolynomial.LowTaggedIndex`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.exists_correlating_frequency`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.exists_correlating_frequency_early`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.exists_correlating_frequency_product_early`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.exists_frozen_ambient_fourier`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.exists_localized_correlating_frequency`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.norm_correlation_star_eq_product`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedRadiusInput`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedRadiusInput_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedRadiusLog`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedRadius_inverse_from_primitive`, `OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_source_geometry`, `OAI.Erdos3.VectorPolynomial.allocatedCommonProductRadius`, `OAI.Erdos3.VectorPolynomial.allocatedCommonProductRadiusLog`, `OAI.Erdos3.VectorPolynomial.allocatedCommonProductRadiusLog_mono`, `OAI.Erdos3.VectorPolynomial.allocatedCommonProductRadius_admissible`, `OAI.Erdos3.VectorPolynomial.allocatedCommonProductRadius_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedCommonRadius`, `OAI.Erdos3.VectorPolynomial.allocatedCommonRadiusLog`, `OAI.Erdos3.VectorPolynomial.allocatedCommonRadiusLog_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedCommonRadiusLog_mono`, `OAI.Erdos3.VectorPolynomial.allocatedCommonRadius_admissible`, `OAI.Erdos3.VectorPolynomial.allocatedProductChartLog`, `OAI.Erdos3.VectorPolynomial.allocatedProductChartLog_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedProductChartLog_mono`, `OAI.Erdos3.VectorPolynomial.allocatedProductChartRadius`, `OAI.Erdos3.VectorPolynomial.allocatedProductChartRadius_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedProductChartRadius_le_charts`, `OAI.Erdos3.VectorPolynomial.allocatedProductGridRadius_inv_exp_bound`, `OAI.Erdos3.VectorPolynomial.allocatedProductIdealSiteRadius_exp_bound`, `OAI.Erdos3.VectorPolynomial.exists_allocatedCommonProductRadiusLog_bound`, `OAI.Erdos3.VectorPolynomial.forecastCongruenceJointAxisEquiv`, `OAI.Erdos3.VectorPolynomial.forecastJointAxisEquiv`, `OAI.Erdos3.VectorPolynomial.forecastJointCoordinateJoin`, `OAI.Erdos3.VectorPolynomial.forecastJointCoordinateJoinEquiv`, `OAI.Erdos3.VectorPolynomial.forecastJointOriginalGridMean`, `OAI.Erdos3.VectorPolynomial.highest_nonannihilating_tag`, `OAI.Erdos3.VectorPolynomial.integerRowPolynomial_constant_of_annihilates`, `OAI.Erdos3.VectorPolynomial.integerRowPolynomial_truncateTaggedFrequency`, `OAI.Erdos3.VectorPolynomial.lowTaggedEmbedding`, `OAI.Erdos3.VectorPolynomial.lowTaggedEmbedding_apply`, `OAI.Erdos3.VectorPolynomial.lowTaggedEmbedding_apply_of_ne`, `OAI.Erdos3.VectorPolynomial.lowTaggedEmbedding_apply_slot`, `OAI.Erdos3.VectorPolynomial.lowTaggedEmbedding_pairing`, `OAI.Erdos3.VectorPolynomial.lowTaggedEmbedding_restriction`, `OAI.Erdos3.VectorPolynomial.lowTaggedFrequency`, `OAI.Erdos3.VectorPolynomial.lowTaggedFrequency_bound`, `OAI.Erdos3.VectorPolynomial.lowTaggedIndex`, `OAI.Erdos3.VectorPolynomial.lowTaggedIndex_card_le`, `OAI.Erdos3.VectorPolynomial.lowTaggedIndex_property`, `OAI.Erdos3.VectorPolynomial.lowTaggedIndex_slot`, `OAI.Erdos3.VectorPolynomial.lowTaggedPolynomial`, `OAI.Erdos3.VectorPolynomial.lowTaggedPolynomial_coeff`, `OAI.Erdos3.VectorPolynomial.lowTaggedPolynomial_degree`, `OAI.Erdos3.VectorPolynomial.lowTaggedPolynomial_eval`, `OAI.Erdos3.VectorPolynomial.lowTaggedRestriction`, `OAI.Erdos3.VectorPolynomial.lowTaggedRestriction_apply`, `OAI.Erdos3.VectorPolynomial.lowTaggedRestriction_embedding`, `OAI.Erdos3.VectorPolynomial.lowTaggedRetained`, `OAI.Erdos3.VectorPolynomial.lowTaggedSlot`, `OAI.Erdos3.VectorPolynomial.lowTaggedSlot_eq_of_tag`, `OAI.Erdos3.VectorPolynomial.lowTaggedSlot_injective`, `OAI.Erdos3.VectorPolynomial.lowTaggedTopPolynomial`, `OAI.Erdos3.VectorPolynomial.lowTaggedTopPolynomial_coeff_apply`, `OAI.Erdos3.VectorPolynomial.lowTaggedTopPolynomial_coeff_mem_iSup`, `OAI.Erdos3.VectorPolynomial.lowTaggedTopPolynomial_coeff_of_degree`, `OAI.Erdos3.VectorPolynomial.lowTaggedTopPolynomial_hasLayerSamplingRank`, `OAI.Erdos3.VectorPolynomial.lowTaggedTopPolynomial_row_layer`, `OAI.Erdos3.VectorPolynomial.lowTaggedWeight`, `OAI.Erdos3.VectorPolynomial.lowTaggedWeight_le`, `OAI.Erdos3.VectorPolynomial.lowTaggedWeight_pos`, `OAI.Erdos3.VectorPolynomial.lowTagged_comap_eq_map`, `OAI.Erdos3.VectorPolynomial.lowTagged_comap_span_eq`, `OAI.Erdos3.VectorPolynomial.lowTagged_sum`, `OAI.Erdos3.VectorPolynomial.normalizedTwistFrequencyPolynomial`, `OAI.Erdos3.VectorPolynomial.normalizedTwistFrequencyPolynomial_eval`, `OAI.Erdos3.VectorPolynomial.normalizedTwistFrequencyPolynomial_low_add_constant`, `OAI.Erdos3.VectorPolynomial.normalizedTwistFrequencyPolynomial_low_degree`, `OAI.Erdos3.VectorPolynomial.normalizedTwistFrequencyPolynomial_low_eval`, `OAI.Erdos3.VectorPolynomial.normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist`, `OAI.Erdos3.VectorPolynomial.normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist_affine`, `OAI.Erdos3.VectorPolynomial.normalizedTwistFrequencyPolynomial_top_not_approximation`, `OAI.Erdos3.VectorPolynomial.normalizedTwistFrequencyPolynomial_truncate`, `OAI.Erdos3.VectorPolynomial.normalizedTwistHighFrequencyConstant`, `OAI.Erdos3.VectorPolynomial.physicalGrid_character_eq_polynomial_phase`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForward_shiftedPower_le_work`, `OAI.Erdos3.VectorPolynomial.taggedScalarHighConstant`, `OAI.Erdos3.VectorPolynomial.taggedScalarLowPolynomial`, `OAI.Erdos3.VectorPolynomial.taggedScalarLowPolynomial_degree`, `OAI.Erdos3.VectorPolynomial.taggedScalar_sum_degree`, `OAI.Erdos3.VectorPolynomial.taggedScalar_sum_eq_low_add_constant`, `OAI.Erdos3.VectorPolynomial.taggedScalar_sum_top`, `OAI.Erdos3.VectorPolynomial.truncateTaggedFrequency`, `OAI.Erdos3.exists_fixed_model_frozen_comparison`, `OAI.Erdos3.exists_native_frozen_comparison`, `OAI.Erdos3.finiteRowChartRadius_support_le_inv`, `OAI.Erdos3.markedGradeRegion`, `OAI.Erdos3.markedGradeRegion_inter`, `OAI.Erdos3.pi_basisGradeProjection_apply`, `OAI.Erdos3.rankUnitDescentConstant`, `OAI.Erdos3.sum_positive_coordinate_grades`, `OAI.Erdos3.torus_integer_character_real_phase`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B152
import Definitions.Def_OAIErdos3B186

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
namespace OAI

section

namespace Erdos3.FreeDegreeRankLieAlgebra

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x) (marked : X → Bool)

noncomputable def markedLayer (d k l : ℕ) : Submodule ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  markedLieSpan (of X s r w hw) w marked d k l

theorem markedLayer_lie_mem {d e k m l n : ℕ} {x y : FreeDegreeRankLieAlgebra X s r w hw}
    (hx : x ∈ markedLayer X s r w hw marked d k l)
    (hy : y ∈ markedLayer X s r w hw marked e m n) :
    ⁅x, y⁆ ∈ markedLayer X s r w hw marked (d + e) (k + m) (l + n) :=
  markedLieSpan_lie_mem _ _ _ hx hy

theorem markedLayer_zero : markedLayer X s r w hw marked 0 0 0 = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := projection_surjective X s r w hw x
  obtain ⟨z, rfl⟩ := FreeNilpotentLieAlgebra.mk_surjective X s y
  let φ := (projection X s r w hw).comp (FreeNilpotentLieAlgebra.mk X s)
  change φ z ∈ markedLayer X s r w hw marked 0 0 0
  apply freeLie_linear_induction (fun z => φ z ∈ markedLayer X s r w hw marked 0 0 0)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  · intro c a ha
    rw [map_smul]
    exact Submodule.smul_mem _ c ha
  · intro a
    rw [map_lieTreeEval]
    change lieTreeEval (of X s r w hw) a ∈ markedLayer X s r w hw marked 0 0 0
    exact Submodule.subset_span ⟨a, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩

noncomputable def markedLayerIdeal (d k l : ℕ) : LieIdeal ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  { markedLayer X s r w hw marked d k l with
    lie_mem := by
      intro x y hy
      have hx : x ∈ markedLayer X s r w hw marked 0 0 0 := by
        rw [markedLayer_zero]
        trivial
      change ⁅x, y⁆ ∈ markedLayer X s r w hw marked d k l
      simpa only [Nat.zero_add] using markedLayer_lie_mem X s r w hw marked hx hy }

theorem markedLayer_le_degreeRank (hr : r ≤ s) (d k l : ℕ) :
    markedLayer X s r w hw marked d k l ≤ (filtration X s r w hw hr).layer d l :=
  markedLieSpan_le_layer (filtration X s r w hw hr) _ _ _
    (of_mem_layer X s r w hw hr) d k l

end Erdos3.FreeDegreeRankLieAlgebra

end

section

namespace Erdos3.FreeDegreeRankLieAlgebra

open VectorPolynomial

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (hr : r ≤ s) {σ : Type*} (g : X → σ →₀ ℕ)

noncomputable def gradingHom :
    FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆
      VectorPolynomial σ ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  lift ((filtration X s r w hw hr).polynomialFiltration (σ := σ)) w hw
    (fun x => monomial (g x) (of X s r w hw x)) (fun x => by
      apply (filtration X s r w hw hr).monomial_mem_polynomialFiltration
      rw [(filtration X s r w hw hr).rank_zero_eq_one]
      exact of_mem_layer X s r w hw hr x)

@[simp] theorem gradingHom_of (x : X) :
    gradingHom X s r w hw hr g (of X s r w hw x) = monomial (g x) (of X s r w hw x) := by
  simp only [gradingHom, lift_of]

theorem gradingHom_tree (a : FreeMagma X) :
    gradingHom X s r w hw hr g (lieTreeEval (of X s r w hw) a) =
      monomial (lieTreeMultidegree g a) (lieTreeEval (of X s r w hw) a) := by
  induction a using FreeMagma.rec with
  | of x => exact gradingHom_of X s r w hw hr g x
  | mul a b ha hb =>
    change gradingHom X s r w hw hr g
      ⁅lieTreeEval (of X s r w hw) a, lieTreeEval (of X s r w hw) b⁆ = _
    rw [LieHom.map_lie, ha, hb, lie_monomial]
    rfl

theorem gradingHom_eval_one (x : FreeDegreeRankLieAlgebra X s r w hw) :
    eval (fun _ : σ => (1 : ℚ)) (gradingHom X s r w hw hr g x) = x := by
  have h : (evalLie (fun _ : σ => (1 : ℚ))).comp (gradingHom X s r w hw hr g) =
      (LieHom.id : FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆ FreeDegreeRankLieAlgebra X s r w hw) := by
    apply hom_ext w hw
    intro y
    change eval (fun _ : σ => (1 : ℚ)) (gradingHom X s r w hw hr g (of X s r w hw y)) = _
    rw [gradingHom_of]
    simp
  exact LieHom.congr_fun h x

noncomputable def gradingExpansion : LieGradingExpansion (of X s r w hw) g where
  expand := (gradingHom X s r w hw hr g).toLinearMap
  expand_tree := gradingHom_tree X s r w hw hr g
  eval_one := gradingHom_eval_one X s r w hw hr g

include hr in
theorem homogeneousSpan_inter (S T : Set (σ →₀ ℕ)) :
    homogeneousLieSpan (of X s r w hw) g (S ∩ T) =
      homogeneousLieSpan (of X s r w hw) g S ⊓ homogeneousLieSpan (of X s r w hw) g T :=
  (gradingExpansion X s r w hw hr g).span_inter S T

end Erdos3.FreeDegreeRankLieAlgebra

end

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem NilpotentLieFiltration.top_rank_map_mem_degreeLengthSpan {s k : ℕ}
    (F : NilpotentLieFiltration L s) (φ : L →ₗ⁅ℚ⁆ M) (v : X → M) (w : X → ℕ)
    (hspan : ∀ d, 0 < d → ∀ x ∈ F.layer d, φ x ∈ weightedLieDegreeLengthSpan v w d 1)
    {x : L} (hx : x ∈ F.rankLayer s k) :
    φ x ∈ weightedLieDegreeLengthSpan v w s k := by
  rw [NilpotentLieFiltration.rankLayer, F.terminal, bot_sup_eq] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hkl, a, rfl⟩ := hx
    exact weightedLieDegreeLengthSpan_antitone v w le_rfl hkl
      (a.map_eval_mem_degreeLengthSpan φ v w hspan)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem FreeWeightedNilpotentLieAlgebra.lift_layer_mem_degreeLengthSpan {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : X → ℕ) (hw : ∀ i, 0 < w i)
    (f : X → L) (hf : ∀ i, f i ∈ F.layer (w i))
    {d : ℕ} {x : FreeWeightedNilpotentLieAlgebra X s w}
    (hx : x ∈ (filtration X s w hw).layer d) :
    lift F w f hf x ∈ weightedLieDegreeLengthSpan f w d 1 := by
  obtain ⟨a, ha, rfl⟩ := hx
  change FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot a ∈
    weightedLieDegreeLengthSpan f w d 1
  have h := weightedLieUpperSpan_map_le_degreeLengthSpan
    (FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot)
    (FreeNilpotentLieAlgebra.of X s) w d ⟨a, ha, rfl⟩
  change FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot a ∈
    weightedLieDegreeLengthSpan
      (fun i => FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot
        (FreeNilpotentLieAlgebra.of X s i)) w d 1 at h
  have heq : (fun i => FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot
      (FreeNilpotentLieAlgebra.of X s i)) = f :=
    funext (fun i => FreeNilpotentLieAlgebra.lift_of f F.lowerCentralSeries_eq_bot i)
  rw [heq] at h
  exact h

theorem FreeDegreeRankLieAlgebra.lift_top_mem_degreeLengthSpan {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ i, 0 < w i)
    (f : X → L) (hf : ∀ i, f i ∈ F.layer (w i) 0)
    {x : FreeDegreeRankLieAlgebra X s r w hw}
    (hx : x ∈ (filtration X s r w hw F.rank_le_degree).layer s r) :
    lift F w hw f hf x ∈ weightedLieDegreeLengthSpan f w s r := by
  obtain ⟨a, ha, rfl⟩ := hx
  change FreeWeightedNilpotentLieAlgebra.lift F.associatedDegree w f hf a ∈
    weightedLieDegreeLengthSpan f w s r
  exact (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).top_rank_map_mem_degreeLengthSpan
    (FreeWeightedNilpotentLieAlgebra.lift F.associatedDegree w f hf) f w
    (fun _ _ _ h => FreeWeightedNilpotentLieAlgebra.lift_layer_mem_degreeLengthSpan
      F.associatedDegree w hw f hf h) ha

theorem FreeDegreeRankLieAlgebra.lift_top_frequency_zero
    {A : Type*} [AddCommGroup A] [Module ℚ A] {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ i, 0 < w i)
    (f : X → L) (hf : ∀ i, f i ∈ F.layer (w i) 0) (η : L →ₗ[ℚ] A)
    (hzero : ∀ a : FreeMagma X, lieTreeWeight w a = s → a.length = r → η (lieTreeEval f a) = 0)
    {x : FreeDegreeRankLieAlgebra X s r w hw}
    (hx : x ∈ (filtration X s r w hw F.rank_le_degree).layer s r) :
    η (lift F w hw f hf x) = 0 := by
  exact weightedLieDegreeLengthSpan_top_le_ker F f w
    (fun i => by rw [← F.rank_zero_eq_one]; exact hf i) η hzero
    (lift_top_mem_degreeLengthSpan F w hw f hf hx)

end Erdos3

end

section

namespace Erdos3

def markedGradeRegion (d k l : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {α | d ≤ α 0 ∧ k ≤ α 1 ∧ l ≤ α 2}

theorem markedGradeRegion_inter (d k l e m n : ℕ) :
    markedGradeRegion (max d e) (max k m) (max l n) =
      markedGradeRegion d k l ∩ markedGradeRegion e m n := by
  ext α
  simp only [markedGradeRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, max_le_iff]
  tauto

namespace FreeDegreeRankLieAlgebra

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (marked : X → Bool)

theorem markedLayer_eq_homogeneousSpan (d k l : ℕ) :
    markedLayer X s r w hw marked d k l =
      homogeneousLieSpan (of X s r w hw) (markedGeneratorGrade w marked) (markedGradeRegion d k l) := by
  unfold markedLayer markedLieSpan homogeneousLieSpan
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, markedGradeRegion, markedTreeGrade_weight,
    markedTreeGrade_count, markedTreeGrade_length, and_assoc]

theorem markedLayer_inf (hr : r ≤ s) (d k l e m n : ℕ) :
    markedLayer X s r w hw marked d k l ⊓ markedLayer X s r w hw marked e m n =
      markedLayer X s r w hw marked (max d e) (max k m) (max l n) := by
  rw [markedLayer_eq_homogeneousSpan, markedLayer_eq_homogeneousSpan,
    markedLayer_eq_homogeneousSpan, markedGradeRegion_inter,
    homogeneousSpan_inter X s r w hw hr]

theorem markedLayer_separate_inter (hr : r ≤ s) (d k l : ℕ) :
    markedLayer X s r w hw marked d 0 l ⊓ markedLayer X s r w hw marked 0 k 0 =
      markedLayer X s r w hw marked d k l := by
  rw [markedLayer_inf X s r w hw marked hr]
  simp only [Nat.max_zero, Nat.zero_max]

theorem topLayer_eq_markedLayer (hr : r ≤ s) :
    (filtration X s r w hw hr).layer s r = markedLayer X s r w hw marked s 0 r := by
  apply le_antisymm
  · intro x hx
    change x ∈ markedLieSpan (of X s r w hw) w marked s 0 r
    rw [markedLieSpan_zero_marked]
    let F := filtration X s r w hw hr
    have hf (i : X) : of X s r w hw i ∈ F.layer (w i) 0 := by
      rw [F.rank_zero_eq_one]
      exact of_mem_layer X s r w hw hr i
    have hid : lift F w hw (of X s r w hw) hf =
        (LieHom.id : FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆ FreeDegreeRankLieAlgebra X s r w hw) := by
      apply hom_ext w hw
      intro i
      rw [lift_of]
      rfl
    have h := lift_top_mem_degreeLengthSpan F w hw (of X s r w hw) hf hx
    simpa only [hid, LieHom.id_apply] using h
  · exact markedLayer_le_degreeRank X s r w hw marked hr s 0 r

theorem topLayer_inter_markedIdeal (hr : r ≤ s) (k : ℕ) :
    (filtration X s r w hw hr).layer s r ⊓ (markedLayerIdeal X s r w hw marked 0 k 0).toSubmodule =
      markedLayer X s r w hw marked s k r := by
  change (filtration X s r w hw hr).layer s r ⊓ markedLayer X s r w hw marked 0 k 0 = _
  rw [topLayer_eq_markedLayer X s r w hw marked hr,
    markedLayer_separate_inter X s r w hw marked hr]

end FreeDegreeRankLieAlgebra
end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} 

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NormalizedTwistLocalizedFourierSelection
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem torus_integer_character_real_phase {J : Type*} [Fintype J]
    (a : J → ℤ) (x : J → ℝ) :
    (∏ j, CircleFourier.character (a j • (x j : UnitAddCircle))) =
      (Real.fourierChar (∑ j, (a j : ℝ) * x j) : ℂ) := by
  rw [← CircleFourier.character_fintype_sum]
  have he : (∑ j, a j • (x j : UnitAddCircle)) =
      ((∑ j, (a j : ℝ) * x j : ℝ) : UnitAddCircle) := by
    simp only [← AddCircle.coe_zsmul, zsmul_eq_mul]
    exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (fun j => (a j : ℝ) * x j) Finset.univ).symm
  rw [he, CircleFourier.character_coe_exp, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

namespace VectorPolynomial

open _root_.MvPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def normalizedTwistFrequencyPolynomial (cover : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    MvPolynomial X ℝ :=
  C (1 / (cover : ℝ)) * ∑ j, integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j)

theorem normalizedTwistFrequencyPolynomial_eval (cover : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℝ) :
    MvPolynomial.eval u (normalizedTwistFrequencyPolynomial cover a poly) =
      ∑ i : Σ j, J j, (a i : ℝ) * (eval u (poly i.1) i.2 / cover) := by
  simp only [normalizedTwistFrequencyPolynomial, map_mul, eval_C, map_sum,
    integerRowPolynomial_eval, Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem physicalGrid_character_eq_polynomial_phase (cover : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℝ) :
    (∏ i, CircleFourier.character (a i • physicalGridFactorInput cover poly u i)) =
      (Real.fourierChar (MvPolynomial.eval u
        (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) := by
  rw [normalizedTwistFrequencyPolynomial_eval]
  exact torus_integer_character_real_phase a _

namespace NormalizedPolynomialTwist

variable [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem exists_frozen_ambient_fourier
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ)
    {δ p : ℝ} (hδ : 0 < δ) (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hL : (L : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → (Σ j, J j) → ℤ) (coeff : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ a j, |(frequency a j : ℝ)| ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      (∑ a, ‖coeff a‖) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℝ),
        ‖W.frozenTorus residue center (physicalGridFactorInput W.cover poly u) -
          ∑ a, coeff a * (Real.fourierChar (MvPolynomial.eval u
            (normalizedTwistFrequencyPolynomial W.cover (frequency a) poly)) : ℂ)‖ ≤ δ := by
  obtain ⟨F, inst, freq, coeff, hcard, hfreq, hmass, herr⟩ :=
    exists_ambient_torus_fourier_approximation (W.frozenTorus residue center) L 1
      (W.frozenTorus_lipschitz residue center) (W.norm_frozenTorus_le residue center)
      hδ hp hdim hL hδp
  let := inst
  refine ⟨F, inst, freq, coeff, hcard, hfreq, ?_, ?_⟩
  · simpa only [NNReal.coe_one, mul_one] using hmass
  · intro poly u
    simpa only [physicalGrid_character_eq_polynomial_phase] using
      herr (physicalGridFactorInput W.cover poly u)

end NormalizedPolynomialTwist
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped BigOperators NNReal

variable {X Ω : Type*} [Fintype X] [Fintype Ω]
  {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
  {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem norm_correlation_star_eq_product (μ : FiniteProbabilityWeights Ω)
    (signal test : Ω → ℂ) :
    ‖μ.correlation (fun x => star (signal x)) test‖ =
      ‖μ.complexMean (fun x => signal x * test x)‖ := by
  have he : μ.correlation (fun x => star (signal x)) test =
      star (μ.complexMean (fun x => signal x * test x)) := by
    unfold FiniteProbabilityWeights.correlation FiniteProbabilityWeights.complexMean
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [he, norm_star]

theorem exists_correlating_frequency
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (μ : FiniteProbabilityWeights Ω) (u : Ω → X → ℤ)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (signal : Ω → ℂ) (residue : X → ZMod W.modulus) (center : X → ℝ)
    (radius ε δ p : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hL : (L : ℝ) ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p)
    (hcell : ∀ x, 0 < μ.weight x →
      (fun i => (u x i : ZMod W.modulus)) = residue ∧
        dist (fun i => (u x i : ℝ) / N i) center ≤ radius)
    (hsignal : ∀ x, 0 < μ.weight x → ‖signal x‖ ≤ 1)
    (herror : (L : ℝ) * radius + ε ≤ δ / 2)
    (hcorr : δ ≤ ‖μ.correlation signal (fun x => W.eval N poly (u x))‖) :
    ∃ a : (Σ j, J j) → ℤ,
      (∀ j, |(a j : ℝ)| ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      δ / (2 * Real.exp (2 * p * (2 * p + 2) ^ 4)) ≤
        ‖μ.correlation signal (fun x =>
          (Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ))‖ := by
  classical
  obtain ⟨F, inst, freq, coeff, _hcard, hfreq, hmass, herr⟩ :=
    W.exists_frozen_ambient_fourier residue center hε hp hdim hL hεp
  let := inst
  let atom : F → Ω → ℂ := fun a x =>
    Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
      (normalizedTwistFrequencyPolynomial W.cover (freq a) poly))
  let approx : Ω → ℂ := fun x => ∑ a, coeff a * atom a x
  have happrox (x : Ω) (hx : μ.weight x ≠ 0) :
      ‖W.eval N poly (u x) - approx x‖ ≤ (L : ℝ) * radius + ε := by
    have hxpos := lt_of_le_of_ne (μ.nonneg x) (Ne.symm hx)
    obtain ⟨hres, hdist⟩ := hcell x hxpos
    have hfreeze : W.frozenSpatialEval center poly (u x) =
        W.frozenTorus residue center
          (physicalGridFactorInput W.cover poly (fun i => (u x i : ℝ))) := by
      simp only [frozenSpatialEval, hres]
    have he := herr poly (fun i => (u x i : ℝ))
    calc
      _ ≤ ‖W.eval N poly (u x) - W.frozenSpatialEval center poly (u x)‖ +
          ‖W.frozenSpatialEval center poly (u x) - approx x‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (L : ℝ) * radius + ε := add_le_add
        ((W.eval_sub_frozenSpatialEval N center poly (u x)).trans
          (mul_le_mul_of_nonneg_left hdist L.coe_nonneg))
        (by rw [hfreeze]; exact he)
  have hmean : ‖μ.correlation signal (fun x => W.eval N poly (u x)) -
      μ.correlation signal approx‖ ≤ (L : ℝ) * radius + ε := by
    rw [μ.correlation_eq_complexMean, μ.correlation_eq_complexMean]
    apply (μ.norm_complexMean_sub_le _ _ (fun _ => (L : ℝ) * radius + ε) ?_).trans_eq
      (μ.mean_const _)
    intro x hx
    rw [← mul_sub, ← star_sub, norm_mul, norm_star]
    calc
      _ ≤ 1 * ‖W.eval N poly (u x) - approx x‖ :=
        mul_le_mul_of_nonneg_right
          (hsignal x (lt_of_le_of_ne (μ.nonneg x) (Ne.symm hx))) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact happrox x hx
  have hexpand : μ.correlation signal approx =
      ∑ a, star (coeff a) * μ.correlation signal (atom a) := by
    simp only [FiniteProbabilityWeights.correlation_eq_complexMean, approx, star_sum, star_mul]
    simpa only [mul_comm] using μ.complexMean_weighted_expansion signal
      (fun a => star (coeff a)) (fun a x => star (atom a x))
  have hlarge : δ / 2 ≤ ‖∑ a, star (coeff a) * μ.correlation signal (atom a)‖ := by
    have htriangle := norm_le_norm_add_norm_sub (μ.correlation signal approx)
      (μ.correlation signal (fun x => W.eval N poly (u x)))
    rw [norm_sub_rev] at htriangle
    rw [← hexpand]
    linarith
  obtain ⟨a, ha⟩ := exists_large_weighted_term (fun a => star (coeff a))
    (fun a => μ.correlation signal (atom a)) (by positivity : 0 < δ / 2)
    (Real.exp_pos _) (by simpa only [norm_star] using hmass) hlarge
  refine ⟨freq a, hfreq a, ?_⟩
  simpa only [div_div, atom] using ha

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem integerRowPolynomial_constant_of_annihilates {I K : Type*} [Fintype K]
    (W : Submodule ℝ (K → ℝ)) (a : K → ℤ) (p : VectorPolynomial I ℝ (K → ℝ))
    (hp : ∀ α, α ≠ 0 → coefficients p α ∈ W)
    (ha : W ≤ LinearMap.ker (integerRowLinear a)) :
    integerRowPolynomial a p = C ((integerRowPolynomial a p).coeff 0) := by
  classical
  ext α
  by_cases hα : α = 0
  · subst α
    simp
  · have hz : integerRowLinear a (coefficients p α) = 0 := ha (hp α hα)
    rw [integerRowPolynomial_coeff, ← integerRowLinear_apply, hz, coeff_C]
    simp only [Ne.symm hα, ite_false]

noncomputable def taggedScalarLowPolynomial (d : ℕ) (F : Fin m → MvPolynomial X ℝ) :
    MvPolynomial X ℝ := ∑ j, if j.val + 1 ≤ d then F j else 0

noncomputable def taggedScalarHighConstant (d : ℕ) (F : Fin m → MvPolynomial X ℝ) : ℝ :=
  ∑ j, if d < j.val + 1 then (F j).coeff 0 else 0

theorem taggedScalar_sum_eq_low_add_constant (d : ℕ) (F : Fin m → MvPolynomial X ℝ)
    (hhigh : ∀ j, d < j.val + 1 → F j = C ((F j).coeff 0)) :
    (∑ j, F j) = taggedScalarLowPolynomial d F + C (taggedScalarHighConstant d F) := by
  classical
  unfold taggedScalarLowPolynomial taggedScalarHighConstant
  rw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val + 1 ≤ d
  · simp only [hj, Nat.not_lt.mpr hj, ite_true, ite_false, map_zero, add_zero]
  · have hj' : d < j.val + 1 := Nat.lt_of_not_ge hj
    simp only [hj, hj', ite_false, ite_true, zero_add]
    exact hhigh j hj'

theorem taggedScalarLowPolynomial_degree (d : ℕ) (F : Fin m → MvPolynomial X ℝ)
    (hdegree : ∀ j, (F j).totalDegree ≤ j.val + 1) :
    (taggedScalarLowPolynomial d F).totalDegree ≤ d := by
  classical
  apply totalDegree_finsetSum_le
  intro j _
  split_ifs with hj
  · exact (hdegree j).trans hj
  · simp only [totalDegree_zero, Nat.zero_le]

theorem taggedScalar_sum_degree (h : Fin m) (F : Fin m → MvPolynomial X ℝ)
    (hdegree : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (hhigh : ∀ j, h < j → F j = C ((F j).coeff 0)) :
    (∑ j, F j).totalDegree ≤ h.val + 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  by_cases hj : j ≤ h
  · exact (hdegree j).trans (Nat.add_le_add_right hj 1)
  · rw [hhigh j (lt_of_not_ge hj), totalDegree_C]
    omega

theorem taggedScalar_sum_top (h : Fin m) (F : Fin m → MvPolynomial X ℝ)
    (hdegree : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (hhigh : ∀ j, h < j → F j = C ((F j).coeff 0)) :
    homogeneousComponent (h.val + 1) (∑ j, F j) =
      homogeneousComponent (h.val + 1) (F h) := by
  classical
  rw [map_sum]
  apply Finset.sum_eq_single h
  · intro j _ hj
    apply homogeneousComponent_eq_zero
    by_cases hjh : j < h
    · exact (hdegree j).trans_lt (Nat.add_lt_add_right hjh 1)
    · have hlt : h < j := lt_of_le_of_ne (le_of_not_gt hjh) (Ne.symm hj)
      rw [hhigh j hlt, totalDegree_C]
      omega
  · simp

theorem highest_nonannihilating_tag (d : ℕ)
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (a : (Σ j, J j) → ℤ) :
    (∀ j : Fin m, d < j.val + 1 →
      W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))) ∨
    ∃ h : Fin m, d < h.val + 1 ∧
      (∃ w ∈ W h, integerRowLinear (fun i => a ⟨h, i⟩) w ≠ 0) ∧
      ∀ j : Fin m, h < j → W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)) := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter (fun j => d < j.val + 1 ∧
    ¬ W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)))
  by_cases hs : S.Nonempty
  · let h := S.max' hs
    have hh : h ∈ S := Finset.max'_mem S hs
    have hh' := (Finset.mem_filter.mp hh).2
    refine Or.inr ⟨h, hh'.1, ?_, ?_⟩
    · by_contra! hn
      apply hh'.2
      intro w hw
      exact hn w hw
    · intro j hj
      by_contra hn
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨hh'.1.trans (Nat.add_lt_add_right hj 1), hn⟩⟩
      exact (not_le_of_gt hj) (Finset.le_max' S j hjS)
  · refine Or.inl ?_
    intro j hj
    by_contra hn
    exact hs ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hn⟩⟩

def truncateTaggedFrequency (d : ℕ) (a : (Σ j, J j) → ℤ) : (Σ j, J j) → ℤ :=
  fun i => if i.1.val + 1 ≤ d then a i else 0

theorem integerRowPolynomial_truncateTaggedFrequency (d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (j : Fin m) :
    integerRowPolynomial (fun i => truncateTaggedFrequency d a ⟨j, i⟩) (poly j) =
      if j.val + 1 ≤ d then integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j) else 0 := by
  classical
  by_cases hj : j.val + 1 ≤ d
  · simp only [truncateTaggedFrequency, hj, ite_true]
  · simp only [truncateTaggedFrequency, hj, ite_false]
    ext α
    simp only [integerRowPolynomial_coeff, Int.cast_zero, zero_mul,
      Finset.sum_const_zero, MvPolynomial.coeff_zero]

theorem normalizedTwistFrequencyPolynomial_truncate (cover d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly =
      C (1 / (cover : ℝ)) * taggedScalarLowPolynomial d
        (fun j => integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j)) := by
  simp only [normalizedTwistFrequencyPolynomial, integerRowPolynomial_truncateTaggedFrequency,
    taggedScalarLowPolynomial]

noncomputable def normalizedTwistHighFrequencyConstant (cover d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) : ℝ :=
  (1 / (cover : ℝ)) * taggedScalarHighConstant d
    (fun j => integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j))

theorem normalizedTwistFrequencyPolynomial_low_degree (cover d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) :
    (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly).totalDegree ≤ d := by
  rw [normalizedTwistFrequencyPolynomial_truncate]
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  exact taggedScalarLowPolynomial_degree d _
    (fun j => integerRowPolynomial_totalDegree_le _ (hpoly j))

theorem normalizedTwistFrequencyPolynomial_low_add_constant (cover d : ℕ)
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (hann : ∀ j, d < j.val + 1 →
      W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))) :
    normalizedTwistFrequencyPolynomial cover a poly =
      normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly +
        C (normalizedTwistHighFrequencyConstant cover d a poly) := by
  rw [normalizedTwistFrequencyPolynomial_truncate]
  unfold normalizedTwistFrequencyPolynomial normalizedTwistHighFrequencyConstant
  rw [taggedScalar_sum_eq_low_add_constant d _ (fun j hj =>
    integerRowPolynomial_constant_of_annihilates (W j) _ _ (hcoeff j) (hann j hj)),
    mul_add, ← map_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped NNReal

theorem exists_correlating_frequency_early :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X Ω : Type*} [Fintype X] [Fintype Ω]
      {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      (μ : FiniteProbabilityWeights Ω) (u : Ω → X → ℤ)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (signal : Ω → ℂ) (residue : X → ZMod W.modulus) (center : X → ℝ)
      (p : ℝ), 0 ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (L : ℝ) ≤ Real.exp p →
      (∀ x, 0 < μ.weight x →
        (fun i => (u x i : ZMod W.modulus)) = residue ∧
          dist (fun i => (u x i : ℝ) / N i) center ≤ Real.exp (-2 * p) / 4) →
      (∀ x, 0 < μ.weight x → ‖signal x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖μ.correlation signal (fun x => W.eval N poly (u x))‖ →
      ∃ a : (Σ j, J j) → ℤ,
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖μ.correlation signal (fun x =>
          (Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ))‖ := by
  let Q : Polynomial ℕ := Polynomial.X + 4 +
    (2 * (Polynomial.X + 4) + 1) * (2 * (Polynomial.X + 4) + 2) ^ 4
  obtain ⟨C, hC, hQ⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro X Ω _ _ m J _ periodCap coverCap L W μ u N poly signal residue center p hp hdim hL
    hcell hsignal hcorr
  let q := p + 4
  let A := 2 * q * (2 * q + 2) ^ 4
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hε : 0 < Real.exp (-p) / 4 := by positivity
  have hεp : (Real.exp (-p) / 4)⁻¹ ≤ Real.exp q := by
    rw [inv_div, Real.exp_neg, div_inv_eq_mul]
    change 4 * Real.exp p ≤ Real.exp (p + 4)
    rw [Real.exp_add]
    nlinarith [Real.exp_pos p]
  have herr : (L : ℝ) * (Real.exp (-2 * p) / 4) + Real.exp (-p) / 4 ≤
      Real.exp (-p) / 2 := by
    calc
      _ ≤ Real.exp p * (Real.exp (-2 * p) / 4) + Real.exp (-p) / 4 := by
        gcongr
      _ = _ := by
        have he : Real.exp p * Real.exp (-2 * p) = Real.exp (-p) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [← mul_div_assoc, he]
        ring
  obtain ⟨a, ha, hscore⟩ := W.exists_correlating_frequency μ u N poly signal residue center
    (Real.exp (-2 * p) / 4) (Real.exp (-p) / 4) (Real.exp (-p)) q hε (Real.exp_pos _)
    hq (hdim.trans hpq) (hL.trans (Real.exp_le_exp.mpr hpq)) hεp hcell hsignal herr hcorr
  have hbudget : p + 4 + (2 * q + 1) * (2 * q + 2) ^ 4 ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hQ p hp
  have hfreq : (2 * q + 2) ^ 4 ≤ (p + C) ^ C := by
    apply le_trans _ hbudget
    nlinarith [pow_nonneg (show 0 ≤ 2 * q + 2 by linarith) 4]
  have hcost : p + A + 4 ≤ (p + C) ^ C := by
    dsimp [A]
    nlinarith [pow_nonneg (show 0 ≤ 2 * q + 2 by linarith) 4]
  refine ⟨a, fun j => (ha j).trans (Real.exp_le_exp.mpr hfreq), ?_⟩
  apply le_trans (Real.exp_le_exp.mpr (neg_le_neg hcost))
  apply le_trans ?_ hscore
  change Real.exp (-(p + A + 4)) ≤ Real.exp (-p) / (2 * Real.exp A)
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.exp A)).mpr
  have he : Real.exp (-(p + A + 4)) * (2 * Real.exp A) =
      2 * Real.exp (-p) / Real.exp 4 := by
    rw [mul_comm (2 : ℝ), ← mul_assoc, ← Real.exp_add]
    have hx : -(p + A + 4) + A = -p - 4 := by ring
    rw [hx, Real.exp_sub]
    ring
  rw [he]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  nlinarith [Real.exp_pos (-p)]

theorem exists_correlating_frequency_product_early :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X Ω : Type*} [Fintype X] [Fintype Ω]
      {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      (μ : FiniteProbabilityWeights Ω) (u : Ω → X → ℤ)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (signal : Ω → ℂ) (residue : X → ZMod W.modulus) (center : X → ℝ)
      (p : ℝ), 0 ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (L : ℝ) ≤ Real.exp p →
      (∀ x, 0 < μ.weight x →
        (fun i => (u x i : ZMod W.modulus)) = residue ∧
          dist (fun i => (u x i : ℝ) / N i) center ≤ Real.exp (-2 * p) / 4) →
      (∀ x, 0 < μ.weight x → ‖signal x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖μ.complexMean (fun x => W.eval N poly (u x) * signal x)‖ →
      ∃ a : (Σ j, J j) → ℤ,
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖μ.complexMean (fun x =>
          (Real.fourierChar (MvPolynomial.eval (fun i => (u x i : ℝ))
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) * signal x)‖ := by
  obtain ⟨C, hC, h⟩ := exists_correlating_frequency_early
  refine ⟨C, hC, ?_⟩
  intro X Ω _ _ m J _ periodCap coverCap L W μ u N poly signal residue center p hp hdim hL
    hcell hsignal hcorr
  obtain ⟨a, ha, hc⟩ := h W μ u N poly (fun x => star (signal x)) residue center p hp
    hdim hL hcell (fun x hx => by simpa only [norm_star] using hsignal x hx) (by
      rw [norm_correlation_star_eq_product]
      simpa only [mul_comm] using hcorr)
  refine ⟨a, ha, ?_⟩
  rw [norm_correlation_star_eq_product] at hc
  simpa only [mul_comm] using hc

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3

namespace VectorPolynomial

open _root_.MvPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem normalizedTwistFrequencyPolynomial_top_not_approximation
    (cover : ℕ) (hcover : 0 < cover) (h : Fin m)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (W : Submodule ℝ (J h → ℝ)) (T : X → ℝ) (R S : ℝ)
    (hT : ∀ i, 0 < T i) (hcost : (cover : ℝ) * S ≤ R)
    (hrank : HasLayerSamplingRank (h.val + 1) T R W (poly h))
    (ha : ∀ i, |(a ⟨h, i⟩ : ℝ)| ≤ R)
    (hw : ∃ w ∈ W, integerRowLinear (fun i => a ⟨h, i⟩) w ≠ 0)
    (htop : homogeneousComponent (h.val + 1)
        (normalizedTwistFrequencyPolynomial cover a poly) =
      C (1 / (cover : ℝ)) * homogeneousComponent (h.val + 1)
        (integerRowPolynomial (fun i => a ⟨h, i⟩) (poly h))) :
    ¬ PolynomialRationalApproximation T S (homogeneousComponent (h.val + 1)
      (normalizedTwistFrequencyPolynomial cover a poly)) := by
  intro happ
  obtain ⟨w, hw, hwa⟩ := hw
  have hwan : ∑ i, (a ⟨h, i⟩ : ℝ) * w i ≠ 0 := by
    simpa only [integerRowLinear_apply] using hwa
  apply hrank (fun i => a ⟨h, i⟩) ha ⟨⟨w, hw⟩, hwan⟩
  have hscaled := (happ.nat_smul cover hcover).mono hcost hT
  rw [htop] at hscaled
  have hcancel (P : MvPolynomial X ℝ) :
      (cover : ℝ) • (C (1 / (cover : ℝ)) * P) = P := by
    rw [smul_eq_C_mul, ← mul_assoc, ← map_mul]
    rw [mul_one_div_cancel (Nat.cast_ne_zero.mpr hcover.ne'), map_one, one_mul]
  rwa [hcancel] at hscaled

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped NNReal BigOperators

theorem exists_localized_correlating_frequency :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
      {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (signal : (X → ℤ) → ℂ) (p : ℝ),
      0 ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (L : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp (3 * p + 16) ≤ (N i : ℝ)) →
      (∀ u ∈ integerBox N, ‖signal u‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N, W.eval N poly u * signal u‖ →
      ∃ (start length : X → ℕ) (a : (Σ j, J j) → ℤ),
        (∀ i, 0 < length i) ∧
        (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
        (∀ i, (N i : ℝ) ≤ Real.exp (3 * p + 16) * W.modulus * length i) ∧
        (∀ v ∈ integerBox length,
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) ∈ integerBox N) ∧
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 v ∈ integerBox length,
          (Real.fourierChar (MvPolynomial.eval
            (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
          signal (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)‖ := by
  obtain ⟨C, hC, hfourier⟩ := exists_correlating_frequency_product_early
  refine ⟨C, hC, ?_⟩
  intro X _ _ m J _ periodCap coverCap L W N poly signal p hp hdim hmod hL hN hsignal hcorr
  obtain ⟨start, length, hpos, hlength, hcomparison, hinside, _, hspatial, _, hselected⟩ :=
    exists_correlated_integer_residue_box N W.modulus p hp W.modulus_pos hmod hN
      (fun u => W.eval N poly u * signal u)
  have hnonempty : (integerBox length).Nonempty := by
    refine ⟨0, (mem_integerBox length 0).mpr ?_⟩
    intro i
    simp only [Pi.zero_apply]
    exact ⟨le_rfl, by exact_mod_cast hpos i⟩
  let μ := FiniteProbabilityWeights.uniformFinset (integerBox length) hnonempty
  let u : ↥(integerBox length) → X → ℤ :=
    fun v i => (start i : ℤ) + (W.modulus : ℤ) * v.val i
  have hcell (v : ↥(integerBox length)) (_ : 0 < μ.weight v) :
      (fun i => (u v i : ZMod W.modulus)) = (fun i => (start i : ZMod W.modulus)) ∧
        dist (fun i => (u v i : ℝ) / N i) (fun i => (start i : ℝ) / N i) ≤
          Real.exp (-2 * p) / 4 := by
    constructor
    · funext i
      simp [u]
    · apply (dist_pi_le_iff (by positivity)).mpr
      intro i
      simpa only [u, Real.dist_eq, Int.cast_add, Int.cast_mul, Int.cast_natCast,
        neg_mul] using hspatial v.val v.property i
  have hselected' : Real.exp (-p) ≤ ‖μ.complexMean
      (fun v => W.eval N poly (u v) * signal (u v))‖ := by
    dsimp only [μ, u]
    rw [FiniteProbabilityWeights.uniformFinset_complexMean _ _
      (fun v : X → ℤ => W.eval N poly (fun i => (start i : ℤ) + W.modulus * v i) *
        signal (fun i => (start i : ℤ) + W.modulus * v i))]
    exact hcorr.trans hselected
  obtain ⟨a, ha, hc⟩ := hfourier W μ u N poly (fun v => signal (u v))
    (fun i => (start i : ZMod W.modulus)) (fun i => (start i : ℝ) / N i) p hp hdim hL
    hcell (fun v _ => hsignal _ (hinside v.val v.property)) hselected'
  refine ⟨start, length, a, hpos, hlength, hcomparison, hinside, ha, ?_⟩
  dsimp only [μ, u] at hc
  rw [FiniteProbabilityWeights.uniformFinset_complexMean _ _
    (fun v : X → ℤ => (Real.fourierChar (MvPolynomial.eval
      (fun i => (((start i : ℤ) + W.modulus * v i : ℤ) : ℝ))
      (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
      signal (fun i => (start i : ℤ) + W.modulus * v i))] at hc
  simpa only [u, Int.cast_add, Int.cast_mul, Int.cast_natCast] using hc

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowTaggedPolynomialCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

abbrev LowTaggedIndex (d : ℕ) := {i : Σ j, J j // i.1.val + 1 ≤ d}

noncomputable def lowTaggedIndex (d : ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    Σ j, J j := ((Fintype.equivFin (LowTaggedIndex J d)).symm i).val

theorem lowTaggedIndex_property (d : ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    (lowTaggedIndex J d i).1.val + 1 ≤ d :=
  ((Fintype.equivFin (LowTaggedIndex J d)).symm i).property

noncomputable def lowTaggedWeight (d : ℕ) : Fin (Fintype.card (LowTaggedIndex J d)) → ℕ :=
  fun i => (lowTaggedIndex J d i).1.val + 1

theorem lowTaggedWeight_pos (d : ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    0 < lowTaggedWeight J d i := Nat.succ_pos _

theorem lowTaggedWeight_le (d : ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    lowTaggedWeight J d i ≤ d := lowTaggedIndex_property J d i

theorem lowTaggedIndex_card_le (d : ℕ) :
    Fintype.card (LowTaggedIndex J d) ≤ Fintype.card (Σ j, J j) :=
  Fintype.card_le_of_injective Subtype.val Subtype.val_injective

theorem lowTagged_sum (d : ℕ) {V : Type*} [AddCommMonoid V] (f : (Σ j, J j) → V) :
    (∑ i : Σ j, J j, if i.1.val + 1 ≤ d then f i else 0) =
      ∑ i : Fin (Fintype.card (LowTaggedIndex J d)), f (lowTaggedIndex J d i) := by
  classical
  calc
    _ = ∑ i : LowTaggedIndex J d, f i.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) f
    _ = _ := Fintype.sum_equiv (Fintype.equivFin (LowTaggedIndex J d)) _ _
      (fun i => by simp only [lowTaggedIndex, Equiv.symm_apply_apply])

variable {X : Type*}

noncomputable def lowTaggedPolynomial (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (i : Fin (Fintype.card (LowTaggedIndex J d))) : MvPolynomial X ℝ :=
  coordinate (LinearMap.proj (lowTaggedIndex J d i).2 :
    (J (lowTaggedIndex J d i).1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom
    (poly (lowTaggedIndex J d i).1)

theorem lowTaggedPolynomial_coeff (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (i : Fin (Fintype.card (LowTaggedIndex J d))) (α : X →₀ ℕ) :
    (lowTaggedPolynomial J d poly i).coeff α =
      coefficients (poly (lowTaggedIndex J d i).1) α (lowTaggedIndex J d i).2 := by
  rw [lowTaggedPolynomial, coeff_coordinate]
  rfl

theorem lowTaggedPolynomial_eval (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (i : Fin (Fintype.card (LowTaggedIndex J d))) (u : X → ℝ) :
    MvPolynomial.eval u (lowTaggedPolynomial J d poly i) =
      eval u (poly (lowTaggedIndex J d i).1) (lowTaggedIndex J d i).2 := by
  rw [lowTaggedPolynomial, ← coordinate_eval₂]
  have he : eval₂ u (poly (lowTaggedIndex J d i).1) =
      eval u (poly (lowTaggedIndex J d i).1) := by
    simpa using (eval₂_algebraMap (S := ℝ) u (poly (lowTaggedIndex J d i).1))
  rw [he]
  rfl

theorem lowTaggedPolynomial_degree (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    (lowTaggedPolynomial J d poly i).totalDegree ≤ lowTaggedWeight J d i := by
  have hw : (lowTaggedPolynomial J d poly i).weightedTotalDegree (1 : X → ℕ) ≤
      lowTaggedWeight J d i := by
    apply (scalar_weightedDegree_le_iff _ _ _).mpr
    intro α hα
    rw [lowTaggedPolynomial_coeff, hpoly _ α hα]
    rfl
  simpa only [MvPolynomial.weightedTotalDegree_one] using hw

noncomputable def lowTaggedFrequency (d : ℕ) (a : (Σ j, J j) → ℤ) :
    Fin (Fintype.card (LowTaggedIndex J d)) → ℤ :=
  fun i => a (lowTaggedIndex J d i)

theorem lowTaggedFrequency_bound (d : ℕ) (a : (Σ j, J j) → ℤ) (B : ℝ)
    (ha : ∀ i, |(a i : ℝ)| ≤ B) :
    ∀ i, |(lowTaggedFrequency J d a i : ℝ)| ≤ B := fun i => ha (lowTaggedIndex J d i)

theorem normalizedTwistFrequencyPolynomial_low_eval (cover d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (u : X → ℝ) :
    MvPolynomial.eval u
        (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly) =
      (∑ i : Fin (Fintype.card (LowTaggedIndex J d)),
        (lowTaggedFrequency J d a i : ℝ) *
          MvPolynomial.eval u (lowTaggedPolynomial J d poly i)) / (cover : ℝ) := by
  classical
  rw [normalizedTwistFrequencyPolynomial_eval]
  calc
    _ = (∑ i : Σ j, J j, if i.1.val + 1 ≤ d then
        (a i : ℝ) * eval u (poly i.1) i.2 else 0) / (cover : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.1.val + 1 ≤ d <;>
        simp only [truncateTaggedFrequency, hi, ite_true, ite_false,
          Int.cast_zero, zero_mul, zero_div, mul_div_assoc]
    _ = _ := by
      rw [lowTagged_sum]
      simp only [lowTaggedFrequency, lowTaggedPolynomial_eval]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowTaggedRationalLiftRewrite
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

theorem normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist
    (M d : ℕ) (hM : 0 < M) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℝ)
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (β : Fin (Fintype.card (LowTaggedIndex J d)) → ℤ) :
    (Real.fourierChar (MvPolynomial.eval u
      (normalizedTwistFrequencyPolynomial M (truncateTaggedFrequency d a) poly)) : ℂ) =
      rationalLiftCharacterTwist M (lowTaggedFrequency J d a) c
        (fun i => MvPolynomial.eval u (lowTaggedPolynomial J d poly i) - c i - (β i : ℝ))
        (fun i => (β i : ZMod M)) := by
  rw [normalizedTwistFrequencyPolynomial_low_eval J]
  symm
  simpa only [sub_add_cancel] using
    rationalLiftCharacterTwist_residual M hM (lowTaggedFrequency J d a) c
      (fun i => MvPolynomial.eval u (lowTaggedPolynomial J d poly i) - c i) β

theorem normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist_affine
    (M d : ℕ) (hM : 0 < M) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (start : X → ℤ) (q : ℤ) (v : X → ℤ)
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (β : Fin (Fintype.card (LowTaggedIndex J d)) → ℤ) :
    (Real.fourierChar (MvPolynomial.eval (fun x => ((start x + q * v x : ℤ) : ℝ))
      (normalizedTwistFrequencyPolynomial M (truncateTaggedFrequency d a) poly)) : ℂ) =
      rationalLiftCharacterTwist M (lowTaggedFrequency J d a) c
        (fun i => MvPolynomial.eval (fun x => ((start x + q * v x : ℤ) : ℝ))
          (lowTaggedPolynomial J d poly i) - c i - (β i : ℝ))
        (fun i => (β i : ZMod M)) :=
  normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist J M d hM a poly
    (fun x => ((start x + q * v x : ℤ) : ℝ)) c β

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFrozenComparison
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct NNReal

namespace NativePolynomialOrbitFactors

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
  (R : NativePolynomialOrbitFactors D g eta A p)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]

structure FrozenMiddleRealization (a r : D.RealGroup) (b : ℝ) where
  model : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra R.subalgebra)
    s (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra R.subalgebra))
  filtration_eq : model.filtration = D.filtration.gradedRefiltration R.subalgebra
  geometry : model.GeometryComplexityLE b
  inclusion_height : ∀ i j, rationalLogHeight (D.basis.repr (model.basis i : L) j) ≤ b
  orbit : model.filtration.realification.PolynomialOrbit (fun _ : σ => 1)
  normalized : model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 orbit = 1
  middle_eval : ∀ x : σ → ℤ,
    realificationMap (hnil := model.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
      (model.filtration.realification.polynomialOrbitEval (fun _ => 1) x orbit) =
    D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (x i : ℝ)) R.middle
  spaceMap : model.Space → D.Space
  spaceMap_mk : ∀ x : model.RealGroup, spaceMap (QuotientGroup.mk x) =
    QuotientGroup.mk (a * realificationMap (hnil := model.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl x * r)
  lipBound : ℝ≥0
  lip_bound : (lipBound : ℝ) ≤ Real.exp b
  lipschitz : letI := model.metricSpace; letI := D.metricSpace; LipschitzWith lipBound spaceMap

namespace FrozenMiddleRealization

variable {R} {a r : D.RealGroup} {b : ℝ} (M : R.FrozenMiddleRealization a r b)

end FrozenMiddleRealization
end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_fixed_model_frozen_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type} {σ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (E : RationalFilteredNilmanifold M (s + 1) e) (φ : L →ₗ⁅ℚ⁆ M)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
      (T : Fin 2 → E.Niltest (fun _ : σ => 1)) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (∀ j, (T j).ComplexityLE p) →
      (∀ j x, ‖(T j).observable x‖ ≤ 1) →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p →
      ∀ a r : Fin 2 → E.RealGroup,
        (∀ j i, |(E.basis.baseChange ℝ).repr (a j).coord i| ≤ Real.exp p) →
        (∀ j, (E.basis.baseChange ℝ).equivFun (r j).coord ∈ realDenominatorGrid m) →
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x : D.RealGroup,
          (T 0).observable (QuotientGroup.mk (a 0 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r 0)) *
          star ((T 1).observable (QuotientGroup.mk (a 1 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r 1))) =
          (T 0).observable (QuotientGroup.mk (a 0 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r 0)) *
          star ((T 1).observable (QuotientGroup.mk (a 1 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r 1)))) →
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
          (fun x => (T 0).observable (QuotientGroup.mk (a 0 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            (D.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) * r 0)) *
          star ((T 1).observable (QuotientGroup.mk (a 1 * realificationMap
            (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            (D.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) * r 1))))) := by
  obtain ⟨K, _, hcover⟩ := exists_uniform_frozen_map (s + 1) 1
  obtain ⟨J, _, hdesc⟩ := exists_topInvariant_integer_expansion s
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + Polynomial.C K) ^ K + 9
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C J) ^ J)
  refine ⟨C, hC, ?_⟩
  intro L M σ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ g T p hp hD hT hcap hφ m hm hmb a r ha hr hinv
  obtain ⟨Λ, _hΛ, _hchar, _hnormal, _hfinite, _hindex, n, hn, hin, hout, hF, hmaps⟩ :=
    hcover D E φ p hp hD (hT 0).1 hφ m hm hmb
  let F := D.withLattice Λ n hn hin hout
  let u := (p + K) ^ K
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hmaps' (j : Fin 2) := hmaps (a j) (r j)
    (fun i => (ha j i).trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))) (hr j)
  choose hconj lip hlip hLip using hmaps'
  let S (j : Fin 2) : F.Niltest (fun _ : σ => 1) :=
    F.frozenComplexNiltest E φ (a j) (r j) (hconj j)
      ((T j).withUnitBound (hcap j)) g (lip j) (hLip j)
  have hSc (j : Fin 2) : (S j).ComplexityLE (p + u + 5) := by
    simpa only [show p + 1 + u + 4 = p + u + 5 by ring] using
      F.frozenComplexNiltest_complexity E φ (a j) (r j) (hconj j)
        ((T j).withUnitBound (hcap j)) g (lip j) (hLip j)
        (by linarith : 0 ≤ p + 1) hu hF
        ((T j).withUnitBound_complexity (hcap j) (hT j)) (hlip j)
  have hSn (j : Fin 2) (x : F.Space) : ‖(S j).observable x‖ ≤ 1 := (S j).norm_le x
  let U := (S 0).unitComparison (S 1) (hSn 0) (hSn 1)
  have hUc : U.ComplexityLE (p + u + 9) := by
    simpa only [show p + u + 5 + 4 = p + u + 9 by ring] using
      (S 0).unitComparison_complexity (S 1) (hSn 0) (hSn 1) (hSc 0) (hSc 1)
  have hUi (z : F.RealGroup) (hz : z ∈ F.filtration.realification.subgroup (s + 1))
      (x : F.Space) : U.observable (z • x) = U.observable x := by
    induction x using Quotient.inductionOn with
    | h x => exact hinv z hz x
  obtain ⟨V⟩ := hdesc F U (by positivity : 0 ≤ p + u + 9) hUc hUi
  have hcost : (p + u + 9 + J) ^ J ≤ (p + C) ^ C := by
    simpa [X, P, u, Polynomial.eval₂_pow] using hbudget p hp
  have heval : U.eval = (fun x => (T 0).observable (QuotientGroup.mk (a 0 * realificationMap
      (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) * r 0)) *
    star ((T 1).observable (QuotientGroup.mk (a 1 * realificationMap
      (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fun _ => 1) x g) * r 1)))) := rfl
  exact ⟨heval ▸ V.mono hcost⟩

theorem RationalFilteredNilmanifold.frozen_refiltered_group_action
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra U) s e)
    (hEF : E.filtration = D.filtration.gradedRefiltration U)
    (a r : D.RealGroup) (z : E.RealGroup)
    (hz : z ∈ E.filtration.realification.subgroup s) (x : E.RealGroup) :
    a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra U).incl (z * x) * r =
    realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra U).incl z *
      (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra U).incl x * r) := by
  let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationSubalgebra U).incl
  have hz' : (φ z).coord ∈ D.filtration.realGradedRefiltrationLayer U s := by
    apply (D.filtration.mem_native_refiltration_layer U s z.coord).mp
    have h : z.coord ∈ E.filtration.realification.layer s := hz
    simpa only [hEF] using h
  have hcomm := D.filtration.realification.top_commutes (φ z)
    (D.filtration.realGradedRefiltrationLayer_le U s hz') a
  change a * φ (z * x) * r = φ z * (a * φ x * r)
  calc
    a * φ (z * x) * r = (a * φ z) * φ x * r := by simp only [map_mul, mul_assoc]
    _ = (φ z * a) * φ x * r := by rw [← hcomm.eq]
    _ = φ z * (a * φ x * r) := by simp only [mul_assoc]

theorem exists_native_frozen_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p)
      (T : Fin 2 → D.Niltest (fun _ : σ => 1)),
      0 ≤ p → (∀ j, (T j).ComplexityLE p) →
      (∀ j x, ‖(T j).observable x‖ ≤ 1) →
      (∀ z : D.RealGroup,
        z.coord ∈ D.filtration.realGradedRefiltrationLayer R.subalgebra (s + 1) →
        ∀ x y : D.Space,
          (T 0).observable (z • x) * star ((T 1).observable (z • y)) =
            (T 0).observable x * star ((T 1).observable y)) →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p →
      ∀ a r : Fin 2 → D.RealGroup,
        (∀ j i, |(D.basis.baseChange ℝ).repr (a j).coord i| ≤ Real.exp p) →
        (∀ j, (D.basis.baseChange ℝ).equivFun (r j).coord ∈ realDenominatorGrid m) →
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
          (fun x => (T 0).observable (QuotientGroup.mk (R.frozenMiddleValue (a 0) (r 0) x)) *
            star ((T 1).observable (QuotientGroup.mk (R.frozenMiddleValue (a 1) (r 1) x))))) := by
  obtain ⟨B, _, hmodel⟩ := exists_native_middle_model
  obtain ⟨K, _, hcompare⟩ := exists_fixed_model_frozen_comparison s
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + Polynomial.C B) ^ B + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ d D g eta A p R T hp hT hcap hpair m hm hmb a r ha hr
  obtain ⟨E, hEF, _hEL, hE, hinc, orbit, horbit⟩ := hmodel D R hp (hT 0).1
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      D.filtration.gradedRefiltrationSubalgebra R.subalgebra) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let t := p + (p + B) ^ B + 4
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith [pow_nonneg (by positivity : 0 ≤ p + B) B]
  have hEt : (p + B) ^ B ≤ t := by dsimp [t]; linarith
  let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot)
    (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
  have hinv (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup (s + 1))
      (x : E.RealGroup) :
      (T 0).observable (QuotientGroup.mk (a 0 * φ (z * x) * r 0)) *
        star ((T 1).observable (QuotientGroup.mk (a 1 * φ (z * x) * r 1))) =
      (T 0).observable (QuotientGroup.mk (a 0 * φ x * r 0)) *
        star ((T 1).observable (QuotientGroup.mk (a 1 * φ x * r 1))) := by
    have htop : (φ z).coord ∈ D.filtration.realGradedRefiltrationLayer R.subalgebra (s + 1) := by
      apply (D.filtration.mem_native_refiltration_layer R.subalgebra (s + 1) z.coord).mp
      have h : z.coord ∈ E.filtration.realification.layer (s + 1) := hz
      simpa only [hEF] using h
    rw [D.frozen_refiltered_group_action R.subalgebra E hEF (a 0) (r 0) z hz x,
      D.frozen_refiltered_group_action R.subalgebra E hEF (a 1) (r 1) z hz x]
    exact hpair (φ z) htop (QuotientGroup.mk (a 0 * φ x * r 0))
      (QuotientGroup.mk (a 1 * φ x * r 1))
  obtain ⟨V⟩ := hcompare E D (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
    orbit T ht (hE.mono E hEt) (fun j => (hT j).mono hpt) hcap
    (fun i j => (hinc j i).trans hEt) m hm (hmb.trans (Real.exp_le_exp.mpr hpt))
    a r (fun j i => (ha j i).trans (Real.exp_le_exp.mpr hpt)) hr hinv
  have hcost : (t + K) ^ K ≤ (p + C) ^ C := by
    simpa [X, P, t, Polynomial.eval₂_pow] using hbudget p hp
  have heval : (fun x => (T 0).observable (QuotientGroup.mk
      (a 0 * φ (E.filtration.realification.polynomialOrbitEval (fun _ => 1) x orbit) * r 0)) *
      star ((T 1).observable (QuotientGroup.mk
        (a 1 * φ (E.filtration.realification.polynomialOrbitEval (fun _ => 1) x orbit) * r 1)))) =
    (fun x => (T 0).observable (QuotientGroup.mk (R.frozenMiddleValue (a 0) (r 0) x)) *
      star ((T 1).observable (QuotientGroup.mk (R.frozenMiddleValue (a 1) (r 1) x)))) := by
    funext x
    dsimp only [φ]
    simp only [horbit]
    rfl
  exact ⟨heval ▸ V.mono hcost⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeRankPolynomialFactorization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {E : RationalFilteredNilmanifold L s n} (T : E.DegreeRankStructure r)

theorem polynomialOrbit_mul_coefficient_sub_mem_rank_two
    (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (g h : E.filtration.realification.PolynomialOrbit w) :
    coefficients (g * h).log α - (coefficients g.log α + coefficients h.log α) ∈
      (T.filtration.layer (Finsupp.weight w α) 2).baseChange ℝ := by
  have hh := T.filtration.realification.polynomialOrbit_mul_coefficient_sub_mem_rank_two
    hs w α (T.orbitEquiv w g) (T.orbitEquiv w h)
  rw [← map_mul, T.orbitEquiv_log, T.orbitEquiv_log, T.orbitEquiv_log] at hh
  exact hh

theorem exists_polynomialOrbit_factorization_rank_two
    (hs : 1 ≤ s) (w : σ → ℕ) (α : ι → σ →₀ ℕ)
    (g ε A U ρ : E.filtration.realification.PolynomialOrbit w)
    (hg : E.filtration.realification.polynomialOrbitEval w 0 g = 1)
    (hε : E.filtration.realification.polynomialOrbitEval w 0 ε = 1)
    (hA : E.filtration.realification.polynomialOrbitEval w 0 A = 1)
    (hU : E.filtration.realification.polynomialOrbitEval w 0 U = 1)
    (hρ : E.filtration.realification.polynomialOrbitEval w 0 ρ = 1)
    (hcoeff : ∀ i, coefficients g.log (α i) -
      (coefficients ε.log (α i) + coefficients A.log (α i) +
        coefficients U.log (α i) + coefficients ρ.log (α i)) ∈
          (T.filtration.layer (Finsupp.weight w (α i)) 2).baseChange ℝ) :
    ∃ K : E.filtration.realification.PolynomialOrbit w,
      E.filtration.realification.polynomialOrbitEval w 0 K = 1 ∧ ε * A * K * U * ρ = g ∧
      ∀ i, coefficients K.log (α i) ∈
        (T.filtration.layer (Finsupp.weight w (α i)) 2).baseChange ℝ := by
  obtain ⟨K, hK0, hprod, hK⟩ := T.filtration.realification.exists_polynomialOrbit_factorization_rank_two
    hs w α (T.orbitEquiv w g) (T.orbitEquiv w ε) (T.orbitEquiv w A)
    (T.orbitEquiv w U) (T.orbitEquiv w ρ)
    ((T.orbitEquiv_eval w g 0).trans hg) ((T.orbitEquiv_eval w ε 0).trans hε)
    ((T.orbitEquiv_eval w A 0).trans hA) ((T.orbitEquiv_eval w U 0).trans hU)
    ((T.orbitEquiv_eval w ρ 0).trans hρ) (by
      intro i
      change coefficients (T.orbitEquiv w g).log (α i) -
        (coefficients (T.orbitEquiv w ε).log (α i) + coefficients (T.orbitEquiv w A).log (α i) +
          coefficients (T.orbitEquiv w U).log (α i) + coefficients (T.orbitEquiv w ρ).log (α i)) ∈
        (T.filtration.layer (Finsupp.weight w (α i)) 2).baseChange ℝ
      simpa only [T.orbitEquiv_log] using hcoeff i)
  let K' := (T.orbitEquiv w).symm K
  have hK'eq : T.orbitEquiv w K' = K := (T.orbitEquiv w).apply_symm_apply K
  have hK'log : K'.log = K.log := by
    rw [← hK'eq, T.orbitEquiv_log]
  refine ⟨K', ?_, ?_, ?_⟩
  · have hh := T.orbitEquiv_eval w K' 0
    rw [hK'eq] at hh
    exact hh.symm.trans hK0
  · apply (T.orbitEquiv w).injective
    simpa only [map_mul, hK'eq] using hprod
  · intro i
    rw [hK'log]
    exact hK i

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonDescent
namespace OAI

section

namespace Erdos3

noncomputable def rankUnitDescentConstant (s : ℕ) : ℕ :=
  (RationalFilteredNilmanifold.UnitVerticalObservable.exists_lower_rank_family.{0, 0, 0} s).choose

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} 
  
  
   (hbQ : b ≤ Q) 
  
  
  
  
  
  
  


variable   {p' q' P' : ℝ}
  
  

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedProductChartRadius
namespace OAI

section

namespace Erdos3

theorem finiteRowChartRadius_support_le_inv (rows dim : ℕ) {C T : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) :
    T ≤ (finiteRowChartRadius rows dim C T)⁻¹ := by
  simp only [finiteRowChartRadius, one_div, inv_inv]
  calc
    T ≤ 1 * 1 * 1 * 1 * (T + 1) := by linarith
    _ ≤ 4 * ((rows : ℝ) + 1) * (C + 1) * ((dim : ℝ) + 1) * (T + 1) := by
      gcongr <;> linarith [Nat.cast_nonneg (α := ℝ) rows, Nat.cast_nonneg (α := ℝ) dim]

namespace VectorPolynomial

def allocatedProductChartLog {A : Type*} [Semiring A] (m : ℕ) (D c : A) : A :=
  4 * ((8 * allocatedIdealCoverInputLog m D c + 14) + 2 * D + 2) + 6

theorem allocatedProductChartLog_bounds (m : ℕ) {D c : ℝ} (hD : 0 ≤ D) (hc : 0 ≤ c) :
    let H := 8 * allocatedIdealCoverInputLog m D c + 14
    let F := H + 2 * D + 2
    0 ≤ H ∧ 0 ≤ F ∧ 2 * D ≤ F ∧ D ≤ F ∧ c ≤ F ∧
      H + 1 ≤ allocatedProductChartLog m D c ∧ 0 ≤ allocatedProductChartLog m D c := by
  obtain ⟨hL, _, _, _, _, hcL⟩ := allocatedIdealCoverInputLog_bounds m hD hc
  dsimp only [allocatedProductChartLog]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem allocatedProductChartLog_mono (m : ℕ) {D c D' c' : ℝ}
    (hD : 0 ≤ D) (hDD : D ≤ D') (hcc : c ≤ c') :
    allocatedProductChartLog m D c ≤ allocatedProductChartLog m D' c' := by
  unfold allocatedProductChartLog allocatedIdealCoverInputLog allocatedSiteCoefficientLog
  gcongr

noncomputable def allocatedProductChartRadius (m : ℕ) (D c : ℝ) : ℝ :=
  Real.exp (-allocatedProductChartLog m D c)

theorem allocatedProductChartRadius_bounds (m : ℕ) {D c : ℝ} (hD : 0 ≤ D) (hc : 0 ≤ c) :
    0 < allocatedProductChartRadius m D c ∧ allocatedProductChartRadius m D c ≤ 1 ∧
      (allocatedProductChartRadius m D c)⁻¹ = Real.exp (allocatedProductChartLog m D c) ∧
      allocatedProductChartRadius m D c ≤
        Real.exp (-(8 * allocatedIdealCoverInputLog m D c + 14 + 1)) := by
  obtain ⟨_, _, _, _, _, hHQ, hQ⟩ := allocatedProductChartLog_bounds m hD hc
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hQ), ?_, ?_⟩
  · simp only [allocatedProductChartRadius, Real.exp_neg, inv_inv]
  · exact Real.exp_le_exp.mpr (neg_le_neg hHQ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D c : ℝ}
variable (hdim : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)
variable (hc : 0 ≤ c) (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ D) (hn : ∀ j, (n j : ℝ) ≤ D)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c)

local notation "H" => 8 * allocatedIdealCoverInputLog m D c + 14
local notation "F" => H + 2 * D + 2

include hdim hc hI hn hC hCc in
theorem allocatedProductIdealSiteRadius_exp_bound :
    2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) ≤ Real.exp F := by
  have hD := hdim.nonneg
  have hde : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hH := (allocatedProductChartLog_bounds m hD hc).1
  have hsupport (j : Fin m) : allocatedIdealCoverSupport (G := G) B rowSets j ≤ Real.exp H :=
    (finiteRowChartRadius_support_le_inv (rowSets j).card (Fintype.card (I j))
      (hC j) (allocatedIdealCoverSupport_nonneg B rowSets j)).trans
      (allocatedIdealCoverRadius_inverse_from_dimensions B rowSets hdim hc hI hn C hC hCc j)
  have hrows (j : Fin m) : ((rowSets j).card : ℝ) ≤ D := by
    simpa only [Fintype.card_coe] using hdim.rows j
  have hsum : (∑ j : Fin m, (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j) ≤
      Real.exp (2 * D + H) := by
    calc
      _ ≤ ∑ _j : Fin m, D * Real.exp H := Finset.sum_le_sum (fun j _ =>
        mul_le_mul (hrows j) (hsupport j) (allocatedIdealCoverSupport_nonneg B rowSets j) hD)
      _ = (m : ℝ) * (D * Real.exp H) := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ Real.exp D * (Real.exp D * Real.exp H) :=
        mul_le_mul (hdim.degree.trans hde)
          (mul_le_mul_of_nonneg_right hde (Real.exp_pos _).le)
          (mul_nonneg hD (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hradius : (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) ≤
      Real.exp (2 * D + H + 1) := by
    change 1 + ∑ j : Fin m, (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j ≤ _
    exact one_add_le_exp_succ (add_nonneg (mul_nonneg (by norm_num) hD) hH) hsum
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp 1 * Real.exp (2 * D + H + 1) :=
      mul_le_mul htwo hradius (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

include hdim hc hI hn hC hCc in
theorem allocatedProductGridRadius_inv_exp_bound (j : Fin m) :
    (allocatedProductGridRadius (G := G) B rowSets C j)⁻¹ ≤
      Real.exp (allocatedProductChartLog m D c) := by
  obtain ⟨_, hF, h2DF, hDF, hcF, _, _⟩ := allocatedProductChartLog_bounds m hdim.nonneg hc
  have hrows : ((rowSets j).card : ℝ) ≤ D := by
    simpa only [Fintype.card_coe] using hdim.rows j
  have hrowadd : ((rowSets j).card : ℝ) + 1 ≤ Real.exp D := by
    linarith [Real.add_one_le_exp D]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsites : (Fintype.card (Finset α) : ℝ) ≤ Real.exp D := by
    simpa only [Fintype.card_finset, Nat.cast_pow, Nat.cast_ofNat, mul_one] using
      pow_le_exp_mul_of_le_exp (by norm_num : (0 : ℝ) ≤ 2) htwo
        (by norm_num : (0 : ℝ) ≤ 1) (Fintype.card α) hdim.cube
  have hrowcount : ((((rowSets j).card + 1) * Fintype.card (Finset α) : ℕ) : ℝ) ≤ Real.exp F := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact ((mul_le_mul hrowadd hsites (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (show Real.exp D * Real.exp D = Real.exp (2 * D) by rw [← Real.exp_add]; congr 1; ring)).trans
        (Real.exp_le_exp.mpr h2DF)
  have hDexp : D ≤ Real.exp F :=
    (show D ≤ Real.exp D by linarith [Real.add_one_le_exp D]).trans (Real.exp_le_exp.mpr hDF)
  exact finiteRowChartRadius_inv_le_exp
    (((rowSets j).card + 1) * Fintype.card (Finset α)) (Fintype.card (I j))
    (hC j) (mul_nonneg (by norm_num) (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg)
    hF hrowcount ((hI j).trans hDexp) ((hCc j).trans (Real.exp_le_exp.mpr hcF))
    (allocatedProductIdealSiteRadius_exp_bound B rowSets hdim hc hI hn C hC hCc)

include hdim hc hI hn hC hCc in
theorem allocatedProductChartRadius_le_charts (j : Fin m) :
    allocatedProductChartRadius m D c ≤ allocatedProductGridRadius (G := G) B rowSets C j ∧
      allocatedProductChartRadius m D c ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j ∧
      allocatedProductChartRadius m D c ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
  have hgrid := allocatedProductGridRadius_inv_exp_bound B rowSets hdim hc hI hn C hC hCc j
  have hgridPos := allocatedProductGridRadius_pos (G := G) B rowSets C hC j
  have hg := (inv_le_inv₀ (Real.exp_pos (allocatedProductChartLog m D c)) (inv_pos.mpr hgridPos)).2 hgrid
  have hgridLe : allocatedProductChartRadius m D c ≤ allocatedProductGridRadius (G := G) B rowSets C j := by
    simpa only [allocatedProductChartRadius, Real.exp_neg, inv_inv] using hg
  have hcover := allocatedIdealCoverRadius_inverse_from_dimensions B rowSets hdim hc hI hn C hC hCc j
  have hcoverPos := allocatedIdealCoverRadius_pos (G := G) B rowSets C hC j
  have hcInv := (inv_le_inv₀ (Real.exp_pos H) (inv_pos.mpr hcoverPos)).2 hcover
  have hcLe : Real.exp (-H) ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
    simpa only [Real.exp_neg, inv_inv] using hcInv
  have hhalf : allocatedProductChartRadius m D c ≤
      allocatedIdealCoverRadius (G := G) B rowSets C j / 2 := by
    apply ((allocatedProductChartRadius_bounds m hdim.nonneg hc).2.2.2).trans
    apply le_trans _ (div_le_div_of_nonneg_right hcLe (by norm_num : (0 : ℝ) ≤ 2))
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp (-(H + 1)) * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_pos _).le
      _ = Real.exp (-H) := by rw [← Real.exp_add]; congr 1; ring
  exact ⟨hgridLe, hhalf.trans (allocatedIdealCoverRadius_half_le_physical B rowSets C hC j),
    hhalf.trans (by linarith)⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedUniformEarlyRadiusWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedBufferedRadiusInput {A : Type*} [Semiring A] (m : ℕ) (p g : A) : A :=
  allocatedComparisonDimension m p + g + ((2 * m + 5) * (m + 1) + 5 : ℕ)

noncomputable def allocatedBufferedRadiusLog {A : Type*} [Semiring A] (m : ℕ) (p g : A) : A :=
  (m + 10 : ℕ) * (allocatedBufferedRadiusInput m p g + (m + 3 : ℕ))

noncomputable def allocatedCommonRadiusLog {A : Type*} [Semiring A]
    (m : ℕ) (p g : A) : A :=
  allocatedBufferedRadiusLog m p g + allocatedIdealCoverPrimitiveLog m p g

noncomputable def allocatedCommonRadius (m : ℕ) (p g : ℝ) : ℝ :=
  Real.exp (-allocatedCommonRadiusLog m p g)

theorem allocatedBufferedRadiusInput_bounds (m : ℕ) {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) :
    let P := allocatedBufferedRadiusInput m p g
    0 ≤ P ∧ allocatedComparisonDimension m p ≤ P ∧ g ≤ P ∧
      (((2 * m + 5) * (m + 1) + 5 : ℕ) : ℝ) ≤ P := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  dsimp only [allocatedBufferedRadiusInput]
  have ha : (0 : ℝ) ≤ ((2 * m + 5) * (m + 1) + 5 : ℕ) := Nat.cast_nonneg _
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem allocatedCommonRadiusLog_bounds (m : ℕ) {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) :
    0 ≤ allocatedCommonRadiusLog m p g ∧
      allocatedBufferedRadiusLog m p g ≤ allocatedCommonRadiusLog m p g ∧
      allocatedIdealCoverPrimitiveLog m p g ≤ allocatedCommonRadiusLog m p g := by
  have hP := (allocatedBufferedRadiusInput_bounds m hp hg).1
  have hb : 0 ≤ allocatedBufferedRadiusLog m p g := by
    unfold allocatedBufferedRadiusLog
    positivity
  have hi := (allocatedIdealCoverPrimitiveRadius_bounds m hp hg).1
  dsimp only [allocatedCommonRadiusLog]
  exact ⟨add_nonneg hb hi, le_add_of_nonneg_right hi, le_add_of_nonneg_left hb⟩

theorem allocatedCommonRadiusLog_mono (m : ℕ) {p g p' g' : ℝ}
    (hp : 0 ≤ p) (_hg : 0 ≤ g) (hpp : p ≤ p') (hgg : g ≤ g') :
    allocatedCommonRadiusLog m p g ≤ allocatedCommonRadiusLog m p' g' := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hDD := allocatedComparisonDimension_mono m hp hpp
  unfold allocatedCommonRadiusLog allocatedBufferedRadiusLog allocatedBufferedRadiusInput
    allocatedIdealCoverPrimitiveLog allocatedIdealCoverInputLog allocatedSiteCoefficientLog
  gcongr

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

theorem allocatedCommonRadius_admissible {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hq : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g) (j : Fin m) :
    allocatedCommonRadius m p g ≤ allocatedBufferedPhysicalChartRadius (G := G) B α C j ∧
      allocatedCommonRadius m p g ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j ∧
      allocatedCommonRadius m p g ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
  obtain ⟨_, hb, hi⟩ := allocatedCommonRadiusLog_bounds m hp hg
  have hbuffer : allocatedCommonRadius m p g ≤ allocatedBufferedPhysicalChartRadius (G := G) B α C j := by
    have hinv := (allocatedBufferedRadius_inverse_from_primitive B hp hg hq hvars hI hn C hC hCg j).trans
      (Real.exp_le_exp.mpr hb)
    have hpos := allocatedBufferedPhysicalChartRadius_pos (G := G) B α C hC j
    have h := (inv_le_inv₀ (Real.exp_pos (allocatedCommonRadiusLog m p g)) (inv_pos.mpr hpos)).2 hinv
    simpa only [allocatedCommonRadius, Real.exp_neg, inv_inv] using h
  refine ⟨hbuffer, hbuffer.trans (allocatedBufferedPhysicalChartRadius_le_original B α C hC j), ?_⟩
  apply le_trans _ (allocatedIdealCoverPrimitiveRadius_le B rowSets hp hg hq hvars hI hn C hC hCg j)
  exact Real.exp_le_exp.mpr (neg_le_neg hi)

end Charts

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCommonProductRadiusLog {A : Type*} [Semiring A]
    (m : ℕ) (p g : A) : A :=
  allocatedCommonRadiusLog m p g +
    allocatedProductChartLog m (allocatedComparisonDimension m p) g

noncomputable def allocatedCommonProductRadius (m : ℕ) (p g : ℝ) : ℝ :=
  Real.exp (-allocatedCommonProductRadiusLog m p g)

theorem allocatedCommonProductRadius_bounds (m : ℕ) {p g : ℝ} (hp : 0 ≤ p) (hg : 0 ≤ g) :
    0 ≤ allocatedCommonProductRadiusLog m p g ∧
      0 < allocatedCommonProductRadius m p g ∧ allocatedCommonProductRadius m p g ≤ 1 ∧
      (allocatedCommonProductRadius m p g)⁻¹ = Real.exp (allocatedCommonProductRadiusLog m p g) ∧
      allocatedCommonProductRadius m p g ≤ allocatedCommonRadius m p g ∧
      allocatedCommonProductRadius m p g ≤
        allocatedProductChartRadius m (allocatedComparisonDimension m p) g ∧
      allocatedCommonProductRadius m p g ≤ allocatedSourceCoverRadius m p g := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hcommon := (allocatedCommonRadiusLog_bounds m hp hg).1
  have hproduct := (allocatedProductChartLog_bounds m hD hg).2.2.2.2.2.2
  have hlog : 0 ≤ allocatedCommonProductRadiusLog m p g := add_nonneg hcommon hproduct
  have hc : allocatedCommonProductRadius m p g ≤ allocatedCommonRadius m p g :=
    Real.exp_le_exp.mpr (neg_le_neg (le_add_of_nonneg_right hproduct))
  have hp' : allocatedCommonProductRadius m p g ≤
      allocatedProductChartRadius m (allocatedComparisonDimension m p) g :=
    Real.exp_le_exp.mpr (neg_le_neg (le_add_of_nonneg_left hcommon))
  refine ⟨hlog, Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlog), ?_, hc, hp', ?_⟩
  · simp only [allocatedCommonProductRadius, Real.exp_neg, inv_inv]
  · exact hp'.trans (allocatedProductChartRadius_bounds m hD hg).2.2.2

theorem allocatedCommonProductRadiusLog_mono (m : ℕ) {p g p' g' : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hpp : p ≤ p') (hgg : g ≤ g') :
    allocatedCommonProductRadiusLog m p g ≤ allocatedCommonProductRadiusLog m p' g' := by
  exact add_le_add (allocatedCommonRadiusLog_mono m hp hg hpp hgg)
    (allocatedProductChartLog_mono m (allocatedComparisonDimension_bounds m hp).1
      (allocatedComparisonDimension_mono m hp hpp) hgg)

theorem exists_allocatedCommonProductRadiusLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p g : ℝ}, 0 ≤ p → 0 ≤ g →
      allocatedCommonProductRadiusLog m p g ≤ (p + g + a) ^ a := by
  let poly : Polynomial ℕ := allocatedCommonProductRadiusLog m Polynomial.X Polynomial.X
  obtain ⟨a, ha, hb⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p g hp hg
  apply (allocatedCommonProductRadiusLog_mono m hp hg (le_add_of_nonneg_right hg)
    (le_add_of_nonneg_left hp)).trans
  simpa [poly, allocatedCommonProductRadiusLog, allocatedCommonRadiusLog,
    allocatedBufferedRadiusLog, allocatedBufferedRadiusInput, allocatedProductChartLog,
    allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
    allocatedComparisonDimension, Polynomial.eval₂_pow] using hb (p + g) (add_nonneg hp hg)

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedCommonProductRadius_admissible {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hq : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g) (j : Fin m) :
    allocatedCommonProductRadius m p g ≤ allocatedBufferedPhysicalChartRadius (G := G) B α C j ∧
      allocatedCommonProductRadius m p g ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j ∧
      allocatedCommonProductRadius m p g ≤ allocatedIdealCoverRadius (G := G) B rowSets C j ∧
      allocatedCommonProductRadius m p g ≤ allocatedProductGridRadius (G := G) B rowSets C j := by
  obtain ⟨_, _, _, _, hcommon, hproduct, _⟩ := allocatedCommonProductRadius_bounds m hp hg
  obtain ⟨hbuffer, hphysical, hideal⟩ := allocatedCommonRadius_admissible B rowSets
    hp hg hq hvars hI hn C hC hCg j
  have hdim := allocatedComparisonDimensions_of_primitive (G := G) (α := α)
    (O := fun k => (rowSets k : Type _)) B (fun k => (Subtype.val : rowSets k → Finset α))
    hq (fun _ => Subtype.val_injective) hp hvars hI hn
  have hpD := (allocatedComparisonDimension_bounds m hp).2.2.1
  have hgrid := (allocatedProductChartRadius_le_charts B rowSets hdim hg
    (fun k => (hI k).trans hpD) (fun k => (hn k).trans hpD) C hC hCg j).1
  exact ⟨hcommon.trans hbuffer, hcommon.trans hphysical, hcommon.trans hideal, hproduct.trans hgrid⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable [∀ j, Nonempty (rowSets j)]

theorem allocatedCanonicalSlice_source_geometry
    {p g : ℝ} (hp : 0 ≤ p) (hg : 0 ≤ g) (hdim : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g)
    {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedCommonProductRadius m p g) :
    let T := allocatedIdealCoverSupport (G := G) B rowSets
    let r := allocatedProductIdealSiteRadius (G := G) B rowSets
    1 ≤ r ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius α m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (r : ℝ)) ∧
      (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
      (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4) := by
  intro T r
  have hgrid (j) : R j ≤ allocatedProductGridRadius (G := G) B rowSets C j :=
    (hsmall j).trans (allocatedCommonProductRadius_admissible B rowSets hp hg hdim hvars hI hn C hC hCg j).2.2.2
  have hT0 := allocatedIdealCoverSupport_nonneg (G := G) B rowSets
  have hrdom := allocatedProductIdealSiteRadius_dominates (G := G) B rowSets
  refine ⟨allocatedProductIdealSiteRadius_one_le B rowSets, hT0,
    allocatedIdealCoverSupport_ideal B rowSets, allocatedIdealCoverSupport_inactive B rowSets,
    hrdom, ?_, allocatedProductGridRadius_recovery_budget B rowSets C hC hR hgrid⟩
  intro j
  have hrow : (1 : ℝ) ≤ (rowSets j).card := by
    let a : rowSets j := Classical.choice (inferInstance : Nonempty (rowSets j))
    exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨a.val, a.property⟩)
  have hTr : T j ≤ (r : ℝ) := by
    calc
      _ ≤ (rowSets j).card * T j := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hrow (hT0 j)
      _ ≤ _ := hrdom j
  have hT2r : T j ≤ 2 * (r : ℝ) := by linarith [r.coe_nonneg]
  apply le_trans _ (allocatedProductGridRadius_source_budget B rowSets C hC hR hgrid j)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT2r (hR j)) (by positivity)) (hC j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

section Charts

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

end Charts
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedFiniteForward_shiftedPower_le_work (A C : ℕ)
    (stageCountConstant : ℕ → ℕ) (stage : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hC : C ≤ A) (hx : 0 ≤ x) :
    (x + C) ^ C ≤ preparedFiniteForwardWork A stageCountConstant stage x := by
  have hp := preparedFiniteForwardParameter_nonneg A stageCountConstant stage hx
  have hxp := le_preparedFiniteForwardParameter A stageCountConstant stage hx
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hCreal : (C : ℝ) ≤ A := Nat.cast_le.mpr hC
  rw [preparedFiniteForwardWork_eq]
  exact (pow_le_pow_left₀ (add_nonneg hx (Nat.cast_nonneg C))
    (add_le_add hxp hCreal) C).trans
      (pow_le_pow_right₀ (by linarith only [hp, hAreal]) hC)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable [∀ j, Nonempty (rowSets j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uα
open scoped Classical BigOperators NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LowTaggedCoordinateRestriction
namespace OAI

section

namespace Erdos3
open Module
open scoped BigOperators

variable {B R : Type*} [Fintype B] [Field R]

theorem pi_basisGradeProjection_apply (w : B → ℕ) (h : ℕ) (x : B → R) (i : B) :
    basisGradeProjection (Pi.basisFun R B) w h x i = if w i = h then x i else 0 := by
  simpa only [Pi.basisFun_repr] using
    basisGradeProjection_repr (Pi.basisFun R B) w h x i

theorem sum_positive_coordinate_grades
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : B → R) :
    (∑ h : Fin d, basisGradeProjection (Pi.basisFun R B) w (h.val + 1) x) = x := by
  classical
  funext i
  rw [Finset.sum_apply]
  simp_rw [pi_basisGradeProjection_apply]
  let hi : Fin d := ⟨w i - 1, by have := hw i; have := hwd i; omega⟩
  have he (h : Fin d) : w i = h.val + 1 ↔ h = hi := by
    dsimp only [hi]
    have := hw i
    constructor
    · intro hh
      apply Fin.ext
      change h.val = w i - 1
      omega
    · intro hh
      subst h
      change w i = (w i - 1) + 1
      omega
  simp_rw [he]
  simp

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedSlot (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (k : J j) : Fin (Fintype.card (LowTaggedIndex J d)) :=
  Fintype.equivFin (LowTaggedIndex J d) ⟨⟨j, k⟩, hj⟩

@[simp] theorem lowTaggedIndex_slot (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (k : J j) : lowTaggedIndex J d (lowTaggedSlot J d j hj k) = ⟨j, k⟩ := by
  simp [lowTaggedIndex, lowTaggedSlot]

theorem lowTaggedSlot_injective (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d) :
    Function.Injective (lowTaggedSlot J d j hj) := by
  intro k l h
  have he := congrArg (lowTaggedIndex J d) h
  simpa using he

theorem lowTaggedSlot_eq_of_tag (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (i : Fin (Fintype.card (LowTaggedIndex J d)))
    (hi : (lowTaggedIndex J d i).1 = j) :
    ∃ k : J j, lowTaggedSlot J d j hj k = i := by
  let q := (Fintype.equivFin (LowTaggedIndex J d)).symm i
  have hq : q.val.1 = j := hi
  have hqi : Fintype.equivFin (LowTaggedIndex J d) q = i :=
    (Fintype.equivFin (LowTaggedIndex J d)).apply_symm_apply i
  obtain ⟨⟨j', k⟩, h⟩ := q
  dsimp at hq
  subst j'
  exact ⟨k, hqi⟩

noncomputable def lowTaggedEmbedding (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d) :
    (J j → ℝ) →ₗ[ℝ] (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) := by
  classical
  exact ∑ k : J j,
    (LinearMap.single ℝ (fun _ : Fin (Fintype.card (LowTaggedIndex J d)) => ℝ)
      (lowTaggedSlot J d j hj k)).comp (LinearMap.proj k)

theorem lowTaggedEmbedding_apply (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (v : J j → ℝ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    lowTaggedEmbedding J d j hj v i =
      ∑ k : J j, (Pi.single (lowTaggedSlot J d j hj k) (v k) :
        Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) i := by
  classical
  simp [lowTaggedEmbedding, LinearMap.sum_apply, Finset.sum_apply]

@[simp] theorem lowTaggedEmbedding_apply_slot (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (v : J j → ℝ) (k : J j) :
    lowTaggedEmbedding J d j hj v (lowTaggedSlot J d j hj k) = v k := by
  classical
  rw [lowTaggedEmbedding_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    exact Pi.single_eq_of_ne (fun he => hl
      ((lowTaggedSlot_injective J d j hj) he.symm)) _
  · simp

theorem lowTaggedEmbedding_apply_of_ne (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (v : J j → ℝ)
    (i : Fin (Fintype.card (LowTaggedIndex J d)))
    (hi : (lowTaggedIndex J d i).1 ≠ j) :
    lowTaggedEmbedding J d j hj v i = 0 := by
  classical
  rw [lowTaggedEmbedding_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply Pi.single_eq_of_ne
  intro he
  apply hi
  rw [he, lowTaggedIndex_slot]

theorem lowTaggedEmbedding_pairing (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (a : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) (v : J j → ℝ) :
    (∑ i, a i * lowTaggedEmbedding J d j hj v i) =
      ∑ k : J j, a (lowTaggedSlot J d j hj k) * v k := by
  classical
  simp only [lowTaggedEmbedding, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.single_apply, LinearMap.proj_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [Pi.single_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedRestriction (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d) :
    (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) →ₗ[ℝ] (J j → ℝ) :=
  LinearMap.pi fun k => LinearMap.proj (lowTaggedSlot J d j hj k)

@[simp] theorem lowTaggedRestriction_apply (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (k : J j) :
    lowTaggedRestriction J d j hj z k = z (lowTaggedSlot J d j hj k) := rfl

@[simp] theorem lowTaggedRestriction_embedding (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (v : J j → ℝ) :
    lowTaggedRestriction J d j hj (lowTaggedEmbedding J d j hj v) = v := by
  funext k
  exact lowTaggedEmbedding_apply_slot J d j hj v k

theorem lowTaggedEmbedding_restriction (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :
    lowTaggedEmbedding J d j hj (lowTaggedRestriction J d j hj z) =
      basisGradeProjection (Pi.basisFun ℝ _) (lowTaggedWeight J d) (j.val + 1) z := by
  classical
  funext i
  rw [pi_basisGradeProjection_apply]
  by_cases hi : (lowTaggedIndex J d i).1 = j
  · obtain ⟨k, rfl⟩ := lowTaggedSlot_eq_of_tag J d j hj i hi
    simp [lowTaggedWeight]
  · have hw : lowTaggedWeight J d i ≠ j.val + 1 := by
      intro hw
      apply hi
      apply Fin.ext
      exact Nat.add_right_cancel hw
    rw [lowTaggedEmbedding_apply_of_ne J d j hj _ i hi, if_neg hw]

theorem lowTagged_comap_eq_map (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d) K) :
    K.comap (lowTaggedEmbedding J d j hj) = K.map (lowTaggedRestriction J d j hj) := by
  apply le_antisymm
  · intro v hv
    exact ⟨lowTaggedEmbedding J d j hj v, hv,
      lowTaggedRestriction_embedding J d j hj v⟩
  · rintro v ⟨z, hz, rfl⟩
    change lowTaggedEmbedding J d j hj (lowTaggedRestriction J d j hj z) ∈ K
    rw [lowTaggedEmbedding_restriction]
    exact hK (j.val + 1) z hz

theorem lowTagged_comap_span_eq {A : Type*} (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d)
    (g : A → Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (hg : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d)
      (Submodule.span ℝ (Set.range g))) :
    (Submodule.span ℝ (Set.range g)).comap (lowTaggedEmbedding J d j hj) =
      Submodule.span ℝ (Set.range (fun a k => g a (lowTaggedSlot J d j hj k))) := by
  rw [lowTagged_comap_eq_map J d j hj _ hg, Submodule.map_span, ← Set.range_comp]
  rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastActiveGridIntegralComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical NNReal

variable {X : Type*} [Fintype X]
variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis L a}, Unit)
local notation "Cont" => (Σ j : Fin m, I j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L

def forecastJointAxisEquiv : Spatial ⊕ Output ≃ Cont ⊕ (X ⊕ IntAxis) where
  toFun a := match a with
    | .inl s => .inr (.inl s.1)
    | .inr a => match forecastActiveAxisEquiv U basis L a with
      | .inl c => .inl c
      | .inr z => .inr (.inr z)
  invFun a := match a with
    | .inl c => .inr ((forecastActiveAxisEquiv U basis L).symm (.inl c))
    | .inr (.inl x) => .inl ⟨x, .inl ()⟩
    | .inr (.inr z) => .inr ((forecastActiveAxisEquiv U basis L).symm (.inr z))
  left_inv a := by
    rcases a with ⟨x, u | e⟩ | a
    · cases u; rfl
    · exact e.elim
    · obtain ⟨c | z, rfl⟩ := (forecastActiveAxisEquiv U basis L).symm.surjective a
      all_goals simp only [Equiv.apply_symm_apply]
  right_inv a := by
    rcases a with c | x | z
    all_goals simp only [Equiv.apply_symm_apply]

def forecastJointCoordinateJoinEquiv :
    ((Cont → ℝ) × ((X ⊕ IntAxis) → ℝ)) ≃ᵐ ((Spatial → ℝ) × (Output → ℝ)) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Cont ⊕ (X ⊕ IntAxis) => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Spatial ⊕ Output => ℝ)
      (forecastJointAxisEquiv (X := X) (I := I) U basis L).symm).trans
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Spatial ⊕ Output => ℝ)))

def forecastJointCoordinateJoin (c : Cont → ℝ) (z : (X ⊕ IntAxis) → ℝ) :
    (Spatial → ℝ) × (Output → ℝ) :=
  (fun a => z (.inl a.1),
   forecastActiveCoordinateJoin U basis L c (fun a => z (.inr a)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "scale" => allocatedActiveIntegerGridScale U basis R S.value

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFixedPathRecoveredJointGridComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical
variable {X : Type*} {m : ℕ} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis L
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L

def forecastCongruenceJointAxisEquiv : Out ≃ Aux ⊕ (X ⊕ IntAxis) where
  toFun a := match a with
    | ⟨_, .inl x⟩ => .inr (.inl x.val)
    | ⟨j, .inr (.inl e)⟩ => .inl ⟨j, e⟩
    | ⟨j, .inr (.inr i)⟩ => .inr (.inr ⟨⟨j, i.val⟩, Nat.lt_of_not_ge i.property⟩)
  invFun a := match a with
    | .inl ⟨j, e⟩ => ⟨j, .inr (.inl e)⟩
    | .inr (.inl x) => ⟨⟨0, hm⟩, .inl ⟨x, rfl⟩⟩
    | .inr (.inr a) => ⟨a.val.1, .inr (.inr ⟨a.val.2, Nat.not_le.mpr a.property⟩)⟩
  left_inv a := by
    rcases a with ⟨j, x | e | i⟩
    · rcases j with ⟨j, hj⟩
      rcases x with ⟨x, hx⟩
      change j = 0 at hx
      subst j
      rfl
    · rfl
    · rfl
  right_inv a := by
    rcases a with ⟨j, e⟩ | x | ⟨⟨j, i⟩, ha⟩ <;> rfl

variable [Fintype X] [∀ j, Fintype (E j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis L
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

noncomputable def forecastJointOriginalGridMean : ℂ :=
  𝔼 aux : Aux → ZMod N, ∫ c : Cont → ℝ,
    (∑' z, ∑' k : Joint → ℤ,
      (density (join c (fun j => ((k j : ℝ) - center j) / scale j)) : ℂ) *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
        (fun a => Sum.elim aux (fun j => (k j : ZMod N)) (axis a)) / gridVolume : ℝ) : ℂ) *
      test z (fun a => Sum.elim (zmodPiReduction hq aux)
        (fun j => (k j : ZMod q)) (axis a))
        (join c (fun j => ((k j : ℝ) - center j) / scale j))) /
      ((∏ j, scale j : ℝ) : ℂ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

variable [NeZero q]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Output" => (Σ _a : Active, Unit)

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)

local notation "sides" => allocatedPrincipalSides B U basis S

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (Pr : Finset ℕ) [∀ p : Pr, NeZero p.val] (Aexp : ℕ → ℕ)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LowTaggedSamplingRank
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedRetained (d : ℕ)
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (h : Fin d) :
    Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :=
  if hm : h.val < m then
    (W ⟨h.val, hm⟩).map (lowTaggedEmbedding J d ⟨h.val, hm⟩ (by exact Nat.succ_le_of_lt h.isLt))
  else ⊥

variable {X : Type*}

noncomputable def lowTaggedTopPolynomial (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    VectorPolynomial X ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :=
  ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
    (fun i => homogeneousComponent (lowTaggedWeight J d i) (lowTaggedPolynomial J d poly i))

theorem lowTaggedTopPolynomial_coeff_apply (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (α : X →₀ ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    coefficients (lowTaggedTopPolynomial J d poly) α i =
      if α.degree = lowTaggedWeight J d i then
        coefficients (poly (lowTaggedIndex J d i).1) α (lowTaggedIndex J d i).2 else 0 := by
  rw [lowTaggedTopPolynomial, coefficients_ofCoordinates_pi_apply,
    coeff_homogeneousComponent, lowTaggedPolynomial_coeff]

theorem lowTaggedTopPolynomial_coeff_of_degree (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (j : Fin m) (hj : j.val + 1 ≤ d) (α : X →₀ ℕ)
    (hα : α.degree = j.val + 1) :
    coefficients (lowTaggedTopPolynomial J d poly) α =
      lowTaggedEmbedding J d j hj (coefficients (poly j) α) := by
  classical
  funext i
  rw [lowTaggedTopPolynomial_coeff_apply]
  by_cases hi : (lowTaggedIndex J d i).1 = j
  · obtain ⟨k, hk⟩ := lowTaggedSlot_eq_of_tag J d j hj i hi
    subst i
    rw [lowTaggedEmbedding_apply_slot]
    simp only [lowTaggedWeight, lowTaggedIndex_slot, hα, ite_true]
    rw [lowTaggedIndex_slot]
  · rw [lowTaggedEmbedding_apply_of_ne J d j hj _ i hi]
    have hne : α.degree ≠ lowTaggedWeight J d i := by
      intro he
      apply hi
      apply Fin.ext
      unfold lowTaggedWeight at he
      omega
    simp only [hne, ite_false]

theorem lowTaggedTopPolynomial_row_layer (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (j : Fin m) (hj : j.val + 1 ≤ d)
    (a : Fin (Fintype.card (LowTaggedIndex J d)) → ℤ) :
    homogeneousComponent (j.val + 1)
        (integerRowPolynomial a (lowTaggedTopPolynomial J d poly)) =
      homogeneousComponent (j.val + 1)
        (integerRowPolynomial (fun k => a (lowTaggedSlot J d j hj k)) (poly j)) := by
  classical
  ext α
  simp only [coeff_homogeneousComponent]
  split
  · rename_i hα
    rw [integerRowPolynomial_coeff, integerRowPolynomial_coeff,
      lowTaggedTopPolynomial_coeff_of_degree J d poly j hj α hα]
    exact lowTaggedEmbedding_pairing J d j hj (fun i => (a i : ℝ)) _
  · rfl

theorem lowTaggedTopPolynomial_hasLayerSamplingRank (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (T : X → ℝ) (R : ℝ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) T R (W j) (poly j))
    (h : Fin d) :
    HasLayerSamplingRank (h.val + 1) T R (lowTaggedRetained J d W h)
      (lowTaggedTopPolynomial J d poly) := by
  classical
  intro a ha hw
  by_cases hm : h.val < m
  · let j : Fin m := ⟨h.val, hm⟩
    have hj : j.val + 1 ≤ d := by dsimp [j]; omega
    obtain ⟨w, hw⟩ := hw
    have hwmem : w.val ∈ (W j).map (lowTaggedEmbedding J d j hj) := by
      simpa only [lowTaggedRetained, dif_pos hm] using w.property
    obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp hwmem
    have hpair : ∃ v : W j,
        (∑ k, (a (lowTaggedSlot J d j hj k) : ℝ) * v.val k) ≠ 0 := by
      refine ⟨⟨v, hv⟩, ?_⟩
      change (∑ k, (a (lowTaggedSlot J d j hj k) : ℝ) * v k) ≠ 0
      rw [← lowTaggedEmbedding_pairing J d j hj (fun i => (a i : ℝ)) v, he]
      exact hw
    have hn := hrank j (fun k => a (lowTaggedSlot J d j hj k))
      (fun k => ha _) hpair
    rw [lowTaggedTopPolynomial_row_layer J d poly j hj]
    exact hn
  · obtain ⟨w, hw⟩ := hw
    have hwzero : w.val = 0 := by
      have := w.property
      simpa only [lowTaggedRetained, dif_neg hm, Submodule.mem_bot] using this
    simp only [hwzero, Pi.zero_apply, mul_zero, Finset.sum_const_zero, ne_eq,
      not_true_eq_false] at hw

theorem lowTaggedTopPolynomial_coeff_mem_iSup (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (W : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (α : X →₀ ℕ) :
    coefficients (lowTaggedTopPolynomial J d poly) α ∈
      ⨆ h : Fin d, lowTaggedRetained J d W h := by
  classical
  by_cases hs : ∃ i, α.degree = lowTaggedWeight J d i
  · obtain ⟨i, hi⟩ := hs
    let j := (lowTaggedIndex J d i).1
    have hj : j.val + 1 ≤ d := lowTaggedIndex_property J d i
    let h : Fin d := ⟨j.val, by omega⟩
    have hα : α.degree = j.val + 1 := hi
    have hα0 : α ≠ 0 := by
      intro he
      subst α
      simp at hα
    apply Submodule.mem_iSup_of_mem h
    rw [lowTaggedTopPolynomial_coeff_of_degree J d poly j hj α hα]
    have heq : lowTaggedRetained J d W h =
        (W j).map (lowTaggedEmbedding J d j hj) := by
      simp only [lowTaggedRetained, h, dif_pos j.isLt]
    rw [heq]
    exact Submodule.mem_map.mpr ⟨_, hcoeff j α hα0, rfl⟩
  · have hz : coefficients (lowTaggedTopPolynomial J d poly) α = 0 := by
      funext i
      rw [lowTaggedTopPolynomial_coeff_apply]
      simp only [show α.degree ≠ lowTaggedWeight J d i from fun he => hs ⟨i, he⟩,
        ite_false, Pi.zero_apply]
    rw [hz]
    exact Submodule.zero_mem _

end Erdos3.VectorPolynomial

end

end OAI

end


