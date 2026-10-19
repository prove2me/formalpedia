-- Prove2me | Definitions.Def_OAIE3v2B050
-- name    : OAIE3v2B050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:13:34.952386+00:00
-- url     : https://prove2.me/theorems/22b99ae1-ffe1-4c57-bf23-03e462b3b59a
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 51 of 311
-- statement:
--   Definitions bundle 51 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B005`, `OAIE3v2B006`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B013`, `OAIE3v2B015`, `OAIE3v2B016`, `OAIE3v2B017`, `OAIE3v2B018` of this split.
--
--   Modules: `Dynamics/CandidateFrontSourceLossBudget.lean`, `Dynamics/ComparisonEquivalenceBudget.lean`, `Dynamics/FrozenCorrelationBudget.lean`, `Dynamics/NativeParameterCoverBudget.lean`, `Dynamics/RationalConstraintCountBudget.lean`, `Dynamics/RationalLieQuotientBudget.lean`, `Dynamics/VerticalDecompositionBudget.lean`, `Estimates/AmbientImageExtension.lean`, `Estimates/CommonIntegralModelEquivalences.lean`, `Estimates/CommonNativeSquareFactors.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/FiniteSeriesCoefficientBounds.lean`, `Estimates/ImageRepresentatives.lean`, `Estimates/InteriorIntervalCutoff.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/NativeCrossFactorization.lean`, `Estimates/PowerSubgroup.lean`, `Estimates/RationalImageIntersections.lean`, `Estimates/RationalLieSubalgebra.lean`, `Estimates/RationalRowReduction.lean`, `Estimates/SharedFreeRoundingThreshold.lean`, `Estimates/SymbolAbsorptionBounds.lean`, `Fourier/NiltestConjugateFrequency.lean`, `Fourier/VerticalFrequencyIdentification.lean`, `Geometry/BoxOverlapSize.lean`, `Geometry/ConjugationCoordinates.lean`, `Geometry/CoordinateSupNorm.lean`, `Geometry/LieStructureTransport.lean`, `Geometry/MultidegreeCoordinateFreezing.lean`, `Geometry/QuantitativeMetricPartition.lean`, `Geometry/RightCosetMetricMap.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Geometry/SupportedLieQuotient.lean`, `Geometry/UnitIntervalBox.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Linear/BoundedAdaptedBasis.lean`, `Linear/FurstenbergWeissProjection.lean`, `Linear/NativeRankQuotientOrbit.lean`, `Linear/RankIntervalFactorization.lean`, `Linear/RankQuotientHeightBudget.lean`, `Linear/RefiltrationLayerBasis.lean`, `Linear/SharedFreeComparisonBasis.lean`, `Linear/WeightedFlagBasis.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Nilpotent/BCHOuterGridChangeBasis.lean`, `Nilpotent/BCHUniformQuotientCharts.lean`, `Nilpotent/LieBCHContinuity.lean`, `Nilpotent/NiltestVerticalBounds.lean`, `Nilpotent/RankBracketFactorizationMonotone.lean`, `Nilpotent/RationalBCHProducts.lean`, `Nilpotent/RealPolynomialBCH.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Polynomial/PolynomialIntegerInputs.lean`, `Polynomial/PolynomialKernelValues.lean`, `Polynomial/RationalPolynomialGrid.lean`, `Polynomial/VectorPolynomialReconstruction.lean`, `Sampling/NormalizedRealBoxHalfGrid.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B005
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B013
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B016
import Definitions.Def_OAIE3v2B017
import Definitions.Def_OAIE3v2B018

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateFrontSourceLossBudget
namespace OAI

section

namespace Erdos3

theorem polynomial_budget_comp {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (a b : ℕ) (hpq : q ≤ (p + 2) ^ a) (hqr : r ≤ (q + 2) ^ b) :
    r ≤ (p + 2) ^ ((a + 2) * b) := by
  calc
    r ≤ (q + 2) ^ b := hqr
    _ ≤ ((p + 2) ^ a + 2) ^ b := by gcongr
    _ ≤ _ := shifted_power_budget_le hp a b

theorem exponential_budget_comp {p q h : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (a b : ℕ) (hpq : q ≤ (p + 2) ^ a) (hh : h ≤ Real.exp ((q + 2) ^ b)) :
    h ≤ Real.exp ((p + 2) ^ ((a + 2) * b)) := by
  exact hh.trans (Real.exp_le_exp.mpr (polynomial_budget_comp hp hq a b hpq le_rfl))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NormalizedRealBoxHalfGrid
namespace OAI

section

namespace Erdos3

theorem uniformIntervalGrid_mem {B : ℝ} (hB : 0 ≤ B) {N : ℕ} (hN : 0 < N)
    (k : Fin (N + 1)) : |uniformIntervalGrid B N k| ≤ B := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (k : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ k.isLt
  have hstep : 0 ≤ 2 * B / N := by positivity
  have htop : (2 * B / N) * N = 2 * B := div_mul_cancel₀ _ hNr.ne'
  have hle := mul_le_mul_of_nonneg_left hk hstep
  apply abs_le.mpr
  dsimp [uniformIntervalGrid]
  constructor
  · have := mul_nonneg hstep (Nat.cast_nonneg k.val)
    linarith
  · linarith

theorem exists_uniformIntervalGrid_approx {B : ℝ} (hB : 0 < B) {N : ℕ} (hN : 0 < N)
    (x : ℝ) (hx : |x| ≤ B) :
    ∃ k : Fin (N + 1), |x - uniformIntervalGrid B N k| ≤ 2 * B / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let δ : ℝ := 2 * B / N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδN : δ * N = 2 * B := div_mul_cancel₀ _ hNr.ne'
  let q : ℝ := (x + B) / δ
  have hq0 : 0 ≤ q := div_nonneg (by linarith [(abs_le.mp hx).1]) hδ.le
  have hqN : q ≤ N := by
    apply (div_le_iff₀ hδ).mpr
    linarith [(abs_le.mp hx).2]
  let k : Fin (N + 1) := ⟨⌊q⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le hqN)⟩
  refine ⟨k, ?_⟩
  have hq : δ * q = x + B := by dsimp [q]; field_simp
  have heq : x - uniformIntervalGrid B N k = δ * (q - ⌊q⌋₊) := by
    change x - (-B + δ * (⌊q⌋₊ : ℝ)) = _
    rw [mul_sub, hq]
    ring
  rw [heq, abs_mul, abs_of_pos hδ]
  exact (mul_le_mul_of_nonneg_left (Nat.abs_sub_floor_le hq0) hδ.le).trans_eq (mul_one δ)

noncomputable def uniformBoxGrid {ι : Type*} (B : ℝ) (N : ℕ) (k : ι → Fin (N + 1)) : ι → ℝ :=
  fun i => uniformIntervalGrid B N (k i)

theorem uniformBoxGrid_mem {ι : Type*} {B : ℝ} (hB : 0 ≤ B) {N : ℕ} (hN : 0 < N)
    (k : ι → Fin (N + 1)) (i : ι) : |uniformBoxGrid B N k i| ≤ B :=
  uniformIntervalGrid_mem hB hN (k i)

theorem exists_uniformBoxGrid_approx {ι : Type*} [Fintype ι] {B : ℝ} (hB : 0 < B)
    {N : ℕ} (hN : 0 < N) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ B) :
    ∃ k : ι → Fin (N + 1), dist v (uniformBoxGrid B N k) ≤ 2 * B / N := by
  classical
  choose k hk using fun i => exists_uniformIntervalGrid_approx hB hN (v i) (hv i)
  refine ⟨k, ?_⟩
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 2 * B / N)).mpr
  intro i
  simpa only [Real.dist_eq, uniformBoxGrid] using hk i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuantitativeMetricPartition
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]

theorem boxCoverMeshCount_pos (B : ℝ) (K : ℝ≥0) (ε : ℝ) : 0 < boxCoverMeshCount B K ε := by
  unfold boxCoverMeshCount
  omega

theorem boxCoverMeshCount_error {B ε : ℝ} (K : ℝ≥0) (hε : 0 < ε) :
    K * (2 * B / boxCoverMeshCount B K ε) ≤ ε := by
  have hN : (0 : ℝ) < boxCoverMeshCount B K ε := by exact_mod_cast boxCoverMeshCount_pos B K ε
  have hceil : 2 * B * K / ε ≤ (boxCoverMeshCount B K ε : ℝ) := by
    exact (Nat.le_ceil _).trans (by unfold boxCoverMeshCount; push_cast; linarith)
  have hm := (div_le_iff₀ hε).mp hceil
  rw [← mul_div_assoc, div_le_iff₀ hN]
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

theorem metricTent_zero_of_far (c x : X) {r : ℝ} (hx : 2 * r ≤ dist x c) : metricTent c r x = 0 := by
  exact max_eq_left (by linarith)

variable {ι : Type*} [Fintype ι]

theorem metricTentSum_ge (c : ι → X) {r : ℝ} (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (x : X) :
    r ≤ metricTentSum c r x := by
  obtain ⟨i, hi⟩ := hcover x
  calc
    r ≤ metricTent (c i) r x := (by linarith : r ≤ 2 * r - dist x (c i)).trans (le_max_right _ _)
    _ ≤ metricTentSum c r x := Finset.single_le_sum (fun j _ => metricTent_nonneg (c j) r x) (Finset.mem_univ i)

noncomputable def metricTentPartition (c : ι → X) (r : ℝ) (i : ι) (x : X) : ℝ :=
  metricTent (c i) r x / metricTentSum c r x

theorem metricTentPartition_nonneg (c : ι → X) (r : ℝ) (i : ι) (x : X) :
    0 ≤ metricTentPartition c r i x :=
  div_nonneg (metricTent_nonneg _ _ _) (Finset.sum_nonneg fun j _ => metricTent_nonneg (c j) r x)

theorem sum_metricTentPartition (c : ι → X) {r : ℝ} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (x : X) : ∑ i, metricTentPartition c r i x = 1 := by
  simp only [metricTentPartition, ← Finset.sum_div]
  exact div_self (hr.trans_le (metricTentSum_ge c hcover x)).ne'

theorem metricTentPartition_le_one (c : ι → X) {r : ℝ} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (i : ι) (x : X) : metricTentPartition c r i x ≤ 1 := by
  rw [← sum_metricTentPartition c hr hcover x]
  exact Finset.single_le_sum (fun j _ => metricTentPartition_nonneg c r j x) (Finset.mem_univ i)

theorem metricTentPartition_zero_of_far (c : ι → X) (r : ℝ) (i : ι) (x : X)
    (hx : 2 * r ≤ dist x (c i)) : metricTentPartition c r i x = 0 := by
  simp only [metricTentPartition, metricTent_zero_of_far (c i) x hx, zero_div]

theorem abs_metricTentPartition_sub_le (c : ι → X) {r : ℝ} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (i : ι) (x y : X) :
    |metricTentPartition c r i x - metricTentPartition c r i y| ≤
      ((2 * Fintype.card ι + 1) / r) * dist x y := by
  have h := abs_div_sub_div_bound hr (metricTentSum_ge c hcover x) (metricTentSum_ge c hcover y)
    dist_nonneg (by positivity : 0 ≤ 2 * r) (by positivity : 0 ≤ (Fintype.card ι : ℝ) * dist x y)
    (abs_metricTent_sub_le (c i) r x y)
    (by simpa only [abs_of_nonneg (metricTent_nonneg _ _ _)] using metricTent_le (c i) hr.le y)
    (abs_metricTentSum_sub_le c r x y)
  apply h.trans_eq
  field_simp
  ring

theorem lipschitz_metricTentPartition (c : ι → X) {r : ℝ≥0} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (i : ι) :
    LipschitzWith ((2 * Fintype.card ι + 1) / r) (metricTentPartition c r i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_one,
    NNReal.coe_ofNat] using abs_metricTentPartition_sub_le c (show (0 : ℝ) < r from hr) hcover i x y

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem boxCoverMeshCount_add_one_le_exp {B ε p : ℝ} (K : ℝ≥0)
    (hB0 : 0 ≤ B) (hε : 0 < ε) (hp : 0 ≤ p)
    (hB : B ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) (hεinv : 1 / ε ≤ Real.exp p) :
    ((boxCoverMeshCount B K ε + 1 : ℕ) : ℝ) ≤ Real.exp (3 * p + 4) := by
  have hprod : 2 * B * K / ε ≤ 2 * Real.exp (3 * p) := by
    calc
      _ = 2 * (B * K * (1 / ε)) := by ring
      _ ≤ 2 * (Real.exp p * Real.exp p * Real.exp p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * B * K / ε)).le
  have hone : 1 ≤ Real.exp (3 * p) := Real.one_le_exp (by linarith)
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 5 * Real.exp (3 * p) := by
      unfold boxCoverMeshCount
      push_cast
      linarith
    _ ≤ Real.exp 4 * Real.exp (3 * p) := mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RightCosetMetricMap
namespace OAI

section

namespace Erdos3

open _root_.Set

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

theorem rightCosetMetricSpace_lipschitz_mk (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) :
    letI := rightCosetMetricSpace Γ hΓ
    LipschitzWith 1 (QuotientGroup.mk : G → G ⧸ Γ) := by
  let := rightCosetMetricSpace Γ hΓ
  intro x y
  change quotientRightEDist Γ (QuotientGroup.mk x) (QuotientGroup.mk y) ≤ 1 * edist x y
  simpa only [one_mul] using quotientRightEDist_mk_le Γ x y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AmbientImageExtension
namespace OAI

section

namespace Erdos3

open _root_.Set

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G]
  [IsTopologicalGroup G]

theorem rightCosetMetricSpace_image_ball (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (g : G) (r : ℝ) :
    letI := rightCosetMetricSpace Γ hΓ
    (QuotientGroup.mk : G → G ⧸ Γ) '' Metric.ball g r =
      Metric.ball (QuotientGroup.mk g) r := by
  let := rightCosetMetricSpace Γ hΓ
  have h := quotientRightEDist_image_eball Γ g (ENNReal.ofReal r)
  change (QuotientGroup.mk : G → G ⧸ Γ) '' Metric.eball g (ENNReal.ofReal r) =
    {y | edist (QuotientGroup.mk g : G ⧸ Γ) y < ENNReal.ofReal r} at h
  have h' : (QuotientGroup.mk : G → G ⧸ Γ) '' Metric.eball g (ENNReal.ofReal r) =
      Metric.eball (QuotientGroup.mk g) (ENNReal.ofReal r) := h.trans (by
    ext y
    simp only [mem_ofPred_eq, Metric.mem_eball, edist_comm])
  simpa only [Metric.eball_ofReal] using h'

theorem rightCosetMetricSpace_exists_lift (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (g : G) (r : ℝ) :
    letI := rightCosetMetricSpace Γ hΓ
    ∀ x : G ⧸ Γ, dist x (QuotientGroup.mk g) < r →
      ∃ h : G, dist h g < r ∧ (QuotientGroup.mk h : G ⧸ Γ) = x := by
  let := rightCosetMetricSpace Γ hΓ
  intro x hx
  have hx' : x ∈ Metric.ball (QuotientGroup.mk g : G ⧸ Γ) r := hx
  rw [← rightCosetMetricSpace_image_ball Γ hΓ g r] at hx'
  exact hx'

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {H G E : Type*} [Group H] [Group G] [MetricSpace H] [MetricSpace G]
  [IsIsometricSMul Hᵐᵒᵖ H] [IsIsometricSMul Gᵐᵒᵖ G]
  [IsTopologicalGroup H] [IsTopologicalGroup G] [NormedAddCommGroup E]

omit [IsTopologicalGroup H] in

theorem quotient_local_lifts_of_identity_lifts (φ : H →* G)
    (hφ : Function.Surjective φ) (Λ : Subgroup G) (hΛ : IsClosed (Λ : Set G))
    (K δ : ℝ≥0) (_hδ : 0 < δ)
    (hlift : ∀ g : G, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∀ y z : G ⧸ Λ, dist y z < δ / 2 →
      ∃ x x' : H, (QuotientGroup.mk (φ x) : G ⧸ Λ) = y ∧
        (QuotientGroup.mk (φ x') : G ⧸ Λ) = z ∧ dist x x' ≤ (2 * K) * dist y z := by
  let := rightCosetMetricSpace Λ hΛ
  intro y z hyz
  have hπ : Function.Surjective (fun x : H => (QuotientGroup.mk (φ x) : G ⧸ Λ)) :=
    QuotientGroup.mk_surjective.comp hφ
  obtain ⟨x, hx⟩ := hπ y
  change (QuotientGroup.mk (φ x) : G ⧸ Λ) = y at hx
  by_cases heq : y = z
  · refine ⟨x, x, hx, hx.trans heq, ?_⟩
    simp only [dist_self, heq, mul_zero, le_refl]
  have hd : 0 < dist y z := dist_pos.mpr heq
  obtain ⟨b, hb, hbq⟩ := rightCosetMetricSpace_exists_lift Λ hΛ (φ x) (2 * dist y z) z (by
    rw [hx, dist_comm]
    linarith)
  let g := b * (φ x)⁻¹
  have hgdist : dist 1 g = dist b (φ x) := by
    simpa only [g, mul_inv_cancel, dist_comm] using
      (dist_mul_right (φ x) b (φ x)⁻¹)
  have hgnear : dist 1 g < δ := by rw [hgdist]; linarith
  obtain ⟨u, hu, hudist⟩ := hlift g hgnear
  refine ⟨x, u * x, hx, ?_, ?_⟩
  · rw [map_mul, hu]
    simpa only [g, inv_mul_cancel_right] using hbq
  · have hdist : dist x (u * x) = dist 1 u := by
      simpa only [one_mul] using dist_mul_right (1 : H) u x
    rw [hdist]
    calc
      dist 1 u ≤ (K : ℝ) * dist 1 g := hudist
      _ ≤ K * (2 * dist y z) := mul_le_mul_of_nonneg_left (by rw [hgdist]; exact hb.le) K.coe_nonneg
      _ = (2 * K) * dist y z := by ring

theorem exists_lipschitz_observable_reconstruction (φ : H →* G)
    (hφ : Function.Surjective φ) (Γ : Subgroup H) (Λ : Subgroup G)
    (hΓ : IsClosed (Γ : Set H)) (hΛ : IsClosed (Λ : Set G))
    (hcover : Λ ≤ Γ.map φ) (f : H ⧸ Γ → E)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (QuotientGroup.mk (k * x)) = f (QuotientGroup.mk x))
    (L K B δ : ℝ≥0) (hδ : 0 < δ)
    (hf : letI := rightCosetMetricSpace Γ hΓ; LipschitzWith L f)
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlift : ∀ g : G, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∃ F : G ⧸ Λ → E,
      (∀ x, F (QuotientGroup.mk (φ x)) = f (QuotientGroup.mk x)) ∧
      LipschitzWith (max (L * (2 * K)) (2 * B / (δ / 2))) F ∧ ∀ y, ‖F y‖ ≤ B := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  obtain ⟨F, hF, _⟩ := exists_unique_observable_reconstruction φ hφ Γ Λ hcover f hker
  let π : H → G ⧸ Λ := fun x => QuotientGroup.mk (φ x)
  have hπ : Function.Surjective π := QuotientGroup.mk_surjective.comp hφ
  have hf' : LipschitzWith L (fun x : H => f (QuotientGroup.mk x)) := by
    simpa only [mul_one, Function.comp_def] using hf.comp (rightCosetMetricSpace_lipschitz_mk Γ hΓ)
  refine ⟨F, hF, ?_, reconstruction_norm_le π hπ _ F hF (fun x => hbound _)⟩
  apply lipschitz_reconstruction_of_local_lifts π hπ _ F hF L (2 * K) B (δ / 2)
    (by positivity) hf' (fun x => hbound _)
  exact quotient_local_lifts_of_identity_lifts φ hφ Λ hΛ K δ hδ hlift

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateSupNorm
namespace OAI

section

namespace Erdos3

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem coordinateL2Norm_le_card_bound (v : ι → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ i, |v i| ≤ B) : coordinateL2Norm v ≤ (Fintype.card ι + 1) * B := by
  unfold coordinateL2Norm
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hsum : (∑ i, v i ^ 2) ≤ (Fintype.card ι : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _i : ι, B ^ 2 := Finset.sum_le_sum fun i _ =>
        sq_le_sq.mpr ((hv i).trans_eq (abs_of_nonneg hB).symm)
      _ = _ := by simp
  apply hsum.trans
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg B)
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι), sq_nonneg (Fintype.card ι : ℝ)]

end Erdos3

end

section

namespace Erdos3

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem coordinateLinearMap_L2_bound (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (B : ℝ)
    (hB : 0 ≤ B) (hA : ∀ k i, |A (Pi.single i 1) k| ≤ B) (v : ι → ℝ) :
    coordinateL2Norm (A v) ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * (B + 1) * coordinateL2Norm v := by
  have heq : A v = fun k => ∑ i, A (Pi.single i 1) k * v i :=
    funext (coordinateLinearMap_apply_sum A v)
  rw [heq]
  exact coordinateL2Norm_matrix_entry_bound (fun k i => A (Pi.single i 1) k) B hB hA v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
namespace OAI

section

namespace Erdos3

variable (A : Type*) [Ring A] [Algebra ℚ A]

namespace NilpotentAlgebraFiltration
variable {A} {s : ℕ} (F : NilpotentAlgebraFiltration A s)

theorem exp_sub_one_mem_layer {i : ℕ} {a : A} (ha : a ∈ F.layer i)
    (hna : IsNilpotent a) : IsNilpotent.exp a - 1 ∈ F.layer i :=
  exp_sub_one_mem (F.layerAlgebra i) ha hna

end NilpotentAlgebraFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem monomialScale_add {σ : Type*} (T : σ → ℝ) (α β : σ →₀ ℕ) :
    monomialScale T (α + β) = monomialScale T α * monomialScale T β := by
  classical
  exact Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {σ ι R S V : Type*} [CommRing R] [CommRing S] [AddCommGroup V] [Module R V]

theorem degreeLE_iff_coordinates (w : σ → ℕ) (d : ℕ)
    (f : ι → V →+ S) (hsep : ∀ v, (∀ i, f i v = 0) → v = 0)
    (p : VectorPolynomial σ R V) :
    DegreeLE w d p ↔ ∀ i, (coordinate (f i) p).weightedTotalDegree w ≤ d := by
  simp only [scalar_weightedDegree_le_iff, coeff_coordinate]
  constructor
  · intro hp i α hα
    rw [hp α hα, map_zero]
  · intro hp α hα
    exact hsep _ (fun i => hp i α hα)

theorem degreeLE_iff_basis_coordinates [Module S V]
    (e : Module.Basis ι S V) (w : σ → ℕ) (d : ℕ) (p : VectorPolynomial σ R V) :
    DegreeLE w d p ↔
      ∀ i, (coordinate (e.coord i).toAddMonoidHom p).weightedTotalDegree w ≤ d := by
  apply degreeLE_iff_coordinates
  intro v hv
  apply e.repr.injective
  ext i
  have hi : (e.coord i) v = 0 := hv i
  simpa only [map_zero, Finsupp.zero_apply, Module.Basis.coord_apply] using hi

theorem degreeLE_one_iff_basis_totalDegree [Module S V]
    (e : Module.Basis ι S V) (d : ℕ) (p : VectorPolynomial σ R V) :
    DegreeLE (1 : σ → ℕ) d p ↔
      ∀ i, (coordinate (e.coord i).toAddMonoidHom p).totalDegree ≤ d := by
  simpa only [MvPolynomial.weightedTotalDegree_one] using
    degreeLE_iff_basis_coordinates e (1 : σ → ℕ) d p

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

noncomputable def scalarTaylorRemainder (h : σ → ℚ) :
    MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ :=
  (polynomialTranslate h).toLinearMap - LinearMap.id - (scalarDirectionalDerivative h).toLinearMap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalRowReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem rational_sum_exp_height {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℚ) {H : ℕ} (hq : ∀ i, RationalHeightLE (q i) H)
    {p : ℝ} (hp : 0 ≤ p) (a c : ℕ)
    (hH : (H : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hcard : (Fintype.card ι : ℝ) ≤ (p + 2) ^ c) :
    ((∑ i, q i).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ (a + c + 1)) ∧
      ((∑ i, q i).den : ℝ) ≤ Real.exp ((p + 2) ^ (a + c + 1)) := by
  have hheight := rationalHeightLE_sum q hq
  have hcost := rational_sum_cost_le_exp (Fintype.card ι) H hp a c hH hcard
  constructor
  · exact (show ((∑ i, q i).num.natAbs : ℝ) ≤ ((Fintype.card ι + 1) * H ^ Fintype.card ι : ℕ) from
      by exact_mod_cast hheight.1).trans hcost
  · exact (show ((∑ i, q i).den : ℝ) ≤ ((Fintype.card ι + 1) * H ^ Fintype.card ι : ℕ) from
      by exact_mod_cast hheight.2).trans hcost

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalImageIntersections
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in

theorem kernel_equations_of_transpose_kernel (A : Matrix ι κ ℚ)
    (v : Fin (Module.finrank ℚ (LinearMap.ker Aᵀ.mulVecLin)) → (ι → ℚ))
    (hli : LinearIndependent ℚ v)
    (hspan : Submodule.span ℚ (Set.range v) = LinearMap.ker Aᵀ.mulVecLin) :
    Function.Surjective (Matrix.mulVec v) ∧
      LinearMap.ker (Matrix.mulVecLin v) = LinearMap.range A.mulVecLin := by
  let D : Matrix (Fin (Module.finrank ℚ (LinearMap.ker Aᵀ.mulVecLin))) ι ℚ := v
  have hrows : LinearIndependent ℚ D.row := hli
  have hDA : D * A = 0 := by
    ext i j
    have hi : v i ∈ LinearMap.ker Aᵀ.mulVecLin := by
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hj := congrFun hi j
    change (∑ k, A k j * v i k) = 0 at hj
    change (∑ k, v i k * A k j) = 0
    simpa only [mul_comm] using hj
  have hle : LinearMap.range A.mulVecLin ≤ LinearMap.ker D.mulVecLin := by
    rintro y ⟨x, rfl⟩
    change D *ᵥ (A *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, hDA, Matrix.zero_mulVec]
  have hdimD := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  have hdimA := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
  change D.rank + Module.finrank ℚ (LinearMap.ker D.mulVecLin) =
    Module.finrank ℚ (ι → ℚ) at hdimD
  change Aᵀ.rank + Module.finrank ℚ (LinearMap.ker Aᵀ.mulVecLin) =
    Module.finrank ℚ (ι → ℚ) at hdimA
  rw [hrows.rank_matrix, Fintype.card_fin] at hdimD
  rw [Matrix.rank_transpose] at hdimA
  have heq : Module.finrank ℚ (LinearMap.range A.mulVecLin) =
      Module.finrank ℚ (LinearMap.ker D.mulVecLin) := by
    change A.rank = _
    omega
  exact ⟨mulVec_surjective_of_independent_rows D hrows,
    (Submodule.eq_of_le_of_finrank_eq hle heq).symm⟩

theorem rationalKernelHeight_pos (t : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    0 < rationalKernelHeight t H := by
  have hsolve := rationalSolveHeight_pos t hH
  have hHpos : 0 < H := Nat.zero_lt_one.trans_le hH
  unfold rationalKernelHeight
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]

theorem spanningCoordinateMatrix_mulVec (e : Basis ι ℚ V) (v : κ → V) (t : κ → ℚ) :
    e.equivFun (∑ j, t j • v j) = spanningCoordinateMatrix e v *ᵥ t := by
  ext i
  simp [spanningCoordinateMatrix, Matrix.mulVec, dotProduct, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialIntegerInputs
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem product_scaled_powers [Fintype σ] (x : σ → ℚ) (q : ℚ) (m : σ →₀ ℕ) :
    (∏ i, (q * x i) ^ m i) = q ^ m.sum (fun _ n => n) * ∏ i, x i ^ m i := by
  classical
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem monomialScale_mul_normalized_prod {σ : Type*} [Fintype σ]
    (T v : σ → ℝ) (hT : ∀ i, 0 < T i) (α : σ →₀ ℕ) :
    monomialScale T α * (∏ i, (v i / T i) ^ α i) = ∏ i, v i ^ α i := by
  classical
  rw [monomialScale, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← mul_pow, mul_div_cancel₀ _ (hT i).ne']

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem integer_difference_mem_grid {σ : Type*} (x y : σ → ℤ) (M : ℕ)
    (hxy : ∀ i, (M : ℤ) ∣ x i - y i) :
    (fun i => (x i : ℚ)) - (fun i => (y i : ℚ)) ∈ scaledIntegerGrid M := by
  classical
  choose z hz using hxy
  refine ⟨z, ?_⟩
  funext i
  have hi := congrArg (fun a : ℤ => (a : ℚ)) (hz i)
  push_cast at hi
  exact hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieStructureTransport
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem basisMatrix_surjective (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ[ℚ] L)
    (hφ : Function.Surjective φ) : Function.Surjective (LinearMap.toMatrix b e φ).mulVec := by
  intro y
  obtain ⟨x, hx⟩ := hφ (e.equivFun.symm y)
  refine ⟨b.equivFun x, ?_⟩
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply, hx, LinearEquiv.apply_symm_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RationalPolynomialGrid
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem pairInput_mem_denominatorGrid {ι : Type*} (a b : ι → ℚ) (q : ℕ)
    (ha : a ∈ denominatorGrid q) (hb : b ∈ denominatorGrid q) :
    (fun xi : Fin 2 × ι => (![a, b] xi.1) xi.2) ∈ denominatorGrid q := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  refine ⟨fun xi => (![u, v] xi.1) xi.2, ?_⟩
  rintro ⟨i, j⟩
  fin_cases i
  · exact hu j
  · exact hv j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3

variable {X A : Type*} [Ring A] [Algebra ℚ A]
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def bchProductPolynomial (s : ℕ) (xs : List X) : FreeAlgebra ℚ X :=
  finiteLog (s + 1)
    ((xs.map (fun x => finiteExp (s + 1) (FreeAlgebra.ι ℚ x))).prod - 1)

theorem bchProductPolynomial_eval (s : ℕ) (f : X → A) (xs : List X) :
    FreeAlgebra.lift ℚ f (bchProductPolynomial s xs) =
      finiteLog (s + 1) ((xs.map (fun x => finiteExp (s + 1) (f x))).prod - 1) := by
  simp only [bchProductPolynomial, map_finiteLog, map_sub, map_one,
    map_list_prod, List.map_map, Function.comp_def, map_finiteExp, FreeAlgebra.lift_ι_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalLieSubalgebra
namespace OAI

section

namespace Erdos3

open Module

variable {ι η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem exists_bounded_lie_subalgebra_basis (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L)
    (v : η → K) (hspan : Submodule.span ℚ (Set.range v) = ⊤) {H : ℕ}
    (hv : ∀ i j, RationalHeightLE (e.repr (v i : L) j) H) :
    ∃ b : Basis (Fin (Module.finrank ℚ K)) ℚ K,
      ∀ i j, RationalHeightLE (e.repr (b i : L) j) H := by
  classical
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan, finrank_top] at hex
  obtain ⟨w, hw, hwspan, hwli⟩ := hex
  refine ⟨Basis.mk hwli (by rw [hwspan]), ?_⟩
  intro i j
  rw [Basis.mk_apply]
  obtain ⟨a, ha⟩ := hw i
  rw [← ha]
  exact hv a j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem mem_cubeDifferenceSupport (Q : Finset A) (h : A) :
    h ∈ cubeDifferenceSupport Q ↔ (derivativeSupport Q h).Nonempty := by
  constructor
  · intro hh
    obtain ⟨⟨x, y⟩, hp, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
    simpa using hy
  · rintro ⟨x, hx⟩
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_image.mpr ⟨(x, x + h), Finset.mem_product.mpr ⟨hx, hxh⟩, by simp⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

namespace Erdos3

theorem mem_cyclicCutNeighborhood (N : ℕ) [NeZero N] (a : ℤ) (δ : ℝ) (x : ZMod N) :
    x ∈ cyclicCutNeighborhood N a δ ↔ |(x.val : ℝ) - a| ≤ δ := by
  classical
  simp only [cyclicCutNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and]

theorem cyclicCutNeighborhood_card_le (N : ℕ) [NeZero N] (a : ℤ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((cyclicCutNeighborhood N a δ).card : ℝ) ≤ 2 * δ + 1 := by
  have hcard : (cyclicCutNeighborhood N a δ).card ≤ (integerAbsInterval δ).card := by
    apply Finset.card_le_card_of_injOn (fun x : ZMod N => (x.val : ℤ) - a)
    · intro x hx
      change (x.val : ℤ) - a ∈ integerAbsInterval δ
      rw [mem_integerAbsInterval]
      simpa only [Int.cast_sub, Int.cast_natCast] using (mem_cyclicCutNeighborhood N a δ x).mp hx
    · intro x _ y _ hxy
      apply ZMod.val_injective N
      have hv : (x.val : ℤ) = (y.val : ℤ) := by dsimp only at hxy; omega
      exact_mod_cast hv
  exact (Nat.cast_le.mpr hcard).trans (integerAbsInterval_card_le δ hδ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem derivativeSupport_translatedIntegerBox (a : ι → ℤ) (T : ι → ℕ) (h : ι → ℤ) :
    derivativeSupport (translatedIntegerBox a T) h =
      translatedIntegerBox (fun i => a i + max 0 (-h i)) (fun i => ((T i : ℤ) - |h i|).toNat) := by
  ext x
  simp only [derivativeSupport, Finset.mem_filter, mem_translatedIntegerBox, Pi.add_apply,
    ← forall_and]
  apply forall_congr'
  intro i
  by_cases hi : 0 ≤ h i
  · rw [abs_of_nonneg hi, max_eq_left (by omega : -h i ≤ 0)]
    omega
  · rw [abs_of_neg (by omega : h i < 0), max_eq_right (by omega : 0 ≤ -h i)]
    omega

theorem box_overlap_length_pos (a : ι → ℤ) (T : ι → ℕ) {h : ι → ℤ}
    (hh : h ∈ cubeDifferenceSupport (translatedIntegerBox a T)) (i : ι) :
    0 < ((T i : ℤ) - |h i|).toNat := by
  obtain ⟨x, hx⟩ := (mem_cubeDifferenceSupport _ h).mp hh
  obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
  have hx' := (mem_translatedIntegerBox a T x).mp hx i
  have hxh' := (mem_translatedIntegerBox a T (x + h)).mp hxh i
  simp only [Pi.add_apply] at hxh'
  by_cases hi : 0 ≤ h i
  · rw [abs_of_nonneg hi]
    omega
  · rw [abs_of_neg (by omega : h i < 0)]
    omega

theorem box_differenceSupport_subset (a : ι → ℤ) (T : ι → ℕ) :
    cubeDifferenceSupport (translatedIntegerBox a T) ⊆
      translatedIntegerBox (fun i => -(T i : ℤ)) (fun i => 2 * T i) := by
  intro h hh
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
  apply (mem_translatedIntegerBox _ _ _).mpr
  intro i
  have hx' := (mem_translatedIntegerBox a T p.1).mp hx i
  have hy' := (mem_translatedIntegerBox a T p.2).mp hy i
  simp only [Pi.sub_apply, Nat.cast_mul, Nat.cast_ofNat]
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

variable {σ R V : Type*} [Fintype σ]
  [CommRing R] [AddCommGroup V] [Module R V]

theorem eval₂_linearPolynomial {S : Type*} [CommRing S] [Algebra R S]
    [Module S V] [IsScalarTower R S V] (a : σ → V) (t : σ → S) :
    eval₂ t (linearPolynomial (R := R) a) = ∑ i, t i • a i := by
  simp [linearPolynomial_apply, eval₂_monomial]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PowerSubgroup
namespace OAI

section

namespace Erdos3

variable {G : Type*} [Group G]

theorem subgroupPowerCover_le (Γ : Subgroup G) (m : ℕ) : subgroupPowerCover Γ m ≤ Γ := by
  rintro _ ⟨g, _, rfl⟩
  exact g.property

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedFlagBasis
namespace OAI

section

namespace Erdos3

open Module

variable {κ : Type*} {n : ℕ}

theorem exists_sorted_weighted_flag_basis {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (P : Fin n → Submodule K V) (hP : Antitone P) :
    ∃ (e : Basis (Fin (finrank K V)) K V) (w : Fin (finrank K V) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ n) ∧
      ∀ i, P i = Submodule.span K (e '' {j | i.val < w j}) := by
  classical
  obtain ⟨κ, instκ, b, S, hS, hb⟩ := exists_basis_with_nested_supports n P hP
  let : Fintype κ := instκ
  let ρ : κ ≃ Fin (finrank K V) := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  let u : Fin (finrank K V) → ℕ := fun j => nestedSupportWeight S (ρ.symm j)
  let σ := Tuple.sort u
  let e := b.reindex (ρ.trans σ.symm)
  let w : Fin (finrank K V) → ℕ := fun j => u (σ j)
  refine ⟨e, w, Tuple.monotone_sort u, fun j => nestedSupportWeight_le S _, ?_⟩
  intro i
  rw [hb i]
  congr 1
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨σ.symm (ρ k), ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, w, u, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
        (mem_nestedSupport_iff S hS i k).mp hk
    · simp [e, Basis.reindex_apply]
  · rintro ⟨j, hj, rfl⟩
    refine ⟨ρ.symm (σ j), (mem_nestedSupport_iff S hS i _).mpr hj, ?_⟩
    simp [e, Basis.reindex_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BoundedAdaptedBasis
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

theorem basis_mem_tail (e : Basis (Fin d) ℚ L) (j : Fin d) {i : ℕ} (hij : i ≤ j.val) :
    e j ∈ basisTail e i := by
  rw [basisTail_eq_span]
  exact Submodule.subset_span ⟨j, hij, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis
namespace OAI

section

namespace Erdos3

open Module

theorem denominator_grid_smul_mem_scaled {ι : Type*} (l m₀ m : ℕ)
    (hm : l * m₀ ∣ m) {x : ι → ℚ} (hx : x ∈ denominatorGrid l) :
    (m : ℚ) • x ∈ scaledIntegerGrid m₀ := by
  obtain ⟨k, rfl⟩ := hm
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => (k : ℤ) * z i, ?_⟩
  ext i
  have hi := hz i
  change (l : ℚ) * x i = (z i : ℚ) at hi
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  calc
    _ = (m₀ : ℚ) * k * ((l : ℚ) * x i) := by ring
    _ = _ := by rw [hi]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSeriesCoefficientBounds
namespace OAI

section

namespace Erdos3

variable {X : Type*}

def finiteSeriesDenominator (s : ℕ) : ℕ := arrayDenominator (finiteSeriesWeight s)

def finiteSeriesNumerator (s : ℕ) (i : Fin 2 × Fin (s + 1)) : ℤ :=
  clearedArray (finiteSeriesWeight s) i

def finiteSeriesNumeratorBound (s : ℕ) : ℕ :=
  1 + ∑ i, (finiteSeriesNumerator s i).natAbs

theorem finiteSeriesDenominator_pos (s : ℕ) : 0 < finiteSeriesDenominator s :=
  arrayDenominator_pos _

theorem finiteSeriesNumerator_cast (s : ℕ) (i : Fin 2 × Fin (s + 1)) :
    (finiteSeriesNumerator s i : ℚ) = (finiteSeriesDenominator s : ℚ) * finiteSeriesWeight s i :=
  clearedArray_cast _ _

theorem finiteSeriesNumerator_le (s : ℕ) (i : Fin 2 × Fin (s + 1)) :
    (finiteSeriesNumerator s i).natAbs ≤ finiteSeriesNumeratorBound s := by
  have h := Finset.single_le_sum (f := fun j => (finiteSeriesNumerator s j).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact h.trans (Nat.le_add_left _ 1)

def bchProductDenominator (s n : ℕ) : ℕ :=
  finiteSeriesDenominator s * (finiteSeriesDenominator s ^ n) ^ s

def bchProductNumeratorBound (s n : ℕ) : ℕ :=
  (s + 1) * finiteSeriesNumeratorBound s *
    (finiteSeriesDenominator s ^ n + (s + 1) *
      ((((s + 1) * ((s + 1) * finiteSeriesNumeratorBound s)) ^ n) + finiteSeriesDenominator s ^ n)) ^ s

theorem bchProductDenominator_pos (s n : ℕ) : 0 < bchProductDenominator s n := by
  unfold bchProductDenominator
  exact Nat.mul_pos (finiteSeriesDenominator_pos s) (pow_pos (pow_pos (finiteSeriesDenominator_pos s) _) _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
namespace OAI

section

namespace Erdos3

def bchProductCoefficientBase (s : ℕ) : ℕ :=
  2 * s + 4 + finiteSeriesDenominator s +
    (s + 1) * ((s + 1) * finiteSeriesNumeratorBound s) + finiteSeriesNumeratorBound s

def bchProductCoefficientHeight (s n : ℕ) : ℕ :=
  bchProductCoefficientBase s ^ ((s + 2) * (n + 2))

theorem bchProductCoefficientBase_pos (s : ℕ) : 0 < bchProductCoefficientBase s := by
  unfold bchProductCoefficientBase
  omega

theorem bchProductDenominator_le_height (s n : ℕ) :
    bchProductDenominator s n ≤ bchProductCoefficientHeight s n := by
  let B := bchProductCoefficientBase s
  have hB : 1 ≤ B := bchProductCoefficientBase_pos s
  have hD : finiteSeriesDenominator s ≤ B := by dsimp [B, bchProductCoefficientBase]; omega
  unfold bchProductDenominator bchProductCoefficientHeight
  change finiteSeriesDenominator s * (finiteSeriesDenominator s ^ n) ^ s ≤ B ^ ((s + 2) * (n + 2))
  calc
    _ ≤ B * (B ^ n) ^ s := Nat.mul_le_mul hD (Nat.pow_le_pow_left (Nat.pow_le_pow_left hD _) _)
    _ = B ^ (1 + n * s) := by rw [← pow_mul, ← pow_succ']; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right hB (by nlinarith)

theorem bchProductNumeratorBound_le_height (s n : ℕ) :
    bchProductNumeratorBound s n ≤ bchProductCoefficientHeight s n := by
  let B := bchProductCoefficientBase s
  let A := (s + 1) * ((s + 1) * finiteSeriesNumeratorBound s)
  have hB : 1 ≤ B := bchProductCoefficientBase_pos s
  have hD : finiteSeriesDenominator s ≤ B := by dsimp [B, bchProductCoefficientBase]; omega
  have hA : A ≤ B := by dsimp [A, B, bchProductCoefficientBase]; omega
  have hs : s + 1 ≤ B := by dsimp [B, bchProductCoefficientBase]; omega
  have hU : finiteSeriesNumeratorBound s ≤ B := by dsimp [B, bchProductCoefficientBase]; omega
  have hsum : finiteSeriesDenominator s ^ n + (s + 1) * (A ^ n + finiteSeriesDenominator s ^ n) ≤
      B ^ (n + 1) := by
    calc
      _ ≤ B ^ n + (s + 1) * (B ^ n + B ^ n) :=
        Nat.add_le_add (Nat.pow_le_pow_left hD _)
          (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.pow_le_pow_left hA _) (Nat.pow_le_pow_left hD _)))
      _ = (2 * s + 3) * B ^ n := by ring
      _ ≤ B * B ^ n := Nat.mul_le_mul_right _ (by dsimp [B, bchProductCoefficientBase]; omega)
      _ = _ := (pow_succ' B n).symm
  unfold bchProductNumeratorBound bchProductCoefficientHeight
  change (s + 1) * finiteSeriesNumeratorBound s *
    (finiteSeriesDenominator s ^ n + (s + 1) * (A ^ n + finiteSeriesDenominator s ^ n)) ^ s ≤
      B ^ ((s + 2) * (n + 2))
  calc
    _ ≤ (B * B) * (B ^ (n + 1)) ^ s :=
      Nat.mul_le_mul (Nat.mul_le_mul hs hU) (Nat.pow_le_pow_left hsum _)
    _ = B ^ (2 + (n + 1) * s) := by rw [← pow_two, ← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hB (by nlinarith)

end Erdos3

end

section

namespace Erdos3

theorem bchProductCoefficientHeight_le_exp (s n C : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hB : bchProductCoefficientBase s ≤ C) (hs : s + 2 ≤ C) :
    (bchProductCoefficientHeight s n : ℝ) ≤ Real.exp ((p + C) ^ 3) := by
  let t : ℝ := p + C
  have hbase : (bchProductCoefficientBase s : ℝ) ≤ t := by
    have h := (Nat.cast_le (α := ℝ)).mpr hB
    dsimp [t]
    linarith
  have hs' : (s : ℝ) + 2 ≤ t := by
    have h : (s : ℝ) + 2 ≤ C := by exact_mod_cast hs
    dsimp [t]
    linarith
  have hn' : (n : ℝ) + 2 ≤ t := by
    have hC : (2 : ℝ) ≤ C := by exact_mod_cast (show 2 ≤ C by omega)
    dsimp [t]
    linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have he : (bchProductCoefficientBase s : ℝ) ≤ Real.exp (bchProductCoefficientBase s) := by
    have h := Real.add_one_le_exp (bchProductCoefficientBase s)
    linarith
  unfold bchProductCoefficientHeight
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (bchProductCoefficientBase s)) ^ ((s + 2) * (n + 2)) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) he _
    _ = Real.exp ((((s + 2) * (n + 2) : ℕ) : ℝ) * bchProductCoefficientBase s) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (t * t * t) := by
      apply Real.exp_le_exp.mpr
      push_cast
      exact mul_le_mul (mul_le_mul hs' hn' (by positivity) ht) hbase (by positivity) (by positivity)
    _ = _ := by congr 1; dsimp [t]; ring

end Erdos3

end

section

namespace Erdos3

open Module

theorem bch_bounded_product_box_expression_le_exp (s a C n k d : ℕ)
    (hC : 2 ≤ C) (hn : n ≤ k) {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (((s + 1) * (n * d + 1) ^ s : ℕ) : ℝ) * Real.exp ((p + k + C) ^ C) *
      (Real.exp ((p + 2) ^ a)) ^ s ≤
      Real.exp ((p + (C + 3 * (s + k) + a + 10)) ^ (C + 3 * (s + k) + a + 10)) := by
  have hcount : (s + 1) * (n * d + 1) ^ s ≤ (s + k + 1) * (n * d + 1) ^ (s + k) :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  have hcoef : Real.exp ((p + k + C) ^ C) ≤ Real.exp ((p + (s + k) + C) ^ C) := by
    apply Real.exp_le_exp.mpr
    apply pow_le_pow_left₀ (by positivity)
    linarith [Nat.cast_nonneg (α := ℝ) s]
  have hinput : (Real.exp ((p + 2) ^ a)) ^ s ≤ (Real.exp ((p + 2) ^ a)) ^ (s + k) :=
    pow_le_pow_right₀ (Real.one_le_exp (by positivity)) (by omega)
  apply le_trans (mul_le_mul (mul_le_mul (Nat.cast_le.mpr hcount) hcoef
    (by positivity) (by positivity)) hinput (by positivity) (by positivity))
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    bch_box_expression_le_exp (s + k) a C n d hC hp (by omega) hd

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FurstenbergWeissProjection
namespace OAI

section

namespace Erdos3

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem mem_fourCoordinateKernel (S : Finset (Fin 4)) (v : Fin 4 → V) :
    v ∈ fourCoordinateKernel S ↔ ∀ k ∈ S, v k = 0 := by
  simp [fourCoordinateKernel]

theorem mem_fourFirstProjection (J : Submodule ℚ (Fin 4 → V)) (v : V) :
    v ∈ fourFirstProjection J ↔ ∃ w ∈ J, w 0 = v := Iff.rfl

theorem mem_fourSparseFirstProjection (J : Submodule ℚ (Fin 4 → V))
    (S : Finset (Fin 4)) (v : V) :
    v ∈ fourSparseFirstProjection J S ↔ ∃ w ∈ J, w 0 = v ∧ ∀ k ∈ S, w k = 0 := by
  change (∃ w, w ∈ J ⊓ fourCoordinateKernel S ∧ w 0 = v) ↔ _
  constructor
  · rintro ⟨w, ⟨hw, hS⟩, hv⟩
    exact ⟨w, hw, hv, (mem_fourCoordinateKernel S w).mp hS⟩
  · rintro ⟨w, hw, hv, hS⟩
    exact ⟨w, ⟨hw, (mem_fourCoordinateKernel S w).mpr hS⟩, hv⟩

theorem fourSparseFirstProjection_le (J : Submodule ℚ (Fin 4 → V)) (S : Finset (Fin 4)) :
    fourSparseFirstProjection J S ≤ fourFirstProjection J :=
  Submodule.map_mono inf_le_left

theorem fourDependentProjection_le (J : Submodule ℚ (Fin 4 → V)) :
    fourDependentProjection J ≤ fourFirstProjection J :=
  inf_le_left.trans (fourSparseFirstProjection_le J {1, 2})

end Erdos3

end

section

namespace Erdos3

theorem four_sparse_lifts_vanish {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    {M A : Type*} [Zero M] [AddCommGroup A]
    (S : Set I) (B : (∀ i, V i) → M)
    (hzero : ∀ v i, i ∈ S → v i = 0 → B v = 0)
    (η : M → A) (hη : η 0 = 0) (J : ∀ i, Submodule ℚ (Fin 4 → V i))
    (hJ : ∀ v : ∀ i, Fin 4 → V i, (∀ i, v i ∈ J i) →
      η (B (fun i => v i 0)) + η (B (fun i => v i 1)) -
        η (B (fun i => v i 2)) - η (B (fun i => v i 3)) = 0)
    (v : ∀ i, V i) (hv : ∀ i, v i ∈ fourFirstProjection (J i))
    (a b : I) (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hva : v a ∈ fourSparseFirstProjection (J a) {1, 2})
    (hvb : v b ∈ fourSparseFirstProjection (J b) {1, 3}) : η (B v) = 0 := by
  classical
  have hlift (i : I) : ∃ w ∈ J i, w 0 = v i := (mem_fourFirstProjection (J i) (v i)).mp (hv i)
  choose w hwJ hw0 using hlift
  obtain ⟨xa, hxa, hxa0, hxaz⟩ := (mem_fourSparseFirstProjection (J a) {1, 2} (v a)).mp hva
  obtain ⟨xb, hxb, hxb0, hxbz⟩ := (mem_fourSparseFirstProjection (J b) {1, 3} (v b)).mp hvb
  let z : ∀ i, Fin 4 → V i := Function.update (Function.update w a xa) b xb
  have hza : z a = xa := by simp [z, hab]
  have hzb : z b = xb := by simp [z]
  have hzJ (i : I) : z i ∈ J i := by
    by_cases hib : i = b
    · subst i
      rw [hzb]
      exact hxb
    by_cases hia : i = a
    · subst i
      rw [hza]
      exact hxa
    simpa only [z, Function.update_of_ne hib, Function.update_of_ne hia] using hwJ i
  have hzfirst : (fun i => z i 0) = v := by
    funext i
    by_cases hib : i = b
    · subst i
      rw [hzb]
      exact hxb0
    by_cases hia : i = a
    · subst i
      rw [hza]
      exact hxa0
    simpa only [z, Function.update_of_ne hib, Function.update_of_ne hia] using hw0 i
  have hz1 : B (fun i => z i 1) = 0 := hzero _ a ha (by rw [hza]; exact hxaz 1 (by simp))
  have hz2 : B (fun i => z i 2) = 0 := hzero _ a ha (by rw [hza]; exact hxaz 2 (by simp))
  have hz3 : B (fun i => z i 3) = 0 := hzero _ b hb (by rw [hzb]; exact hxbz 3 (by simp))
  have h := hJ z hzJ
  simpa only [hzfirst, hz1, hz2, hz3, hη, add_zero, sub_zero] using h

theorem four_dependent_inputs_vanish {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    {M A : Type*} [Zero M] [AddCommGroup A]
    (S : Set I) (B : (∀ i, V i) → M)
    (hzero : ∀ v i, i ∈ S → v i = 0 → B v = 0)
    (η : M → A) (hη : η 0 = 0) (J : ∀ i, Submodule ℚ (Fin 4 → V i))
    (hJ : ∀ v : ∀ i, Fin 4 → V i, (∀ i, v i ∈ J i) →
      η (B (fun i => v i 0)) + η (B (fun i => v i 1)) -
        η (B (fun i => v i 2)) - η (B (fun i => v i 3)) = 0)
    (v : ∀ i, V i) (hv : ∀ i, v i ∈ fourFirstProjection (J i))
    (a b : I) (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hva : v a ∈ fourDependentProjection (J a))
    (hvb : v b ∈ fourDependentProjection (J b)) : η (B v) = 0 :=
  four_sparse_lifts_vanish S B hzero η hη J hJ v hv a b hab ha hb hva.1 hvb.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageRepresentatives
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

theorem span_basis_brackets_layer (e : Basis ι ℚ L) (v : κ → L) (n : ℕ)
    (hv : Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule) :
    Submodule.span ℚ (Set.range (fun ij : ι × κ => ⁅e ij.1, v ij.2⁆)) =
      (LieModule.lowerCentralSeries ℚ L L (n + 1)).toSubmodule := by
  classical
  rw [LieModule.lowerCentralSeries_succ]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    apply LieSubmodule.lie_mem_lie (by simp)
    change v j ∈ (LieModule.lowerCentralSeries ℚ L L n).toSubmodule
    rw [← hv]
    exact Submodule.subset_span ⟨j, rfl⟩
  · rw [LieSubmodule.lieIdeal_oper_eq_linear_span']
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, y, hy, rfl⟩
    have hy' : y ∈ Submodule.span ℚ (Set.range v) := hv.symm ▸ hy
    obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hy'
    rw [← e.sum_repr x, ← ht]
    simp only [sum_lie, lie_sum, smul_lie, lie_smul]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(j, i), rfl⟩

omit [Fintype κ] in
theorem exists_small_bounded_spanning_family (e : Basis ι ℚ L) (P : Submodule ℚ L)
    (v : κ → L) (hspan : Submodule.span ℚ (Set.range v) = P) {H : ℕ}
    (hv : ∀ i j, RationalHeightLE (e.repr (v i) j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ w : Fin r → L,
      Submodule.span ℚ (Set.range w) = P ∧
      ∀ i j, RationalHeightLE (e.repr (w i) j) H := by
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨w, hw, hwspan, _⟩ := hex
  refine ⟨finrank ℚ P, ?_, w, hwspan, ?_⟩
  · simpa only [Module.finrank_eq_card_basis e] using P.finrank_le
  · intro i j
    obtain ⟨a, ha⟩ := hw i
    rw [← ha]
    exact hv a j

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

def layerRoundingBound (d H l n : ℕ) : ℕ :=
  d * l * lieCoordinateHeight d H n ^ (d * d + 1)

theorem layerRoundingBound_mono_layer (d H l : ℕ) : Monotone (layerRoundingBound d H l) := by
  intro m n hmn
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (lieCoordinateHeight_mono_length d H hmn) _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ConjugationCoordinates
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

theorem conjugationInput_sub_mem_scaledGrid {ι : Type*} (a b : ι → ℚ) (m : ℕ)
    (hb : b ∈ scaledIntegerGrid m) :
    conjugationInput a b - conjugationInput a 0 ∈ scaledIntegerGrid m := by
  obtain ⟨z, hz⟩ := hb
  refine ⟨fun ji => ![0, z ji.2, 0] ji.1, ?_⟩
  funext ⟨j, i⟩
  have hi := congrFun hz i
  change b i = (m : ℚ) * (z i : ℚ) at hi
  fin_cases j <;> simp [conjugationInput, Pi.smul_apply, smul_eq_mul, hi]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RationalBCHProducts
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realDenominatorGrid_zero {ι : Type*} (l : ℕ) :
    (0 : ι → ℝ) ∈ realDenominatorGrid l := by
  exact ⟨0, by ext i; simp⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

omit [Fintype κ] in
theorem scaled_real_basis_coordinate_bound (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    (N : ℕ) (j : κ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, |(e.repr (b j) i : ℝ)| ≤ B) :
    coordinateL2Norm ((e.baseChange ℝ).equivFun ((N : ℝ) • (b.baseChange ℝ) j)) ≤
      (Fintype.card ι + 1) * ((N : ℝ) * B) := by
  apply coordinateL2Norm_le_card_bound _ (mul_nonneg (Nat.cast_nonneg N) hB)
  intro i
  change |(e.baseChange ℝ).repr ((N : ℝ) • (b.baseChange ℝ) j) i| ≤ _
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul]
  rw [abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  simpa [Basis.baseChange_apply, Basis.baseChange_repr_tmul, Algebra.smul_def] using hb i

end Erdos3

end

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H]

theorem cosetMap_smul (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) (g : G) (x : G ⧸ Γ) :
    cosetMap Γ Λ φ hφ (g • x) = φ g • cosetMap Γ Λ φ hφ x := by
  induction x using Quotient.inductionOn with
  | h a =>
    change (QuotientGroup.mk (φ (g * a)) : H ⧸ Λ) = QuotientGroup.mk (φ g * φ a)
    rw [map_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultidegreeCoordinateFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

theorem retainedCoordinate_degree [Fintype σ] (S : Finset σ) (bound : σ → ℕ) :
    multidegreeWeight (retainedCoordinateWeight S) bound = ∑ i ∈ S, bound i := by
  simp [multidegreeWeight, retainedCoordinateWeight]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds
namespace OAI

section

namespace Erdos3

theorem realDenominatorGrid_neg {ι : Type*} (l : ℕ) {x : ι → ℝ}
    (hx : x ∈ realDenominatorGrid l) : -x ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨-z, ?_⟩
  funext i
  have hi := congrFun hz i
  change (z i : ℝ) = (l : ℝ) * x i at hi
  change ((-z i : ℤ) : ℝ) = (l : ℝ) * (-x i)
  rw [Int.cast_neg, hi, mul_neg]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalLieQuotientBudget
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem rationalQuotientSectionHeight_le_exp (t d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (ht : (t : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalSolveHeight d (rationalKernelHeight t H) : ℝ) ≤ Real.exp ((p + 2) ^ 45) := by
  have hK := rationalKernelHeight_le_budget t H hp ht hH
  have hS := rationalSolveHeight_le_budget d (rationalKernelHeight t H)
    (by positivity : 0 ≤ (p + 2) ^ 7)
    (hd.trans (le_power_budget hp (by decide : 1 ≤ 7))) hK
  exact exponential_budget_comp hp (by positivity) 7 5 le_rfl hS

theorem rationalLieQuotientStructureHeight_le_exp (n t d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hd : (d : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalLieStructureHeight n
      (max H (max (rationalKernelHeight t H)
        (rationalSolveHeight d (rationalKernelHeight t H)))) : ℝ) ≤
      Real.exp ((p + 2) ^ 51) := by
  apply rationalLieStructureHeight_le_exp n _ hp hn 45
  simp only [Nat.cast_max, max_le_iff]
  refine ⟨hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide))), ?_,
    rationalQuotientSectionHeight_le_exp t d H hp ht hd hH⟩
  exact (rationalKernelHeight_le_budget t H hp ht hH).trans
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 7 ≤ 45)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

theorem abs_sub_le_of_circle_dist_on_interior {x y η δ : ℝ}
    (hx : η ≤ x ∧ x ≤ 1 - η) (hy : η ≤ y ∧ y ≤ 1 - η)
    (hδ : δ < 2 * η) (hdist : dist (x : CircleFourier.Circle) (y : CircleFourier.Circle) ≤ δ) :
    |x - y| ≤ δ := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq] at hdist
  have hxy : |x - y| ≤ 1 - 2 * η := abs_le.mpr ⟨by linarith, by linarith⟩
  have hz : |(round (x - y) : ℝ)| ≤ |x - y - (round (x - y) : ℝ)| + |x - y| := by
    calc
      _ = |((round (x - y) : ℝ) - (x - y)) + (x - y)| := by ring_nf
      _ ≤ |(round (x - y) : ℝ) - (x - y)| + |x - y| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (round (x - y) : ℝ) (x - y)]
  have hzlt : |(round (x - y) : ℝ)| < 1 := by linarith
  have hzlo : (-1 : ℤ) < round (x - y) := by exact_mod_cast (abs_lt.mp hzlt).1
  have hzhi : round (x - y) < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hzlt).2
  have hz0 : round (x - y) = 0 := by omega
  simpa only [hz0, Int.cast_zero, sub_zero] using hdist

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem frozenRealSection_unit_interval {Z Ξ : Type*} (F : Z → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (a : Option Ξ) (z : Z) :
    0 ≤ frozenRealSection F a z ∧ frozenRealSection F a z ≤ 1 := by
  cases a with
  | none => simp [frozenRealSection]
  | some a => exact hF z a

end Erdos3

end

section

namespace Erdos3

noncomputable def cyclicWrapExceptional {N : ℕ} [NeZero N] (h : ZMod N) (ρ : ℝ) : Finset (ZMod N) :=
  cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ) ∪
    cyclicCutNeighborhood N ((N - h.val : ℕ) : ℤ) (N * ρ)

theorem cyclicWrapExceptional_card_le {N : ℕ} [NeZero N] (h : ZMod N)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : ((cyclicWrapExceptional h ρ).card : ℝ) ≤ 6 * N * ρ + 3 := by
  have hδ : 0 ≤ (N : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have h0 := cyclicCutNeighborhood_card_le N 0 hδ
  have hN := cyclicCutNeighborhood_card_le N N hδ
  have hw := cyclicCutNeighborhood_card_le N ((N - h.val : ℕ) : ℤ) hδ
  have hu := Finset.card_union_le (cyclicCutNeighborhood N 0 (N * ρ))
    (cyclicCutNeighborhood N N (N * ρ))
  have hv := Finset.card_union_le
    (cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ))
    (cyclicCutNeighborhood N ((N - h.val : ℕ) : ℤ) (N * ρ))
  have hu' : ((cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ)).card : ℝ) ≤
      (cyclicCutNeighborhood N 0 (N * ρ)).card + (cyclicCutNeighborhood N N (N * ρ)).card := by
    exact_mod_cast hu
  have hv' : ((cyclicWrapExceptional h ρ).card : ℝ) ≤
      (cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ)).card +
        (cyclicCutNeighborhood N ((N - h.val : ℕ) : ℤ) (N * ρ)).card := by
    exact_mod_cast hv
  linarith

theorem cyclicWrapExceptional_density_le {N : ℕ} [NeZero N] (h : ZMod N)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  calc
    _ ≤ (6 * (N : ℝ) * ρ + 3) / N :=
      div_le_div_of_nonneg_right (cyclicWrapExceptional_card_le h hρ) (Nat.cast_nonneg _)
    _ = _ := by field_simp

theorem outside_cyclicWrapExceptional {N : ℕ} [NeZero N] (h x : ZMod N) {ρ : ℝ}
    (hx : x ∉ cyclicWrapExceptional h ρ) :
    ρ < (x.val : ℝ) / N ∧ (x.val : ℝ) / N < 1 - ρ ∧
      (N : ℝ) * ρ < |(x.val : ℝ) - ((N - h.val : ℕ) : ℝ)| := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hxN : (x.val : ℝ) < N := Nat.cast_lt.mpr x.val_lt
  simp only [cyclicWrapExceptional, Finset.mem_union, not_or, mem_cyclicCutNeighborhood] at hx
  have h0 : (N : ℝ) * ρ < (x.val : ℝ) := by
    simpa only [Int.cast_zero, sub_zero,
      abs_of_nonneg (show (0 : ℝ) ≤ x.val from Nat.cast_nonneg _)] using lt_of_not_ge hx.1.1
  have h1 : (N : ℝ) * ρ < (N : ℝ) - x.val := by
    simpa only [Int.cast_natCast, abs_of_neg (sub_neg.mpr hxN), neg_sub] using lt_of_not_ge hx.1.2
  refine ⟨(lt_div_iff₀ hN).mpr (by nlinarith), (div_lt_iff₀ hN).mpr (by nlinarith), ?_⟩
  simpa only [Int.cast_natCast] using lt_of_not_ge hx.2

end Erdos3

end

section

namespace Erdos3

theorem good_circle_observations_control_representatives {N : ℕ} [NeZero N]
    (h x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    |(x.val : ℝ) / N - (y.val : ℝ) / N| ≤ ρ := by
  have hx' := outside_cyclicWrapExceptional h x hx
  have hy' := outside_cyclicWrapExceptional h y hy
  apply abs_sub_le_of_circle_dist_on_interior ⟨hx'.1.le, hx'.2.1.le⟩ ⟨hy'.1.le, hy'.2.1.le⟩
    (by linarith)
  simpa only [ZMod.toAddCircle_apply] using hdist

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeParameterCoverBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem boxCoverCount_dimension_bound (d : ℕ) (K : ℝ≥0) {B ε p : ℝ}
    (hB0 : 0 ≤ B) (hε : 0 < ε) (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hB : B ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) (hinv : 1 / ε ≤ Real.exp p) :
    (((boxCoverMeshCount B K ε + 1) ^ d : ℕ) : ℝ) ≤ Real.exp (p * (3 * p + 4)) := by
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (3 * p + 4)) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (boxCoverMeshCount_add_one_le_exp K hB0 hε hp hB hK hinv) d
    _ = Real.exp ((d : ℝ) * (3 * p + 4)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd (by positivity))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedLieQuotient
namespace OAI

section

namespace Erdos3

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem supportedQuotientBasis_lieStructure (b : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (S : Set ι) (hI : I.toSubmodule = Submodule.span ℚ (b '' S))
    (i j k : {i // i ∉ S}) :
    lieStructureConstants (L := L ⧸ I) (supportedQuotientBasis b I.toSubmodule S hI) i j k =
      lieStructureConstants b i j k := by
  unfold lieStructureConstants
  rw [supportedQuotientBasis_apply, supportedQuotientBasis_apply]
  change (supportedQuotientBasis b I.toSubmodule S hI).repr
    (I.toSubmodule.mkQ ⁅b i, b j⁆) k = _
  exact supportedQuotientBasis_repr_mk b I.toSubmodule S hI _ k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.VerticalFrequencyIdentification
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct

theorem real_frequency_eq_of_character_multiples (a b : ℝ)
    (h : ∀ t : ℝ, character ((t * a : ℝ) : CircleFourier.Circle) =
      character ((t * b : ℝ) : CircleFourier.Circle)) : a = b := by
  have hinj : Function.Injective character := by
    intro x y hxy
    apply AddCircle.injective_toCircle one_ne_zero
    exact Subtype.ext hxy
  have hzero (t : ℝ) : ((t * (a - b) : ℝ) : CircleFourier.Circle) = 0 := by
    rw [mul_sub, AddCircle.coe_sub]
    exact sub_eq_zero.mpr (hinj (h t))
  by_contra hne
  have hab : a - b ≠ 0 := sub_ne_zero.mpr hne
  have ht : (1 / (2 * (a - b))) * (a - b) = (1 : ℝ) / 2 := by
    field_simp
  have hhalf := hzero (1 / (2 * (a - b)))
  rw [ht] at hhalf
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hhalf
  have hn' : (n : ℝ) = 1 / 2 := by simpa only [zsmul_eq_mul, mul_one] using hn
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hn1 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype υ] [Fintype χ] [Fintype κ] [Fintype ν]

theorem stepDrop_basis_height_budget (n r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (((n + 1) * rationalKernelHeight r H ^ n : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
  have hkernel := rationalKernelHeight_le_budget r H hp hr hH
  have hfront : (n + 1 : ℝ) ≤ Real.exp n := Real.add_one_le_exp n
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (rationalKernelHeight r H)) hkernel n
  rw [← Real.exp_nat_mul] at hpower
  have h : (((n + 1) * rationalKernelHeight r H ^ n : ℕ) : ℝ) ≤
      Real.exp ((n : ℝ) + n * (p + 2) ^ 7) := by
    push_cast
    rw [Real.exp_add]
    exact mul_le_mul hfront hpower (by positivity) (Real.exp_nonneg _)
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have ht : (1 : ℝ) ≤ p + 2 := by linarith
  have hpow : p + 2 ≤ (p + 2) ^ 8 := by
    simpa only [pow_one] using pow_le_pow_right₀ ht (by decide : 1 ≤ 8)
  calc
    (n : ℝ) + n * (p + 2) ^ 7 ≤ p + p * (p + 2) ^ 7 := by gcongr
    _ ≤ (p + 2) + (p + 2) * (p + 2) ^ 7 := by gcongr <;> linarith
    _ = (p + 2) + (p + 2) ^ 8 := by ring
    _ ≤ 2 * (p + 2) ^ 8 := by linarith
    _ ≤ (p + 2) * (p + 2) ^ 8 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (p + 2) ^ 9 := by ring

end Erdos3

end

section

namespace Erdos3

open Module

variable {L μ υ ν : Type*} [LieRing L] [LieAlgebra ℚ L]

def homogeneousIntersectionBasisHeight (n r H : ℕ) : ℕ :=
  (n + 1) * rationalKernelHeight r H ^ n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.VerticalDecompositionBudget
namespace OAI

section

namespace Erdos3

theorem centralActionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ centralActionBudget p := by
  unfold centralActionBudget
  positivity

theorem le_centralActionBudget {p : ℝ} (hp : 0 ≤ p) : p ≤ centralActionBudget p := by
  have h : 0 ≤ (p + 3) ^ 9 := by positivity
  unfold centralActionBudget
  linarith

theorem verticalDecompositionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ verticalDecompositionBudget p := by
  unfold verticalDecompositionBudget
  have := centralActionBudget_nonneg hp
  positivity

theorem exists_verticalDecompositionBudget_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → verticalDecompositionBudget p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + 3) ^ 9 + 2 * Polynomial.X + 2
  let P : Polynomial ℕ :=
    2 * Q * (2 * Q + 2) ^ 4 + ((2 * Q + 2) ^ 4 + Q + (Polynomial.X + 3) ^ 5 + 2) ^ 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, Q, verticalDecompositionBudget, centralActionBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration

theorem squareGeometryBudget_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ squareGeometryBudget p := by
  unfold squareGeometryBudget
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FrozenCorrelationBudget
namespace OAI

section

namespace Erdos3

theorem frozen_witness_budget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    productNiltestBudget (raisedNiltestBudget p) ≤ productNiltestBudget (raisedNiltestBudget q) := by
  unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
  gcongr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCrossFactorization
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem le_productNiltestBudget {p : ℝ} (hp : 0 ≤ p) : p ≤ productNiltestBudget p := by
  apply le_trans _ (productNiltestBudget_geometry hp)
  nlinarith [sq_nonneg p]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealPolynomialBCH
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

theorem differenceInput_sub_mem_scaledGrid {ι : Type*} (a b : ι → ℚ) (m : ℕ)
    (hba : b - a ∈ scaledIntegerGrid m) :
    differenceInput a b - differenceInput a a ∈ scaledIntegerGrid m := by
  obtain ⟨z, hz⟩ := hba
  refine ⟨fun ji => ![0, z ji.2, 0] ji.1, ?_⟩
  funext ⟨j, i⟩
  have hi := congrFun hz i
  change b i - a i = (m : ℚ) * (z i : ℚ) at hi
  fin_cases j <;> simp [differenceInput, Pi.smul_apply, smul_eq_mul, hi]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def normalizedSquareProjectionBudget (p : ℝ) : ℝ :=
  (squareGeometryBudget p + p + 4) ^ 2

noncomputable def normalizedSquareObservableBudget (a b : ℕ) (p : ℝ) : ℝ :=
  2 * p + normalizedSquareProjectionBudget p + normalizedSquareLeftBudget a b p + 1

noncomputable def normalizedSquareReconstructionBudget (a b : ℕ) (p : ℝ) : ℝ :=
  squareGeometryBudget p + 1 + normalizedSquareObservableBudget a b p + 2 * p

noncomputable def normalizedSquareComplexityBudget (a b c : ℕ) (p : ℝ) : ℝ :=
  squareGeometryBudget p + 2 * p + (normalizedSquareReconstructionBudget a b p + c) ^ c + 4

theorem normalizedSquareProjectionBudget_nonneg (p : ℝ) :
    0 ≤ normalizedSquareProjectionBudget p := sq_nonneg _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalConstraintCountBudget
namespace OAI

section

namespace Erdos3

open Module

theorem rational_log_height_count_exp_bound (N : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ((((2 * ⌈Real.exp A⌉₊ + 1) * (⌈Real.exp A⌉₊ + 1)) ^ N : ℕ) : ℝ) ≤
      Real.exp (3 * N * (A + 2)) := by
  have he := rational_height_count_exp_bound ⌈Real.exp A⌉₊ N
    (A := A + 1) (by linarith) (ceil_exp_le_exp_add_one hA)
  convert he using 1
  congr 1
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonIntegralModelEquivalences
namespace OAI

section

namespace Erdos3

open Module

theorem exists_common_positive_nat {α : Type*} (S : Finset α) (hS : S.Nonempty)
    (n : α → ℕ) {p : ℝ} (hn : ∀ a ∈ S, 0 < n a ∧ (n a : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, n a = n a₀) ∧
      Real.exp (-p) * S.card ≤ (T.card : ℝ) := by
  let A := Finset.Icc 1 ⌊Real.exp p⌋₊
  have hA : ((A : Set ℕ).ncard : ℝ) ≤ Real.exp p := by
    simpa only [A, Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] using
      (Nat.floor_le (Real.exp_nonneg p))
  obtain ⟨k, _, T, hTS, hT, hk, hlarge⟩ := exists_exponential_constant_fiber S hS n
    (A : Set ℕ) A.finite_toSet
    (fun a ha => Finset.mem_Icc.mpr ⟨(hn a ha).1, Nat.le_floor (hn a ha).2⟩) hA
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀, fun a ha => (hk a ha).trans (hk a₀ ha₀).symm, hlarge⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

theorem tail_span_basis_members (b : Basis (Fin d) ℚ L) (P : Submodule ℚ L) (c : ℕ)
    (hP : P = basisTail b c) : P = Submodule.span ℚ (b '' {j | b j ∈ P}) := by
  apply le_antisymm
  · conv_lhs => rw [hP, basisTail_eq_span]
    apply Submodule.span_mono
    rintro x ⟨j, hj, rfl⟩
    exact ⟨j, hP.symm ▸ basis_mem_tail b j hj, rfl⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨j, hj, rfl⟩; exact hj)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxOverlapSize
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem cardinality_ge_overlap_weight {A : Type*} [AddCommGroup A] [DecidableEq A]
    {Q : Finset A} (hQ : Q.Nonempty) (I : Finset A) (P : A → Prop) [DecidablePred P]
    {μ : ℝ}
    (hweight : μ ≤ ∑ h ∈ I, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
      (if P h then (1 : ℝ) else 0)) :
    μ * Q.card ≤ ((I.filter P).card : ℝ) := by
  have hq : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hbound (h : A) : ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2 ≤
      1 / Q.card := by
    have hc : ((derivativeSupport Q h).card : ℝ) ≤ Q.card := by
      exact_mod_cast Finset.card_filter_le Q (fun x => x + h ∈ Q)
    apply (div_le_div_iff₀ (sq_pos_of_pos hq) hq).mpr
    nlinarith
  have hsum : (∑ h ∈ I, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
      (if P h then (1 : ℝ) else 0)) ≤ ((I.filter P).card : ℝ) / Q.card := by
    calc
      _ = ∑ h ∈ I.filter P, ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro h _
        split_ifs <;> simp
      _ ≤ ∑ _h ∈ I.filter P, 1 / (Q.card : ℝ) := Finset.sum_le_sum (fun h _ => hbound h)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  exact (le_div_iff₀ hq).mp (hweight.trans hsum)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_finiteCorrelation_one {A : Type*} (Q : Finset A) (u : A → ℂ) :
    ‖finiteCorrelation Q (fun _ => 1) u‖ = ‖𝔼 x ∈ Q, u x‖ := by
  have he : (𝔼 x ∈ Q, star (u x)) = star (𝔼 x ∈ Q, u x) := by
    simp [Finset.expect, star_sum]
  simp only [finiteCorrelation, one_mul, he, norm_star]

theorem finiteCorrelation_one_derivative {A : Type*} [AddCommGroup A]
    (Q : Finset A) (u : A → ℂ) (h : A) :
    finiteCorrelation Q (multiplicativeDerivative (fun _ : A => 1) h) (multiplicativeDerivative u h) =
      𝔼 x ∈ Q, u (x + h) * star (u x) := by
  simp only [finiteCorrelation, multiplicativeDerivative, star_one, one_mul, star_mul, star_star]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitIntervalBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem unitIntervalBox_eq_image (a : ℤ) (len : ℕ) :
    translatedIntegerBox (fun _ : Unit => a) (fun _ => len) =
      (Finset.Ico a (a + len)).image (scalarUnitEquiv ℤ) := by
  ext x
  rw [mem_translatedIntegerBox, Finset.mem_image]
  constructor
  · intro hx
    exact ⟨x (), Finset.mem_Ico.mpr (hx ()), (scalarUnitEquiv ℤ).apply_symm_apply x⟩
  · rintro ⟨n, hn, rfl⟩ u
    exact Finset.mem_Ico.mp hn

theorem unitIntervalBox_expect (a : ℤ) (len : ℕ) (f : (Unit → ℤ) → ℂ) :
    (𝔼 x ∈ translatedIntegerBox (fun _ : Unit => a) (fun _ => len), f x) =
      𝔼 n ∈ Finset.Ico a (a + len), f (fun _ => n) := by
  rw [unitIntervalBox_eq_image]
  exact Finset.expect_image (scalarUnitEquiv ℤ).injective.injOn

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NiltestConjugateFrequency
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realifyFunctional_neg {V : Type*} [AddCommGroup V] [Module ℚ V]
    (eta : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional (-eta) x = -realifyFunctional eta x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp only [realifyFunctional_tmul, LinearMap.neg_apply, Rat.cast_neg, mul_neg]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RefiltrationLayerBasis
namespace OAI

section

namespace Erdos3

open Module

theorem span_selected_basis {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (S : Set ι) [DecidablePred (· ∈ S)] :
    Submodule.span ℚ (Set.range (fun i => if i ∈ S then b i else 0)) =
      Submodule.span ℚ (b '' S) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (if i ∈ S then b i else 0) ∈ Submodule.span ℚ (b '' S)
    split_ifs with hi
    · exact Submodule.subset_span ⟨i, hi, rfl⟩
    · exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    simpa only [if_pos hi] using
      (Submodule.subset_span (s := Set.range (fun i => if i ∈ S then b i else 0)) ⟨i, rfl⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RankBracketFactorizationMonotone
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realifyFunctional_sub_apply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ξ η : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional (ξ - η) x = realifyFunctional ξ x - realifyFunctional η x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t v => simp only [realifyFunctional_tmul, LinearMap.sub_apply, Rat.cast_sub, mul_sub]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3

def rankIntervalInputBudget (c : ℕ) (p : ℝ) : ℝ :=
  (p + c) ^ c + raisedNiltestBudget p + p + 5

theorem rankIntervalInputBudget_bounds (c : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    5 ≤ rankIntervalInputBudget c p ∧ p + 4 ≤ rankIntervalInputBudget c p ∧
      raisedNiltestBudget p ≤ rankIntervalInputBudget c p ∧
      (p + c) ^ c ≤ rankIntervalInputBudget c p := by
  have ha : 0 ≤ (p + c) ^ c := by positivity
  have hb : 0 ≤ raisedNiltestBudget p := by unfold raisedNiltestBudget; positivity
  unfold rankIntervalInputBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeRoundingThreshold
namespace OAI

section

namespace Erdos3

theorem sharedFreeEquationInputBudget_bounds (s : ℕ) {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) :
    let z := 8 * sharedRefinementInputBudget s p + 1
    let a := fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p)
    let A := sharedFreeEquationInputBudget s q p
    0 ≤ A ∧ 4 * p ≤ A ∧ a + 1 ≤ A ∧ z + ((z + 2) ^ 3 + (z + 2) ^ 36) ≤ A := by
  intro z a A
  have hi := (sharedRefinementInputBudget_bounds s hp).2.2.1
  have hz : 0 ≤ z := by dsimp only [z]; linarith
  have ha : 0 ≤ a :=
    fourRefinementAnnihilatorBudget_nonneg (add_nonneg hq (coefficientFourHeightBudget_nonneg hp))
  have hZ : 0 ≤ z + ((z + 2) ^ 3 + (z + 2) ^ 36) := by positivity
  have hA : A = 4 * p + (a + 1) + (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) := rfl
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

noncomputable def sharedFreeRecoveryThreshold (s : ℕ) (q p : ℝ) : ℝ :=
  max (separationBudget (8 * sharedRefinementInputBudget s p + 1))
    ((sharedFreeEquationInputBudget s q p + 2) ^ 5)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeComparisonBasis
namespace OAI

section

namespace Erdos3

noncomputable def sharedFreeComparisonBasisBudget (q p : ℝ) : ℝ :=
  let A := q + fourRefinementBasisBudget (q + coefficientFourHeightBudget p)
  A + preimageBasisBudget (4 * A)

end Erdos3

end

end OAI
end


