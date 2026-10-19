-- Prove2me | Definitions.Def_OAIE3v2B199
-- name    : OAIE3v2B199
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:17:13.965675+00:00
-- url     : https://prove2.me/theorems/f33772a5-417f-4205-ae2a-2b6f072dee39
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 203 of 311
-- statement:
--   Definitions bundle 203 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B299`, `OAIE3v2B180`, `OAIE3v2B181`, `OAIE3v2B183` of this split.
--
--   Modules: `Dynamics/SharedFreeCorrelationBudget.lean`, `Estimates/AllocatedRecoveredPreparedFreeze.lean`, `Estimates/CommonFreeSunflower.lean`, `Estimates/CoveredQuotientCorrelation.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Estimates/NativeCommonModelQuadruples.lean`, `Estimates/NativeCorrelatedFactorFamily.lean`, `Estimates/NativeFixedFactoredQuadruples.lean`, `Estimates/NativeResidualCrossInduction.lean`, `Estimates/NativeResidualMultiplier.lean`, `Estimates/NativeSharedFrozenCorrelations.lean`, `Estimates/NativeSubspaceFreeModel.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/QuadraticBoundedFamily.lean`, `Estimates/QuadraticPairCorrelator.lean`, `Estimates/QuadraticPairStepDrop.lean`, `Estimates/SharedFreeComparisonDescent.lean`, `Estimates/SharedFreeComparisonLift.lean`, `Estimates/SharedFreeFrozenComparison.lean`, `Estimates/SharedFreeLowerFactorization.lean`, `Estimates/UnitVerticalNativeInverseModels.lean`, `Fourier/ForecastSpatialCharacterSplit.lean`, `Geometry/CertifiedFullChartFrozenTerminal.lean`, `Geometry/NativeCoordinateSplitFreezing.lean`, `Lattices/AllocatedRecoveredIntegerFullChart.lean`, `Lattices/CommonAffineOrbitEvaluation.lean`, `Linear/BinaryLowerRankFamily.lean`, `Linear/CommonFreeSpanBounds.lean`, `Linear/CommonRankCoefficientCorrections.lean`, `Linear/FullFastHorizontalSpanning.lean`, `Linear/NativeCoefficientKernel.lean`, `Linear/NativeRankRelationExistence.lean`, `Linear/NativeReplacedRankFamily.lean`, `Linear/RankIntervalFactorization.lean`, `Linear/ReducedSquareGradedKernel.lean`, `Nilpotent/AntisymmetricPairNiltest.lean`, `Polynomial/AllocatedSeparatedCongruencePolynomial.lean`, `Polynomial/LowTaggedPolynomialCoordinates.lean`, `Sampling/AllocatedForecastShortRawDependence.lean`, `Sampling/ForecastLawNativeRawJointMean.lean`, `Sampling/SamplerSeparatedVariables.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B183

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualMultiplier
namespace OAI

section

namespace Erdos3

namespace NativeCorrelationStructure

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def mono (hpq : p ≤ q) : NativeCorrelationStructure s r N q f where
  shifts := W.shifts
  nonempty := W.nonempty
  density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
    (Nat.cast_nonneg _)).trans W.density
  mixed := W.mixed.mono hpq
  family := W.family.mono hpq
  correlation h hh := by
    obtain ⟨V⟩ := W.correlation h hh
    exact ⟨V.mono hpq⟩

end NativeCorrelationStructure

end Erdos3

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def selectedProduct (h : W.shifts) (x : ZMod N) : ℂ :=
  W.mixed.evalCyclic N (W.selectedWitness h).coordinate.1 (correlationInput h.val x) *
    W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x *
    (W.selectedWitness h).test.evalCyclic N (fun _ => x)

theorem selectedProduct_correlation (h : W.shifts) :
    Real.exp (-p) ≤ ‖𝔼 x, multiplicativeDerivative f h.val x * star (W.selectedProduct h x)‖ := by
  simpa only [selectedProduct, nativeCorrelationResidual, star_mul, mul_assoc, mul_left_comm, mul_comm]
    using (W.selectedWitness h).correlation

end Erdos3.NativeCorrelationStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFixedFactoredQuadruples
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def selectedMixed (h : W.shifts) (x : ZMod N) : ℂ :=
  W.mixed.evalCyclic N (W.selectedWitness h).coordinate.1 (correlationInput h.val x)

noncomputable def selectedRank (h : W.shifts) (x : ZMod N) : ℂ :=
  W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x

noncomputable def selectedLower (h : W.shifts) (x : ZMod N) : ℂ :=
  (W.selectedWitness h).test.evalCyclic N (fun _ => x)

theorem selectedProduct_eq (h : W.shifts) (x : ZMod N) :
    W.selectedProduct h x = W.selectedMixed h x * W.selectedRank h x * W.selectedLower h x := rfl

end Erdos3.NativeCorrelationStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeReplacedRankFamily
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def replacedRankResidual (h : ZMod N)
    (c : Fin W.family.outputDim → ZMod N → ℂ)
    (ij : Fin W.mixed.outputDim × Fin W.family.outputDim) (x : ZMod N) : ℂ :=
  multiplicativeDerivative f h x * star (W.mixed.evalCyclic N ij.1 (correlationInput h x)) *
    star (c ij.2 x)

theorem exists_rank_approximation_correlation {J : Type*} [Fintype J]
    (hf : ∀ x, ‖f x‖ ≤ 1) (h : W.shifts) (A : J → ZMod N → ℝ)
    (c : J → Fin W.family.outputDim → ZMod N → ℂ) {q : ℝ}
    (hq : 2 ≤ q) (hcard : (Fintype.card J : ℝ) ≤ Real.exp q)
    (hA : ∀ j, PositiveCyclicNiltest.{0} (s - 1) N q (A j))
    (herr : (𝔼 x, ‖W.selectedRank h x -
      ∑ j, (A j x : ℂ) * c j (W.selectedWitness h).coordinate.2 x‖) ≤ Real.exp (-(2 * p)) / 2) :
    ∃ j, Nonempty (NativeVectorCorrelation (s - 1) N
      (productNiltestBudget (raisedNiltestBudget (p + q + 2))) (W.replacedRankResidual h.val (c j))) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let b (x : ZMod N) := W.selectedMixed h x * W.selectedLower h x
  have hb (x : ZMod N) : ‖b x‖ ≤ Real.exp p := by
    have hm := W.mixed.norm_eval (W.selectedWitness h).coordinate.1
      (fun i => (((correlationInput h.val x) i).val : ℤ))
    have hl := (W.selectedWitness h).test.eval_budget (W.selectedWitness h).complexity
      (fun _ : Unit => (x.val : ℤ))
    exact (norm_mul _ _).trans_le ((mul_le_mul hm hl (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  let v (j : J) (x : ZMod N) := (A j x : ℂ) * c j (W.selectedWitness h).coordinate.2 x * b x
  have hmean : (𝔼 x, ‖W.selectedProduct h x - ∑ j, v j x‖) ≤ Real.exp (-p) / 2 := by
    have he := mean_error_mul_bounded (W.selectedRank h)
      (fun x => ∑ j, (A j x : ℂ) * c j (W.selectedWitness h).coordinate.2 x) b
      (Real.exp_pos p).le hb herr
    have hid (x : ZMod N) : W.selectedProduct h x - ∑ j, v j x =
        W.selectedRank h x * b x -
        (∑ j, (A j x : ℂ) * c j (W.selectedWitness h).coordinate.2 x) * b x := by
      rw [Finset.sum_mul]
      simp only [v, b, W.selectedProduct_eq]
      ring
    have hexp : Real.exp p * (Real.exp (-(2 * p)) / 2) = Real.exp (-p) / 2 := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      ring
    simpa only [hid, hexp] using he
  obtain ⟨j, hj⟩ := exists_correlating_summand_of_mean (multiplicativeDerivative f h.val)
    (W.selectedProduct h) v (Real.exp_pos (-p)) (Real.exp_pos q) hcard
    (multiplicativeDerivative_norm_le_one f hf h.val) hmean (W.selectedProduct_correlation h)
  have hthreshold : Real.exp (-(p + q + 2)) ≤ Real.exp (-p) / (2 * Real.exp q) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have he : Real.exp (-(p + q + 2)) * (2 * Real.exp q) = 2 * Real.exp (-p - 2) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    rw [he]
    have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    calc
      _ ≤ Real.exp 2 * Real.exp (-p - 2) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
  have hpR : p ≤ p + q + 2 := by linarith
  have hqR : q ≤ p + q + 2 := by linarith
  let V : NativeVectorCorrelation (s - 1) N (p + q + 2)
      (fun ij x => (A j x : ℂ) * W.replacedRankResidual h.val (c j) ij x) := {
    L := (W.selectedWitness h).L
    dim := (W.selectedWitness h).dim
    model := (W.selectedWitness h).model
    test := (W.selectedWitness h).test
    complexity := (W.selectedWitness h).complexity.mono hpR
    coordinate := (W.selectedWitness h).coordinate
    correlation := by
      have hc := hthreshold.trans hj
      have heq (x : ZMod N) : multiplicativeDerivative f h.val x * star (v j x) =
          ((A j x : ℂ) * W.replacedRankResidual h.val (c j) (W.selectedWitness h).coordinate x) *
            star ((W.selectedWitness h).test.evalCyclic N (fun _ => x)) := by
        simp only [v, b, selectedMixed, selectedLower, replacedRankResidual, star_mul,
          Complex.star_def, Complex.conj_ofReal]
        ring
      simpa only [heq] using hc }
  exact ⟨j, V.exists_absorb_positive (W.replacedRankResidual h.val (c j)) (A j)
    (by linarith) ((hA j).mono le_rfl hqR)⟩

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

open VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem exists_native_frozen_rank_correlation (s a : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (h : W.shifts) (P : ℝ), 2 ≤ P → p ≤ P →
      ∀ M : ℕ, 0 < M → (M : ℝ) ≤ Real.exp P →
      ∀ ε ξ v γ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      ε * ξ * v * γ = W.family.orbit h.val →
      CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P + 2) ^ a)) ε.log →
      (∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
        (QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) x γ) : W.family.model.Space) =
        QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) y γ)) →
      Real.exp ((P + C) ^ C) ≤ N →
      ∃ y : ZMod N,
        (∀ x, ∑ i, ‖W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) ε (ξ * v) γ y x‖ ^ 2 = 1) ∧
        Nonempty (NativeVectorCorrelation (s - 1) N ((P + C) ^ C)
          (W.replacedRankResidual h.val (fun i x => W.family.model.frozenCyclicOrbitValue
            (W.family.vertical.observable i) ε (ξ * v) γ y x))) := by
  obtain ⟨c, _, hfreeze⟩ := exists_partition_orbit_freezing s a
  obtain ⟨b, _, hpart⟩ := exists_interval_residue_partition 1
  obtain ⟨C, hC, hbudget⟩ := exists_frozen_correlation_budget c b
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf h P hP hpP M hM hMP ε ξ v γ hprod hε hperiod hN
  classical
  let : NeZero M := ⟨hM.ne'⟩
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  have hP0 : 0 ≤ P := by linarith
  let D := (P + c) ^ c
  let L := D + 2 * P + 40
  let Q := P + (L + b) ^ b + 2
  let ρ := Real.exp (-L)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hPL : P ≤ L := by dsimp only [L]; linarith
  have hρ : 0 < ρ := Real.exp_pos _
  obtain ⟨hLC, hQC⟩ := hbudget P hP0
  have hlarge : Real.exp L ≤ N := (Real.exp_le_exp.mpr hLC).trans hN
  have hprec : 1 / ρ ≤ Real.exp ((L + 2) ^ 1) := by
    rw [pow_one]
    have he : 1 / ρ = Real.exp L := by simp only [ρ, Real.exp_neg, one_div, inv_inv]
    rw [he]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨n, hn, hcard, A, hA, hsum, hcells⟩ := hpart N M hL
    (hMP.trans (Real.exp_le_exp.mpr hPL)) hρ hprec
  have hqQ : (L + b) ^ b ≤ Q := by dsimp only [Q]; linarith
  have hQ : 2 ≤ Q := by
    have ht : 0 ≤ (L + b) ^ b := by positivity
    dsimp only [Q]
    linarith
  have hDgeom := W.family.complexity.1.mono W.family.model hpP
  have hprod' : ε * (ξ * v) * γ = W.family.orbit h.val := by
    simpa only [mul_assoc] using hprod
  obtain ⟨y, _, hmean⟩ := hfreeze W.family.model (by linarith : 1 ≤ P) hDgeom hρ A
    (fun j x => ((hA j).unit_interval x).1) hsum hcells
    (W.family.vertical.observable (W.selectedWitness h).coordinate.2) W.family.vertical.lipBound
    (W.family.vertical.norm _) (W.family.vertical.lipschitz _)
    (W.family.vertical.lip_bound.trans (Real.exp_le_exp.mpr hpP))
    ε (ξ * v) γ (W.family.orbit h.val) hprod' hε hperiod
  let B (j : Fin n × ZMod M) (i : Fin W.family.outputDim) (x : ZMod N) :=
    W.family.model.frozenCyclicOrbitValue (W.family.vertical.observable i) ε (ξ * v) γ (y j) x
  have herror : (𝔼 x, ‖W.selectedRank h x -
      ∑ j, (A j x : ℂ) * B j (W.selectedWitness h).coordinate.2 x‖) ≤ Real.exp (-(2 * p)) / 2 := by
    apply hmean.trans
    exact (frozen_correlation_precision_error P D hD (NeZero.pos N) hlarge).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  obtain ⟨j, V⟩ := W.exists_rank_approximation_correlation hf h A B hQ
    (hcard.trans (Real.exp_le_exp.mpr hqQ))
    (fun j => (hA j).mono (by omega) hqQ) herror
  have hcost : productNiltestBudget (raisedNiltestBudget (p + Q + 2)) ≤ (P + C) ^ C :=
    (frozen_witness_budget_mono (by positivity) (by linarith)).trans hQC
  refine ⟨y j, fun x => W.family.vertical.unit _, ?_⟩
  exact ⟨(Classical.choice V).mono hcost⟩

end Erdos3

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)
  {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (E : RationalFilteredNilmanifold L s d) (T : E.DegreeRankStructure r)
  (hpq : p ≤ q) (hT : T.ComplexityLE q)
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

noncomputable def replacementFamily : NativeDegreeRankFamily s r (ZMod N) q where
  L := L
  dim := d
  model := E
  rank := T
  complexity := hT
  orbit := g
  normalized := hg
  outputDim := W.family.outputDim
  output_pos := W.family.output_pos
  output_bound := W.family.output_bound.trans (Real.exp_le_exp.mpr hpq)
  vertical := V

noncomputable def replaceRank (H : Finset (ZMod N)) (hne : H.Nonempty)
    (hdense : Real.exp (-q) * Fintype.card (ZMod N) ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N q
      (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (g h))))))) :
    NativeCorrelationStructure s r N q f where
  shifts := H
  nonempty := hne
  density := hdense
  mixed := W.mixed.mono hpq
  family := W.replacementFamily E T hpq hT V g hg
  correlation := hcorr

end Erdos3.NativeCorrelationStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSharedFrozenCorrelations
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem NativeCorrelationStructure.replacedRankResidual_norm_sub_le
    {s r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
    (W : NativeCorrelationStructure s r N p F) (hF : ∀ x, ‖F x‖ ≤ 1)
    (h : ZMod N) (c c' : Fin W.family.outputDim → ZMod N → ℂ)
    (ij : Fin W.mixed.outputDim × Fin W.family.outputDim) (x : ZMod N) :
    ‖W.replacedRankResidual h c ij x - W.replacedRankResidual h c' ij x‖ ≤
      ‖c ij.2 x - c' ij.2 x‖ := by
  unfold NativeCorrelationStructure.replacedRankResidual
  rw [← mul_sub, ← star_sub, norm_mul, norm_mul, norm_star, norm_star]
  have hd := multiplicativeDerivative_norm_le_one F hF h x
  have hm := W.mixed.norm_eval ij.1 (fun j => (((correlationInput h x) j).val : ℤ))
  have hmul : ‖multiplicativeDerivative F h x‖ *
      ‖W.mixed.evalCyclic N ij.1 (correlationInput h x)‖ ≤ 1 := by
    exact (mul_le_mul hd hm (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  exact mul_le_of_le_one_left (norm_nonneg _) hmul

theorem exists_native_shared_frozen_correlations (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p P : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      0 ≤ P → p ≤ P → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp P →
      ∀ (H : Finset (ZMod N)) (a u : ZMod N → W.family.model.RealGroup)
        (b : ZMod N → ZMod N → W.family.model.RealGroup), H.Nonempty →
      (∀ h ∈ H, ∀ i, |(W.family.model.basis.baseChange ℝ).repr (a h).coord i| ≤ Real.exp ((P + 2) ^ k)) →
      (∀ h ∈ H, ∀ i, |(W.family.model.basis.baseChange ℝ).repr (u h).coord i| ≤ Real.exp ((P + 2) ^ k)) →
      (∀ h ∈ H, (W.family.model.basis.baseChange ℝ).equivFun (u h).coord ∈ realDenominatorGrid q) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N P
        (W.replacedRankResidual h (fun i x => W.family.vertical.observable i
          (QuotientGroup.mk (a h * b h x * u h)))))) →
      ∃ Λ : Subgroup W.family.model.filtration.Group, Λ ≤ W.family.model.lattice ∧
        (Λ.subgroupOf W.family.model.lattice).Characteristic ∧
        (Λ.subgroupOf W.family.model.lattice).Normal ∧
        (Λ.subgroupOf W.family.model.lattice).FiniteIndex ∧
        (Λ.relIndex W.family.model.lattice : ℝ) ≤ Real.exp ((P + C) ^ C) ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates W.family.model.basis Λ)
          (hout : bchSubgroupCoordinates W.family.model.basis Λ ⊆ denominatorGrid m),
          (W.family.rank.withLattice Λ m hm hin hout).ComplexityLE ((P + C) ^ C) ∧
          ∃ H' : Finset (ZMod N), H' ⊆ H ∧ H'.Nonempty ∧
            Real.exp (-((P + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
            ∃ U : (W.family.model.withLattice Λ m hm hin hout).UnitVerticalObservable
                ((W.family.rank.withLattice Λ m hm hin hout).realSubgroup s r)
                (Fin W.family.outputDim) ((P + C) ^ C),
              U.frequency = W.family.vertical.frequency ∧
              ∀ h ∈ H', Nonempty (NativeVectorCorrelation (s - 1) N ((P + C) ^ C)
                (W.replacedRankResidual h (fun i x => U.observable i (QuotientGroup.mk (b h x))))) := by
  obtain ⟨a₀, _, hshared⟩ := exists_shared_frozen_unit_observable s k
  let Q : Polynomial ℕ := 3 * Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C a₀) ^ a₀ + 2)
  refine ⟨C, hC, ?_⟩
  intro r N _ p P F W hF hP hpP q hq hqP H a u b hH ha hu hugrid hcorr
  let T := 3 * P + 2
  let ε := Real.exp (-T)
  have hPT : P ≤ T := by dsimp only [T]; linarith
  have hpT : p ≤ T := hpP.trans hPT
  have hT : 0 ≤ T := hP.trans hPT
  have hε : 0 < ε := Real.exp_pos _
  have hεT : 1 / ε ≤ Real.exp T := by simp only [ε, one_div, ← Real.exp_neg, neg_neg, le_refl]
  have hsum : T + (T + a₀) ^ a₀ + 2 ≤ (P + C) ^ C := by
    simpa [Q, T, Polynomial.eval₂_pow] using hbudget P hP
  have hTC : (T + a₀) ^ a₀ ≤ (P + C) ^ C := by linarith
  have hPC : P + 1 ≤ (P + C) ^ C := by
    have : 0 ≤ (T + a₀) ^ a₀ := by positivity
    linarith
  have hbound : Real.exp ((P + 2) ^ k) ≤ Real.exp ((T + 2) ^ k) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k)
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout,
      hRank, H', hsub, hnonempty, hdense, U, hfreq, happ⟩ :=
    hshared W.family.model W.family.rank hT (W.family.complexity.mono _ hpT)
      hε hεT q hq (hqP.trans (Real.exp_le_exp.mpr hPT))
      (W.family.vertical.mono hpT) H a u hH
      (fun h hh i => (ha h hh i).trans hbound)
      (fun h hh i => (hu h hh i).trans hbound) hugrid
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hTC),
    m, hm, hin, hout, hRank.mono _ hTC, H', hsub, hnonempty, ?_, U.mono hTC, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hTC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    have hprecision : (W.family.vertical.lipBound : ℝ) * ε ≤ Real.exp (-(2 * P)) / 2 := by
      calc
        _ ≤ Real.exp P * ε := mul_le_mul_of_nonneg_right
          (W.family.vertical.lip_bound.trans (Real.exp_le_exp.mpr hpP)) hε.le
        _ = Real.exp (-(2 * P) - 2) := by
          dsimp only [ε, T]
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-(2 * P) - 1) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ _ := exp_sub_one_le_half_exp _
    obtain ⟨V⟩ := hcorr h (hsub hh)
    obtain ⟨V'⟩ := V.exists_of_uniform_approx
      (W.replacedRankResidual h (fun i x => (U.mono hTC).observable i (QuotientGroup.mk (b h x))))
      (fun ij x => (W.replacedRankResidual_norm_sub_le hF h _ _ ij x).trans
        ((happ h hh ij.2 (b h x)).trans hprecision))
    exact ⟨V'.mono hPC⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateSplitFreezing
namespace OAI

section

namespace Erdos3.NativeCoordinateSplit

open scoped TensorProduct

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra
  NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd
  NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

variable {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ] {i : σ} {s d : ℕ}
  {p epsilon : ℝ} {f : (σ → ℤ) → ℂ} (R : NativeCoordinateSplit i s d p epsilon f)

theorem first_eval_firstFactor (j : Fin R.count) (x : σ → ℤ) :
    (R.test false j).eval x = R.firstFactor j (x i) :=
  R.first_eval_eq j x (fun _ => x i) rfl

end Erdos3.NativeCoordinateSplit

end

section

namespace Erdos3.NativeCoordinateSplit

open Module RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra
  NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd
  NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

theorem exists_second_expansion_budget (σ : Type) [Fintype σ] [DecidableEq σ] [Nonempty σ]
    (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {i : σ} {d : ℕ} {p epsilon : ℝ} {f : (σ → ℤ) → ℂ}
      (R : NativeCoordinateSplit i s d p epsilon f) (j : Fin R.count) (b : σ → ℤ),
      ∃ E : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => (R.test true j).eval (Function.update b i (x ()))), E.count = 1 := by
  obtain ⟨C, hC, hfreeze⟩ := exists_controlled_frozen_niltest (∑ _ : σ, s)
  refine ⟨C, hC, ?_⟩
  intro i d p epsilon f R j b
  classical
  let S : Finset σ := {i}
  have hp : 0 ≤ p := (Nat.cast_nonneg (R.dim true)).trans (R.complexity true).1.1
  have hlip : ((R.test true j).lipBound : ℝ) ≤ Real.exp p := by
    have hb := (R.test true j).observable_budget (R.test_complexity true j)
    have hn := (R.test true j).normBound.coe_nonneg
    linarith
  have hub : ∀ x, ‖(R.test true j).observable x‖ ≤ (1 : ℝ) := fun x =>
    ((R.test true j).norm_le x).trans
      (show ((R.test true j).normBound : ℝ) ≤ 1 from R.test_norm true j)
  obtain ⟨E, _, _, hE⟩ := hfreeze (R.model true) (R.multi true) S b
    (R.orbit true) (R.test true j).observable (R.test true j).lipBound 1
    (R.test true j).lipschitz hub (R.complexity true) hlip
    (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)
  let K := (R.multi true).filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  obtain ⟨T, _, hT, _, hTeval⟩ := hE
  let U := T.affinePullback (fun _ (_ : Unit) => (1 : ℤ)) 0
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hval (x : Unit → ℤ) : U.eval x = (R.test true j).eval (Function.update b i (x ())) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, hTeval]
    unfold RationalFilteredNilmanifold.Niltest.eval
    rw [R.test_orbit true j, (R.multi true).orbitToOrdinary_eval]
    congr 2
    apply congrArg (fun z => (R.multi true).filtration.realification.polynomialOrbitEval z
      (R.orbit true))
    funext k
    by_cases hk : k = i
    · subst k
      simp [S, freezeCoordinates, integerAffineMap]
    · simp [S, freezeCoordinates, hk]
  have hdegree : multidegreeWeight (retainedCoordinateWeight S) (coordinateSplitBound s i true) =
      s - 1 := by
    rw [retainedCoordinate_degree]
    simp [S, coordinateSplitBound]
  have hresult : ∃ Q : NativeIntegerExpansion (fun _ : Unit => 1)
      (multidegreeWeight (retainedCoordinateWeight S) (coordinateSplitBound s i true))
      ((p + C) ^ C) (fun x => (R.test true j).eval (Function.update b i (x ()))), Q.count = 1 :=
    ⟨NativeIntegerExpansion.ofTest U hU (fun x => (hval x).symm), rfl⟩
  exact hdegree ▸ hresult

end Erdos3.NativeCoordinateSplit

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3.NativeMultilinearIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

noncomputable def rankProduct (t : B.quadruples) (n : ℤ) : ℂ :=
  fourPointProduct (W.family.eval B.rankCoordinate t.val.2.1)
    (W.family.eval B.rankCoordinate (t.val.2.1 - t.val.1))
    (W.family.eval B.rankCoordinate t.val.2.2)
    (W.family.eval B.rankCoordinate (t.val.2.2 - t.val.1)) (B.delta t) n

noncomputable def lowerProduct (t : B.quadruples) (n : ℤ) : ℂ :=
  fourPointProduct
    (B.lower.integerLower ⟨t.val.2.1, (B.interval t).first_mem⟩)
    (B.lower.integerLower ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩)
    (B.lower.integerLower ⟨t.val.2.2, (B.interval t).third_mem⟩)
    (B.lower.integerLower ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩) (B.delta t) n

noncomputable def residual (t : B.quadruples) (n : ℤ) : ℂ :=
  B.rankProduct t n * B.lowerProduct t n

end Erdos3.NativeMultilinearIntervalFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankRelationExistence
namespace OAI

section

namespace Erdos3

namespace NativeAnchoredRankFibers

variable {s r N : ℕ} [NeZero N] {b p : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim} {H : Finset (ZMod N)}
  {F : NativeWeightedRankIntervals W out H p} (A : NativeAnchoredRankFibers F)

theorem exists_interval_pairs (a : ZMod N) (ha : a ∈ A.parameters) :
    ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-(8 * p + 1)) * ((A.fiber a).card : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, Nonempty (NativeRankInterval W out H (a, t) A.branch
        (8 * p + 1) (mixedErrorPairBudget p)) := by
  classical
  obtain ⟨i₀, hi₀⟩ := A.fiber_nonempty a ha
  let : Nonempty (A.fiber a) := ⟨⟨i₀, hi₀⟩⟩
  obtain ⟨Q, hQ, hQsize, hpair⟩ := native_interval_weight_pairs W out a A.anchor
    (cyclicBranchOffset a A.branch) (fun i : A.fiber a => (F.index i.val).2.1)
    (fun i => F.start i.val) (fun i => F.length i.val) F.weight
    (fun i => F.lower i.val) (fun i => F.expansion i.val) F.budget_two F.weight_norm
    (fun i => F.endpoint_le i.val) (fun i => F.length_short i.val)
    (fun i => F.length_ratio i.val) (fun i => by
      simpa only [A.fiber_parameter a i, A.fiber_anchor a i, A.fiber_branch a i]
        using F.correlation i.val)
  let e : (A.fiber a × A.fiber a) ↪ ZMod N × ZMod N := {
    toFun := fun t => ((F.index t.1.val).2.1, (F.index t.2.val).2.1)
    inj' := by
      intro t u htu
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj htu
      exact Prod.ext (A.fiber_shift_injective a h₁) (A.fiber_shift_injective a h₂) }
  refine ⟨Q.map e, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hQ
    exact ⟨e t, Finset.mem_map.mpr ⟨t, ht, rfl⟩⟩
  · simpa only [Finset.card_map, Fintype.card_coe] using hQsize
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨c, len, hlen, hN, hshort, hsize, ⟨E⟩, hc⟩ := hpair u hu
    refine ⟨{
      first_mem := F.first_mem u.1.val
      second_mem := ?_
      third_mem := F.first_mem u.2.val
      fourth_mem := ?_
      integer_relation := ?_
      start := c
      length := len
      length_pos := hlen
      endpoint_le := hN
      length_short := hshort
      length_ratio := hsize
      lower := fun n => F.lower u.1.val n * star (F.lower u.2.val n)
      expansion := E
      correlation := hc }⟩
    · change (F.index u.1.val).2.1 - a ∈ H
      simpa only [A.fiber_parameter a u.1] using F.second_mem u.1.val
    · change (F.index u.2.val).2.1 - a ∈ H
      simpa only [A.fiber_parameter a u.2] using F.second_mem u.2.val
    · have h₁ := F.integer_relation u.1.val
      have h₂ := F.integer_relation u.2.val
      rw [A.fiber_parameter a u.1, A.fiber_anchor a u.1] at h₁
      rw [A.fiber_parameter a u.2, A.fiber_anchor a u.2] at h₂
      change -((F.index u.1.val).2.1.val : ℤ) + ((F.index u.1.val).2.1 - a).val +
        (F.index u.2.val).2.1.val - ((F.index u.2.val).2.1 - a).val = 0
      omega

end NativeAnchoredRankFibers

end Erdos3

end

section

namespace Erdos3

namespace NativeRankRelation

noncomputable def mono {s r N : ℕ} [NeZero N] {b p q p' q' : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} (R : NativeRankRelation W out H p q) (hp : p ≤ p') (hq : q ≤ q') :
    NativeRankRelation W out H p' q' :=
  { R with
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hp))
      (by positivity)).trans R.density
    interval := fun t => (R.interval t).mono hp hq }

end NativeRankRelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReducedSquareGradedKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))

theorem reducedSquareGradedDifference_relativePiece (j : ℕ) (hj : 1 ≤ j)
    (x : F.layer (j + 1)) :
    F.reducedSquareGradedDifference e ω hF (F.reducedSquareGradedRelativePiece j hj x) =
      F.associatedGradedPieceMap (j + 1) x := by
  change F.reducedSquareGradedDifference e ω hF
    (F.squareFiltration.quotientTopGradedMap
      (F.squareFiltration.associatedGradedPieceMap j (F.squareRelativeLayer j hj x))) = _
  rw [F.squareFiltration.quotientTopGradedMap_piece,
    ← F.squareFiltration.quotientTop.gradedPieceProjection_eq_pieceMap
      (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)]
  rw [F.reducedSquareGradedDifference_projection, F.reducedSquareDifference_mk]
  change F.gradedPieceProjection e ω hF (j + 1) ((x : L) - 0) = _
  rw [sub_zero, F.gradedPieceProjection_eq_pieceMap]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "bG" => F.associatedGradedBasis e ω hF

theorem layerOneGradedMap_pure (x : L ⧸ F.layer 2) :
    basisGradeProjection bG ω 1 (F.layerOneGradedMap e ω hF x) = F.layerOneGradedMap e ω hF x := by
  rw [← F.layerOneGradedMap_projection, F.gradedLayerOneProjection_rightInverse]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (R : ∀ i, (D i).DegreeRankStructure r)

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {w : σ → ℕ}

theorem productObservable_rank_vertical (T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (hvert : ∀ i z, z ∈ (R i).realSubgroup s r → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (z : (pi D).RealGroup) (hz : z ∈ (piRank D R).realSubgroup s r)
    (x : (pi D).Space) :
    productObservable D T (z • x) =
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) *
        productObservable D T x := by
  have hchar :
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) =
        ∏ i, CircleFourier.character
          ((realifyFunctional (eta i) (productProjectionHom D i z).coord : ℝ) : CircleFourier.Circle) := by
    rw [realify_piFrequency]
    have hcoe (f : ι → ℝ) : ((∑ i, f i : ℝ) : CircleFourier.Circle) =
        ∑ i, (f i : CircleFourier.Circle) :=
      map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ
    simp only [hcoe, CircleFourier.character_fintype_sum,
      productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord]
  rw [hchar, productObservable, productObservable, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_smul]
  exact hvert i _ (productProjectionHom_mem_rank D R i s r z hz) _

variable [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem piNiltest_rank_vertical (T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hvert : ∀ i z, z ∈ (R i).realSubgroup s r → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (z : (pi D).RealGroup) (hz : z ∈ (piRank D R).realSubgroup s r)
    (x : (pi D).Space) :
    (piNiltest D T hp hι hT).observable (z • x) =
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) *
        (piNiltest D T hp hι hT).observable x :=
  productObservable_rank_vertical D R T eta hvert z hz x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NativeDegreeRankFamily

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p)

theorem fourPointFactors_complexity (hp : 0 ≤ p) (out : Fin W.outputDim)
    (a : Fin 4 → A) (δ : ℤ) (i : Fin 4) :
    (W.fourPointFactors out a δ i).ComplexityLE (p + 4) := by
  fin_cases i
  · exact W.component_complexity hp out (a 0)
  · exact W.component_complexity hp out (a 1)
  · exact W.component_complexity hp out (a 2)
  · exact W.component_complexity hp out (a 3)

end Erdos3.NativeDegreeRankFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)
  (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)

theorem refilteredHorizontalImage_eq (d : ℕ) :
    I.refilteredHorizontalImage i U d =
      W.rank.filtration.horizontalImageOfSubmodule (I.refilteredProjectionImage i U d) d :=
  W.rank.filtration.layerHorizontalImage_eq_of_submodule
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U)
    (I.rankProjection i) (I.rankProjection_mem_refiltered i U) d

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

theorem refilteredProjectionImage_mem_candidates
    (R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r)
    (F : (piRank (I.productModels i) (I.productRanks i R₀)).AdaptedData)
    (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)
    (v : Fin (finrank ℚ (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) →
      (pi (I.productModels i)).filtration.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {P : ℝ} (hP : 0 ≤ P) (hF : F.rank.ComplexityLE P)
    (hforward : ∀ j k, rationalLogHeight ((pi (I.productModels i)).basis.repr (F.basis j) k) ≤ P)
    (hv : ∀ j k, rationalLogHeight
      (((pi (I.productModels i)).filtration.associatedGradedBasis F.basis F.weight F.layers).repr
        (v j) k) ≤ P) (d : ℕ) :
    I.refilteredProjectionImage i U d ∈
      heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
        ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ := by
  have hdim : (Fintype.card (Fin (finrank ℚ (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))) : ℝ) ≤ P := by
    simpa only [Fintype.card_fin] using hF.1.1
  obtain ⟨a, ha⟩ := (pi (I.productModels i)).filtration.exists_refiltration_bases_in_coordinates
    F.basis F.weight F.layers (pi (I.productModels i)).basis U v hspan hP hdim hdim hv hforward d
  let z := fun j => I.rankProjection i (a j).val
  have hz : Submodule.span ℚ (Set.range z) = I.refilteredProjectionImage i U d := by
    have hsource := span_submodule_basis ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U d) a
    calc
      _ = (Submodule.span ℚ (Set.range (fun j => (a j).val))).map (I.rankProjection i).toLinearMap := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = _ := congrArg (fun K => K.map (I.rankProjection i).toLinearMap) hsource
  apply bounded_submodule_spanning_mem_candidates W.fourRankBasis _ z hz
    (one_le_ceil_exp (refiltrationCoordinateBudget P))
  intro j k
  apply rationalHeightLE_ceil_exp
  exact I.rankProjection_coordinates_logHeight i (a j).val (ha j) k

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}

namespace SunflowerWitness

variable {I : NativeRankInterval W out H t branch p q} {P : ℝ} (D : I.SunflowerWitness P)

theorem projection_mem_candidates (hP : 0 ≤ P) (d : ℕ) :
    D.projection d ∈ heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
      ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ :=
  I.refilteredProjectionImage_mem_candidates D.index D.lowerRank D.adapted D.subalgebra
    D.spanning D.span hP D.adapted_complexity D.forward D.height d

theorem horizontalImage_eq (d : ℕ) :
    I.refilteredHorizontalImage D.index D.subalgebra d =
      W.rank.filtration.horizontalImageOfSubmodule (D.projection d) d :=
  I.refilteredHorizontalImage_eq D.index D.subalgebra d

end SunflowerWitness

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_common_rank_projection_family
    {α : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {t : α → ZMod N × ZMod N × ZMod N} {branch : Bool}
    (I : ∀ a, NativeRankInterval W out H (t a) branch p q)
    (S : Finset α) (hS : S.Nonempty) (hP : 0 ≤ P)
    (D : ∀ a ∈ S, (I a).SunflowerWitness P) :
    ∃ (K : Fin (s + 1) → Submodule ℚ (Fin 4 → W.L)) (T : Finset α),
      T ⊆ S ∧ T.Nonempty ∧
      Real.exp (-(3 * (Fintype.card (Σ _ : Fin 4, Fin W.dim) : ℝ) *
        Fintype.card (Σ _ : Fin 4, Fin W.dim) * (refiltrationCoordinateBudget P + 2)) * (s + 1)) *
        S.card ≤ (T.card : ℝ) ∧
      (∀ d, K d ∈ heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
        ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊) ∧
      ∀ a ∈ T, ∃ E : (I a).SunflowerWitness P,
        (∀ d : Fin (s + 1), E.projection d.val = K d) ∧
        ∀ d : Fin (s + 1), (I a).refilteredHorizontalImage E.index E.subalgebra d.val =
          W.rank.filtration.horizontalImageOfSubmodule (K d) d.val := by
  classical
  let code (a : α) : Fin (s + 1) → Submodule ℚ (Fin 4 → W.L) :=
    if ha : a ∈ S then fun d => (D a ha).projection d.val else 0
  have hcode (a : α) (ha : a ∈ S) : code a = fun d => (D a ha).projection d.val := by
    simp only [code, dif_pos ha]
  have hmem : ∀ a ∈ S, ∀ d, code a d ∈
      heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
        ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ := by
    intro a ha d
    rw [hcode a ha]
    exact (D a ha).projection_mem_candidates hP d.val
  obtain ⟨a₀, ha₀, T, hTS, haT, hcommon, hsize⟩ := exists_common_height_bounded_subspace_family
    W.fourRankBasis S hS code (Fintype.card (Σ _ : Fin 4, Fin W.dim))
    (refiltrationCoordinateBudget_nonneg hP) hmem
  refine ⟨code a₀, T, hTS, ⟨a₀, haT⟩, ?_, hmem a₀ ha₀, ?_⟩
  · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hsize
  · intro a ha
    let E := D a (hTS ha)
    have heq (d : Fin (s + 1)) : E.projection d.val = code a₀ d := by
      have h := congrFun (hcommon a ha) d
      rwa [hcode a (hTS ha)] at h
    exact ⟨E, heq, fun d => (E.horizontalImage_eq d.val).trans (congrArg
      (fun B => W.rank.filtration.horizontalImageOfSubmodule B d.val) (heq d))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
namespace OAI

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankRelation

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)}

namespace CommonData

variable {R : NativeRankRelation W out H p q} {P Q : ℝ} (D : R.CommonData P)

noncomputable def mono (hPQ : P ≤ Q) : R.CommonData Q :=
  { D with
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hPQ))
      (by positivity)).trans D.density
    witness := fun t ht => (D.witness t ht).mono hPQ
    projection := fun t ht d => D.projection t ht d }

end CommonData

end NativeRankRelation

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def horizontal (d : Fin (s + 1)) :
    Submodule ℚ (Fin 4 → W.rank.filtration.HigherHorizontal d.val) :=
  W.rank.filtration.horizontalImageOfSubmodule (D.spaces d) d.val

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFreeSunflower
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def commonCoefficientSpace (d : Fin (s + 1)) : Submodule ℚ W.L :=
  W.rank.filtration.horizontalPreimage d.val (fourFirstProjection (D.horizontal d))

noncomputable def dependentCoefficientSpace (d : Fin (s + 1)) : Submodule ℚ W.L :=
  W.rank.filtration.horizontalPreimage d.val (fourDependentProjection (D.horizontal d))

theorem commonCoefficientSpace_le (d : Fin (s + 1)) :
    D.commonCoefficientSpace d ≤ W.rank.filtration.layer d.val 1 :=
  W.rank.filtration.horizontalPreimage_le d.val _

theorem dependentCoefficientSpace_le_common (d : Fin (s + 1)) :
    D.dependentCoefficientSpace d ≤ D.commonCoefficientSpace d :=
  W.rank.filtration.horizontalPreimage_mono d.val (fourDependentProjection_le _)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

structure CoefficientBases (Q : ℝ) where
  common : ∀ d : Fin s, Basis
    (Fin (finrank ℚ (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩))) ℚ
    (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩)
  dependent : ∀ d : Fin s, Basis
    (Fin (finrank ℚ (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩))) ℚ
    (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩)
  common_height : ∀ d i j, rationalLogHeight (W.model.basis.repr (common d i : W.L) j) ≤ Q
  dependent_height : ∀ d i j, rationalLogHeight (W.model.basis.repr (dependent d i : W.L) j) ≤ Q

def CoefficientAlphabet : Type :=
  (Σ d : Fin s, Fin (finrank ℚ (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩))) ⊕
    (Σ d : Fin s, Fin (finrank ℚ (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩)))

noncomputable instance coefficientAlphabetFintype : Fintype D.CoefficientAlphabet := by
  unfold CoefficientAlphabet
  infer_instance

def coefficientDegree : D.CoefficientAlphabet → Fin (s + 1) :=
  Sum.elim (fun x => ⟨x.1.val + 1, by omega⟩) (fun x => ⟨x.1.val + 1, by omega⟩)

def coefficientWeight (x : D.CoefficientAlphabet) : ℕ := (D.coefficientDegree x).val

theorem coefficientWeight_pos (x : D.CoefficientAlphabet) : 0 < D.coefficientWeight x := by
  cases x with
  | inl x => exact Nat.zero_lt_succ _
  | inr x => exact Nat.zero_lt_succ _

noncomputable def CoefficientBases.generator {Q : ℝ} (B : D.CoefficientBases Q) :
    D.CoefficientAlphabet → W.L :=
  Sum.elim (fun x => (B.common x.1 x.2 : W.L)) (fun x => (B.dependent x.1 x.2 : W.L))

theorem CoefficientBases.generator_mem_common {Q : ℝ} (B : D.CoefficientBases Q)
    (x : D.CoefficientAlphabet) :
    B.generator D x ∈ D.commonCoefficientSpace (D.coefficientDegree x) := by
  cases x with
  | inl x => exact (B.common x.1 x.2).property
  | inr x => exact D.dependentCoefficientSpace_le_common _ (B.dependent x.1 x.2).property

theorem CoefficientBases.generator_mem_layer {Q : ℝ} (B : D.CoefficientBases Q)
    (x : D.CoefficientAlphabet) :
    B.generator D x ∈ W.rank.filtration.layer (D.coefficientWeight x) 0 := by
  rw [W.rank.filtration.rank_zero_eq_one]
  exact D.commonCoefficientSpace_le _ (B.generator_mem_common D x)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def coefficientFourSpace (d : Fin (s + 1)) : Submodule ℚ (Fin 4 → W.L) :=
  ((D.horizontal d).comap (W.rank.filtration.fourHorizontalMap d.val)).map
    (W.rank.filtration.fourHorizontalLayer d.val).subtype

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

abbrev CoefficientFreeLieAlgebra :=
  FreeDegreeRankLieAlgebra D.CoefficientAlphabet s r D.coefficientWeight D.coefficientWeight_pos

noncomputable def coefficientFreeFiltration : DegreeRankLieFiltration D.CoefficientFreeLieAlgebra s r :=
  FreeDegreeRankLieAlgebra.filtration D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos W.rank.filtration.rank_le_degree

noncomputable def coefficientFreeGenerator (x : D.CoefficientAlphabet) : D.CoefficientFreeLieAlgebra :=
  FreeDegreeRankLieAlgebra.of D.CoefficientAlphabet s r D.coefficientWeight D.coefficientWeight_pos x

noncomputable def commonFreeSpan (d : Fin s) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  Submodule.span ℚ (Set.range (fun i => D.coefficientFreeGenerator (Sum.inl ⟨d, i⟩)))

noncomputable def dependentFreeSpan (d : Fin s) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  Submodule.span ℚ (Set.range (fun i => D.coefficientFreeGenerator (Sum.inr ⟨d, i⟩)))

variable {Q : ℝ} (B : D.CoefficientBases Q)

noncomputable def CoefficientBases.freeEvaluation : D.CoefficientFreeLieAlgebra →ₗ⁅ℚ⁆ W.L :=
  FreeDegreeRankLieAlgebra.lift W.rank.filtration D.coefficientWeight D.coefficientWeight_pos
    (B.generator D) (B.generator_mem_layer D)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

noncomputable def CoefficientBases.freeFrequency : D.CoefficientFreeLieAlgebra →ₗ[ℚ] ℚ :=
  W.vertical.frequency.comp (B.freeEvaluation D).toLinearMap

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def coefficientFreeSpan (d : Fin s) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  D.commonFreeSpan d ⊔ D.dependentFreeSpan d

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCorrelatedFactorFamily
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem exists_native_shared_frozen_orbit_correlations (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p P : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      0 ≤ P → p ≤ P → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp P →
      ∀ (H : Finset (ZMod N))
        (ε γ b : ZMod N → W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (y : ZMod N → ZMod N), H.Nonempty →
      (∀ h ∈ H, CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P + 2) ^ k)) (ε h).log) →
      (∀ h ∈ H, CoefficientGrid (W.family.model.basis.baseChange ℝ) q (γ h).log) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N P
        (W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε h) (b h) (γ h) (y h) x)))) →
      ∃ Λ : Subgroup W.family.model.filtration.Group, Λ ≤ W.family.model.lattice ∧
        (Λ.subgroupOf W.family.model.lattice).Characteristic ∧
        (Λ.subgroupOf W.family.model.lattice).Normal ∧
        (Λ.subgroupOf W.family.model.lattice).FiniteIndex ∧
        (Λ.relIndex W.family.model.lattice : ℝ) ≤ Real.exp ((P + C) ^ C) ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates W.family.model.basis Λ)
          (hout : bchSubgroupCoordinates W.family.model.basis Λ ⊆ denominatorGrid m),
          (W.family.rank.withLattice Λ m hm hin hout).ComplexityLE ((P + C) ^ C) ∧
          ∃ H' : Finset (ZMod N), H' ⊆ H ∧ H'.Nonempty ∧
            Real.exp (-((P + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
            ∃ U : (W.family.model.withLattice Λ m hm hin hout).UnitVerticalObservable
                ((W.family.rank.withLattice Λ m hm hin hout).realSubgroup s r)
                (Fin W.family.outputDim) ((P + C) ^ C),
              U.frequency = W.family.vertical.frequency ∧
              ∀ h ∈ H', Nonempty (NativeVectorCorrelation (s - 1) N ((P + C) ^ C)
                (W.replacedRankResidual h (fun i x => U.observable i (QuotientGroup.mk
                  (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (b h)))))) := by
  obtain ⟨a₀, _, hconstants⟩ := exists_bounded_frozen_constants s k
  obtain ⟨b₀, _, hshared⟩ := exists_native_shared_frozen_correlations s 1
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a₀) ^ a₀ + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C b₀) ^ b₀)
  refine ⟨C, hC, ?_⟩
  intro r N _ p P F W hF hP hpP q hq hqP H ε γ b y hH hε hγ hcorr
  classical
  let T := P + (P + a₀) ^ a₀ + 2
  have hA : 0 ≤ (P + a₀) ^ a₀ := by positivity
  have hPT : P ≤ T := by dsimp only [T]; linarith
  have hAT : (P + a₀) ^ a₀ ≤ T := by dsimp only [T]; linarith
  have hT : 0 ≤ T := hP.trans hPT
  have hsum : T + (T + b₀) ^ b₀ ≤ (P + C) ^ C := by
    simpa [Q, T, Polynomial.eval₂_pow] using hbudget P hP
  have hTC : (T + b₀) ^ b₀ ≤ (P + C) ^ C := by linarith
  obtain ⟨l, hl, hlbound, hsolve⟩ := hconstants (N := N) W.family.model P hP
    (W.family.complexity.1.mono _ hpP) q hq hqP
  have hreps (h : {h // h ∈ H}) := (hsolve (ε h) (γ h) (hε h h.property) (hγ h h.property) (y h)).2
  choose u hu hugrid δ hδ heq using hreps
  let u' (h : ZMod N) : W.family.model.RealGroup := if hh : h ∈ H then u ⟨h, hh⟩ else 1
  let a (h : ZMod N) := W.family.model.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => ((y h).val : ℤ)) (ε h)
  let b' (h x : ZMod N) := W.family.model.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (b h)
  have hbound : Real.exp ((P + a₀) ^ a₀) ≤ Real.exp ((T + 2) ^ 1) :=
    Real.exp_le_exp.mpr (by simp only [pow_one]; linarith)
  have ha (h : ZMod N) (hh : h ∈ H) (i : Fin W.family.dim) :
      |(W.family.model.basis.baseChange ℝ).repr (a h).coord i| ≤ Real.exp ((T + 2) ^ 1) :=
    ((hsolve (ε h) (γ h) (hε h hh) (hγ h hh) (y h)).1 i).trans hbound
  have hu' (h : ZMod N) (hh : h ∈ H) (i : Fin W.family.dim) :
      |(W.family.model.basis.baseChange ℝ).repr (u' h).coord i| ≤ Real.exp ((T + 2) ^ 1) := by
    simpa only [u', dif_pos hh] using (hu ⟨h, hh⟩ i).trans hbound
  have hugrid' (h : ZMod N) (hh : h ∈ H) :
      (W.family.model.basis.baseChange ℝ).equivFun (u' h).coord ∈ realDenominatorGrid l := by
    simpa only [u', dif_pos hh] using hugrid ⟨h, hh⟩
  have hc (h : ZMod N) (hh : h ∈ H) : Nonempty (NativeVectorCorrelation (s - 1) N T
      (W.replacedRankResidual h (fun i x => W.family.vertical.observable i
        (QuotientGroup.mk (a h * b' h x * u' h))))) := by
    have hfun : (fun i x => W.family.vertical.observable i (QuotientGroup.mk (a h * b' h x * u' h))) =
        (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε h) (b h) (γ h) (y h) x) := by
      funext i x
      change W.family.vertical.observable i (QuotientGroup.mk (a h * b' h x * u' h)) =
        W.family.vertical.observable i (QuotientGroup.mk (a h * b' h x *
          W.family.model.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => ((y h).val : ℤ)) (γ h)))
      rw [heq ⟨h, hh⟩]
      simp only [u', dif_pos hh]
      exact congrArg (W.family.vertical.observable i)
        (right_lattice_factor_mk_eq W.family.model.realLattice (a h) (b' h x) (u ⟨h, hh⟩)
          (δ ⟨h, hh⟩) (hδ ⟨h, hh⟩)).symm
    rw [hfun]
    exact ⟨(Classical.choice (hcorr h hh)).mono hPT⟩
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout,
      hRank, H', hsub, hnonempty, hdense, U, hfreq, hU⟩ :=
    hshared W hF hT (hpP.trans hPT) l hl
      (hlbound.trans (Real.exp_le_exp.mpr hAT)) H a u' b' hH ha hu' hugrid' hc
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hTC),
    m, hm, hin, hout, hRank.mono _ hTC, H', hsub, hnonempty, ?_, U.mono hTC, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hTC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact ⟨(Classical.choice (hU h hh)).mono hTC⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem exists_shared_factor_correlations (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p P : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      2 ≤ P → p ≤ P → ∀ (m M : ℕ), 0 < m → (m : ℝ) ≤ Real.exp P →
      0 < M → (M : ℝ) ≤ Real.exp P →
      ∀ (J : Finset (ZMod N)), J ⊆ W.shifts → J.Nonempty →
      ∀ ε a ρ : ZMod N → W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      (∀ h ∈ J, ε h * a h * ρ h = W.family.orbit h) →
      (∀ h ∈ J, CoefficientBound (W.family.model.basis.baseChange ℝ)
        (fun _ : Unit => (N : ℝ)) (Real.exp ((P + 2) ^ 1)) (ε h).log) →
      (∀ h ∈ J, CoefficientGrid (W.family.model.basis.baseChange ℝ) m (ρ h).log) →
      (∀ h ∈ J, ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
        (QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) x (ρ h)) : W.family.model.Space) =
        QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) y (ρ h))) →
      Real.exp ((P + C) ^ C) ≤ (N : ℝ) →
      ∃ Λ : Subgroup W.family.model.filtration.Group, Λ ≤ W.family.model.lattice ∧
        (Λ.subgroupOf W.family.model.lattice).Characteristic ∧
        (Λ.subgroupOf W.family.model.lattice).Normal ∧
        (Λ.subgroupOf W.family.model.lattice).FiniteIndex ∧
        (Λ.relIndex W.family.model.lattice : ℝ) ≤ Real.exp ((P + C) ^ C) ∧
        ∃ (l : ℕ) (hl : 0 < l)
          (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates W.family.model.basis Λ)
          (hout : bchSubgroupCoordinates W.family.model.basis Λ ⊆ denominatorGrid l),
          (W.family.rank.withLattice Λ l hl hin hout).ComplexityLE ((P + C) ^ C) ∧
          ∃ J' : Finset (ZMod N), J' ⊆ J ∧ J'.Nonempty ∧
            Real.exp (-((P + C) ^ C)) * J.card ≤ (J'.card : ℝ) ∧
            ∃ V : (W.family.model.withLattice Λ l hl hin hout).UnitVerticalObservable
                ((W.family.rank.withLattice Λ l hl hin hout).realSubgroup s r)
                (Fin W.family.outputDim) ((P + C) ^ C),
              V.frequency = W.family.vertical.frequency ∧
              ∀ h ∈ J', Nonempty (NativeVectorCorrelation (s - 1) N ((P + C) ^ C)
                (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
                  (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (a h)))))) := by
  obtain ⟨b, _, hfreeze⟩ := exists_native_frozen_rank_correlation s 1 hs
  obtain ⟨c, _, hshared⟩ := exists_native_shared_frozen_orbit_correlations s 1
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C b) ^ b + Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (B + (B + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ p P f W hf hP hpP m M hm hmP hM hMP J hJW hJ ε a ρ hprod hε hρ hperiod hN
  classical
  let P₁ := (P + b) ^ b + P + 2
  have hP0 : 0 ≤ P := by linarith
  have hb0 : 0 ≤ (P + b) ^ b := by positivity
  have hP₁ : 0 ≤ P₁ := by dsimp only [P₁]; positivity
  have hPP₁ : P ≤ P₁ := by dsimp only [P₁]; linarith
  have hbP₁ : (P + b) ^ b ≤ P₁ := by dsimp only [P₁]; linarith
  have hsum : P₁ + (P₁ + c) ^ c ≤ (P + C) ^ C := by
    simpa [P₁, B, Polynomial.eval₂_pow] using hbudget P hP0
  have hP₁C : P₁ ≤ (P + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P₁ + c) ^ c)).trans hsum
  have hcC : (P₁ + c) ^ c ≤ (P + C) ^ C := (le_add_of_nonneg_left hP₁).trans hsum
  have hchoose (h : {h // h ∈ J}) : ∃ y : ZMod N,
      Nonempty (NativeVectorCorrelation (s - 1) N P₁
        (W.replacedRankResidual h.val (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε h.val) (a h.val) (ρ h.val) y x))) := by
    obtain ⟨y, _, hy⟩ := hfreeze W hf ⟨h.val, hJW h.property⟩ P hP hpP M hM hMP
      (ε h.val) (a h.val) 1 (ρ h.val) (by simpa only [mul_one] using hprod h.val h.property)
      (hε h.val h.property) (hperiod h.val h.property)
      ((Real.exp_le_exp.mpr (hbP₁.trans hP₁C)).trans hN)
    refine ⟨y, ?_⟩
    simpa only [mul_one] using
      (show Nonempty _ from ⟨(Classical.choice hy).mono hbP₁⟩)
  choose y hy using hchoose
  let y' (h : ZMod N) := if hh : h ∈ J then y ⟨h, hh⟩ else 0
  have hcorr (h : ZMod N) (hh : h ∈ J) :
      Nonempty (NativeVectorCorrelation (s - 1) N P₁
        (W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε h) (a h) (ρ h) (y' h) x))) := by
    simpa only [y', dif_pos hh] using hy ⟨h, hh⟩
  have hε' (h : ZMod N) (hh : h ∈ J) :
      CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P₁ + 2) ^ 1)) (ε h).log :=
    CoefficientBound.mono _ _ (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (hε h hh)
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using (show P + 2 ≤ P₁ + 2 by linarith)))
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
      hRank, J', hsub, hnonempty, hdense, V, hfreq, hV⟩ :=
    hshared W hf hP₁ (hpP.trans hPP₁) m hm
      (hmP.trans (Real.exp_le_exp.mpr hPP₁)) J ε ρ a y' hJ hε' hρ hcorr
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcC),
    l, hl, hin, hout, hRank.mono _ hcC, J', hsub, hnonempty, ?_, V.mono hcC, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact ⟨(Classical.choice (hV h hh)).mono hcC⟩

noncomputable def sharedFactorCorrelationConstant (s : ℕ) (hs : 2 ≤ s) : ℕ :=
  (exists_shared_factor_correlations s hs).choose

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BinaryLowerRankFamily
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (T : D.DegreeRankStructure r) {p : ℝ}
  (V : D.UnitVerticalObservable (T.realSubgroup s r) I p)

theorem rank_invariant_of_frequency_zero
    (hzero : ∀ x ∈ T.filtration.layer s r, V.frequency x = 0)
    (z : D.RealGroup) (hz : z ∈ T.realSubgroup s r) (i : I) (x : D.Space) :
    V.observable i (z • x) = V.observable i x := by
  have hle : T.filtration.layer s r ≤ V.frequency.ker := hzero
  have hr : realifyFunctional V.frequency z.coord = 0 :=
    (mem_realified_frequency_kernel_iff V.frequency z.coord).mp
      (Submodule.baseChange_mono ℝ hle hz)
  rw [V.vertical i z hz x, hr, AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

section Coordinates

variable {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p)

noncomputable def coordinateNiltest {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i : I) : D.Niltest w where
  orbit := g
  observable := V.observable i
  normBound := 1
  lipBound := V.lipBound
  norm_le := V.norm i
  lipschitz := V.lipschitz i

theorem coordinateNiltest_complexity {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i : I)
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    (V.coordinateNiltest g i).ComplexityLE (p + 4) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + (V.lipBound : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp p := by nlinarith [V.lip_bound, Real.one_le_exp hp]
    _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Coordinates

theorem exists_lower_rank_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {r d : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure (r + 1))
      {p : ℝ} (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
      {w : σ → ℕ} (g : D.filtration.realification.PolynomialOrbit w),
      0 ≤ p → R.ComplexityLE p →
      (∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = 0) →
      ∃ n : ℕ, n ≤ d ∧
        ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
          ∃ U : Q.DegreeRankStructure r,
            ∃ hQF : Q.filtration = D.filtration.quotientLie
                (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal,
              U.filtration = R.filtration.quotientRank r (Nat.le_of_succ_le R.filtration.rank_le_degree) ∧
              Q.lattice = D.lattice.map (D.filtration.quotientStepHom
                (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal) ∧
              U.ComplexityLE ((p + C) ^ C) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
                 IsModuleTopology.topologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 Q.basis
               ∃ S : I → Q.Niltest w,
                 (∀ i, (S i).orbit = R.rankQuotientOrbit Q hQF g) ∧
                 (∀ i, (S i).normBound = 1) ∧
                 (∀ i, (S i).ComplexityLE ((p + C) ^ C)) ∧
                 (∀ y : Q.Space, ∑ i, ‖(S i).observable y‖ ^ 2 = 1) ∧
                 (∀ i x, (S i).observable (QuotientGroup.mk
                   (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                     (hM := Q.filtration.lowerCentralSeries_eq_bot)
                     (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x)) =
                   V.observable i (QuotientGroup.mk x)) ∧
                 ∀ i x, (S i).eval x = V.observable i
                   (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g))) := by
  obtain ⟨a, _, hdescent⟩ := DegreeRankStructure.exists_rankInvariant_niltest_budget s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 7) ^ 11
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C a) ^ a + P)
  refine ⟨C, hC, ?_⟩
  intro L I σ _ _ _ _ _ _ _ r d D R p V w g hp hR hzero
  let q := (p + 7) ^ 11
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hp4q : p + 4 ≤ q := by
    apply (show p + 4 ≤ p + 7 by linarith).trans
    exact (pow_one (p + 7)).symm.le.trans
      (pow_le_pow_right₀ (by linarith) (by decide : 1 ≤ 11))
  have hbudget' : (q + a) ^ a + q ≤ (p + C) ^ C := by
    simpa [q, P, X, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (q + a) ^ a)).trans hbudget'
  have haC : (q + a) ^ a ≤ (p + C) ^ C := (le_add_of_nonneg_right hq).trans hbudget'
  obtain ⟨n, hn, Q, U, hU, hQF, hQL, hUc, he⟩ := R.exists_controlled_lower_rank_quotient hp hR
  have h11 : (p + 3) ^ 11 ≤ q := pow_le_pow_left₀ (by positivity) (by linarith) 11
  have h5 : (p + 3) ^ 5 ≤ q :=
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + 3) (by decide : 5 ≤ 11)).trans h11
  have hUq : U.ComplexityLE q := hUc.mono U h11
  refine ⟨n, hn, Q, U, hQF, hU, hQL, hUq.mono U hqC, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  have htests := fun i => hdescent R Q hQF hQL (V.coordinateNiltest g i) q hq
    ((V.coordinateNiltest_complexity g i hp hR.1).mono hp4q) hUq.1
    (fun i j => (he j i).trans h5)
    (fun z hz x => V.rank_invariant_of_frequency_zero R hzero z hz i x)
  choose S hSo hSn hSc hSp hSe using htests
  refine ⟨S, hSo, hSn, (fun i => (hSc i).mono haC), ?_, hSp, hSe⟩
  intro y
  induction y using Quotient.inductionOn with
  | h y =>
    obtain ⟨x, hx⟩ := D.filtration.realQuotientStepHom_surjective
      (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal y
    have heq : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x = y := hx
    rw [← heq]
    simpa only [hSp, coordinateNiltest] using V.unit (QuotientGroup.mk x)

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

def HasLowerRankOrbitFamily {L I σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure (r + 1))
    (w : σ → ℕ) (f : τ → I → (σ → ℤ) → ℂ) (p : ℝ) : Prop :=
  ∃ n : ℕ, n ≤ d ∧
    ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
      ∃ U : Q.DegreeRankStructure r, U.ComplexityLE p ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
           IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 Q.basis
         ∃ K : I → Q.Niltest w,
           (∀ i, (K i).normBound = 1) ∧ (∀ i, (K i).ComplexityLE p) ∧
           (∀ y : Q.Space, ∑ i, ‖(K i).observable y‖ ^ 2 = 1) ∧
           ∃ a : τ → Q.filtration.realification.PolynomialOrbit w,
             (∀ t, Q.filtration.realification.polynomialOrbitEval w 0 (a t) = 1) ∧
             ∀ t i x, ((K i).withOrbit (a t)).eval x = f t i x)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredQuotientCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M I : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] {s t d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup E.RealGroup} {p : ℝ} (V : E.UnitVerticalObservable T I p)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
  (S : Subgroup D.RealGroup)
  (hS : S ≤ T.comap (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
  (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
  (hentries : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p)

noncomputable def controlledPullback :
    D.UnitVerticalObservable S I (p + (p + 3) ^ 2 + (p + 2) ^ 4) :=
  V.pullback φ hφ S hS ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
    (D.nativeSpaceMap_lipschitz E φ hφ hp hD hE hentries)
    (by
      change (V.lipBound : ℝ) * Real.exp ((p + 3) ^ 2) ≤ _
      calc
        _ ≤ Real.exp p * Real.exp ((p + 3) ^ 2) :=
          mul_le_mul_of_nonneg_right V.lip_bound (Real.exp_pos _).le
        _ = Real.exp (p + (p + 3) ^ 2) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity)))
    (by
      intro i
      exact (rational_functional_value_logHeight E.basis V.frequency hp
        (by simpa only [Fintype.card_fin] using hE.1) V.height (φ (D.basis i))
        (fun j => hentries j i)).trans
          (le_add_of_nonneg_left (add_nonneg hp (sq_nonneg (p + 3)))))

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_native_free_evaluation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X L : Type*) [Fintype X] [LieRing L] [LieAlgebra ℚ L]
      (r d : ℕ) (hr : r ≤ s) (D : RationalFilteredNilmanifold L s d)
      (R : D.DegreeRankStructure r) (w : X → ℕ) (hw : ∀ x, 0 < w x)
      (f : X → L) (hf : ∀ x, f x ∈ R.filtration.layer (w x) 0)
      (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p → R.ComplexityLE p →
      (∀ x i, rationalLogHeight (D.basis.repr (f x) i) ≤ p) →
      ∃ E : RationalFilteredNilmanifold (FreeDegreeRankLieAlgebra X s r w hw) s
          (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw)),
        ∃ Q : E.DegreeRankStructure r,
          Q.filtration = FreeDegreeRankLieAlgebra.filtration X s r w hw hr ∧
          Q.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
          (∀ i j, rationalLogHeight (D.basis.repr
            (FreeDegreeRankLieAlgebra.lift R.filtration w hw f hf (E.basis j)) i) ≤ (p + C) ^ C) ∧
          E.lattice ≤ D.lattice.comap (mapOfSteps
            (hL := E.filtration.lowerCentralSeries_eq_bot) (hM := D.filtration.lowerCentralSeries_eq_bot)
            (FreeDegreeRankLieAlgebra.lift R.filtration w hw f hf)) := by
  obtain ⟨a, _, hfree⟩ := exists_free_degree_rank_nilmanifold s
  obtain ⟨c, _, hcover⟩ := RationalFilteredNilmanifold.exists_native_source_cover
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q₀ := Polynomial.X + B₀
  let V₀ := ((Q₀ + 3) ^ (6 * s + 2) + Q₀ + 2) ^ 4
  let P₀ := Q₀ + V₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (P₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ r d hr D R w hw f hf p hp hX hR hfH
  let B := (p + a) ^ a
  let q := p + B
  let v := ((q + 3) ^ (6 * s + 2) + q + 2) ^ 4
  let P := q + v
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpq : p ≤ q := le_add_of_nonneg_right hB
  have hBq : B ≤ q := le_add_of_nonneg_left hp
  have hq : 0 ≤ q := hp.trans hpq
  have hqP : q ≤ P := le_add_of_nonneg_right (by dsimp only [v]; positivity)
  have hvP : v ≤ P := le_add_of_nonneg_left hq
  have hP : 0 ≤ P := hq.trans hqP
  have hsum : P + (P + c) ^ c ≤ (p + C) ^ C := by
    simpa [B₀, Q₀, V₀, P₀, B, q, v, P, Polynomial.eval₂_pow] using hbudget p hp
  have hPC : P ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P + c) ^ c)).trans hsum
  have hcoverC : (P + c) ^ c ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans hsum
  have hBC : B ≤ (p + C) ^ C := hBq.trans (hqP.trans hPC)
  obtain ⟨E₀, Q, hQ, hQcomplex, hcentral, _, _, htree, e, he, hdim, S, hS, hSH⟩ :=
    hfree X r hr w hw 1 (by decide) p hp hX
      (by simpa only [Nat.cast_one, Real.exp_zero] using Real.exp_le_exp.mpr hp)
  let φ := FreeDegreeRankLieAlgebra.lift R.filtration w hw f hf
  have hφ (i j) : rationalLogHeight (D.basis.repr (φ (E₀.basis j)) i) ≤ v := by
    have h := FreeDegreeRankLieAlgebra.lift_basis_matrix_logHeight R.filtration w hw f hf e he
      E₀.basis D.basis S hS hq (hdim.trans hBq)
      (by simpa only [Fintype.card_fin] using hR.1.1.trans hpq)
      (fun i j => (hSH i j).trans hBq)
      (fun i j k => (hR.1.2.2.1 i j k).trans hpq)
      (fun x i => (hfH x i).trans hpq) i j
    rw [LinearMap.toMatrix_apply] at h
    exact h
  obtain ⟨Λ, _, _, _, _, _, N, hN, hin, hout, hgeom, hmap⟩ :=
    hcover E₀ D φ hP (hQcomplex.1.mono E₀ (hBq.trans hqP))
      (hR.1.mono D (hpq.trans hqP)) (fun i j => (hφ i j).trans hvP)
  refine ⟨E₀.withLattice Λ N hN hin hout, Q.withLattice Λ N hN hin hout, hQ, ?_,
    hcentral, ⟨{
      tree_height := fun x hx i => (htree x hx i).trans hBC
      sourceBasis := e
      sourceBasis_trees := he
      sourceDimension := hdim.trans hBC
      sectionMatrix := S
      section_right_inverse := hS
      section_height := fun i j => (hSH i j).trans hBC
    }⟩, fun i j => (hφ i j).trans (hvP.trans hPC), hmap⟩
  exact Q.withLattice_complexity Λ N hN hin hout hQcomplex hBC
    (hgeom.mono _ hcoverC)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_free_unit_observable (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X L I : Type*) [Fintype X] [Fintype I]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (r d : ℕ) (hr : r ≤ s) (D : RationalFilteredNilmanifold L s d)
      (R : D.DegreeRankStructure r) (w : X → ℕ) (hw : ∀ x, 0 < w x)
      (f : X → L) (hf : ∀ x, f x ∈ R.filtration.layer (w x) 0)
      (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p → R.ComplexityLE p →
      (∀ x i, rationalLogHeight (D.basis.repr (f x) i) ≤ p) →
      ∀ U : D.UnitVerticalObservable (R.realSubgroup s r) I p,
      let φ := FreeDegreeRankLieAlgebra.lift R.filtration w hw f hf
      ∃ E : RationalFilteredNilmanifold (FreeDegreeRankLieAlgebra X s r w hw) s
          (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw)),
        ∃ Q : E.DegreeRankStructure r,
          Q.filtration = FreeDegreeRankLieAlgebra.filtration X s r w hw hr ∧
          Q.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
          (∀ i j, rationalLogHeight (D.basis.repr (φ (E.basis j)) i) ≤ (p + C) ^ C) ∧
          E.lattice ≤ D.lattice.comap (mapOfSteps
            (hL := E.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot) φ) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] FreeDegreeRankLieAlgebra X s r w hw)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] FreeDegreeRankLieAlgebra X s r w hw) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 E.basis
           ∃ V : E.UnitVerticalObservable (Q.realSubgroup s r) I ((p + C) ^ C),
             V.frequency = U.frequency.comp φ.toLinearMap ∧
             ∀ i x, V.observable i (QuotientGroup.mk x) =
               U.observable i (QuotientGroup.mk (realificationMap
                 (hnil := E.filtration.lowerCentralSeries_eq_bot)
                 (hM := D.filtration.lowerCentralSeries_eq_bot) φ x))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_free_evaluation s
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let T₀ := Polynomial.X + A₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (A₀ + (T₀ + (T₀ + 3) ^ 2 + (T₀ + 2) ^ 4))
  refine ⟨C, hC, ?_⟩
  intro X L I _ _ _ _ _ _ _ _ r d hr D R w hw f hf p hp hX hR hfH U φ
  let A := (p + a) ^ a
  let t := p + A
  let q := t + (t + 3) ^ 2 + (t + 2) ^ 4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right hA
  have hAt : A ≤ t := le_add_of_nonneg_left hp
  have ht : 0 ≤ t := hp.trans hpt
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hcost : A + q ≤ (p + C) ^ C := by
    simpa [A₀, T₀, A, t, q, Polynomial.eval₂_pow] using hbudget p hp
  have hAC : A ≤ (p + C) ^ C := (le_add_of_nonneg_right hq).trans hcost
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_left hA).trans hcost
  obtain ⟨E, Q, hQ, hcomplex, hcentral, ⟨frame⟩, hmatrix, hlattice⟩ :=
    hfree X L r d hr D R w hw f hf p hp hX hR hfH
  let := moduleTopology ℝ (ℝ ⊗[ℚ] FreeDegreeRankLieAlgebra X s r w hw)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] FreeDegreeRankLieAlgebra X s r w hw) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  have hlayer (i j : ℕ) :
      (Q.filtration.layer i j).map φ.toLinearMap ≤ R.filtration.layer i j := by
    rintro y ⟨x, hx, rfl⟩
    rw [hQ] at hx
    exact FreeDegreeRankLieAlgebra.lift_mem_layer R.filtration w hw f hf hr hx
  have htop : Q.realSubgroup s r ≤ (R.realSubgroup s r).comap
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) φ) := by
    intro z hz
    change realificationLieHom φ z.coord ∈ (R.filtration.layer s r).baseChange ℝ
    have hz' : z.coord ∈ (Q.filtration.layer s r).baseChange ℝ := hz
    have h := Submodule.baseChange_mono ℝ (hlayer s r)
    rw [realification_map] at h
    exact h ⟨z.coord, hz', rfl⟩
  let V := (U.mono hpt).controlledPullback φ hlattice (Q.realSubgroup s r) htop ht
    (hcomplex.1.mono E hAt) (hR.1.mono D hpt) (fun i j => (hmatrix i j).trans hAt)
  refine ⟨E, Q, hQ, hcomplex.mono Q hAC, hcentral,
    ⟨frame.mono hAC⟩, (fun i j => (hmatrix i j).trans hAC), hlattice, ?_⟩
  exact ⟨V.mono hqC, rfl, fun i x => rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

namespace RationalFilteredNilmanifold.UnitVerticalObservable

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))]
  {D : RationalFilteredNilmanifold L s d} (T : D.DegreeRankStructure r) {p : ℝ}
  (V : D.UnitVerticalObservable (T.realSubgroup s r) I p)

noncomputable def pairedObservable (a : I × I) (x : (pi (fun _ : Fin 2 => D)).Space) : ℂ :=
  V.observable a.1 (productProjection (fun _ : Fin 2 => D) 0 x) *
    star (V.observable a.2 (productProjection (fun _ : Fin 2 => D) 1 x))

omit [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))] in
theorem pairedObservable_unit (x : (pi (fun _ : Fin 2 => D)).Space) :
    ∑ a, ‖V.pairedObservable T a x‖ ^ 2 = 1 := by
  simp only [pairedObservable, norm_mul, norm_star, mul_pow, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, V.unit, mul_one]

omit [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))] in
theorem pairedObservable_norm (a : I × I) (x : (pi (fun _ : Fin 2 => D)).Space) :
    ‖V.pairedObservable T a x‖ ≤ 1 := by
  simpa only [pairedObservable, norm_mul, norm_star, mul_one] using
    mul_le_mul (V.norm a.1 _) (V.norm a.2 _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem pairedObservable_lipschitz (a : I × I) :
    letI := (pi (fun _ : Fin 2 => D)).metricSpace
    LipschitzWith
      (2 * (V.lipBound * coordinateLipschitzBound d (Fintype.card (Σ _ : Fin 2, Fin d)) 1))
      (V.pairedObservable T a) := by
  let := D.metricSpace
  let := (pi (fun _ : Fin 2 => D)).metricSpace
  have h₀ := (V.lipschitz a.1).comp (productProjection_lipschitz (fun _ : Fin 2 => D) 0)
  have h₁ := (V.lipschitz a.2).comp (productProjection_lipschitz (fun _ : Fin 2 => D) 1)
  change LipschitzWith _ (fun x : (pi (fun _ : Fin 2 => D)).Space =>
    V.observable a.1 (productProjection (fun _ : Fin 2 => D) 0 x) *
      star (V.observable a.2 (productProjection (fun _ : Fin 2 => D) 1 x)))
  exact (lipschitz_mul_star_of_bounds
    (fun x : (pi (fun _ : Fin 2 => D)).Space => V.observable a.1 (productProjection (fun _ : Fin 2 => D) 0 x))
    (fun x : (pi (fun _ : Fin 2 => D)).Space => V.observable a.2 (productProjection (fun _ : Fin 2 => D) 1 x))
    (Bf := 1) (Bg := 1) h₀ h₁ (fun x => V.norm a.1 _) (fun x => V.norm a.2 _)).weaken
      (by simp only [one_mul, two_mul, le_refl])

omit [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))] in
theorem pairedObservable_vertical (a : I × I) (z : (pi (fun _ : Fin 2 => D)).RealGroup)
    (hz : z ∈ (piRank (fun _ : Fin 2 => D) (fun _ => T)).realSubgroup s r)
    (x : (pi (fun _ : Fin 2 => D)).Space) :
    V.pairedObservable T a (z • x) =
      CircleFourier.character
        ((realifyFunctional (pairDifferenceFunctional V.frequency) z.coord : ℝ) : CircleFourier.Circle) *
        V.pairedObservable T a x := by
  simp only [pairedObservable, productProjection_smul]
  rw [V.vertical a.1 _ (productProjectionHom_mem_rank (fun _ : Fin 2 => D)
    (fun _ => T) 0 s r z hz), V.vertical a.2 _
    (productProjectionHom_mem_rank (fun _ : Fin 2 => D) (fun _ => T) 1 s r z hz)]
  rw [star_mul, realify_pairDifferenceFunctional, AddCircle.coe_sub,
    sub_eq_add_neg, CircleFourier.character_add, CircleFourier.character_neg]
  simp only [productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord]
  ring

noncomputable def paired (hp : 2 ≤ p) (hD : D.GeometryComplexityLE p) :
    (pi (fun _ : Fin 2 => D)).UnitVerticalObservable
      ((piRank (fun _ : Fin 2 => D) (fun _ => T)).realSubgroup s r) (I × I)
      (p + (p ^ 2 + p + 3) ^ 2 + 2) where
  observable := V.pairedObservable T
  unit := V.pairedObservable_unit T
  norm := V.pairedObservable_norm T
  lipBound := 2 * (V.lipBound * coordinateLipschitzBound d (Fintype.card (Σ _ : Fin 2, Fin d)) 1)
  lip_bound := by
    have hp₀ : 0 ≤ p := by linarith
    have hproj := productProjection_lipschitz_bound (fun _ : Fin 2 => D) hp₀
      (by simpa using hp) (fun _ => hD) 0
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    calc
      _ ≤ Real.exp 2 * (Real.exp p * Real.exp ((p ^ 2 + p + 3) ^ 2)) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (2 : ℝ)])
          (mul_le_mul V.lip_bound hproj (by positivity) (Real.exp_pos _).le)
          (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  lipschitz := V.pairedObservable_lipschitz T
  frequency := pairDifferenceFunctional V.frequency
  height i := by
    have hsmall : p ≤ p + (p ^ 2 + p + 3) ^ 2 + 2 := by nlinarith [sq_nonneg (p ^ 2 + p + 3)]
    apply le_trans _ hsmall
    rw [pairDifferenceFunctional_eq_piFrequency]
    apply piFrequency_logHeight
    intro j k
    split_ifs
    · exact V.height k
    · simpa [rationalLogHeight] using V.height k
  vertical := V.pairedObservable_vertical T
  integral z hz hL := by
    have hmem (i : Fin 2) : productProjectionHom (fun _ : Fin 2 => D) i z ∈ D.realLattice :=
      NilpotentLieBCHGroup.realificationMap_subgroup (liePiEval i) _ _
        (productProjection_lattice (fun _ : Fin 2 => D) i) hL
    obtain ⟨m, hm⟩ := V.integral _
      (productProjectionHom_mem_rank (fun _ : Fin 2 => D) (fun _ => T) 0 s r z hz) (hmem 0)
    obtain ⟨n, hn⟩ := V.integral _
      (productProjectionHom_mem_rank (fun _ : Fin 2 => D) (fun _ => T) 1 s r z hz) (hmem 1)
    refine ⟨m - n, ?_⟩
    rw [realify_pairDifferenceFunctional]
    change realifyFunctional V.frequency (productProjectionHom (fun _ : Fin 2 => D) 0 z).coord -
      realifyFunctional V.frequency (productProjectionHom (fun _ : Fin 2 => D) 1 z).coord = _
    rw [hm, hn, Int.cast_sub]

end RationalFilteredNilmanifold.UnitVerticalObservable
end Erdos3

end

section

namespace Erdos3.SubspaceFreeLift

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (L I : Type*) [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (r d : ℕ) (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure r)
      (S : Fin s → Submodule ℚ L)
      (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (hS : ∀ j, S j ≤ T.filtration.layer (j.val + 1) 0)
      (p : ℝ), 0 ≤ p → T.ComplexityLE p →
      (∀ j a i, rationalLogHeight (D.basis.repr (B j a : L) i) ≤ p) →
      ∀ U : D.UnitVerticalObservable (T.realSubgroup s r) I p,
      ∃ E : RationalFilteredNilmanifold (Algebra S r) s (finrank ℚ (Algebra S r)),
        ∃ Q : E.DegreeRankStructure r,
          Q.filtration = filtration S T.filtration.rank_le_degree ∧
          Q.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
          (∀ i j, rationalLogHeight (D.basis.repr
            (evaluation S B T.filtration hS (E.basis j)) i) ≤ (p + C) ^ C) ∧
          E.lattice ≤ D.lattice.comap (mapOfSteps
            (hL := E.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot) (evaluation S B T.filtration hS)) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S r)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 E.basis
           ∃ V : E.UnitVerticalObservable (Q.realSubgroup s r) I ((p + C) ^ C),
             V.frequency = U.frequency.comp (evaluation S B T.filtration hS).toLinearMap ∧
             ∀ i x, V.observable i (QuotientGroup.mk x) =
               U.observable i (QuotientGroup.mk (realificationMap
                 (hnil := E.filtration.lowerCentralSeries_eq_bot)
                 (hM := D.filtration.lowerCentralSeries_eq_bot) (evaluation S B T.filtration hS) x))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_free_unit_observable s
  let K₀ : Polynomial ℕ := Polynomial.C (s + 1) * Polynomial.X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((K₀ + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ r d D T S B hS p hp hT hB U
  let : Module.Finite ℚ L := D.basis.finiteDimensional_of_finite
  let K := ((s + 1 : ℕ) : ℝ) * p + 1
  have hpK : p ≤ K := by dsimp only [K]; push_cast; nlinarith [show (0 : ℝ) ≤ s from Nat.cast_nonneg s]
  have hK : 0 ≤ K := hp.trans hpK
  have hdim : (finrank ℚ L : ℝ) ≤ p := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hT.1.1
  have hcard : (Fintype.card (Alphabet S) : ℝ) ≤ K := by
    calc
      _ ≤ (s : ℝ) * finrank ℚ L := by exact_mod_cast alphabet_card_le S
      _ ≤ (s : ℝ) * p := mul_le_mul_of_nonneg_left hdim (Nat.cast_nonneg _)
      _ ≤ K := by dsimp only [K]; push_cast; nlinarith
  have hbound : (K + a) ^ a ≤ (p + C) ^ C := by
    simpa [K₀, K, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨E, Q, hQ, hQc, hcentral, ⟨frame⟩, hmatrix, hlattice, hV⟩ :=
    hfree (Alphabet S) L I r d T.filtration.rank_le_degree D T (weight S) (weight_pos S)
      (fun x => (B x.1 x.2).val) (fun x => hS x.1 (B x.1 x.2).property) K hK hcard
      (hT.mono T hpK) (fun x i => (hB x.1 x.2 i).trans hpK) (U.mono hpK)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S r)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, hobs⟩ := hV
  exact ⟨E, Q, hQ, hQc.mono Q hbound, hcentral, ⟨frame.mono hbound⟩,
    (fun i j => (hmatrix i j).trans hbound), hlattice, V.mono hbound, hfreq, hobs⟩

end Erdos3.SubspaceFreeLift

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
namespace OAI

section

namespace Erdos3.SubspaceFreeLift

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_native_pair_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (L I : Type*) [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))]
      (r d : ℕ) (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure r)
      (S : Fin s → Submodule ℚ (Fin 2 → L))
      (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (hS : ∀ j, S j ≤ (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration.layer (j.val + 1) 0)
      (p : ℝ), 2 ≤ p → T.ComplexityLE p →
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => D.basis)).repr
        (B j a : Fin 2 → L) i) ≤ p) →
      ∀ U : D.UnitVerticalObservable (T.realSubgroup s r) I p,
      let φ := evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS
      ∃ E : RationalFilteredNilmanifold (Algebra S r) s (finrank ℚ (Algebra S r)),
        ∃ Q : E.DegreeRankStructure r,
          Q.filtration = filtration S T.filtration.rank_le_degree ∧
          Q.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
          (∀ i j, rationalLogHeight ((pi (fun _ : Fin 2 => D)).basis.repr
            (φ (E.basis j)) i) ≤ (p + C) ^ C) ∧
          E.lattice ≤ (pi (fun _ : Fin 2 => D)).lattice.comap (mapOfSteps
            (hL := E.filtration.lowerCentralSeries_eq_bot)
            (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot) φ) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S r)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 E.basis
           ∃ V : E.UnitVerticalObservable (Q.realSubgroup s r) (I × I) ((p + C) ^ C),
             V.frequency = (pairDifferenceFunctional U.frequency).comp φ.toLinearMap ∧
             ∀ i x, V.observable i (QuotientGroup.mk x) =
               U.pairedObservable T i (QuotientGroup.mk (realificationMap
                 (hnil := E.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot) φ x))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_model s
  let K₀ : Polynomial ℕ := (Polynomial.X + 2) ^ 2 +
    (Polynomial.X + (Polynomial.X ^ 2 + Polynomial.X + 3) ^ 2 + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((K₀ + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ _ _ _ _ r d D T S B hS p hp hT hB U φ
  have hp₀ : 0 ≤ p := by linarith
  let P := p + (p ^ 2 + p + 3) ^ 2 + 2
  let K := (p + 2) ^ 2 + P
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hpP : p ≤ P := by dsimp only [P]; nlinarith [sq_nonneg (p ^ 2 + p + 3)]
  have hPK : P ≤ K := le_add_of_nonneg_left (sq_nonneg (p + 2))
  have hGK : (p + 2) ^ 2 ≤ K := le_add_of_nonneg_right hP
  have hK : 0 ≤ K := hP.trans hPK
  have hbound : (K + a) ^ a ≤ (p + C) ^ C := by
    simpa [K₀, K, P, Polynomial.eval₂_pow] using hbudget p hp₀
  let D₂ := pi (fun _ : Fin 2 => D)
  let T₂ := piRank (fun _ : Fin 2 => D) (fun _ => T)
  have hT₂ : T₂.ComplexityLE K :=
    (piRank_complexity (fun _ : Fin 2 => D) (fun _ => T) hp₀
      (by simpa using hp) (fun _ => hT)).mono T₂ hGK
  have hB₂ (j : Fin s) (k : Fin (finrank ℚ (S j))) (i) :
      rationalLogHeight (D₂.basis.repr (B j k : Fin 2 → L) i) ≤ K := by
    change rationalLogHeight ((productFinBasis (fun _ : Fin 2 => D)).repr _ i) ≤ K
    rw [productFinBasis, Basis.repr_reindex_apply]
    exact (hB j k _).trans (hpP.trans hPK)
  obtain ⟨E, Q, hQ, hQc, hcentral, ⟨frame⟩, hmatrix, hlattice, hV⟩ :=
    hfree (Fin 2 → L) (I × I) r _ D₂ T₂ S B hS K hK hT₂ hB₂
      ((U.paired T hp hT.1).mono hPK)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S r)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, hobs⟩ := hV
  exact ⟨E, Q, hQ, hQc.mono Q hbound, hcentral, ⟨frame.mono hbound⟩,
    (fun i j => (hmatrix i j).trans hbound), hlattice, V.mono hbound, hfreq, hobs⟩

end Erdos3.SubspaceFreeLift

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

noncomputable def comparisonCoefficientSpace (d : Fin s) :
    Submodule ℚ (Fin 2 → D.CoefficientFreeLieAlgebra) :=
  petalComparisonSpace
    ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0))
    (fourPetalSpace (D.dependentFreeSpan d)
      (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)))
    (D.coefficientFreeFiltration.layer (d.val + 1) 2)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def nativePairModelConstant (s : ℕ) : ℕ :=
  (SubspaceFreeLift.exists_native_pair_model.{0, 0} s).choose

end Erdos3

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

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeFrozenComparison
namespace OAI

section

namespace Erdos3

noncomputable def nativeLowerPairModelBudget (s : ℕ) (p : ℝ) : ℝ :=
  ((p + nativePairModelConstant s) ^ nativePairModelConstant s + rankUnitDescentConstant s) ^
    rankUnitDescentConstant s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeLowerFactorization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct NNReal

theorem exists_sharedFreeFactorFreezing (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) {q p : ℝ},
      0 ≤ q → q ≤ p → 0 ≤ p → D.GeometryComplexityLE q →
      ∀ m : ℕ, 0 < m →
      (m : ℝ) ≤ Real.exp ((s : ℝ) *
        (sharedFreeCommonCorrectionBudget s q p + sharedFreePetalLiftBudget s q p)) →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ ρ : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
          CoefficientGrid (D.basis.baseChange ℝ) m ρ.log →
          ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
              (fun _ : Unit => 1) x ρ) : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
                (fun _ : Unit => 1) y ρ)) ∧
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
              (fun _ : Unit => 1) x ρ)⁻¹ : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
                (fun _ : Unit => 1) y ρ)⁻¹)) ∧
        ∀ (Φ : D.Space → ℂ) (K : ℝ≥0), (∀ z, ‖Φ z‖ ≤ 1) →
          (letI := D.metricSpace; LipschitzWith K Φ) → (K : ℝ) ≤ Real.exp q →
          ∀ ε a ρ g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
            ε * a * ρ = g → ∀ T : ℝ, 0 < T →
            CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => T)
              (Real.exp (sharedFreeCommonCorrectionBudget s q p) +
                Real.exp (sharedFreePetalLiftBudget s q p)) ε.log →
            CoefficientGrid (D.basis.baseChange ℝ) m ρ.log →
            ∀ (x y : Unit → ℤ) (δ : ℝ), 0 ≤ δ →
              (∀ j, |(x j : ℝ)| ≤ T) → (∀ j, |(y j : ℝ)| ≤ T) →
              (∀ j, |(x j : ℝ) - y j| ≤ T * δ) →
              (∀ j, (M : ℤ) ∣ x j - y j) →
              ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) x g)) -
                Φ (QuotientGroup.mk
                  (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y ε *
                   D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x a *
                   D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y ρ))‖ ≤
                Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨a, _, hfull⟩ := exists_sharedFreeFullOrbitBudget_bound s
  obtain ⟨b, _, hperiod⟩ := exists_native_orbit_rational_period s
  obtain ⟨c, _, hfreeze⟩ := exists_orbit_factor_freezing s 1
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((B + Polynomial.C b) ^ b + (B + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D q p hq hqp hp hD m hm hmb
  let t := (p + a) ^ a + p + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hqt : q ≤ t := by dsimp only [t]; linarith
  have hbt : (p + a) ^ a ≤ t := by dsimp only [t]; linarith
  have ht1 : (1 : ℝ) ≤ t := by dsimp only [t]; linarith
  have hsum : (t + b) ^ b + (t + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, t, Polynomial.eval₂_pow] using hbudget p hp
  have hbC : (t + b) ^ b ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (t + c) ^ c by positivity]
  have hcC : (t + c) ^ c ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (t + b) ^ b by positivity]
  obtain ⟨_, _, _, hden, hslow⟩ := hfull q p hq hqp hp
  obtain ⟨M, hM, hMb, hsolve⟩ := hperiod D (fun _ : Unit => 1)
    (fun _ => Nat.zero_lt_one) t ht (hD.mono D hqt)
    (by simpa only [Fintype.card_unit, Nat.cast_one] using ht1) m hm
    (hmb.trans (Real.exp_le_exp.mpr (hden.trans hbt)))
  refine ⟨M, hM, hMb.trans (Real.exp_le_exp.mpr hbC), hsolve, ?_⟩
  intro Φ K hΦ hLip hK ε a₀ ρ g hprod T hT hε hρ x y δ hδ hx hy hxy hres
  have hε' : CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => T)
      (Real.exp ((t + 2) ^ 1)) ε.log :=
    CoefficientBound.mono _ _ (fun _ => hT) hε
      (hslow.trans (Real.exp_le_exp.mpr (by simpa only [pow_one] using
        (hbt.trans (show t ≤ t + 2 by linarith)))))
  exact (hfreeze D (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) t ht
    (hD.mono D hqt) (by simpa only [Fintype.card_unit, Nat.cast_one] using ht1)
    Φ K hΦ hLip (hK.trans (Real.exp_le_exp.mpr hqt)) ε a₀ ρ g hprod
    (fun _ : Unit => T) (fun _ => hT) hε' x y δ hδ hx hy hxy
    (hsolve ρ hρ x y hres).1).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcC) hδ)

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3

noncomputable def sharedFreeFactorFreezingConstant (s : ℕ) : ℕ :=
  (RationalFilteredNilmanifold.exists_sharedFreeFactorFreezing.{0} s).choose

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedFreeCorrelationBudget
namespace OAI

section

namespace Erdos3

noncomputable def sharedFreeCorrelationInput (s : ℕ) (p : ℝ) : ℝ :=
  p + (p + (exists_sharedFreeFullOrbitBudget_bound s).choose) ^
      (exists_sharedFreeFullOrbitBudget_bound s).choose +
    (p + sharedFreeFactorFreezingConstant s) ^ sharedFreeFactorFreezingConstant s + 2

noncomputable def sharedFreeCorrelationBudget (s : ℕ) (hs : 2 ≤ s) (p : ℝ) : ℝ :=
  (sharedFreeCorrelationInput s p + sharedFactorCorrelationConstant s hs) ^
    sharedFactorCorrelationConstant s hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

noncomputable def NativeCommonDerivativeModels.mono {s N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} (B : NativeCommonDerivativeModels s N p f) (hpq : p ≤ q) :
    NativeCommonDerivativeModels s N q f :=
  { B with
    geometry := B.geometry.mono B.model hpq
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
      (Nat.cast_nonneg _)).trans B.density
    complexity := fun h => (B.complexity h).mono hpq
    correlation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (B.correlation h hh) }

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

namespace MultidegreeLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s m : ℕ} {bound : Fin 2 → ℕ}
  (F : MultidegreeLieFiltration (Fin 2) L s bound)
  (c d : Fin m → L)
  (hc : ∀ j, c j ∈ F.layer (correlationInput 0 (j.val + 1)))
  (hd : ∀ j, d j ∈ F.layer (correlationInput 1 (j.val + 1)))

noncomputable def affineMixedOrbit : F.PolynomialOrbit :=
  F.polynomialOrbitOfLog (affineMixedLog c d) (F.affineMixedLog_adapted c d hc hd)

theorem affineMixedOrbit_eval (x : Fin 2 → ℤ) :
    (F.polynomialOrbitEval x (F.affineMixedOrbit c d hc hd)).coord =
      ∑ j, (x 1 : ℚ) ^ (j.val + 1) • (c j + (x 0 : ℚ) • d j) :=
  affineMixedLog_eval c d _

end MultidegreeLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
namespace OAI

section

namespace Erdos3.NativeBoundedMultidegreeFamily

open scoped TensorProduct

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

noncomputable def slice {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p)
    (i : I) (h : ℤ) : F.model.Niltest (fun _ : Unit => 1) :=
  (F.test i).affinePullback (fun j _ => correlationInput 0 1 j) (correlationInput h 0)

theorem slice_eval {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p)
    (i : I) (h : ℤ) (x : Unit → ℤ) :
    (F.slice i h).eval x = F.eval i (correlationInput h (x ())) := by
  rw [slice, RationalFilteredNilmanifold.Niltest.eval_affinePullback]
  apply congrArg (F.test i).eval
  funext j
  refine Fin.cases ?_ (fun _ => ?_) j <;> simp [integerAffineMap, correlationInput]

theorem slice_orbit_eval {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p)
    (i : I) (h : ℤ) (x : Unit → ℤ) :
    F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (F.slice i h).orbit =
      F.multi.filtration.realification.polynomialOrbitEval (correlationInput h (x ())) F.orbit := by
  let A : Fin 2 → Unit → ℤ := fun j _ => correlationInput 0 1 j
  let b := correlationInput h 0
  have heq : integerAffineMap A b x = correlationInput h (x ()) := by
    funext j
    refine Fin.cases ?_ (fun _ => ?_) j <;> simp [A, b, integerAffineMap, correlationInput]
  have he := F.model.filtration.realification.polynomialOrbitSubstitute_eval
    (integerAffinePolynomial A b) (integerAffinePolynomial_support A b)
    (F.test i).orbit x (integerAffineMap A b x) (integerAffinePolynomial_eval A b x)
  change F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (F.slice i h).orbit =
    F.model.filtration.realification.polynomialOrbitEval (fun _ : Fin 2 => 1)
      (integerAffineMap A b x) (F.test i).orbit at he
  rw [he, heq, F.test_orbit, F.multi.orbitToOrdinary_eval]

theorem slice_norm {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p) (i : I) (h : ℤ) :
    (F.slice i h).normBound = 1 := F.test_norm i

theorem slice_complexity {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p) (i : I) (h : ℤ) :
    (F.slice i h).ComplexityLE p := F.test_complexity i

theorem slice_observable {I : Type*} {s : ℕ} {p : ℝ}
    (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p) (i : I) (h : ℤ) :
    (F.slice i h).observable = (F.test i).observable := rfl

end Erdos3.NativeBoundedMultidegreeFamily

end

section

namespace Erdos3

open scoped TensorProduct

namespace NativeBoundedMultidegreeFamily

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

variable {σ I : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (M : NativeBoundedMultidegreeFamily bound I p) (hpq : p ≤ q)
  {n : ℕ} (hn : (n + 1 : ℝ) ≤ Real.exp q)
  (V : M.model.UnitVerticalObservable
    (M.model.filtration.realification.subgroup (∑ i, bound i)) (Fin (n + 1)) q)

noncomputable def toNilcharacter : NativeMultidegreeNilcharacter bound q where
  L := M.L
  dim := M.dim
  model := M.model
  multi := M.multi
  complexity := M.complexity.mono M.multi hpq
  orbit := M.orbit
  outputDim := n + 1
  output_pos := Nat.succ_pos n
  output_bound := by simpa only [Nat.cast_add, Nat.cast_one] using hn
  vertical := {
    V with
    vertical := fun i z hz x => V.vertical i z (M.multi.realSubgroup_top ▸ hz) x
    integral := fun z hz hL => V.integral z (M.multi.realSubgroup_top ▸ hz) hL
  }

theorem toNilcharacter_eval (i : Fin (n + 1)) (x : σ → ℤ) :
    (M.toNilcharacter hpq hn V).eval i x = V.observable i (QuotientGroup.mk
      (M.multi.filtration.realification.polynomialOrbitEval x M.orbit)) := rfl

end NativeBoundedMultidegreeFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem NativeCommonDerivativeModels.exists_large_common_observable {s N : ℕ} [NeZero N]
    {p : ℝ} {f : ZMod N → ℂ} (B : NativeCommonDerivativeModels s N p f)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ y : B.model.Space, Real.exp (-p) ≤ ‖(B.test 0).observable y‖ := by
  obtain ⟨h, hh⟩ := B.nonempty
  have hmean : Real.exp (-p) ≤ 𝔼 x, ‖(B.test h).evalCyclic N (fun _ => x)‖ := by
    apply (B.correlation h hh).trans
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le_expect
    intro x _
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (multiplicativeDerivative_norm_le_one f hf h x)
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  refine ⟨QuotientGroup.mk (B.model.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (B.test h).orbit), ?_⟩
  rw [B.common_observable 0 h]
  exact hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairCorrelator
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

include V in
theorem antisymmetricPairBudget_four_le : 4 ≤ antisymmetricPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  unfold antisymmetricPairBudget raisedNiltestBudget
  nlinarith [sq_nonneg (p + q + 2)]

theorem antisymmetricPairTests_complexity (k : Option (Fin 2)) :
    (V.antisymmetricPairTests k).ComplexityLE (antisymmetricPairBudget p q) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hpq : 0 ≤ p + q := add_nonneg hp hq
  have hr : 0 ≤ raisedNiltestBudget (p + q) := hpq.trans (le_raisedNiltestBudget _)
  cases k with
  | none =>
    exact (V.test.raiseStep_complexity (by decide) hpq
      (V.complexity.mono (le_add_of_nonneg_left hp))).mono
        (by unfold antisymmetricPairBudget; linarith)
  | some k =>
    have hcost : p + 4 ≤ antisymmetricPairBudget p q := by
      unfold antisymmetricPairBudget
      linarith
    fin_cases k
    · exact (W.component_complexity i).mono hcost
    · exact (W.component_complexity j).mono hcost

end NativeSampleCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AntisymmetricPairNiltest
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

noncomputable def antisymmetricPairNiltest :
    (pi V.antisymmetricPairModels).Niltest (fun _ : Fin 2 => 1) :=
  piNiltest V.antisymmetricPairModels V.antisymmetricPairTests
    ((by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le)
    (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
    V.antisymmetricPairTests_complexity

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

structure NativeAntisymmetricPairFactorization {p q : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
    (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))) (r : ℝ) where
  [topology : TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  basis : Basis (Fin (finrank ℚ V.AntisymmetricPairAlgebra)) ℚ V.AntisymmetricPairAlgebra
  weight : Fin (finrank ℚ V.AntisymmetricPairAlgebra) → ℕ
  adapted : ∀ k, (pi V.antisymmetricPairModels).filtration.layer k =
    Submodule.span ℚ (basis '' {l | k ≤ weight l})
  height : ∀ a b, rationalLogHeight ((pi V.antisymmetricPairModels).basis.repr (basis a) b) ≤ r
  factorization : (pi V.antisymmetricPairModels).filtration.ControlledSymbolFactorization
    basis weight adapted (piFrequency V.antisymmetricPairFrequencies) (fun _ : Fin 2 => (N : ℝ))
    (V.antisymmetricPairNiltest.symbol basis weight adapted) r

noncomputable def NativeAntisymmetricPairFactorization.mono {p q r r' : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
    {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
    (F : NativeAntisymmetricPairFactorization V r) (hrr' : r ≤ r') :
    NativeAntisymmetricPairFactorization V r' := by
  letI := F.topology
  letI := F.topologicalAdd
  letI := F.continuousSMul
  letI := F.hausdorff
  exact { F with
    height := fun a b => (F.height a b).trans hrr'
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      (pi V.antisymmetricPairModels).filtration F.basis F.weight F.adapted F.factorization hrr'
      (fun _ => by exact_mod_cast NeZero.pos N) }

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

def NativeCharacterCrossRowDetection (s C : ℕ) : Prop :=
  ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
    ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
    ∀ (f g : ZMod N → ℂ) (χ : ZMod N → AddChar (ZMod N) ℂ),
    (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
    Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      characterCrossRow f g χ h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
    Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 1) g

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecoveredPreparedFreeze
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G V : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

include hσ1 hC hchart

theorem allocatedLayerSupported_polynomial_bound (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (x : LayerSamplerVariables G I n B → ℝ) (hx : ∀ v, |x v| ≤ layerSamplerBox B U b S v)
    (i : J j) :
    |mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x i| ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have hs := (allocatedArraySupported_iff_rows Subtype.val (layerSamplerBox B U b S)
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (R j) (σ j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) a).mp ha
  have hc (k : I j) : |MvPolynomial.eval x (monomialArrayPolynomial Subtype.val (a.1 k))| ≤ R j :=
    (continuousPolynomialDensity_box Subtype.val _ hT _ _
      (layerContinuousPrincipalSlots_not_constant B j k) (hR j) (hσ j) (hσ1 j)
      (hs.1 k) x hx).trans (by linarith [hR j])
  have hz (k : Fin (n j)) :
      |MvPolynomial.eval x (monomialArrayPolynomial Subtype.val
        (fun d => (a.2 k d : ℝ) / basisAxisScale (b j) k))| ≤ R j := by
    exact (allocatedIntegerPolynomial_box (layerIntegerPrincipalSlots B j k) (constantCoefficientSlot _ _)
      (j.val + 1) (basisAxisScale (b j) k) S.value (layerTailDegree m) (Nat.zero_lt_succ _)
      (basisAxisScale_pos (b j) k) S.positive (layerSamplerBox B U b S) hT
      (layerSamplerBox_le B U b S) Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (S.gap j k) (S.width j)
      (layerIntegerPrincipalSlots_not_constant B j k) rfl (hσ1 j)
      (layerSamplerSides_integer_principal B U b R S.value j k) (a.2 k) (hs.2 k) x hx).trans
        (by linarith [hR j])
  have hnorm := mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j)
    (hC j) (hR j).le (hchart j) _ _ hc hz
  have hi := PiLp.norm_apply_le
    (mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x) i
  simpa only [Real.norm_eq_abs] using hi.trans hnorm

end Erdos3.VectorPolynomial

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

variable {X : Type*}

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

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {V : Type*} (Long : V → Prop) [DecidablePred Long]

namespace ResidueBoxSlice

variable {N : V → ℕ} {q : ℕ}

variable [Fintype V] [DecidableEq V]

theorem freezeShort_dense
    (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hq : 0 < q) {cost B : ℝ}
    (hA : IsDenseCommonStrideBox (fun i : {i // Long i} => N i.val) cost A.integerPoints)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) :
    IsDenseCommonStrideBox N (max cost (Real.log B))
      (A.freezeShort Long fixed hfixed).integerPoints := by
  let A' := A.freezeShort Long fixed hfixed
  refine ⟨fun i => (A'.start i : ℤ), q, A'.length, hq, ?_,
    A'.progression_inside, ?_, A'.integerPoints_eq_commonStrideBox⟩
  · intro i
    by_cases hi : Long i
    · simpa only [A', freezeShort, dif_pos hi] using A.length_pos_of_dense hA ⟨i, hi⟩
    · simp [A', freezeShort, hi]
  · intro i
    by_cases hi : Long i
    · calc
        _ ≤ Real.exp (-cost) * (N i : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (neg_le_neg (le_max_left _ _))) (Nat.cast_nonneg _)
        _ ≤ A'.length i := by
          simpa only [A', freezeShort, dif_pos hi] using
            A.length_lower_of_dense hq hA ⟨i, hi⟩
    · have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
      have hexp : Real.exp (-max cost (Real.log B)) ≤ B⁻¹ := by
        calc
          _ ≤ Real.exp (-Real.log B) :=
            Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))
          _ = B⁻¹ := by rw [Real.exp_neg, Real.exp_log hBpos]
      simp only [A', freezeShort, dif_neg hi, Nat.cast_one]
      calc
        _ ≤ B⁻¹ * (N i : ℝ) := mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg _)
        _ ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hshort i hi) (inv_nonneg.mpr hBpos.le)
        _ = 1 := inv_mul_cancel₀ hBpos.ne'

end ResidueBoxSlice

namespace RationalFilteredNilmanifold.Niltest

variable [Fintype V] {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

omit [DecidablePred Long] in
theorem eval_liftLong (T : D.Niltest (fun _ : {i // Long i} => 1)) (x : V → ℤ) :
    (T.liftLong Long).eval x = T.eval (fun i => x i.val) :=
  T.eval_linearPullbackHom (longCoordinateProjection Long) x

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ForecastSpatialCharacterSplit
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

def forecastCoefficientOutputHom {R : Type*} [AddCommMonoid R] :
    (∀ j, Fin (n j) ⊕ E j → R) →+
      (Sigma (AllocatedCongruenceRankOutput X E inactive) → R) where
  toFun label o := match o.2 with
    | .inl _ => 0
    | .inr (.inl i) => label o.1 (.inr i)
    | .inr (.inr a) => label o.1 (.inl a.val)
  map_zero' := by
    funext o
    rcases o with ⟨j, x | i | a⟩ <;> rfl
  map_add' u v := by
    funext o
    rcases o with ⟨j, x | i | a⟩ <;> simp

def forecastCongruenceOutput {R : Type*} (u : X → R)
    (label : ∀ j, Fin (n j) ⊕ E j → R) :
    Sigma (AllocatedCongruenceRankOutput X E inactive) → R := fun o =>
  match o.2 with
  | .inl x => u x.val
  | .inr (.inl i) => label o.1 (.inr i)
  | .inr (.inr a) => label o.1 (.inl a.val)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedRecoveredIntegerFullChart
namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators
variable {m : ℕ} {K X : Type*} [Fintype K] (J : Fin m → Type*)
    (a : X → ℤ) (v : Option K × X → ℤ)
    (tag : ∀ j, J j → MvPolynomial K ℤ)

theorem jointIntegerFullChart_spatial (x : K → ℤ) :
    integerSampledSpatial (jointIntegerFullChart J a v tag) x =
      jointIntegerPhysicalSite x (a, v) := by
  funext i
  change MvPolynomial.aeval x (affineFramePolynomial (jointIntegerFrame (a, v)) i) = _
  rw [affineFramePolynomial_eval]
  have h := congrFun (integerAffineMap_jointIntegerFrame (a, v) x) i
  simpa only [integerAffineMap] using h

theorem cast_jointIntegerPhysicalSite_eq_frame (x : K → ℤ) :
    (fun i => (jointIntegerPhysicalSite x (a, v) i : ℝ)) =
      (fun i => (jointIntegerFrame (a, v) none i : ℝ) +
        ∑ k, (jointIntegerFrame (a, v) (some k) i : ℝ) * (x k : ℝ)) := by
  rw [← integerAffineMap_jointIntegerFrame]
  funext i
  simp only [integerAffineMap, Int.cast_add, Int.cast_sum, Int.cast_mul]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem allocatedParameterBox_side_eq (i : LayerSamplerVariables G I n B) :
    layerSamplerBox B U b S i = (sides i : ℝ) := by
  cases i <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplerSeparatedVariables
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {D G : Type*} {B : D → Type*}

noncomputable def samplerSeparatedVariable (inactive : D → Prop) (h : D → ℕ) :
    SamplerTupleIndex G B h →
      SamplerLongVariables inactive G B h ⊕ (PrincipalTupleIndex B h × Option Empty) := by
  classical
  exact fun
    | .inl g => .inl (.inl g)
    | .inr ⟨d, b, v⟩ =>
        if hd : inactive d then .inr (⟨d, b, v⟩, none)
        else .inl (.inr ⟨⟨d, hd⟩, b, v⟩)

@[simp] theorem samplerSeparatedVariable_common (inactive : D → Prop)
    (h : D → ℕ) (g : G) :
    samplerSeparatedVariable (B := B) inactive h (.inl g) = .inl (.inl g) := rfl

@[simp] theorem samplerSeparatedVariable_inactive (inactive : D → Prop)
    (h : D → ℕ) (d : D) (b : B d) (v : Fin (h d)) (hd : inactive d) :
    samplerSeparatedVariable (G := G) inactive h (.inr ⟨d, b, v⟩) =
      .inr (⟨d, b, v⟩, none) := by
  simp only [samplerSeparatedVariable, hd, dite_true]

@[simp] theorem samplerSeparatedVariable_active (inactive : D → Prop)
    (h : D → ℕ) (d : D) (b : B d) (v : Fin (h d)) (hd : ¬ inactive d) :
    samplerSeparatedVariable (G := G) inactive h (.inr ⟨d, b, v⟩) =
      .inl (.inr ⟨⟨d, hd⟩, b, v⟩) := by
  simp only [samplerSeparatedVariable, hd, dite_false]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedSeparatedCongruencePolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

noncomputable def allocatedUnconditionedCongruenceIntegerPolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ) :
    AllocatedCongruenceRankOutput X E inactive j →
      MvPolynomial (LayerSamplerVariables G I n B) ℤ
  | .inl x => C (base x.val) + spatialRankPolynomial (fun d => noise (d, x.val))
  | .inr (.inl i) => modularBoundedCoefficientPolynomial (j.val + 1) (fun q => r j q i)
  | .inr (.inr a) => modularBoundedCoefficientPolynomial (j.val + 1)
      (projection (allocatedCongruenceIntegerEmbedding inactive j a))

noncomputable def allocatedSeparatedCongruencePolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    MvPolynomial (LayerSamplerLongVariables inactive G B ⊕
      (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ :=
  rename (samplerSeparatedVariable inactive (layerSamplerDegree I n))
    (allocatedUnconditionedCongruenceIntegerPolynomial inactive j base noise r projection o)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

local instance forecastModulusNeZero_r5e2505_1 (Pr : Finset ℕ) (A : ℕ → ℕ)
    [∀ p : Pr, NeZero p.val] : NeZero (∏ p : Pr, p.val ^ A p.val) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
noncomputable def allocatedForecastPolynomial
    (inactive : LayerSamplerAxis I n → Prop)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (o : Sigma (AllocatedCongruenceRankOutput X E inactive)) :
    MvPolynomial (LayerSamplerLongVariables inactive G B ⊕
      (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ :=
  allocatedSeparatedCongruencePolynomial inactive o.1 base noise r (projection o.1) o.2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawNativeRawJointMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

noncomputable def forecastLawDensityPhysicalDeckSource (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ) : ℂ := by
  exact (density ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
    forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
  (rationalInactiveForecast law active
    (forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
    Y N volume (fun a _ => (w (selected a).1).2 (selected a).2)
    (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (deck j)) output : ZMod N)) : ℂ)

local notation "deckSource" => forecastLawDensityPhysicalDeckSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

noncomputable def forecastLawDensityPhysicalChartSource (u : X → ℤ)
    (z : MixedCoveredJetSource I single Eout n N) : ℂ :=
  deckSource u (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())
    (fun j i => ((z.2 j () i).val : ℤ))

end Erdos3.VectorPolynomial

end

end OAI
end


