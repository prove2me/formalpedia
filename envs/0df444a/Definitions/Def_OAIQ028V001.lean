-- Prove2me | Definitions.Def_OAIQ028V001
-- name    : OAIQ028V001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T00:07:08.782971+00:00
-- url     : https://prove2.me/theorems/9df2bf2b-4fe9-4e3f-9d15-1cef5ecd2b5a
-- title:
--   Definitions bundle OAIQ028V001 of the split of OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.VertexCover.explicit_cover_gap` and `OAI.VertexCover.every_fixed_factor_below_two`, carved from OpenAI's openai/math development (OpenAI, *The Factor-Two Hardness Threshold for Vertex Cover (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 588 declarations of OpenAI's Lean: 264 definitions, 6 inductive types or structures, 10 instances and 308 theorems. The definitions and types are `OAI.UniqueGames.Foundations.CorrelatedSampling.totalVariation`, `OAI.UniqueGames.Foundations.Games.Game.simulatedStrategy`, `OAI.UniqueGames.Foundations.Games.KernelSampling.Seed`, `OAI.UniqueGames.Foundations.Games.KernelSampling.completedLeft`, `OAI.UniqueGames.Foundations.Games.KernelSampling.completedRight`, `OAI.UniqueGames.Foundations.Games.KernelSampling.readLeft`, `OAI.UniqueGames.Foundations.Games.KernelSampling.readRight`, `OAI.UniqueGames.Foundations.Games.Strategy`, `OAI.UniqueGames.Foundations.Hastad.SourceContexts.J`, `OAI.UniqueGames.Foundations.Hastad.SourceContexts.clauseAnswerEquiv`, `OAI.UniqueGames.Foundations.Hastad.SourceContexts.clauseAnswerFinEquiv`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.Encoding`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.Encoding.bool`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.Encoding.fin`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.Encoding.function`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.Encoding.prod`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.Encoding.sum`, `OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.Encoding.unit`, `OAI.UniqueGames.Foundations.Information.IsProbability`, `OAI.UniqueGames.Foundations.Information.SupportedBy`, `OAI.UniqueGames.Foundations.Information.conditionalKernel`, `OAI.UniqueGames.Foundations.Information.coordinateMarginal`, `OAI.UniqueGames.Foundations.Information.firstMarginal`, `OAI.UniqueGames.Foundations.Information.hellingerSquared`, `OAI.UniqueGames.Foundations.Information.independentProduct`, `OAI.UniqueGames.Foundations.Information.posterior`, `OAI.UniqueGames.Foundations.Information.posteriorOrOriginal`, `OAI.UniqueGames.Foundations.Information.relativeEntropy`, `OAI.UniqueGames.Foundations.Information.secondMarginal`, `OAI.UniqueGames.Foundations.Information.totalVariation`, `OAI.UniqueGames.Foundations.PCP.AlphabetGraphBounds.dartFactor`, `OAI.UniqueGames.Foundations.PCP.AlphabetGraphBounds.localEventFactor`, `OAI.UniqueGames.Foundations.PCP.AlphabetGraphBounds.sizeFactor`, `OAI.UniqueGames.Foundations.PCP.AlphabetGraphBounds.vertexFactor`, `OAI.UniqueGames.Foundations.PCP.AmplificationIteration.rounds`, `OAI.UniqueGames.Foundations.PCP.AmplificationIteration.run`, `OAI.UniqueGames.Foundations.PCP.AssignmentTester.disagree`, `OAI.UniqueGames.Foundations.PCP.AssignmentTester.distance`, `OAI.UniqueGames.Foundations.PCP.ClauseAnswer`, `OAI.UniqueGames.Foundations.PCP.CloudRounding.Nonmajor` and 230 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `VertexCover_Analysis_AeRegular`, `VertexCover_Analysis_GraphComplete`, `VertexCover_Analysis_SelectedIntegralAbs`, `VertexCover_Analysis_SignAtom`, `VertexCover_Fourier_SourceContexts`, `VertexCover_Fourier_SourceOccurrences`, `VertexCover_Games_Basic`, `VertexCover_Games_KernelSampling`, `VertexCover_Information_ChainRule`, `VertexCover_Information_Conditionals`, `VertexCover_Information_Finite`, `VertexCover_Information_Kernels`, `VertexCover_Information_LogSum`, `VertexCover_Information_Pinsker`, `VertexCover_Information_SideInformation`, `VertexCover_Information_Tensorization`, `VertexCover_Machines_Approximation`, `VertexCover_Machines_BinaryOutput`, `VertexCover_Machines_BoundedBinary`, `VertexCover_Machines_Composition`, `VertexCover_Machines_FiniteMemory`, `VertexCover_Machines_ListNat`, `VertexCover_Machines_Lists`, `VertexCover_Machines_Loop`, `VertexCover_Machines_Naturals`, `VertexCover_Machines_Pair`, `VertexCover_Machines_Primitive`, `VertexCover_Machines_Primitives`, `VertexCover_PCP_AlphabetGraph`, `VertexCover_PCP_AlphabetGraphBounds`, `VertexCover_PCP_AmplificationIteration`, `VertexCover_PCP_AssignmentTester`, `VertexCover_PCP_BinaryCoordinates`, `VertexCover_PCP_ClauseVerifier`, `VertexCover_PCP_CloudRounding`, `VertexCover_PCP_CodeComposition`, `VertexCover_PCP_ExpanderTables`, `VertexCover_PCP_FinalBooleanVerifier`, `VertexCover_PCP_FinalConstants`, `VertexCover_PCP_GraphGap`, `VertexCover_PCP_InitialGraph`, `VertexCover_PCP_LazySmoothing`, `VertexCover_PCP_LazySpectral`, `VertexCover_PCP_PoweringAddresses`, `VertexCover_PCP_PoweringDecoding`, `VertexCover_PCP_PoweringEnumeration`, `VertexCover_PCP_PoweringFinalConstants`, `VertexCover_PCP_PoweringGap`, `VertexCover_PCP_PoweringLabels`, `VertexCover_PCP_PoweringMoment`, `VertexCover_PCP_PoweringMomentBound`, `VertexCover_PCP_PoweringNumeric`, `VertexCover_PCP_PoweringPortReindex`, `VertexCover_PCP_PoweringReturn`, `VertexCover_PCP_PoweringSoundness`, `VertexCover_PCP_PoweringTables`, `VertexCover_PCP_PreprocessingLevels`, `VertexCover_PCP_PreprocessingOverlayTables`, `VertexCover_PCP_RawInitialTables`, `VertexCover_PCP_RoundTables`, `VertexCover_PCP_SpectralCut`, `VertexCover_PCP_SpectralReturn`, `VertexCover_PCP_VerifierToCNF`, `VertexCover_PCP_ZigzagSpectral`, `VertexCover_Reduction_CloneGap`, `VertexCover_Reduction_PairEventMean`, `VertexCover_Reduction_ReductionSound`, `VertexCover_Repetition_AlphabetBudget`, `VertexCover_Repetition_CompletedSampling`, `VertexCover_Repetition_Factorization`, `VertexCover_Repetition_MaskedVariation`, `VertexCover_Repetition_Overlap`, `VertexCover_Repetition_PartialReveal`, `VertexCover_Repetition_ProfileBounds`, `VertexCover_Repetition_ProfileCorrection`, `VertexCover_Repetition_Reveal`, `VertexCover_Repetition_RightProfileBounds`, `VertexCover_Repetition_Scalar`, `VertexCover_Repetition_SelectedCommon`, `VertexCover_Repetition_SelectedCommonMarginal`, `VertexCover_Repetition_SelectedCompletion`, `VertexCover_Repetition_SelectedInformation`, `VertexCover_Repetition_SelectedLikelihood`, `VertexCover_Repetition_SelectedMarginal`, `VertexCover_Repetition_SelectionSequence`, `VertexCover_Repetition_SharedSampling`, `VertexCover_Repetition_Variation`, `VertexCover_Sampling_Basic`.
--
--   **Imports.** It imports the published bundle `Def_VertexCover`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ028V003`, `OAIQ028V004` and `OAIQ028V005`.
-- source:
--   OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_VertexCover

section
-- module Solutions.OAIQ028_VC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_AeRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.AffineSelector
open Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def Regular (a : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (x : E) : Prop :=
  ∀ i j, a i x + b i = a j x + b j → a i = a j

theorem locally_affine (a : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    {f : E → ℝ} (hf : Continuous f)
    (hselect : ∀ y, ∃ i, f y = a i y + b i) {x : E}
    (hx : Regular a b x) :
    ∃ i, f =ᶠ[𝓝 x] (fun y => a i y + b i) := by
  obtain ⟨i, hi⟩ := hselect x
  refine ⟨i, ?_⟩
  have hj : ∀ j, ∀ᶠ y in 𝓝 x,
      f y = a j y + b j → a j y + b j = a i y + b i := by
    intro j
    by_cases h : f x = a j x + b j
    · have ha : a i = a j := hx i j (hi.symm.trans h)
      have hb : b i = b j := by rw [ha] at hi; linarith
      exact Filter.Eventually.of_forall (fun y _ => by rw [ha, hb])
    · have hn : f x - (a j x + b j) ≠ 0 := sub_ne_zero.mpr h
      have he := (hf.continuousAt.sub ((a j).continuous.continuousAt.add_const (b j))).eventually_ne hn
      filter_upwards [he] with y hy
      intro heq
      exact (hy (sub_eq_zero.mpr heq)).elim
  filter_upwards [Filter.eventually_all.mpr hj] with y hy
  obtain ⟨j, hj⟩ := hselect y
  exact hj.trans (hy j hj)

theorem hasFDerivAt (a : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    {f : E → ℝ} (hf : Continuous f)
    (hselect : ∀ y, ∃ i, f y = a i y + b i) {x : E}
    (hx : Regular a b x) : ∃ i, HasFDerivAt f (a i) x := by
  obtain ⟨i, hi⟩ := locally_affine a b hf hselect hx
  exact ⟨i, ((a i).hasFDerivAt.add_const (b i)).congr_of_eventuallyEq hi⟩

variable [MeasurableSpace E] [BorelSpace E]

theorem regular_measurableSet (a : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    MeasurableSet {x | Regular a b x} := by
  classical
  simp only [Regular, Set.ofPred_forall]
  apply MeasurableSet.iInter; intro i
  apply MeasurableSet.iInter; intro j
  by_cases h : a i = a j
  · simp [h]
  · simp only [h, imp_false]
    exact (measurableSet_eq_fun ((a i).continuous.measurable.add_const (b i))
      ((a j).continuous.measurable.add_const (b j))).compl

theorem affine_tie_null [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (a a' : E →L[ℝ] ℝ) (b b' : ℝ) (ha : a ≠ a') :
    μ {x | a x + b = a' x + b'} = 0 := by
  let S : AffineSubspace ℝ E := AffineSubspace.comap
    (a-a').toLinearMap.toAffineMap (affineSpan ℝ ({b'-b} : Set ℝ))
  have hmem : ∀ x, x ∈ S ↔ a x + b = a' x + b' := by
    intro x
    simp only [S, AffineSubspace.mem_comap, AffineSubspace.mem_affineSpan_singleton]
    change a x - a' x = b'-b ↔ _
    constructor <;> intro h <;> linarith
  have hproper : S ≠ ⊤ := by
    intro htop
    have hall : ∀ x, a x + b = a' x + b' := fun x =>
      (hmem x).mp (by rw [htop]; exact AffineSubspace.mem_top ℝ E x)
    have hz : b = b' := by simpa using hall 0
    apply ha
    ext x
    linarith [hall x]
  have heq : (S : Set E) = {x | a x + b = a' x + b'} := Set.ext hmem
  rw [← heq]
  exact Measure.addHaar_affineSubspace μ S hproper

theorem ae_regular [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : ι → E →L[ℝ] ℝ) (b : ι → ℝ) : ∀ᵐ x ∂μ, Regular a b x := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : a i = a j
  · exact Filter.Eventually.of_forall (fun _ _ => hij)
  · have hne : ∀ᵐ x ∂μ, a i x + b i ≠ a j x + b j := by
      rw [ae_iff]
      simpa only [not_not] using affine_tie_null μ (a i) (a j) (b i) (b j) hij
    filter_upwards [hne] with x hx
    exact fun h => (hx h).elim

end VertexCover.AffineSelector


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_SignAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.AntiConcentration
noncomputable section

def centralProbability (n : ℕ) : ℝ := (n.centralBinom : ℝ) / 4^n

theorem centralProbability_nonneg (n : ℕ) : 0 ≤ centralProbability n := by
  unfold centralProbability
  positivity

theorem centralProbability_step (n : ℕ) :
    centralProbability (n+1) = centralProbability n * ((2*(n:ℝ)+1)/(2*(n:ℝ)+2)) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : 2*(n : ℝ)+2 ≠ 0 := by positivity
  have h4 : (4 : ℝ)^n ≠ 0 := by positivity
  have hrec := congrArg (fun k : ℕ => (k : ℝ)) (Nat.succ_mul_centralBinom_succ n)
  push_cast at hrec
  have hc : ((n+1).centralBinom : ℝ) = 2*(2*(n:ℝ)+1)*(n.centralBinom : ℝ)/((n:ℝ)+1) := by
    apply (eq_div_iff hn).mpr
    nlinarith [hrec]
  unfold centralProbability
  rw [hc, pow_succ]
  field_simp
  ; ring

theorem centralProbability_sq (n : ℕ) :
    centralProbability n ^ 2 * ((n : ℝ)+1) ≤ 1 := by
  induction n with
  | zero => norm_num [centralProbability]
  | succ n ih =>
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have hden : 0 < (2*(n : ℝ)+2)^2 := by positivity
      have hstep : ((2*(n : ℝ)+1)/(2*(n : ℝ)+2))^2 * ((n : ℝ)+2) ≤ (n : ℝ)+1 := by
        rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hden]
        nlinarith
      rw [centralProbability_step]
      push_cast
      calc
        _ = centralProbability n ^2 *
            ((((2*(n:ℝ)+1)/(2*(n:ℝ)+2))^2) * ((n:ℝ)+2)) := by ring
        _ ≤ centralProbability n ^2 * ((n:ℝ)+1) :=
          mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
        _ ≤ 1 := ih

theorem centralProbability_le (n : ℕ) :
    centralProbability n ≤ 1 / Real.sqrt ((n : ℝ)+1) := by
  have hs : 0 < Real.sqrt ((n : ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  apply (le_div_iff₀ hs).mpr
  have hsq : (centralProbability n * Real.sqrt ((n : ℝ)+1))^2 ≤ (1:ℝ)^2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    simpa only [one_pow] using centralProbability_sq n
  exact (sq_le_sq₀ (mul_nonneg (centralProbability_nonneg n) hs.le) zero_le_one).mp hsq

theorem centralProbability_lt (n : ℕ) (hn : 0 < n) :
    centralProbability n < Real.sqrt 2 / Real.sqrt (2*(n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hs2 : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hstrict : 1 / Real.sqrt ((n : ℝ)+1) < 1 / Real.sqrt (n : ℝ) := by
    exact one_div_lt_one_div_of_lt hnS (Real.sqrt_lt_sqrt hnR.le (by linarith))
  have heq : 1 / Real.sqrt (n : ℝ) = Real.sqrt 2 / Real.sqrt (2*(n : ℝ)) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  exact lt_of_le_of_lt (centralProbability_le n) (hstrict.trans_eq heq)

theorem sign_atom_le (n v : ℕ) :
    ((2*n).choose v : ℝ) / 2^(2*n) ≤ centralProbability n := by
  have hb : (2 : ℝ)^(2*n) = (4 : ℝ)^n := by rw [pow_mul]; norm_num
  rw [hb]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.choose_le_centralBinom v n)) (by positivity)

end
end VertexCover.AntiConcentration


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AssignmentTester
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                         

noncomputable section

namespace UniqueGames.Foundations.PCP.AssignmentTester

open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def disagree (a b : Bool) : ℝ := if a = b then 0 else 1

theorem disagree_nonneg (a b : Bool) : 0 ≤ disagree a b := by
  cases a <;> cases b <;> norm_num [disagree]

theorem disagree_xor_le (a b «c» d : Bool) :
    disagree (a ^^ b) («c» ^^ d) ≤ disagree a «c» + disagree b d := by
  cases a <;> cases b <;> cases «c» <;> cases d <;> norm_num [disagree]

def distance {K : Type*} [Fintype K] (f g : K → Bool) : ℝ :=
  𝔼 k, disagree (f k) (g k)

theorem disagree_triangle (a b «c» : Bool) :
    disagree a «c» ≤ disagree a b + disagree b «c» := by
  cases a <;> cases b <;> cases «c» <;> norm_num [disagree]

theorem and_disagree_transfer (p₀ p₁ p₂ q₀ q₁ q₂ : Bool) :
    disagree p₀ (p₁ && p₂) ≤ disagree q₀ (q₁ && q₂) +
      disagree q₀ p₀ + disagree q₁ p₁ + disagree q₂ p₂ := by
  cases p₀ <;> cases p₁ <;> cases p₂ <;>
    cases q₀ <;> cases q₁ <;> cases q₂ <;> norm_num [disagree]

end UniqueGames.Foundations.PCP.AssignmentTester
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_CodeComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                        

noncomputable section

namespace UniqueGames.Foundations.PCP.CodeComposition

open scoped BigOperators

def disagreement (a b : Bool) : ℝ := if a = b then 0 else 1

@[simp] theorem disagreement_self (a : Bool) : disagreement a a = 0 := by
  simp [disagreement]

theorem disagreement_nonnegative (a b : Bool) : 0 ≤ disagreement a b := by
  cases a <;> cases b <;> norm_num [disagreement]

theorem disagreement_comm (a b : Bool) : disagreement a b = disagreement b a := by
  simp [disagreement, eq_comm]

theorem disagreement_triangle (a b «c» : Bool) :
    disagreement a «c» ≤ disagreement a b + disagreement b «c» := by
  cases a <;> cases b <;> cases «c» <;> norm_num [disagreement]

def relativeDistance {X : Type*} [Fintype X] (f g : X → Bool) : ℝ :=
  𝔼 x, disagreement (f x) (g x)

@[simp] theorem relativeDistance_self {X : Type*} [Fintype X] (f : X → Bool) :
    relativeDistance f f = 0 := by
  simp [relativeDistance]

theorem relativeDistance_nonnegative {X : Type*} [Fintype X] (f g : X → Bool) :
    0 ≤ relativeDistance f g :=
  Finset.expect_nonneg (fun _ _ => disagreement_nonnegative _ _)

theorem relativeDistance_comm {X : Type*} [Fintype X] (f g : X → Bool) :
    relativeDistance f g = relativeDistance g f := by
  simp only [relativeDistance, disagreement_comm]

theorem relativeDistance_triangle {X : Type*} [Fintype X] (f g h : X → Bool) :
    relativeDistance f h ≤ relativeDistance f g + relativeDistance g h := by
  rw [relativeDistance, relativeDistance, relativeDistance,
    ← Finset.expect_add_distrib]
  exact Finset.expect_le_expect (fun _ _ => disagreement_triangle _ _ _)

end UniqueGames.Foundations.PCP.CodeComposition
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

noncomputable section

namespace UniqueGames.Foundations.PCP.AlphabetGraph

open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem expect_prod {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℝ) :
    (𝔼 z : I × J, f z) = 𝔼 i : I, 𝔼 j : J, f (i, j) := by
  simpa only [Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset I) (Finset.univ : Finset J) f

end UniqueGames.Foundations.PCP.AlphabetGraph

end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ClauseVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP

structure ClauseAnswer where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq

inductive Slot where
  | first
  | second
  | third
  deriving DecidableEq

def answerAt (answer : ClauseAnswer) : Slot → Bool
  | .first => answer.first
  | .second => answer.second
  | .third => answer.third

def literalValue (positive value : Bool) : Bool :=
  if positive then value else !value

def matchingSlots (a b : ClauseAnswer) : Nat :=
  (if a.first = b.first then 1 else 0) +
  (if a.second = b.second then 1 else 0) +
  (if a.third = b.third then 1 else 0)

end UniqueGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_SpectralReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.SpectralReturn

open scoped BigOperators

noncomputable section

def edgeProfile {V D : Type*} [Fintype D] (bad : V × D → Bool) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then 1 else 0)

theorem geometric_sum_le (lambda : ℝ) (h0 : 0 ≤ lambda) (h1 : lambda < 1) (n : Nat) :
    (∑ k ∈ Finset.range n, lambda ^ k) ≤ 1 / (1 - lambda) := by
  have hsum : (∑ k ∈ Finset.range n, lambda ^ k) * (1 - lambda) = 1 - lambda ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  have hden : 0 < 1 - lambda := by linarith
  apply (le_div_iff₀ hden).2
  rw [hsum]
  linarith [pow_nonneg h0 n]

end

end UniqueGames.Foundations.PCP.SpectralReturn

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ZigzagSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.ZigzagSpectral

open SpectralReturn

noncomputable section

variable {V D E : Type*}

def liftCloud (f : V → ℝ) (x : V × D) : ℝ := f x.1

end

end UniqueGames.Foundations.PCP.ZigzagSpectral

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Games_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                
section

namespace UniqueGames.Foundations.Games

open scoped BigOperators

noncomputable section

abbrev Strategy (Q₁ Q₂ A₁ A₂ : Type*) := (Q₁ → A₁) × (Q₂ → A₂)

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def simulatedStrategy {R₁ R₂ B₁ B₂ : Type*}
    (questionMap₁ : Q₁ → R₁) (questionMap₂ : Q₂ → R₂)
    (answerMap₁ : Q₁ → B₁ → A₁) (answerMap₂ : Q₂ → B₂ → A₂)
    (strategy : Strategy R₁ R₂ B₁ B₂) : Strategy Q₁ Q₂ A₁ A₂ :=
  (fun x => answerMap₁ x (strategy.1 (questionMap₁ x)),
   fun y => answerMap₂ y (strategy.2 (questionMap₂ y)))

end Game

end

end UniqueGames.Foundations.Games

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Games_KernelSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                         
section

namespace UniqueGames.Foundations.Games

open scoped BigOperators
noncomputable section

namespace KernelSampling

abbrev Seed (Q₁ Q₂ A B : Type*) := (Q₁ → A) × (Q₂ → B)

def readLeft {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₁) : A := seed.1 q
def readRight {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₂) : B := seed.2 q

section Completion

variable {I A B S : Type*} [DecidableEq I]

def completedLeft (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) : I → A :=
  Function.update (readLeft seed q) j q.1

def completedRight (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) : I → B :=
  Function.update (readRight seed q) j q.1

@[simp] theorem completedLeft_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) :
    completedLeft j seed q j = q.1 := by simp [completedLeft]

@[simp] theorem completedRight_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) :
    completedRight j seed q j = q.1 := by simp [completedRight]

theorem update_eq_of_coordinate (xs : I → A) (j : I) (a : A)
    (h : xs j = a) : Function.update xs j a = xs := by
  funext i
  by_cases hi : i = j <;> simp [Function.update, hi, h]

end Completion

end KernelSampling
end
end UniqueGames.Foundations.Games

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Information_Finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsProbability (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

def SupportedBy (p q : α → ℝ) : Prop := ∀ a, p a ≠ 0 → q a ≠ 0

noncomputable def relativeEntropy (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

noncomputable def totalVariation (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

noncomputable def posterior (p w : α → ℝ) (z : ℝ) : α → ℝ :=
  fun a => p a * w a / z

theorem posterior_isProbability (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) : IsProbability (posterior p w z) := by
  constructor
  · intro a
    exact div_nonneg (mul_nonneg (hp.1 a) (hw a)) hz.le
  · simp only [posterior, div_eq_mul_inv, ← Finset.sum_mul, hmass,
      mul_inv_cancel₀ hz.ne']

omit [Fintype α] in
theorem posterior_supportedBy (p w : α → ℝ) (z : ℝ) :
    SupportedBy (posterior p w z) p := by
  intro a ha hp
  exact ha (by simp [posterior, hp])

theorem mul_log_div_ge_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
  have hm := mul_le_mul_of_nonneg_left h hx.le
  have he : x * (1 - (x / y)⁻¹) = x - y := by
    field_simp [hx.ne', hy.ne']
  rwa [he] at hm

theorem relativeEntropy_nonneg (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) : 0 ≤ relativeEntropy p q := by
  have hpoint : ∀ a, p a - q a ≤ p a * Real.log (p a / q a) := by
    intro a
    by_cases hpa : p a = 0
    · simp only [hpa, zero_sub, zero_div, zero_mul]
      exact neg_nonpos.mpr (hq.1 a)
    · exact mul_log_div_ge_sub (lt_of_le_of_ne (hp.1 a) (Ne.symm hpa))
        (lt_of_le_of_ne (hq.1 a) (Ne.symm (hs a hpa)))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa [relativeEntropy, Finset.sum_sub_distrib, hp.2, hq.2] using hsum

theorem posterior_relativeEntropy_le (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) (hw_one : ∀ a, w a ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) :
    relativeEntropy (posterior p w z) p ≤ Real.log (1 / z) := by
  have hpost := posterior_isProbability p w hp hw hz hmass
  have hpoint : ∀ a, posterior p w z a * Real.log (posterior p w z a / p a) ≤
      posterior p w z a * Real.log (1 / z) := by
    intro a
    by_cases hpa : posterior p w z a = 0
    · simp [hpa]
    have hpne := posterior_supportedBy p w z a hpa
    have hppos : 0 < p a := lt_of_le_of_ne (hp.1 a) (Ne.symm hpne)
    have hpostpos : 0 < posterior p w z a :=
      lt_of_le_of_ne (hpost.1 a) (Ne.symm hpa)
    have hr : posterior p w z a / p a = w a / z := by
      dsimp [posterior]
      field_simp [hpne, hz.ne']
    apply mul_le_mul_of_nonneg_left _ (hpost.1 a)
    apply Real.log_le_log (div_pos hpostpos hppos)
    rw [hr]
    exact div_le_div_of_nonneg_right (hw_one a) hz.le
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa only [relativeEntropy, ← Finset.sum_mul, hpost.2, one_mul] using hsum

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => abs_nonneg (p a - q a))) (by norm_num)

theorem totalVariation_symm (p q : α → ℝ) : totalVariation p q = totalVariation q p := by
  simp only [totalVariation, abs_sub_comm]

theorem weighted_sum_sq_le (w x : α → ℝ) (hw : IsProbability w) :
    (∑ a, w a * x a)^2 ≤ ∑ a, w a * (x a)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => Real.sqrt (w a)) (fun a => Real.sqrt (w a) * x a)
  have hfirst : ∀ a, Real.sqrt (w a) * (Real.sqrt (w a) * x a) = w a * x a := by
    intro a
    rw [← mul_assoc, Real.mul_self_sqrt (hw.1 a)]
  have hsecond : ∀ a, (Real.sqrt (w a) * x a)^2 = w a * (x a)^2 := by
    intro a
    rw [mul_pow, Real.sq_sqrt (hw.1 a)]
  simpa only [hfirst, hsecond, Real.sq_sqrt (hw.1 _), hw.2, one_mul] using hcs

end UniqueGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Information_ChainRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                          
section

namespace UniqueGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def firstMarginal (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)

noncomputable def secondMarginal (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)

theorem firstMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (firstMarginal p) := by
  constructor
  · intro a
    exact Finset.sum_nonneg (fun b _ => hp.1 (a, b))
  · simpa only [firstMarginal, Fintype.sum_prod_type] using hp.2

theorem point_le_firstMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ firstMarginal p a := by
  classical
  exact Finset.single_le_sum (fun b _ => hp.1 (a, b)) (Finset.mem_univ b)

end UniqueGames.Foundations.Information

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Information_Conditionals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ) (a : α) (b : β) : ℝ := by
  classical
  exact if firstMarginal p a = 0 then fallback b
    else p (a, b) / firstMarginal p a

theorem kernelProduct_isProbability
    (r : α → ℝ) (k : α → β → ℝ)
    (hr : IsProbability r) (hk : ∀ a, IsProbability (k a)) :
    IsProbability (fun ab : α × β => r ab.1 * k ab.1 ab.2) := by
  constructor
  · intro ab
    exact mul_nonneg (hr.1 ab.1) ((hk ab.1).1 ab.2)
  · simp only [Fintype.sum_prod_type, ← Finset.mul_sum,
      (hk _).2, mul_one, hr.2]

end UniqueGames.Foundations.Information

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Information_Kernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                        
section

namespace UniqueGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem totalVariation_joint_common_weights (w : α → ℝ) (p q : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    totalVariation (fun ab : α × β => w ab.1 * p ab.1 ab.2)
      (fun ab : α × β => w ab.1 * q ab.1 ab.2) =
        ∑ a, w a * totalVariation (p a) (q a) := by
  have hpoint : ∀ a b, |w a * p a b - w a * q a b| = w a * |p a b - q a b| := by
    intro a b
    rw [← mul_sub, abs_mul, abs_of_nonneg (hw a)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    div_eq_mul_inv, Finset.sum_mul, mul_assoc]

theorem totalVariation_joint_common_kernel (p q : α → ℝ) (k : α → β → ℝ)
    (hk : ∀ a, IsProbability (k a)) :
    totalVariation (fun ab : α × β => p ab.1 * k ab.1 ab.2)
      (fun ab : α × β => q ab.1 * k ab.1 ab.2) = totalVariation p q := by
  have hpoint : ∀ a b, |p a * k a b - q a * k a b| = |p a - q a| * k a b := by
    intro a b
    rw [← sub_mul, abs_mul, abs_of_nonneg ((hk a).1 b)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    (hk _).2, mul_one]

theorem weighted_coordinate_sum_sq_le
    (w : α → ℝ) (d : α → β → ℝ) (C : α → ℝ)
    (hw : IsProbability w)
    (hbudget : ∀ a, w a * (∑ b, d a b ^ 2) ≤ w a * C a) :
    (∑ b, ∑ a, w a * d a b)^2 ≤
      (Fintype.card β : ℝ) * (∑ a, w a * C a) := by
  have hv := Finset.sum_le_sum
    (fun b (_ : b ∈ (Finset.univ : Finset β)) =>
      weighted_sum_sq_le w (fun a => d a b) hw)
  have he :
      (∑ b, ∑ a, w a * d a b ^ 2) =
        ∑ a, w a * (∑ b, d a b ^ 2) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [he] at hv
  have hb := Finset.sum_le_sum
    (fun a (_ : a ∈ (Finset.univ : Finset α)) => hbudget a)
  have hs := hv.trans hb
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset β)
    (fun b => ∑ a, w a * d a b) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  calc
    (∑ b, ∑ a, w a * d a b)^2
        ≤ (∑ b, (∑ a, w a * d a b)^2) *
            (Fintype.card β : ℝ) := hcs
    _ = (Fintype.card β : ℝ) *
          (∑ b, (∑ a, w a * d a b)^2) := mul_comm _ _
    _ ≤ (Fintype.card β : ℝ) * (∑ a, w a * C a) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)

end UniqueGames.Foundations.Information

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_Variation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                         
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Information

variable {α β : Type*} [Fintype α] [Fintype β]

theorem totalVariation_triangle (p q r : α → ℝ) :
    totalVariation p r ≤ totalVariation p q + totalVariation q r := by
  have hpoint : ∀ a, |p a - r a| ≤ |p a - q a| + |q a - r a| := by
    intro a
    have := abs_add_le (p a - q a) (q a - r a)
    simpa only [sub_add_sub_cancel] using this
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [Finset.sum_add_distrib] at hsum
  unfold totalVariation
  linarith

noncomputable def kernelPushforward (p : α → ℝ) (kernel : α → β → ℝ) : β → ℝ :=
  fun b => ∑ a, p a * kernel a b

theorem totalVariation_kernelPushforward_le (p q : α → ℝ) (kernel : α → β → ℝ)
    (hk : ∀ a, IsProbability (kernel a)) :
    totalVariation (kernelPushforward p kernel) (kernelPushforward q kernel) ≤
      totalVariation p q := by
  have hpoint : ∀ b,
      |kernelPushforward p kernel b - kernelPushforward q kernel b| ≤
        ∑ a, |p a - q a| * kernel a b := by
    intro b
    simp only [kernelPushforward, ← Finset.sum_sub_distrib, ← sub_mul]
    have h := Finset.abs_sum_le_sum_abs (fun a => (p a - q a) * kernel a b) Finset.univ
    have habs : ∀ a, |kernel a b| = kernel a b := fun a => abs_of_nonneg ((hk a).1 b)
    simpa only [abs_mul, habs] using h
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset β)) => hpoint b)
  rw [Finset.sum_comm] at hsum
  simp only [← Finset.mul_sum, (hk _).2, mul_one] at hsum
  exact div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)

end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_Overlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                       
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Information

theorem min_half_formula (x y : ℝ) :
    min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem sum_min_one_sub_tv {Ω : Type*} [Fintype Ω]
    (p q : Ω → ℝ) (hp : IsProbability p) (hq : IsProbability q) :
    (∑ z, min (p z) (q z)) = 1 - totalVariation p q := by
  classical
  simp_rw [min_half_formula]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp.2, hq.2, totalVariation]
  ring

theorem discount_le_self {«c» t : ℝ} (hc : 0 ≤ «c») (ht : 0 ≤ t) :
    «c» / (1 + t) ≤ «c» := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + t)).2
  nlinarith [mul_nonneg hc ht]

theorem discount_loss_le_mul {«c» t : ℝ} (hc : 0 ≤ «c») (ht : 0 ≤ t) :
    «c» - «c» / (1 + t) ≤ «c» * t := by
  have hd : 0 < 1 + t := by linarith
  have hid : «c» - «c» / (1 + t) = «c» * t / (1 + t) := by
    field_simp [hd.ne']
    ; ring
  rw [hid]
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg (mul_nonneg hc ht) ht]

noncomputable def discountedCommonMass {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (t : X → ℝ) : ℝ :=
  ∑ z, min (p z) (min (a z) (b z)) / (1 + t z.1)

theorem discounted_common_mass_bounds {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (μ t : X → ℝ)
    (hp : IsProbability p) (ha : IsProbability a) (hb : IsProbability b)
    (ht : ∀ x, 0 ≤ t x)
    (hrow : ∀ x, (∑ s, a (x, s)) = μ x)
    (htv : (∑ x, μ x * t x) = totalVariation a b) :
    1 - 2 * totalVariation p a - 2 * totalVariation p b ≤ discountedCommonMass p a b t ∧
      discountedCommonMass p a b t ≤ 1 := by
  classical
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have hC0 : ∀ z, 0 ≤ C z := by
    intro z
    exact le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
  have hCp : ∀ z, C z ≤ p z := by
    intro z
    exact min_le_left _ _
  have hCa : ∀ z, C z ≤ a z := by
    intro z
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmass : 1 - totalVariation p a - totalVariation p b ≤ ∑ z, C z := by
    have hpoint : ∀ z, min (p z) (a z) + min (p z) (b z) - p z ≤ C z := by
      intro z
      dsimp [C]
      refine le_min ?_ (le_min ?_ ?_)
      · linarith [min_le_left (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (b z), min_le_left (p z) (a z)]
    have hsum := Finset.sum_le_sum
      (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
    rw [sum_min_one_sub_tv p a hp ha, sum_min_one_sub_tv p b hp hb, hp.2] at hsum
    linarith
  have hrowC : ∀ x, (∑ s, C (x, s)) ≤ μ x := by
    intro x
    calc
      (∑ s, C (x, s)) ≤ ∑ s, a (x, s) := Finset.sum_le_sum (fun s _ => hCa (x, s))
      _ = μ x := hrow x
  have hweighted : (∑ z, C z * t z.1) ≤ totalVariation a b := by
    rw [← htv, Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro x _
    change (∑ s, C (x, s) * t x) ≤ μ x * t x
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrowC x) (ht x)
  have hloss : (∑ z, C z) - discountedCommonMass p a b t ≤ ∑ z, C z * t z.1 := by
    change (∑ z, C z) - (∑ z, C z / (1 + t z.1)) ≤ ∑ z, C z * t z.1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun z _ => discount_loss_le_mul (hC0 z) (ht z.1))
  have htriangle : totalVariation a b ≤ totalVariation p a + totalVariation p b := by
    have h := totalVariation_triangle a p b
    rw [totalVariation_symm a p] at h
    exact h
  have hupper : discountedCommonMass p a b t ≤ 1 := by
    change (∑ z, C z / (1 + t z.1)) ≤ 1
    calc
      _ ≤ ∑ z, p z := Finset.sum_le_sum
        (fun z _ => (discount_le_self (hC0 z) (ht z.1)).trans (hCp z))
      _ = 1 := hp.2
  exact ⟨by linarith, hupper⟩

noncomputable def diagonalWeights {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) : X × S × S → ℝ := by
  classical
  exact fun z => if z.2.1 = z.2.2 then p (z.1, z.2.1) else 0

theorem diagonalWeights_isProbability {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (hp : IsProbability p) : IsProbability (diagonalWeights p) := by
  classical
  constructor
  · intro z
    dsimp [diagonalWeights]
    split
    · exact hp.1 _
    · exact le_rfl
  · simpa [diagonalWeights, Fintype.sum_prod_type] using hp.2

theorem diagonal_overlap_identity {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (sim : X × S × S → ℝ)
    (hp : IsProbability p) (hsim : IsProbability sim) :
    totalVariation sim (diagonalWeights p) =
      1 - ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
  classical
  have h := sum_min_one_sub_tv sim (diagonalWeights p) hsim (diagonalWeights_isProbability p hp)
  have heq : (∑ z, min (sim z) (diagonalWeights p z)) =
      ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
    simp only [Fintype.sum_prod_type, diagonalWeights]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro s _
    have hpoint : ∀ s', min (sim (x, s, s')) (if s = s' then p (x, s) else 0) =
        if s = s' then min (p (x, s)) (sim (x, s, s')) else 0 := by
      intro s'
      by_cases he : s = s'
      · simp [he, min_comm]
      · simp [he, min_eq_right (hsim.1 (x, s, s'))]
    simp only [hpoint]
    simp
  rw [heq] at h
  linarith

theorem diagonal_sampler_totalVariation_le {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (μ : X → ℝ) (L R : X → S → ℝ)
    (sim : X × S × S → ℝ) (hp : IsProbability p) (hμ : IsProbability μ)
    (hL : ∀ x, IsProbability (L x)) (hR : ∀ x, IsProbability (R x))
    (hsim : IsProbability sim) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hdiag : ∀ x s, μ x * min (L x s) (R x s) /
      (1 + totalVariation (L x) (R x)) * (1 - τ) ≤ sim (x, s, s)) :
    totalVariation sim (diagonalWeights p) ≤
      2 * totalVariation p (fun z => μ z.1 * L z.1 z.2) +
      2 * totalVariation p (fun z => μ z.1 * R z.1 z.2) + τ := by
  classical
  let a : X × S → ℝ := fun z => μ z.1 * L z.1 z.2
  let b : X × S → ℝ := fun z => μ z.1 * R z.1 z.2
  let t : X → ℝ := fun x => totalVariation (L x) (R x)
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have ha : IsProbability a := kernelProduct_isProbability μ L hμ hL
  have hb : IsProbability b := kernelProduct_isProbability μ R hμ hR
  have ht : ∀ x, 0 ≤ t x := fun x => totalVariation_nonneg (L x) (R x)
  have hrow : ∀ x, (∑ s, a (x, s)) = μ x := by
    intro x
    simp only [a, ← Finset.mul_sum, (hL x).2, mul_one]
  have htv : (∑ x, μ x * t x) = totalVariation a b :=
    (totalVariation_joint_common_weights μ L R hμ.1).symm
  obtain ⟨hBlower, hBupper⟩ := discounted_common_mass_bounds p a b μ t hp ha hb ht hrow htv
  have hpoint : ∀ z : X × S,
      (1 - τ) * (C z / (1 + t z.1)) ≤ min (p z) (sim (z.1, z.2, z.2)) := by
    intro z
    have hden : 0 < 1 + t z.1 := by linarith [ht z.1]
    have hC0 : 0 ≤ C z := le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
    have hCp : C z ≤ p z := min_le_left _ _
    have hdisc0 : 0 ≤ C z / (1 + t z.1) := div_nonneg hC0 hden.le
    have hmin : min (a z) (b z) = μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      dsimp [a, b]
      rcases le_total (L z.1 z.2) (R z.1 z.2) with h | h
      · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
      · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
    have hCmin : C z ≤ μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      rw [← hmin]
      exact min_le_right _ _
    apply le_min
    · calc
        _ ≤ 1 * (C z / (1 + t z.1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hdisc0
        _ ≤ C z := by simpa using discount_le_self hC0 (ht z.1)
        _ ≤ p z := hCp
    · have hd := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hCmin hden.le) (by linarith : 0 ≤ 1 - τ)
      calc
        _ ≤ (1 - τ) * (μ z.1 * min (L z.1 z.2) (R z.1 z.2) / (1 + t z.1)) := hd
        _ ≤ sim (z.1, z.2, z.2) := by
          simpa only [t, mul_comm] using hdiag z.1 z.2
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
  rw [← Finset.mul_sum] at hsum
  change (1 - τ) * discountedCommonMass p a b t ≤ _ at hsum
  rw [diagonal_overlap_identity p sim hp hsim]
  have hτB := mul_le_mul_of_nonneg_left hBupper hτ0
  change 1 - _ ≤ 2 * totalVariation p a + 2 * totalVariation p b + τ
  nlinarith

end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Sampling_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.CorrelatedSampling

noncomputable section FiniteWeights

variable {α : Type*} [Fintype α]

def totalVariation (p q : α → ℝ) : ℝ := (∑ a, |p a - q a|) / 2

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

theorem max_abs_identity (x y : ℝ) : 2 * max x y - |x - y| = x + y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

end FiniteWeights

end UniqueGames.Foundations.CorrelatedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SharedSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                              
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

universe u

def TraceSeed (σ : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => σ × TraceSeed σ n

instance traceSeedFintype {σ : Type*} [Fintype σ] (n : Nat) : Fintype (TraceSeed σ n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (σ × TraceSeed σ n))

instance traceSeedUniqueZero {σ : Type*} : Unique (TraceSeed σ 0) :=
  inferInstanceAs (Unique PUnit)

def traceList {σ : Type*} : (n : Nat) → TraceSeed σ n → List σ
  | 0, _ => []
  | n + 1, seed => seed.1 :: traceList n seed.2

end
end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_CompletedSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                 
section

namespace UniqueGames.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

abbrev Seed (Γ X Y S U V : Type*) :=
  Γ × KernelSampling.Seed (X × S) (Y × S) U V

def left (sL : Γ → X → S) (seed : Seed Γ X Y S U V) (x : X) : U :=
  KernelSampling.readLeft seed.2 (x, sL seed.1 x)

def right (sR : Γ → Y → S) (seed : Seed Γ X Y S U V) (y : Y) : V :=
  KernelSampling.readRight seed.2 (y, sR seed.1 y)

end Completion

section CoordinateCompletion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def coordinateLeft (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) : I → X :=
  KernelSampling.completedLeft j seed.2 (x, sL seed.1 x)

def coordinateRight (j : I) (sR : Γ → Y → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (y : Y) : I → Y :=
  KernelSampling.completedRight j seed.2 (y, sR seed.1 y)

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
@[simp] theorem coordinateLeft_preserves (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) :
    coordinateLeft j sL seed x j = x := by
  simp [coordinateLeft]

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
@[simp] theorem coordinateRight_preserves (j : I) (sR : Γ → Y → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (y : Y) :
    coordinateRight j sR seed y j = y := by
  simp [coordinateRight]

end CoordinateCompletion

end

end UniqueGames.Foundations.Repetition.CompletedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_PairEventMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover

noncomputable def truthValue (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

end VertexCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_ExpanderTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.ExpanderTables

open SpectralReturn

def vertexCount (q : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => vertexCount q n * (q * q)

theorem vertexCount_eq (q n : Nat) : vertexCount q n = (q * q) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [vertexCount, ih, pow_succ]

theorem vertexCount_positive {q : Nat} (hq : 0 < q) (n : Nat) :
    0 < vertexCount q n := by
  rw [vertexCount_eq]
  exact Nat.pow_pos (Nat.mul_pos hq hq)

end UniqueGames.Foundations.PCP.ExpanderTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_GraphGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                 

noncomputable section

namespace UniqueGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

variable {W D B : Type*}

def labelingEquiv (vertices : V ≃ W) (labels : A ≃ B) : (V → A) ≃ (W → B) where
  toFun := fun labeling w => labels (labeling (vertices.symm w))
  invFun := fun labeling v => labels.symm (labeling (vertices v))
  left_inv := by intro labeling; funext v; simp
  right_inv := by intro labeling; funext w; simp

end UniqueGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_LazySmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGames.Foundations.PCP.LazySmoothing

open scoped BigOperators

def bitCount {n : ℕ} (tape : Fin n → Bool) : ℕ :=
  ∑ i, if tape i then 1 else 0

noncomputable def binomialMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  Finset.univ.expect (fun tape : Fin n → Bool => g (bitCount tape))

def splitTape (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Bool × (Fin n → Bool)) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv _ := rfl

theorem bitCount_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    bitCount x = (if x 0 then 1 else 0) + bitCount (fun i => x i.succ) := by
  exact Fin.sum_univ_succ _

theorem mean_congr {n : ℕ} {f g : ℕ → ℝ} (h : ∀ k, f k = g k) :
    binomialMean n f = binomialMean n g := by
  unfold binomialMean
  exact Finset.expect_congr rfl (fun x _ => h (bitCount x))

@[simp] theorem mean_const (n : ℕ) («c» : ℝ) :
    binomialMean n (fun _ => «c») = «c» := Fintype.expect_const «c»

theorem mean_add (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k + g k) = binomialMean n f + binomialMean n g :=
  Finset.expect_add_distrib _ _ _

theorem mean_sub (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k - g k) = binomialMean n f - binomialMean n g :=
  Finset.expect_sub_distrib _ _ _

theorem mean_mul (n : ℕ) («c» : ℝ) (f : ℕ → ℝ) :
    binomialMean n (fun k => «c» * f k) = «c» * binomialMean n f := by
  exact (Finset.mul_expect Finset.univ (fun x : Fin n → Bool => f (bitCount x)) «c»).symm

@[simp] theorem mean_zero (g : ℕ → ℝ) : binomialMean 0 g = g 0 := by
  simp [binomialMean, bitCount]

theorem expect_bool (f : Bool → ℝ) : Finset.univ.expect f = (f false + f true) / 2 := by
  rw [Finset.expect_eq_sum_div_card]
  simp [Fintype.univ_bool, add_comm]

theorem mean_succ (n : ℕ) (g : ℕ → ℝ) :
    binomialMean (n + 1) g =
      (binomialMean n g + binomialMean n (fun k => g (k + 1))) / 2 := by
  unfold binomialMean
  rw [Fintype.expect_equiv (splitTape n)
    (fun x => g (bitCount x))
    (fun x => g ((if x.1 then 1 else 0) + bitCount x.2))
    (fun x => congrArg g (bitCount_succ x))]
  rw [← Finset.univ_product_univ, Finset.expect_product, expect_bool]
  simp [Nat.add_comm]

def score (n k : ℕ) : ℝ := (n : ℝ) - 2 * (k : ℝ)

noncomputable def scoreMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  binomialMean n (fun k => score n k * g k)

@[simp] theorem scoreMean_zero (g : ℕ → ℝ) : scoreMean 0 g = 0 := by
  simp [scoreMean, score]

theorem scoreMean_succ (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g =
      ((scoreMean n g + binomialMean n g) +
       (scoreMean n (fun k => g (k + 1)) -
        binomialMean n (fun k => g (k + 1)))) / 2 := by
  unfold scoreMean
  rw [mean_succ]
  have h₁ : (fun k => score (n + 1) k * g k) =
      (fun k => score n k * g k + g k) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  have h₂ : (fun k => score (n + 1) (k + 1) * g (k + 1)) =
      (fun k => score n k * g (k + 1) - g (k + 1)) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  rw [h₁, h₂, mean_add, mean_sub]

theorem score_identity (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) / 2 *
      (binomialMean n g - binomialMean n (fun k => g (k + 1))) := by
  induction n generalizing g with
  | zero => simp [scoreMean_succ]; ring
  | succ n ih =>
    rw [scoreMean_succ, ih g, ih (fun k => g (k + 1))]
    simp only [mean_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem score_mean_zero (n : ℕ) : binomialMean n (score n) = 0 := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (fun _ => 1)
    simpa [scoreMean] using h

theorem score_second_moment (n : ℕ) :
    binomialMean n (fun k => score n k ^ 2) = (n : ℝ) := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (score (n + 1))
    have hd : binomialMean n (score (n + 1)) -
        binomialMean n (fun k => score (n + 1) (k + 1)) = 2 := by
      rw [← mean_sub]
      calc
        _ = binomialMean n (fun _ => 2) := by
          apply mean_congr
          intro k
          simp only [score, Nat.cast_add, Nat.cast_one]
          ring
        _ = 2 := mean_const _ _
    rw [hd] at h
    simpa [scoreMean, pow_two] using h

theorem score_difference (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) := by
  rw [score_identity, mean_succ]
  ring

theorem adjacent_difference_sq (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    4 * ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) ^ 2 ≤ 1 := by
  have hc : binomialMean (n + 1)
      (fun k => score (n + 1) k * (g k - 1 / 2)) = scoreMean (n + 1) g := by
    calc
      _ = binomialMean (n + 1) (fun k =>
          score (n + 1) k * g k - (1 / 2) * score (n + 1) k) := by
        apply mean_congr
        intro k
        ring
      _ = scoreMean (n + 1) g := by
        rw [mean_sub, mean_mul, score_mean_zero]
        simp [scoreMean]
  have hv : binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) ≤ 1 / 4 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro tape _
    have h₀ := (hg (bitCount tape)).1
    have h₁ := (hg (bitCount tape)).2
    have hp := mul_nonneg h₀ (sub_nonneg.mpr h₁)
    nlinarith
  have hcs : (binomialMean (n + 1)
        (fun k => score (n + 1) k * (g k - 1 / 2))) ^ 2 ≤
      binomialMean (n + 1) (fun k => score (n + 1) k ^ 2) *
        binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) :=
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ _ _
  rw [hc, score_difference, score_second_moment] at hcs
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hv (le_of_lt hn)
  simp only [Nat.cast_add, Nat.cast_one] at hcs
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

theorem adjacent_difference_le (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean n g - binomialMean (n + 1) g| ≤ 1 / r := by
  have hs := adjacent_difference_sq n g hg
  have hd := sq_nonneg (binomialMean n g - binomialMean (n + 1) g)
  have hh := mul_le_mul_of_nonneg_right hrn hd
  rw [le_div_iff₀ hr]
  have ha := sq_abs (binomialMean n g - binomialMean (n + 1) g)
  have hp : 0 ≤ |binomialMean n g - binomialMean (n + 1) g| * r :=
    mul_nonneg (abs_nonneg _) (le_of_lt hr)
  nlinarith [sq_nonneg (|binomialMean n g - binomialMean (n + 1) g| * r - 1)]

theorem mean_shift_le (n d : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean (n + d) g - binomialMean n g| ≤ (d : ℝ) / r := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hrnd : r ^ 2 ≤ 4 * ((n + d : ℕ) + 1 : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith
    have ha := adjacent_difference_le (n + d) g hg r hr hrnd
    rw [abs_sub_comm] at ha
    calc
      _ ≤ |binomialMean (n + d + 1) g - binomialMean (n + d) g| +
          |binomialMean (n + d) g - binomialMean n g| := abs_sub_le _ _ _
      _ ≤ 1 / r + (d : ℝ) / r := add_le_add ha ih
      _ = ((d + 1 : ℕ) : ℝ) / r := by push_cast; ring

theorem mean_ordered_difference_le (m n : ℕ) (hmn : m ≤ n) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1)) :
    |binomialMean n g - binomialMean m g| ≤ ((n - m : ℕ) : ℝ) / r := by
  simpa [Nat.add_sub_of_le hmn] using mean_shift_le m (n - m) g hg r hr hrm

theorem mean_window_le (N M m : ℕ) (hlo : N - M ≤ m) (hhi : m ≤ N + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (r : ℝ) (hr : 0 < r) (hbase : r ^ 2 ≤ 4 * (((N - M : ℕ) : ℝ) + 1)) :
    |binomialMean m g - binomialMean N g| ≤ (M : ℝ) / r := by
  by_cases hmN : m ≤ N
  · have hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlo
      linarith
    have h := mean_ordered_difference_le m N hmN g hg r hr hrm
    rw [abs_sub_comm] at h
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : N - m ≤ M := by omega
    exact_mod_cast this
  · have hNm : N ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmN)
    have hrN : r ^ 2 ≤ 4 * ((N : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N M
      linarith
    have h := mean_ordered_difference_le N m hNm g hg r hr hrN
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : m - N ≤ M := by omega
    exact_mod_cast this

theorem square_window_le (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    |binomialMean m g - binomialMean ((4 * q * M) ^ 2) g| ≤ 1 / (4 * (q : ℝ)) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR : (4 : ℝ) * M ≤ ((4 * q * M : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hRM : (M : ℝ) ≤ (((4 * q * M : ℕ) : ℝ)) ^ 2 := by nlinarith
  have hMN : M ≤ (4 * q * M) ^ 2 := by exact_mod_cast hRM
  have hr : (0 : ℝ) < ((4 * q * M : ℕ) : ℝ) := by linarith
  have hb : (((4 * q * M : ℕ) : ℝ)) ^ 2 ≤
      4 * (((((4 * q * M) ^ 2 - M : ℕ)) : ℝ) + 1) := by
    rw [Nat.cast_sub hMN, Nat.cast_pow]
    nlinarith
  have h := mean_window_le ((4 * q * M) ^ 2) M m hlo hhi g hg
    ((4 * q * M : ℕ) : ℝ) hr hb
  have he : (M : ℝ) / ((4 * q * M : ℕ) : ℝ) = 1 / (4 * (q : ℝ)) := by
    push_cast
    have hq0 : (q : ℝ) ≠ 0 := by linarith
    have hM0 : (M : ℝ) ≠ 0 := by linarith
    field_simp
  rw [he] at h
  exact h

theorem modal_transfer (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (hmodal : 1 / (q : ℝ) ≤ binomialMean ((4 * q * M) ^ 2) g) :
    1 / (2 * (q : ℝ)) ≤ binomialMean m g := by
  have h := square_window_le q M m hq hM hlo hhi g hg
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hrec : 0 < 1 / (q : ℝ) := one_div_pos.mpr hqR
  have he₁ : 1 / (4 * (q : ℝ)) = (1 / (q : ℝ)) / 4 := by ring
  have he₂ : 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) / 2 := by ring
  rw [he₁] at h
  rw [he₂]
  have hl := (abs_le.mp h).1
  linarith

end UniqueGames.Foundations.PCP.LazySmoothing

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingOverlayTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                   

namespace UniqueGames.Foundations.PCP.PreprocessingOverlayTables

def lazyPorts (d : Nat) : (Bool × Fin d) ≃ Fin (2 * d) :=
  (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl (Fin d))).trans finProdFinEquiv

end UniqueGames.Foundations.PCP.PreprocessingOverlayTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_GraphComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.ExplicitGraph
noncomputable section

 theorem coverNumber_le {G : ExplicitGraph} (C : Finset (Fin G.n)) (hC : G.Cover C) :
    G.coverNumber ≤ C.card := Nat.find_min' _ ⟨C,hC,rfl⟩

end
end VertexCover.ExplicitGraph


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Analysis_SelectedIntegralAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Average
open MeasureTheory

noncomputable def fiberAverage {α β : Type*} [Fintype α]
    (q : α → β) (f : β → α → ℝ) (i : β) : ℝ := by
  classical
  exact (∑ a ∈ Finset.univ.filter (fun a => q a = i), f i a) /
    (Finset.univ.filter (fun a => q a = i)).card

end VertexCover.Average


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_SourceContexts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                          
section

namespace UniqueGames.Foundations.Hastad.SourceContexts

open PCP

def clauseAnswerEquiv : ClauseAnswer ≃ Bool × Bool × Bool where
  toFun a := (a.first, a.second, a.third)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨a, b, «c»⟩; rfl

def clauseAnswerFinEquiv : ClauseAnswer ≃ Fin 8 :=
  clauseAnswerEquiv.trans
    ((Equiv.prodCongr finTwoEquiv.symm
      (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm)).trans
      ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv))

instance clauseAnswerFintype : Fintype ClauseAnswer :=
  Fintype.ofEquiv (Bool × Bool × Bool) clauseAnswerEquiv.symm

instance clauseAnswerInhabited : Inhabited ClauseAnswer := ⟨⟨false, false, false⟩⟩

instance slotFintype : Fintype Slot where
  elems := {.first, .second, .third}
  complete s := by cases s <;> simp

instance slotInhabited : Inhabited Slot := ⟨.first⟩

@[simp] theorem card_clauseAnswer : Fintype.card ClauseAnswer = 8 := by
  rw [Fintype.card_congr clauseAnswerFinEquiv]
  rfl

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide

abbrev J (u : ℕ) := Fin u → ClauseAnswer
@[simp] theorem card_J (u : ℕ) : Fintype.card (J u) = 8 ^ u := by simp [J]

end UniqueGames.Foundations.Hastad.SourceContexts

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_CloneGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                           
section

namespace UniqueGames.Reduction.CloneGap

variable {α β : Type*} {Name : Type}

structure Equation (Name : Type) where
  first : Name
  second : Name
  third : Name
  rhs : Bool

end UniqueGames.Reduction.CloneGap
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Fourier_SourceOccurrences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.Hastad.SourceOccurrences

open UniqueGames.Reduction.CloneGap
open scoped BigOperators

structure Encoding (α : Type) where
  size : ℕ
  code : α ≃ Fin size

namespace Encoding

def fin (n : ℕ) : Encoding (Fin n) := ⟨n, Equiv.refl _⟩
def bool : Encoding Bool := ⟨2, finTwoEquiv.symm⟩
def unit : Encoding Unit := ⟨1, finOneEquiv.symm⟩

def prod {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α × β) :=
  ⟨a.size * b.size, (Equiv.prodCongr a.code b.code).trans finProdFinEquiv⟩

def sum {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α ⊕ β) :=
  ⟨a.size + b.size, (Equiv.sumCongr a.code b.code).trans finSumFinEquiv⟩

def function {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α → β) where
  size := b.size ^ a.size
  code := (show (α → β) ≃ (Fin a.size → Fin b.size) from
    { toFun := fun f i => b.code (f (a.code.symm i))
      invFun := fun f x => b.code.symm (f (a.code x))
      left_inv := by intro f; funext x; simp
      right_inv := by intro f; funext i; simp }).trans finFunctionFinEquiv

end Encoding

end UniqueGames.Foundations.Hastad.SourceOccurrences

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Information_LogSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                       
section

namespace UniqueGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem normalize_isProbability (b : α → ℝ) (hb : ∀ a, 0 ≤ b a)
    {B : ℝ} (hB : 0 < B) (hmass : ∑ a, b a = B) :
    IsProbability (fun a => b a / B) := by
  constructor
  · intro a
    exact div_nonneg (hb a) hB.le
  · simp only [div_eq_mul_inv, ← Finset.sum_mul, hmass, mul_inv_cancel₀ hB.ne']

theorem relativeEntropy_normalize_right (p b : α → ℝ) (hp : IsProbability p)
    (hs : SupportedBy p b) {B : ℝ} (hB : 0 < B) :
    relativeEntropy p (fun a => b a / B) = relativeEntropy p b + Real.log B := by
  have hpoint : ∀ a, p a * Real.log (p a / (b a / B)) =
      p a * Real.log (p a / b a) + p a * Real.log B := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    have hbne := hs a hpa
    rw [Real.log_div hpa (div_ne_zero hbne hB.ne'), Real.log_div hbne hB.ne',
      Real.log_div hpa hbne]
    ring
  simp only [relativeEntropy, hpoint, Finset.sum_add_distrib, ← Finset.sum_mul, hp.2, one_mul]

theorem neg_relativeEntropy_le_log_mass (p b : α → ℝ) (hp : IsProbability p)
    (hb : ∀ a, 0 ≤ b a) (hs : SupportedBy p b) {B : ℝ} (hB : 0 < B)
    (hmass : ∑ a, b a = B) : -relativeEntropy p b ≤ Real.log B := by
  have hs' : SupportedBy p (fun a => b a / B) :=
    fun a ha => div_ne_zero (hs a ha) hB.ne'
  have hnonneg := relativeEntropy_nonneg p (fun a => b a / B) hp
    (normalize_isProbability b hb hB hmass) hs'
  rw [relativeEntropy_normalize_right p b hp hs hB] at hnonneg
  linarith

theorem posterior_weighted_log_inverse_le (p b «c» : α → ℝ) (hp : IsProbability p)
    (hb : ∀ a, 0 ≤ b a) {z B : ℝ} (hz : 0 < z) (hB : 0 < B)
    (hmass : ∑ a, b a = B) (hpost : ∀ a, p a = b a * «c» a / z) :
    (∑ a, p a * Real.log (1 / «c» a)) ≤ Real.log (B / z) := by
  have hs : SupportedBy p b := by
    intro a ha hba
    apply ha
    rw [hpost, hba, zero_mul, zero_div]
  have hpoint : ∀ a, p a * Real.log (1 / «c» a) =
      p a * Real.log (1 / z) - p a * Real.log (p a / b a) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    have hbne := hs a hpa
    have hcne : «c» a ≠ 0 := by
      intro hca
      apply hpa
      rw [hpost, hca, mul_zero, zero_div]
    have hratio : p a / b a = «c» a / z := by
      rw [hpost]
      field_simp [hbne, hz.ne']
    rw [hratio, Real.log_div hcne hz.ne', Real.log_div one_ne_zero hcne,
      Real.log_div one_ne_zero hz.ne', Real.log_one]
    ring
  have hid : (∑ a, p a * Real.log (1 / «c» a)) =
      Real.log (1 / z) - relativeEntropy p b := by
    simp only [hpoint, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul,
      relativeEntropy]
  have hkl := neg_relativeEntropy_le_log_mass p b hp hb hs hB hmass
  rw [hid, Real.log_div hB.ne' hz.ne', Real.log_div one_ne_zero hz.ne', Real.log_one]
  linarith

end UniqueGames.Foundations.Information

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Information_Pinsker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                        
section

namespace UniqueGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

noncomputable def hellingerSquared (p q : α → ℝ) : ℝ :=
  ∑ a, (Real.sqrt (p a) - Real.sqrt (q a)) ^ 2

theorem sqrt_distance_le_relativeEntropy_term {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : x ≠ 0 → y ≠ 0) :
    (Real.sqrt x - Real.sqrt y)^2 ≤ x * Real.log (x / y) - x + y := by
  by_cases hxzero : x = 0
  · subst x
    simp [Real.sq_sqrt hy]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm (hs hxzero))
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsy hsx)
  have hlogid : Real.log (Real.sqrt y / Real.sqrt x) =
      -(Real.log (x / y)) / 2 := by
    rw [Real.log_div hsy.ne' hsx.ne', Real.log_sqrt hy, Real.log_sqrt hx,
      Real.log_div hxzero (hs hxzero)]
    ring
  have hprod : x * (Real.sqrt y / Real.sqrt x) = Real.sqrt x * Real.sqrt y := by
    calc
      x * (Real.sqrt y / Real.sqrt x) = (Real.sqrt x)^2 * (Real.sqrt y / Real.sqrt x) := by
        rw [Real.sq_sqrt hx]
      _ = Real.sqrt x * Real.sqrt y := by field_simp [hsx.ne']
  have hm := mul_le_mul_of_nonneg_left hlog hx
  rw [hlogid, mul_sub, mul_one, hprod] at hm
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

theorem hellingerSquared_le_relativeEntropy (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) :
    hellingerSquared p q ≤ relativeEntropy p q := by
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) =>
    sqrt_distance_le_relativeEntropy_term (hp.1 a) (hq.1 a) (hs a))
  simpa only [hellingerSquared, relativeEntropy, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hp.2, hq.2, sub_add_cancel] using hsum

theorem totalVariation_sq_le_hellingerSquared (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) : totalVariation p q ^ 2 ≤ hellingerSquared p q := by
  have hfactor : ∀ a, |Real.sqrt (p a) - Real.sqrt (q a)| *
      (Real.sqrt (p a) + Real.sqrt (q a)) = |p a - q a| := by
    intro a
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
      ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (hp.1 a), Real.sq_sqrt (hq.1 a)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => |Real.sqrt (p a) - Real.sqrt (q a)|)
    (fun a => Real.sqrt (p a) + Real.sqrt (q a))
  simp only [hfactor, sq_abs] at hcs
  have hpoint : ∀ a, (Real.sqrt (p a) + Real.sqrt (q a)) ^ 2 ≤ 2 * (p a + q a) := by
    intro a
    nlinarith [sq_nonneg (Real.sqrt (p a) - Real.sqrt (q a)),
      Real.sq_sqrt (hp.1 a), Real.sq_sqrt (hq.1 a)]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, hp.2, hq.2] at hsum
  have hnonneg : 0 ≤ ∑ a, (Real.sqrt (p a) - Real.sqrt (q a)) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hsum hnonneg
  dsimp [totalVariation, hellingerSquared]
  nlinarith

theorem totalVariation_sq_le_relativeEntropy (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) :
    totalVariation p q ^ 2 ≤ relativeEntropy p q :=
  (totalVariation_sq_le_hellingerSquared p q hp hq).trans
    (hellingerSquared_le_relativeEntropy p q hp hq hs)

end UniqueGames.Foundations.Information

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Information_Tensorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                              
section

namespace UniqueGames.Foundations.Information

open scoped BigOperators

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

noncomputable def coordinateMarginal (p : (ι → α) → ℝ) (i : ι) (a : α) : ℝ := by
  classical
  exact ∑ x, if x i = a then p x else 0

noncomputable def independentProduct (q : ι → α → ℝ) (x : ι → α) : ℝ := ∏ i, q i (x i)

theorem coordinateMarginal_isProbability (p : (ι → α) → ℝ) (hp : IsProbability p) (i : ι) :
    IsProbability (coordinateMarginal p i) := by
  classical
  constructor
  · intro a
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact hp.1 x
    · exact le_rfl
  · simp only [coordinateMarginal]
    rw [Finset.sum_comm]
    simpa using hp.2

theorem point_le_coordinateMarginal (p : (ι → α) → ℝ) (hp : IsProbability p)
    (i : ι) (x : ι → α) : p x ≤ coordinateMarginal p i (x i) := by
  classical
  have h := Finset.single_le_sum
    (f := fun y : ι → α => if y i = x i then p y else 0)
    (fun y _ => by split_ifs; exact hp.1 y; exact le_rfl) (Finset.mem_univ x)
  simpa [coordinateMarginal] using h

theorem marginal_expectation (p : (ι → α) → ℝ) (i : ι) (f : α → ℝ) :
    (∑ x, p x * f (x i)) = ∑ a, coordinateMarginal p i a * f a := by
  classical
  simp only [coordinateMarginal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

theorem independentProduct_isProbability (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) :
    IsProbability (independentProduct q) := by
  classical
  constructor
  · intro x
    exact Finset.prod_nonneg (fun i _ => (hq i).1 (x i))
  · simp only [independentProduct, ← Fintype.prod_sum, (hq _).2, Finset.prod_const_one]

theorem joint_supportedBy_product_coordinateMarginals (p : (ι → α) → ℝ)
    (hp : IsProbability p) : SupportedBy p (independentProduct (coordinateMarginal p)) := by
  intro x hx
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ne_of_gt ((lt_of_le_of_ne (hp.1 x) (Ne.symm hx)).trans_le
    (point_le_coordinateMarginal p hp i x))

theorem relativeEntropy_independent_reference (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (_hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    relativeEntropy p (independentProduct q) =
      relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, relativeEntropy (coordinateMarginal p i) (q i) := by
  classical
  have hpoint : ∀ x : ι → α, p x * Real.log (p x / independentProduct q x) =
      p x * Real.log (p x / independentProduct (coordinateMarginal p) x) +
        ∑ i, p x * Real.log (coordinateMarginal p i (x i) / q i (x i)) := by
    intro x
    by_cases hx : p x = 0
    · simp [hx]
    have hm : ∀ i, coordinateMarginal p i (x i) ≠ 0 := by
      intro i
      exact ne_of_gt ((lt_of_le_of_ne (hp.1 x) (Ne.symm hx)).trans_le
        (point_le_coordinateMarginal p hp i x))
    have hqne : ∀ i, q i (x i) ≠ 0 := fun i => hs i (x i) (hm i)
    have hmp : (∏ i, coordinateMarginal p i (x i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hm i)
    have hqp : (∏ i, q i (x i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hqne i)
    simp only [independentProduct, Real.log_div hx hmp, Real.log_div hx hqp,
      Real.log_prod (fun i _ => hm i), Real.log_prod (fun i _ => hqne i)]
    simp_rw [Real.log_div (hm _) (hqne _)]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  calc
    relativeEntropy p (independentProduct q) =
        ∑ x, (p x * Real.log (p x / independentProduct (coordinateMarginal p) x) +
          ∑ i, p x * Real.log (coordinateMarginal p i (x i) / q i (x i))) := by
      exact Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, ∑ x, p x * Real.log (coordinateMarginal p i (x i) / q i (x i)) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      rfl
    _ = relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, relativeEntropy (coordinateMarginal p i) (q i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact marginal_expectation p i (fun a => Real.log (coordinateMarginal p i a / q i a))

theorem coordinate_relativeEntropy_sum_le (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    (∑ i, relativeEntropy (coordinateMarginal p i) (q i)) ≤
      relativeEntropy p (independentProduct q) := by
  rw [relativeEntropy_independent_reference p q hp hq hs]
  exact le_add_of_nonneg_left (relativeEntropy_nonneg _ _ hp
    (independentProduct_isProbability _ (coordinateMarginal_isProbability p hp))
    (joint_supportedBy_product_coordinateMarginals p hp))

theorem coordinate_totalVariation_sq_sum_le (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    (∑ i, totalVariation (coordinateMarginal p i) (q i) ^ 2) ≤
      relativeEntropy p (independentProduct q) := by
  exact (Finset.sum_le_sum (fun i _ => totalVariation_sq_le_relativeEntropy _ _
    (coordinateMarginal_isProbability p hp i) (hq i) (hs i))).trans
      (coordinate_relativeEntropy_sum_le p q hp hq hs)

theorem posterior_coordinate_supportedBy (q : ι → α → ℝ) (w : (ι → α) → ℝ)
    (z : ℝ) (i : ι) :
    SupportedBy (coordinateMarginal (posterior (independentProduct q) w z) i) (q i) := by
  classical
  intro a ha hqa
  apply ha
  unfold coordinateMarginal
  apply Finset.sum_eq_zero
  intro x _
  by_cases hxa : x i = a
  · have hzprod : independentProduct q x = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa only [hxa] using hqa)
    simp [hxa, posterior, hzprod]
  · simp [hxa]

theorem posterior_coordinate_totalVariation_sq_sum_le_log
    (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) (w : (ι → α) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw_one : ∀ x, w x ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ x, independentProduct q x * w x = z) :
    (∑ i, totalVariation
      (coordinateMarginal (posterior (independentProduct q) w z) i) (q i) ^ 2) ≤
        Real.log (1 / z) := by
  have hp := independentProduct_isProbability q hq
  exact (coordinate_totalVariation_sq_sum_le _ q
    (posterior_isProbability _ w hp hw hz hmass) hq
    (posterior_coordinate_supportedBy q w z)).trans
      (posterior_relativeEntropy_le _ w hp hw hw_one hz hmass)

end UniqueGames.Foundations.Information

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Information_SideInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.Information
open scoped BigOperators

noncomputable def posteriorOrOriginal
    {A : Type*} [Fintype A] (p e : A → ℝ) (z : ℝ) : A → ℝ := by
  classical
  exact if 0 < z then posterior p e z else p

end UniqueGames.Foundations.Information
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Composition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                            
section

namespace VertexCover.Machine
open Turing
open Turing.TM2
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace Compose

variable (A B : FinTM2)

abbrev K := A.K ⊕ (B.K ⊕ Unit)
abbrev Γ : K A B → Type
  | .inl k => A.Γ k
  | .inr (.inl k) => B.Γ k
  | .inr (.inr _) => Bool
abbrev Λ := A.Λ ⊕ (B.Λ ⊕ Bool)
abbrev State := A.σ × B.σ × Option Bool

instance instFintypeState : Fintype (State A B) := inferInstanceAs (Fintype (A.σ × B.σ × Option Bool))

abbrev Cfg := Turing.TM2.Cfg (Γ A B) (Λ A B) (State A B)
abbrev Stmt := Turing.TM2.Stmt (Γ A B) (Λ A B) (State A B)

abbrev first (k : A.K) : K A B := .inl k
abbrev second (k : B.K) : K A B := .inr (.inl k)
abbrev temporary : K A B := .inr (.inr ())
abbrev transfer (b : Bool) : Λ A B := .inr (.inr b)

def firstStatement : A.Stmt → Stmt A B
  | .push k f p => .push (first A B k) (fun s => f s.1) (firstStatement p)
  | .peek k f p => .peek (first A B k) (fun s x => (f s.1 x, s.2)) (firstStatement p)
  | .pop k f p => .pop (first A B k) (fun s x => (f s.1 x, s.2)) (firstStatement p)
  | .load f p => .load (fun s => (f s.1, s.2)) (firstStatement p)
  | .branch f p q => .branch (fun s => f s.1) (firstStatement p) (firstStatement q)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => transfer A B false)

def secondStatement : B.Stmt → Stmt A B
  | .push k f p => .push (second A B k) (fun s => f s.2.1) (secondStatement p)
  | .peek k f p => .peek (second A B k)
      (fun s x => (s.1, f s.2.1 x, s.2.2)) (secondStatement p)
  | .pop k f p => .pop (second A B k)
      (fun s x => (s.1, f s.2.1 x, s.2.2)) (secondStatement p)
  | .load f p => .load (fun s => (s.1, f s.2.1, s.2.2)) (secondStatement p)
  | .branch f p q => .branch (fun s => f s.2.1) (secondStatement p) (secondStatement q)
  | .goto f => .goto (fun s => .inr (.inl (f s.2.1)))
  | .halt => .halt

variable (outA : A.Γ A.k₁ ≃ Bool) (inB : B.Γ B.k₀ ≃ Bool)

def program : Λ A B → Stmt A B
  | .inl l => firstStatement A B (A.m l)
  | .inr (.inl l) => secondStatement A B (B.m l)
  | .inr (.inr false) =>
      .pop (first A B A.k₁) (fun s x => (s.1, s.2.1, x.map outA))
        (.branch (fun s => s.2.2.isSome)
          (.push (temporary A B) (fun s => s.2.2.getD false)
            (.goto (fun _ => transfer A B false)))
          (.goto (fun _ => transfer A B true)))
  | .inr (.inr true) =>
      .pop (temporary A B) (fun s x => (s.1, s.2.1, x))
        (.branch (fun s => s.2.2.isSome)
          (.push (second A B B.k₀) (fun s => inB.symm (s.2.2.getD false))
            (.goto (fun _ => transfer A B true)))
          (.goto (fun _ => .inr (.inl B.main))))

abbrev machine : FinTM2 where
  K := K A B
  k₀ := first A B A.k₀
  k₁ := second A B B.k₁
  Γ := Γ A B
  Λ := Λ A B
  main := .inl A.main
  σ := State A B
  initialState := (A.initialState, B.initialState, none)
  m := program A B outA inB
  Γk₀Fin := A.Γk₀Fin

def tapes (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k)) (temp : List Bool) :
    ∀ k, List (Γ A B k)
  | .inl k => ta k
  | .inr (.inl k) => tb k
  | .inr (.inr _) => temp

@[simp] theorem tapes_first (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k))
    (t : List Bool) (k : A.K) : tapes A B ta tb t (first A B k) = ta k := rfl
@[simp] theorem tapes_second (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k))
    (t : List Bool) (k : B.K) : tapes A B ta tb t (second A B k) = tb k := rfl
@[simp] theorem tapes_temporary (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k))
    (t : List Bool) : tapes A B ta tb t (temporary A B) = t := rfl

theorem tapes_update_first (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k))
    (t : List Bool) (k : A.K) (v : List (A.Γ k)) :
    tapes A B (Function.update ta k v) tb t =
      Function.update (tapes A B ta tb t) (first A B k) v := by
  funext j
  rcases j with j | (j | j)
  · by_cases h : j = k
    · subst j; simp [tapes, first]
    · simp [tapes, first, Function.update, h]
  · simp [tapes, first, Function.update]
  · simp [tapes, first, Function.update]

theorem tapes_update_second (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k))
    (t : List Bool) (k : B.K) (v : List (B.Γ k)) :
    tapes A B ta (Function.update tb k v) t =
      Function.update (tapes A B ta tb t) (second A B k) v := by
  funext j
  rcases j with j | (j | j)
  · simp [tapes, second, Function.update]
  · by_cases h : j = k
    · subst j; simp [tapes, second]
    · simp [tapes, second, Function.update, h]
  · simp [tapes, second, Function.update]

theorem tapes_update_temporary (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k))
    (t v : List Bool) :
    tapes A B ta tb v = Function.update (tapes A B ta tb t) (temporary A B) v := by
  funext j
  rcases j with j | (j | j)
  · simp [tapes, temporary, Function.update]
  · simp [tapes, temporary, Function.update]
  · cases j; simp [tapes, temporary]

def firstCfg (state : B.σ) (flag : Option Bool)
    (tb : ∀ k, List (B.Γ k)) (temp : List Bool) (c : A.Cfg) : Cfg A B where
  l := some (c.l.elim (transfer A B false) Sum.inl)
  var := (c.var, state, flag)
  stk := tapes A B c.stk tb temp

def secondCfg (state : A.σ) (flag : Option Bool)
    (ta : ∀ k, List (A.Γ k)) (temp : List Bool) (c : B.Cfg) : Cfg A B where
  l := c.l.map (fun l => .inr (.inl l))
  var := (state, c.var, flag)
  stk := tapes A B ta c.stk temp

theorem first_stepAux (b : B.σ) (flag : Option Bool)
    (tb : ∀ k, List (B.Γ k)) (temp : List Bool)
    (q : A.Stmt) (s : A.σ) (ta : ∀ k, List (A.Γ k)) :
    stepAux (firstStatement A B q) (s, b, flag) (tapes A B ta tb temp) =
      firstCfg A B b flag tb temp (stepAux q s ta) := by
  induction q generalizing s ta with
  | push k f p ih =>
    simp only [firstStatement, stepAux, tapes_first]
    rw [← tapes_update_first]
    exact ih s _
  | peek k f p ih =>
    simpa only [firstStatement, stepAux, tapes_first] using ih (f s (ta k).head?) ta
  | pop k f p ih =>
    simp only [firstStatement, stepAux, tapes_first]
    rw [← tapes_update_first]
    exact ih (f s (ta k).head?) _
  | load f p ih => simpa only [firstStatement, stepAux] using ih (f s) ta
  | branch f p q ihp ihq =>
    cases h : f s with
    | false => simpa only [firstStatement, stepAux, h, Bool.cond_false] using ihq s ta
    | true => simpa only [firstStatement, stepAux, h, Bool.cond_true] using ihp s ta
  | goto f => rfl
  | halt => rfl

theorem second_stepAux (a : A.σ) (flag : Option Bool)
    (ta : ∀ k, List (A.Γ k)) (temp : List Bool)
    (q : B.Stmt) (s : B.σ) (tb : ∀ k, List (B.Γ k)) :
    stepAux (secondStatement A B q) (a, s, flag) (tapes A B ta tb temp) =
      secondCfg A B a flag ta temp (stepAux q s tb) := by
  induction q generalizing s tb with
  | push k f p ih =>
    simp only [secondStatement, stepAux, tapes_second]
    rw [← tapes_update_second]
    exact ih s _
  | peek k f p ih =>
    simpa only [secondStatement, stepAux, tapes_second] using ih (f s (tb k).head?) tb
  | pop k f p ih =>
    simp only [secondStatement, stepAux, tapes_second]
    rw [← tapes_update_second]
    exact ih (f s (tb k).head?) _
  | load f p ih => simpa only [secondStatement, stepAux] using ih (f s) tb
  | branch f p q ihp ihq =>
    cases h : f s with
    | false => simpa only [secondStatement, stepAux, h, Bool.cond_false] using ihq s tb
    | true => simpa only [secondStatement, stepAux, h, Bool.cond_true] using ihp s tb
  | goto f => rfl
  | halt => rfl

theorem first_step (b : B.σ) (flag : Option Bool)
    (tb : ∀ k, List (B.Γ k)) (temp : List Bool) (c c' : A.Cfg)
    (h : A.step c = some c') :
    (machine A B outA inB).step (firstCfg A B b flag tb temp c) =
      some (firstCfg A B b flag tb temp c') := by
  rcases c with ⟨l,s,ta⟩
  cases l with
  | none => simp [FinTM2.step, step] at h
  | some l =>
    have hc : stepAux (A.m l) s ta = c' := Option.some.inj h
    rw [← hc]
    change some (stepAux (firstStatement A B (A.m l)) (s,b,flag) (tapes A B ta tb temp)) = _
    exact congrArg some (first_stepAux A B b flag tb temp (A.m l) s ta)

theorem second_step (a : A.σ) (flag : Option Bool)
    (ta : ∀ k, List (A.Γ k)) (temp : List Bool) (c c' : B.Cfg)
    (h : B.step c = some c') :
    (machine A B outA inB).step (secondCfg A B a flag ta temp c) =
      some (secondCfg A B a flag ta temp c') := by
  rcases c with ⟨l,s,tb⟩
  cases l with
  | none => simp [FinTM2.step, step] at h
  | some l =>
    have hc : stepAux (B.m l) s tb = c' := Option.some.inj h
    rw [← hc]
    change some (stepAux (secondStatement A B (B.m l)) (a,s,flag) (tapes A B ta tb temp)) = _
    exact congrArg some (second_stepAux A B a flag ta temp (B.m l) s tb)

def tapeOnly {K : Type} {Γ : K → Type} [DecidableEq K] (k : K) (s : List (Γ k)) :
    ∀ j, List (Γ j) := Function.update (fun _ => []) k s

@[simp] theorem tapeOnly_self {K : Type} {Γ : K → Type} [DecidableEq K]
    (k : K) (s : List (Γ k)) : tapeOnly k s k = s := Function.update_self _ _ _

@[simp] theorem tapeOnly_nil {K : Type} {Γ : K → Type} [DecidableEq K]
    (k : K) : tapeOnly (Γ := Γ) k [] = fun _ => [] := Function.update_eq_self _ _

@[simp] theorem tapeOnly_update {K : Type} {Γ : K → Type} [DecidableEq K]
    (k : K) (s t : List (Γ k)) : Function.update (tapeOnly k s) k t = tapeOnly k t :=
  Function.update_idem _ _ _

def bridgeOne (s : List (A.Γ A.k₁)) (temp : List Bool) (flag : Option Bool) : Cfg A B where
  l := some (transfer A B false)
  var := (A.initialState, B.initialState, flag)
  stk := tapes A B (tapeOnly A.k₁ s) (fun _ => []) temp

def bridgeTwo (temp : List Bool) (s : List (B.Γ B.k₀)) (flag : Option Bool) : Cfg A B where
  l := some (transfer A B true)
  var := (A.initialState, B.initialState, flag)
  stk := tapes A B (fun _ => []) (tapeOnly B.k₀ s) temp

theorem bridgeOne_cons (x : A.Γ A.k₁) (xs : List (A.Γ A.k₁)) (temp : List Bool)
    (flag : Option Bool) :
    (machine A B outA inB).step (bridgeOne A B (x::xs) temp flag) =
      some (bridgeOne A B xs (outA x::temp) (some (outA x))) := by
  change step (program A B outA inB) _ = _
  simp only [bridgeOne, step, program, stepAux, tapes_first,
    tapeOnly_self, List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some,
    Bool.cond_true, Option.getD_some]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapes_temporary]
  rw [← tapes_update_temporary]

theorem bridgeOne_nil (temp : List Bool) (flag : Option Bool) :
    (machine A B outA inB).step (bridgeOne A B [] temp flag) =
      some (bridgeTwo A B temp [] none) := by
  change step (program A B outA inB) _ = _
  simp only [bridgeOne, step, program, stepAux, tapes_first,
    tapeOnly_self, List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none,
    Bool.cond_false]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapeOnly_nil, bridgeTwo]

theorem bridgeTwo_cons (x : Bool) (xs : List Bool) (s : List (B.Γ B.k₀))
    (flag : Option Bool) :
    (machine A B outA inB).step (bridgeTwo A B (x::xs) s flag) =
      some (bridgeTwo A B xs (inB.symm x::s) (some x)) := by
  change step (program A B outA inB) _ = _
  simp only [bridgeTwo, step, program, stepAux, tapes_temporary,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [← tapes_update_temporary]
  simp only [tapes_second, tapeOnly_self]
  rw [← tapes_update_second, tapeOnly_update]

theorem init_tapes (M : FinTM2) (s : List (M.Γ M.k₀)) :
    (initList M s).stk = tapeOnly M.k₀ s := by
  funext k
  by_cases h : k = M.k₀
  · subst k; simp [initList, tapeOnly]
  · simp [initList, tapeOnly, Function.update, h]

theorem halt_tapes (M : FinTM2) (s : List (M.Γ M.k₁)) :
    (haltList M s).stk = tapeOnly M.k₁ s := by
  funext k
  by_cases h : k = M.k₁
  · subst k; simp [haltList, tapeOnly]
  · simp [haltList, tapeOnly, Function.update, h]

theorem bridgeTwo_nil (s : List (B.Γ B.k₀)) (flag : Option Bool) :
    (machine A B outA inB).step (bridgeTwo A B [] s flag) =
      some (secondCfg A B A.initialState none (fun _ => []) [] (Turing.initList B s)) := by
  change step (program A B outA inB) _ = _
  simp only [bridgeTwo, step, program, stepAux, tapes_temporary,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [← tapes_update_temporary]
  simp only [secondCfg, init_tapes]
  rfl

def oneStep {S : Type} (step : S → Option S) (a b : S) (h : step a = some b) :
    StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := h
  steps_le_m := le_rfl

def bridgeOne_run (s : List (A.Γ A.k₁)) (temp : List Bool) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A B) (machine A B outA inB).step
      (bridgeOne A B s temp flag)
      (some (bridgeTwo A B ((s.map outA).reverse ++ temp) [] none)) (s.length + 1) := by
  induction s generalizing temp flag with
  | nil =>
    exact oneStep _ _ _ (bridgeOne_nil A B outA inB temp flag)
  | cons x xs ih =>
    have e₁ := oneStep _ _ _ (bridgeOne_cons A B outA inB x xs temp flag)
    have e₂ := ih (outA x :: temp) (some (outA x))
    have both := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using both

def bridgeTwo_run (temp : List Bool) (s : List (B.Γ B.k₀)) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A B) (machine A B outA inB).step
      (bridgeTwo A B temp s flag)
      (some (secondCfg A B A.initialState none (fun _ => []) []
        (Turing.initList B ((temp.map inB.symm).reverse ++ s)))) (temp.length + 1) := by
  induction temp generalizing s flag with
  | nil => exact oneStep _ _ _ (bridgeTwo_nil A B outA inB s flag)
  | cons x xs ih =>
    have e₁ := oneStep _ _ _ (bridgeTwo_cons A B outA inB x xs s flag)
    have e₂ := ih (inB.symm x :: s) (some x)
    have both := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using both

theorem cfg_ext {c c' : Cfg A B} (hl : c.l = c'.l)
    (hs : c.var = c'.var) (ht : c.stk = c'.stk) : c = c' := by
  rcases c with ⟨l,s,t⟩
  rcases c' with ⟨l',s',t'⟩
  cases hl; cases hs; cases ht
  rfl

theorem first_initial (s : List (A.Γ A.k₀)) :
    firstCfg A B B.initialState none (fun _ => []) [] (Turing.initList A s) =
      Turing.initList (machine A B outA inB) s := by
  apply cfg_ext A B
  · rfl
  · rfl
  · rw [init_tapes]
    change tapes A B (initList A s).stk (fun _ => []) [] = _
    rw [init_tapes]
    funext k
    rcases k with k | (k | k)
    · by_cases h : k = A.k₀
      · subst k; simp [machine, tapes, tapeOnly, first]
      · simp [machine, tapes, tapeOnly, first, Function.update, h]
    · simp [machine, tapes, tapeOnly, first, Function.update]
    · simp [machine, tapes, tapeOnly, first, Function.update]

theorem first_halted (s : List (A.Γ A.k₁)) :
    firstCfg A B B.initialState none (fun _ => []) [] (Turing.haltList A s) =
      bridgeOne A B s [] none := by
  simp only [firstCfg, halt_tapes, bridgeOne]
  rfl

theorem second_halted (s : List (B.Γ B.k₁)) :
    secondCfg A B A.initialState none (fun _ => []) [] (Turing.haltList B s) =
      Turing.haltList (machine A B outA inB) s := by
  apply cfg_ext A B
  · rfl
  · rfl
  · rw [halt_tapes]
    change tapes A B (fun _ => []) (haltList B s).stk [] = _
    rw [halt_tapes]
    funext k
    rcases k with k | (k | k)
    · simp [machine, tapes, tapeOnly, second, Function.update]
    · by_cases h : k = B.k₁
      · subst k; simp [machine, tapes, tapeOnly, second]
      · simp [machine, tapes, tapeOnly, second, Function.update, h]
    · simp [machine, tapes, tapeOnly, second, Function.update]

theorem finiteAlphabet (hA : ∀ k, Finite (A.Γ k)) (hB : ∀ k, Finite (B.Γ k)) :
    ∀ k, Finite ((machine A B outA inB).Γ k) := by
  rintro (k | (k | k))
  · exact hA k
  · exact hB k
  · exact inferInstanceAs (Finite Bool)

end Compose

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Pair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                         
section

namespace VertexCover.Machine
open Turing Turing.TM2
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: frame bs

def pairBits (a b : List Bool) : List Bool := frame a ++ b

theorem frame_length (a : List Bool) : (frame a).length = 2 * a.length + 1 := by
  induction a with
  | nil => rfl
  | cons b bs ih => simp [frame, ih]; omega

namespace Pair
open Compose (K Γ State tapes first second temporary tapes_first tapes_second
  tapes_temporary tapes_update_first tapes_update_second tapes_update_temporary
  tapeOnly init_tapes halt_tapes tapeOnly_self tapeOnly_nil tapeOnly_update)
variable (A B : FinTM2)
abbrev Λ := A.Λ ⊕ (B.Λ ⊕ Fin 4)
abbrev phase (i : Fin 4) : Λ A B := .inr (.inr i)
abbrev Cfg := Turing.TM2.Cfg (Γ A B) (Λ A B) (State A B)
abbrev Stmt := Turing.TM2.Stmt (Γ A B) (Λ A B) (State A B)
def firstStatement : A.Stmt → Stmt A B
  | .push k f p => .push (first A B k) (fun s => f s.1) (firstStatement p)
  | .peek k f p => .peek (first A B k) (fun s x => (f s.1 x, s.2)) (firstStatement p)
  | .pop k f p => .pop (first A B k) (fun s x => (f s.1 x, s.2)) (firstStatement p)
  | .load f p => .load (fun s => (f s.1, s.2)) (firstStatement p)
  | .branch f p q => .branch (fun s => f s.1) (firstStatement p) (firstStatement q)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => .inr (.inl B.main))

def secondStatement : B.Stmt → Stmt A B
  | .push k f p => .push (second A B k) (fun s => f s.2.1) (secondStatement p)
  | .peek k f p => .peek (second A B k)
      (fun s x => (s.1, f s.2.1 x, s.2.2)) (secondStatement p)
  | .pop k f p => .pop (second A B k)
      (fun s x => (s.1, f s.2.1 x, s.2.2)) (secondStatement p)
  | .load f p => .load (fun s => (s.1, f s.2.1, s.2.2)) (secondStatement p)
  | .branch f p q => .branch (fun s => f s.2.1) (secondStatement p) (secondStatement q)
  | .goto f => .goto (fun s => .inr (.inl (f s.2.1)))
  | .halt => .goto (fun _ => phase A B 2)

variable (inA : A.Γ A.k₀ ≃ Bool) (inB : B.Γ B.k₀ ≃ Bool)
  (outA : A.Γ A.k₁ ≃ Bool) (outB : B.Γ B.k₁ ≃ Bool)

def program : Λ A B → Stmt A B
  | .inl l => firstStatement A B (A.m l)
  | .inr (.inl l) => secondStatement A B (B.m l)
  | .inr (.inr i) =>
    if i = 0 then
      .pop (first A B A.k₀) (fun s x => (s.1, s.2.1, x.map inA))
        (.branch (fun s => s.2.2.isSome)
          (.push (temporary A B) (fun s => s.2.2.getD false)
            (.goto (fun _ => phase A B 0)))
          (.goto (fun _ => phase A B 1)))
    else if i = 1 then
      .pop (temporary A B) (fun s x => (s.1, s.2.1, x))
        (.branch (fun s => s.2.2.isSome)
          (.push (first A B A.k₀) (fun s => inA.symm (s.2.2.getD false))
            (.push (second A B B.k₀) (fun s => inB.symm (s.2.2.getD false))
              (.goto (fun _ => phase A B 1))))
          (.goto (fun _ => .inl A.main)))
    else if i = 2 then
      .pop (first A B A.k₁) (fun s x => (s.1, s.2.1, x.map outA))
        (.branch (fun s => s.2.2.isSome)
          (.push (temporary A B) (fun s => s.2.2.getD false)
            (.goto (fun _ => phase A B 2)))
          (.push (second A B B.k₁) (fun _ => outB.symm false)
            (.goto (fun _ => phase A B 3))))
    else
      .pop (temporary A B) (fun s x => (s.1, s.2.1, x))
        (.branch (fun s => s.2.2.isSome)
          (.push (second A B B.k₁) (fun s => outB.symm (s.2.2.getD false))
            (.push (second A B B.k₁) (fun _ => outB.symm true)
              (.goto (fun _ => phase A B 3))))
          (.load (fun _ => (A.initialState, B.initialState, none)) .halt))

abbrev machine : FinTM2 where
  K := K A B
  k₀ := first A B A.k₀
  k₁ := second A B B.k₁
  Γ := Γ A B
  Λ := Λ A B
  σ := State A B
  initialState := (A.initialState, B.initialState, none)
  main := phase A B 0
  m := program A B inA inB outA outB
  Γk₀Fin := A.Γk₀Fin

def firstCfg (state : B.σ) (flag : Option Bool)
    (tb : ∀ k, List (B.Γ k)) (temp : List Bool) (c : A.Cfg) : Cfg A B where
  l := some (c.l.elim ((.inr (.inl B.main))) Sum.inl)
  var := (c.var, state, flag)
  stk := tapes A B c.stk tb temp

def secondCfg (state : A.σ) (flag : Option Bool)
    (ta : ∀ k, List (A.Γ k)) (temp : List Bool) (c : B.Cfg) : Cfg A B where
  l := some (c.l.elim (phase A B 2) (fun l => .inr (.inl l)))
  var := (state, c.var, flag)
  stk := tapes A B ta c.stk temp

theorem first_stepAux (b : B.σ) (flag : Option Bool)
    (tb : ∀ k, List (B.Γ k)) (temp : List Bool)
    (q : A.Stmt) (s : A.σ) (ta : ∀ k, List (A.Γ k)) :
    stepAux (firstStatement A B q) (s, b, flag) (tapes A B ta tb temp) =
      firstCfg A B b flag tb temp (stepAux q s ta) := by
  induction q generalizing s ta with
  | push k f p ih =>
    simp only [firstStatement, stepAux, tapes_first]
    rw [← tapes_update_first]
    exact ih s _
  | peek k f p ih =>
    simpa only [firstStatement, stepAux, tapes_first] using ih (f s (ta k).head?) ta
  | pop k f p ih =>
    simp only [firstStatement, stepAux, tapes_first]
    rw [← tapes_update_first]
    exact ih (f s (ta k).head?) _
  | load f p ih => simpa only [firstStatement, stepAux] using ih (f s) ta
  | branch f p q ihp ihq =>
    cases h : f s with
    | false => simpa only [firstStatement, stepAux, h, Bool.cond_false] using ihq s ta
    | true => simpa only [firstStatement, stepAux, h, Bool.cond_true] using ihp s ta
  | goto f => rfl
  | halt => rfl

theorem second_stepAux (a : A.σ) (flag : Option Bool)
    (ta : ∀ k, List (A.Γ k)) (temp : List Bool)
    (q : B.Stmt) (s : B.σ) (tb : ∀ k, List (B.Γ k)) :
    stepAux (secondStatement A B q) (a, s, flag) (tapes A B ta tb temp) =
      secondCfg A B a flag ta temp (stepAux q s tb) := by
  induction q generalizing s tb with
  | push k f p ih =>
    simp only [secondStatement, stepAux, tapes_second]
    rw [← tapes_update_second]
    exact ih s _
  | peek k f p ih =>
    simpa only [secondStatement, stepAux, tapes_second] using ih (f s (tb k).head?) tb
  | pop k f p ih =>
    simp only [secondStatement, stepAux, tapes_second]
    rw [← tapes_update_second]
    exact ih (f s (tb k).head?) _
  | load f p ih => simpa only [secondStatement, stepAux] using ih (f s) tb
  | branch f p q ihp ihq =>
    cases h : f s with
    | false => simpa only [secondStatement, stepAux, h, Bool.cond_false] using ihq s tb
    | true => simpa only [secondStatement, stepAux, h, Bool.cond_true] using ihp s tb
  | goto f => rfl
  | halt => rfl

theorem first_step (b : B.σ) (flag : Option Bool)
    (tb : ∀ k, List (B.Γ k)) (temp : List Bool) (c c' : A.Cfg)
    (h : A.step c = some c') :
    (machine A B inA inB outA outB).step (firstCfg A B b flag tb temp c) =
      some (firstCfg A B b flag tb temp c') := by
  rcases c with ⟨l,s,ta⟩
  cases l with
  | none => simp [FinTM2.step, step] at h
  | some l =>
    have hc : stepAux (A.m l) s ta = c' := Option.some.inj h
    rw [← hc]
    change some (stepAux (firstStatement A B (A.m l)) (s,b,flag) (tapes A B ta tb temp)) = _
    exact congrArg some (first_stepAux A B b flag tb temp (A.m l) s ta)

theorem second_step (a : A.σ) (flag : Option Bool)
    (ta : ∀ k, List (A.Γ k)) (temp : List Bool) (c c' : B.Cfg)
    (h : B.step c = some c') :
    (machine A B inA inB outA outB).step (secondCfg A B a flag ta temp c) =
      some (secondCfg A B a flag ta temp c') := by
  rcases c with ⟨l,s,tb⟩
  cases l with
  | none => simp [FinTM2.step, step] at h
  | some l =>
    have hc : stepAux (B.m l) s tb = c' := Option.some.inj h
    rw [← hc]
    change some (stepAux (secondStatement A B (B.m l)) (a,s,flag) (tapes A B ta tb temp)) = _
    exact congrArg some (second_stepAux A B a flag ta temp (B.m l) s tb)

theorem cfg_ext {c c' : Cfg A B} (hl : c.l = c'.l)
    (hs : c.var = c'.var) (ht : c.stk = c'.stk) : c = c' := by
  rcases c with ⟨l,s,t⟩
  rcases c' with ⟨l',s',t'⟩
  cases hl; cases hs; cases ht
  rfl

def oneStep {S : Type} (step : S → Option S) (a b : S) (h : step a = some b) :
    StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := h
  steps_le_m := le_rfl

def cfg0 (s : List (A.Γ A.k₀)) (temp : List Bool) (flag : Option Bool) : Cfg A B where
  l := some (phase A B 0)
  var := (A.initialState, B.initialState, flag)
  stk := tapes A B (tapeOnly A.k₀ s) (fun _ => []) temp

def cfg1 (s : List (A.Γ A.k₀)) (t : List (B.Γ B.k₀)) (temp : List Bool)
    (flag : Option Bool) : Cfg A B where
  l := some (phase A B 1)
  var := (A.initialState, B.initialState, flag)
  stk := tapes A B (tapeOnly A.k₀ s) (tapeOnly B.k₀ t) temp

def cfg2 (s : List (A.Γ A.k₁)) (t : List (B.Γ B.k₁)) (temp : List Bool)
    (flag : Option Bool) : Cfg A B where
  l := some (phase A B 2)
  var := (A.initialState, B.initialState, flag)
  stk := tapes A B (tapeOnly A.k₁ s) (tapeOnly B.k₁ t) temp

def cfg3 (t : List (B.Γ B.k₁)) (temp : List Bool) (flag : Option Bool) : Cfg A B where
  l := some (phase A B 3)
  var := (A.initialState, B.initialState, flag)
  stk := tapes A B (fun _ => []) (tapeOnly B.k₁ t) temp

theorem cfg0_cons (x : A.Γ A.k₀) (xs : List (A.Γ A.k₀)) (temp : List Bool)
    (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg0 A B (x::xs) temp flag) =
      some (cfg0 A B xs (inA x::temp) (some (inA x))) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg0, step, program, phase, ↓reduceIte, stepAux, tapes_first,
    tapeOnly_self, List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some,
    Bool.cond_true, Option.getD_some]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapes_temporary]
  rw [← tapes_update_temporary]

theorem cfg0_nil (temp : List Bool) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg0 A B [] temp flag) =
      some (cfg1 A B [] [] temp none) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg0, step, program, phase, ↓reduceIte, stepAux, tapes_first,
    tapeOnly_self, List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none,
    Bool.cond_false]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapeOnly_nil, cfg1]

theorem cfg1_cons (x : Bool) (xs : List Bool) (s : List (A.Γ A.k₀))
    (t : List (B.Γ B.k₀)) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg1 A B s t (x::xs) flag) =
      some (cfg1 A B (inA.symm x::s) (inB.symm x::t) xs (some x)) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg1, step, program, phase, Fin.reduceEq, ↓reduceIte, stepAux, tapes_temporary,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [← tapes_update_temporary]
  simp only [tapes_first, tapeOnly_self]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapes_second, tapeOnly_self]
  rw [← tapes_update_second, tapeOnly_update]

theorem cfg1_nil (s : List (A.Γ A.k₀)) (t : List (B.Γ B.k₀)) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg1 A B s t [] flag) =
      some (firstCfg A B B.initialState none (tapeOnly B.k₀ t) [] (initList A s)) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg1, step, program, phase, Fin.reduceEq, ↓reduceIte, stepAux, tapes_temporary,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [← tapes_update_temporary]
  simp only [firstCfg, init_tapes]
  rfl

theorem cfg2_cons (x : A.Γ A.k₁) (xs : List (A.Γ A.k₁)) (t : List (B.Γ B.k₁))
    (temp : List Bool) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg2 A B (x::xs) t temp flag) =
      some (cfg2 A B xs t (outA x::temp) (some (outA x))) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg2, step, program, phase, Fin.reduceEq, ↓reduceIte, stepAux, tapes_first,
    tapeOnly_self, List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some,
    Bool.cond_true, Option.getD_some]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapes_temporary]
  rw [← tapes_update_temporary]

theorem cfg2_nil (t : List (B.Γ B.k₁)) (temp : List Bool) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg2 A B [] t temp flag) =
      some (cfg3 A B (outB.symm false :: t) temp none) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg2, step, program, phase, Fin.reduceEq, ↓reduceIte, stepAux, tapes_first,
    tapeOnly_self, List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none,
    Bool.cond_false]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapeOnly_nil, tapes_second, tapeOnly_self]
  rw [← tapes_update_second, tapeOnly_update]
  rfl

theorem cfg3_cons (x : Bool) (xs : List Bool) (t : List (B.Γ B.k₁)) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg3 A B t (x::xs) flag) =
      some (cfg3 A B (outB.symm true::outB.symm x::t) xs (some x)) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg3, step, program, phase, Fin.reduceEq, ↓reduceIte, stepAux, tapes_temporary,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [← tapes_update_temporary]
  simp only [tapes_second, tapeOnly_self]
  rw [← tapes_update_second, tapeOnly_update]
  simp only [tapes_second, tapeOnly_self]
  rw [← tapes_update_second, tapeOnly_update]

theorem cfg3_nil (t : List (B.Γ B.k₁)) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg3 A B t [] flag) =
      some (haltList (machine A B inA inB outA outB) t) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg3, step, program, phase, Fin.reduceEq, ↓reduceIte, stepAux, tapes_temporary,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [← tapes_update_temporary]
  congr 1
  apply cfg_ext A B
  · rfl
  · rfl
  · rw [halt_tapes]
    funext k
    rcases k with k | (k | k)
    · simp [tapes, tapeOnly, second, Function.update]
    · by_cases h : k = B.k₁
      · subst k; simp [tapes, tapeOnly, second]
      · simp [tapes, tapeOnly, second, Function.update, h]
    · simp [tapes, tapeOnly, second, Function.update]
def cfg0_run (s : List (A.Γ A.k₀)) (temp : List Bool) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg0 A B s temp flag)
      (some (cfg1 A B [] [] ((s.map inA).reverse ++ temp) none)) (s.length+1) := by
  induction s generalizing temp flag with
  | nil => exact oneStep _ _ _ (cfg0_nil A B inA inB outA outB temp flag)
  | cons x xs ih =>
    have e₁ := oneStep _ _ _ (cfg0_cons A B inA inB outA outB x xs temp flag)
    have e₂ := ih (inA x::temp) (some (inA x))
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

def cfg1_run (temp : List Bool) (s : List (A.Γ A.k₀)) (t : List (B.Γ B.k₀))
    (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg1 A B s t temp flag)
      (some (firstCfg A B B.initialState none
        (tapeOnly B.k₀ ((temp.map inB.symm).reverse ++ t)) []
        (initList A ((temp.map inA.symm).reverse ++ s)))) (temp.length+1) := by
  induction temp generalizing s t flag with
  | nil => exact oneStep _ _ _ (cfg1_nil A B inA inB outA outB s t flag)
  | cons x xs ih =>
    have e₁ := oneStep _ _ _ (cfg1_cons A B inA inB outA outB x xs s t flag)
    have e₂ := ih (inA.symm x::s) (inB.symm x::t) (some x)
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

def cfg2_run (s : List (A.Γ A.k₁)) (t : List (B.Γ B.k₁)) (temp : List Bool)
    (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg2 A B s t temp flag)
      (some (cfg3 A B (outB.symm false::t) ((s.map outA).reverse ++ temp) none))
      (s.length+1) := by
  induction s generalizing temp flag with
  | nil => exact oneStep _ _ _ (cfg2_nil A B inA inB outA outB t temp flag)
  | cons x xs ih =>
    have e₁ := oneStep _ _ _ (cfg2_cons A B inA inB outA outB x xs t temp flag)
    have e₂ := ih (outA x::temp) (some (outA x))
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

def cfg3_run (temp : List Bool) (t : List (B.Γ B.k₁)) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg3 A B t temp flag)
      (some (haltList (machine A B inA inB outA outB)
        ((temp.reverse.flatMap (fun b => [outB.symm true, outB.symm b])) ++ t)))
      (temp.length+1) := by
  induction temp generalizing t flag with
  | nil => exact oneStep _ _ _ (cfg3_nil A B inA inB outA outB t flag)
  | cons x xs ih =>
    have e₁ := oneStep _ _ _ (cfg3_cons A B inA inB outA outB x xs t flag)
    have e₂ := ih (outB.symm true::outB.symm x::t) (some x)
    simpa only [List.reverse_cons, List.flatMap_append, List.flatMap_singleton,
      List.append_assoc, List.cons_append, List.nil_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

theorem initial_eq (s : List (A.Γ A.k₀)) :
    cfg0 A B s [] none = initList (machine A B inA inB outA outB) s := by
  apply cfg_ext A B
  · rfl
  · rfl
  · rw [init_tapes]
    funext k
    rcases k with k | (k | k)
    · by_cases h : k = A.k₀
      · subst k; simp [cfg0, tapes, tapeOnly, first]
      · simp [cfg0, tapes, tapeOnly, first, Function.update, h]
    · simp [cfg0, tapes, tapeOnly, first, Function.update]
    · simp [cfg0, tapes, tapeOnly, first, Function.update]

theorem first_halted (s : List (A.Γ A.k₁)) (t : List (B.Γ B.k₀)) :
    firstCfg A B B.initialState none (tapeOnly B.k₀ t) [] (haltList A s) =
      secondCfg A B A.initialState none (tapeOnly A.k₁ s) [] (initList B t) := by
  simp only [firstCfg, secondCfg, init_tapes, halt_tapes]
  rfl

theorem second_halted (s : List (A.Γ A.k₁)) (t : List (B.Γ B.k₁)) :
    secondCfg A B A.initialState none (tapeOnly A.k₁ s) [] (haltList B t) =
      cfg2 A B s t [] none := by
  simp only [secondCfg, halt_tapes, cfg2]
  rfl

theorem frame_eq (s t : List Bool) :
    s.flatMap (fun b => [true,b]) ++ false::t = pairBits s t := by
  induction s with
  | nil => rfl
  | cons x xs ih => simpa only [List.flatMap_cons, List.cons_append, List.nil_append,
        List.append_assoc, pairBits, frame] using congrArg (fun l => true::x::l) ih

theorem finiteAlphabet (hA : ∀ k, Finite (A.Γ k)) (hB : ∀ k, Finite (B.Γ k)) :
    ∀ k, Finite ((machine A B inA inB outA outB).Γ k) := by
  rintro (k | (k | k))
  · exact hA k
  · exact hB k
  · exact inferInstanceAs (Finite Bool)

end Pair

structure Poly {α β : Type} (eα : α → List Bool) (eβ : β → List Bool) (f : α → β) where
  computation : TM2ComputableInPolyTime eα eβ f
  finiteAlphabet : ∀ k, Finite (computation.tm.Γ k)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Primitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                              
section

namespace VertexCover.Machine
open Turing Turing.TM2

namespace Stream
variable {Q : Type} [Fintype Q]
abbrev K := Fin 3
abbrev Γ (_ : K) := Bool
abbrev State (Q : Type) := Q × Option Bool
abbrev Stmt (Q : Type) := Turing.TM2.Stmt Γ Bool (State Q)
abbrev Cfg (Q : Type) := Turing.TM2.Cfg Γ Bool (State Q)

omit [Fintype Q] in
theorem cfg_ext {c d : Cfg Q} (hl : c.l = d.l) (hv : c.var = d.var) (ht : c.stk = d.stk) : c = d := by
  cases c; cases d; cases hl; cases hv; cases ht; rfl

def emit (k : K) : ℕ → (State Q → List Bool) → Stmt Q → Stmt Q
  | 0, _, p => p
  | n+1, f, p => .branch (fun s => (f s).isEmpty) p
    (.push k (fun s => (f s).headD false) (emit k n (fun s => (f s).tail) p))

omit [Fintype Q] in
theorem emit_step (k : K) (n : ℕ) (f : State Q → List Bool) (p : Stmt Q)
    (s : State Q) (t : K → List Bool) (h : (f s).length ≤ n) :
    stepAux (emit k n f p) s t =
      stepAux p s (Function.update t k ((f s).reverse ++ t k)) := by
  induction n generalizing f t with
  | zero =>
    have hf : f s = [] := List.length_eq_zero_iff.mp (by omega)
    simp [emit, hf]
  | succ n ih =>
    cases hf : f s with
    | nil => simp [emit, hf]
    | cons b bs =>
      simp only [emit, stepAux, hf, List.isEmpty_cons, Bool.cond_false, List.headD_cons]
      rw [ih (fun s => (f s).tail) (Function.update t k (b :: t k)) (by simp [hf] at h ⊢; omega)]
      simp only [hf, List.tail_cons, Function.update_self, Function.update_idem,
        List.reverse_cons, List.append_assoc, List.singleton_append]

variable (q₀ : Q) (δ : Q → Bool → Q × List Bool) (finish : Q → List Bool) (W : ℕ)

def program : Bool → Stmt Q
  | false => .pop 0 (fun s b => (s.1,b))
      (.branch (fun s => s.2.isSome)
        (emit 1 W (fun s => (δ s.1 (s.2.getD false)).2)
          (.load (fun s => ((δ s.1 (s.2.getD false)).1,s.2)) (.goto (fun _ => false))))
        (emit 1 W (fun s => finish s.1) (.goto (fun _ => true))))
  | true => .pop 1 (fun s b => (s.1,b))
      (.branch (fun s => s.2.isSome)
        (.push 2 (fun s => s.2.getD false) (.goto (fun _ => true)))
        (.load (fun _ => (q₀,none)) .halt))

abbrev machine : FinTM2 where
  K := K
  Γ := Γ
  k₀ := 0
  k₁ := 2
  Λ := Bool
  σ := State Q
  main := false
  initialState := (q₀,none)
  m := program q₀ δ finish W

def output : Q → List Bool → List Bool
  | q, [] => finish q
  | q, b :: bs => (δ q b).2 ++ output (δ q b).1 bs

def finalState : Q → List Bool → Q
  | q, [] => q
  | q, b :: bs => finalState (δ q b).1 bs

def tapes (a b c : List Bool) : K → List Bool := ![a,b,c]
@[simp] theorem tapes_zero (a b c : List Bool) : tapes a b c 0 = a := rfl
@[simp] theorem tapes_one (a b c : List Bool) : tapes a b c 1 = b := rfl
@[simp] theorem tapes_two (a b c : List Bool) : tapes a b c 2 = c := rfl

theorem update_zero (a b c d : List Bool) : Function.update (tapes a b c) 0 d = tapes d b c := by
  funext k; fin_cases k <;> simp [tapes]
theorem update_one (a b c d : List Bool) : Function.update (tapes a b c) 1 d = tapes a d c := by
  funext k; fin_cases k <;> simp [tapes]
theorem update_two (a b c d : List Bool) : Function.update (tapes a b c) 2 d = tapes a b d := by
  funext k; fin_cases k <;> simp [tapes]

abbrev cfg (phase : Bool) (q : Q) (flag : Option Bool) (a b c : List Bool) : Cfg Q :=
  ⟨some phase,(q,flag),tapes a b c⟩

variable (hδ : ∀ q b, (δ q b).2.length ≤ W) (hf : ∀ q, (finish q).length ≤ W)

include hδ in
theorem scan_cons (q : Q) (flag : Option Bool) (b : Bool) (bs t : List Bool) :
    (machine q₀ δ finish W).step (cfg false q flag (b::bs) t []) =
      some (cfg false (δ q b).1 (some b) bs ((δ q b).2.reverse ++ t) []) := by
  change step (program q₀ δ finish W) _ = _
  simp only [cfg, step, program, stepAux, tapes_zero, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, update_zero]
  rw [emit_step _ _ _ _ _ _ (hδ q b)]
  simp only [Option.getD_some, tapes_one, update_one, stepAux]

include hf in
theorem scan_nil (q : Q) (flag : Option Bool) (t : List Bool) :
    (machine q₀ δ finish W).step (cfg false q flag [] t []) =
      some (cfg true q none [] ((finish q).reverse ++ t) []) := by
  change step (program q₀ δ finish W) _ = _
  simp only [cfg, step, program, stepAux, tapes_zero, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, update_zero]
  rw [emit_step _ _ _ _ _ _ (hf q)]
  simp only [tapes_one, update_one, stepAux]

theorem reverse_cons (q : Q) (flag : Option Bool) (b : Bool) (bs out : List Bool) :
    (machine q₀ δ finish W).step (cfg true q flag [] (b::bs) out) =
      some (cfg true q (some b) [] bs (b::out)) := by
  change step (program q₀ δ finish W) _ = _
  simp only [cfg, step, program, stepAux, tapes_one, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, update_one, Option.getD_some, tapes_two, update_two]

theorem reverse_nil (q : Q) (flag : Option Bool) (out : List Bool) :
    (machine q₀ δ finish W).step (cfg true q flag [] [] out) =
      some (haltList (machine q₀ δ finish W) out) := by
  change step (program q₀ δ finish W) _ = _
  simp only [step, program, stepAux, tapes_one, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, update_one]
  congr 1
  apply cfg_ext <;> try rfl
  funext k; fin_cases k <;> simp [haltList, tapes, machine]

def scan_run (q : Q) (flag : Option Bool) (input t : List Bool) :
    @StateTransition.EvalsToInTime (Cfg Q) (machine q₀ δ finish W).step
      (cfg false q flag input t [])
      (some (cfg true (finalState δ q input) none []
        ((output δ finish q input).reverse ++ t) [])) (input.length+1) := by
  induction input generalizing q flag t with
  | nil => exact Pair.oneStep _ _ _ (scan_nil q₀ δ finish W hf q flag t)
  | cons b bs ih =>
    have s := Pair.oneStep _ _ _ (scan_cons q₀ δ finish W hδ q flag b bs t)
    have u := ih (δ q b).1 (some b) ((δ q b).2.reverse++t)
    have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ s u
    simpa only [output, finalState, List.reverse_append, List.append_assoc,
      List.length_cons, Nat.add_comm 1 (bs.length+1)] using all

def reverse_run (q : Q) (flag : Option Bool) (t out : List Bool) :
    @StateTransition.EvalsToInTime (Cfg Q) (machine q₀ δ finish W).step
      (cfg true q flag [] t out)
      (some (haltList (machine q₀ δ finish W) (t.reverse++out))) (t.length+1) := by
  induction t generalizing flag out with
  | nil => exact Pair.oneStep _ _ _ (reverse_nil q₀ δ finish W q flag out)
  | cons b bs ih =>
    have s := Pair.oneStep _ _ _ (reverse_cons q₀ δ finish W q flag b bs out)
    have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ s (ih (some b) (b::out))
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, Nat.add_comm 1 (bs.length+1)] using all

theorem initial_eq (input : List Bool) :
    initList (machine q₀ δ finish W) input = cfg false q₀ none input [] [] := by
  apply cfg_ext <;> try rfl
  funext k; fin_cases k <;> simp [initList, tapes, machine]

def execution (input : List Bool) :
    TM2OutputsInTime (machine q₀ δ finish W) input (some (output δ finish q₀ input))
      (input.length + (output δ finish q₀ input).length + 2) := by
  have s := scan_run q₀ δ finish W hδ hf q₀ none input []
  have r := reverse_run q₀ δ finish W (finalState δ q₀ input) none
    (output δ finish q₀ input).reverse []
  simp only [List.append_nil] at s
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at r
  have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ s r
  rw [← initial_eq] at all
  exact { all with steps_le_m := by have h := all.steps_le_m; omega }

omit [Fintype Q] in
include hδ hf in
theorem output_length (q : Q) (input : List Bool) :
    (output δ finish q input).length ≤ W * (input.length + 1) := by
  induction input generalizing q with
  | nil => simpa [output] using hf q
  | cons b bs ih =>
    simp only [output, List.length_append, List.length_cons]
    have h := hδ q b
    have hh := ih (δ q b).1
    calc
      _ ≤ W + W * (bs.length+1) := Nat.add_le_add h hh
      _ = _ := by ring

noncomputable def poly : Poly id id (output δ finish q₀) where
  computation := {
    tm := machine q₀ δ finish W
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.C (W+1) * (Polynomial.X+1) + 1
    outputsFun := fun input => by
      simp only [id_eq, show (Equiv.refl Bool).invFun = id from rfl, List.map_id]
      have run := execution q₀ δ finish W hδ hf input
      refine { run with steps_le_m := ?_ }
      apply run.steps_le_m.trans
      have h := output_length δ finish W hδ hf q₀ input
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one]
      nlinarith }
  finiteAlphabet := fun _ => (inferInstance : Finite Bool)

end Stream
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Primitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                        
section

namespace VertexCover.Machine
open Turing

noncomputable def Poly.realizes {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : List Bool → List Bool} {g : α → β} (c : Poly id id f)
    (h : ∀ a, f (ea a) = eb (g a)) : Poly ea eb g where
  computation := { c.computation with
    outputsFun := fun a => by
      have run := c.computation.outputsFun (ea a)
      simpa only [id_eq, h a] using run }
  finiteAlphabet := c.finiteAlphabet

noncomputable def Poly.congr {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f g : α → β} (c : Poly ea eb f) (h : ∀ a, f a = g a) : Poly ea eb g where
  computation := { c.computation with
    outputsFun := fun a => by
      simpa only [h a] using c.computation.outputsFun a }
  finiteAlphabet := c.finiteAlphabet

noncomputable def Poly.encodeCongr {α β γ δ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {ed : δ → List Bool} {f : α → β} {g : γ → δ}
    (c : Poly ea eb f) (lift : γ → α) (hi : ∀ a, ea (lift a) = ec a)
    (ho : ∀ a, eb (f (lift a)) = ed (g a)) : Poly ec ed g where
  computation := { c.computation with
    outputsFun := fun a => by
      simpa only [hi a, ho a] using c.computation.outputsFun (lift a) }
  finiteAlphabet := c.finiteAlphabet

abbrev prodBits {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (p : α × β) : List Bool :=
  pairBits (ea p.1) (eb p.2)

noncomputable def Poly.identity {α : Type} (ea : α → List Bool) : Poly ea ea id := by
  let δ : Unit → Bool → Unit × List Bool := fun _ b => ((),[b])
  have h (q : Unit) (s : List Bool) : Stream.output δ (fun _ => []) q s = s := by
    induction s generalizing q with
    | nil => rfl
    | cons b bs ih => simp [Stream.output, δ, ih]
  exact (Stream.poly () δ (fun _ => []) 1 (by simp [δ]) (by simp)).realizes
    (fun a => h () (ea a))

noncomputable def Poly.const {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (b : β) : Poly ea eb (fun _ => b) := by
  let δ : Unit → Bool → Unit × List Bool := fun _ _ => ((),[])
  have h (q : Unit) (s : List Bool) : Stream.output δ (fun _ => eb b) q s = eb b := by
    induction s generalizing q with
    | nil => rfl
    | cons x xs ih => simp [Stream.output, δ, ih]
  exact (Stream.poly () δ (fun _ => eb b) (eb b).length (by simp [δ]) (by simp)).realizes
    (fun a => h () (ea a))

namespace Project
                                                                                
def trans (left right : Bool) (q : Fin 3) (b : Bool) : Fin 3 × List Bool :=
  if q = 0 then (if b then 1 else 2, [])
  else if q = 1 then (0, if left then [b] else [])
  else (2, if right then [b] else [])

theorem bound (left right : Bool) (q : Fin 3) (b : Bool) :
    (trans left right q b).2.length ≤ 1 := by
  unfold trans; split <;> try split <;> cases left <;> cases right <;> simp_all

theorem tail (left right : Bool) (s : List Bool) :
    Stream.output (trans left right) (fun _ => []) 2 s = if right then s else [] := by
  induction s with
  | nil => simp [Stream.output]
  | cons b bs ih => cases right <;> simp [Stream.output, trans, ih]

theorem framed (left right : Bool) (a b : List Bool) :
    Stream.output (trans left right) (fun _ => []) 0 (pairBits a b) =
      (if left then a else []) ++ (if right then b else []) := by
  induction a with
  | nil => simpa [pairBits, frame, Stream.output, trans] using tail left right b
  | cons x xs ih =>
    simp only [pairBits, frame, List.cons_append, Stream.output, trans, ↓reduceIte,
      Fin.reduceEq, List.nil_append] at ih ⊢
    cases left <;> simp_all
end Project

noncomputable def Poly.fst {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    Poly (prodBits ea eb) ea Prod.fst :=
  (Stream.poly 0 (Project.trans true false) (fun _ => []) 1
    (Project.bound true false) (by simp)).realizes (fun p => by
      simpa only [Bool.true_eq, ↓reduceIte, Bool.false_eq_true, List.append_nil] using
        Project.framed true false (ea p.1) (eb p.2))

noncomputable def Poly.snd {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    Poly (prodBits ea eb) eb Prod.snd :=
  (Stream.poly 0 (Project.trans false true) (fun _ => []) 1
    (Project.bound false true) (by simp)).realizes (fun p => by
      simpa only [Bool.true_eq, ↓reduceIte, Bool.false_eq_true, List.nil_append] using
        Project.framed false true (ea p.1) (eb p.2))

noncomputable def Poly.append : Poly (prodBits id id) id (fun p : List Bool × List Bool => p.1++p.2) :=
  (Stream.poly 0 (Project.trans true true) (fun _ => []) 1
    (Project.bound true true) (by simp)).realizes (fun p => by
      simpa only [Bool.true_eq, ↓reduceIte, prodBits, id_eq] using Project.framed true true p.1 p.2)

noncomputable def Poly.cons (b : Bool) : Poly id id (List.cons b) := by
  let δ : Bool → Bool → Bool × List Bool := fun first x => (false, if first then [b,x] else [x])
  let last : Bool → List Bool := fun first => if first then [b] else []
  have noPrefix (s : List Bool) : Stream.output δ last false s = s := by
    induction s with
    | nil => rfl
    | cons x xs ih => simp [Stream.output, δ, last, ih]
  have yesPrefix (s : List Bool) : Stream.output δ last true s = b::s := by
    cases s with
    | nil => rfl
    | cons x xs => simp [Stream.output, δ, noPrefix]
  exact (Stream.poly true δ last 2 (by intro q x; cases q <;> simp [δ])
    (by intro q; cases q <;> simp [last])).realizes yesPrefix

abbrev boolBits (b : Bool) : List Bool := [b]

noncomputable def Poly.headD (b : Bool) : Poly id boolBits (fun s => s.headD b) := by
  let δ : Option Bool → Bool → Option Bool × List Bool := fun q x => (q.or (some x),[])
  let last : Option Bool → List Bool := fun q => [q.getD b]
  have h (q : Option Bool) (s : List Bool) :
      Stream.output δ last q s = [(q.or s.head?).getD b] := by
    induction s generalizing q with
    | nil => simp [Stream.output, last]
    | cons x xs ih =>
      simp only [Stream.output, δ, List.nil_append, ih]
      cases q <;> simp
  exact (Stream.poly none δ last 1 (by simp [δ]) (by simp [last])).realizes
    (fun s => by have hh := h none s; cases s <;> simpa [boolBits] using hh)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FiniteMemory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                          
section

namespace VertexCover.Machine

namespace BoundedMemory
abbrev Memory (B : ℕ) := {s : List Bool // s.length ≤ B}

noncomputable instance instFintypeMemory (B : ℕ) : Fintype (Memory B) := by
  let f : (Σ n : Fin (B+1), List.Vector Bool n.val) → Memory B :=
    fun p => ⟨p.2.val, by have h := p.2.property; omega⟩
  have hf : Function.Surjective f := by
    intro ⟨s,hs⟩
    exact ⟨⟨⟨s.length, by omega⟩,⟨s,rfl⟩⟩,rfl⟩
  letI : Finite (Memory B) := Finite.of_surjective f hf
  exact Fintype.ofFinite _

noncomputable def next (B : ℕ) (q : Option (Memory B)) (b : Bool) :
    Option (Memory B) × List Bool :=
  (q.bind (fun p => if h : (p.val++[b]).length ≤ B then some ⟨p.val++[b],h⟩ else none), [])

theorem output (B : ℕ) (last : Option (Memory B) → List Bool) (s xs : List Bool)
    (h : (s++xs).length ≤ B) :
    Stream.output (next B) last (some ⟨s, by simp only [List.length_append] at h; omega⟩) xs =
      last (some ⟨s++xs,h⟩) := by
  induction xs generalizing s with
  | nil => simp only [Stream.output, List.append_nil]
  | cons b bs ih =>
    have hs : (s++[b]).length ≤ B := by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega
    simp only [Stream.output, next, Option.bind_some, dite_eq_left hs, List.nil_append]
    rw [ih (s++[b]) (by simpa only [List.append_assoc, List.singleton_append] using h)]
    simp only [List.append_assoc, List.singleton_append]

end BoundedMemory

noncomputable def Poly.finite {α β : Type} [Fintype α]
    (ea : α → List Bool) (eb : β → List Bool) (hc : Function.Injective ea)
    (f : α → β) : Poly ea eb f := by
  classical
  let B := Finset.univ.sup (fun a : α => (ea a).length)
  let W := Finset.univ.sup (fun a : α => (eb (f a)).length)
  let last : Option (BoundedMemory.Memory B) → List Bool := fun q =>
    match q with
    | none => []
    | some s => if h : ∃ a, ea a = s.val then eb (f h.choose) else []
  have hl : ∀ q, (last q).length ≤ W := by
    intro q
    cases q with
    | none => exact Nat.zero_le _
    | some s =>
      dsimp [last]
      split
      · exact Finset.le_sup (f := fun a : α => (eb (f a)).length) (Finset.mem_univ _)
      · exact Nat.zero_le _
  let c := Stream.poly (some (⟨[],by simp⟩ : BoundedMemory.Memory B))
    (BoundedMemory.next B) last W (by intro q b; simp [BoundedMemory.next]) hl
  apply c.realizes
  intro a
  have ha : (ea a).length ≤ B := Finset.le_sup (f := fun a : α => (ea a).length) (Finset.mem_univ a)
  rw [BoundedMemory.output B last [] (ea a) (by simpa using ha)]
  dsimp [last]
  split
  · rename_i h
    rw [hc h.choose_spec]
  · rename_i h
    exact False.elim (h ⟨a,rfl⟩)

noncomputable def Poly.bool (f : Bool → Bool) : Poly boolBits boolBits f :=
  Poly.finite boolBits boolBits (by intro a b h; simpa [boolBits] using h) f

namespace Select

def trans (s : Fin 6 × Bool) (b : Bool) : (Fin 6 × Bool) × List Bool :=
  if s.1 = 0 then ((1,s.2),[])
  else if s.1 = 1 then ((2,b),[])
  else if s.1 = 2 then ((3,s.2),[])
  else if s.1 = 3 then ((if b then 4 else 5,s.2),[])
  else if s.1 = 4 then ((3,s.2),if s.2 then [b] else [])
  else ((5,s.2),if s.2 then [] else [b])

def emb (q : Fin 3) (b : Bool) : Fin 6 × Bool := (⟨q.val+3,by omega⟩,b)

theorem bound (s : Fin 6 × Bool) (b : Bool) : (trans s b).2.length ≤ 1 := by
  rcases s with ⟨q,f⟩
  fin_cases q <;> cases f <;> cases b <;> decide

theorem trans_emb (q : Fin 3) (flag b : Bool) :
    trans (emb q flag) b =
      (emb (Project.trans flag (!flag) q b).1 flag, (Project.trans flag (!flag) q b).2) := by
  fin_cases q <;> cases flag <;> cases b <;> rfl

theorem normal (q : Fin 3) (flag : Bool) (xs : List Bool) :
    Stream.output trans (fun _ => []) (emb q flag) xs =
      Stream.output (Project.trans flag (!flag)) (fun _ => []) q xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih => simp only [Stream.output, trans_emb, ih]

theorem encoded (flag : Bool) (a b : List Bool) :
    Stream.output trans (fun _ => []) (0,false) (pairBits [flag] (pairBits a b)) =
      if flag then a else b := by
  change Stream.output trans (fun _ => []) (emb 0 flag) (pairBits a b) = _
  rw [normal, Project.framed]
  cases flag <;> simp
end Select

noncomputable def Poly.select {α : Type} (e : α → List Bool) :
    Poly (prodBits boolBits (prodBits e e)) e
      (fun p : Bool × (α × α) => if p.1 then p.2.1 else p.2.2) :=
  (Stream.poly (0,false) Select.trans (fun _ => []) 1 Select.bound (by simp)).realizes
    (fun p => by simpa only [prodBits, boolBits, apply_ite] using
      Select.encoded p.1 (e p.2.1) (e p.2.2))

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Loop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                         
section

namespace VertexCover.Machine
open Turing Turing.TM2
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace Loop
variable (A : FinTM2)
abbrev K := A.K ⊕ Bool
abbrev Λ := A.Λ ⊕ Fin 3
abbrev State := A.σ × Bool × Option Bool
abbrev temporary : K A := .inr false
abbrev output : K A := .inr true
abbrev phase (i : Fin 3) : Λ A := .inr i
abbrev haltTarget : Option (Λ A) := some (phase A 0)

variable (inA : A.Γ A.k₀ ≃ Bool) (outA : A.Γ A.k₁ ≃ Bool)

open Compose (tapeOnly tapeOnly_nil tapeOnly_self tapeOnly_update init_tapes halt_tapes)

def extraTapes (temp out : List Bool) : Bool → List Bool
  | false => temp
  | true => out

@[simp] theorem extraTapes_false (temp out : List Bool) : extraTapes temp out false = temp := rfl
@[simp] theorem extraTapes_true (temp out : List Bool) : extraTapes temp out true = out := rfl

theorem update_extra_false (a b c : List Bool) :
    Function.update (extraTapes a b) false c = extraTapes c b := by
  funext k; cases k <;> simp [extraTapes]

theorem update_extra_true (a b c : List Bool) :
    Function.update (extraTapes a b) true c = extraTapes a c := by
  funext k; cases k <;> simp [extraTapes]

theorem halt_label (s : List (A.Γ A.k₁)) : (haltList A s).l = none := rfl

theorem halt_var (s : List (A.Γ A.k₁)) : (haltList A s).var = A.initialState := rfl

end Loop

inductive BoundedRun {α : Type} (e : α → List Bool) (body : α → Bool × α) (bound : ℕ) :
    α → α → ℕ → Prop
  | stop (a : α) (size : (e a).length ≤ bound) (done : (body a).1 = false) :
      BoundedRun e body bound a (body a).2 1
  | next (a z : α) (n : ℕ) (size : (e a).length ≤ bound) (more : (body a).1 = true)
      (tail : BoundedRun e body bound (body a).2 z n) :
      BoundedRun e body bound a z (n+1)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Lists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                        
section

namespace VertexCover.Machine

def listBits {α : Type} (e : α → List Bool) : List α → List Bool
  | [] => [false]
  | a::as => true :: pairBits (e a) (listBits e as)

@[simp] theorem listBits_nil {α : Type} (e : α → List Bool) : listBits e [] = [false] := rfl
@[simp] theorem listBits_cons {α : Type} (e : α → List Bool) (a : α) (as : List α) :
    listBits e (a::as) = true :: pairBits (e a) (listBits e as) := rfl

@[simp] theorem pairBits_length (a b : List Bool) : (pairBits a b).length = 2*a.length+1+b.length := by
  simp [pairBits, frame_length]

@[simp] theorem listBits_cons_length {α : Type} (e : α → List Bool) (a : α) (as : List α) :
    (listBits e (a::as)).length = 2*(e a).length+2+(listBits e as).length := by
  simp only [listBits_cons, List.length_cons, pairBits_length]; omega

theorem list_length_le_bits {α : Type} (e : α → List Bool) (as : List α) :
    as.length ≤ (listBits e as).length := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.length_cons, listBits_cons_length]; omega

theorem listBits_append_length {α : Type} (e : α → List Bool) (as bs : List α) :
    (listBits e (as++bs)).length + 1 = (listBits e as).length + (listBits e bs).length := by
  induction as with
  | nil => simp; omega
  | cons a as ih => simp only [List.cons_append,listBits_cons_length]; omega

namespace ListProject

def trans (left right : Bool) (defaultCode : List Bool) (q : Option (Fin 3)) (b : Bool) :
    Option (Fin 3) × List Bool :=
  match q with
  | none => if b then (some 0,[]) else (some 2,defaultCode)
  | some q => let r := Project.trans left right q b; (some r.1,r.2)

theorem bound (left right : Bool) (d : List Bool) (q : Option (Fin 3)) (b : Bool) :
    (trans left right d q b).2.length ≤ max 1 d.length := by
  cases q with
  | none => cases b <;> simp [trans]
  | some q => exact (Project.bound left right q b).trans (Nat.le_max_left _ _)

theorem normal (left right : Bool) (d : List Bool) (q : Fin 3) (xs : List Bool) :
    Stream.output (trans left right d) (fun _ => []) (some q) xs =
      Stream.output (Project.trans left right) (fun _ => []) q xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih => simp only [Stream.output,trans,ih]

theorem encoded {α : Type} (e : α → List Bool) (left right : Bool) (d : List Bool) (xs : List α) :
    Stream.output (trans left right d) (fun _ => []) none (listBits e xs) =
      match xs with
      | [] => d
      | a::as => (if left then e a else []) ++ (if right then listBits e as else []) := by
  cases xs with
  | nil => simp [listBits, Stream.output, trans]
  | cons a as =>
    change Stream.output (trans left right d) (fun _ => []) (some 0)
      (pairBits (e a) (listBits e as)) = _
    rw [normal, Project.framed]
end ListProject

noncomputable def Poly.listTail {α : Type} (e : α → List Bool) :
    Poly (listBits e) (listBits e) List.tail :=
  (Stream.poly none (ListProject.trans false true [false]) (fun _ => []) (max 1 [false].length)
    (ListProject.bound false true [false]) (by simp)).realizes (fun xs => by
      rw [ListProject.encoded]
      cases xs <;> simp)

noncomputable def Poly.listHeadD {α : Type} (e : α → List Bool) (a : α) :
    Poly (listBits e) e (fun xs => xs.headD a) :=
  (Stream.poly none (ListProject.trans true false (e a)) (fun _ => []) (max 1 (e a).length)
    (ListProject.bound true false (e a)) (by simp)).realizes (fun xs => by
      rw [ListProject.encoded]
      cases xs <;> simp)

noncomputable def Poly.listHasHead {α : Type} (e : α → List Bool) :
    Poly (listBits e) boolBits (fun xs => !xs.isEmpty) :=
  (Poly.headD false).encodeCongr (listBits e) (fun _ => rfl) (fun xs => by cases xs <;> rfl)

abbrev flagBits {α : Type} (e : α → List Bool) (p : Bool × α) : List Bool := p.1::e p.2

noncomputable def Poly.flag {α : Type} (e : α → List Bool) :
    Poly (prodBits boolBits e) (flagBits e) id :=
  Poly.append.encodeCongr (fun p => (boolBits p.1,e p.2)) (fun _ => rfl) (fun _ => rfl)

namespace Fold
variable {α β : Type} (f : β × α → β)

def body : β × List α → Bool × (β × List α)
  | (b,[]) => (false,(b,[]))
  | (b,a::as) => (true,(f (b,a),as))

theorem run (ea : α → List Bool) (eb : β → List Bool) (b : β) (xs : List α) (B : ℕ)
    (bound : ∀ pre suf, pre++suf=xs →
      (prodBits eb (listBits ea) (pre.foldl (fun b a => f (b,a)) b,suf)).length ≤ B) :
    BoundedRun (prodBits eb (listBits ea)) (body f) B (b,xs)
      (xs.foldl (fun b a => f (b,a)) b,[]) (xs.length+1) := by
  induction xs generalizing b with
  | nil => exact .stop _ (bound [] [] rfl) rfl
  | cons a as ih =>
    have htail : ∀ pre suf, pre++suf=as →
        (prodBits eb (listBits ea) (pre.foldl (fun b a => f (b,a)) (f (b,a)),suf)).length ≤ B := by
      intro pre suf h
      exact bound (a::pre) suf (by simp [h])
    exact .next _ _ _ (bound [] (a::as) rfl) rfl (ih (f (b,a)) htail)
end Fold

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Naturals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                       
section

namespace VertexCover.Machine

abbrev natBits (n : ℕ) : List Bool := List.replicate n true
@[simp] theorem natBits_length (n : ℕ) : (natBits n).length = n := List.length_replicate

noncomputable def Poly.natSucc : Poly natBits natBits Nat.succ :=
  (Poly.cons true).realizes (fun _ => rfl)

noncomputable def Poly.natAdd : Poly (prodBits natBits natBits) natBits
    (fun p : ℕ × ℕ => p.1+p.2) :=
  Poly.append.encodeCongr (fun p => (natBits p.1,natBits p.2)) (fun _ => rfl)
    (fun _ => (List.replicate_add _ _ _).symm)

namespace Iterate
variable {α : Type} (f : α → α)

def run : ℕ → α → α
  | 0,a => a
  | n+1,a => run n (f a)

def body : ℕ × α → Bool × (ℕ × α)
  | (0,a) => (false,(0,a))
  | (n+1,a) => (true,(n,f a))

end Iterate

theorem iterate_pred (k n : ℕ) : Iterate.run Nat.pred k n = n-k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [Iterate.run,ih, Nat.pred_eq_sub_one]; omega

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringLabels
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.PoweringLabels

open scoped BigOperators

variable {V D A : Type*}

abbrev PortWords (D : Type*) (t : Nat) := (n : Fin (t + 1)) × (Fin n.val → D)

instance finitePortWords [Finite D] (t : Nat) : Finite (PortWords D t) := by
  let := Fintype.ofFinite D
  exact Finite.of_fintype _

def scanWitness {A : Type*} (p : A → Prop) [DecidablePred p] :
    (xs : List A) → (∃ a ∈ xs, p a) → {a // p a}
  | [], h => False.elim (by simp at h)
  | a :: xs, h =>
    if ha : p a then ⟨a, ha⟩ else
      scanWitness p xs (by
        obtain ⟨b, hb, hp⟩ := h
        rcases List.mem_cons.mp hb with he | hm
        · exact False.elim (ha (he ▸ hp))
        · exact ⟨b, hm, hp⟩)

abbrev PaddedLabel (D : Type*) (t : Nat) (A : Type*) := PortWords D t → A

end UniqueGames.Foundations.PCP.PoweringLabels

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                        
section

namespace VertexCover.Machine

theorem foldl_count {α : Type} (xs : List α) (a : ℕ) :
    xs.foldl (fun n _ => n+1) a = xs.length+a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons,ih,List.length_cons]; omega

namespace RawList

def trans (_ : Unit) (b : Bool) : Unit × List Bool := ((),[true,true,b,false])

theorem encode (bs : List Bool) :
    Stream.output trans (fun _ => [false]) () bs = listBits boolBits bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [Stream.output,trans, ih]; rfl

end RawList

noncomputable def Poly.rawToList : Poly (id : List Bool → List Bool) (listBits boolBits) id :=
  (Stream.poly () RawList.trans (fun _ => [false]) 4 (by intros; rfl) (by intros; decide)).realizes
    RawList.encode

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGames.Foundations.PCP.PoweringMoment

open scoped BigOperators

def bit (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

def hits {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ i, bit (E i ω)

def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ := Finset.univ.expect f

theorem bit_nonneg (p : Prop) : 0 ≤ bit p := by
  classical
  by_cases hp : p <;> simp [bit, hp]

theorem bit_sq (p : Prop) : bit p ^ 2 = bit p := by
  classical
  by_cases hp : p <;> simp [bit, hp]

theorem bit_mul (p q : Prop) : bit p * bit q = bit (p ∧ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

theorem bit_mono {p q : Prop} (hpq : p → q) : bit p ≤ bit q := by
  classical
  by_cases hp : p
  · simp [bit, hp, hpq hp]
  · have hz : bit p = 0 := by simp [bit, hp]
    rw [hz]
    exact bit_nonneg q

theorem hits_nonneg {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) :
    0 ≤ hits E ω := Finset.sum_nonneg (fun i _ => bit_nonneg (E i ω))

theorem mean_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ mean f := Finset.expect_nonneg (fun ω _ => hf ω)

theorem mean_hits {I Ω : Type*} [Fintype I] [Fintype Ω] (E : I → Ω → Prop) :
    mean (hits E) = ∑ i, mean (fun ω => bit (E i ω)) := by
  exact Finset.expect_sum_comm _ _ _

theorem second_moment_eq {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E : I → Ω → Prop) :
    mean (fun ω => hits E ω ^ 2) =
      ∑ i, ∑ j, mean (fun ω => bit (E i ω ∧ E j ω)) := by
  simp only [hits, pow_two, Finset.sum_mul, Finset.mul_sum, bit_mul,
    mean, Finset.expect_sum_comm]
  exact Finset.sum_comm

theorem mean_witness_sq_le {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E W : I → Ω → Prop) (reject : Ω → Prop)
    (hWE : ∀ i ω, W i ω → E i ω)
    (hWR : ∀ i ω, W i ω → reject ω) :
    mean (hits W) ^ 2 ≤
      mean (fun ω => bit (reject ω)) * mean (fun ω => hits E ω ^ 2) := by
  classical
  have hNH (ω : Ω) : hits W ω ≤ hits E ω :=
    Finset.sum_le_sum (fun i _ => bit_mono (hWE i ω))
  have hzero (ω : Ω) (hr : ¬ reject ω) : hits W ω = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hw : ¬ W i ω := fun h => hr (hWR i ω h)
    simp [bit, hw]
  have hsupport (ω : Ω) : bit (reject ω) * hits W ω = hits W ω := by
    by_cases hr : reject ω
    · simp [bit, hr]
    · rw [hzero ω hr]
      simp
  have hCS := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => bit (reject ω)) (hits W)
  have hsquares : mean (fun ω => hits W ω ^ 2) ≤ mean (fun ω => hits E ω ^ 2) := by
    apply Finset.expect_le_expect
    intro ω _
    simpa only [pow_two] using
      (mul_le_mul (hNH ω) (hNH ω) (hits_nonneg W ω) (hits_nonneg E ω))
  calc
    _ ≤ mean (fun ω => bit (reject ω)) * mean (fun ω => hits W ω ^ 2) := by
      simpa only [mean, hsupport, bit_sq] using hCS
    _ ≤ _ := mul_le_mul_of_nonneg_left hsquares
      (mean_nonneg _ (fun ω => bit_nonneg (reject ω)))

theorem rejection_lower_bound {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E W : I → Ω → Prop) (reject : Ω → Prop)
    (hWE : ∀ i ω, W i ω → E i ω)
    (hWR : ∀ i ω, W i ω → reject ω)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfirst : a ≤ mean (hits W))
    (hsecond : mean (fun ω => hits E ω ^ 2) ≤ b) :
    a ^ 2 / b ≤ mean (fun ω => bit (reject ω)) := by
  have hN : 0 ≤ mean (hits W) := mean_nonneg _ (hits_nonneg W)
  have hρ : 0 ≤ mean (fun ω => bit (reject ω)) :=
    mean_nonneg _ (fun ω => bit_nonneg (reject ω))
  have haSq : a ^ 2 ≤ mean (hits W) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hfirst hfirst ha.le hN
  have hCS := mean_witness_sq_le E W reject hWE hWR
  apply (div_le_iff₀ hb).2
  exact haSq.trans (hCS.trans (mul_le_mul_of_nonneg_left hsecond hρ))

end UniqueGames.Foundations.PCP.PoweringMoment
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_BoundedBinary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                  
section

namespace VertexCover.Machine
open UniqueGames.BinaryEncoding

namespace CappedBinary
abbrev State := ℕ × ℕ
abbrev enc : State → List Bool := prodBits natBits natBits

def step (p : State × Bool) : State :=
  (p.1.1,min p.1.1 (Nat.bit p.2 p.1.2))

theorem fold_bound (xs : List Bool) (B v : ℕ) :
    (xs.foldl (fun s b => step (s,b)) (B,v)).1 = B ∧
    (xs.foldl (fun s b => step (s,b)) (B,v)).2 ≤ max B v := by
  induction xs generalizing v with
  | nil => exact ⟨rfl, Nat.le_max_right _ _⟩
  | cons b bs ih =>
    obtain ⟨h₁,h₂⟩ := ih (min B (Nat.bit b v))
    refine ⟨h₁, h₂.trans ?_⟩
    exact (max_le (le_refl _) (Nat.min_le_left _ _)).trans (Nat.le_max_left _ _)

end CappedBinary

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_LazySpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.LazySpectral

open SpectralReturn

noncomputable section

variable {V D : Type*}

theorem half_sum_sq_le (a b : ℝ) : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

end

end UniqueGames.Foundations.PCP.LazySpectral

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_CloudRounding
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.CloudRounding

open scoped BigOperators

theorem dart_rejection_count_le
    {E V A : Type*} [Fintype E] [DecidableEq A]
    (tail : E → V) (reverse : E ≃ E) (accepts : E → A → A → Bool)
    (ell : E → A) (rounded : V → A) :
    (Finset.univ.filter (fun e =>
      accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)).card ≤
    (Finset.univ.filter (fun e => accepts e (ell e) (ell (reverse e)) = false)).card +
      2 * (Finset.univ.filter (fun e => ell e ≠ rounded (tail e))).card := by
  classical
  let R : Finset E := Finset.univ.filter (fun e =>
    accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)
  let B : Finset E := Finset.univ.filter (fun e =>
    accepts e (ell e) (ell (reverse e)) = false)
  let M : Finset E := Finset.univ.filter (fun e => ell e ≠ rounded (tail e))
  let MR : Finset E := Finset.univ.filter (fun e =>
    ell (reverse e) ≠ rounded (tail (reverse e)))
  have hrev : MR.card = M.card := by
    have hsets : MR = M.map reverse.symm.toEmbedding := by
      ext e
      constructor
      · intro he
        apply Finset.mem_map.mpr
        refine ⟨reverse e, ?_, reverse.symm_apply_apply e⟩
        simpa [MR, M] using he
      · intro he
        obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
        simpa [MR, M] using hd
    rw [hsets, Finset.card_map]
  have hsub : R ⊆ (B ∪ M) ∪ MR := by
    intro e he
    by_cases hl : ell e = rounded (tail e)
    · by_cases hr : ell (reverse e) = rounded (tail (reverse e))
      · have hb : e ∈ B := by simpa [B, R, hl, hr] using he
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
      · exact Finset.mem_union_right _ (by simp [MR, hr])
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [M, hl]))
  change R.card ≤ B.card + 2 * M.card
  calc
    R.card ≤ ((B ∪ M) ∪ MR).card := Finset.card_le_card hsub
    _ ≤ (B ∪ M).card + MR.card := Finset.card_union_le _ _
    _ ≤ (B.card + M.card) + MR.card :=
      Nat.add_le_add_right (Finset.card_union_le B M) _
    _ = B.card + 2 * M.card := by rw [hrev]; omega

section CloudCounts

variable {X A D : Type*} [Fintype X] [Fintype A] [Fintype D]
variable [DecidableEq X] [DecidableEq A]

def colorSet (ell : X → A) (a : A) : Finset X :=
  Finset.univ.filter (fun x => ell x = a)

def minoritySet (ell : X → A) (m : A) : Finset X :=
  Finset.univ.filter (fun x => ell x ≠ m)

def directedCut (next : X × D → X) (S : Finset X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => xd.1 ∈ S ∧ next xd ∉ S)

def disagreementSet (ell : X → A) (next : X × D → X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => ell xd.1 ≠ ell (next xd))

abbrev Nonmajor (m : A) := {a : A // a ≠ m}

omit [DecidableEq X] in
theorem exists_max_color (ell : X → A) [Nonempty A] :
    ∃ m : A, ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun a : A => (colorSet ell a).card) Finset.univ_nonempty
  exact ⟨m, fun a => hm a (Finset.mem_univ a)⟩

noncomputable def majority (ell : X → A) [Nonempty A] : A :=
  Classical.choose (exists_max_color ell)

omit [DecidableEq X] in
theorem majority_maximal (ell : X → A) [Nonempty A] (a : A) :
    (colorSet ell a).card ≤ (colorSet ell (majority ell)).card :=
  Classical.choose_spec (exists_max_color ell) a

omit [Fintype A] in
                                                             
theorem nonchosen_color_twice_le (ell : X → A) (m : A)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (a : A) (ha : a ≠ m) :
    2 * (colorSet ell a).card ≤ Fintype.card X := by
  have hd : Disjoint (colorSet ell a) (colorSet ell m) := by
    apply Finset.disjoint_left.mpr
    intro x hx hm
    have hxa : ell x = a := by simpa [colorSet] using hx
    have hxm : ell x = m := by simpa [colorSet] using hm
    exact ha (hxa.symm.trans hxm)
  have hu : (colorSet ell a).card + (colorSet ell m).card ≤ Fintype.card X := by
    calc
      _ = (colorSet ell a ∪ colorSet ell m).card :=
        (Finset.card_union_of_disjoint hd).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card X := Finset.card_univ
  have hm := maximal a
  omega

def minorityEquiv (ell : X → A) (m : A) :
    (Σ a : Nonmajor m, ↥(colorSet ell a.val)) ≃ ↥(minoritySet ell m) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val = t.1.val := (Finset.mem_filter.mp t.2.property).2
    have hn : ell t.2.val ≠ m := fun h => t.1.property (hc.symm.trans h)
    simpa [minoritySet] using hn⟩
  invFun x :=
    ⟨⟨ell x.val, by simpa [minoritySet] using x.property⟩,
      ⟨x.val, by simp [colorSet]⟩⟩
  left_inv t := by
    rcases t with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    have hxa : ell x = a := by simpa [colorSet] using hx
    cases hxa
    rfl
  right_inv x := by apply Subtype.ext; rfl

omit [DecidableEq X] in
theorem minority_card_eq_sum (ell : X → A) (m : A) :
    (minoritySet ell m).card = ∑ a : Nonmajor m, (colorSet ell a.val).card := by
  have h := Fintype.card_congr (minorityEquiv ell m)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

def minorityCutEmbedding (ell : X → A) (next : X × D → X) (m : A) :
    (Σ a : Nonmajor m, ↥(directedCut next (colorSet ell a.val))) ↪
      ↥(disagreementSet ell next) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val.1 = t.1.val ∧ ell (next t.2.val) ≠ t.1.val := by
      simpa [directedCut, colorSet] using t.2.property
    have hn : ell t.2.val.1 ≠ ell (next t.2.val) :=
      fun h => hc.2 (h.symm.trans hc.1)
    simpa [disagreementSet] using hn⟩
  inj' p q h := by
    rcases p with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    rcases q with ⟨⟨b, hb⟩, ⟨y, hy⟩⟩
    have hxy : x = y := congrArg Subtype.val h
    cases hxy
    have hxa : ell x.1 = a := by
      have hc : ell x.1 = a ∧ ell (next x) ≠ a := by
        simpa [directedCut, colorSet] using hx
      exact hc.1
    have hxb : ell x.1 = b := by
      have hc : ell x.1 = b ∧ ell (next x) ≠ b := by
        simpa [directedCut, colorSet] using hy
      exact hc.1
    have hab : a = b := hxa.symm.trans hxb
    cases hab
    rfl

theorem minority_cut_sum_le (ell : X → A) (next : X × D → X) (m : A) :
    (∑ a : Nonmajor m, (directedCut next (colorSet ell a.val)).card) ≤
      (disagreementSet ell next).card := by
  have h := Fintype.card_le_of_injective
    (minorityCutEmbedding ell next m) (minorityCutEmbedding ell next m).injective
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h

theorem minority_expansion_bound (ell : X → A) (next : X × D → X) (m : A)
    (h : ℚ)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (expansion : ∀ S : Finset X, S.card ≤ Fintype.card X / 2 →
      h * (S.card : ℚ) ≤ ((directedCut next S).card : ℚ)) :
    h * ((minoritySet ell m).card : ℚ) ≤ ((disagreementSet ell next).card : ℚ) := by
  have each (a : Nonmajor m) :
      h * ((colorSet ell a.val).card : ℚ) ≤
        ((directedCut next (colorSet ell a.val)).card : ℚ) := by
    apply expansion
    have ha := nonchosen_color_twice_le ell m maximal a.val a.property
    omega
  calc
    h * ((minoritySet ell m).card : ℚ) =
        ∑ a : Nonmajor m, h * ((colorSet ell a.val).card : ℚ) := by
      rw [minority_card_eq_sum, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ a : Nonmajor m, ((directedCut next (colorSet ell a.val)).card : ℚ) :=
      Finset.sum_le_sum (fun a _ => each a)
    _ ≤ ((disagreementSet ell next).card : ℚ) := by
      exact_mod_cast minority_cut_sum_le ell next m

end CloudCounts

end UniqueGames.Foundations.PCP.CloudRounding

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_SpectralCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                    

noncomputable section
namespace UniqueGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicator (S : Finset V) (v : V) : ℝ := if v ∈ S then 1 else 0

omit [Fintype V] in
theorem indicator_nonnegative (S : Finset V) (v : V) : 0 ≤ indicator S v := by
  unfold indicator
  split_ifs <;> norm_num
end Indicators

end UniqueGames.Foundations.PCP.SpectralCut
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.PreprocessingLevels

def levelLoop (g k : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, e, s => (e, s)
  | fuel + 1, e, s =>
      if k ≤ s then (e, s)
      else levelLoop g k fuel (e + 1) (s * g)

theorem levelLoop_power (g k fuel e : Nat) :
    (levelLoop g k fuel e (g ^ e)).2 =
      g ^ (levelLoop g k fuel e (g ^ e)).1 := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · rfl
      · simpa only [pow_succ] using ih (e + 1)

theorem levelLoop_covers (g k fuel e s : Nat) (hg : 1 < g)
    (hs : 0 < s) (hbudget : k ≤ s + fuel) :
    k ≤ (levelLoop g k fuel e s).2 := by
  induction fuel generalizing e s with
  | zero => simpa only [levelLoop, Nat.add_zero] using hbudget
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · assumption
      · apply ih
        · exact Nat.mul_pos hs (by omega)
        · have htwo : 2 ≤ g := by omega
          have hmul : s * 2 ≤ s * g := Nat.mul_le_mul_left s htwo
          omega

theorem levelLoop_le_of_covering_power (g k fuel e j : Nat)
    (he : e ≤ j) (hj : k ≤ g ^ j) :
    (levelLoop g k fuel e (g ^ e)).1 ≤ j := by
  induction fuel generalizing e with
  | zero => exact he
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · exact he
      · rename_i hnot
        have hne : e ≠ j := by
          intro h
          subst e
          exact hnot hj
        have hnext : e + 1 ≤ j := by omega
        simpa only [pow_succ] using ih (e + 1) hnext

end UniqueGames.Foundations.PCP.PreprocessingLevels

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover
open Machine

namespace Approximation
variable {α : ℝ}

def test (A : Approximation α) (m : ℕ) (G : ExplicitGraph) : Bool :=
  decide (m*(A.run G).length < (m-1)*G.n)

end Approximation

end VertexCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringAddresses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                          

namespace UniqueGames.Foundations.PCP.PoweringAddresses

open PoweringLabels
open scoped BigOperators

variable {V : Type*}

def allWords (d : Nat) : (n : Nat) → List (Fin n → Fin d)
  | 0 => [Fin.elim0]
  | n + 1 => (List.finRange d).flatMap fun a =>
      (allWords d n).map fun p => Fin.cases a p

theorem mem_allWords (d : Nat) :
    ∀ n (p : Fin n → Fin d), p ∈ allWords d n := by
  intro n
  induction n with
  | zero =>
    intro p
    simp only [allWords, List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro p
    simp only [allWords, List.mem_flatMap, List.mem_map]
    refine ⟨p 0, List.mem_finRange (p 0), (fun j => p j.succ), ih _, ?_⟩
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

def allAddresses (d t : Nat) : List (PortWords (Fin d) t) :=
  (List.finRange (t + 1)).flatMap fun n =>
    (allWords d n.val).map fun p => Sigma.mk n p

theorem mem_allAddresses (d t : Nat) (w : PortWords (Fin d) t) :
    w ∈ allAddresses d t := by
  rcases w with ⟨n, p⟩
  unfold allAddresses
  apply List.mem_flatMap.mpr
  refine ⟨n, List.mem_finRange n, ?_⟩
  exact List.mem_map.mpr ⟨p, mem_allWords d n.val p, rfl⟩

end UniqueGames.Foundations.PCP.PoweringAddresses

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                         

namespace UniqueGames.Foundations.PCP.PoweringDecoding

open scoped BigOperators

variable {Ω A : Type*} [Fintype Ω] [Nonempty Ω] [Fintype A] [Nonempty A]

noncomputable def mass (opinion : Ω → A) (a : A) : ℝ := by
  classical
  exact Finset.univ.expect (fun ω => if opinion ω = a then 1 else 0)

omit [Nonempty A] in
theorem mass_sum (opinion : Ω → A) : (∑ a, mass opinion a) = 1 := by
  classical
  calc
    (∑ a, mass opinion a) =
        (Finset.univ : Finset Ω).expect
          (fun ω => ∑ a : A, if opinion ω = a then (1 : ℝ) else 0) :=
      (Finset.expect_sum_comm (Finset.univ : Finset Ω) (Finset.univ : Finset A)
        (fun ω a => if opinion ω = a then (1 : ℝ) else 0)).symm
    _ = (Finset.univ : Finset Ω).expect (fun _ => (1 : ℝ)) := by
      apply Finset.expect_congr rfl
      intro ω _
      simp
    _ = 1 := Finset.expect_const Finset.univ_nonempty 1

omit [Nonempty Ω] in
theorem exists_mode (opinion : Ω → A) :
    ∃ a : A, ∀ b : A, mass opinion b ≤ mass opinion a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A)
    (mass opinion) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

noncomputable def mode (opinion : Ω → A) : A := Classical.choose (exists_mode opinion)

omit [Nonempty Ω] in
theorem mode_max (opinion : Ω → A) (b : A) :
    mass opinion b ≤ mass opinion (mode opinion) :=
  Classical.choose_spec (exists_mode opinion) b

theorem mode_mass_lower (opinion : Ω → A) :
    1 / (Fintype.card A : ℝ) ≤ mass opinion (mode opinion) := by
  have hk : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (1 : ℝ) ≤ mass opinion (mode opinion) * (Fintype.card A : ℝ) := by
    calc
      (1 : ℝ) = ∑ a : A, mass opinion a := (mass_sum opinion).symm
      _ ≤ ∑ _a : A, mass opinion (mode opinion) :=
        Finset.sum_le_sum (fun a _ => mode_max opinion a)
      _ = mass opinion (mode opinion) * (Fintype.card A : ℝ) := by simp [mul_comm]
  exact (div_le_iff₀ hk).2 hsum

end UniqueGames.Foundations.PCP.PoweringDecoding

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.PoweringReturn

open SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

def portConsEquiv (D : Type*) (n : Nat) :
    (D × (Fin n → D)) ≃ (Fin (n + 1) → D) where
  toFun z := Fin.cases z.1 z.2
  invFun r := (r 0, fun j => r j.succ)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext j
      rfl
  right_inv r := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

theorem bit_bool (b : Bool) : bit (b = true) = (if b then 1 else 0 : ℝ) := by
  cases b <;> simp [bit]

end UniqueGames.Foundations.PCP.PoweringReturn

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringMomentBound
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.PoweringMomentBound

open scoped BigOperators
open SpectralReturn PoweringReturn
open PoweringMoment (bit hits)

theorem symmetric_gap_matrix_sum (ε : ℝ) (r : Nat → ℝ) :
    ∀ (m : Nat) (f : Fin m → Fin m → ℝ),
      (∀ i j, f i j = f j i) → (∀ i, f i i = ε) →
      (∀ i j, i.val < j.val → f i j = r (j.val - i.val - 1)) →
      (∑ i, ∑ j, f i j) = (m : ℝ) * ε +
        2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap := by
  intro m
  induction m with
  | zero => intro f _hSym _hDiag _hUpper; simp
  | succ m ih =>
    intro f hSym hDiag hUpper
    have hOld : (∑ i : Fin m, ∑ j : Fin m, f i.castSucc j.castSucc) =
        (m : ℝ) * ε + 2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap := by
      apply ih (fun i j => f i.castSucc j.castSucc)
      · intro i j; exact hSym i.castSucc j.castSucc
      · intro i; exact hDiag i.castSucc
      · intro i j hij; exact hUpper i.castSucc j.castSucc hij
    have hLast : (∑ i : Fin m, f i.castSucc (Fin.last m)) =
        ∑ gap ∈ Finset.range m, r gap := by
      calc
        _ = ∑ i : Fin m, r (m - 1 - i.val) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hUpper i.castSucc (Fin.last m) i.isLt]
          simp only [Fin.val_last, Fin.val_castSucc]
          congr 1
          omega
        _ = ∑ i ∈ Finset.range m, r (m - 1 - i) :=
          Fin.sum_univ_eq_sum_range (fun i => r (m - 1 - i)) m
        _ = _ := Finset.sum_range_reflect r m
    have hLastRow : (∑ j : Fin m, f (Fin.last m) j.castSucc) =
        ∑ gap ∈ Finset.range m, r gap := by
      calc
        _ = ∑ j : Fin m, f j.castSucc (Fin.last m) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hSym (Fin.last m) j.castSucc
        _ = _ := hLast
    calc
      (∑ i, ∑ j, f i j) =
          (∑ i : Fin m, ∑ j : Fin m, f i.castSucc j.castSucc) +
            (∑ i : Fin m, f i.castSucc (Fin.last m)) +
            (∑ j : Fin m, f (Fin.last m) j.castSucc) + f (Fin.last m) (Fin.last m) := by
        simp only [Fin.sum_univ_castSucc, Finset.sum_add_distrib]
        ring
      _ = (m : ℝ) * ε +
          2 * (∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap) +
          (∑ gap ∈ Finset.range m, r gap) + (∑ gap ∈ Finset.range m, r gap) + ε := by
        rw [hOld, hLast, hLastRow, hDiag]
      _ = ((m + 1 : Nat) : ℝ) * ε +
          2 * ∑ j ∈ Finset.range (m + 1), ∑ gap ∈ Finset.range j, r gap := by
        rw [Finset.sum_range_succ]
        simp only [Nat.cast_add, Nat.cast_one]
        ring

def windowIndex (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) : Fin (n + 1) :=
  ⟨start + i.val, (Nat.add_lt_add_left i.isLt start).trans_le h⟩

end UniqueGames.Foundations.PCP.PoweringMomentBound

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringNumeric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                        

namespace UniqueGames.Foundations.PCP.PoweringNumeric

theorem min_density_ratio (ε C k t : ℝ)
    (hε : 0 < ε) (hC : 0 < C) (hk : 0 ≤ k)
    (ht : 0 < t) (hkt : k ≤ t) :
    min ε (1 / t) / (C + 1) ≤ ε / (C + k * ε) := by
  have hx : 0 ≤ min ε (1 / t) :=
    le_min hε.le (one_div_nonneg.mpr ht.le)
  have hxt : min ε (1 / t) * t ≤ 1 :=
    (le_div_iff₀ ht).mp (min_le_right ε (1 / t))
  have hkx : k * min ε (1 / t) ≤ 1 := by
    calc
      k * min ε (1 / t) ≤ t * min ε (1 / t) :=
        mul_le_mul_of_nonneg_right hkt hx
      _ ≤ 1 := by simpa only [mul_comm] using hxt
  have hC1 : 0 < C + 1 := by positivity
  have hden : 0 < C + k * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  apply (div_le_div_iff₀ hC1 hden).2
  calc
    min ε (1 / t) * (C + k * ε) =
        C * min ε (1 / t) + ε * (k * min ε (1 / t)) := by ring
    _ ≤ C * ε + ε * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (min_le_left ε (1 / t)) hC.le)
        (mul_le_mul_of_nonneg_left hkx hε.le)
    _ = ε * (C + 1) := by ring

theorem count_moment_ratio_lower (α ε C t : ℝ) (m : ℕ)
    (hm : 0 < m) (hε : 0 < ε) (hC : 0 < C) (ht : 0 < t)
    (hmt : (m : ℝ) - 1 ≤ t) :
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) ≤
      (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hk : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hm1
  have hden : 0 < C + ((m : ℝ) - 1) * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  have hαm : 0 ≤ α ^ 4 * (m : ℝ) := by positivity
  have hratio := min_density_ratio ε C ((m : ℝ) - 1) t hε hC hk ht hmt
  calc
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) =
        (α ^ 4 * (m : ℝ)) * (min ε (1 / t) / (C + 1)) := by ring
    _ ≤ (α ^ 4 * (m : ℝ)) * (ε / (C + ((m : ℝ) - 1) * ε)) :=
      mul_le_mul_of_nonneg_left hratio hαm
    _ = (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
      field_simp [ne_of_gt hm0, ne_of_gt hε, ne_of_gt hden]

end UniqueGames.Foundations.PCP.PoweringNumeric

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringSoundness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                          

noncomputable section

namespace UniqueGames.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open PoweringLabels
open SpectralReturn PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

def center (q M : Nat) : Nat := (4 * q * M) ^ 2

theorem le_center (q M : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M) : M ≤ center q M := by
  have hfour : 1 ≤ 4 * q := by omega
  have hx : M ≤ 4 * q * M := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right M hfour
  have hone : 1 ≤ 4 * q * M := hM.trans hx
  have hsquare : 4 * q * M ≤ (4 * q * M) * (4 * q * M) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * q * M) hone
  exact hx.trans (by simpa only [center, pow_two] using hsquare)

def gain (q M : Nat) (lambda : ℝ) : ℝ :=
  (1 / (2 * (q : ℝ))) ^ 4 * ((2 * M + 1 : Nat) : ℝ) /
    ((1 + 2 / (1 - lambda)) + 1)

end UniqueGames.Foundations.PCP.PoweringSoundness
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                    

namespace UniqueGames.Foundations.PCP.PoweringGap

open PoweringLabels
open SpectralReturn PoweringSoundness

variable {V D A : Type*}

theorem gain_nonneg (q M : Nat) (lambda : ℝ) (hlambda : lambda < 1) :
    0 ≤ gain q M lambda := by
  have hden : 0 < 1 - lambda := sub_pos.mpr hlambda
  unfold gain
  positivity

end UniqueGames.Foundations.PCP.PoweringGap

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringEnumeration
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.PoweringEnumeration

open PoweringLabels
open scoped BigOperators

def addressCount (d t : Nat) : Nat := ∑ i : Fin (t + 1), d ^ i.val

def reverseWordEquiv (d n : Nat) : (Fin n → Fin d) ≃ (Fin n → Fin d) where
  toFun p i := p i.rev
  invFun p i := p i.rev
  left_inv p := by funext i; simp only [Fin.rev_rev]
  right_inv p := by funext i; simp only [Fin.rev_rev]

def wordEquiv (d n : Nat) : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  (reverseWordEquiv d n).trans finFunctionFinEquiv

def addressEquiv (d t : Nat) : PortWords (Fin d) t ≃ Fin (addressCount d t) :=
  (Equiv.sigmaCongrRight (fun i : Fin (t + 1) => wordEquiv d i.val)).trans
    finSigmaFinEquiv

def paddedLabelEquiv (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) ≃ Fin (q ^ addressCount d t) :=
  ((addressEquiv d t).arrowCongr (Equiv.refl (Fin q))).trans
    (wordEquiv q (addressCount d t))

def orientationEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem orientationEquiv_false : orientationEquiv false = 0 := rfl
@[simp] theorem orientationEquiv_true : orientationEquiv true = 1 := rfl

def dartBlockEquiv (d n : Nat) :
    ((Fin (n + 1) → Fin d) × Bool) ≃ Fin (2 * d ^ (n + 1)) :=
  ((wordEquiv d (n + 1)).prodCongr orientationEquiv).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm (d ^ (n + 1)) 2)))

theorem dartBlockEquiv_val (d n : Nat) (p : Fin (n + 1) → Fin d) (b : Bool) :
    (dartBlockEquiv d n (p, b)).val =
      2 * (wordEquiv d (n + 1) p).val + (orientationEquiv b).val := by
  change (orientationEquiv b).val + 2 * (wordEquiv d (n + 1) p).val = _
  exact Nat.add_comm _ _

def dartVertexEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      (Fin vertices × ((Fin (n + 1) → Fin d) × Bool)) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv x := by rcases x with ⟨b, v, p⟩; rfl
  right_inv x := by rcases x with ⟨v, p, b⟩; rfl

def dartEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      Fin (2 * vertices * d ^ (n + 1)) :=
  (dartVertexEquiv vertices d n).trans
    (((Equiv.refl (Fin vertices)).prodCongr (dartBlockEquiv d n)).trans
      (finProdFinEquiv.trans
        (finCongr (show vertices * (2 * d ^ (n + 1)) =
          2 * vertices * d ^ (n + 1) by ac_rfl))))

theorem dartEquiv_val (vertices d n : Nat) (b : Bool) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) :
    (dartEquiv vertices d n (b, (v, p))).val =
      (2 * d ^ (n + 1)) * v.val +
        2 * (wordEquiv d (n + 1) p).val + (orientationEquiv b).val := by
  change (dartBlockEquiv d n (p, b)).val + (2 * d ^ (n + 1)) * v.val = _
  rw [dartBlockEquiv_val]
  omega

def decodeWord (d n : Nat) : Fin (d ^ n) → (Fin n → Fin d) := (wordEquiv d n).symm

def encodeAddress (d t : Nat) : PortWords (Fin d) t → Fin (addressCount d t) :=
  addressEquiv d t

def encodeLabel (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) → Fin (q ^ addressCount d t) := paddedLabelEquiv d t q

def decodeLabel (d t q : Nat) :
    Fin (q ^ addressCount d t) → PaddedLabel (Fin d) t (Fin q) :=
  (paddedLabelEquiv d t q).symm

@[simp] theorem decodeLabel_encodeLabel (d t q : Nat) (a : PaddedLabel (Fin d) t (Fin q)) :
    decodeLabel d t q (encodeLabel d t q a) = a := (paddedLabelEquiv d t q).symm_apply_apply a

@[simp] theorem encodeLabel_decodeLabel (d t q : Nat) (i : Fin (q ^ addressCount d t)) :
    encodeLabel d t q (decodeLabel d t q i) = i := (paddedLabelEquiv d t q).apply_symm_apply i

@[simp] theorem decodeLabel_apply (d t q : Nat) (i : Fin (q ^ addressCount d t))
    (w : PortWords (Fin d) t) :
    decodeLabel d t q i w = decodeWord q (addressCount d t) i (encodeAddress d t w) := rfl

def encodeDart (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) →
      Fin (2 * vertices * d ^ (n + 1)) := dartEquiv vertices d n

def decodeDart (vertices d n : Nat) :
    Fin (2 * vertices * d ^ (n + 1)) →
      (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) := (dartEquiv vertices d n).symm

@[simp] theorem decodeDart_encodeDart (vertices d n : Nat)
    (e : Bool × (Fin vertices × (Fin (n + 1) → Fin d))) :
    decodeDart vertices d n (encodeDart vertices d n e) = e :=
  (dartEquiv vertices d n).symm_apply_apply e

@[simp] theorem encodeDart_decodeDart (vertices d n : Nat)
    (i : Fin (2 * vertices * d ^ (n + 1))) :
    encodeDart vertices d n (decodeDart vertices d n i) = i :=
  (dartEquiv vertices d n).apply_symm_apply i

end UniqueGames.Foundations.PCP.PoweringEnumeration

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.PoweringTables

open PoweringLabels PoweringAddresses PoweringEnumeration

def labelCount (d n : Nat) : Nat := 64 ^ addressCount d (n + 1)

def dartCount (vertices d n : Nat) : Nat := 2 * vertices * d ^ (n + 1)

end UniqueGames.Foundations.PCP.PoweringTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringPortReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

noncomputable section
namespace UniqueGames.Foundations.PCP.PoweringPortReindex
open PoweringLabels
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def wordEquiv (ports : D ≃ E) (n : Nat) : (Fin n → D) ≃ (Fin n → E) where
  toFun p := fun i => ports (p i)
  invFun p := fun i => ports.symm (p i)
  left_inv p := by funext i; exact ports.symm_apply_apply (p i)
  right_inv p := by funext i; exact ports.apply_symm_apply (p i)

def addressEquiv (ports : D ≃ E) (t : Nat) : PortWords D t ≃ PortWords E t where
  toFun w := ⟨w.1, wordEquiv ports w.1.val w.2⟩
  invFun w := ⟨w.1, (wordEquiv ports w.1.val).symm w.2⟩
  left_inv w := by rcases w with ⟨n,p⟩; simp
  right_inv w := by rcases w with ⟨n,p⟩; simp

end UniqueGames.Foundations.PCP.PoweringPortReindex

end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AlphabetGraphBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

def localEventFactor (q : Nat) : Nat :=
  4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5

def vertexFactor (q : Nat) : Nat := localEventFactor q + 2 ^ (q * q)

def dartFactor (q : Nat) : Nat := 12 * localEventFactor q

def sizeFactor (q : Nat) : Nat := 2 ^ q + vertexFactor q + dartFactor q

theorem sizeFactor_positive (q : Nat) : 0 < sizeFactor q := by
  have hp : (0 : Nat) < 2 ^ q := pow_pos (by decide) q
  unfold sizeFactor
  omega

end UniqueGames.Foundations.PCP.AlphabetGraphBounds

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_FinalConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.FinalConstants

def alphabet : Nat := 64
def compositionLoss : Nat := 12288
def denominator : Nat := 16 * alphabet ^ 4 * 66 * compositionLoss

theorem denominator_positive : 0 < denominator := by
  norm_num [denominator, alphabet, compositionLoss]

end UniqueGames.Foundations.PCP.FinalConstants

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringFinalConstants
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                               

namespace UniqueGames.Foundations.PCP.PoweringFinalConstants

abbrev Alphabet := Fin 6 → Bool

@[simp] theorem card_alphabet : Fintype.card Alphabet = 64 := by
  norm_num [Alphabet, Fintype.card_fun]

theorem spectral_denominator_eq :
    (1 + 2 / (1 - (31 / 32 : ℝ))) + 1 = 66 := by
  norm_num

end UniqueGames.Foundations.PCP.PoweringFinalConstants

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_InitialGraph
attribute [-instance] _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.clauseAnswerFintype _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.clauseAnswerInhabited _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.slotFintype _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.slotInhabited _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_J _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_clauseAnswer _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_slot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.InitialGraph

abbrev Label := Bool × Bool × Bool

instance slotFintype : Fintype Slot where
  elems := {Slot.first, Slot.second, Slot.third}
  complete := by intro s; cases s <;> simp

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide
@[simp] theorem card_label : Fintype.card Label = 8 := by
  simp [Label, Fintype.card_prod]

def toClauseAnswer (label : Label) : ClauseAnswer := ⟨label.1, label.2.1, label.2.2⟩
def fromClauseAnswer (answer : ClauseAnswer) : Label := (answer.first, answer.second, answer.third)
def variableLabel (value : Bool) : Label := (value, false, false)

@[simp] theorem to_fromClauseAnswer (answer : ClauseAnswer) :
    toClauseAnswer (fromClauseAnswer answer) = answer := by
  cases answer; rfl

def variableValid (label : Label) : Bool :=
  decide (label.2.1 = false ∧ label.2.2 = false)

theorem clauseAnswer_eq_of_slots (a b : ClauseAnswer)
    (h : ∀ s, answerAt a s = answerAt b s) : a = b := by
  rcases a with ⟨a₀, a₁, a₂⟩
  rcases b with ⟨b₀, b₁, b₂⟩
  have h₀ : a₀ = b₀ := h .first
  have h₁ : a₁ = b₁ := h .second
  have h₂ : a₂ = b₂ := h .third
  cases h₀; cases h₁; cases h₂; rfl

end UniqueGames.Foundations.PCP.InitialGraph

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_BinaryCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

namespace UniqueGames.Integration.BinaryCoordinates

abbrev Coordinates (n : Nat) := Fin n → Bool

def pack : {n : Nat} → Coordinates n → BitVec n
  | 0, _ => 0
  | _ + 1, f => BitVec.concat (pack (fun i => f i.succ)) (f 0)

def unpack {n : Nat} (v : BitVec n) : Coordinates n :=
  fun i => v.getLsbD i.val

theorem pack_get {n : Nat} (f : Coordinates n) (i : Fin n) :
    (pack f).getLsbD i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact BitVec.getLsbD_concat_zero
    · exact (BitVec.getLsbD_concat_succ).trans (ih (fun j => f j.succ) j)

theorem unpack_pack {n : Nat} (f : Coordinates n) : unpack (pack f) = f := by
  funext i
  exact pack_get f i

theorem pack_unpack {n : Nat} (v : BitVec n) : pack (unpack v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact pack_get (unpack v) ⟨i, hi⟩

end UniqueGames.Integration.BinaryCoordinates

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_RawInitialTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                         

namespace UniqueGames.Foundations.PCP.RawInitialTables

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by fin_cases i; rfl

def binaryOrder (n : Nat) : (Fin n → Bool) ≃ Fin (2 ^ n) where
  toFun bits := (UniqueGames.Integration.BinaryCoordinates.pack bits).toFin
  invFun index := UniqueGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index)
  left_inv bits := UniqueGames.Integration.BinaryCoordinates.unpack_pack bits
  right_inv index := by
    change (UniqueGames.Integration.BinaryCoordinates.pack
      (UniqueGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index))).toFin = index
    rw [UniqueGames.Integration.BinaryCoordinates.pack_unpack]

end UniqueGames.Foundations.PCP.RawInitialTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_RoundTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                    

namespace UniqueGames.Foundations.PCP.RoundTables

theorem dartFactor_positive (q : Nat) : 0 < AlphabetGraphBounds.dartFactor q := by
  unfold AlphabetGraphBounds.dartFactor AlphabetGraphBounds.localEventFactor
  positivity

end UniqueGames.Foundations.PCP.RoundTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_VerifierToCNF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                      
section

namespace UniqueGames.Foundations.PCP.VerifierToCNF

abbrev BoolTriple := Bool × Bool × Bool

def tripleValue (t : BoolTriple) : Bool := (t.1 || t.2.1) || t.2.2

def chainView : List Bool → List Bool → List BoolTriple
  | [a, b, «c»], [] => [(a, b, «c»)]
  | a :: b :: rest, y :: ys => (a, b, y) :: chainView ((!y) :: rest) ys
  | _, _ => []

theorem chainView_length (bits ys : List Bool)
    (size : bits.length = ys.length + 3) :
    (chainView bits ys).length = ys.length + 1 := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, «c»] => rfl
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have h := ih ((!y) :: rest) smaller
      simpa only [chainView, List.length_cons] using congrArg (fun n => n + 1) h

theorem chainView_sound (bits ys : List Bool)
    (size : bits.length = ys.length + 3)
    (accepted : (chainView bits ys).all tripleValue = true) : bits.any id = true := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, «c»] => simpa [chainView, tripleValue, Bool.or_assoc] using accepted
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have accepted' : tripleValue (a, b, y) = true ∧
          (chainView ((!y) :: rest) ys).all tripleValue = true := by
        simpa only [chainView, List.all_cons, Bool.and_eq_true] using accepted
      have tailAccepted := ih ((!y) :: rest) smaller accepted'.2
      cases a <;> cases b <;> cases y <;> simp_all [tripleValue]

theorem zero_false_count_iff_all (bits : List Bool) :
    bits.count false = 0 ↔ bits.all id = true := by
  induction bits with
  | nil => simp
  | cons b bits ih => cases b <;> simp [ih]

theorem chainView_failed (bits ys : List Bool)
    (size : bits.length = ys.length + 3) (failed : bits.any id = false) :
    1 ≤ ((chainView bits ys).map tripleValue).count false := by
  by_contra none
  have zero : ((chainView bits ys).map tripleValue).count false = 0 := by omega
  have all := (zero_false_count_iff_all _).mp zero
  have accepted : (chainView bits ys).all tripleValue = true := by
    simpa only [List.all_map, Function.comp_def, id_eq] using all
  have impossible := chainView_sound bits ys size accepted
  rw [failed] at impossible
  contradiction

theorem flatMap_pair_length {α β : Type*} (xs : List α) (f g : α → β) :
    (xs.flatMap (fun x => [f x, g x])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem ofFn_getElem_of_length {α : Type*} (xs : List α) (n : Nat) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs[i.val]'(by rw [h]; exact i.isLt)) = xs := by
  subst n
  exact List.ofFn_getElem

theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β) (k : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := lengths x (by simp)
    have ht := ih (fun y hy => lengths y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hx, ht,
      Nat.add_mul, Nat.one_mul]
    omega

theorem count_false_map_sum {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.map (fun x => if f x then 0 else 1)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem nat_sum_map_le {α : Type*} (xs : List α) (f g : α → Nat)
    (bound : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (bound x (by simp)) (ih (fun y hy => bound y (by simp [hy])))

theorem twelve_query_factor : 2 ^ 12 * (12 - 2) = 40960 := by decide

end UniqueGames.Foundations.PCP.VerifierToCNF

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_FinalBooleanVerifier
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.PCP.FinalBooleanVerifier

variable {V E : Type*} {n m : Nat}

theorem count_false_map_filter {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.filter (fun x => decide (f x = false))).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem count_false_finRange (f : Fin m → Bool) :
    ((List.finRange m).map f).count false =
      (Finset.univ.filter (fun e : Fin m => f e = false)).card := by
  classical
  calc
    _ = ((List.finRange m).filter (fun e => decide (f e = false))).length :=
      count_false_map_filter _ _
    _ = (((List.finRange m).filter (fun e => decide (f e = false))).toFinset).card :=
      (List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)).symm
    _ = _ := by
      congr 1
      ext e
      simp

theorem twelve_query_auxiliary_factor : 2 ^ 12 * (12 - 3) = 36864 := by decide

end UniqueGames.Foundations.PCP.FinalBooleanVerifier

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_Scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                      
section

namespace UniqueGames.Foundations.Repetition

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

@[simp] theorem logTwo_one : logTwo 1 = 0 := by simp [logTwo]

theorem logTwo_inv_le_of_half_pow_le {p : ℝ} (m : ℕ)
    (h : (1 / 2 : ℝ) ^ m ≤ p) : logTwo (1 / p) ≤ m := by
  have hp : 0 < p := (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m).trans_le h
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m) h
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [Real.log_pow, hhalf] at hlog
  unfold logTwo
  rw [one_div, Real.log_inv]
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  nlinarith

theorem contraction_step {v ell : ℝ} {n m : ℕ} {p next : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hm : 1 ≤ m) (hmn : m < n) (hp : 0 ≤ p)
    (hmono : next ≤ p)
    (hprev : p ≤ ((1 + v) / 2) ^ m)
    (hcut : 2700 * (m : ℝ) * ell ≤ (1 - v) ^ 2 * ((n : ℝ) - m))
    (hstep : next ≤ p * (v + 15 * Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)))) :
    next ≤ ((1 + v) / 2) ^ (m + 1) := by
  by_cases hsmall : p ≤ ((1 + v) / 2) ^ (m + 1)
  · exact hmono.trans hsmall
  have hq : (1 / 2 : ℝ) ≤ (1 + v) / 2 := by linarith
  have hhalf : (1 / 2 : ℝ) ^ (m + 1) ≤ p :=
    (pow_le_pow_left₀ (by norm_num) hq (m + 1)).trans (le_of_not_ge hsmall)
  have hlog := logTwo_inv_le_of_half_pow_le (m + 1) hhalf
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (n : ℝ) - m := by
    have hmnreal : (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  have hmell : (m : ℝ) ≤ (m : ℝ) * ell := by nlinarith
  have hbudget : (m : ℝ) * ell + logTwo (1 / p) ≤ 3 * (m : ℝ) * ell := by
    simp only [Nat.cast_add, Nat.cast_one] at hlog
    nlinarith
  have hsqrt : Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)) ≤ (1 - v) / 30 := by
    apply (Real.sqrt_le_left (by linarith : 0 ≤ (1 - v) / 30)).2
    apply (div_le_iff₀ hden).2
    nlinarith
  have hfactor : v + 15 * Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)) ≤ (1 + v) / 2 := by
    linarith
  calc
    next ≤ p * (v + 15 * Real.sqrt
        (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m))) := hstep
    _ ≤ p * ((1 + v) / 2) := mul_le_mul_of_nonneg_left hfactor hp
    _ ≤ ((1 + v) / 2) ^ m * ((1 + v) / 2) :=
      mul_le_mul_of_nonneg_right hprev (by linarith)
    _ = ((1 + v) / 2) ^ (m + 1) := (pow_succ _ _).symm

theorem cutoff_step {v ell : ℝ} {n m : ℕ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hm : (m : ℝ) < (n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) :
    2700 * (m : ℝ) * ell ≤ (1 - v) ^ 2 * ((n : ℝ) - m) := by
  have hell0 : 0 < ell := by linarith
  have hd : (1 - v) ^ 2 ≤ 1 := by nlinarith
  have hmul : (m : ℝ) * (2925 * ell) < (n : ℝ) * (1 - v) ^ 2 :=
    (lt_div_iff₀ (by positivity : 0 < 2925 * ell)).1 hm
  have hdell : (1 - v) ^ 2 ≤ 225 * ell := by linarith
  have hprod := mul_le_mul_of_nonneg_left hdell (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  nlinarith

theorem cutoff_le_length {v ell : ℝ} (n : ℕ)
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell) :
    (n : ℝ) * (1 - v) ^ 2 / (2925 * ell) ≤ n := by
  have hell0 : 0 < ell := by linarith
  apply (div_le_iff₀ (by positivity : 0 < 2925 * ell)).2
  have hd : (1 - v) ^ 2 ≤ 2925 * ell := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

def ScalarRecurrence (p : ℕ → ℝ) (n : ℕ) (v ell : ℝ) : Prop :=
  ∀ m, m < n → p (m + 1) ≤ p m * (v + 15 * Real.sqrt
    (((m : ℝ) * ell + logTwo (1 / p m)) / ((n : ℝ) - m)))

theorem decay_to_cutoff (p : ℕ → ℝ) (n : ℕ) {v ell : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hp0 : p 0 = 1) (hpnonneg : ∀ m, 0 ≤ p m)
    (hpmono : Antitone p) (hrec : ScalarRecurrence p n v ell) :
    p n ≤ ((1 + v) / 2) ^
      ((n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) := by
  let T : ℝ := (n : ℝ) * (1 - v) ^ 2 / (2925 * ell)
  let M : ℕ := Nat.ceil T
  have hMn : M ≤ n := Nat.ceil_le.mpr (cutoff_le_length n hv0 hv1 hell)
  have hind : ∀ m, m ≤ M → p m ≤ ((1 + v) / 2) ^ m := by
    intro m
    induction m with
    | zero => intro _; simp [hp0]
    | succ m ih =>
        intro hmM
        have hmM' : m < M := Nat.lt_of_succ_le hmM
        have hmn : m < n := hmM'.trans_le hMn
        have hprev := ih (Nat.le_of_lt hmM')
        by_cases hm0 : m = 0
        · subst m
          have hinit : p 1 ≤ v := by
            have hs := hrec 0 hmn
            simpa [hp0] using hs
          simpa using hinit.trans (by linarith : v ≤ (1 + v) / 2)
        · have hmT : (m : ℝ) < T := Nat.lt_ceil.mp hmM'
          exact contraction_step hv0 hv1 hell (Nat.one_le_iff_ne_zero.mpr hm0)
            hmn (hpnonneg m) (hpmono (Nat.le_succ m)) hprev
            (cutoff_step hv0 hv1 hell hmT) (hrec m hmn)
  have hq0 : 0 < (1 + v) / 2 := by linarith
  have hq1 : (1 + v) / 2 ≤ 1 := by linarith
  calc
    p n ≤ p M := hpmono hMn
    _ ≤ ((1 + v) / 2) ^ M := hind M le_rfl
    _ = ((1 + v) / 2) ^ (M : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ ((1 + v) / 2) ^ T :=
      Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (Nat.le_ceil T)

theorem block_contraction {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ((1 + v) / 2) ^ ((1 - v) ^ 2 / 2925 : ℝ) ≤
      1 - (1 - v) ^ 3 / 5850 := by
  have hd : (1 - v) ^ 2 ≤ 1 := by nlinarith
  have hb := rpow_one_add_le_one_add_mul_self
    (s := -(1 - v) / 2) (p := (1 - v) ^ 2 / 2925)
    (by linarith) (by positivity) (by nlinarith)
  have hbase : 1 + -(1 - v) / 2 = (1 + v) / 2 := by ring
  have hrhs : 1 + (1 - v) ^ 2 / 2925 * (-(1 - v) / 2) =
      1 - (1 - v) ^ 3 / 5850 := by ring
  rwa [hbase, hrhs] at hb

theorem scalar_bound_6000 (p : ℕ → ℝ) (n : ℕ) {v ell : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hp0 : p 0 = 1) (hpnonneg : ∀ m, 0 ≤ p m)
    (hpmono : Antitone p) (hrec : ScalarRecurrence p n v ell) :
    p n ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / ell) := by
  have hell0 : 0 < ell := by linarith
  have hq0 : 0 ≤ (1 + v) / 2 := by linarith
  have hexp : 0 ≤ (n : ℝ) / ell := by positivity
  have hblock := block_contraction hv0 hv1
  have hweak : 1 - (1 - v) ^ 3 / 5850 ≤ 1 - (1 - v) ^ 3 / 6000 := by
    have : 0 ≤ (1 - v) ^ 3 := by positivity
    nlinarith
  calc
    p n ≤ ((1 + v) / 2) ^
        ((n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) :=
      decay_to_cutoff p n hv0 hv1 hell hp0 hpnonneg hpmono hrec
    _ = (((1 + v) / 2) ^ ((1 - v) ^ 2 / 2925 : ℝ)) ^ ((n : ℝ) / ell) := by
      rw [← Real.rpow_mul hq0]
      congr 1
      ring
    _ ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / ell) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hq0 _) (hblock.trans hweak) hexp

end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_Reveal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                      
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealEndpoint (q : X × Y) (side : Bool) : X ⊕ Y :=
  if side then Sum.inr q.2 else Sum.inl q.1

end
end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_MaskedVariation
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                               
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

def maskedJoint (p : S × (X × Y) → ℝ) : (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  (if z.1.2 = Sum.inl z.2.1 then p (z.1.1, z.2) / 2 else 0) +
  (if z.1.2 = Sum.inr z.2.2 then p (z.1.1, z.2) / 2 else 0)

theorem sum_maskedJoint (p : S × (X × Y) → ℝ) :
    (∑ z, maskedJoint p z) = ∑ z, p z := by
  classical
  have hrow (s : S) (q : X × Y) :
      (∑ r : X ⊕ Y, maskedJoint p ((s,r),q)) = p (s,q) := by
    simp [maskedJoint]
  calc
    _ = ∑ s : S, ∑ r : X ⊕ Y, ∑ q : X × Y, maskedJoint p ((s,r),q) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ s : S, ∑ q : X × Y, p (s,q) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      simp_rw [hrow]
    _ = _ := (Fintype.sum_prod_type _).symm

theorem maskedJoint_isProbability_iff (p : S × (X × Y) → ℝ) :
    Information.IsProbability (maskedJoint p) ↔ Information.IsProbability p := by
  classical
  constructor
  · intro h
    constructor
    · intro z
      have hp := h.1 ((z.1,Sum.inl z.2.1),z.2)
      simp [maskedJoint] at hp
      linarith
    · rw [← sum_maskedJoint]
      exact h.2
  · intro h
    constructor
    · intro z
      have hp : 0 ≤ p (z.1.1,z.2) / 2 := div_nonneg (h.1 _) (by norm_num)
      dsimp [maskedJoint]
      split_ifs <;> linarith
    · rw [sum_maskedJoint]
      exact h.2

omit [Fintype S] in
theorem maskedJoint_firstMarginal_inl (p : S × (X × Y) → ℝ) (s : S) (x : X) :
    Information.firstMarginal (maskedJoint p) (s, Sum.inl x) =
      (∑ y, p (s, (x, y))) / 2 := by
  simp [Information.firstMarginal, maskedJoint, Fintype.sum_prod_type,
    div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

omit [Fintype S] in
theorem maskedJoint_firstMarginal_inr (p : S × (X × Y) → ℝ) (s : S) (y : Y) :
    Information.firstMarginal (maskedJoint p) (s, Sum.inr y) =
      (∑ x, p (s, (x, y))) / 2 := by
  simp [Information.firstMarginal, maskedJoint, Fintype.sum_prod_type,
    div_eq_mul_inv, Finset.sum_mul]

theorem abs_half_sub_half_mul (a b «c» : ℝ) :
    |a / 2 - b / 2 * «c»| = |a - b * «c»| / 2 := by
  rw [show a / 2 - b / 2 * «c» = (a - b * «c») / 2 by ring, abs_div]
  norm_num

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_PartialReveal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def mergeAt {R : Type*} (j : I) (a : R) (rest : {i : I // i ≠ j} → R) : I → R :=
  fun i => if h : i = j then a else rest ⟨i,h⟩

omit [Fintype I] in
@[simp] theorem mergeAt_self {R : Type*} (j : I) (a : R) (rest : {i : I // i ≠ j} → R) :
    mergeAt j a rest j = a := by simp [mergeAt]

omit [Fintype I] in
@[simp] theorem mergeAt_other {R : Type*} (j : I) (a : R)
    (rest : {i : I // i ≠ j} → R) (i : {i : I // i ≠ j}) :
    mergeAt j a rest i.1 = rest i := by simp [mergeAt, i.property]

def revealSplitEquiv (j : I) :
    ((T × (I → X ⊕ Y)) × (X × Y)) ≃
      (((T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y)) × (X × Y)) where
  toFun z := (((z.1.1, fun i => z.1.2 i.1), z.1.2 j), z.2)
  invFun z := ((z.1.1.1, mergeAt j z.1.2 z.1.1.2), z.2)
  left_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        by_cases h : i = j <;> simp [mergeAt, h]
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext i
          exact mergeAt_other j z.1.2 z.1.1.2 i
      · exact mergeAt_self j z.1.2 z.1.1.2
    · rfl

theorem totalVariation_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p q : B → ℝ) :
    Information.totalVariation (fun a => p (e a)) (fun a => q (e a)) =
      Information.totalVariation p q := by
  unfold Information.totalVariation
  congr 1
  exact e.sum_comp (fun b => |p b - q b|)

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                   
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

def mergeCoordinates {Ω : Type*} {n : Nat} (selected : Finset (Fin n))
    (fixed : selected → Ω) (remaining : {i : Fin n // i ∉ selected} → Ω) : Fin n → Ω :=
  fun i => if h : i ∈ selected then fixed ⟨i,h⟩ else remaining ⟨i,h⟩

def coordinateSplitEquiv {Ω : Type*} {n : Nat} (selected : Finset (Fin n)) :
    (Fin n → Ω) ≃ ((selected → Ω) × ({i : Fin n // i ∉ selected} → Ω)) where
  toFun x := (fun i => x i.1, fun i => x i.1)
  invFun x := mergeCoordinates selected x.1 x.2
  left_inv x := by funext i; simp [mergeCoordinates]
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp [mergeCoordinates, i.property]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

abbrev SelectedLabels (selected : Finset (Fin n)) :=
  (selected → A₁) × (selected → A₂)

def selectedQuestionTuple (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (Fin n → Q₁) × (Fin n → Q₂) :=
  (fun i => (mergeCoordinates selected fixed remaining i).1,
   fun i => (mergeCoordinates selected fixed remaining i).2)

abbrev SelectedInput (Q₁ Q₂ : Type*) {n : Nat} (selected : Finset (Fin n)) :=
  (selected → Q₁ × Q₂) × ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedObservationEquiv (selected : Finset (Fin n)) :
    ((SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      (Q₁ × Q₂)) ≃
    ((((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)) × (Q₁ × Q₂)) where
  toFun z := (((z.1.1.1,z.1.2),z.1.1.2),z.2)
  invFun z := (((z.1.1.1,z.1.2),z.1.1.2),z.2)
  left_inv _ := rfl
  right_inv _ := rfl

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_AlphabetBudget
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                              
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : ℕ}

theorem selectedLabels_card (selected : Finset (Fin n)) :
    Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) =
      (Fintype.card A₁ * Fintype.card A₂) ^ selected.card := by
  simp [SelectedLabels, Fintype.card_prod, mul_pow]

theorem unusedCoordinates_card (selected : Finset (Fin n)) :
    Fintype.card {i : Fin n // i ∉ selected} = n - selected.card := by
  classical
  simp

theorem unusedCoordinates_card_real (selected : Finset (Fin n)) :
    (Fintype.card {i : Fin n // i ∉ selected} : ℝ) = (n : ℝ) - selected.card := by
  have hs : selected.card ≤ n := by simpa using Finset.card_le_univ selected
  rw [unusedCoordinates_card, Nat.cast_sub hs]

theorem log_le_logTwo {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ logTwo x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo_le : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 ; norm_num
  unfold logTwo
  apply (le_div_iff₀ htwo).2
  simpa using mul_le_mul_of_nonneg_left htwo_le hlog

theorem selectedLabels_log_le [Nonempty A₁] [Nonempty A₂]
    (selected : Finset (Fin n)) (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) ≤
      (selected.card : ℝ) * ell := by
  have ha : (1 : ℝ) ≤ Fintype.card A₁ := by exact_mod_cast Fintype.card_pos (α := A₁)
  have hb : (1 : ℝ) ≤ Fintype.card A₂ := by exact_mod_cast Fintype.card_pos (α := A₂)
  have hab : (1 : ℝ) ≤ (Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ) := by nlinarith
  rw [selectedLabels_card, Nat.cast_pow, Nat.cast_mul, Real.log_pow]
  exact mul_le_mul_of_nonneg_left ((log_le_logTwo hab).trans hell) (Nat.cast_nonneg _)

theorem sqrt_budget_factor (a b : ℝ) (ha : 0 < a) :
    Real.sqrt (a * b) = a * Real.sqrt (b / a) := by
  have he : a * b = a ^ 2 * (b / a) := by
    field_simp
  rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq (le_of_lt ha)]

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_Factorization
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators

noncomputable section

variable {ι α β : Type*} [Fintype ι] [DecidableEq α] [DecidableEq β]

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem productWeight_mass (left : X → ℝ) (right : Y → ℝ) :
    (∑ xy : X × Y, left xy.1 * right xy.2) =
      (∑ x, left x) * (∑ y, right y) := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

def normalizedWeight (weight : X → ℝ) : X → ℝ :=
  fun x => weight x / ∑ x', weight x'

theorem normalizedWeight_isProbability (weight : X → ℝ)
    (hweight : ∀ x, 0 ≤ weight x) (hmass : 0 < ∑ x, weight x) :
    (∀ x, 0 ≤ normalizedWeight weight x) ∧ (∑ x, normalizedWeight weight x) = 1 := by
  constructor
  · intro x
    exact div_nonneg (hweight x) hmass.le
  · simp only [normalizedWeight, div_eq_mul_inv, ← Finset.sum_mul, mul_inv_cancel₀ hmass.ne']

end

end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedCommon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                              
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem isProbability_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → ℝ) (hp : IsProbability p) :
    IsProbability (fun a => p (e a)) := by
  constructor
  · intro a
    exact hp.1 _
  · rw [e.sum_comp]
    exact hp.2

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

abbrev SelectedCommonData (selected : Finset (Fin n))
    (j : {i : Fin n // i ∉ selected}) :=
  ((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
    ({i : {i : Fin n // i ∉ selected} // i ≠ j} → Q₁ ⊕ Q₂)

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedLikelihood
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                  
section

namespace UniqueGames.Foundations.Repetition
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLocalAnswers {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q)
    (remaining : {i : Fin n // i ∉ selected} → Q) : selected → A :=
  fun i => strategy (mergeCoordinates selected fixed remaining) i.1

def selectedLocalTest {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q) (label : selected → A)
    (remaining : {i : Fin n // i ∉ selected} → Q) : ℝ := by
  classical
  exact if selectedLocalAnswers strategy selected fixed remaining = label then 1 else 0

theorem selectedLocalTest_nonnegative {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q) (label : selected → A)
    (remaining : {i : Fin n // i ∉ selected} → Q) :
    0 ≤ selectedLocalTest strategy selected fixed label remaining := by
  classical
  unfold selectedLocalTest
  split <;> norm_num

omit [Fintype Q₁] [Fintype Q₂] [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionTuple_left (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂) (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (selectedQuestionTuple selected fixed remaining).1 =
      mergeCoordinates selected (fun i => (fixed i).1) (fun i => (remaining i).1) := by
  funext i
  simp only [selectedQuestionTuple, mergeCoordinates]
  split <;> rfl

omit [Fintype Q₁] [Fintype Q₂] [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionTuple_right (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂) (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (selectedQuestionTuple selected fixed remaining).2 =
      mergeCoordinates selected (fun i => (fixed i).2) (fun i => (remaining i).2) := by
  funext i
  simp only [selectedQuestionTuple, mergeCoordinates]
  split <;> rfl

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                  
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

section LocalNormalization

variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y]

def completionTupleEquiv : (I → X × Y) ≃ ((I → X) × (I → Y)) where
  toFun u := (fun i => (u i).1, fun i => (u i).2)
  invFun z := fun i => (z.1 i, z.2 i)
  left_inv u := by funext i; rfl
  right_inv z := by cases z; rfl

end LocalNormalization

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedCommonMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                      
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Games Information
noncomputable section

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealDataSplitEquiv (j : I) :
    (T × (I → X ⊕ Y)) ≃ ((T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y)) where
  toFun z := ((z.1, fun i => z.2 i.1), z.2 j)
  invFun z := (z.1.1, mergeAt j z.2 z.1.2)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext i
      by_cases h : i = j <;> simp [mergeAt, h]
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        exact mergeAt_other j z.2 z.1.2 i
    · exact mergeAt_self j z.2 z.1.2

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedObservationDataEquiv (selected : Finset (Fin n)) :
    (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ≃
      (((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
        ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)) where
  toFun z := ((z.1.1,z.2),z.1.2)
  invFun z := ((z.1.1,z.2),z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

end
end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_ProfileCorrection
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                 
section

namespace UniqueGames.Foundations.Repetition.ProfileCorrection
open scoped BigOperators
open UniqueGames.Foundations.Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

def seedQuestionMarginal (p : X × (S × Y) → ℝ) : X × S → ℝ :=
  firstMarginal (fun z : (X × S) × Y => p (z.1.1, (z.1.2, z.2)))

theorem seedQuestionMarginal_isProbability (p : X × (S × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (seedQuestionMarginal p) := by
  apply firstMarginal_isProbability
  constructor
  · intro z
    exact hp.1 _
  · have h := hp.2
    simp only [Fintype.sum_prod_type] at h ⊢
    exact h

omit [Fintype X] in
theorem seedQuestionMarginal_first (p : X × (S × Y) → ℝ) :
    firstMarginal (seedQuestionMarginal p) = firstMarginal p := by
  funext x
  simp only [seedQuestionMarginal, firstMarginal, Fintype.sum_prod_type]

theorem totalVariation_triangle {Ω : Type*} [Fintype Ω]
    (p «c» d : Ω → ℝ) :
    totalVariation p d ≤ totalVariation p «c» + totalVariation «c» d := by
  unfold totalVariation
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => abs_sub_le (p x) («c» x) (d x))
  rw [Finset.sum_add_distrib] at h
  linarith

end
end UniqueGames.Foundations.Repetition.ProfileCorrection
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_ProfileBounds
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem firstMarginal_totalVariation_le (r t : X × Y → ℝ) :
    totalVariation (firstMarginal r) (firstMarginal t) ≤ totalVariation r t := by
  unfold totalVariation firstMarginal
  simp_rw [← Finset.sum_sub_distrib]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => Finset.abs_sum_le_sum_abs (fun y : Y => r (x,y)-t (x,y)) Finset.univ)
  rw [Fintype.sum_prod_type]
  linarith

def leftCommonMarginal (p : S × (X × Y) → ℝ) : X × S → ℝ :=
  fun z => ∑ y, p (z.2,(z.1,y))

def leftCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : X → S → ℝ :=
  conditionalKernel (leftCommonMarginal p) fallback

def swapSeedLeft : (X × (S × Y)) ≃ (S × (X × Y)) where
  toFun z := (z.2.1,(z.1,z.2.2))
  invFun z := (z.2.1,(z.1,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem leftCommonMarginal_isProbability (p : S × (X × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (leftCommonMarginal p) := by
  exact ProfileCorrection.seedQuestionMarginal_isProbability
    (fun z => p (swapSeedLeft z)) (isProbability_comp_equiv swapSeedLeft p hp)

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_RightProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                  
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

def swapQuestionEndpoints : (S × (Y × X)) ≃ (S × (X × Y)) where
  toFun z := (z.1,(z.2.2,z.2.1))
  invFun z := (z.1,(z.2.2,z.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def rightCommonMarginal (p : S × (X × Y) → ℝ) : Y × S → ℝ :=
  fun z => ∑ x, p (z.2,(x,z.1))

def rightCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : Y → S → ℝ :=
  conditionalKernel (rightCommonMarginal p) fallback

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectionSequence
attribute [-instance] _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                 
section

namespace UniqueGames.Foundations.Repetition.SelectionSequence

theorem exists_unused {n : Nat} (S : Finset (Fin n)) (hcard : S.card < n) :
    ∃ j : Fin n, j ∉ S := by
  classical
  apply Classical.byContradiction
  intro h
  have hall : ∀ j : Fin n, j ∈ S := by
    intro j
    apply Classical.byContradiction
    intro hj
    exact h ⟨j, hj⟩
  have hfull : S = Finset.univ :=
    Finset.ext (fun j => iff_of_true (hall j) (Finset.mem_univ j))
  have hbad : n < n := by
    simpa only [hfull, Finset.card_univ, Fintype.card_fin] using hcard
  exact Nat.lt_irrefl n hbad

noncomputable def nextSet {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  if hs : S.card < n then insert (Classical.choose (witness S hs)) S else S

noncomputable def selectedSet {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) : Nat → Finset (Fin n)
  | 0 => ∅
  | m + 1 => nextSet Step witness (selectedSet Step witness m)

theorem selectedSet_card {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) (m : Nat) :
    (selectedSet Step witness m).card = min m n := by
  induction m with
  | zero => simp [selectedSet]
  | succ m ih =>
    by_cases hm : m < n
    · have hc : (selectedSet Step witness m).card = m := by
        simpa only [Nat.min_eq_left (Nat.le_of_lt hm)] using ih
      have hs : (selectedSet Step witness m).card < n := by
        simpa only [hc] using hm
      rw [selectedSet, nextSet, dite_eq_left hs,
        Finset.card_insert_of_notMem ((Classical.choose_spec (witness _ hs)).1),
        hc, Nat.min_eq_left (Nat.succ_le_of_lt hm)]
    · have hc : (selectedSet Step witness m).card = n := by
        simpa only [Nat.min_eq_right (Nat.le_of_not_gt hm)] using ih
      have hs : ¬(selectedSet Step witness m).card < n := by
        rw [hc]
        exact Nat.not_lt.mpr (Nat.le_refl n)
      rw [selectedSet, nextSet, dite_eq_right hs, hc,
        Nat.min_eq_right (Nat.le_trans (Nat.le_of_not_gt hm) (Nat.le_succ m))]

theorem selectedSet_subset_succ {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) (m : Nat) :
    selectedSet Step witness m ⊆ selectedSet Step witness (m + 1) := by
  change selectedSet Step witness m ⊆ nextSet Step witness (selectedSet Step witness m)
  unfold nextSet
  split
  · exact Finset.subset_insert _ _
  · exact le_rfl

theorem selectedSet_monotone {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) :
    Monotone (selectedSet Step witness) :=
  monotone_nat_of_le_succ (selectedSet_subset_succ Step witness)

theorem selectedSet_univ {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) :
    selectedSet Step witness n = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp [selectedSet_card]

theorem selectedSet_step {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j)
    (m : Nat) (hm : m < n) :
    ∃ j, j ∉ selectedSet Step witness m ∧
      selectedSet Step witness (m + 1) = insert j (selectedSet Step witness m) ∧
      Step (selectedSet Step witness m) j := by
  have hc : (selectedSet Step witness m).card = m := by
    rw [selectedSet_card, Nat.min_eq_left (Nat.le_of_lt hm)]
  have hs : (selectedSet Step witness m).card < n := by simpa only [hc] using hm
  let j := Classical.choose (witness (selectedSet Step witness m) hs)
  have hj := Classical.choose_spec (witness (selectedSet Step witness m) hs)
  refine ⟨j, hj.1, ?_, hj.2⟩
  simp only [selectedSet, nextSet, dite_eq_left hs, j]

def SetStep {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (S : Finset (Fin n)) (j : Fin n) : Prop :=
  P (insert j S) ≤ P S *
    (v + 15 * Real.sqrt (((S.card : ℝ) * ell + logTwo (1 / P S)) /
      ((n : ℝ) - S.card)))

theorem totalSetStep {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (hnonneg : ∀ S, 0 ≤ P S) (hanti : Antitone P)
    (hpositive : ∀ S, S.card < n → 0 < P S →
      ∃ j, j ∉ S ∧ SetStep P v ell S j) :
    ∀ S, S.card < n → ∃ j, j ∉ S ∧ SetStep P v ell S j := by
  intro S hcard
  by_cases hp : 0 < P S
  · exact hpositive S hcard hp
  · obtain ⟨j, hj⟩ := exists_unused S hcard
    have hz : P S = 0 := le_antisymm (le_of_not_gt hp) (hnonneg S)
    have hnext : P (insert j S) = 0 := le_antisymm
      ((hanti (Finset.subset_insert j S)).trans (le_of_eq hz)) (hnonneg (insert j S))
    refine ⟨j, hj, ?_⟩
    simpa only [SetStep, hnext, hz, zero_mul] using (le_refl (0 : ℝ))

theorem exists_scalar_sequence {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (hempty : P ∅ = 1) (hnonneg : ∀ S, 0 ≤ P S) (hanti : Antitone P)
    (hpositive : ∀ S, S.card < n → 0 < P S →
      ∃ j, j ∉ S ∧ SetStep P v ell S j) :
    ∃ p : Nat → ℝ, p 0 = 1 ∧ (∀ m, 0 ≤ p m) ∧ Antitone p ∧
      ScalarRecurrence p n v ell ∧ p n = P Finset.univ := by
  let witness := totalSetStep P v ell hnonneg hanti hpositive
  let sets := selectedSet (SetStep P v ell) witness
  let p := fun m => P (sets m)
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · change P (selectedSet (SetStep P v ell) witness 0) = 1
    simpa only [selectedSet] using hempty
  · intro m
    exact hnonneg (sets m)
  · intro i j hij
    exact hanti (selectedSet_monotone (SetStep P v ell) witness hij)
  · intro m hm
    obtain ⟨j, _, hnext, hbound⟩ :=
      selectedSet_step (SetStep P v ell) witness m hm
    have hc : (selectedSet (SetStep P v ell) witness m).card = m := by
      rw [selectedSet_card, Nat.min_eq_left (Nat.le_of_lt hm)]
    change P (selectedSet (SetStep P v ell) witness (m + 1)) ≤ _
    rw [hnext]
    simpa only [SetStep, hc] using hbound
  · change P (selectedSet (SetStep P v ell) witness n) = P Finset.univ
    rw [selectedSet_univ]

open UniqueGames.Foundations.Games

end UniqueGames.Foundations.Repetition.SelectionSequence

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_AmplificationIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                               
section

namespace UniqueGames.Foundations.PCP.AmplificationIteration

def run {X : Type*} (step : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => step (run step n x)

theorem min_double_min (u cap : ℝ) (hc : 0 ≤ cap) :
    min (2 * min u cap) cap = min (2 * u) cap := by
  by_cases hu : u ≤ cap
  · rw [min_eq_left hu]
  · have hcu : cap ≤ u := le_of_not_ge hu
    rw [min_eq_right hcu, min_eq_right (by linarith : cap ≤ 2 * cap),
      min_eq_right (by linarith : cap ≤ 2 * u)]

theorem run_gap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) :
    min (2 ^ n * gap x) cap ≤ gap (run step n x) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hm : min (2 * min (2 ^ n * gap x) cap) cap ≤
        min (2 * gap (run step n x)) cap :=
      min_le_min (mul_le_mul_of_nonneg_left ih (by norm_num)) le_rfl
    rw [min_double_min _ _ hc] at hm
    have h := hm.trans (amplifies (run step n x))
    simpa [run, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

theorem run_preserves {X : Type*} (step : X → X) (P : X → Prop)
    (preserves : ∀ x, P x → P (step x)) (n : Nat) (x : X) (hx : P x) :
    P (run step n x) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact preserves _ ih

theorem run_size {X : Type*} (step : X → X) (size : X → Nat) (C : Nat)
    (blowup : ∀ x, size (step x) ≤ C * size x) (n : Nat) (x : X) :
    size (run step n x) ≤ C ^ n * size x := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have h := (blowup (run step n x)).trans (Nat.mul_le_mul_left C ih)
    simpa [run, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

def rounds (n : Nat) : Nat := Nat.log2 n + 1

theorem rounds_large (n : Nat) : n < 2 ^ rounds n := by
  simpa [rounds, Nat.log2_eq_log_two] using
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)

theorem rounds_power_le {n : Nat} (hn : 0 < n) : 2 ^ rounds n ≤ 2 * n := by
  have h := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  simpa [rounds, Nat.log2_eq_log_two, pow_succ, Nat.mul_comm] using
    (Nat.mul_le_mul_right 2 h)

theorem blowup_rounds_le {C degree n : Nat} (hn : 0 < n) (hC : C ≤ 2 ^ degree) :
    C ^ rounds n ≤ (2 * n) ^ degree := by
  calc
    C ^ rounds n ≤ (2 ^ degree) ^ rounds n := Nat.pow_le_pow_left hC _
    _ = (2 ^ rounds n) ^ degree := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm degree (rounds n)]
    _ ≤ (2 * n) ^ degree := Nat.pow_le_pow_left (rounds_power_le hn) _

theorem run_reaches_cap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap) (hc1 : cap ≤ 1)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) (hg : 0 ≤ gap x) (hstart : 1 ≤ (n : ℝ) * gap x) :
    cap ≤ gap (run step (rounds n) x) := by
  have hp : (n : ℝ) ≤ (2 : ℝ) ^ rounds n := by
    exact_mod_cast (Nat.le_of_lt (rounds_large n))
  have hcap : cap ≤ (2 : ℝ) ^ rounds n * gap x :=
    hc1.trans (hstart.trans (mul_le_mul_of_nonneg_right hp hg))
  have h := run_gap step gap cap hc amplifies (rounds n) x
  rwa [min_eq_right hcap] at h

end UniqueGames.Foundations.PCP.AmplificationIteration
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Reduction_ReductionSound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.ClauseProjection
open UniqueGames.Foundations
noncomputable section

def repetitionAlphabetBudget : ℝ := max 1 (Repetition.logTwo 14)

theorem repetitionAlphabetBudget_pos : 0 < repetitionAlphabetBudget :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

end
end VertexCover.ClauseProjection


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_BinaryOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
namespace BinaryOutput
abbrev State := ℕ × List Bool
end BinaryOutput
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end


