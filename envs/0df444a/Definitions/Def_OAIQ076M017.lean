-- Prove2me | Definitions.Def_OAIQ076M017
-- name    : OAIQ076M017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:10:30.16411+00:00
-- url     : https://prove2.me/theorems/4a7dd5c6-cc8e-4363-89d4-fe36a378b18c
-- title:
--   Definitions bundle OAIQ076M017 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 113 declarations of OpenAI's Lean: 22 definitions, 4 inductive types or structures, 2 instances and 85 theorems. The definitions and types are `OAI.MinUncut.Inner.zeroProcessed`, `OAI.MinUncut.Outer.Active`, `OAI.MinUncut.Outer.BackgroundStatistic`, `OAI.MinUncut.Outer.FirstDirection`, `OAI.MinUncut.Outer.HintCoefficients`, `OAI.MinUncut.Outer.HintLists`, `OAI.MinUncut.Outer.HintLists.matches`, `OAI.MinUncut.Outer.HintLists.strategy`, `OAI.MinUncut.Outer.HintedStrategy`, `OAI.MinUncut.Outer.IndexedLists`, `OAI.MinUncut.Outer.IndexedLists.matches`, `OAI.MinUncut.Outer.LocalRows`, `OAI.MinUncut.Outer.LocalRows.atom`, `OAI.MinUncut.Outer.LocalRows.distance`, `OAI.MinUncut.Outer.coefficientVectors`, `OAI.MinUncut.Outer.firstHints`, `OAI.MinUncut.Outer.hintGenerator`, `OAI.MinUncut.Outer.hintTupleGenerator`, `OAI.MinUncut.Outer.hintedAcceptance`, `OAI.MinUncut.Outer.hintedWins`, `OAI.MinUncut.Outer.ordinaryAccepts`, `OAI.MinUncut.Outer.ordinaryGame`, `OAI.MinUncut.Outer.readBit`, `OAI.MinUncut.Outer.sampledEquations`, `OAI.MinUncut.Outer.secondHints`, `OAI.MinUncut.Outer.slotZero`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_CenteredPointCorrelationPower`, `MinUncut_Analysis_FaceCorrelation`, `MinUncut_Analysis_GaussianSliceContinuous`, `MinUncut_Analysis_HermiteComponent`, `MinUncut_Analysis_MaskHermite`, `MinUncut_Analysis_OddAtom`, `MinUncut_Analysis_SelectedProjectGaussianLocal`, `MinUncut_Estimates_AnalyticOuter`, `MinUncut_Estimates_Assembly`, `MinUncut_Estimates_Away`, `MinUncut_Estimates_CoefficientMoments`, `MinUncut_Estimates_ComparisonSoundness`, `MinUncut_Estimates_Density`, `MinUncut_Estimates_EraseAway`, `MinUncut_Estimates_ExpectResampleRow`, `MinUncut_Estimates_F2`, `MinUncut_Estimates_FaceUpdateSelf`, `MinUncut_Estimates_FourthTest`, `MinUncut_Estimates_IndexedLists`, `MinUncut_Estimates_InnerAssembly`, `MinUncut_Estimates_IntegralExpect`, `MinUncut_Estimates_ListDecoding`, `MinUncut_Estimates_OuterRemainder`, `MinUncut_Estimates_OuterSampling`, `MinUncut_Estimates_PointField`, `MinUncut_Estimates_Rest`, `MinUncut_Estimates_SelectedProject`, `MinUncut_Estimates_SelectedProjectSliceContinuous`, `MinUncut_Games_HintSections`, `MinUncut_Games_HintSimulation`, `MinUncut_Games_HintSoundness`, `MinUncut_Games_MaskRowKernel`, `MinUncut_Games_OuterQuestions`, `MinUncut_Games_Sampling`, `MinUncut_Machines_OuterAlphabets`, `MinUncut_PCP_SelectedInformation`, `MinUncut_PCP_SelectionSequence`.
--
--   **Imports.** It imports the bundles `OAIQ076M006`, `OAIQ076M007`, `OAIQ076M008` and `OAIQ076M009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M022`, `OAIQ076M023` and `OAIQ076M027`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ076M006
import Definitions.Def_OAIQ076M007
import Definitions.Def_OAIQ076M008
import Definitions.Def_OAIQ076M009

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_F2
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace MinUncut.Inner
open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {m n : ℕ}

variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

variable [Fintype A]

lemma gradient_abs_le (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : 0 < σ) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    |gradient f B σ η c x| ≤ Real.sqrt (n^m : ℕ) / σ := by
  let S : Point m n → ℝ := fun y => ∫ g : Point m n → ℝ,
    g y * tableSmooth f B η (c + σ • g) ∂gauss (Point m n)
  have hS : (∑ y, S y ^ 2) ≤ 1 :=
    GaussianSmoothing.gaussian_score_energy
      ((measurable_tableSmooth f B η).comp (by fun_prop))
      (fun _ => tableSmooth_abs_le f B η _)
  have hsx : S x ^ 2 ≤ 1 := le_trans
    (Finset.single_le_sum (fun y _ => sq_nonneg (S y)) (Finset.mem_univ x)) hS
  have hx : |S x| ≤ 1 := by nlinarith [sq_abs (S x), abs_nonneg (S x)]
  rw [gradient_score f B hσ.ne', abs_mul, abs_of_nonneg
    (div_nonneg (Real.sqrt_nonneg _) hσ.le)]
  simpa using mul_le_mul_of_nonneg_left hx
    (div_nonneg (Real.sqrt_nonneg (n^m : ℕ)) hσ.le)

end MinUncut.Inner

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Density
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
namespace MinUncut.OuterSmoothness

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]

lemma membership_probability [Nonempty ι] {k : ℕ} (hk : k ≤ Fintype.card ι) (i : ι) :
    (𝔼 H : FixedSets ι k, if i ∈ H.val then (1 : ℝ) else 0) =
      (k : ℝ) / Fintype.card ι := by
  let : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
  have hsum : (∑ j : ι, 𝔼 H : FixedSets ι k, if j ∈ H.val then (1 : ℝ) else 0) = k := by
    rw [← Finset.expect_sum_comm]
    have hx (H : FixedSets ι k) : (∑ j : ι, if j ∈ H.val then (1 : ℝ) else 0) = k := by
      simp [H.property]
    simp_rw [hx]
    exact Fintype.expect_const _
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  calc
    (𝔼 H : FixedSets ι k, if i ∈ H.val then (1 : ℝ) else 0) =
        (∑ j : ι, 𝔼 H : FixedSets ι k, if i ∈ H.val then (1 : ℝ) else 0) /
          Fintype.card ι := by simp [hc]
    _ = (∑ j : ι, 𝔼 H : FixedSets ι k, if j ∈ H.val then (1 : ℝ) else 0) /
          Fintype.card ι := by
      congr 1
      exact Finset.sum_congr rfl (fun j _ => membership_probability_eq i j)
    _ = _ := by rw [hsum]

end MinUncut.OuterSmoothness

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_MaskRowKernel
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open BinaryFourier
open scoped BigOperators
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

omit [AddCommGroup W] [Module F₂ W] in
lemma maskRowKernel_symmetric (active : Bool) (b c : W) :
    maskRowKernel active b c = maskRowKernel active c b := by
  simp only [maskRowKernel, rowDensity_symmetric]

omit [Module F₂ W] in
lemma maskRowKernel_abs_mean (active : Bool) (b : W) :
    (𝔼 c, |maskRowKernel active b c|) ≤ if active then 2 else 1 := by
  cases active
  · simp [maskRowKernel]
  · dsimp only [maskRowKernel]
    calc
      _ ≤ 𝔼 c, (rowDensity 0 b c+1) := by
        apply Finset.expect_le_expect
        intro c _
        exact (abs_sub _ _).trans (by rw [abs_of_nonneg (rowDensity_nonneg (by norm_num) (by norm_num) _ _), abs_one])
      _ = 2 := by rw [Finset.expect_add_distrib, rowDensity_mean]; norm_num

omit [AddCommGroup W] [Module F₂ W] in
lemma maskKernel_symmetric (S : Finset R) (B C : R → W) :
    maskKernel S B C = maskKernel S C B := by simp only [maskKernel, maskRowKernel_symmetric]

omit [Module F₂ W] in
lemma maskKernel_abs_mean (S : Finset R) (B : R → W) :
    (𝔼 C, |maskKernel S B C|) ≤ (2 : ℝ)^Fintype.card R := by
  simp only [maskKernel, Finset.abs_prod]
  rw [expect_prod (f := fun r (c : W) => |maskRowKernel (decide (r ∈ S)) (B r) c|)]
  calc
    _ ≤ ∏ r : R, (2:ℝ) := by
      apply Finset.prod_le_prod
      · intro r _; exact Finset.expect_nonneg (fun _ _ => abs_nonneg _)
      · intro r _
        exact (maskRowKernel_abs_mean _ _).trans (by split_ifs <;> norm_num)
    _ = _ := by simp

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Rest
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open BinaryFourier
open scoped BigOperators
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

lemma rowCoefficient_maskProject (r : R) (S : Finset R) (f : (R → W) → ℝ)
    (α : Module.Dual F₂ W) (hα : α ≠ 0) (D : Rest (W := W) r) :
    rowCoefficient r (maskProject S f) α D =
      if r∈S then maskProject (restMask r S) (rowCoefficient r f α) D else 0 := by
  unfold rowCoefficient maskProject
  simp_rw [expect_splitRow r, maskKernel_split, Finset.expect_mul]
  rw [Finset.expect_comm]
  have hc (c : W) : (𝔼 b, 𝔼 E : Rest (W := W) r,
      maskRowKernel (decide (r∈S)) b c * maskKernel (restMask r S) D E *
      f (joinRow r c E) * character α b) =
      𝔼 E : Rest (W := W) r, 𝔼 b,
      maskRowKernel (decide (r∈S)) b c * maskKernel (restMask r S) D E *
      f (joinRow r c E) * character α b := by rw [Finset.expect_comm]
  simp_rw [hc]
  simp_rw [show ∀ b c, maskRowKernel (decide (r∈S)) b c =
      maskRowKernel (decide (r∈S)) c b from fun b c => maskRowKernel_symmetric _ _ _]
  simp_rw [show ∀ b c (E : Rest (W := W) r),
      maskRowKernel (decide (r∈S)) c b * maskKernel (restMask r S) D E *
        f (joinRow r c E) * character α b =
      maskKernel (restMask r S) D E * f (joinRow r c E) *
        (maskRowKernel (decide (r∈S)) c b * character α b) from fun _ _ _ => by ring]
  simp_rw [← Finset.mul_expect, maskRowKernel_character]
  have hdec : decide (α≠0)=true := by simp [hα]
  by_cases hs : r∈S
  · simp only [hs, hdec, decide_true, ↓reduceIte]
    rw [Finset.expect_comm]
    simp_rw [mul_assoc, ← Finset.mul_expect]
  · simp [hs, hα]

lemma rowCoefficient_maskProject_envelope (r : R) (S : Finset R)
    (f : (R → W) → ℝ) (a : Rest (W := W) r → ℝ)
    (ha : ∀ D, 0 ≤ a D) (α : Module.Dual F₂ W) (hα : α≠0)
    (h : ∀ D, |rowCoefficient r f α D| ≤ a D) (D : Rest (W := W) r) :
    |rowCoefficient r (maskProject S f) α D| ≤
      𝔼 E, |maskKernel (restMask r S) D E| * a E := by
  rw [rowCoefficient_maskProject _ _ _ _ hα]
  split_ifs with hs
  · calc
      _ ≤ 𝔼 E, |maskKernel (restMask r S) D E| * |rowCoefficient r f α E| := by
        simpa only [maskProject, abs_mul] using
          Finset.abs_expect_le Finset.univ (fun E => maskKernel (restMask r S) D E * rowCoefficient r f α E)
      _ ≤ _ := Finset.expect_le_expect (fun E _ => mul_le_mul_of_nonneg_left (h E) (abs_nonneg _))
  · simpa only [abs_zero] using Finset.expect_nonneg (fun E _ => mul_nonneg (abs_nonneg _) (ha E))

omit [Module F₂ W] in
lemma rowEnvelope_mean (r : R) (S : Finset R) (a : Rest (W := W) r → ℝ)
    (ha : ∀ D, 0 ≤ a D) :
    (𝔼 D, 𝔼 E, |maskKernel (restMask r S) D E| * a E) ≤
      (2:ℝ)^Fintype.card R * (𝔼 E, a E) := by
  rw [Finset.expect_comm]
  simp only [maskKernel_symmetric]
  simp_rw [← Finset.expect_mul]
  calc
    _ ≤ 𝔼 E, ((2:ℝ)^Fintype.card {t : R // t≠r}) * a E := by
      exact Finset.expect_le_expect (fun E _ => mul_le_mul_of_nonneg_right (maskKernel_abs_mean _ E) (ha E))
    _ ≤ 𝔼 E, ((2:ℝ)^Fintype.card R) * a E := by
      apply Finset.expect_le_expect
      intro E _
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Fintype.card_subtype_le (fun t : R => t≠r))) (ha E)
    _ = _ := (Finset.mul_expect _ _ _).symm
end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_OddAtom
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open BinaryFourier
open scoped BigOperators
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

lemma oddAtom_maskProject (r : R) (one : W) (S : Finset R) (f : (R → W) → ℝ)
    (D : Rest (W := W) r) :
    oddAtom r one (maskProject S f) D ≤
      𝔼 E, |maskKernel (restMask r S) D E| * oddAtom r one f E := by
  apply oddAtom_le
  · exact Finset.expect_nonneg (fun E _ => mul_nonneg (abs_nonneg _) (oddAtom_nonneg _ _ _ _))
  intro α hα
  have hα0 : α≠0 := by intro he; simp [he] at hα
  exact rowCoefficient_maskProject_envelope r S f (oddAtom r one f)
    (oddAtom_nonneg _ _ _) α hα0 (rowCoefficient_le_oddAtom _ _ _ α hα) D

lemma oddAtom_maskProject_mean (r : R) (one : W) (S : Finset R) (f : (R → W) → ℝ) :
    (𝔼 D, oddAtom r one (maskProject S f) D) ≤
      (2:ℝ)^Fintype.card R * (𝔼 D, oddAtom r one f D) := by
  exact (Finset.expect_le_expect (fun D _ => oddAtom_maskProject r one S f D)).trans
    (rowEnvelope_mean r S (oddAtom r one f) (oddAtom_nonneg _ _ _))

omit [Fintype R] [DecidableEq W] in
lemma oddAtom_sum {T : Type*} (s : Finset T) (r : R) (one : W)
    (f : T → (R → W) → ℝ) (D : Rest (W := W) r) :
    oddAtom r one (fun B => ∑ t∈s, f t B) D ≤ ∑ t∈s, oddAtom r one (f t) D := by
  apply oddAtom_le
  · exact Finset.sum_nonneg (fun _ _ => oddAtom_nonneg _ _ _ _)
  intro α hα
  simp only [rowCoefficient, Finset.sum_mul, Finset.expect_sum_comm]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun t _ =>
    rowCoefficient_le_oddAtom r one (f t) α hα D))
end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_IntegralExpect
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.GaussianHermite
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma psi_l1 (I : ι → ℕ) : (∫ x, |psi I x| ∂γpi ι) ≤ 1 := by
  have h := integral_norm_mul_le_sqrt (memLp_psi I)
    (memLp_const (1:ℝ) (p:=2) (μ:=γpi ι))
  have hn : (∫ x, psi I x^2 ∂γpi ι) = 1 := by simpa [sq] using psi_product I I
  simpa [hn] using h

end MinUncut.GaussianHermite

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_HermiteComponent
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [DecidableEq R] [Fintype W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

lemma rowCoefficient_hermiteComponent (r : R) (I : ι → ℕ)
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι))
    (α : Module.Dual F₂ W) (D : Rest (W := W) r) (c : ι → ℝ) :
    rowCoefficient r (fun B => hermiteComponent I u B c) α D =
      psi I c * GaussianHermite.coeff (fun c' => rowCoefficient r (fun B => u B c') α D) I := by
  simp only [rowCoefficient, hermiteComponent, GaussianHermite.coeff, mul_assoc, ← Finset.mul_expect]
  congr 1
  simp_rw [← integral_mul_const]
  rw [← integral_expect]
  · congr 1
    funext c'
    simp only [mul_assoc, ← Finset.mul_expect]
  · intro b
    exact ((memLp_psi I).integrable_mul (hu (joinRow r b D))).mul_const _

lemma oddAtom_hermiteComponent (r : R) (one : W) (I : ι → ℕ)
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι))
    (D : Rest (W := W) r) (c : ι → ℝ) :
    oddAtom r one (fun B => hermiteComponent I u B c) D ≤
      |psi I c| * ∫ c', |psi I c'| * oddAtom r one (fun B => u B c') D ∂γpi ι := by
  apply oddAtom_le
  · exact mul_nonneg (abs_nonneg _) (integral_nonneg (fun _ => mul_nonneg (abs_nonneg _) (oddAtom_nonneg _ _ _ _)))
  intro α hα
  rw [rowCoefficient_hermiteComponent r I u hu, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    _ ≤ ∫ c', |psi I c' * rowCoefficient r (fun B => u B c') α D| ∂γpi ι := abs_integral_le_integral_abs
    _ ≤ _ := by
      apply integral_mono
      · exact ((memLp_psi I).integrable_mul (memLp_rowCoefficient r u hu α D)).abs
      · exact (memLp_psi I).norm.integrable_mul (memLp_oddAtom r one u hu D)
      · intro c'
        dsimp only
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (rowCoefficient_le_oddAtom _ _ _ α hα _) (abs_nonneg _)

lemma oddAtom_hermiteComponent_mean (r : R) (one : W) (I : ι → ℕ)
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι))
    (D : Rest (W := W) r) :
    (∫ c, oddAtom r one (fun B => hermiteComponent I u B c) D ∂γpi ι) ≤
      Real.sqrt (∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι) := by
  have ha := memLp_oddAtom r one u hu D
  have hh : ∀ B, MemLp (hermiteComponent I u B) 2 (γpi ι) := fun B =>
    (memLp_psi I).mul_const _
  have hc : 0 ≤ ∫ c', |psi I c'| * oddAtom r one (fun B => u B c') D ∂γpi ι :=
    integral_nonneg (fun c' => mul_nonneg (abs_nonneg _) (oddAtom_nonneg _ _ _ _))
  calc
    _ ≤ ∫ c, |psi I c| * ∫ c', |psi I c'| * oddAtom r one (fun B => u B c') D ∂γpi ι ∂γpi ι := by
      exact integral_mono ((memLp_oddAtom r one (hermiteComponent I u) hh D).integrable (by norm_num))
        (((memLp_psi I).integrable (by norm_num)).norm.mul_const _)
        (oddAtom_hermiteComponent r one I u hu D)
    _ = (∫ c, |psi I c| ∂γpi ι) * ∫ c', |psi I c'| * oddAtom r one (fun B => u B c') D ∂γpi ι := integral_mul_const _ _
    _ ≤ ∫ c', |psi I c'| * oddAtom r one (fun B => u B c') D ∂γpi ι := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (psi_l1 I) hc
    _ ≤ _ := by
      have h := integral_norm_mul_le_sqrt (memLp_psi I) ha
      have hn : (∫ c, psi I c^2 ∂γpi ι)=1 := by simpa [sq] using psi_product I I
      simpa only [abs_of_nonneg (oddAtom_nonneg _ _ _ _), hn, Real.sqrt_one, one_mul] using h
end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_MaskHermite
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

lemma oddAtom_maskHermite_mean (r : R) (one : W) (S : Finset R) (I : ι → ℕ)
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    (𝔼 D, ∫ c, oddAtom r one (fun B => maskHermite S I u B c) D ∂γpi ι) ≤
      (2:ℝ)^Fintype.card R * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι) := by
  have hh : ∀ B, MemLp (hermiteComponent I u B) 2 (γpi ι) := fun B => (memLp_psi I).mul_const _
  have hi (D : Rest (W := W) r) := (memLp_oddAtom r one (maskHermite S I u)
    (memLp_maskHermite S I u) D).integrable (by norm_num)
  have hj (D : Rest (W := W) r) := (memLp_oddAtom r one (hermiteComponent I u) hh D).integrable (by norm_num)
  calc
    _ = ∫ c, (𝔼 D, oddAtom r one (fun B => maskHermite S I u B c) D) ∂γpi ι := (integral_expect _ hi).symm
    _ ≤ ∫ c, (2:ℝ)^Fintype.card R * (𝔼 D, oddAtom r one (fun B => hermiteComponent I u B c) D) ∂γpi ι := by
      apply integral_mono
      · simp only [Finset.expect_eq_sum_div_card]
        exact (integrable_finsetSum _ (fun D _ => hi D)).div_const _
      · simp only [Finset.expect_eq_sum_div_card]
        exact ((integrable_finsetSum _ (fun D _ => hj D)).div_const _).const_mul _
      · intro c
        exact oddAtom_maskProject_mean r one S (fun B => hermiteComponent I u B c)
    _ = (2:ℝ)^Fintype.card R * (𝔼 D, ∫ c, oddAtom r one (fun B => hermiteComponent I u B c) D ∂γpi ι) := by
      rw [integral_const_mul, integral_expect _ hj]
    _ ≤ (2:ℝ)^Fintype.card R * (𝔼 D, Real.sqrt (∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι)) := by
      exact mul_le_mul_of_nonneg_left (Finset.expect_le_expect (fun D _ =>
        oddAtom_hermiteComponent_mean r one I u hu D)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (expect_sqrt_le _ (fun _ => integral_nonneg (fun _ => sq_nonneg _))) (by positivity)
end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SelectedProject
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

lemma selectedProject_atom_mean (J : Finset (Finset R × (ι → ℕ))) (r : R) (one : W)
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    (𝔼 D, ∫ c, oddAtom r one (fun B => selectedProject J u B c) D ∂γpi ι) ≤
      J.card * (2:ℝ)^Fintype.card R * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι) := by
  have hi (D : Rest (W := W) r) := (memLp_oddAtom r one (selectedProject J u)
    (memLp_selectedProject J u) D).integrable (by norm_num)
  have hj (j : Finset R × (ι → ℕ)) (D : Rest (W := W) r) :=
    (memLp_oddAtom r one (maskHermite j.1 j.2 u) (memLp_maskHermite j.1 j.2 u) D).integrable (by norm_num)
  calc
    _ ≤ 𝔼 D, ∫ c, (∑ j ∈ J, oddAtom r one (fun B => maskHermite j.1 j.2 u B c) D) ∂γpi ι := by
      apply Finset.expect_le_expect
      intro D _
      exact integral_mono (hi D) (integrable_finsetSum _ (fun j _ => hj j D))
        (fun c => oddAtom_sum J r one (fun j B => maskHermite j.1 j.2 u B c) D)
    _ = ∑ j ∈ J, 𝔼 D, ∫ c, oddAtom r one (fun B => maskHermite j.1 j.2 u B c) D ∂γpi ι := by
      simp_rw [integral_finsetSum _ (fun j _ => hj j _), Finset.expect_sum_comm]
    _ ≤ ∑ _j ∈ J, (2:ℝ)^Fintype.card R * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι) :=
      Finset.sum_le_sum (fun j _ => oddAtom_maskHermite_mean r one j.1 j.2 u hu)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
end MinUncut.RowNoise
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Away
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Subbox
open scoped BigOperators
open OuterSmoothness
attribute [local instance] Classical.propDecidable
variable {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι]

lemma pointed_membership {x a : A} (ha : a ≠ x) {k : ℕ}
    (hk : k ≤ Fintype.card A-1) :
    (𝔼 H : FixedSets (Away x) k, if a ∈ pointedSet x H then (1:ℝ) else 0) =
      (k:ℝ)/(Fintype.card A-1) := by
  have : Nonempty (Away x) := ⟨⟨a,ha⟩⟩
  simp_rw [mem_pointedSet ha]
  rw [membership_probability (by simpa [card_away] using hk), card_away]
  have hc : 1 ≤ Fintype.card A := Fintype.card_pos_iff.mpr ⟨x⟩
  rw [Nat.cast_sub hc, Nat.cast_one]

lemma other_point_probability {x u : ι → A} (hu : u ≠ x) {k : ℕ}
    (hk : k ≤ Fintype.card A-1) :
    (𝔼 H : PointedBox x k, if InBox H u then (1:ℝ) else 0) ≤
      (k:ℝ)/(Fintype.card A-1) := by
  classical
  have (i : ι) : Nonempty (FixedSets (Away (x i)) k) :=
    fixedSets_nonempty (by simpa [card_away] using hk)
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
  calc
    _ ≤ 𝔼 H : PointedBox x k, if u i ∈ pointedSet (x i) (H i) then (1:ℝ) else 0 := by
      apply Finset.expect_le_expect
      intro H _
      by_cases h : InBox H u
      · simp [h, h i]
      · simp only [h, ite_false]; positivity
    _ = _ := by
      rw [expect_coordinate (B := fun i => FixedSets (Away (x i)) k) i (fun H : FixedSets (Away (x i)) k => if u i ∈ pointedSet (x i) H then (1:ℝ) else 0), pointed_membership hi hk]

lemma other_face_probability (i : ι) {x : ι → A} (u : {j : ι // j ≠ i} → A)
    (hu : u ≠ fun j : {j : ι // j ≠ i} => x j.val) {k : ℕ} (hk : k ≤ Fintype.card A-1) :
    (𝔼 H : PointedBox x k, if FaceInBox H i u then (1:ℝ) else 0) ≤
      (k:ℝ)/(Fintype.card A-1) := by
  classical
  have (j : ι) : Nonempty (FixedSets (Away (x j)) k) :=
    fixedSets_nonempty (by simpa [card_away] using hk)
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hu
  calc
    _ ≤ 𝔼 H : PointedBox x k, if u j ∈ pointedSet (x j.val) (H j.val) then (1:ℝ) else 0 := by
      apply Finset.expect_le_expect
      intro H _
      by_cases h : FaceInBox H i u
      · simp [h, h j]
      · simp only [h, ite_false]; positivity
    _ = _ := by
      rw [expect_coordinate (B := fun i => FixedSets (Away (x i)) k) j.val (fun H : FixedSets (Away (x j.val)) k => if u j ∈ pointedSet (x j.val) H then (1:ℝ) else 0), pointed_membership hj hk]

lemma removal_probability [Nonempty A] {x : ι → A} {k : ℕ} (hk : k ≤ Fintype.card A-1)
    (P : Finset (ι → A)) (S : Finset (Row ι A)) :
    (𝔼 H : PointedBox x k, if Removed H P S then (1:ℝ) else 0) ≤
      (P.card+S.card)*((k:ℝ)/(Fintype.card A-1)) := by
  classical
  have (j : ι) : Nonempty (FixedSets (Away (x j)) k) :=
    fixedSets_nonempty (by simpa [card_away] using hk)
  have hprob : 0 ≤ (k:ℝ)/(Fintype.card A-1) := by
    have hc : 1 ≤ Fintype.card A := Fintype.card_pos
    exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hc))
  have hp (u : ι → A) :
      (𝔼 H : PointedBox x k, if u ≠ x ∧ InBox H u then (1:ℝ) else 0) ≤
        (k:ℝ)/(Fintype.card A-1) := by
    by_cases hu : u=x
    · simp [hu]; exact hprob
    · simpa only [ne_eq, hu, not_false_eq_true, true_and] using other_point_probability hu hk
  have hs (r : Row ι A) :
      (𝔼 H : PointedBox x k, if r.2 ≠ (fun j => x j.val) ∧ FaceInBox H r.1 r.2 then (1:ℝ) else 0) ≤
        (k:ℝ)/(Fintype.card A-1) := by
    by_cases hr : r.2=(fun j => x j.val)
    · simp [hr]; exact hprob
    · simpa only [ne_eq, hr, not_false_eq_true, true_and] using other_face_probability r.1 r.2 hr hk
  calc
    _ ≤ (𝔼 H : PointedBox x k,
        ((∑ u ∈ P, if u ≠ x ∧ InBox H u then (1:ℝ) else 0) +
        (∑ r ∈ S, if r.2 ≠ (fun j => x j.val) ∧ FaceInBox H r.1 r.2 then (1:ℝ) else 0))) := by
      apply Finset.expect_le_expect
      intro H _
      have hp0 : 0 ≤ ∑ u ∈ P, if u ≠ x ∧ InBox H u then (1:ℝ) else 0 :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      have hs0 : 0 ≤ ∑ r ∈ S, if r.2 ≠ (fun j => x j.val) ∧ FaceInBox H r.1 r.2 then (1:ℝ) else 0 :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      by_cases hh : Removed H P S
      · rw [ite_eq_left hh]
        rcases hh with ⟨u,hu,hux,huH⟩ | ⟨r,hr,hrx,hrH⟩
        · have h := Finset.single_le_sum (s := P)
            (f := fun u => if u ≠ x ∧ InBox H u then (1:ℝ) else 0) (fun _ _ => by positivity) hu
          rw [ite_eq_left ⟨hux,huH⟩] at h
          exact h.trans (le_add_of_nonneg_right hs0)
        · have h := Finset.single_le_sum (s := S)
            (f := fun r => if r.2 ≠ (fun j => x j.val) ∧ FaceInBox H r.1 r.2 then (1:ℝ) else 0) (fun _ _ => by positivity) hr
          rw [ite_eq_left ⟨hrx,hrH⟩] at h
          exact h.trans (le_add_of_nonneg_left hp0)
      · rw [ite_eq_right hh]
        exact add_nonneg hp0 hs0
    _ = (∑ u ∈ P, 𝔼 H : PointedBox x k, if u ≠ x ∧ InBox H u then (1:ℝ) else 0) +
        (∑ r ∈ S, 𝔼 H : PointedBox x k, if r.2 ≠ (fun j => x j.val) ∧ FaceInBox H r.1 r.2 then (1:ℝ) else 0) := by
      rw [Finset.expect_add_distrib, Finset.expect_sum_comm, Finset.expect_sum_comm]
    _ ≤ (∑ _u ∈ P, (k:ℝ)/(Fintype.card A-1)) +
        (∑ _r ∈ S, (k:ℝ)/(Fintype.card A-1)) :=
      add_le_add (Finset.sum_le_sum (fun u _ => hp u)) (Finset.sum_le_sum (fun r _ => hs r))
    _ = _ := by simp; ring
end MinUncut.Subbox
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

omit [Fintype W] [DecidableEq W] in
lemma dual_local_sum (F : Finset R) (r s : R) (hrs : r ≠ s) (hr : r ∈ F) (hs : s ∈ F)
    (α : Module.Dual F₂ (R → W)) (hm : frequency α r=frequency α s)
    (hz : ∀ t ∈ F, t ≠ r → t ≠ s → frequency α t=0) (B C : R → W)
    (hBC : ∀ t ∉ F, B t=C t) :
    α B = α (zeroFree F C)+frequency α r (B r+B s) := by
  have he (t : R) : frequency α t (B t) = frequency α t (zeroFree F C t)+
      (if t=r then frequency α r (B r) else 0)+(if t=s then frequency α s (B s) else 0) := by
    by_cases htr : t=r
    · subst t; simp [zeroFree, hr, hrs]
    by_cases hts : t=s
    · subst t; simp [zeroFree, hs, hrs.symm]
    by_cases htF : t∈F
    · simp [hz t htF htr hts, htr, hts]
    · simp [zeroFree, htF, htr, hts, hBC t htF]
  calc
    α B = ∑ t, (frequency α t (zeroFree F C t)+
      (if t=r then frequency α r (B r) else 0)+(if t=s then frequency α s (B s) else 0)) := by
        rw [dual_apply]; exact Finset.sum_congr rfl (fun t _ => he t)
    _ = α (zeroFree F C)+frequency α r (B r)+frequency α s (B s) := by
      simp [Finset.sum_add_distrib, ← dual_apply]
    _ = _ := by rw [map_add, hm]; abel

omit [Fintype W] [DecidableEq W] in
lemma character_local_sum (F : Finset R) (r s : R) (hrs : r ≠ s) (hr : r ∈ F) (hs : s ∈ F)
    (α : Module.Dual F₂ (R → W)) (hm : frequency α r=frequency α s)
    (hz : ∀ t ∈ F, t ≠ r → t ≠ s → frequency α t=0) (B C : R → W)
    (hBC : ∀ t ∉ F, B t=C t) :
    character α B = character α (zeroFree F C)*character (frequency α r) (B r+B s) := by
  simp only [character, dual_local_sum F r s hrs hr hs α hm hz B C hBC, sign_add]

local instance awayRowNoiseDualFintype_ra56b7a_1 {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
lemma selectedProject_local_sum (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (F : Finset R) (r s : R)
    (hrs : r ≠ s) (hr : r ∈ F) (hs : s ∈ F)
    (hJ : ∀ j ∈ J, ∀ t ∈ j.1, t ∈ F → t=r ∨ t=s)
    (hm : ∀ j ∈ J, ∀ α : Module.Dual F₂ (R → W), mask α=j.1 →
      coefficient (fun B => coeff (u B) j.2) α ≠ 0 → frequency α r=frequency α s)
    (B C : R → W) (hBC : ∀ t ∉ F, B t=C t) (c : ι → ℝ) :
    selectedProject J u B c = localSlice J u F r C c (B r+B s) := by
  unfold localSlice selectedProject
  apply Finset.sum_congr rfl
  intro j hj
  simp only [maskHermite_eq, maskProject_expansion]
  congr 1
  apply Finset.sum_congr rfl
  intro α hα
  by_cases hmask : mask α=j.1
  swap
  · simp [hmask]
  rw [ite_eq_left hmask, ite_eq_left hmask]
  by_cases hc : coefficient (fun B => coeff (u B) j.2) α=0
  · simp [hc]
  have hz (t : R) (htF : t∈F) (htr : t≠r) (hts : t≠s) : frequency α t=0 := by
    by_contra ht
    have htm : t∈j.1 := by rw [← hmask]; simpa [mask] using ht
    exact (hJ j hj t htm htF).elim htr hts
  rw [character_local_sum F r s hrs hr hs α (hm j hj α hmask hc) hz B C hBC]
  simp only [character_add, character_single]

end MinUncut.RowNoise
namespace MinUncut.GaussianHermite
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma memLp_psi_update (I : ι → ℕ) (x : ι) (C : ι → ℝ) :
    MemLp (fun t => psi I (Function.update C x t)) 2 γ := by
  simpa only [psi_update] using (memLp_H (I x)).mul_const (∏ y ∈ Finset.univ.erase x, H (I y) (C y))

end MinUncut.GaussianHermite

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_FaceCorrelation
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.Inner
open scoped BigOperators

variable {m n : ℕ}

lemma faceCorrelation_add_le (v w : Point m n → ℝ) :
    faceCorrelation (v+w) ≤ faceCorrelation v + faceCorrelation w := by
  apply faceCorrelation_le
  intro z
  simp only [Pi.add_apply, add_mul, Finset.expect_add_distrib]
  exact (abs_add_le _ _).trans (add_le_add (code_correlation_le v z) (code_correlation_le w z))

lemma faceCorrelation_lipschitz (v w : Point m n → ℝ) :
    |faceCorrelation v-faceCorrelation w| ≤ 𝔼 x : Point m n, |v x-w x| := by
  apply abs_le.mpr
  have h₁ := faceCorrelation_add_le (v-w) w
  have h₂ := faceCorrelation_add_le (w-v) v
  have h₃ := faceCorrelation_le_l1 (v-w)
  have h₄ := faceCorrelation_le_l1 (w-v)
  simp only [sub_add_cancel] at h₁ h₂
  simp only [Pi.sub_apply] at h₃ h₄
  simp_rw [abs_sub_comm (w _)] at h₄
  constructor <;> linarith

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FaceUpdateSelf
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [DecidableEq ι]

lemma selectedProject_atom_mean_uniform (s : ℕ) (J : Finset (Finset R × (ι → ℕ)))
    (hJ : ∀ j ∈ J, GaussianHermite.degree j.2 ≤ s) (r : R) (one : W)
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    (𝔼 D, ∫ c, oddAtom r one (fun B => selectedProject J u B c) D ∂γpi ι) ≤
      (4:ℝ)^Fintype.card R * ((Fintype.card ι+s).choose s : ℝ) * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι) := by
  have hj : J ⊆ (Finset.univ : Finset (Finset R)) ×ˢ low s := by
    intro j hj
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, (mem_low _ _).mpr (hJ j hj)⟩
  have hc : J.card ≤ 2^Fintype.card R * (Fintype.card ι+s).choose s := by
    calc
      J.card ≤ ((Finset.univ : Finset (Finset R)) ×ˢ low s).card := Finset.card_le_card hj
      _ = 2^Fintype.card R * (low (ι := ι) s).card := by simp
      _ ≤ _ := Nat.mul_le_mul_left _ (card_low_le s)
  have hc' : (J.card : ℝ) ≤ (2:ℝ)^Fintype.card R * ((Fintype.card ι+s).choose s : ℝ) := by exact_mod_cast hc
  refine (selectedProject_atom_mean J r one u hu).trans ?_
  have hp : (2:ℝ)^Fintype.card R * (2:ℝ)^Fintype.card R = (4:ℝ)^Fintype.card R := by
    rw [← mul_pow]; norm_num
  calc
    _ ≤ ((2:ℝ)^Fintype.card R * ((Fintype.card ι+s).choose s : ℝ)) *
        (2:ℝ)^Fintype.card R * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom r one (fun B => u B c) D)^2 ∂γpi ι) := by
      gcongr
    _ = _ := by rw [mul_right_comm ((2:ℝ)^Fintype.card R), hp]
end MinUncut.RowNoise
namespace MinUncut.Slice
open BinaryFourier
variable {W : Type*} [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]

open BinaryFourier
variable {W : Type*} [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]

omit [DecidableEq W] in
lemma processed_mean_loss {H γ A : ℝ} (hH : 0 < H) (hA : 0 < A)
    (one : W) (f : W → ℝ) :
    (𝔼 w, |f w-processed H γ A one f w|) ≤
      (𝔼 w, (f w)^2)/H +
      (if γ < oddMax one f then Real.sqrt (𝔼 w, (f w)^2) else 0) +
      (𝔼 w, (f w)^2)/A := by
  have hE : 0 ≤ 𝔼 w, (f w)^2 := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  have hu : 0 ≤ (𝔼 w, (f w)^2)/H := div_nonneg hE hH.le
  have hv : 0 ≤ (𝔼 w, (f w)^2)/A := div_nonneg hE hA.le
  by_cases hn : H < Real.sqrt (𝔼 w, (f w)^2)
  · simp only [processed, hn, true_or, ↓reduceIte, sub_zero]
    have ht : Real.sqrt (𝔼 w, (f w)^2) ≤ (𝔼 w, (f w)^2)/H := by
      rw [le_div_iff₀ hH]
      have hh := mul_le_mul_of_nonneg_left hn.le (Real.sqrt_nonneg (𝔼 w, (f w)^2))
      nlinarith [Real.sq_sqrt hE]
    have hi : 0 ≤ if γ < oddMax one f then Real.sqrt (𝔼 w, (f w)^2) else 0 := by split_ifs <;> positivity
    linarith [mean_abs_le_sqrt f]
  · by_cases hq : γ < oddMax one f
    · simp only [processed, hq, or_true, ↓reduceIte, sub_zero]
      linarith [mean_abs_le_sqrt f]
    · simp only [processed, hn, hq, or_self, ↓reduceIte, add_zero]
      linarith [clip_mean_loss hA f]
end MinUncut.Slice

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_PointField
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

lemma centered_point_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (V : Point m n → ℝ → ℝ) (hcont : ∀ x, Continuous (V x)) {C : ℝ} (hC : 0≤C)
    (hV : ∀ x t, |V x t|≤C) (hmean : ∀ x, (∫ t, V x t ∂μ)=0) (hn : 0 < n) :
    (∫ c, Box.moment (pointField V c) ∂Measure.pi (fun _ : Point m n => μ)) ≤ C^(2^m)*((m:ℝ)/n) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [point_moment_integral μ V hcont hC hV]
  have hb (x y : Point m n) :
      (∫ c, ∏ ν : Fin m → Bool, pointField V c (Box.vertex ν x y) ∂Measure.pi (fun _ : Point m n => μ)) ≤
        C^(2^m)*(if ∃ i, x i=y i then (1:ℝ) else 0) := by
    by_cases hxy : ∃ i, x i=y i
    · simp only [ite_eq_left hxy,mul_one]
      calc
        _ ≤ ∫ _c : Point m n → ℝ, C^(2^m) ∂Measure.pi (fun _ : Point m n => μ) :=
          integral_mono (point_cube_integrable μ V hcont hC hV x y) (integrable_const _)
            (fun c => (le_abs_self _).trans (point_cube_abs V hC hV x y c))
        _ = _ := by simp
    · have hz := CubeRows.centered_point_cube_zero μ V (fun x => (hcont x).measurable) hmean x y
        (by simpa only [not_exists] using hxy)
      change _=0 at hz
      rw [show (∫ c, ∏ ν : Fin m → Bool, pointField V c (Box.vertex ν x y) ∂Measure.pi (fun _ : Point m n => μ))=0 from hz]
      simp only [ite_eq_right hxy,mul_zero,le_refl]
  calc
    _ ≤ 𝔼 x : Point m n, 𝔼 y : Point m n, C^(2^m)*(if ∃ i, x i=y i then (1:ℝ) else 0) :=
      Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun y _ => hb x y))
    _ = C^(2^m)*(𝔼 x : Point m n, 𝔼 y : Point m n, if ∃ i, x i=y i then (1:ℝ) else 0) := by
      simp only [← Finset.mul_expect]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC _)
      have collisionBound := CubeRows.collision_probability (ι := Fin m) (A := Fin n)
      simp only [Fintype.card_fin] at collisionBound
      convert collisionBound using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext point
      apply Finset.expect_congr rfl
      intro other _
      by_cases collision : ∃ index, point index = other index <;> simp [collision]
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_CenteredPointCorrelationPower
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {m n : ℕ}

theorem centered_point_correlation_power (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (V : Point m n → ℝ → ℝ) (hcont : ∀ x, Continuous (V x)) {C : ℝ} (hC : 0≤C)
    (hV : ∀ x t, |V x t|≤C) (hmean : ∀ x, (∫ t, V x t ∂μ)=0)
    (hm : 0 < m) (hn : 0 < n) :
    (∫ c, faceCorrelation (pointField V c) ∂Measure.pi (fun _ : Point m n => μ))^(2^m) ≤
      C^(2^m)*((m:ℝ)/n) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hb (c : Point m n → ℝ) : |faceCorrelation (pointField V c)|≤C := by
    rw [abs_of_nonneg (faceCorrelation_nonneg _)]
    exact (faceCorrelation_le_l1 _).trans ((Finset.expect_le_expect (fun x _ => hV x (c x))).trans_eq (Fintype.expect_const C))
  have hi : Integrable (fun c => faceCorrelation (pointField V c)^(2^m)) (Measure.pi (fun _ : Point m n => μ)) := by
    apply Box.bounded_integrable (C := C^(2^m)) ((point_correlation_continuous V hcont).pow _).aestronglyMeasurable
    intro c
    simp only [Pi.pow_apply, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb c) _
  have hmom : Integrable (fun c => Box.moment (pointField V c)) (Measure.pi (fun _ : Point m n => μ)) := by
    unfold Box.moment
    simp only [Finset.expect_eq_sum_div_card]
    apply Integrable.div_const
    apply integrable_finsetSum
    intro x _
    apply Integrable.div_const
    exact integrable_finsetSum _ (fun y _ => point_cube_integrable μ V hcont hC hV x y)
  calc
    _ ≤ ∫ c, faceCorrelation (pointField V c)^(2^m) ∂Measure.pi (fun _ : Point m n => μ) :=
      Box.integral_pow_bound (point_correlation_continuous V hcont).aestronglyMeasurable hb
        (fun c => faceCorrelation_nonneg _) _
    _ ≤ ∫ c, Box.moment (pointField V c) ∂Measure.pi (fun _ : Point m n => μ) :=
      integral_mono hi hmom (fun c => faceCorrelation_box_cs hm hn _)
    _ ≤ _ := centered_point_moment μ V hcont hC hV hmean hn
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_SelectedProjectGaussianLocal
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [DecidableEq ι]

omit [AddCommGroup W] [Module F₂ W] in
lemma selectedProject_gaussian_local (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (x : ι) (F : Finset ι)
    (hJ : ∀ j ∈ J, ∀ y ∈ F, y≠x → j.2 y=0) (B : R → W)
    (c C : ι → ℝ) (hC : ∀ y ∉ F, c y=C y) :
    selectedProject J u B c=selectedProject J u B (Function.update C x (c x)) := by
  unfold selectedProject
  apply Finset.sum_congr rfl
  intro j hj
  simp only [maskHermite_eq,psi_localized j.2 x F (hJ j hj) c C hC]

omit [AddCommGroup W] [Module F₂ W] in
lemma selectedProject_gaussian_memLp (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (x : ι) (B : R → W) (C : ι → ℝ) :
    MemLp (fun t => selectedProject J u B (Function.update C x t)) 2 γ := by
  unfold selectedProject
  apply memLp_finsetSum
  intro j _
  simp only [maskHermite_eq]
  exact (memLp_psi_update j.2 x C).mul_const _

end MinUncut.RowNoise
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma gaussianSlice_memLp (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (H : Subbox.PointedBox x k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (C : Point m n → ℝ) :
    MemLp (gaussianSlice f σ η x H J B C) 2 γ :=
  selectedProject_gaussian_memLp _ _ x B C

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SelectedProjectSliceContinuous
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.RowNoise
open MeasureTheory GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module BinaryFourier.F₂ W] [Fintype ι] [DecidableEq ι]
omit [AddCommGroup W] [Module BinaryFourier.F₂ W] in
lemma selectedProject_slice_continuous (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (B : R → W) (C : ι → ℝ) (x : ι) :
    Continuous (fun t => selectedProject J u B (Function.update C x t)) := by
  have hu : Continuous (fun t => Function.update C x t) := by
    apply continuous_pi
    intro y
    by_cases hy : y=x
    · subst y
      simp only [Function.update_self]
      exact continuous_id
    · simp only [Function.update_of_ne hy]
      exact continuous_const
  unfold selectedProject
  apply continuous_finsetSum
  intro j _
  simp only [maskHermite_eq]
  exact ((continuous_psi j.2).comp hu).mul_const _
end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianSliceContinuous
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma gaussianSlice_continuous (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : Subbox.PointedBox x k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (C : Point m n → ℝ) :
    Continuous (gaussianSlice f σ η x Y J B C) :=
  selectedProject_slice_continuous _ _ _ _ _

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FourthTest
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
attribute [local instance] Classical.propDecidable
attribute [local irreducible] query pullQuery
variable {V A V' A' : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A'] [Fintype A'] {m n : ℕ}

omit [Fintype A] [Fintype A'] in
lemma comparisonFailure_eq (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) :
    (coupledAnswer f B σ η c p-coupledAnswer g C σ η c p)^2 =
      4*comparisonFailure f g B C σ η c p := by
  unfold coupledAnswer comparisonFailure
  cases f.answer (pullQuery B (c+σ•p.1) (η•p.2)) <;>
    cases g.answer (pullQuery C (c+σ•p.1) (η•p.2)) <;> norm_num [bitSign]

omit [Fintype A] [Fintype A'] in
lemma comparisonFailure_indicator (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) :
    comparisonFailure f g B C σ η c p =
      (coupledAnswer f B σ η c p-coupledAnswer g C σ η c p)^2/4 := by
  have h := comparisonFailure_eq f g B C σ η c p
  linarith

lemma comparisonRejection_measurable (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ) :
    Measurable (comparisonRejection f g B C σ η) := by
  have hf : Measurable
      (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
        coupledAnswer f B σ η u.1 u.2) := by
    have hm : Measurable (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
        (u.1+σ•u.2.1,u.2.2)) := by fun_prop
    exact (measurable_answer f B η).comp hm
  have hg : Measurable
      (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
        coupledAnswer g C σ η u.1 u.2) := by
    have hm : Measurable (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
        (u.1+σ•u.2.1,u.2.2)) := by fun_prop
    exact (measurable_answer g C η).comp hm
  have hm : Measurable (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
      comparisonFailure f g B C σ η u.1 u.2) := by
    simp_rw [comparisonFailure_indicator]
    exact (hf.sub hg).pow_const 2 |>.div_const 4
  exact hm.stronglyMeasurable.integral_prod_right.measurable

end MinUncut.Inner

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_OuterAlphabets
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner

variable {Name : Type*}

instance alphabetFintype (E : Equation Name) : Fintype (alphabet E) := Fintype.ofFinite _

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_OuterQuestions
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I : Type*}

abbrev FirstDirection (U : I → Equation Name) := ∀ j, (alphabet (U j)).direction

open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

lemma slotFunctional_add (v : SecondQuestion Name) (β γ : F₂) (l k : Module.Dual F₂ Triple) :
    slotFunctional v (β+γ) (l+k)=slotFunctional v β l + slotFunctional v γ k := by
  cases v with
  | inl x => exact add_smul _ _ _
  | inr E => rfl

lemma slotFunctional_smul (v : SecondQuestion Name) (c β : F₂) (l : Module.Dual F₂ Triple) :
    slotFunctional v (c • β) (c • l)=c • slotFunctional v β l := by
  cases v with
  | inl x =>
    change (c*β) • (LinearMap.proj (0 : Fin 1) : Module.Dual F₂ (Fin 1 → F₂)) = _
    exact mul_smul _ _ _
  | inr E => rfl

lemma slotFunctional_project (E : Equation Name) (hidden : Bool) (p : Fin 3)
    (β : F₂) (l : Module.Dual F₂ Triple) (a : alphabet E) :
    slotFunctional (slotQuestion E hidden p) β l (slotProjection E hidden p a) =
      if hidden then β*a.val p else l a.val := by
  cases hidden <;> rfl

lemma pulledHint_apply (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (κ : F₂) (β : I → F₂) (l : I → Module.Dual F₂ Triple) (a : FirstAlphabet U) :
    formPullback (projection U hidden pos)
      (directHint (secondQuestion U hidden pos) κ β l) a =
      (∑ j, if hidden j then β j*(a j).val (pos j) else l j (a j).val)+κ := by
  change directHint (secondQuestion U hidden pos) κ β l (projection U hidden pos a)=_
  rw [directHint_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact slotFunctional_project (U j) (hidden j) (pos j) (β j) (l j) (a j)

lemma pulledHint_independent_active (U : I → Equation Name) (hidden : I → Bool)
    (pos pos' : I → Fin 3) (κ : F₂) (β : I → F₂) (l : I → Module.Dual F₂ Triple)
    (h : ∀ j, hidden j=true → pos j≠pos' j → β j=0) :
    formPullback (projection U hidden pos)
      (directHint (secondQuestion U hidden pos) κ β l) =
    formPullback (projection U hidden pos')
      (directHint (secondQuestion U hidden pos') κ β l) := by
  ext a
  rw [pulledHint_apply,pulledHint_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hh : hidden j=true
  · simp only [hh,↓reduceIte]
    by_cases hp : pos j=pos' j
    · rw [hp]
    · rw [h j hh hp]; simp
  · simp [hh]

def hintGenerator (V : I → SecondQuestion Name) :
    (F₂ × ((I → F₂) × (I → Module.Dual F₂ Triple))) →ₗ[F₂] Forms (SecondAlphabet V) where
  toFun c := directHint V c.1 c.2.1 c.2.2
  map_add' c d := by
    ext a
    change directHint V (c.1+d.1) (c.2.1+d.2.1) (c.2.2+d.2.2) a =
      directHint V c.1 c.2.1 c.2.2 a + directHint V d.1 d.2.1 d.2.2 a
    simp only [directHint_apply,Pi.add_apply,slotFunctional_add,LinearMap.add_apply,
      Finset.sum_add_distrib]
    abel
  map_smul' k c := by
    ext a
    change directHint V (k • c.1) (k • c.2.1) (k • c.2.2) a =
      k • (directHint V c.1 c.2.1 c.2.2 a)
    simp only [directHint_apply,Pi.smul_apply,slotFunctional_smul,LinearMap.smul_apply,
      ← Finset.smul_sum,← smul_add]

attribute [local instance] BinaryFourier.dualFintype

def hintTupleGenerator (V : I → SecondQuestion Name) (q : ℕ) :
    (Fin q → (F₂ × ((I → F₂) × (I → Module.Dual F₂ Triple)))) →ₗ[F₂]
      (Fin q → Forms (SecondAlphabet V)) :=
  LinearMap.pi (fun k => (hintGenerator V).comp (LinearMap.proj k))

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Sampling
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncutGames.Foundations.Games
attribute [local instance] Classical.propDecidable
variable {Name S : Type*}

instance equationFintype [Fintype Name] : Fintype (Equation Name) :=
  Fintype.ofEquiv ((Fin 3 → Name) × F₂)
    { toFun := fun x => ⟨x.1,x.2⟩
      invFun := fun E => (E.names,E.rhs)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def ordinaryAccepts (E : Equation Name) (x : Name) (a : Triple) (b : F₂) : Bool :=
  decide (Valid E a ∧ ∀ p, E.names p=x → a p=b)

variable [Fintype S] [Nonempty S]

variable [Fintype Name]

def ordinaryGame (equations : S → Equation Name) :
    Game (Equation Name) Name Triple F₂ where
  questions := (FiniteDistribution.uniform (S × Fin 3)).pushforward
    (fun ip => (equations ip.1,(equations ip.1).names ip.2))
  accepts := ordinaryAccepts

lemma ordinary_success_formula (equations : S → Equation Name)
    (strategy : Strategy (Equation Name) Name Triple F₂) :
    (ordinaryGame equations).success strategy =
      (∑ i, ∑ p : Fin 3,
        if ordinaryAccepts (equations i) ((equations i).names p)
          (strategy.1 (equations i)) (strategy.2 ((equations i).names p)) then
          (1 : ℝ) else 0) / ((Fintype.card S : ℝ)*3) := by
  unfold Game.success
  dsimp only [ordinaryGame]
  rw [FiniteDistribution.probability_pushforward]
  simp only [FiniteDistribution.probability,FiniteDistribution.uniform,Game.wins,
    Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_div,ite_div,zero_div]

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_HintSimulation
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

abbrev HintCoefficients (I : Type*) (q : ℕ) :=
  Fin q → (F₂ × ((I → F₂) × (I → Module.Dual F₂ Triple)))

def secondHints {q : ℕ} (V : I → SecondQuestion Name) (c : HintCoefficients I q) :
    Fin q → Forms (SecondAlphabet V) := fun k => hintGenerator V (c k)

def firstHints {q : ℕ} (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (c : HintCoefficients I q) : Fin q → Forms (FirstAlphabet U) :=
  fun k => formPullback (projection U hidden pos) (secondHints (secondQuestion U hidden pos) c k)

structure HintedStrategy (Name I : Type*) [Fintype I] (q : ℕ) where
  first : (U : I → Equation Name) → (Fin q → Forms (FirstAlphabet U)) → FirstAlphabet U
  second : (V : I → SecondQuestion Name) → (Fin q → Forms (SecondAlphabet V)) → SecondAlphabet V

def hintedWins {q : ℕ} (strategy : HintedStrategy Name I q)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (c : HintCoefficients I q) : Prop :=
  projection U hidden pos (strategy.first U (firstHints U hidden pos c)) =
    strategy.second (secondQuestion U hidden pos) (secondHints (secondQuestion U hidden pos) c)

def slotZero (v : SecondQuestion Name) : Fin (secondSlotCount v) :=
  ⟨0,by cases v <;> exact Nat.zero_lt_succ _⟩

def readBit (V : I → SecondQuestion Name) (a : SecondAlphabet V) (i : I) : F₂ :=
  a i (slotZero (V i))

omit [Fintype I] in
lemma projection_hidden_bit (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (a : FirstAlphabet U) (i : I) (hi : hidden i=true) :
    readBit (secondQuestion U hidden pos) (projection U hidden pos a) i=(a i).val (pos i) := by
  change (slotProjection (U i) (hidden i) (pos i) (a i))
    (slotZero (slotQuestion (U i) (hidden i) (pos i)))=_
  rw [hi]
  rfl

lemma firstHints_position_independent {q : ℕ} (U : I → Equation Name) (hidden : I → Bool)
    (pos pos' : I → Fin 3) (c : HintCoefficients I q)
    (h : ∀ k j, hidden j=true → pos j≠pos' j → (c k).2.1 j=0) :
    firstHints U hidden pos c=firstHints U hidden pos' c := by
  funext k
  exact pulledHint_independent_active U hidden pos pos' _ _ _ (h k)

omit [Fintype I] in

lemma secondQuestion_patch (A : I → Prop) (hidden : I → Bool)
    (hA : ∀ i, A i → hidden i=true) (bgU : I → Equation Name) (bgp : I → Fin 3)
    (U : {i // A i} → Equation Name) (p : {i // A i} → Fin 3) :
    secondQuestion (patch A bgU U) hidden (patch A bgp p) =
      patch A (secondQuestion bgU hidden bgp) (fun i => Sum.inl ((U i).names (p i))) := by
  funext i
  by_cases hi : A i
  · simp [patch,secondQuestion,slotQuestion,hA i hi,hi]
  · simp [patch,secondQuestion,hi]

end MinUncut.Outer

namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

theorem active_simulation {q : ℕ} (strategy : HintedStrategy Name I q)
    (A : I → Prop) (hidden : I → Bool) (hA : ∀ i, A i → hidden i=true)
    (c : HintCoefficients I q) (hzero : ∀ k i, A i → (c k).2.1 i=0)
    (bgU : I → Equation Name) (bgp : I → Fin 3) :
    ∃ (a : ({i // A i} → Equation Name) → {i // A i} → Triple)
      (b : ({i // A i} → Name) → {i // A i} → F₂),
    ∀ (U : {i // A i} → Equation Name) (p : {i // A i} → Fin 3),
      hintedWins strategy (patch A bgU U) hidden (patch A bgp p) c →
      ∀ j, ordinaryAccepts (U j) ((U j).names (p j)) (a U j)
        (b (fun i => (U i).names (p i)) j)=true := by
  classical
  let p₀ : I → Fin 3 := patch A bgp (fun _ => 0)
  let first (U : {i // A i} → Equation Name) : FirstAlphabet (patch A bgU U) :=
    strategy.first (patch A bgU U) (firstHints (patch A bgU U) hidden p₀ c)
  let V (y : {i // A i} → Name) : I → SecondQuestion Name :=
    patch A (secondQuestion bgU hidden bgp) (fun i => Sum.inl (y i))
  let second (y : {i // A i} → Name) : SecondAlphabet (V y) :=
    strategy.second (V y) (secondHints (V y) c)
  let a := fun U (j : {i // A i}) => (first U j).val
  let b := fun y (j : {i // A i}) => readBit (V y) (second y) j
  refine ⟨a,b,?_⟩
  intro U p hwin j
  have hints : firstHints (patch A bgU U) hidden (patch A bgp p) c =
      firstHints (patch A bgU U) hidden p₀ c := by
    apply firstHints_position_independent
    intro k i _ hdiff
    apply hzero k i
    by_contra hi
    exact hdiff (by simp [p₀,patch,hi])
  have hv : secondQuestion (patch A bgU U) hidden (patch A bgp p) =
      V (fun i => (U i).names (p i)) := secondQuestion_patch A hidden hA bgU bgp U p
  unfold hintedWins at hwin
  rw [hints] at hwin
  have hb := congrArg (fun z =>
    readBit (secondQuestion (patch A bgU U) hidden (patch A bgp p)) z j) hwin
  rw [projection_hidden_bit _ _ _ _ _ (hA j j.property)] at hb
  have hcoord : a U j (p j)=b (fun i => (U i).names (p i)) j := by
    simp only [patch_active] at hb
    rw [hv] at hb
    exact hb
  have hvalid : Valid (U j) (a U j) := by
    have hv' : Valid (patch A bgU U j) (a U j) := (first U j).property
    simpa only [patch_active] using hv'
  apply decide_eq_true
  refine ⟨hvalid,?_⟩
  intro p' hp'
  exact (hvalid.2 p' (p j) hp').trans hcoord

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SelectedInformation
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

open scoped BigOperators
open Information

variable {α β : Type*} [Fintype α] [Fintype β]

open scoped BigOperators
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

theorem rightRevealModel_totalVariation_le (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    Information.totalVariation p (rightRevealModel μ p) ≤
      2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) := by
  rw [masked_totalVariation_identity]
  linarith [Information.totalVariation_nonneg p (leftRevealModel μ p)]

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SelectionSequence
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Outer
open MinUncut.Inner MinUncutGames.Foundations.Games MinUncutGames.Foundations.Repetition

lemma ordinary_alphabet_log :
    logTwo ((Fintype.card Triple : ℝ)*(Fintype.card F₂ : ℝ)) ≤ 4 := by
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hcard : (Fintype.card Triple : ℝ)*(Fintype.card F₂ : ℝ) = 2^4 := by
    norm_num [Triple,F₂,Fintype.card_fun]
  rw [hcard,logTwo,Real.log_pow]
  norm_num

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CoefficientMoments
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {I : Type*} [Fintype I]

def coefficientVectors (q : ℕ) : HintCoefficients I q →ₗ[F₂] (I → Fin q → F₂) where
  toFun c i k := (c k).2.1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype I] in
lemma coefficientVectors_surjective (q : ℕ) : Function.Surjective (coefficientVectors (I := I) q) := by
  intro v
  exact ⟨fun k => (0,(fun i => v i k,fun _ => 0)),rfl⟩

def Active {q : ℕ} (hidden : I → Bool) (v : I → Fin q → F₂) (i : I) : Prop :=
  hidden i=true ∧ v i=0

lemma active_power_product {q : ℕ} (hidden : I → Bool) (v : I → Fin q → F₂) (r : ℝ) :
    r ^ Fintype.card {i // Active hidden v i} =
      ∏ i, if hidden i=true ∧ v i=0 then r else 1 := by
  classical
  rw [Fintype.card_subtype (Active hidden v),← Finset.prod_const,Finset.prod_filter]
  simp only [Active]
  congr 1
  funext i
  split_ifs with h
  · exact ite_eq_left h
  · exact ite_eq_right h

lemma zero_vector_expect (q : ℕ) (r : ℝ) :
    (𝔼 v : Fin q → F₂, if v=0 then r else 1) = 1-(1/(2:ℝ)^q)*(1-r) := by
  classical
  have hpoint (v : Fin q → F₂) : (if v=0 then r else (1:ℝ)) =
      1+(r-1)*(if v=0 then 1 else 0) := by split_ifs <;> ring
  simp_rw [hpoint]
  rw [Finset.expect_add_distrib,← Finset.mul_expect,Fintype.expect_const]
  have hz : (𝔼 v : Fin q → F₂, if v=0 then (1:ℝ) else 0) = 1/(2:ℝ)^q := by
    simp [F₂]
  rw [hz]
  ring

lemma active_power_expect (q : ℕ) (hidden : I → Bool) :
    (𝔼 v : I → Fin q → F₂, repetitionRate ^ Fintype.card {i // Active hidden v i}) =
      hintRate q ^ Fintype.card {i // hidden i=true} := by
  classical
  simp_rw [active_power_product]
  rw [OuterSmoothness.expect_prod (fun i (v : Fin q → F₂) =>
    if hidden i=true ∧ v=0 then repetitionRate else 1)]
  have h j : (𝔼 v : Fin q → F₂,
      if hidden j=true ∧ v=0 then repetitionRate else 1) =
      if hidden j=true then hintRate q else 1 := by
    by_cases hj : hidden j=true
    · simp only [hj,true_and,↓reduceIte]
      exact zero_vector_expect q repetitionRate
    · simp [hj]
  simp_rw [h]
  rw [Fintype.card_subtype (fun i => hidden i=true),← Finset.prod_const,Finset.prod_filter]

lemma coefficient_active_expect (q : ℕ) (hidden : I → Bool) :
    (𝔼 c : HintCoefficients I q,
      repetitionRate ^ Fintype.card {i // Active hidden (coefficientVectors q c) i}) =
      hintRate q ^ Fintype.card {i // hidden i=true} := by
  exact (IndependentSquares.expect_surjective_linear (coefficientVectors q)
    (coefficientVectors_surjective q) (fun v =>
      repetitionRate ^ Fintype.card {i // Active hidden v i})).trans
    (active_power_expect q hidden)

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_OuterSampling
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncutGames.Foundations.Games
attribute [local instance] Classical.propDecidable
variable {Name S : Type*} [Fintype Name] [Fintype S] [Nonempty S]

lemma ordinary_repetition_formula (equations : S → Equation Name) (r : ℕ)
    (strategy : Strategy (Fin r → Equation Name) (Fin r → Name)
      (Fin r → Triple) (Fin r → F₂)) :
    ((ordinaryGame equations).repetition r).success strategy =
      𝔼 w : Fin r → S × Fin 3,
        if (∀ j, ordinaryAccepts (equations (w j).1)
          ((equations (w j).1).names (w j).2)
          (strategy.1 (fun i => equations (w i).1) j)
          (strategy.2 (fun i => (equations (w i).1).names (w i).2) j)=true)
        then (1 : ℝ) else 0 := by
  unfold Game.success
  change (((ordinaryGame equations).questions.iid r).transport
    (Game.tupleQuestionEquiv r)).probability _ = _
  rw [FiniteDistribution.probability_transport]
  change (((FiniteDistribution.uniform (S × Fin 3)).pushforward
    (fun ip => (equations ip.1,(equations ip.1).names ip.2))).iid r).probability _ = _
  rw [FiniteDistribution.iid_pushforward,FiniteDistribution.iid_uniform,
    FiniteDistribution.probability_pushforward]
  change (∑ w : Fin r → S × Fin 3,
    if decide (∀ j, ordinaryAccepts (equations (w j).1)
      ((equations (w j).1).names (w j).2)
      (strategy.1 (fun i => equations (w i).1) j)
      (strategy.2 (fun i => (equations (w i).1).names (w i).2) j)=true)
    then (1 : ℝ) / Fintype.card (Fin r → S × Fin 3) else 0) = _
  simp only [decide_eq_true_eq,Fintype.expect_eq_sum_div_card,Finset.sum_div,ite_div,zero_div]

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_HintSections
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I S : Type*} [Fintype Name] [Fintype I] [Fintype S] [Nonempty S]

def sampledEquations (equations : S → Equation Name) (w : I → S × Fin 3) : I → Equation Name :=
  fun j => equations (w j).1

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_HintSoundness
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I S : Type*} [Fintype Name] [Fintype I] [Fintype S] [Nonempty S]

def hintedAcceptance {q : ℕ} (strategy : HintedStrategy Name I q)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (L : Fin q → Forms (SecondAlphabet (secondQuestion U hidden pos))) : Prop :=
  projection U hidden pos
    (strategy.first U (fun k => formPullback (projection U hidden pos) (L k))) =
      strategy.second (secondQuestion U hidden pos) L

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ListDecoding
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

variable {Name I : Type*} [Fintype I]

structure HintLists (Name I : Type*) [Fintype I] (q : ℕ) where
  first : (U : I → Equation Name) → (Fin q → Forms (FirstAlphabet U)) → Finset (FirstAlphabet U)
  second : (V : I → SecondQuestion Name) → (Fin q → Forms (SecondAlphabet V)) → Finset (SecondAlphabet V)

def HintLists.strategy {q L R : ℕ} (lists : HintLists Name I q) (z : Fin L × Fin R) :
    HintedStrategy Name I q where
  first U B := paddedChoice (lists.first U B) z.1
  second V B := paddedChoice (lists.second V B) z.2

def HintLists.matches {q : ℕ} (lists : HintLists Name I q)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (B : Fin q → Forms (SecondAlphabet (secondQuestion U hidden pos))) : Prop :=
  ∃ a ∈ lists.first U (fun j => formPullback (projection U hidden pos) (B j)),
    ∃ b ∈ lists.second (secondQuestion U hidden pos) B, projection U hidden pos a=b

lemma HintLists.matching_le_sum {q L R : ℕ} (lists : HintLists Name I q)
    (hL : ∀ U B, (lists.first U B).card≤L)
    (hR : ∀ V B, (lists.second V B).card≤R)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (B : Fin q → Forms (SecondAlphabet (secondQuestion U hidden pos))) :
    (if lists.matches U hidden pos B then (1 : ℝ) else 0) ≤
      ∑ z : Fin L × Fin R, if hintedAcceptance (lists.strategy z) U hidden pos B then 1 else 0 := by
  classical
  by_cases hm : lists.matches U hidden pos B
  · rw [ite_eq_left hm]
    obtain ⟨a,ha,b,hb,hab⟩ := hm
    obtain ⟨i,hi⟩ := paddedChoice_covers _ (hL _ _) a ha
    obtain ⟨j,hj⟩ := paddedChoice_covers _ (hR _ _) b hb
    have hwin : hintedAcceptance (lists.strategy (i,j)) U hidden pos B := by
      change projection U hidden pos (paddedChoice _ i)=paddedChoice _ j
      rw [hi,hj]
      exact hab
    have hs := Finset.single_le_sum (s := Finset.univ) (f := fun z : Fin L × Fin R =>
      if hintedAcceptance (lists.strategy z) U hidden pos B then (1 : ℝ) else 0)
      (fun _ _ => by positivity) (Finset.mem_univ (i,j))
    simpa only [ite_eq_left hwin] using hs
  · rw [ite_eq_right hm]
    exact Finset.sum_nonneg (fun _ _ => by positivity)


open scoped BigOperators
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_IndexedLists
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

structure IndexedLists (Name I J : Type*) [Fintype I] where
  first : (U : I → Equation Name) → (J → Forms (FirstAlphabet U)) → Finset (FirstAlphabet U)
  second : (V : I → SecondQuestion Name) → (J → Forms (SecondAlphabet V)) → Finset (SecondAlphabet V)

variable {Name I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

def IndexedLists.matches (lists : IndexedLists Name I J)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (B : J → Forms (SecondAlphabet (secondQuestion U hidden pos))) : Prop :=
  ∃ a ∈ lists.first U (fun j => formPullback (projection U hidden pos) (B j)),
    ∃ b ∈ lists.second (secondQuestion U hidden pos) B, projection U hidden pos a=b

open scoped BigOperators
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

variable {Name I J S : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [Nonempty S]

open scoped BigOperators
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I J S : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [Nonempty S]

abbrev BackgroundStatistic (Name I J : Type*) [Fintype I] :=
  (U : I → Equation Name) → (hidden : I → Bool) → (pos : I → Fin 3) →
    (J → Forms (SecondAlphabet (secondQuestion U hidden pos))) → ℝ

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_OuterRemainder
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [DecidableEq J]


open scoped BigOperators
open MinUncut.Inner OuterSmoothness MinUncut.Composition
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

structure LocalRows (Name I J : Type*) [Fintype I] where
  first : (U : I → Equation Name) → (J → Forms (FirstAlphabet U)) → Forms (FirstAlphabet U) → ℝ
  second : (V : I → SecondQuestion Name) → (J → Forms (SecondAlphabet V)) → Forms (SecondAlphabet V) → ℝ

variable {Name I J S : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [Nonempty S]

def LocalRows.atom (rows : LocalRows Name I J) (θ : ℝ) : BackgroundStatistic Name I J :=
  fun U hidden pos B => if (labelList (rows.second (secondQuestion U hidden pos) B) θ).Nonempty
    then 1 else 0

def LocalRows.distance (rows : LocalRows Name I J) : BackgroundStatistic Name I J :=
  fun U hidden pos B => rowDistance (projection U hidden pos)
    (rows.first U (fun j => formPullback (projection U hidden pos) (B j)))
    (rows.second (secondQuestion U hidden pos) B)

end MinUncut.Outer

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_EraseAway
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Subbox
open OuterSmoothness
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι]

open OuterSmoothness
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

lemma pointwise_bayes {k : ℕ} (hk : k≤Fintype.card A-1) (f : (ι → A) → ℝ) :
    (𝔼 x : ι → A, f x) = 𝔼 Y : UnpointedBox ι A k, 𝔼 u : ι → Fin (k+1), f (pointEmbed Y u) := by
  have (x : ι → A) (i : ι) : Nonempty (FixedSets (Away (x i)) k) :=
    fixedSets_nonempty (by simpa only [card_away] using hk)
  have h := bayes_box (ι := ι) (A := A) k (fun _ x => f x)
  simp only [Fintype.expect_const] at h
  rw [h]
  apply Finset.expect_congr rfl
  intro Y _
  symm
  exact Fintype.expect_equiv (pointEnum Y) _ _ (fun u => rfl)
end MinUncut.Subbox

namespace MinUncut.Inner
open Subbox OuterSmoothness
open scoped BigOperators
variable {m n : ℕ}

theorem faceCorrelation_restriction {k : ℕ} (hk : k≤n-1) (v : Point m n → ℝ) :
    faceCorrelation v ≤ 𝔼 Y : UnpointedBox (Fin m) (Fin n) k,
      faceCorrelation (fun u : Point m (k+1) => v (pointEmbed Y u)) := by
  apply faceCorrelation_le
  intro z
  have he := pointwise_bayes (ι := Fin m) (A := Fin n) (by simpa using hk)
    (fun x => v x*BinaryFourier.sign (z.val x))
  rw [he]
  calc
    _ ≤ 𝔼 Y : UnpointedBox (Fin m) (Fin n) k,
      |𝔼 u, v (pointEmbed Y u)*BinaryFourier.sign (z.val (pointEmbed Y u))| :=
        Finset.abs_expect_le _ _
    _ ≤ _ := Finset.expect_le_expect (fun Y _ => code_correlation_le _ (codeRestriction Y z))
end MinUncut.Inner
namespace MinUncut.Slice
open MeasureTheory BinaryFourier
open scoped BigOperators
variable {W Ω : Type*} [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq W] in
lemma processed_memLp (one : W) (v : Ω → W → ℝ)
    (hm : ∀ w, Measurable (fun t => v t w)) {H γ A : ℝ} (hA : 0≤A) (w : W) :
    MemLp (fun t => processed H γ A one (v t) w) 2 μ := by
  exact MemLp.of_bound (processed_measurable one v hm H γ A w).aestronglyMeasurable A
    (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using processed_abs_le hA one (v t) w))

omit [DecidableEq W] in
theorem processed_integral_loss (one : W) (v : Ω → W → ℝ)
    (hm : ∀ w, Measurable (fun t => v t w)) (hv : ∀ w, MemLp (fun t => v t w) 2 μ)
    {H γ A : ℝ} (hH : 0<H) (hγ : 0<γ) (hA : 0<A) :
    (∫ t, (𝔼 w, |v t w-processed H γ A one (v t) w|) ∂μ) ≤
      (∫ t, energy v t ∂μ)/H +
      Real.sqrt (∫ t, energy v t ∂μ)*Real.sqrt ((∫ t, oddMax one (v t) ∂μ)/γ) +
      (∫ t, energy v t ∂μ)/A := by
  let S := {t : Ω | γ < oddMax one (v t)}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (oddMax_measurable one v hm)
  have he := energy_integrable v hv
  have hn := sliceNorm_memLp v hm hv
  have hq := oddMax_memLp one v hv
  have hi : Integrable (fun t => 𝔼 w, |v t w-processed H γ A one (v t) w|) μ := by
    simp only [Finset.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun w _ =>
      ((hv w).sub (processed_memLp one v hm hA.le w)).integrable (by norm_num) |>.abs)).div_const _
  have hvS : Integrable (S.indicator (fun t => Real.sqrt (energy v t))) μ :=
    (hn.integrable (by norm_num)).indicator hS
  have htail := integral_tail_loss hn (oddMax_measurable one v hm)
    (hq.integrable (by norm_num)) (fun t => oddMax_nonneg one (v t)) hγ
  simp only [abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (energy_nonneg v _)] at htail
  calc
    _ ≤ ∫ t, energy v t/H + S.indicator (fun t => Real.sqrt (energy v t)) t + energy v t/A ∂μ := by
      apply integral_mono hi (((he.div_const _).add hvS).add (he.div_const _))
      intro t
      simp only [Pi.add_apply]
      simpa only [energy,Set.indicator_apply,S,Set.mem_ofPred_eq] using processed_mean_loss hH hA one (v t)
    _ = (∫ t, energy v t ∂μ)/H + (∫ t in S, Real.sqrt (energy v t) ∂μ) + (∫ t, energy v t ∂μ)/A := by
      rw [integral_add, integral_add, integral_div, integral_div, integral_indicator hS]
      · exact he.div_const _
      · exact hvS
      · exact (he.div_const _).add hvS
      · exact he.div_const _
    _ ≤ _ := by change (∫ t in S, Real.sqrt (energy v t) ∂μ) ≤ _ at htail; linarith
end MinUncut.Slice

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ExpectResampleRow
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

variable {m n : ℕ}
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.RowNoise
open BinaryFourier GaussianHermite MeasureTheory
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [DecidableEq ι]

omit [DecidableEq W] [Module F₂ W] in
lemma expect_resample_row (r : R) (f : (R → W) → ℝ) :
    (𝔼 B : R → W, 𝔼 b : W, f (joinRow r b (fun t => B t.val)))=𝔼 B, f B := by
  conv_lhs => rw [expect_splitRow r]
  simp only [joinRow_other, Fintype.expect_const]
  rw [Finset.expect_comm]
  exact (expect_splitRow r f).symm

omit [DecidableEq W] [Module F₂ W] in
lemma expect_rest (r : R) (f : Rest (W := W) r → ℝ) :
    (𝔼 B : R → W, f (fun t => B t.val))=𝔼 D, f D := by
  rw [expect_splitRow r]
  simp only [joinRow_other, Fintype.expect_const]

end MinUncut.RowNoise

namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairSlice_memLp (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n) (b : Forms A) :
    MemLp (fun c => pairSlice f σ η x Y p J B c b) 2 (γpi (Point m n)) :=
  memLp_selectedProject _ _ _

end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma gaussianSlice_background (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (C D : Point m n → ℝ)
    (hCD : ∀ y ∉ freeGaussianPoints x Y, C y=D y) :
    gaussianSlice f σ η x Y J B C=gaussianSlice f σ η x Y J B D := by
  funext t
  unfold gaussianSlice
  have hh := selectedProject_gaussian_local (retainedClass x Y none J)
    (fun B c => gradient f B σ η c x) x (freeGaussianPoints x Y)
    (retained_gaussian_local x Y none J) B (Function.update C x t) (Function.update D x t)
    (fun y hy => by
      by_cases he : y=x
      · subst y; simp only [Function.update_self]
      · simp only [Function.update_of_ne he,hCD y hy])
  simpa only [Function.update_idem,Function.update_self] using hh

attribute [local irreducible] gaussianSlice Slice.centeredClip

attribute [local irreducible] pointEmbed coordinateEnum

lemma zeroProcessedOnBox_abs_le (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) {A₀ : ℝ} (hA : 0≤A₀)
    (B : FaceArray A m n) (c : Point m n → ℝ) (u : Point m (k+1)) :
    |zeroProcessedOnBox f σ η Y J A₀ B c u|≤2*A₀ :=
  Slice.centeredClip_abs_le hA (gaussianSlice_memLp f σ η (pointEmbed Y u) (pointBox Y u) J B c) (c (pointEmbed Y u))

lemma zeroProcessedOnBox_join (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (A₀ : ℝ)
    (B : FaceArray A m n) (C : Point m (k+1) → ℝ) (D : BoxGaussian.Outside (pointEmbed Y) → ℝ) :
    zeroProcessedOnBox f σ η Y J A₀ B (BoxGaussian.join _ (pointEmbed_injective Y) C D) =
      pointField (fun u => Slice.centeredClip γ A₀
        (gaussianSlice f σ η (pointEmbed Y u) (pointBox Y u) J B
          (BoxGaussian.join _ (pointEmbed_injective Y) 0 D))) C := by
  funext u
  unfold zeroProcessedOnBox pointField
  rw [BoxGaussian.join_at]
  have hh : gaussianSlice f σ η (pointEmbed Y u) (pointBox Y u) J B
      (BoxGaussian.join _ (pointEmbed_injective Y) C D) =
      gaussianSlice f σ η (pointEmbed Y u) (pointBox Y u) J B
      (BoxGaussian.join _ (pointEmbed_injective Y) 0 D) := by
    apply gaussianSlice_background
    intro x hx
    have ho : x∉Set.range (pointEmbed Y) := by simpa only [← freeGaussianPoints_range Y u] using hx
    exact (BoxGaussian.join_other _ _ C D ⟨x,ho⟩).trans (BoxGaussian.join_other _ _ 0 D ⟨x,ho⟩).symm
  rw [hh]
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_InnerAssembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
variable {m n : ℕ}

namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory GaussianHermite
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [Nonempty W] [Fintype ι]

lemma jointL1_le_sqrt (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) : jointL1 u ≤ Real.sqrt (jointEnergy u) := by
  have hi (B : R → W) : (∫ c, |u B c| ∂γpi ι) ≤ Real.sqrt (∫ c, (u B c)^2 ∂γpi ι) := by
    simpa using integral_norm_mul_le_sqrt (hu B) (memLp_const (1:ℝ) (p := 2) (μ := γpi ι))
  exact (Finset.expect_le_expect (fun B _ => hi B)).trans
    (expect_sqrt_le _ (fun B => integral_nonneg (fun c => sq_nonneg _)))
end MinUncut.RowNoise

namespace MinUncut.Slice
open MeasureTheory GaussianHermite BinaryFourier
open scoped BigOperators
variable {Ω T W : Type*} [MeasurableSpace Ω] [Fintype T]
  [Fintype W] [AddCommGroup W] [Module F₂ W] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma processed_average_integral_loss (one : W) (v : T → Ω → W → ℝ)
    (hm : ∀ t w, Measurable (fun c => v t c w))
    (hv : ∀ t w, MemLp (fun c => v t c w) 2 μ)
    {H γ A : ℝ} (hH : 0<H) (hγ : 0<γ) (hA : 0<A) :
    (𝔼 t, ∫ c, (𝔼 w, |v t c w-processed H γ A one (v t c) w|) ∂μ) ≤
      (𝔼 t, ∫ c, energy (v t) c ∂μ)/H +
      Real.sqrt (𝔼 t, ∫ c, energy (v t) c ∂μ)*
        Real.sqrt ((𝔼 t, ∫ c, oddMax one (v t c) ∂μ)/γ) +
      (𝔼 t, ∫ c, energy (v t) c ∂μ)/A := by
  classical
  have he t : 0≤∫ c, energy (v t) c ∂μ := integral_nonneg (energy_nonneg (v t))
  have hq t : 0≤(∫ c, oddMax one (v t c) ∂μ)/γ :=
    div_nonneg (integral_nonneg (fun c => oddMax_nonneg one (v t c))) hγ.le
  calc
    _ ≤ 𝔼 t, ((∫ c, energy (v t) c ∂μ)/H +
        Real.sqrt (∫ c, energy (v t) c ∂μ)*Real.sqrt ((∫ c, oddMax one (v t c) ∂μ)/γ) +
        (∫ c, energy (v t) c ∂μ)/A) :=
      Finset.expect_le_expect (fun t _ => processed_integral_loss one (v t) (hm t) (hv t) hH hγ hA)
    _ = (𝔼 t, ∫ c, energy (v t) c ∂μ)/H +
        (𝔼 t, Real.sqrt (∫ c, energy (v t) c ∂μ)*Real.sqrt ((∫ c, oddMax one (v t c) ∂μ)/γ)) +
        (𝔼 t, ∫ c, energy (v t) c ∂μ)/A := by
      simp only [Finset.expect_add_distrib, Finset.expect_div]
    _ ≤ _ := by
      have hcs := Average.expect_sqrt_mul_sqrt
        (fun t => ∫ c, energy (v t) c ∂μ) (fun t => (∫ c, oddMax one (v t c) ∂μ)/γ) he hq
      rw [← Finset.expect_div] at hcs
      linarith only [hcs]
end MinUncut.Slice

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairSlice_resample (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n) (b : Forms A) :
    pairSlice f σ η x Y p J (joinRow ⟨p.val.1,face x p.val.1⟩ b (fun t => B t.val)) =
      pairSlice f σ η x Y p J B := by
  apply pairSlice_background
  intro t ht
  have htr : t≠⟨p.val.1,face x p.val.1⟩ := by
    rintro rfl
    exact ht (local_free_left x Y p)
  exact joinRow_other _ _ _ ⟨t,htr⟩

attribute [local irreducible] gradient selectedProject retainedClass pairSlice pairProcessed Slice.processed

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
end MinUncut.Inner

open scoped BigOperators
variable {m n : ℕ}
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory GaussianHermite
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [Nonempty W] [Fintype ι]

omit [Nonempty W] in
lemma jointL1_sub_triangle (u v w : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (hv : ∀ B, MemLp (v B) 2 (γpi ι))
    (hw : ∀ B, MemLp (w B) 2 (γpi ι)) :
    jointL1 (fun B c => u B c-w B c) ≤
      jointL1 (fun B c => u B c-v B c)+jointL1 (fun B c => v B c-w B c) := by
  unfold jointL1
  rw [← Finset.expect_add_distrib]
  apply Finset.expect_le_expect
  intro B _
  change (∫ c, |u B c-w B c| ∂γpi ι) ≤
    (∫ c, |(u B-v B) c| ∂γpi ι) + (∫ c, |(v B-w B) c| ∂γpi ι)
  rw [← integral_add ((hu B).sub (hv B) |>.integrable (by norm_num) |>.abs)
    ((hv B).sub (hw B) |>.integrable (by norm_num) |>.abs)]
  apply integral_mono ((hu B).sub (hw B) |>.integrable (by norm_num) |>.abs)
    (((hu B).sub (hv B) |>.integrable (by norm_num) |>.abs).add
      ((hv B).sub (hw B) |>.integrable (by norm_num) |>.abs))
  intro c
  simpa only [sub_add_sub_cancel, Pi.add_apply, Pi.sub_apply] using abs_add_le (u B c-v B c) (v B c-w B c)
end MinUncut.RowNoise

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] faceCorrelation pointEmbed pointBox
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pointedJointL1_bayes {k : ℕ}
    (u : (x : Point m n) → PointedBox x k → FaceArray A m n → (Point m n → ℝ) → ℝ)
    (hu : ∀ x Y B, Integrable (u x Y B) (γpi (Point m n))) :
    (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointL1 (u x Y)) =
      𝔼 Y : UnpointedBox (Fin m) (Fin n) k, 𝔼 B : FaceArray A m n,
        ∫ c, (𝔼 t : Point m (k+1), |u (pointEmbed Y t) (pointBox Y t) B c|) ∂γpi (Point m n) := by
  rw [pointed_bayes]
  apply Finset.expect_congr rfl
  intro Y _
  unfold jointL1
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro B _
  exact (integral_expect _ (fun t => (hu (pointEmbed Y t) (pointBox Y t) B).abs)).symm

lemma faceCorrelation_pointed_compare {k : ℕ} (hk : k≤n-1)
    (u : Point m n → ℝ) (v : (x : Point m n) → PointedBox x k → ℝ) :
    faceCorrelation u ≤
      (𝔼 Y : UnpointedBox (Fin m) (Fin n) k,
        faceCorrelation (fun t : Point m (k+1) => v (pointEmbed Y t) (pointBox Y t))) +
      (𝔼 Y : UnpointedBox (Fin m) (Fin n) k,
        𝔼 t : Point m (k+1), |u (pointEmbed Y t)-v (pointEmbed Y t) (pointBox Y t)|) := by
  have ht := faceCorrelation_restriction hk u
  rw [← Finset.expect_add_distrib]
  apply ht.trans
  apply Finset.expect_le_expect
  intro Y _
  have hl := faceCorrelation_lipschitz (fun t : Point m (k+1) => u (pointEmbed Y t))
    (fun t : Point m (k+1) => v (pointEmbed Y t) (pointBox Y t))
  linarith only [le_trans (le_abs_self _) hl]

lemma averagedCorrelation_pointed_compare {k : ℕ} (hk : k≤n-1)
    (u : FaceArray A m n → (Point m n → ℝ) → Point m n → ℝ)
    (v : (x : Point m n) → PointedBox x k → FaceArray A m n → (Point m n → ℝ) → ℝ)
    (hum : ∀ B x, Measurable (fun c => u B c x))
    (hui : ∀ B x, Integrable (fun c => u B c x) (γpi (Point m n)))
    (hvm : ∀ x Y B, Measurable (v x Y B))
    (hvi : ∀ x Y B, Integrable (v x Y B) (γpi (Point m n))) :
    averagedCorrelation u ≤
      (𝔼 Y : UnpointedBox (Fin m) (Fin n) k, 𝔼 B : FaceArray A m n,
        ∫ c, faceCorrelation (fun t : Point m (k+1) => v (pointEmbed Y t) (pointBox Y t) B c) ∂γpi (Point m n)) +
      (𝔼 x : Point m n, 𝔼 Y : PointedBox x k,
        jointL1 (fun B c => u B c x-v x Y B c)) := by
  let C := fun (Y : UnpointedBox (Fin m) (Fin n) k) (B : FaceArray A m n) c =>
    faceCorrelation (fun t : Point m (k+1) => v (pointEmbed Y t) (pointBox Y t) B c)
  let D := fun (Y : UnpointedBox (Fin m) (Fin n) k) (B : FaceArray A m n) c =>
    𝔼 t : Point m (k+1), |u B c (pointEmbed Y t)-v (pointEmbed Y t) (pointBox Y t) B c|
  have hC Y B : Integrable (C Y B) (γpi (Point m n)) :=
    faceCorrelation_integrable _ (fun t => hvm _ _ B) (fun t => hvi _ _ B)
  have hD Y B : Integrable (D Y B) (γpi (Point m n)) := by
    simp only [D,Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun t _ => ((hui B _).sub (hvi _ _ B)).abs)).div_const _
  have hu' B : Integrable (fun c => faceCorrelation (u B c)) (γpi (Point m n)) :=
    faceCorrelation_integrable _ (hum B) (hui B)
  have hCi B : Integrable (fun c => 𝔼 Y, C Y B c) (γpi (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun Y _ => hC Y B)).div_const _
  have hDi B : Integrable (fun c => 𝔼 Y, D Y B c) (γpi (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun Y _ => hD Y B)).div_const _
  have hB B : (∫ c, faceCorrelation (u B c) ∂γpi (Point m n)) ≤
      (𝔼 Y, ∫ c, C Y B c ∂γpi (Point m n)) + (𝔼 Y, ∫ c, D Y B c ∂γpi (Point m n)) := by
    rw [← integral_expect _ (fun Y => hC Y B), ← integral_expect _ (fun Y => hD Y B),
      ← integral_add (hCi B) (hDi B)]
    exact integral_mono (hu' B) ((hCi B).add (hDi B))
      (fun c => faceCorrelation_pointed_compare hk (u B c) (fun x Y => v x Y B c))
  have hh := Finset.expect_le_expect (fun B (_ : B∈(Finset.univ : Finset (FaceArray A m n))) => hB B)
  rw [Finset.expect_add_distrib] at hh
  rw [Finset.expect_comm (f := fun B Y => ∫ c, C Y B c ∂γpi (Point m n)),
    Finset.expect_comm (f := fun B Y => ∫ c, D Y B c ∂γpi (Point m n))] at hh
  have hl := pointedJointL1_bayes
    (fun x Y B c => u B c x-v x Y B c) (fun x Y B => (hui B x).sub (hvi x Y B))
  rw [hl]
  exact hh
end MinUncut.Inner

open scoped BigOperators
variable {m n : ℕ}

open scoped BigOperators

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient oddAtom
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A] {m n : ℕ}

lemma rowAtom_le_gradientBound (f : FoldedProof A) {σ : ℝ} (hσ : 0 < σ) (η : ℝ)
    (x : Point m n) (i : Fin m) (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n))
    (c : Point m n → ℝ) : rowAtom f σ η x i D c ≤ Real.sqrt (n^m : ℕ)/σ :=
  oddAtom_le_bound _ _ _ _ (by positivity) (fun B => gradient_abs_le f B hσ η c x)

lemma gradient_measurable (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (x : Point m n) :
    Measurable (fun c => gradient f B σ η c x) := by
  have hh := (measurable_score 1 σ (measurable_tableSmooth f B η) x).const_mul
    (Real.sqrt (n^m : ℕ)/σ)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext c
  rw [gradient_score f B hσ]
  simp only [score,one_smul]
  rfl

lemma rowAtom_measurable (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (x : Point m n) (i : Fin m)
    (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n)) :
    Measurable (rowAtom f σ η x i D) :=
  measurable_oddAtom _ _ _ (fun B => gradient_measurable f B hσ η x) _

lemma rowAtom_memLp (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (x : Point m n) (i : Fin m)
    (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n)) :
    MemLp (rowAtom f σ η x i D) 2 (γpi (Point m n)) :=
  memLp_oddAtom _ _ _ (fun B => gradient_memLp f B hσ η x) _

lemma rowAtomIndicator_integrable (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η θ : ℝ) (x : Point m n) (i : Fin m)
    (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n)) :
    Integrable (rowAtomIndicator f σ η θ x i D) (γpi (Point m n)) := by
  have hm : Measurable (rowAtomIndicator f σ η θ x i D) :=
    Measurable.ite (measurableSet_le measurable_const (rowAtom_measurable f hσ η x i D))
      measurable_const measurable_const
  apply (MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ (fun c => ?_)) :
    MemLp (rowAtomIndicator f σ η θ x i D) 2 (γpi (Point m n))).integrable (by norm_num)
  unfold rowAtomIndicator
  split_ifs <;> norm_num

lemma rowAtom_sq_le (f : FoldedProof A) {σ θ : ℝ} (hσ : 0 < σ) (hθ : 0 ≤ θ) (η : ℝ)
    (x : Point m n) (i : Fin m) (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n))
    (c : Point m n → ℝ) :
    (rowAtom f σ η x i D c)^2 ≤ θ^2 + (n^m : ℕ)/σ^2*rowAtomIndicator f σ η θ x i D c := by
  have hn : 0 ≤ (n^m : ℕ) := Nat.zero_le _
  have hu := rowAtom_le_gradientBound f hσ η x i D c
  have hl := rowAtom_nonneg f σ η x i D c
  have hs : (Real.sqrt (n^m : ℕ)/σ)^2 = (n^m : ℕ)/σ^2 := by
    rw [div_pow,Real.sq_sqrt (by positivity)]
  unfold rowAtomIndicator
  split_ifs with h
  · have hh := sq_le_sq₀ hl (by positivity) |>.mpr hu
    nlinarith [sq_nonneg θ]
  · simp only [mul_zero,add_zero]
    exact sq_le_sq₀ hl hθ |>.mpr (le_of_lt (lt_of_not_ge h))

lemma rowAtom_secondMoment (f : FoldedProof A) {σ θ : ℝ} (hσ : 0 < σ) (hθ : 0 ≤ θ) (η : ℝ)
    (x : Point m n) (i : Fin m) :
    (𝔼 D, ∫ c, (rowAtom f σ η x i D c)^2 ∂γpi (Point m n)) ≤
      θ^2 + (n^m : ℕ)/σ^2*rowEventProbability f σ η θ x i := by
  calc
    _ ≤ 𝔼 D, ∫ c, θ^2 + (n^m : ℕ)/σ^2*rowAtomIndicator f σ η θ x i D c ∂γpi (Point m n) := by
      apply Finset.expect_le_expect
      intro D _
      exact integral_mono (rowAtom_memLp f hσ.ne' η x i D).integrable_sq
        ((integrable_const _).add ((rowAtomIndicator_integrable f hσ.ne' η θ x i D).const_mul _))
        (rowAtom_sq_le f hσ hθ η x i D)
    _ = _ := by
      simp_rw [integral_add (integrable_const _) ((rowAtomIndicator_integrable f hσ.ne' η θ x i _).const_mul _),
        integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [Finset.expect_add_distrib,Fintype.expect_const, ← Finset.mul_expect]
      rfl

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_AnalyticOuter
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient oddAtom rowAtom pairSlice pairAtomMean
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)] {m n : ℕ}

lemma weighted_row_secondMoment (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ) (hw1 : ∑ ξ, w ξ=1)
    (f : ∀ ξ, FoldedProof (A ξ)) {σ θ p : ℝ} (hσ : 0 < σ) (hθ : 0 ≤ θ) (η : ℝ)
    (hn : 0 < n) (i : Fin m)
    (hp : (∑ ξ, w ξ*atomProbability (m := m) (n := n) (f ξ) σ η θ) ≤ p) :
    (∑ ξ, w ξ*(𝔼 x : Point m n, 𝔼 D, ∫ c, (rowAtom (f ξ) σ η x i D c)^2 ∂γpi (Point m n))) ≤
      θ^2 + (m:ℝ)*p*(n^m:ℕ)/σ^2 := by
  have : NeZero n := ⟨by omega⟩
  have hcap : (0:ℝ) ≤ (n^m:ℕ)/σ^2 := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hξ (ξ : Ξ) : (𝔼 x : Point m n, 𝔼 D, ∫ c, (rowAtom (f ξ) σ η x i D c)^2 ∂γpi (Point m n)) ≤
      θ^2 + (n^m:ℕ)/σ^2*((m:ℝ)*atomProbability (m := m) (n := n) (f ξ) σ η θ) := by
    calc
      _ ≤ (𝔼 x : Point m n, (θ^2 + (n^m:ℕ)/σ^2*rowEventProbability (f ξ) σ η θ x i)) :=
        Finset.expect_le_expect (fun x _ => rowAtom_secondMoment (f ξ) hσ hθ η x i)
      _ = θ^2+(n^m:ℕ)/σ^2*(𝔼 x : Point m n, rowEventProbability (f ξ) σ η θ x i) := by
        rw [Finset.expect_add_distrib,Fintype.expect_const,← Finset.mul_expect]
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (fixed_row_probability_le (f ξ) σ η θ i) hcap) _
  calc
    _ ≤ ∑ ξ, w ξ*(θ^2 + (n^m:ℕ)/σ^2*((m:ℝ)*atomProbability (m := m) (n := n) (f ξ) σ η θ)) :=
      Finset.sum_le_sum (fun ξ _ => mul_le_mul_of_nonneg_left (hξ ξ) (hw ξ))
    _ = θ^2+(n^m:ℕ)/σ^2*(m:ℝ)*(∑ ξ, w ξ*atomProbability (m := m) (n := n) (f ξ) σ η θ) := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul]
      rw [hw1,one_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    _ ≤ θ^2+(n^m:ℕ)/σ^2*(m:ℝ)*p :=
      add_le_add_right (mul_le_mul_of_nonneg_left hp (mul_nonneg hcap hm0)) _
    _ = _ := by ring

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Assembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox BoxGaussian
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient selectedProject retainedClass Slice.centeredClip
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def zeroProcessed (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (A₀ : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) : ℝ :=
  Slice.centeredClip γ A₀ (gaussianSlice f σ η x Y J B c) (c x)

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] classField pairSlice Slice.processed gaussianSlice

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] oddAtom rowAtom pairAtomMean lowGradient

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ComparisonSoundness
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory GaussianHermite
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A] {m n : ℕ}
lemma thirdError_nonneg (f : FoldedProof A) (σ η : ℝ) : 0 ≤ thirdError (m := m) (n := n) f σ η := by
  exact Finset.expect_nonneg (fun B _ => integral_nonneg (fun c =>
    Finset.expect_nonneg (fun z _ => integral_nonneg (fun g => integral_nonneg
      (fun l => thirdFailure_nonneg f B η (c+σ•g) l z)))))
end MinUncut.Inner

end
end

end OAI
end


