-- Prove2me | Definitions.Def_OAIQ076M023
-- name    : OAIQ076M023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:22:21.110634+00:00
-- url     : https://prove2.me/theorems/8f450f31-77e4-4430-aa12-50e081cd792a
-- title:
--   Definitions bundle OAIQ076M023 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 169 declarations of OpenAI's Lean: 30 definitions and 139 theorems. The definitions and types are `OAI.MinUncut.Outer.IndexedLists.numbered`, `OAI.MinUncut.Outer.LocalRows.fourth`, `OAI.MinUncut.Outer.LocalRows.lists`, `OAI.MinUncut.Outer.Parameters.baseTable`, `OAI.MinUncut.Outer.ProofFamily.atomAt`, `OAI.MinUncut.Outer.ProofFamily.distanceAt`, `OAI.MinUncut.Outer.ProofFamily.rows`, `OAI.MinUncut.Outer.budgetWeight`, `OAI.MinUncut.Outer.firstLabel`, `OAI.MinUncut.Outer.hintRawEquiv`, `OAI.MinUncut.Outer.honestProof`, `OAI.MinUncut.Outer.rawCoefficients`, `OAI.MinUncut.Outer.secondLabel`, `OAI.MinUncut.Outer.secondSlotLabel`, `OAI.MinUncutGames.BinaryLiteralMachine.outputWord`, `OAI.MinUncutGames.BinaryLiteralMachine.signWord`, `OAI.MinUncutGames.BinaryRenameLoop.outputBody`, `OAI.MinUncutGames.BinaryRenameLoop.steps`, `OAI.MinUncutGames.BinaryRenameMachine.outputsInTime`, `OAI.MinUncutGames.BinaryRenameMachine.steps`, `OAI.MinUncutGames.BinaryRenameWords.body`, `OAI.MinUncutGames.BinaryRenameWords.outputLiteral`, `OAI.MinUncutGames.Foundations.PCP.ExpanderFamily.baseOnCloud`, `OAI.MinUncutGames.Foundations.PCP.ExpanderFamily.baseVertexEquiv`, `OAI.MinUncutGames.Foundations.PCP.PreprocessingTables.overlayFamily`, `OAI.MinUncutGames.Foundations.PCP.RoundTables.Input`, `OAI.MinUncutGames.Foundations.PCP.RoundTables.Satisfiable`, `OAI.MinUncutGames.Foundations.PCP.RoundTables.alphabet`, `OAI.MinUncutGames.Foundations.PCP.RoundTables.initial`, `OAI.MinUncutGames.Foundations.PCP.RoundTables.size`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_FiniteGaussianLaw`, `MinUncut_Analysis_GaussianDistance`, `MinUncut_Analysis_GaussianRows`, `MinUncut_Encoding_QuestionEncoding`, `MinUncut_Estimates_AnalyticOuter`, `MinUncut_Estimates_ComparisonSoundness`, `MinUncut_Estimates_Density`, `MinUncut_Estimates_FourthTest`, `MinUncut_Estimates_IndexedLists`, `MinUncut_Estimates_InnerUniform`, `MinUncut_Estimates_ListDecoding`, `MinUncut_Estimates_OuterRemainder`, `MinUncut_Estimates_TableTestFunctions`, `MinUncut_Games_HintSections`, `MinUncut_Games_JointHintBound`, `MinUncut_Games_JointHintSampling`, `MinUncut_Games_OuterQuestions`, `MinUncut_Games_Sampling`, `MinUncut_Graphs_CanonicalPathGraph`, `MinUncut_Graphs_CanonicalSamplerGraph`, `MinUncut_Graphs_EdgeMean`, `MinUncut_Graphs_Graph`, `MinUncut_Graphs_GraphOutput`, `MinUncut_Graphs_HonestBudgets`, `MinUncut_Graphs_HonestComparisons`, `MinUncut_Graphs_HonestRows`, `MinUncut_Graphs_SignedGraph`, `MinUncut_Machines_MachineBinaryLiteralMachine`, `MinUncut_Machines_MachineBinaryParsing`, `MinUncut_Machines_MachineBinaryRenameMachine`, `MinUncut_PCP_CayleySampling`, `MinUncut_PCP_CayleySpectral`, `MinUncut_PCP_DegreeReplacement`, `MinUncut_PCP_ExpanderFamily`, `MinUncut_PCP_GraphGap`, `MinUncut_PCP_Overlap`, `MinUncut_PCP_RawInitialTables`, `MinUncut_PCP_SelectedInformation`, `MinUncut_PCP_SelectedMarginal`, `MinUncut_PCP_SelectionSequence`, `MinUncut_PCP_SpectralCut`, `MinUncut_Search_FiniteAverageBounds`, `MinUncut_Search_FiniteQueryFamily`, `MinUncut_Search_RationalBasics`, `MinUncut_Search_RationalInner`.
--
--   **Imports.** It imports the published bundle `Def_MinUncut`; the bundles `OAIQ076M014`, `OAIQ076M015`, `OAIQ076M016`, `OAIQ076M017`, `OAIQ076M018` and `OAIQ076M019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M028`, `OAIQ076M029` and `OAIQ076M030`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_MinUncut
import Definitions.Def_OAIQ076M014
import Definitions.Def_OAIQ076M015
import Definitions.Def_OAIQ076M016
import Definitions.Def_OAIQ076M017
import Definitions.Def_OAIQ076M018
import Definitions.Def_OAIQ076M019

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_HonestRows
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma character_noise_distance {R W : Type*} [Fintype R] [DecidableEq R]
    [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]
    (a : ℝ) (α : Module.Dual F₂ (R → W)) (B : R → W) :
    (𝔼 C, density a B C*(character α B-character α C)^2)=2*(1-(1-a)^degree α) := by
  have he (C : R → W) : density a B C*(character α B-character α C)^2=
      2*density a B C-2*character α B*(density a B C*character α C) := by
    have hb := character_sq α B
    have hc := character_sq α C
    nlinarith only [congrArg (fun t => density a B C*t) hb,congrArg (fun t => density a B C*t) hc]
  simp_rw [he,Finset.expect_sub_distrib,← Finset.mul_expect,density_mean,mul_one]
  change 2-2*character α B*noise a (character α) B=_
  rw [noise_character]
  have hb := character_sq α B
  nlinarith only [congrArg (fun t => (1-a)^degree α*t) hb]

lemma character_noise_distance_le {R W : Type*} [Fintype R] [DecidableEq R]
    [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]
    {ρ : ℝ} (hρ1 : ρ≤1) (α : Module.Dual F₂ (R → W)) (B : R → W) :
    (𝔼 C, density ρ B C*(character α B-character α C)^2)≤2*(degree α:ℝ)*ρ := by
  rw [character_noise_distance]
  have h := one_add_mul_le_pow (by linarith : -2 ≤ -ρ) (degree α)
  simp only [mul_neg,← sub_eq_add_neg] at h
  linarith

end MinUncut.Inner

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_FiniteGaussianLaw
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.LocalTemplate.indexFintype _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

attribute [local instance] OAI.MinUncut.FiniteGaussian.coordsDecEq
lemma tableGrid_real_bound (m n : ℕ) {ε : ℚ} (hε : 0<ε) :
    let g := tableGrid m n ε hε
    (Fintype.card (TestCoordinates m n):ℝ)/(g.T:ℝ)^2+
        2*(Fintype.card (ScoreIndex m n):ℝ)*(2*(n^m:ℕ)+1)*((g.T:ℝ)/g.L)+
        2*(Fintype.card (TestCoordinates m n):ℝ)*(g.T:ℝ)*error g.r ((g.T:ℝ)^2/2) < (ε:ℝ) := by
  let g := tableGrid m n ε hε
  have hg := tableGrid_check m n ε hε
  have he1 : (Fintype.card (TestCoordinates m n):ℝ)/(g.T:ℝ)^2 < (ε:ℝ)/4 := by
    have h : (((Fintype.card (TestCoordinates m n):ℚ)/(g.T:ℚ)^2 : ℚ):ℝ) < ((ε/4:ℚ):ℝ) := Rat.cast_lt.mpr hg.2.2.1
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using (h : (_ : ℝ) < _)
  have he2 : 2*(Fintype.card (ScoreIndex m n):ℝ)*(2*(n^m:ℕ)+1)*(g.T:ℝ)/(g.L:ℝ) < (ε:ℝ)/4 := by
    have h : ((2*(Fintype.card (ScoreIndex m n):ℚ)*(2*(n^m:ℕ)+1)*(g.T:ℚ)/g.L : ℚ):ℝ) < ((ε/4:ℚ):ℝ) := Rat.cast_lt.mpr hg.2.2.2.1
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using (h : (_ : ℝ) < _)
  have he3 : 2*(Fintype.card (TestCoordinates m n):ℝ)*(g.T:ℝ)*error g.r ((g.T:ℝ)^2/2) < (ε:ℝ)/4 := by
    have he := hg.2.2.2.2
    have he' : ((2*(Fintype.card (TestCoordinates m n):ℚ)*g.T*qError g.r ((g.T:ℚ)^2/2)):ℝ) < (ε:ℝ)/4 := by
      exact_mod_cast he
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,qError_cast,Rat.cast_div,Rat.cast_pow] using he'
  have hep : (0:ℝ)<ε := by exact_mod_cast hε
  have hbound : (Fintype.card (TestCoordinates m n):ℝ)/(g.T:ℝ)^2+
        2*(Fintype.card (ScoreIndex m n):ℝ)*(2*(n^m:ℕ)+1)*((g.T:ℝ)/g.L)+
        2*(Fintype.card (TestCoordinates m n):ℝ)*(g.T:ℝ)*error g.r ((g.T:ℝ)^2/2) < ε := by
    rw [mul_div_assoc] at he2
    linarith
  exact hbound

attribute [local irreducible] tableGrid scoreFamily

lemma tableGrid_error (hn : 0<n) {σ η ε : ℚ} (hσ : 0≤σ) (hσ1 : σ≤1)
    (hη : 0≤η) (hη1 : η≤1) (hε : 0<ε)
    (F : (ScoreIndex m n → Bool) → ℝ) (hF : ∀ t, 0≤F t ∧ F t≤1) :
    |(∫ x, F (thresholdTable (scoreFamily (σ:ℝ) (η:ℝ)) x) ∂gaussianLaw (TestCoordinates m n))-
      ∑ j : TestCoordinates m n → Fin (tableGrid m n ε hε).L,
        (gridWeight (tableGrid m n ε hε) j:ℝ)*
          F (rationalScoreTable σ η (fun i => midpoint (tableGrid m n ε hε).T (tableGrid m n ε hε).L (j i)))| < ε := by
  have hg := tableGrid_check m n ε hε
  have hT : (1:ℚ)≤(tableGrid m n ε hε).T := by exact_mod_cast hg.1
  exact (rational_table_error hn hσ hσ1 hη hη1 _ hT hg.2.1 F hF).trans_lt
    (tableGrid_real_bound m n hε)

end MinUncut.FiniteGaussian

end
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

lemma fixedSet_overlap_probability [Nonempty ι] {k : ℕ} (hk : k ≤ Fintype.card ι) :
    (𝔼 H : FixedSets ι k, 𝔼 K : FixedSets ι k,
      if ¬Disjoint H.val K.val then (1 : ℝ) else 0) ≤
      (k : ℝ)^2 / Fintype.card ι := by
  let : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
  have hfix (H : FixedSets ι k) :
      (𝔼 K : FixedSets ι k, if ¬Disjoint H.val K.val then (1 : ℝ) else 0) ≤
        (k : ℝ)^2 / Fintype.card ι := by
    calc
      _ ≤ 𝔼 K : FixedSets ι k, ∑ i ∈ H.val, if i ∈ K.val then (1 : ℝ) else 0 :=
        Finset.expect_le_expect (fun K _ => overlap_union_bound _ _)
      _ = ∑ i ∈ H.val, (k : ℝ) / Fintype.card ι := by
        rw [Finset.expect_sum_comm]
        simp_rw [membership_probability hk]
      _ = _ := by simp [H.property, sq, mul_div_assoc]
  calc
    _ ≤ 𝔼 _H : FixedSets ι k, (k : ℝ)^2 / Fintype.card ι :=
      Finset.expect_le_expect (fun H _ => hfix H)
    _ = _ := Fintype.expect_const _

lemma mixture_tv_bound [Nonempty ι] {k : ℕ} (hk : k ≤ Fintype.card ι)
    (p : ∀ i, Density (A i)) {b : ℝ} (hb : 1 ≤ b)
    (hcard : ∀ i, (Fintype.card (A i) : ℝ) ≤ b) :
    letI : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
    (mixture (fun H : FixedSets ι k => H.val) p).tvUniform ≤
      Real.sqrt ((b ^ (2*k) - 1) * (k : ℝ)^2 / Fintype.card ι) / 2 := by
  let : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  have hconstant : 0 ≤ b^(2*k) - 1 := sub_nonneg.mpr (one_le_pow₀ hb)
  let d := mixture (fun H : FixedSets ι k => H.val) p
  have hcross (H K : FixedSets ι k) :
      (𝔼 x, hiddenDensity p H.val x * hiddenDensity p K.val x) ≤
        1 + (b^(2*k)-1) * (if ¬Disjoint H.val K.val then 1 else 0) := by
    by_cases h : Disjoint H.val K.val
    · simp [hiddenDensity_cross_disjoint p h, h]
    · simp only [h, not_false_eq_true, ite_true, mul_one, add_sub_cancel]
      have hprod (x : ∀ i, A i) : hiddenDensity p H.val x * hiddenDensity p K.val x ≤ b^(2*k) := by
        have hH := hiddenDensity_le p hb0 hcard H.val x
        have hK := hiddenDensity_le p hb0 hcard K.val x
        rw [H.property] at hH
        rw [K.property] at hK
        calc _ ≤ b^k * b^k := mul_le_mul hH hK ((hiddenDensity p K.val).nonneg x) (pow_nonneg hb0 _)
             _ = _ := by rw [← pow_add]; congr 1; omega
      calc _ ≤ 𝔼 _x : ∀ i, A i, b^(2*k) := Finset.expect_le_expect (fun x _ => hprod x)
           _ = _ := Fintype.expect_const _
  have hvar : (𝔼 x, (d x - 1)^2) ≤ (b^(2*k)-1) * (k : ℝ)^2 / Fintype.card ι := by
    rw [mixture_variance]
    have havg := Finset.expect_le_expect (s := Finset.univ)
      (fun H _ => Finset.expect_le_expect (s := Finset.univ) (fun K _ => hcross H K))
    simp_rw [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect] at havg
    have hh := mul_le_mul_of_nonneg_left (fixedSet_overlap_probability hk) hconstant
    rw [← mul_div_assoc] at hh
    linarith
  exact (Density.tvUniform_le_sqrt d).trans
    (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hvar) (by norm_num))

namespace JointForms

variable {r : ι → ℕ} {d : ℕ}

attribute [local instance] OAI.MinUncut.OuterSmoothness.JointForms.dualFintype
attribute [local instance] OAI.MinUncut.OuterSmoothness.JointForms.densityDualDecidableEq
theorem joint_smoothness [Nonempty ι] {k : ℕ} (hk : k ≤ Fintype.card ι)
    (hr : ∀ i, r i ≤ 2) (T : ∀ i, (Fin (r i) → F₂) →ₗ[F₂] Triple)
    (hT : ∀ i, Function.Injective (T i)) (o : ι → Triple) :
    letI : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
    (Density.ofMap (affineOutput T o (d := d) (k := k))).tvUniform ≤
      Real.sqrt (((2 : ℝ)^(4*d*k)-1) * (k : ℝ)^2 / Fintype.card ι) / 2 := by
  let : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
  have heq : (Density.ofMap (affineOutput T o (d := d) (k := k))).tvUniform =
      (mixture (fun H : FixedSets ι k => H.val) (fun i => hiddenLaw (d := d) (T i))).tvUniform := by
    unfold Density.tvUniform
    rw [expect_pair]
    simp_rw [joint_density hk T hT o]
    exact congrArg (fun x : ℝ => x / 2) (Fintype.expect_const _)
  rw [heq]
  have hcard (i : ι) : (Fintype.card (Block (r i) d) : ℝ) ≤ (2 : ℝ)^(2*d) := by
    rw [card_block, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right d (hr i))
  have h := mixture_tv_bound hk (fun i => hiddenLaw (d := d) (T i))
    (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)) hcard
  have hexp : 2*d*(2*k) = 4*d*k := by ring
  simpa only [← pow_mul, hexp] using h

end JointForms
end MinUncut.OuterSmoothness

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FourthTest
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

theorem gradient_comparison (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n)
    (hn : 0 < n) {σ : ℝ} (hσ : σ≠0) (η : ℝ) (c : Point m n → ℝ) :
    spatialEnergy (fun x => gradient f B σ η c x-gradient g C σ η c x) ≤
      4*σ⁻¹^2*comparisonRejection f g B C σ η c := by
  let μ := (gauss (Point m n)).prod (gauss (Code m n))
  let D := fun p => coupledAnswer f B σ η c p-coupledAnswer g C σ η c p
  have hD : MemLp D 2 μ := (coupledAnswer_memLp f B σ η c).sub (coupledAnswer_memLp g C σ η c)
  have hX (x : Point m n) : MemLp (fun p => p.1 x) 2 μ :=
    (GaussianSmoothing.coordinate_memLp_two x).comp_fst (gauss (Code m n))
  have hXX (x y : Point m n) : (∫ p, p.1 x*p.1 y ∂μ)=if x=y then 1 else 0 := by
    have hi : Integrable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => p.1 x*p.1 y) μ :=
      (hX x).integrable_mul (hX y)
    change (∫ p, p.1 x*p.1 y ∂(gauss (Point m n)).prod (gauss (Code m n)))=_
    rw [integral_prod _ hi]
    simpa only [integral_const,MeasureTheory.probReal_univ,one_smul,gauss,GaussianSmoothing.gamma] using GaussianSmoothing.coordinate_second_moment x y
  have hS := GaussianSmoothing.integral_bessel hX hXX hD
  have hN : (0 : ℝ)<(n^m:ℕ) := by exact_mod_cast pow_pos hn m
  have hd (x : Point m n) :
      gradient f B σ η c x-gradient g C σ η c x =
      Real.sqrt (n^m:ℕ)/σ*(∫ p, p.1 x*D p ∂μ) := by
    rw [gradient_coupled_score f B hσ,gradient_coupled_score g C hσ]
    simp only [D,mul_sub]
    rw [integral_sub (coupled_score_integrable f B σ η c x) (coupled_score_integrable g C σ η c x)]
    ring
  have he : spatialEnergy (fun x => gradient f B σ η c x-gradient g C σ η c x) =
      σ⁻¹^2*∑ x, (∫ p, p.1 x*D p ∂μ)^2 := by
    simp only [spatialEnergy,hd,mul_pow,div_pow,Real.sq_sqrt hN.le,← Finset.mul_sum]
    field_simp
  rw [he]
  calc
    _ ≤ σ⁻¹^2*(∫ p, (D p)^2 ∂μ) := mul_le_mul_of_nonneg_left hS (sq_nonneg _)
    _ = _ := by
      simp_rw [D,comparisonFailure_eq]
      rw [integral_const_mul]
      change σ⁻¹^2*(4*comparisonRejection f g B C σ η c)=_
      ring

lemma comparisonRejection_range (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ)
    (c : Point m n → ℝ) :
    0≤ comparisonRejection f g B C σ η c ∧ comparisonRejection f g B C σ η c≤1 := by
  have hm : Measurable (comparisonFailure f g B C σ η c) := by
    change Measurable (fun p => comparisonFailure f g B C σ η c p)
    simp_rw [comparisonFailure_indicator]
    exact ((coupledAnswer_measurable f B σ η c).sub
      (coupledAnswer_measurable g C σ η c)).pow_const 2 |>.div_const 4
  have hb (p : (Point m n → ℝ) × (Code m n → ℝ)) :
      0≤ comparisonFailure f g B C σ η c p ∧ comparisonFailure f g B C σ η c p≤1 := by
    unfold comparisonFailure; split_ifs <;> norm_num
  have hi : Integrable (comparisonFailure f g B C σ η c)
      ((gauss (Point m n)).prod (gauss (Code m n))) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hb p).1]; exact (hb p).2))
  constructor
  · exact integral_nonneg (fun p => (hb p).1)
  · unfold comparisonRejection
    simpa only [integral_const,MeasureTheory.probReal_univ,one_smul] using
      integral_mono hi (integrable_const 1) (fun p => (hb p).2)

lemma comparisonRejection_integrable (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ) :
    Integrable (comparisonRejection f g B C σ η) (gauss (Point m n)) :=
  Integrable.of_bound (comparisonRejection_measurable f g B C σ η).aestronglyMeasurable 1
    (ae_of_all _ (fun c => by
      rw [Real.norm_eq_abs,abs_of_nonneg (comparisonRejection_range f g B C σ η c).1]
      exact (comparisonRejection_range f g B C σ η c).2))

lemma averaged_comparison (π : A →ᵃ[F₂] A') (f : FoldedProof A) (g : FoldedProof A')
    (hn : 0<n) {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    averagedEnergy (m := m) (n := n) (fun C c x => gradient f (pullbackFaces π C) σ η c x-
      gradient g C σ η c x) ≤ 4*σ⁻¹^2*fourthError (m := m) (n := n) π f g σ η := by
  have he (C : FaceArray A' m n) :
      (∫ c, spatialEnergy (fun x => gradient f (pullbackFaces π C) σ η c x-
          gradient g C σ η c x) ∂gauss (Point m n)) ≤
        4*σ⁻¹^2*(∫ c, comparisonRejection f g (pullbackFaces π C) C σ η c ∂gauss (Point m n)) := by
    have hi : Integrable (fun c => spatialEnergy (fun x =>
        gradient f (pullbackFaces π C) σ η c x-gradient g C σ η c x)) (gauss (Point m n)) := by
      apply Integrable.const_mul
      apply integrable_finsetSum
      intro x _
      exact ((gradient_memLp f (pullbackFaces π C) hσ η x).sub
        (gradient_memLp g C hσ η x)).integrable_sq
    rw [← integral_const_mul]
    exact integral_mono hi ((comparisonRejection_integrable f g _ _ σ η).const_mul _)
      (fun c => gradient_comparison f g _ _ hn hσ η c)
  simpa only [averagedEnergy,fourthError,← Finset.mul_expect] using
    Finset.expect_le_expect (s := Finset.univ) (fun C _ => he C)

end MinUncut.Inner

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_OuterQuestions
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.equationFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

lemma evaluatedTriple_valid (s : Name → F₂) (E : Equation Name) (h : Satisfied s E) :
    Valid E (evaluatedTriple s E) :=
  ⟨h,fun _ _ he => congrArg s he⟩

def firstLabel (s : Name → F₂) (U : I → Equation Name) : FirstAlphabet U :=
  fun j => if h : Satisfied s (U j) then ⟨evaluatedTriple s (U j),evaluatedTriple_valid s (U j) h⟩
    else origin (U j)

def secondSlotLabel (s : Name → F₂) : (v : SecondQuestion Name) → secondSlot v
  | .inl x => fun _ => s x
  | .inr E => evaluatedTriple s E

def secondLabel (s : Name → F₂) (V : I → SecondQuestion Name) : SecondAlphabet V :=
  fun j => secondSlotLabel s (V j)

lemma honest_slot (s : Name → F₂) (E : Equation Name) (h : Satisfied s E)
    (hidden : Bool) (p : Fin 3) :
    slotProjection E hidden p ⟨evaluatedTriple s E,evaluatedTriple_valid s E h⟩ =
      secondSlotLabel s (slotQuestion E hidden p) := by
  cases hidden <;> rfl

lemma honest_projection (s : Name → F₂) (U : I → Equation Name)
    (h : ∀ j, Satisfied s (U j)) (hidden : I → Bool) (position : I → Fin 3) :
    projection U hidden position (firstLabel s U) =
      secondLabel s (secondQuestion U hidden position) := by
  funext j
  change slotProjection (U j) (hidden j) (position j) (firstLabel s U j)=_
  simp only [firstLabel,dite_eq_left (h j)]
  exact honest_slot s (U j) (h j) (hidden j) (position j)

open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

lemma hintGenerator_surjective (V : I → SecondQuestion Name) :
    Function.Surjective (hintGenerator V) := by
  classical
  intro f
  let localPart (j : I) : Module.Dual F₂ (secondSlot (V j)) :=
    f.linear.comp (LinearMap.single F₂ (fun j => secondSlot (V j)) j)
  let c := fun j => unpackFunctional (V j) (localPart j)
  refine ⟨(f 0,(fun j => (c j).1,fun j => (c j).2)),?_⟩
  ext a
  change directHint V (f 0) (fun j => (c j).1) (fun j => (c j).2) a=f a
  rw [directHint_apply]
  have hlin : (∑ j,slotFunctional (V j) (c j).1 (c j).2 (a j))=f.linear a := by
    simp only [c,slotFunctional_unpack,localPart,LinearMap.comp_apply,LinearMap.single_apply]
    rw [← map_sum,Finset.univ_sum_single]
  rw [hlin]
  simpa using (f.map_vadd (0 : SecondAlphabet V) a).symm

attribute [local instance] BinaryFourier.dualFintype

lemma hintTupleGenerator_surjective (V : I → SecondQuestion Name) (q : ℕ) :
    Function.Surjective (hintTupleGenerator V q) := by
  intro f
  choose c hc using fun k => hintGenerator_surjective V (f k)
  exact ⟨c,funext hc⟩

lemma uniform_hintTupleGenerator (V : I → SecondQuestion Name) (q : ℕ)
    (f : (Fin q → Forms (SecondAlphabet V)) → ℝ) :
    (𝔼 c, f (hintTupleGenerator V q c)) = 𝔼 L, f L :=
  IndependentSquares.expect_surjective_linear (hintTupleGenerator V q)
    (hintTupleGenerator_surjective V q) f

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Sampling
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

lemma ordinary_all_implies_satisfied (E : Equation Name) (a : Triple) (s : Name → F₂)
    (h : ∀ p, ordinaryAccepts E (E.names p) a (s (E.names p))=true) :
    Satisfied s E := by
  have hvalid : Valid E a := (of_decide_eq_true (h 0)).1
  have he : a=evaluatedTriple s E := by
    funext p
    exact (of_decide_eq_true (h p)).2 p rfl
  simpa only [Satisfied,← he] using hvalid.1

lemma ordinary_coordinate_bound (E : Equation Name) (a : Triple) (s : Name → F₂) :
    (∑ p : Fin 3, if ordinaryAccepts E (E.names p) a (s (E.names p)) then (1 : ℝ) else 0)
      ≤ 2+(if Satisfied s E then (1 : ℝ) else 0) := by
  have hall := ordinary_all_implies_satisfied E a s
  simp only [Fin.sum_univ_three]
  by_cases h0 : ordinaryAccepts E (E.names 0) a (s (E.names 0))=true
  <;> by_cases h1 : ordinaryAccepts E (E.names 1) a (s (E.names 1))=true
  <;> by_cases h2 : ordinaryAccepts E (E.names 2) a (s (E.names 2))=true
  · have hs : Satisfied s E := hall (by intro p; fin_cases p <;> assumption)
    norm_num [h0,h1,h2,hs]
  all_goals simp only [h0,h1,h2,Bool.false_eq_true,↓reduceIte]; split <;> norm_num

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

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem rightReveal_full_error (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (partialRevealMarginal μ j likelihood)
      (rightRevealModel μ (partialRevealMarginal μ j likelihood)) ≤
      2 * Information.totalVariation (fullRevealMarginal μ j likelihood)
        (fullRevealModel μ j likelihood) := by
  rw [fullReveal_totalVariation]
  exact rightRevealModel_totalVariation_le μ _

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SelectedMarginal
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
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selected_rightReveal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected)))) ≤
      2 * selectedInformationRadius G strategy selected := by
  calc
    _ ≤ ∑ j : {i : Fin n // i ∉ selected},
        2 * totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
      apply Finset.sum_le_sum
      intro j _
      exact rightReveal_full_error G.questions j _
    _ = 2 * ∑ j : {i : Fin n // i ∉ selected},
        totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (selected_fullReveal_information_bound G strategy selected positive) (by norm_num)


end

end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Overlap
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition

open scoped BigOperators
open Information

open scoped BigOperators
open Games
noncomputable section

universe u

open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

open scoped BigOperators
open Games Information

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedRightProfileError_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedRightProfileError G strategy selected positive j) ≤
      3 * selectedInformationRadius G strategy selected := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset {i : Fin n // i ∉ selected})) =>
      selectedRightProfileError_le G strategy selected positive j)
  simp_rw [selectedCommonLaw_secondMarginal] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hright := selected_rightReveal_error_sum G strategy selected positive
  have hquestion := selectedQuestionMarginal_error_sum G strategy selected positive
  change (∑ j : {i : Fin n // i ∉ selected},
    Information.totalVariation (selectedQuestionMarginal G strategy selected positive j.1).weight
      G.questions.weight) ≤ _ at hquestion
  linarith

theorem selectedEmbeddingError_sum_le_fifteen [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedEmbeddingError G strategy selected positive j) ≤
      15 * selectedInformationRadius G strategy selected := by
  have hl := selectedLeftProfileError_sum G strategy selected positive
  have hr := selectedRightProfileError_sum G strategy selected positive
  have hn : 0 ≤ selectedInformationRadius G strategy selected := Real.sqrt_nonneg _
  simp only [selectedEmbeddingError, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

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

namespace MinUncutGames.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem holenstein_conditionalCoordinateBound
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (ell : ℝ)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    SelectionSequence.ConditionalCoordinateBound G n strategy ell := by
  intro selected hcard positive
  obtain ⟨j,hj⟩ := exists_coordinate_le_information_budget G strategy selected positive ell
    halphabet hcard (selectedEmbeddingError G strategy selected positive)
    (selectedEmbeddingError_sum_le_fifteen G strategy selected positive)
  exact ⟨j.1,j.property,
    (selected_coordinate_probability_le_value_add_error G strategy selected positive j).trans
      (add_le_add le_rfl hj)⟩

theorem holenstein_repetition_success
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv : v < 1) (hell : 1 ≤ ell)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    (G.repetition n).success strategy ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) :=
  SelectionSequence.repetition_success_le_of_conditionalCoordinateBound G n strategy
    hvalue hv hell (holenstein_conditionalCoordinateBound G n strategy ell halphabet)

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_HintSections
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

omit [Fintype Name] [Fintype I] [Fintype S] [Nonempty S] in
lemma sampledEquations_patch (equations : S → Equation Name) (A : I → Prop)
    (bg : I → S × Fin 3) (w : {i // A i} → S × Fin 3) :
    sampledEquations equations (patch A bg w)=
      patch A (sampledEquations equations bg) (sampledEquations equations w) :=
  patch_comp A bg w (fun x => equations x.1)

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ListDecoding
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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


open scoped BigOperators
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I : Type*} [Fintype I]

lemma uniform_tupleCoordinateGenerator (U : I → Equation Name) (d : ℕ)
    (f : (Fin d → Forms (FirstAlphabet U)) → ℝ) :
    (𝔼 z : TupleCoordinateData U d, f (tupleCoordinateGenerator U d z)) = 𝔼 L, f L :=
  IndependentSquares.expect_surjective_linear _ (tupleCoordinateGenerator_surjective U d) f

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_JointHintSampling
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I : Type*} [Fintype I]

def rawCoefficients {d : ℕ} (κ : Fin d → F₂) (w : I → JointForms.Raw d) :
    HintCoefficients I d := fun k => (κ k,(fun i => (w i).1.2 k,fun i => (w i).2 k))

def hintRawEquiv (d : ℕ) :
    ((I → Fin 3) × HintCoefficients I d) ≃ ((Fin d → F₂) × (I → JointForms.Raw d)) where
  toFun z := (fun k => (z.2 k).1,fun i => ((z.1 i,fun k => (z.2 k).2.1 i),
    fun k => (z.2 k).2.2 i))
  invFun z := (rawPositions z.2,rawCoefficients z.1 z.2)
  left_inv _ := rfl
  right_inv _ := rfl

lemma raw_joint_identity (U : I → Equation Name) {d k : ℕ} (H : FixedSets I k)
    (κ : Fin d → F₂) (w : I → JointForms.Raw d) :
    firstHints U (hiddenSet H.val) (rawPositions w) (rawCoefficients κ w) =
    tupleCoordinateGenerator U d
      (JointForms.affineOutput (fun i => directionEmbedding (U i))
        (fun i => (origin (U i)).val) (κ,H,w)) := by
  classical
  funext l
  apply AffineMap.ext
  intro a
  change formPullback (projection U (hiddenSet H.val) (rawPositions w))
    (directHint _ (κ l) (fun i => (w i).1.2 l) (fun i => (w i).2 l)) a =
    firstFormCoordinates U (_,_) a
  rw [pulledHint_apply,firstFormCoordinates_apply]
  simp only [hiddenSet,decide_eq_true_eq,rawPositions]
  simp_rw [raw_slot_expansion U H.val w a]
  simp only [Finset.sum_add_distrib,JointForms.affineOutput,JointForms.offset,Pi.add_apply]
  ring

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_JointHintBound
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I : Type*} [Fintype I]

lemma raw_background_expect (U : I → Equation Name) {d : ℕ} (H : Finset I)
    (f : (Fin d → Forms (FirstAlphabet U)) → ℝ) :
    (𝔼 pos : I → Fin 3,
      𝔼 L : Fin d → Forms (SecondAlphabet (secondQuestion U (hiddenSet H) pos)),
        f (fun k => formPullback (projection U (hiddenSet H) pos) (L k))) =
    (𝔼 z : (Fin d → F₂) × (I → JointForms.Raw d),
      f (firstHints U (hiddenSet H) (rawPositions z.2) (rawCoefficients z.1 z.2))) := by
  classical
  have hpos (pos : I → Fin 3) :
      (𝔼 L : Fin d → Forms (SecondAlphabet (secondQuestion U (hiddenSet H) pos)),
        f (fun k => formPullback (projection U (hiddenSet H) pos) (L k))) =
      (𝔼 c : HintCoefficients I d, f (firstHints U (hiddenSet H) pos c)) :=
    (uniform_hintTupleGenerator _ d (fun L =>
      f (fun k => formPullback (projection U (hiddenSet H) pos) (L k)))).symm
  simp_rw [hpos]
  rw [← expect_pair (fun z : (I → Fin 3) × HintCoefficients I d =>
    f (firstHints U (hiddenSet H) z.1 z.2))]
  exact Fintype.expect_equiv (hintRawEquiv (I := I) d) _ _ (fun z => rfl)

lemma actual_joint_law (U : I → Equation Name) {d k : ℕ} (hk : k≤Fintype.card I)
    (f : (Fin d → Forms (FirstAlphabet U)) → ℝ) :
    let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
    (𝔼 H : FixedSets I k,𝔼 pos : I → Fin 3,
      𝔼 L : Fin d → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        f (fun j => formPullback (projection U (hiddenSet H.val) pos) (L j))) =
    (𝔼 sample : (Fin d → F₂) × (FixedSets I k × (I → JointForms.Raw d)),
      f (tupleCoordinateGenerator U d
        (JointForms.affineOutput (fun i => directionEmbedding (U i))
          (fun i => (origin (U i)).val) sample))) := by
  classical
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  simp_rw [raw_background_expect]
  rw [expect_pair]
  simp_rw [expect_pair]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro κ _
  apply Finset.expect_congr rfl
  intro H _
  apply Finset.expect_congr rfl
  intro w _
  exact congrArg f (raw_joint_identity U H κ w)

theorem actual_joint_smoothness [Nonempty I] (U : I → Equation Name) {d k : ℕ}
    (hk : k≤Fintype.card I) (f : (Fin d → Forms (FirstAlphabet U)) → ℝ)
    {M : ℝ} (hM : 0≤M) (hf : ∀ L, |f L|≤M) :
    let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
    |(𝔼 H : FixedSets I k,𝔼 pos : I → Fin 3,
      𝔼 L : Fin d → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        f (fun j => formPullback (projection U (hiddenSet H.val) pos) (L j))) -
      (𝔼 L : Fin d → Forms (FirstAlphabet U), f L)| ≤
    Real.sqrt (((2 : ℝ)^(4*d*k)-1)*(k : ℝ)^2/Fintype.card I)*M := by
  classical
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  rw [actual_joint_law U hk]
  let output := JointForms.affineOutput (fun i => directionEmbedding (U i))
    (fun i => (origin (U i)).val) (d := d) (k := k)
  have h := Density.expect_difference (Density.ofMap output)
    (fun z => f (tupleCoordinateGenerator U d z)) hM (fun z => hf _)
  rw [Density.expect_ofMap,uniform_tupleCoordinateGenerator] at h
  have htv := JointForms.joint_smoothness hk (fun i => alphabet_dimension_le (U i))
    (fun i => directionEmbedding (U i)) (fun i => directionEmbedding_injective (U i))
    (fun i => (origin (U i)).val) (d := d)
  refine h.trans ?_
  calc
    _ ≤ 2 * (Real.sqrt (((2 : ℝ)^(4*d*k)-1)*(k : ℝ)^2/Fintype.card I)/2)*M := by
      gcongr
      convert htv using 1
      all_goals try with_reducible_and_instances rfl
      exact Density.tv_ofMap_instances _ _ _ _ _ _ _ _ output
    _ = _ := by ring

end MinUncut.Outer

namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

variable {Name I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

theorem actual_joint_smoothness_index [Nonempty I] (U : I → Equation Name) {k : ℕ}
    (hk : k≤Fintype.card I) (f : (J → Forms (FirstAlphabet U)) → ℝ)
    {M : ℝ} (hM : 0≤M) (hf : ∀ L, |f L|≤M) :
    let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
    |(𝔼 H : FixedSets I k,𝔼 pos : I → Fin 3,
      𝔼 L : J → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        f (fun j => formPullback (projection U (hiddenSet H.val) pos) (L j))) -
      (𝔼 L : J → Forms (FirstAlphabet U), f L)| ≤
    Real.sqrt (((2 : ℝ)^(4*Fintype.card J*k)-1)*(k : ℝ)^2/Fintype.card I)*M := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  let e := Fintype.equivFin J
  have h := actual_joint_smoothness (d := Fintype.card J) U hk (fun L => f (fun j => L (e j))) hM
    (fun L => hf _)
  dsimp only at h
  rw [actual_background_reindex U k e f,expect_reindex e f] at h
  exact h

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_IndexedLists
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

variable {Name I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

def IndexedLists.numbered (lists : IndexedLists Name I J) : HintLists Name I (Fintype.card J) where
  first U D := lists.first U (fun j => D (Fintype.equivFin J j))
  second V D := lists.second V (fun j => D (Fintype.equivFin J j))

lemma IndexedLists.numbered_matches (lists : IndexedLists Name I J)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3) :
    (𝔼 B : Fin (Fintype.card J) → Forms (SecondAlphabet (secondQuestion U hidden pos)),
      if lists.numbered.matches U hidden pos B then (1 : ℝ) else 0) =
    𝔼 B : J → Forms (SecondAlphabet (secondQuestion U hidden pos)),
      if lists.matches U hidden pos B then (1 : ℝ) else 0 :=
  expect_reindex (Fintype.equivFin J) (fun B => if lists.matches U hidden pos B then 1 else 0)

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

omit [Nonempty S] in
lemma backgroundMean_mono (equations : S → Equation Name) (k : ℕ)
    {F G : BackgroundStatistic Name I J} (h : ∀ U hidden pos B, F U hidden pos B≤G U hidden pos B) :
    backgroundMean equations k F ≤ backgroundMean equations k G := by
  apply Finset.expect_le_expect
  intro H _
  apply Finset.expect_le_expect
  intro a _
  apply Finset.expect_le_expect
  intro pos _
  exact Finset.expect_le_expect (fun B _ => h _ _ _ _)

omit [Nonempty S] in
lemma backgroundMean_add (equations : S → Equation Name) (k : ℕ)
    (F G : BackgroundStatistic Name I J) :
    backgroundMean equations k (fun U h pos B => F U h pos B+G U h pos B) =
      backgroundMean equations k F+backgroundMean equations k G := by
  simp only [backgroundMean,Finset.expect_add_distrib]

omit [Nonempty S] in
lemma backgroundMean_mul (equations : S → Equation Name) (k : ℕ)
    (F : BackgroundStatistic Name I J) (t : ℝ) :
    backgroundMean equations k (fun U h pos B => t*F U h pos B) =
      t*backgroundMean equations k F := by
  simp only [backgroundMean,← Finset.mul_expect]

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_OuterRemainder
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

theorem actual_remainder_fourth (U : I → Equation Name) {k : ℕ} (hk : k≤Fintype.card I)
    (f : (J → Forms (FirstAlphabet U)) → Forms (FirstAlphabet U) → ℝ)
    {M u : ℝ} (hM : 0≤M) (hu : 0<u) (hf : ∀ D z, |f D z|≤M) :
    let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
    (𝔼 H : FixedSets I k,𝔼 pos : I → Fin 3,
      𝔼 D : J → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        restrictedFourth (projection U (hiddenSet H.val) pos)
          (f (fun j => formPullback (projection U (hiddenSet H.val) pos) (D j))) u) ≤
      u^2*M^2+Real.sqrt (((2 : ℝ)^(4*(Fintype.card J+3)*k)-1)*(k : ℝ)^2/Fintype.card I)*
        (M+M^2/u)^4 := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  have h := actual_joint_smoothness_index U hk (adaptiveKernel f u)
    (by positivity : 0≤(M+M^2/u)^4) (adaptiveKernel_abs f hM hu hf)
  rw [TripleIndex.card] at h
  have he (H : FixedSets I k) (pos : I → Fin 3) :
      (𝔼 L : TripleIndex J → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        adaptiveKernel f u (fun j => formPullback (projection U (hiddenSet H.val) pos) (L j))) =
      𝔼 D : J → Forms (SecondAlphabet (secondQuestion U (hiddenSet H.val) pos)),
        restrictedFourth (projection U (hiddenSet H.val) pos)
          (f (fun j => formPullback (projection U (hiddenSet H.val) pos) (D j))) u :=
    adaptiveKernel_pullback_mean _ f u
  simp_rw [he] at h
  have hm := adaptiveKernel_uniform f hM hu hf
  have hh := (le_abs_self _).trans h
  linarith


open scoped BigOperators
open MinUncut.Inner OuterSmoothness MinUncut.Composition
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

variable {Name I J S : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [Nonempty S]

def LocalRows.lists (rows : LocalRows Name I J) (u θ : ℝ) : IndexedLists Name I J where
  first U D := labelList (rows.first U D) u
  second V D := labelList (rows.second V D) θ

def LocalRows.fourth (rows : LocalRows Name I J) (u : ℝ) : BackgroundStatistic Name I J :=
  fun U hidden pos B => restrictedFourth (projection U hidden pos)
    (rows.first U (fun j => formPullback (projection U hidden pos) (B j))) u

omit [Fintype J] [DecidableEq J] in
lemma LocalRows.card_first (rows : LocalRows Name I J) {M u θ : ℝ}
    (hM : 0≤M) (hu : 0<u) (hf : ∀ U D z, |rows.first U D z|≤M)
    (U : I → Equation Name) (D : J → Forms (FirstAlphabet U)) :
    ((rows.lists u θ).first U D).card≤⌈M^2/u^2⌉₊ := by
  exact_mod_cast (labelList_card _ hM hu (hf U D)).trans (Nat.le_ceil _)

omit [Fintype J] [DecidableEq J] in
lemma LocalRows.card_second (rows : LocalRows Name I J) {M u θ : ℝ}
    (hM : 0≤M) (hθ : 0<θ) (hg : ∀ V D z, |rows.second V D z|≤M)
    (V : I → SecondQuestion Name) (D : J → Forms (SecondAlphabet V)) :
    ((rows.lists u θ).second V D).card≤⌈M^2/θ^2⌉₊ := by
  exact_mod_cast (labelList_card _ hM hθ (hg V D)).trans (Nat.le_ceil _)

lemma LocalRows.mean_fourth [Nonempty I] (rows : LocalRows Name I J)
    (equations : S → Equation Name) {k : ℕ} (hk : k≤Fintype.card I)
    {M u : ℝ} (hM : 0≤M) (hu : 0<u) (hf : ∀ U D z, |rows.first U D z|≤M) :
    backgroundMean equations k (rows.fourth u) ≤
      u^2*M^2+Real.sqrt (((2 : ℝ)^(4*(Fintype.card J+3)*k)-1)*(k : ℝ)^2/Fintype.card I)*
        (M+M^2/u)^4 := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  unfold backgroundMean
  rw [Finset.expect_comm]
  exact (Finset.expect_le_expect (fun a _ =>
    actual_remainder_fourth (fun i => equations (a i)) hk (rows.first _) hM hu (hf _))).trans_eq
      (Fintype.expect_const _)

end MinUncut.Outer

open scoped BigOperators
namespace MinUncut.Outer
open MeasureTheory GaussianHermite MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I J S Ω : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [MeasurableSpace Ω] {μ : Measure Ω}

lemma backgroundMean_integrable (equations : S → Equation Name) (k : ℕ)
    (F : Ω → BackgroundStatistic Name I J)
    (hF : ∀ U h pos B, Integrable (fun c => F c U h pos B) μ) :
    Integrable (fun c => backgroundMean equations k (F c)) μ := by
  exact integrable_expect _ (fun H => integrable_expect _ (fun a =>
    integrable_expect _ (fun pos => integrable_expect _ (fun B => hF _ _ _ B))))

lemma integral_backgroundMean (equations : S → Equation Name) (k : ℕ)
    (F : Ω → BackgroundStatistic Name I J)
    (hF : ∀ U h pos B, Integrable (fun c => F c U h pos B) μ) :
    (∫ c, backgroundMean equations k (F c) ∂μ) =
      backgroundMean equations k (fun U h pos B => ∫ c, F c U h pos B ∂μ) := by
  unfold backgroundMean
  rw [integral_expect _ (fun H => integrable_expect _ (fun a =>
    integrable_expect _ (fun pos => integrable_expect _ (fun B => hF _ _ _ B))))]
  congr 1
  funext H
  rw [integral_expect _ (fun a =>
    integrable_expect _ (fun pos => integrable_expect _ (fun B => hF _ _ _ B)))]
  congr 1
  funext a
  rw [integral_expect _ (fun pos => integrable_expect _ (fun B => hF _ _ _ B))]
  congr 1
  funext pos
  exact integral_expect _ (fun B => hF _ _ _ B)
end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianRows
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient

variable {Name I S : Type*} [Fintype I] [Fintype S] {m n : ℕ}

def ProofFamily.rows (f : ProofFamily Name I) (σ η : ℝ) (c : Point m n → ℝ)
    (x : Point m n) (r : Row m n) : LocalRows Name I {t : Row m n // t≠r} where
  first U := comparisonRow (f.first U) σ η c x r
  second V := comparisonRow (f.second V) σ η c x r

lemma ProofFamily.rows_first_bound (f : ProofFamily Name I) {σ : ℝ} (hσ : 0<σ) (η : ℝ)
    (c : Point m n → ℝ) (x : Point m n) (r : Row m n)
    (U : I → Equation Name) (D : Rest (W := Forms (FirstAlphabet U)) r)
    (z : Forms (FirstAlphabet U)) :
    |(f.rows σ η c x r).first U D z| ≤ Real.sqrt (n^m:ℕ)/σ :=
  gradient_abs_le _ _ hσ η c x

lemma ProofFamily.rows_second_bound (f : ProofFamily Name I) {σ : ℝ} (hσ : 0<σ) (η : ℝ)
    (c : Point m n → ℝ) (x : Point m n) (r : Row m n)
    (V : I → SecondQuestion Name) (D : Rest (W := Forms (SecondAlphabet V)) r)
    (z : Forms (SecondAlphabet V)) :
    |(f.rows σ η c x r).second V D z| ≤ Real.sqrt (n^m:ℕ)/σ :=
  gradient_abs_le _ _ hσ η c x

lemma ProofFamily.rows_atom_integrable (f : ProofFamily Name I) {σ θ : ℝ}
    (hσ : σ≠0) (hθ : 0<θ) (η : ℝ) (x : Point m n) (i : Fin m)
    (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (B : Rest (W := Forms (SecondAlphabet (secondQuestion U h pos))) (⟨i,face x i⟩ : Row m n)) :
    Integrable (fun c => (f.rows σ η c x ⟨i,face x i⟩).atom θ U h pos B) (gauss (Point m n)) := by
  change Integrable (fun c => if (labelList (comparisonRow (f.second _) σ η c x ⟨i,face x i⟩ B) θ).Nonempty then (1:ℝ) else 0) _
  simp_rw [← rowAtomIndicator_eq_list _ σ η hθ]
  exact rowAtomIndicator_integrable _ hσ η θ x i B

lemma ProofFamily.rows_distance_integrable (f : ProofFamily Name I) {σ : ℝ}
    (hσ : σ≠0) (η : ℝ) (x : Point m n) (r : Row m n)
    (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (B : Rest (W := Forms (SecondAlphabet (secondQuestion U h pos))) r) :
    Integrable (fun c => (f.rows σ η c x r).distance U h pos B) (gauss (Point m n)) := by
  apply integrable_expect
  intro z
  exact ((gradient_memLp (f.second _) _ hσ η x).sub
    (gradient_memLp (f.first U) _ hσ η x)).integrable_sq

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_EdgeMean
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I S : Type*} [Fintype I] [Fintype S]

lemma edgeMean_mono (equations : S → Equation Name) (k : ℕ) {F G : EdgeStatistic Name I}
    (h : ∀ U hidden pos, F U hidden pos ≤ G U hidden pos) :
    edgeMean equations k F ≤ edgeMean equations k G := by
  exact Finset.expect_le_expect (fun H _ => Finset.expect_le_expect (fun a _ =>
    Finset.expect_le_expect (fun pos _ => h _ _ _)))

lemma edgeMean_mul (equations : S → Equation Name) (k : ℕ) (F : EdgeStatistic Name I) (t : ℝ) :
    edgeMean equations k (fun U h pos => t*F U h pos) = t*edgeMean equations k F := by
  simp only [edgeMean,← Finset.mul_expect]

lemma edgeMean_expect {X : Type*} [Fintype X] (equations : S → Equation Name) (k : ℕ)
    (F : X → EdgeStatistic Name I) :
    (𝔼 x, edgeMean equations k (F x)) = edgeMean equations k (fun U h pos => 𝔼 x,F x U h pos) := by
  unfold edgeMean
  rw [Finset.expect_comm]
  congr 1
  funext H
  rw [Finset.expect_comm]
  congr 1
  funext a
  rw [Finset.expect_comm]

lemma edgeMean_const [Nonempty S] (equations : S → Equation Name) {k : ℕ}
    (hk : k≤Fintype.card I) (t : ℝ) : edgeMean (I := I) equations k (fun _ _ _ => t)=t := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  simp only [edgeMean,Fintype.expect_const]

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianDistance
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n : ℕ}

def ProofFamily.atomAt (f : ProofFamily Name I) (σ η θ : ℝ) (x : Point m n) (i : Fin m) :
    EdgeStatistic Name I :=
  fun U h pos => rowEventProbability (f.second (secondQuestion U h pos)) σ η θ x i

def ProofFamily.distanceAt (f : ProofFamily Name I) (σ η : ℝ) (x : Point m n) (i : Fin m) :
    EdgeStatistic Name I := fun U h pos =>
  𝔼 D : Rest (W := Forms (SecondAlphabet (secondQuestion U h pos))) (⟨i,face x i⟩ : Row m n),
    ∫ c, (f.rows σ η c x ⟨i,face x i⟩).distance U h pos D ∂gauss (Point m n)

lemma ProofFamily.atomAt_integral (f : ProofFamily Name I) (equations : S → Equation Name)
    (k : ℕ) {σ θ : ℝ} (hσ : σ≠0) (hθ : 0<θ) (η : ℝ)
    (x : Point m n) (i : Fin m) :
    (∫ c, backgroundMean equations k ((f.rows σ η c x ⟨i,face x i⟩).atom θ) ∂gauss (Point m n)) =
      edgeMean equations k (f.atomAt σ η θ x i) := by
  rw [integral_backgroundMean _ _ _ (f.rows_atom_integrable hσ hθ η x i)]
  unfold backgroundMean edgeMean ProofFamily.atomAt rowEventProbability LocalRows.atom ProofFamily.rows
  simp_rw [← rowAtomIndicator_eq_list _ σ η hθ]
  rfl

lemma ProofFamily.distanceAt_integral (f : ProofFamily Name I) (equations : S → Equation Name)
    (k : ℕ) {σ : ℝ} (hσ : σ≠0) (η : ℝ) (x : Point m n) (i : Fin m) :
    (∫ c, backgroundMean equations k (f.rows σ η c x ⟨i,face x i⟩).distance ∂gauss (Point m n)) =
      edgeMean equations k (f.distanceAt σ η x i) :=
  integral_backgroundMean _ _ _ (f.rows_distance_integrable hσ η x _)

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_SignedGraph
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.PathRealization
attribute [local instance] Classical.propDecidable

variable {V D : Type*}

variable [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D]

omit [Fintype V] [DecidableEq V] [DecidableEq D] in
lemma uncut_lower (e : D → Demand V) (s : Vertex V D → Bool) :
    totalFailure e (fun v => s (.inl v)) ≤ uncut e s := by
  rw [uncut_locals]
  exact Finset.sum_le_sum (fun d _ => local_lower _ _ _ _ _ _)

omit [Fintype V] [DecidableEq V] [DecidableEq D] in
lemma uncut_extend (e : D → Demand V) (s : V → Bool) : uncut e (extend e s)=totalFailure e s := by
  rw [uncut_locals]
  apply Finset.sum_congr rfl
  intro d _
  simpa [extend,failure] using
    local_extension (e d).equal (s (e d).left) (s (e d).right)

end MinUncut.PathRealization

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_FiniteQueryFamily
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

lemma proofFamily_ext {f g : ProofFamily Name I}
    (hf : f.first=g.first) (hg : f.second=g.second) : f=g := by
  cases f
  cases g
  cases hf
  cases hg
  rfl

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_QuestionEncoding
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences

lemma decodeFirst_encodeFirst {N t : ℕ} (U : Fin t → Equation (Fin N)) (a : FirstAlphabet U) :
    decodeFirst U (encodeFirst U a)=some a := by
  have ha : ∀j, Valid (U j) (encodeFirst U a j) := fun j => (a j).property
  simp only [decodeFirst,dite_eq_left ha]
  rfl

lemma decodeSecond_encodeSecond {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (a : SecondAlphabet Q) :
    decodeSecond Q (encodeSecond Q a)=a := by
  funext j k
  exact dite_eq_left k.isLt

lemma decodeAlphabet_encodeAlphabet {N t : ℕ} (q : FamilyQuestion (Fin N) (Fin t)) (a : FamilyAlphabet q) :
    decodeAlphabet q (encodeAlphabet q a)=some a := by
  cases q with
  | inl U => exact decodeFirst_encodeFirst U a
  | inr Q => exact congrArg some (decodeSecond_encodeSecond Q a)

lemma extendTable_eval {N t : ℕ} (q : FamilyQuestion (Fin N) (Fin t)) (R : FamilyAlphabet q → Bool)
    (a : FamilyAlphabet q) : extendTable q R (encodeAlphabet q a)=R a := by
  simp only [extendTable,decodeAlphabet_encodeAlphabet,Option.map_some,Option.getD_some]

lemma extendTable_injective {N t : ℕ} (q : FamilyQuestion (Fin N) (Fin t)) :
    Function.Injective (extendTable q) := by
  intro R S h
  funext a
  simpa only [extendTable_eval] using congrFun h (encodeAlphabet q a)

lemma variableCode_injective {N t : ℕ} : Function.Injective (variableCode (N := N) (t := t)) := by
  rintro ⟨q,R⟩ ⟨s,S⟩ h
  have hp := (paddedVariableEncoding N t).code.injective h
  have hq : q=s := congrArg Prod.fst hp
  subst s
  have hR : R=S := Subtype.ext (extendTable_injective q (congrArg Prod.snd hp))
  subst S
  rfl

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_AnalyticOuter
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n : ℕ}

lemma ProofFamily.atomTotal_mean (f : ProofFamily Name I) (equations : S → Equation Name)
    (k : ℕ) (σ η θ : ℝ) :
    (𝔼 x : Point m n, 𝔼 i : Fin m,edgeMean equations k (f.atomAt σ η θ x i)) =
      edgeMean equations k (f.atomTotal (m := m) (n := n) σ η θ) := by
  simp_rw [edgeMean_expect]
  rfl

lemma ProofFamily.distanceTotal_bound (f : ProofFamily Name I) (equations : S → Equation Name)
    (k : ℕ) (hm : 0 < m) (hn : 0 < n) {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    (𝔼 x : Point m n, 𝔼 i : Fin m,edgeMean equations k (f.distanceAt σ η x i)) ≤
      (4*σ⁻¹^2)*edgeMean equations k (f.fourthTotal (m := m) (n := n) σ η) := by
  simp_rw [edgeMean_expect]
  rw [← edgeMean_mul]
  apply edgeMean_mono
  intro U h pos
  change (𝔼 x : Point m n, 𝔼 i : Fin m,
    𝔼 D, ∫ c, rowDistance (projection U h pos)
      (comparisonRow (f.first U) σ η c x ⟨i,face x i⟩ (fun t => formPullback (projection U h pos) (D t)))
      (comparisonRow (f.second (secondQuestion U h pos)) σ η c x ⟨i,face x i⟩ D) ∂gauss (Point m n)) ≤ _
  rw [comparisonRow_distance_total _ _ _ hm hσ]
  exact averaged_comparison _ _ _ hn hσ η

end MinUncut.Outer

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_InnerUniform
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] firstError secondError thirdError atomProbability
variable {Name I S : Type*} [Fintype I] [Fintype S]

lemma edgeSample_expect (equations : S → Equation Name) (k : ℕ) (F : EdgeStatistic Name I) :
    (𝔼 e : EdgeSamples I S k, F (fun i => equations (e.2.1 i)) (hiddenSet e.1.val) e.2.2) =
      edgeMean equations k F := by
  rw [expect_pair]
  simp_rw [expect_pair]
  rfl

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ComparisonSoundness
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
lemma firstError_nonneg (f : FoldedProof A) (σ η : ℝ) : 0 ≤ firstError (m := m) (n := n) f σ η := by
  exact Finset.expect_nonneg (fun B _ => integral_nonneg (fun c => (firstRejection_range f B σ η c).1))
lemma secondError_nonneg (f : FoldedProof A) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (σ η : ℝ) :
    0 ≤ secondError (m := m) (n := n) f a σ η := by
  exact Finset.expect_nonneg (fun B _ => Finset.expect_nonneg (fun C _ =>
    mul_nonneg (RowNoise.density_nonneg ha ha1 B C)
      (integral_nonneg (fun c => (secondRejection_range f B C σ η c).1))))
end MinUncut.Inner
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] firstError secondError thirdError fourthError atomProbability
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

omit [Nonempty S] in
lemma edgeMean_nonneg {I : Type*} [Fintype I] (equations : S → Equation Name) (k : ℕ)
    (F : EdgeStatistic Name I) (hF : ∀ U h pos, 0 ≤ F U h pos) : 0 ≤ edgeMean equations k F := by
  exact Finset.expect_nonneg (fun H _ => Finset.expect_nonneg (fun a _ =>
    Finset.expect_nonneg (fun pos _ => hF _ _ _)))

lemma fourthError_nonneg {V A W B : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
    [Fintype A] [AddCommGroup W] [Module F₂ W] [AddTorsor W B] [Fintype B]
    {m n : ℕ} (π : A →ᵃ[F₂] B) (f : FoldedProof A) (g : FoldedProof B) (σ η : ℝ) :
    0 ≤ fourthError (m := m) (n := n) π f g σ η := by
  unfold fourthError
  exact Finset.expect_nonneg (fun C _ => MeasureTheory.integral_nonneg
    (fun c => (comparisonRejection_range f g (pullbackFaces π C) C σ η c).1))

attribute [local irreducible] edgeMean

omit [Nonempty S] in
lemma ProofFamily.testErrors_nonneg {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J) (O : OuterParameters J P)
    (f : ProofFamily Name I) (equations : S → Equation Name) (j : Test) :
    0 ≤ f.testErrors P O equations j := by
  have hm : 0 < P.m := by have := P.hm; omega
  have ha := source_row_rate hJ hm
  cases j <;> rw [ProofFamily.testErrors] <;> apply edgeMean_nonneg <;> intro U h pos
  · exact firstError_nonneg (V := SecondAlphabet (secondQuestion U h pos)) _ _ _
  · exact secondError_nonneg (V := SecondAlphabet (secondQuestion U h pos)) _ ha.1 ha.2.1 _ _
  · exact thirdError_nonneg (V := SecondAlphabet (secondQuestion U h pos)) _ _ _
  · unfold ProofFamily.fourthTotal
    exact fourthError_nonneg (V := FirstDirection U) (W := SecondAlphabet (secondQuestion U h pos)) _ _ _ _ _

attribute [local irreducible] ProofFamily.fourthTotal ProofFamily.atomTotal

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_TableTestFunctions
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {V A V' A' : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A'] [Fintype A'] {m n : ℕ}

omit [Fintype A] in
lemma thirdTable_source (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c g : Point m n → ℝ) (l : Code m n → ℝ) (z : Code m n) :
    thirdTable f B z (sourceTable σ η c g l)=thirdFailure f B η (c+σ•g) l z := rfl

omit [Fintype A] in
lemma firstTable_integral (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) :
    (∫ c, firstRejection f B σ η c ∂gauss (Point m n))=
      ∫ x, firstTable f B (thresholdTable (scoreFamily σ η) x) ∂gaussianLaw (TestCoordinates m n) :=
  table_integral_pack σ η (firstTable f B) (fun _ => disagreement_range _ _)

omit [Fintype A] in
lemma secondTable_integral (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ) :
    (∫ c, secondRejection f B C σ η c ∂gauss (Point m n))=
      ∫ x, secondTable f B C (thresholdTable (scoreFamily σ η) x) ∂gaussianLaw (TestCoordinates m n) :=
  table_integral_product σ η (secondTable f B C) (fun _ => disagreement_range _ _)

omit [Fintype A] in
lemma thirdTable_integral (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) :
    (∫ c, thirdRejection f B σ η c ∂gauss (Point m n))=
      𝔼 z : Code m n, ∫ x, thirdTable f B z (thresholdTable (scoreFamily σ η) x)
        ∂gaussianLaw (TestCoordinates m n) := by
  unfold thirdRejection
  simp only [Fintype.expect_eq_sum_div_card,integral_div]
  simp_rw [← thirdTable_source]
  rw [integral_finsetSum _ (fun z _ => sourceTest_outer_integrable σ η (thirdTable f B z)
    (fun _ => disagreement_range _ _))]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  exact table_integral_pack σ η (thirdTable f B z) (fun _ => disagreement_range _ _)

omit [Fintype A] [Fintype A'] in
lemma fourthTable_integral (f : FoldedProof A) (g : FoldedProof A') (B : FaceArray A m n)
    (C : FaceArray A' m n) (σ η : ℝ) :
    (∫ c, comparisonRejection f g B C σ η c ∂gauss (Point m n))=
      ∫ x, fourthTable f g B C (thresholdTable (scoreFamily σ η) x) ∂gaussianLaw (TestCoordinates m n) :=
  table_integral_product σ η (fourthTable f g B C) (fun _ => disagreement_range _ _)

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_GraphOutput
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.PathRealization
attribute [local instance] Classical.propDecidable
variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D]
variable {N : ℕ}

omit [Fintype V] in
lemma output_yes (e : D → Demand V) (number : Vertex V D ≃ Fin N) (k : ℕ) (hk : 1 ≤ k)
    (s : V → Bool) (h : totalFailure e s ≤ k) : (output e number k hk).opt ≤ k := by
  apply (output_opt_le _ ((extend e s) ∘ number.symm)).trans
  erw [output_uncut]
  have he : ((extend e s) ∘ number.symm) ∘ number=extend e s := by ext v; simp
  erw [he,uncut_extend]
  exact h

omit [Fintype V] in
lemma output_no (e : D → Demand V) (number : Vertex V D ≃ Fin N) (k : ℕ) (hk : 1 ≤ k)
    (R : ℕ) (h : ∀ s : V → Bool, R<totalFailure e s) : R<(output e number k hk).opt := by
  apply lt_of_lt_of_le (Nat.lt_succ_self R)
  apply le_output_opt
  intro s
  erw [output_uncut]
  exact (h (fun v => s (number (.inl v)))).trans_le (uncut_lower e (s ∘ number))
end MinUncut.PathRealization

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CanonicalPathGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace MinUncut.PathRealization

lemma canonicalOutput_yes {N M : ℕ} (e : Fin M → Demand (Fin N)) (k : ℕ) (hk : 1≤k)
    (s : Fin N → Bool) (h : totalFailure e s≤k) : (canonicalOutput e k hk).opt≤k := by
  rw [canonicalOutput_eq]
  exact output_yes _ _ _ _ s h

lemma canonicalOutput_no {N M : ℕ} (e : Fin M → Demand (Fin N)) (k : ℕ) (hk : 1≤k)
    (K : ℕ) (h : ∀ s, K*k<totalFailure e s) : K*k<(canonicalOutput e k hk).opt := by
  rw [canonicalOutput_eq]
  exact output_no _ _ _ _ _ h

end MinUncut.PathRealization

end

open scoped BigOperators
namespace MinUncut.PathRealization
open MinUncut.FiniteProof MinUncutGames.Foundations.Hastad.SourceOccurrences

lemma listFailure_eq {V : Type*} (ds : List (Demand V)) (s : V → Bool) :
    listFailure ds s=totalFailure (fun i : Fin ds.length => ds[i]) s := by
  unfold listFailure totalFailure
  simp only [Fin.getElem_fin]
  rw [← List.sum_ofFn]
  exact (congrArg List.sum (List.ofFn_getElem_eq_map ds (fun d => failure d s))).symm

end MinUncut.PathRealization

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_FiniteAverageBounds
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.LocalTemplate.indexFintype _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
attribute [local instance] coordsDecEq
variable {V A V' A' : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A'] [Fintype A'] {m n : ℕ}

lemma tableAverage_difference (hn : 0<n) {σ η ε : ℚ} (hσ : 0≤σ) (hσ1 : σ≤1)
    (hη : 0≤η) (hη1 : η≤1) (hε : 0<ε)
    (F : (ScoreIndex m n → Bool) → ℝ) (hF : ∀ t, 0≤F t ∧ F t≤1) :
    |(∫ x,F (thresholdTable (scoreFamily (σ:ℝ) (η:ℝ)) x) ∂gaussianLaw (TestCoordinates m n))-
      tableAverage (tableGrid m n ε hε) σ η F|≤ε :=
by
  simpa only [tableAverage] using (tableGrid_error hn hσ hσ1 hη hη1 hε F hF).le

lemma finiteFirst_difference (f : FoldedProof A) (hn : 0<n) {σ η ε : ℚ}
    (hσ : 0≤σ) (hσ1 : σ≤1) (hη : 0≤η) (hη1 : η≤1) (hε : 0<ε) :
    |firstError (m := m) (n := n) f σ η-finiteFirst (m := m) (n := n) (tableGrid m n ε hε) f σ η|≤ε := by
  apply expect_abs_difference
  intro B
  rw [firstTable_integral]
  exact tableAverage_difference hn hσ hσ1 hη hη1 hε _ (fun _ => disagreement_range _ _)

lemma finiteSecond_difference (f : FoldedProof A) (hn : 0<n) {σ η ε : ℚ}
    (hσ : 0≤σ) (hσ1 : σ≤1) (hη : 0≤η) (hη1 : η≤1) (hε : 0<ε)
    {a : ℝ} (ha : 0≤a) (ha1 : a≤1) :
    |secondError (m := m) (n := n) f a σ η-finiteSecond (m := m) (n := n) (tableGrid m n ε hε) f a σ η|≤ε := by
  apply expect_abs_difference
  intro B
  apply weighted_expect_abs_difference _ _ _ (fun C => RowNoise.density_nonneg ha ha1 B C)
    (RowNoise.density_mean a B)
  intro C
  rw [secondTable_integral]
  exact tableAverage_difference hn hσ hσ1 hη hη1 hε _ (fun _ => disagreement_range _ _)

lemma finiteThird_difference (f : FoldedProof A) (hn : 0<n) {σ η ε : ℚ}
    (hσ : 0≤σ) (hσ1 : σ≤1) (hη : 0≤η) (hη1 : η≤1) (hε : 0<ε) :
    |thirdError (m := m) (n := n) f σ η-finiteThird (m := m) (n := n) (tableGrid m n ε hε) f σ η|≤ε := by
  apply expect_abs_difference
  intro B
  rw [thirdTable_integral]
  apply expect_abs_difference
  intro z
  exact tableAverage_difference hn hσ hσ1 hη hη1 hε _ (fun _ => disagreement_range _ _)

omit [Fintype A] in
lemma finiteFourth_difference (π : A →ᵃ[F₂] A') (f : FoldedProof A) (f' : FoldedProof A')
    (hn : 0<n) {σ η ε : ℚ} (hσ : 0≤σ) (hσ1 : σ≤1) (hη : 0≤η) (hη1 : η≤1) (hε : 0<ε) :
    |fourthError (m := m) (n := n) π f f' σ η-
      finiteFourth (m := m) (n := n) (tableGrid m n ε hε) π f f' σ η|≤ε := by
  apply expect_abs_difference
  intro C
  rw [fourthTable_integral]
  exact tableAverage_difference hn hσ hσ1 hη hη1 hε _ (fun _ => disagreement_range _ _)
end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_HonestComparisons
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma noise_vector_sq (a : A) (B : FaceArray A m n) (hn : 0<n) (ρ : ℝ) :
    (𝔼 C : FaceArray A m n, density ρ B C*‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖^2)=
      ((n^m:ℕ):ℝ)⁻¹*∑ x : Point m n, 2*(1-(1-ρ)^degree (labelFunctional a x)) := by
  simp_rw [codeVector_distance_sq hn,← character_label,Finset.mul_sum,mul_left_comm (density ρ B _),
    Finset.expect_sum_comm,← Finset.mul_expect,character_noise_distance]

lemma noise_vector_sq_le (a : A) (B : FaceArray A m n) (hn : 0<n)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (𝔼 C : FaceArray A m n, density ρ B C*‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖^2) ≤ 2*(m:ℝ)*ρ := by
  have hn' : (0:ℝ)<(n^m:ℕ) := by positivity
  rw [noise_vector_sq a B hn]
  calc
    _  ≤  ((n^m:ℕ):ℝ)⁻¹ * ∑ _ : Point m n, 2*(m:ℝ)*ρ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn'.le)
      apply Finset.sum_le_sum
      intro x _
      have hb := character_noise_distance_le hρ1 (labelFunctional a x) B
      rw [character_noise_distance] at hb
      have hd : (degree (labelFunctional a x):ℝ) ≤ m := by exact_mod_cast labelFunctional_degree a x
      exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) hρ)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul]
      rw [← mul_assoc,inv_mul_cancel₀ hn'.ne',one_mul]

lemma noise_vector_le (a : A) (B : FaceArray A m n) (hn : 0<n) (hm : 0 < m)
    {δ : ℝ} (hδ : 0 ≤ δ) (hρ1 : δ^2/(m:ℝ) ≤ 1) :
    (𝔼 C : FaceArray A m n, density (δ^2/(m:ℝ)) B C*
      ‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖) ≤ 2*δ := by
  have hρ : 0 ≤ δ^2/(m:ℝ) := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hs := weighted_expect_sq (density (δ^2/(m:ℝ)) B)
    (fun C => ‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖)
    (density_nonneg hρ hρ1 B) (density_mean _ B)
  have hb := noise_vector_sq_le a B hn hρ hρ1
  have hmp : (0:ℝ)< m := by exact_mod_cast hm
  have he : 2*(m:ℝ)*(δ^2/(m:ℝ))=2*δ^2 := by field_simp
  rw [he] at hb
  have hM : 0 ≤ 𝔼 C : FaceArray A m n, density (δ^2/(m:ℝ)) B C*
      ‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖ :=
    Finset.expect_nonneg (fun C _ => mul_nonneg (density_nonneg hρ hρ1 B C) (norm_nonneg _))
  have hs' := hs.trans hb
  exact (sq_le_sq₀ hM (by positivity)).mp (by nlinarith [sq_nonneg δ])
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_HonestBudgets
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory RowNoise GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma secondError_evaluation_le (a : A) (hn : 0 < n) (hm : 0 < m)
    {σ η δ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hρ : δ^2/(m:ℝ) ≤ 1) :
    secondError (m := m) (n := n) (evaluationProof a) (δ^2/(m:ℝ)) σ η ≤ 8*δ+4*η := by
  have hρ0 : 0 ≤ δ^2/(m:ℝ) := by positivity
  have hB (B : FaceArray A m n) :
      (𝔼 C : FaceArray A m n, density (δ^2/(m:ℝ)) B C*
        (∫ c, secondRejection (evaluationProof a) B C σ η c ∂gauss (Point m n))) ≤ 8*δ+4*η := by
    calc
      _ ≤ 𝔼 C : FaceArray A m n, density (δ^2/(m:ℝ)) B C*
          (4*‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖+4*η) := by
        apply Finset.expect_le_expect
        intro C _
        exact mul_le_mul_of_nonneg_left (secondRejection_evaluation_le a B C hn hσ hσ1 hη)
          (density_nonneg hρ0 hρ B C)
      _ = 4*(𝔼 C : FaceArray A m n, density (δ^2/(m:ℝ)) B C*
          ‖vector (codeVector (labelCode B a))-vector (codeVector (labelCode C a))‖)+4*η := by
        simp_rw [mul_add,mul_left_comm (density _ B _),Finset.expect_add_distrib,
          ← Finset.mul_expect]
        rw [← Finset.expect_mul,density_mean,one_mul]
      _ ≤ _ := by have h := noise_vector_le a B hn hm hδ hρ; linarith
  exact (Finset.expect_le_expect (fun B _ => hB B)).trans_eq (Fintype.expect_const _)

lemma honest_second_budget (a : A) (hn : 0 < n) (hm : 0 < m) {J : ℝ} (hJ : 1 ≤ J) :
    secondError (m := m) (n := n) (evaluationProof a) ((sourceEta J)^2/(m:ℝ))
      (sourceSigma J) (sourceEta J) ≤ 10*(sourceEta J+sourceEta J) := by
  have h := secondError_evaluation_le a hn hm (sourceSigma_pos hJ).le (sourceSigma_le_one hJ)
    (sourceEta_pos hJ).le (sourceEta_pos hJ).le (source_row_rate hJ hm).2.1
  have := sourceEta_pos hJ
  linarith
end MinUncut.Inner

namespace MinUncut.Inner
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {V A W B : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup W] [Module F₂ W] [AddTorsor W B] [Fintype B] {m n : ℕ}

lemma fourthError_le_one (π : A →ᵃ[F₂] B) (f : FoldedProof A) (g : FoldedProof B) (σ η : ℝ) :
    fourthError (m := m) (n := n) π f g σ η ≤ 1 := by
  have hC (C : FaceArray B m n) :
      (∫ c, comparisonRejection f g (pullbackFaces π C) C σ η c ∂gauss (Point m n)) ≤ 1 := by
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (comparisonRejection_integrable f g _ _ σ η) (integrable_const 1)
        (fun c => (comparisonRejection_range f g _ _ σ η c).2)
  exact (Finset.expect_le_expect (fun C _ => hC C)).trans_eq (Fintype.expect_const _)
end MinUncut.Inner
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

def honestProof (s : Name → F₂) : ProofFamily Name I where
  first U := evaluationProof (firstLabel s U)
  second Q := evaluationProof (secondLabel s Q)

lemma honest_fourth_point (s : Name → F₂) (U : I → Equation Name) (h : I → Bool)
    (pos : I → Fin 3) (m n : ℕ) (σ η : ℝ) :
    (honestProof (I := I) s).fourthTotal (m := m) (n := n) σ η U h pos ≤
      ∑ i, if Satisfied s (U i) then (0:ℝ) else 1 := by
  by_cases hall : ∀ i, Satisfied s (U i)
  · have hp := honest_projection s U hall h pos
    simp only [ProofFamily.fourthTotal,honestProof]
    rw [← hp,fourthError_evaluation]
    simp only [hall,ite_eq_left,Finset.sum_const_zero,le_refl]
  · obtain ⟨i,hi⟩ := not_forall.mp hall
    have hs : (1:ℝ) ≤ ∑ j, if Satisfied s (U j) then (0:ℝ) else 1 := by
      simpa only [hi,ite_false] using
        (Finset.single_le_sum (a := i) (fun j _ => by split <;> norm_num : ∀ j ∈ Finset.univ, 0 ≤ if Satisfied s (U j) then (0:ℝ) else 1) (Finset.mem_univ i))
    exact (fourthError_le_one (projection U h pos) _ _ σ η).trans hs

attribute [local irreducible] firstError secondError thirdError fourthError edgeMean

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalBasics
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

lemma edgeMean_abs_difference (equations : S → Equation Name) {k : ℕ}
    (hk : k≤Fintype.card I) (F G : EdgeStatistic Name I) {ε : ℝ}
    (h : ∀ U hidden pos, |F U hidden pos-G U hidden pos|≤ε) :
    |edgeMean equations k F-edgeMean equations k G|≤ε := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  apply expect_abs_difference
  intro H
  apply expect_abs_difference
  intro a
  apply expect_abs_difference
  intro pos
  exact h _ _ _

def budgetWeight {J : ℝ} (P : InnerParameters J) (O : OuterParameters J P) : ℝ :=
  ∑ j, (budgets P O j)⁻¹

attribute [local irreducible] edgeMean
end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalInner
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.innerDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.outerDataPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian

lemma rationalWeight_cast {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) :
    (rationalWeight J d o:ℝ)=budgetWeight (d.realize hJ hd) (o.realize hJ d hd ho) := by
  simp only [rationalWeight,budgetWeight,Rat.cast_sum,Rat.cast_inv,
    rationalBudgets_cast hJ d hd o ho]

lemma tableAccuracy_error {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) : tableAccuracy J d o*rationalWeight J d o<1/2 := by
  have hw := rationalWeight_nonneg hJ d hd o ho
  unfold tableAccuracy
  rw [one_div,inv_mul_eq_div]
  apply (div_lt_iff₀ (by positivity : 0<8*(1+rationalWeight J d o))).mpr
  linarith

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_DegreeReplacement
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.PCP.AssignmentTester

open MinUncutGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] in
theorem flipAt_eq_xor (i : A) (f : Cube A) : flipAt i f = cubeXor f (singleMask i) := by
  funext j
  by_cases h : j = i <;> simp [flipAt, cubeXor, singleMask, h]

theorem walsh_singleMask (s : Cube A) (i : A) :
    walsh s (singleMask i) = bitSign (s i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp [singleMask]
  · intro j _ hj
    simp [singleMask, hj, bitSign]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem parity_singleMask (s : Cube A) (i : A) : parity s (singleMask i) = s i := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_singleMask]

theorem parity_flipAt (s : Cube A) (i : A) (f : Cube A) (hs : s i = true) :
    parity s (flipAt i f) = !(parity s f) := by
  rw [flipAt_eq_xor, parity_xor, parity_singleMask, hs]
  cases parity s f <;> rfl

end MinUncutGames.Foundations.PCP.AssignmentTester

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySampling
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.PCP.CayleySampling

open scoped BigOperators
open Finset
open MinUncutGames.Foundations.Hastad

variable {V D : Type*}

section Walsh

variable {I : Type*} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]

theorem expect_parity_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → Bool) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => AssignmentTester.parity s (g d))) =
      𝔼 b : D → Bool, F b := by
  obtain ⟨i, hi⟩ := exists_true_of_ne_zero s hs
  exact expect_boolean_samples (AssignmentTester.parity s) (AssignmentTester.flipAt i)
    (AssignmentTester.flipAt_twice i)
    (fun x => AssignmentTester.parity_flipAt s i x hi) F

end Walsh

end MinUncutGames.Foundations.PCP.CayleySampling

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySpectral
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset
open MinUncutGames.Foundations.Hastad
open PoweringWalks

variable {I D : Type*}


variable [Fintype I] [DecidableEq I] [Fintype D]

theorem eigenvalue_powerGenerators (g : D → Cube I) (n : Nat) (s : Cube I) :
    eigenvalue (powerGenerators g n) s = eigenvalue g s ^ n := by
  induction n with
  | zero =>
    let : Nonempty (Fin 0 → D) := ⟨fun i => Fin.elim0 i⟩
    simp [eigenvalue, powerGenerators, zeroFrequency, walsh, bitSign]
  | succ n ih =>
    calc
      eigenvalue (powerGenerators g (n + 1)) s =
          𝔼 z : D × (Fin n → D),
            walsh s (cubeXor (g z.1) (powerGenerators g n z.2)) := by
        unfold eigenvalue
        apply Fintype.expect_equiv (splitPortWord n)
        intro p
        rfl
      _ = 𝔼 d, 𝔼 p : Fin n → D,
          walsh s (cubeXor (g d) (powerGenerators g n p)) := by
        exact SpectralReturn.mean_prod _
      _ = eigenvalue g s * eigenvalue (powerGenerators g n) s := by
        simp_rw [walsh_xor, ← Finset.mul_expect]
        rw [← Finset.expect_mul]
        rfl
      _ = eigenvalue g s ^ (n + 1) := by
        rw [ih, pow_succ, mul_comm]

theorem cayley_energy_contraction (g : D → Cube I) (lambda : ℝ) (_hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (f : Cube I → ℝ) (hmean : (𝔼 x, f x) = 0) :
    (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2) := by
  classical
  have hzero : coefficient f zeroFrequency = 0 := by
    rw [coefficient_zeroFrequency]
    exact hmean
  calc
    (𝔼 x, cayleyAverage g f x ^ 2) =
        ∑ s, coefficient (cayleyAverage g f) s ^ 2 := (walsh_parseval _).symm
    _ = ∑ s, (eigenvalue g s * coefficient f s) ^ 2 := by
      simp only [coefficient_cayleyAverage]
    _ ≤ ∑ s, lambda ^ 2 * coefficient f s ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s = zeroFrequency
      · subst s
        simp [hzero]
      · have hb := hbias s hs
        have hlo : -lambda ≤ eigenvalue g s := (abs_le.mp hb).1
        have hhi : eigenvalue g s ≤ lambda := (abs_le.mp hb).2
        have hprod : 0 ≤ (lambda - eigenvalue g s) * (lambda + eigenvalue g s) :=
          mul_nonneg (sub_nonneg.mpr hhi) (by linarith)
        have hsq : eigenvalue g s ^ 2 ≤ lambda ^ 2 := by nlinarith
        calc
          (eigenvalue g s * coefficient f s) ^ 2 =
              eigenvalue g s ^ 2 * coefficient f s ^ 2 := by rw [mul_pow]
          _ ≤ lambda ^ 2 * coefficient f s ^ 2 :=
            mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = lambda ^ 2 * (𝔼 x, f x ^ 2) := by
      rw [← Finset.mul_sum, walsh_parseval]

theorem cayley_spectralCertificate (g : D → Cube I) (lambda : ℝ)
    (hlambda : 0 ≤ lambda) (hlambdaone : lambda < 1)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda) :
    SpectralReturn.SpectralCertificate (cayleyGraph g) lambda where
  nonnegative := hlambda
  lt_one := hlambdaone
  contraction := by
    intro f hf
    change (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2)
    exact cayley_energy_contraction g lambda hlambda hbias f hf

theorem power_eigenvalue_bound (g : D → Cube I) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (n : Nat) (s : Cube I) (hs : s ≠ zeroFrequency) :
    |eigenvalue (powerGenerators g n) s| ≤ lambda ^ n := by
  rw [eigenvalue_powerGenerators, abs_pow]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih (hbias s hs) (abs_nonneg _) (pow_nonneg hlambda _)


end MinUncutGames.Foundations.PCP.CayleySpectral


namespace MinUncutGames.Foundations.PCP.Expanders

open scoped BigOperators
open MinUncutGames.Foundations.Hastad
open CayleySpectral

theorem mean_badFrequency_le {n m : Nat} (s : Cube (Fin n)) :
    (𝔼 g : Generators n m, badFrequency g s) ≤ 2 * (2 / 3 : ℝ) ^ m := by
  classical
  by_cases hs : s = zeroFrequency
  · simp only [badFrequency, ite_eq_left hs, Finset.expect_const_zero]
    positivity
  · have hs' : s ≠ (fun _ => false) := hs
    simp only [badFrequency, ite_eq_right hs]
    rw [CayleySampling.expect_parity_samples s hs'
      (fun w : Fin (4 * m) → Bool => if CayleyTailCount.badWord m w then (1 : ℝ) else 0)]
    exact CayleyTailCount.twoTail_probability m (by simp)

theorem mean_badMass_le (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    (𝔼 g : Generators n m, badMass g) ≤ 1 / 2 := by
  calc
    _ = ∑ s : Cube (Fin n), 𝔼 g : Generators n m, badFrequency g s := by
      unfold badMass
      rw [Finset.expect_sum_comm]
    _ ≤ ∑ _s : Cube (Fin n), 2 * (2 / 3 : ℝ) ^ m :=
      Finset.sum_le_sum (fun s _ => mean_badFrequency_le s)
    _ = (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) := by
      simp [Cube]
    _ ≤ 1 / 2 := CayleyTailCount.union_bound_le_half n m hm

theorem exists_generators (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    ∃ g : Generators n m, ∀ s : Cube (Fin n),
      s ≠ zeroFrequency → |eigenvalue g s| ≤ (1 / 2 : ℝ) := by
  classical
  have hmpos : 0 < m := by omega
  let : Nonempty (Fin (4 * m)) := ⟨⟨0, by omega⟩⟩
  have havg : (𝔼 g : Generators n m, badMass g) < (1 : ℝ) :=
    lt_of_le_of_lt (mean_badMass_le n m hm) (by norm_num)
  obtain ⟨g, _, hg⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty havg
  refine ⟨g, fun s hs => ?_⟩
  have hgood : ¬ CayleyTailCount.badWord m
      (fun d => AssignmentTester.parity s (g d)) := by
    intro hbad
    have hsingle : badFrequency g s ≤ badMass g :=
      Finset.single_le_sum (fun t _ => badFrequency_nonnegative g t) (Finset.mem_univ s)
    simp only [badFrequency, ite_eq_right hs, ite_eq_left hbad] at hsingle
    exact (not_le_of_gt hg) hsingle
  unfold eigenvalue
  simp_rw [← AssignmentTester.bitSign_parity]
  exact CayleyTailCount.not_badWord_bias m (by simp) hmpos _ hgood

theorem exists_initial_generators :
    ∃ g : Generators baseDimension initialQuarterDegree,
      ∀ s : Cube (Fin baseDimension), s ≠ zeroFrequency →
        |eigenvalue g s| ≤ (1 / 2 : ℝ) :=
  exists_generators _ _ base_arithmetic.2.1

theorem card_baseVertex : Fintype.card BaseVertex = baseDegree ^ 4 := by
  simpa only [BaseVertex, Cube, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, baseDegree] using base_arithmetic.2.2.1

theorem exists_baseGraph :
    ∃ H : PoweringWalks.PortGraph BaseVertex BasePort,
      SpectralReturn.SpectralCertificate H (1 / 100 : ℝ) := by
  obtain ⟨g, hg⟩ := exists_initial_generators
  refine ⟨cayleyGraph (powerGenerators g basePower), ?_⟩
  apply cayley_spectralCertificate
  · norm_num
  · norm_num
  · intro s hs
    exact (power_eigenvalue_bound g (1 / 2) (by norm_num) hg basePower s hs).trans
      base_arithmetic.2.2.2

end MinUncutGames.Foundations.PCP.Expanders

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ExpanderFamily
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

noncomputable def baseVertexEquiv : BaseVertex ≃ CloudPort :=
  Fintype.equivOfCardEq (card_baseVertex.trans card_cloudPort.symm)

noncomputable def baseOnCloud : PortGraph CloudPort BasePort :=
  GraphTransport.reindex (Classical.choose exists_baseGraph) baseVertexEquiv (Equiv.refl _)

theorem baseOnCloud_certificate : SpectralCertificate baseOnCloud (1 / 100 : ℝ) :=
  GraphTransport.reindex_spectralCertificate _ _ _ _ (Classical.choose_spec exists_baseGraph)

end MinUncutGames.Foundations.PCP.ExpanderFamily

namespace MinUncutGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

theorem exists_base_table : ∃ H : Table
    ((Expanders.baseDegree * Expanders.baseDegree) *
      (Expanders.baseDegree * Expanders.baseDegree)) Expanders.baseDegree,
    SpectralCertificate (graph H) (1 / 100 : ℝ) := by
  classical
  have hv : Fintype.card ExpanderFamily.CloudPort =
      (Expanders.baseDegree * Expanders.baseDegree) *
        (Expanders.baseDegree * Expanders.baseDegree) := by
    rw [ExpanderFamily.card_cloudPort]
    unfold ExpanderFamily.growth
    ring
  let vertices := Fintype.equivFinOfCardEq hv
  let ports := Fintype.equivFinOfCardEq Expanders.card_basePort
  let G := GraphTransport.reindex ExpanderFamily.baseOnCloud vertices ports
  refine ⟨ofGraph G, ?_⟩
  rw [graph_ofGraph]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    ExpanderFamily.baseOnCloud_certificate

end MinUncutGames.Foundations.PCP.ExpanderTables

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphGap
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncutGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

variable {W D B : Type*}

theorem reindex_edgeSatisfied (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B)
    (labeling : V → A) (e : E) :
    (G.reindex vertices darts labels).edgeSatisfied (labelingEquiv vertices labels labeling)
      (darts e) = G.edgeSatisfied labeling e := by
  simp [reindex, labelingEquiv, edgeSatisfied, head, Equiv.trans_apply]

end MinUncutGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SpectralCut
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

def overlayFamily (H : BaseTable) (t : GraphTables.Table) :
    ExpanderTables.Table (vertices t) internalDegree :=
  resizeTable (PreprocessingLevels.table_vertexCount_eq_paddedSize (regularVertices t))
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel (regularVertices t)))

end MinUncutGames.Foundations.PCP.PreprocessingTables

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_RawInitialTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.RawInitialTables

open Target GraphTables

theorem table_darts_positive (F : Formula) : 0 < (table F).darts := by
  rw [table_darts]; omega

end MinUncutGames.Foundations.PCP.RawInitialTables

end
section
namespace MinUncutGames.Foundations.PCP.RoundTables

def alphabet : Nat := PoweringTables.labelCount PreprocessingTables.degree walkParameter

abbrev Input := {table : GraphTables.Table // 0 < table.darts}

def initial (F : Target.Formula) : Input :=
  ⟨RawInitialTables.table F, RawInitialTables.table_darts_positive F⟩

def size (input : Input) : Nat := input.val.vertices + input.val.darts

def Satisfiable (input : Input) : Prop := (GraphTables.semantics input.val).Satisfiable

end MinUncutGames.Foundations.PCP.RoundTables

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CanonicalSamplerGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace MinUncut.PathRealization
open MinUncut.FiniteProof MinUncutGames.Foundations.Hastad.SourceOccurrences

lemma listOutput_yes {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) (hk : 1≤k)
    (s : Fin N → Bool) (hs : listFailure ds s≤k) : (listOutput ds k hk).opt≤k :=
  canonicalOutput_yes _ k hk s (by simpa only [← listFailure_eq] using hs)

lemma listOutput_no {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) (hk : 1≤k)
    (K : ℕ) (hs : ∀ s, K*k<listFailure ds s) : K*k<(listOutput ds k hk).opt :=
  canonicalOutput_no _ k hk K (by simpa only [← listFailure_eq] using hs)

lemma listFailure_extend {V W : Type*} (f : V → W) (hf : Function.Injective f)
    (ds : List (Demand V)) (s : V → Bool) :
    listFailure (ds.map (Demand.map f)) (extendAssignment f s)=listFailure ds s := by
  simp only [listFailure,List.map_map,Function.comp_def,mapDemand_extend f hf]

end MinUncut.PathRealization

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryLiteralMachine
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.BinaryLiteralMachine

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition
open MinUncutGames.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

def signWord (sign : Bool) : List Bool := encodeWord (if sign then 1 else 0)

def outputWord (tokens : List BinaryNameSearch.Token) (bits : List Bool) (sign : Bool) :
    List Bool := encodeWord (index tokens bits) ++ signWord sign

theorem literalTrace (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit malformed : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit malformed l)
    (base : K → List Bool) (tokens : List BinaryNameSearch.Token)
    (sign : Bool) (bits suffix : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (tokensCanonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (present : bits ∈ BinaryNameSearch.payloads tokens)
    (cursor : base (tape 0) = sign :: (BinaryNameMachine.frame bits ++ suffix))
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 9, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = [])
    (ambient : A) :
    (advance (TM2.step program))^[steps tokens bits]
      (some ⟨some (labels .readSign), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update (Function.update base (tape 0) suffix) (tape 8)
          ((outputWord tokens bits sign).reverse ++ base (tape 8))⟩ := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have he (i : Fin 9) (hlo : 2 ≤ i.val := by decide) (hhi : i.val ≤ 7 := by decide) :
      base (tape i) = [] := empty i hlo hhi
  let s₁ := Function.update (Function.update base (tape 7) [false]) (tape 0)
    (BinaryNameMachine.frame bits ++ suffix)
  let s₂ := Function.update (Function.update s₁ (tape 0) suffix) (tape 2) bits.reverse
  let s₃ := Function.update s₂ (tape 3) (BinaryNameSearch.stream tokens)
  let tail := BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)
  let s₄ := tapesAt (tape 3) (tape 7) s₃ tail (encodeWord (index tokens bits))
  let s₅ := Function.update s₄ (tape 3) []
  let s₆ := Function.update s₅ (tape 2) []
  let s₇ := tapesAt (tape 7) (tape 8) s₆ []
    ((encodeWord (index tokens bits)).reverse ++ s₆ (tape 8))
  let s₈ := Function.update s₇ (tape 8) ((signWord sign).reverse ++ s₇ (tape 8))
  have signRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .readSign), clean ambient, base⟩) =
      some ⟨some (labels .scanKey), clean ambient sign, s₁⟩ := by
    change some (TM2.stepAux (program (labels .readSign)) _ _) = _
    rw [atLabels .readSign]
    simp [instruction, readSign, TM2.stepAux, clean, BinaryNameCompare.clean,
      cursor, he 7, hd 0 7 (by decide), s₁]
  have s₁cursor : s₁ (tape 0) = BinaryNameMachine.frame bits ++ suffix := by simp [s₁]
  have s₁key : s₁ (tape 2) = [] := by
    simp [s₁, hd 2 0 (by decide), hd 2 7 (by decide), he 2]
  have keyRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .scanKey), clean ambient sign, s₁⟩) =
      some ⟨some (labels .copyOut), clean ambient sign, s₂⟩ := by
    let e := BinaryNameCompare.scanStateEquiv (A × Bool)
    let back := MachineStateEquiv.program e.symm program
    have atScan : back (labels .scanKey) =
        BinaryNameMachine.scan (tape 0) (tape 2) (labels .scanKey)
          (some (labels .copyOut)) malformed := by
      change MachineStateEquiv.statement e.symm (program (labels .scanKey)) = _
      rw [atLabels .scanKey]
      exact MachineStateEquiv.statement_symm_statement e _
    have backForward : MachineStateEquiv.program e back = program := by
      funext l
      change MachineStateEquiv.statement e (MachineStateEquiv.statement e.symm (program l)) = _
      exact MachineStateEquiv.statement_symm_statement e.symm _
    have initial : tapesAt (tape 0) (tape 2) s₁
        (BinaryNameMachine.frame bits ++ suffix) [] = s₁ := by
      rw [← s₁cursor, ← s₁key]
      exact tapesAt_self _ _ _
    have native := BinaryNameMachine.framedTrace (tape 0) (tape 2) (hd 0 2 (by decide))
      (labels .scanKey) (some (labels .copyOut)) malformed back atScan s₁
      ((ambient, sign), false) bits suffix [] none
    simp only [canonical, ↓reduceIte, initial, List.append_nil] at native
    have transported := MachineStateEquiv.trace e back _ _ _ native
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, e, BinaryNameCompare.scanStateEquiv, Equiv.coe_fn_mk,
      BinaryNameMachine.clean, clean, BinaryNameCompare.clean, s₂, tapesAt] using transported
  have s₂permanent : s₂ (tape 1) = BinaryNameSearch.stream tokens := by
    simpa [s₂, s₁, hd 1 0 (by decide), hd 1 2 (by decide), hd 1 7 (by decide)] using permanent
  have s₂empty (i : Fin 9) (hi : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) : s₂ (tape i) = [] := by
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [s₂, s₁, hd, he]
  have copyRun : (advance (TM2.step program))^[2 * ((BinaryNameSearch.stream tokens).length + 1)]
      (some ⟨some (labels .copyOut), clean ambient sign, s₂⟩) =
      some ⟨some (labels (.search .sign)), clean ambient sign, s₃⟩ := by
    have h := MachineCopy.copyTrace (tape 1) (tape 3) (tape 6)
      (hd 1 3 (by decide)) (hd 1 6 (by decide)) (hd 3 6 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels (.search .sign))) program
      (atLabels .copyOut) (atLabels .copyBack) s₂
      (s₂empty 6 (by simp)) ((ambient, sign), false, none) none
    simpa only [s₂permanent, s₂empty 3 (by simp), List.append_nil,
      clean, BinaryNameCompare.clean, s₃] using h
  have s₃key : s₃ (tape 2) = bits.reverse := by
    simp [s₃, s₂, hd 2 3 (by decide)]
  have s₃counter : s₃ (tape 7) = [false] := by
    simp [s₃, s₂, s₁, hd 7 3 (by decide), hd 7 2 (by decide), hd 7 0 (by decide)]
  have s₃stream : s₃ (tape 3) = BinaryNameSearch.stream tokens := by simp [s₃]
  have searchRun : (advance (TM2.step program))^[BinaryNameSearch.steps tokens bits]
      (some ⟨some (labels (.search .sign)), clean ambient sign, s₃⟩) =
      some ⟨some (labels .drainSearch), clean ambient sign, s₄⟩ := by
    have h := BinaryNameSearch.searchTrace (searchTapes tape)
      (searchTapes_injective tape distinct) (fun l => labels (.search l))
      (some (labels .drainSearch)) malformed malformed program
      (fun l => atLabels (.search l)) s₃ (ambient, sign) tokens bits [] [false]
      tokensCanonical present s₃key
      (by simpa [s₃, searchTapes, hd 4 3 (by decide)] using s₂empty 4 (by simp))
      (by simpa [s₃, searchTapes, hd 5 3 (by decide)] using s₂empty 5 (by simp))
      (by simpa [s₃, searchTapes, hd 6 3 (by decide)] using s₂empty 6 (by simp))
    have initial : tapesAt (tape 3) (tape 7) s₃ (BinaryNameSearch.stream tokens) [false] = s₃ := by
      rw [← s₃stream, ← s₃counter]
      exact tapesAt_self _ _ _
    simpa only [searchTapes, List.append_nil, initial, clean, BinaryNameSearch.clean,
      s₄, tail, encodeWord, index] using h
  have s₄stream : s₄ (tape 3) = tail := by simp [s₄, hd 3 7 (by decide)]
  have drainSearchRun : (advance (TM2.step program))^[tail.length + 1]
      (some ⟨some (labels .drainSearch), clean ambient sign, s₄⟩) =
      some ⟨some (labels .drainKey), clean ambient sign, s₅⟩ := by
    have h := MachineDrain.drainTrace (tape 3) (labels .drainSearch)
      (some (labels .drainKey)) program (atLabels .drainSearch) s₄ tail
      ((ambient, sign), false, none) none
    have initial : Function.update s₄ (tape 3) tail = s₄ := by
      rw [← s₄stream]; exact Function.update_eq_self _ _
    simpa only [initial, clean, BinaryNameCompare.clean, s₅] using h
  have s₅key : s₅ (tape 2) = bits.reverse := by
    simp [s₅, s₄, tapesAt, hd 2 3 (by decide), hd 2 7 (by decide), s₃key]
  have drainKeyRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .drainKey), clean ambient sign, s₅⟩) =
      some ⟨some (labels .emitIndex), clean ambient sign, s₆⟩ := by
    have h := MachineDrain.drainTrace (tape 2) (labels .drainKey)
      (some (labels .emitIndex)) program (atLabels .drainKey) s₅ bits.reverse
      ((ambient, sign), false, none) none
    have initial : Function.update s₅ (tape 2) bits.reverse = s₅ := by
      rw [← s₅key]; exact Function.update_eq_self _ _
    simpa only [initial, List.length_reverse, clean, BinaryNameCompare.clean, s₆] using h
  have s₆index : s₆ (tape 7) = encodeWord (index tokens bits) := by
    simp [s₆, s₅, s₄, hd 7 2 (by decide), hd 7 3 (by decide)]
  have indexRun : (advance (TM2.step program))^[index tokens bits + 2]
      (some ⟨some (labels .emitIndex), clean ambient sign, s₆⟩) =
      some ⟨some (labels .emitSign), clean ambient sign, s₇⟩ := by
    change (nextAt (Γ := Alphabet) (tape 8) program)^[index tokens bits + 2]
      (some ⟨some (labels .emitIndex), (((ambient, sign), false, none), none), s₆⟩) =
      some ⟨some (labels .emitSign), (((ambient, sign), false, none), none), s₇⟩
    have h := transferAt_fromTapes (Γ := Alphabet) (tape 7) (tape 8)
      (hd 7 8 (by decide)) id false (labels .emitIndex) (some (labels .emitSign)) program
      (atLabels .emitIndex) s₆ ((ambient, sign), false, none) none
    have time : index tokens bits + 1 + 1 = index tokens bits + 2 := by omega
    simpa only [s₆index, encodeWord_length, List.map_id_fun, id_eq, time, s₇] using h
  have emitRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .emitSign), clean ambient sign, s₇⟩) =
      some ⟨exit, clean ambient, s₈⟩ := by
    change some (TM2.stepAux (program (labels .emitSign)) _ _) = _
    rw [atLabels .emitSign]
    cases sign <;> simp [instruction, emitSign, clean, BinaryNameCompare.clean,
      TM2.stepAux, signWord, encodeWord, s₈, Function.update_idem]
  have full := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace signRun keyRun) copyRun) searchRun) drainSearchRun) drainKeyRun) indexRun) emitRun
  have finalTapes : s₈ = Function.update (Function.update base (tape 0) suffix) (tape 8)
      ((outputWord tokens bits sign).reverse ++ base (tape 8)) := by
    funext k
    by_cases h8 : k = tape 8
    · subst k
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, outputWord,
        List.reverse_append, List.append_assoc, hd]
    · by_cases h0 : k = tape 0
      · subst k
        simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd]
      · by_cases h2 : k = tape 2
        · subst k
          simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd, he 2]
        · by_cases h3 : k = tape 3
          · subst k
            simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd, he 3]
          · by_cases h7 : k = tape 7
            · subst k
              simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd, he 7]
            · simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, h8, h0, h2, h3, h7]
  simpa only [steps, tail, finalTapes] using full

end MinUncutGames.BinaryLiteralMachine

namespace MinUncutGames.BinaryRenameLoop

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition

def outputBody (tokens input : List Token) : List Bool :=
  input.flatMap (fun token => BinaryLiteralMachine.outputWord tokens token.2 token.1)

@[simp] theorem outputBody_nil (tokens : List Token) : outputBody tokens [] = [] := rfl

@[simp] theorem outputBody_cons (tokens : List Token) (token : Token) (input : List Token) :
    outputBody tokens (token :: input) =
      BinaryLiteralMachine.outputWord tokens token.2 token.1 ++ outputBody tokens input := rfl

def steps (tokens : List Token) : List Token → Nat
  | [] => 1
  | token :: input => BinaryLiteralMachine.steps tokens token.2 + 2 + steps tokens input

theorem payload_length_le_stream (tokens : List Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    bits.length ≤ (BinaryNameSearch.stream tokens).length := by
  induction tokens with
  | nil => simp at present
  | cons token tokens ih =>
      rcases List.mem_cons.mp present with equal | remaining
      · rw [equal]
        simp only [BinaryNameSearch.stream_cons, List.length_append,
          BinaryNameSearch.tokenBits, List.length_cons, BinaryNameMachine.frame_length]
        omega
      · have tail := ih remaining
        simp only [BinaryNameSearch.stream_cons, List.length_append]
        omega

theorem literal_steps_le (tokens : List Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    BinaryLiteralMachine.steps tokens bits + 2 ≤
      perLiteralBound (BinaryNameSearch.stream tokens).length := by
  have body := BinaryLiteralMachine.steps_le tokens bits present
  have size := payload_length_le_stream tokens bits present
  have sumBound : (BinaryNameSearch.stream tokens).length + bits.length ≤
      2 * (BinaryNameSearch.stream tokens).length := by omega
  have sq := Nat.mul_self_le_mul_self sumBound
  unfold perLiteralBound
  nlinarith

theorem steps_le (tokens input : List Token) (included : ∀ token ∈ input, token ∈ tokens) :
    steps tokens input ≤
      perLiteralBound (BinaryNameSearch.stream tokens).length * input.length + 1 := by
  induction input with
  | nil => simp [steps]
  | cons token input ih =>
      have present : token.2 ∈ BinaryNameSearch.payloads tokens :=
        List.mem_map.mpr ⟨token, included token (by simp), rfl⟩
      have head := literal_steps_le tokens token.2 present
      have tail := ih (fun t ht => included t (by simp [ht]))
      simp only [steps, List.length_cons]
      nlinarith

variable {K Λ A : Type} [DecidableEq K]

variable (tape : Fin 11 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done malformed : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done malformed l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem bodyTrace (tokens : List Token) (token : Token) (slot : Fin 3)
    (suffix output variableCounter clauses : List Bool)
    (canonical : BinaryNameMachine.canonical token.2 = true)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (present : token.2 ∈ BinaryNameSearch.payloads tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[BinaryLiteralMachine.steps tokens token.2 + 2]
      (some ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base (BinaryNameSearch.tokenBits token ++ suffix) output variableCounter clauses⟩) =
      some ⟨some (labels .entry), clean ambient (nextSlot slot),
        loopTapes tape base suffix
          ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
          (true :: variableCounter) (List.replicate (clauseIncrement slot) true ++ clauses)⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let initial := loopTapes tape base (BinaryNameSearch.tokenBits token ++ suffix)
    output variableCounter clauses
  have first : (advance (TM2.step program))^[1]
      (some ⟨some (labels .entry), clean ambient slot, initial⟩) =
      some ⟨some (labels (.literal .readSign)), clean ambient slot, initial⟩ := by
    simpa only [Function.iterate_one, advance_some, initial,
      BinaryNameSearch.tokenBits, List.cons_append] using
      peekStep tape distinct labels done malformed program atLabels base ambient slot token.1
        (BinaryNameMachine.frame token.2 ++ suffix) output variableCounter clauses
  have workEmpty (i : Fin 11) (lo : 2 ≤ i.val) (hi : i.val ≤ 7) :
      initial (tape i) = [] := by
    have h0 : i ≠ 0 := by intro h; subst i; omega
    have h8 : i ≠ 8 := by intro h; subst i; omega
    have h9 : i ≠ 9 := by intro h; subst i; omega
    have h10 : i ≠ 10 := by intro h; subst i; omega
    simpa [initial, loopTapes, hd i 0 h0, hd i 8 h8, hd i 9 h9, hd i 10 h10]
      using empty i lo hi
  have literal := BinaryLiteralMachine.literalTrace (literalTapes tape)
    (literalTapes_injective tape distinct) (fun l => labels (.literal l))
    (some (labels .tally)) malformed program (fun l => atLabels (.literal l))
    initial tokens token.1 token.2 suffix canonical tokensCanonical present
    (by simp [initial, literalTapes, loopTapes, BinaryNameSearch.tokenBits, hd])
    (by simpa [initial, literalTapes, loopTapes, hd] using permanent)
    (fun i lo hi => workEmpty i.castSucc.castSucc lo hi) (ambient, slot)
  have finalTapes :
      Function.update (Function.update initial (literalTapes tape 0) suffix)
        (literalTapes tape 8)
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++
          initial (literalTapes tape 8)) =
      loopTapes tape base suffix
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
        variableCounter clauses := by
    have out : initial (literalTapes tape 8) = output := by
      simp [initial, literalTapes, loopTapes, hd]
    rw [out]
    change Function.update (Function.update
      (loopTapes tape base (BinaryNameSearch.tokenBits token ++ suffix) output variableCounter clauses)
      (tape 0) suffix) (tape 8) _ = _
    rw [update_cursor tape distinct, update_output tape distinct]
  rw [finalTapes] at literal
  have tally : (advance (TM2.step program))^[1]
      (some ⟨some (labels .tally), clean ambient slot,
        loopTapes tape base suffix
          ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
          variableCounter clauses⟩) =
      some ⟨some (labels .entry), clean ambient (nextSlot slot),
        loopTapes tape base suffix
          ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
          (true :: variableCounter) (List.replicate (clauseIncrement slot) true ++ clauses)⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      tallyStep tape distinct labels done malformed program atLabels base ambient slot suffix
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
        variableCounter clauses
  have full := joinTrace (joinTrace first literal) tally
  simpa only [show 1 + BinaryLiteralMachine.steps tokens token.2 + 1 =
    BinaryLiteralMachine.steps tokens token.2 + 2 by omega] using full

theorem loopTrace (tokens input : List Token) (slot : Fin 3)
    (output variableCounter clauses : List Bool)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (included : ∀ t ∈ input, t ∈ tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[steps tokens input]
      (some ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base (BinaryNameSearch.stream input) output variableCounter clauses⟩) =
      some ⟨done, clean ambient (finalSlot input.length slot),
        loopTapes tape base [] ((outputBody tokens input).reverse ++ output)
          (List.replicate input.length true ++ variableCounter)
          (List.replicate (completedClauses input.length slot) true ++ clauses)⟩ := by
  induction input generalizing slot output variableCounter clauses with
  | nil =>
      simpa only [steps, Function.iterate_one, advance_some, BinaryNameSearch.stream_nil,
        List.length_nil, outputBody_nil, List.reverse_nil, List.nil_append,
        finalSlot, completedClauses, List.replicate_zero] using
        emptyStep tape distinct labels done malformed program atLabels base ambient
          slot output variableCounter clauses
  | cons token input ih =>
      have member := included token (by simp)
      have present : token.2 ∈ BinaryNameSearch.payloads tokens :=
        List.mem_map.mpr ⟨token, member, rfl⟩
      have first := bodyTrace tape distinct labels done malformed program atLabels base ambient
        tokens token slot (BinaryNameSearch.stream input) output variableCounter clauses
        (tokensCanonical token member) tokensCanonical present permanent empty
      have rest := ih (nextSlot slot)
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
        (true :: variableCounter) (List.replicate (clauseIncrement slot) true ++ clauses)
        (fun t ht => included t (by simp [ht]))
      have full := joinTrace first rest
      have variableEq : List.replicate input.length true ++ (true :: variableCounter) =
          List.replicate (input.length + 1) true ++ variableCounter := by
        rw [List.replicate_succ']
        simp only [List.append_assoc, List.singleton_append]
      have clauseEq : List.replicate (completedClauses input.length (nextSlot slot)) true ++
          (List.replicate (clauseIncrement slot) true ++ clauses) =
          List.replicate (completedClauses (input.length + 1) slot) true ++ clauses := by
        rw [← List.append_assoc, ← List.replicate_add]
        rfl
      simpa only [steps, BinaryNameSearch.stream_cons, List.length_cons, finalSlot,
        outputBody_cons, List.reverse_append, List.append_assoc, variableEq, clauseEq] using full

theorem triplesTrace (tokens input : List Token) (count : Nat)
    (length_eq : input.length = 3 * count) (output variableCounter clauses : List Bool)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (included : ∀ t ∈ input, t ∈ tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[steps tokens input]
      (some ⟨some (labels .entry), clean ambient 0,
        loopTapes tape base (BinaryNameSearch.stream input) output variableCounter clauses⟩) =
      some ⟨done, clean ambient 0,
        loopTapes tape base [] ((outputBody tokens input).reverse ++ output)
          (List.replicate (3 * count) true ++ variableCounter)
          (List.replicate count true ++ clauses)⟩ := by
  have h := loopTrace tape distinct labels done malformed program atLabels base ambient
    tokens input 0 output variableCounter clauses tokensCanonical included permanent empty
  simpa only [length_eq, finalSlot_triples, completedClauses_triples] using h

end MinUncutGames.BinaryRenameLoop

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryParsing
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.BinaryRenameWords

open BinaryFormula MinUncutGames.Foundations

def outputLiteral (names : List Nat) (literal : Literal) : List Bool :=
  Complexity.encodeWord (names.idxOf literal.name) ++
    Complexity.encodeWord (if literal.positive then 1 else 0)

def body (F : Formula) : List Bool :=
  (literals F.clauses).flatMap (outputLiteral (sourceNames F))

theorem encoded_clause (F : Formula) (c : Clause) (mem : c ∈ F.clauses) :
    Complexity.encodeWords (Complexity.clauseWords (BinaryOccurrenceRename.clause F c mem)) =
      (clauseLiterals c).flatMap (outputLiteral (sourceNames F)) := by
  simp [Complexity.clauseWords, Complexity.literalWords, Complexity.encodeWords,
    BinaryOccurrenceRename.clause, BinaryOccurrenceRename.literal,
    BinaryOccurrenceRename.nameIndex, clauseLiterals, outputLiteral, List.append_assoc]
  rfl

theorem encodeWords_flatMap {α : Type} (xs : List α) (f : α → List Nat) :
    Complexity.encodeWords (xs.flatMap f) =
      xs.flatMap (fun x => Complexity.encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, Complexity.encodeWords_append, ih]

theorem encoded_body (F : Formula) :
    Complexity.encodeWords ((BinaryOccurrenceRename.renamed F).clauses.flatMap
      Complexity.clauseWords) = body F := by
  rw [encodeWords_flatMap]
  change (F.clauses.attach.map (fun c => BinaryOccurrenceRename.clause F c.val c.property)).flatMap
    (fun c => Complexity.encodeWords (Complexity.clauseWords c)) = body F
  rw [List.flatMap_map]
  simp only [encoded_clause]
  have h := congrArg (fun cs : List Clause =>
    cs.flatMap (fun c => (clauseLiterals c).flatMap (outputLiteral (sourceNames F))))
    (List.attach_map_subtype_val F.clauses)
  simpa only [List.flatMap_map, body, literals, List.flatMap_assoc] using h

theorem encoded_renamed (F : Formula) :
    Complexity.formulaBits (BinaryOccurrenceRename.renamed F) =
      Complexity.encodeWord (3 * F.clauses.length) ++
        Complexity.encodeWord F.clauses.length ++ body F := by
  simp only [Complexity.formulaBits, Complexity.formulaWords, Complexity.encodeWords_append,
    Complexity.encodeWords, List.append_nil,
    BinaryOccurrenceRename.renamed_variable_count,
    BinaryOccurrenceRename.renamed_clause_count, encoded_body, List.append_assoc]

end MinUncutGames.BinaryRenameWords

namespace MinUncutGames.BinaryHeaderMachine

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition
open MinUncutGames.Reduction.MachineTransfer

section Placement

variable {K Λ A : Type} [DecidableEq K]

variable (variableTape clauses destination : K)
variable (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (cd : clauses ≠ destination)
variable (clauseStart clauseLoop variableStart variableLoop : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atClauseStart : program clauseStart = delimiter destination clauseLoop)
variable (atClauseLoop : program clauseLoop =
  loopAt clauses destination id false clauseLoop (some variableStart))
variable (atVariableStart : program variableStart = delimiter destination variableLoop)
variable (atVariableLoop : program variableLoop =
  loopAt variableTape destination id false variableLoop exit)
variable (base : K → List Bool) (ambient : A)

include vc vd cd atClauseStart atClauseLoop atVariableStart atVariableLoop

theorem headerTrace (n m : Nat) (body : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[n + m + 4]
      (some ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base
          (List.replicate n true) (List.replicate m true) body⟩) =
      some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] [] (encodeWord n ++ encodeWord m ++ body)⟩ := by
  have first := clauseDelimiterStep variableTape clauses destination clauseStart clauseLoop program
    atClauseStart base ambient (List.replicate n true) (List.replicate m true) body register
  change (advance (TM2.step program))^[1]
    (some ⟨some clauseStart, (ambient, register),
      tapes variableTape clauses destination base (List.replicate n true) (List.replicate m true) body⟩) = _ at first
  have second := clauseCounterTrace variableTape clauses destination cd clauseLoop variableStart program
    atClauseLoop base ambient m (List.replicate n true) (false :: body) none
  have third := variableDelimiterStep variableTape clauses destination variableStart variableLoop program
    atVariableStart base ambient (List.replicate n true) []
    (List.replicate m true ++ false :: body) none
  change (advance (TM2.step program))^[1]
    (some ⟨some variableStart, (ambient, none),
      tapes variableTape clauses destination base (List.replicate n true) []
        (List.replicate m true ++ false :: body)⟩) = _ at third
  have fourth := variableCounterTrace variableTape clauses destination vc vd variableLoop exit program
    atVariableLoop base ambient n [] (false :: (List.replicate m true ++ false :: body)) none
  have full := joinTrace (joinTrace (joinTrace first second) third) fourth
  have htime : ((1 + (m + 1)) + 1) + (n + 1) = n + m + 4 := by omega
  rw [htime] at full
  simpa only [encodeWord, List.append_assoc, List.singleton_append,
    List.cons_append, List.nil_append] using full

end Placement

end MinUncutGames.BinaryHeaderMachine

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineBinaryRenameMachine
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.BinaryRenameMachine


open _root_.Turing MinUncutGames.Foundations
open Complexity Complexity.MachineComposition
open MinUncutGames.Reduction.MachineTransfer

theorem headerTrace (input body : List Bool) (n m : Nat) :
    (advance machine.step)^[n + m + 4]
      (some (cfg (some .clauseStart) input [] []
        (List.replicate n true) (List.replicate m true) body)) =
      some (cfg (some .cleanup) input [] [] [] []
        (encodeWord n ++ encodeWord m ++ body)) := by
  change (advance (TM2.step program))^[n + m + 4]
    (some ⟨some .clauseStart, ((BinaryRenameLoop.clean () 0).1, none),
      tapes input [] [] (List.replicate n true) (List.replicate m true) body⟩) =
    some ⟨some .cleanup, ((BinaryRenameLoop.clean () 0).1, none),
      tapes input [] [] [] [] (encodeWord n ++ encodeWord m ++ body)⟩
  have updated (variableWord clauses output : List Bool) :
      BinaryHeaderMachine.tapes (9 : Tape) 10 11 (tapes input [] [] [] [] [])
        variableWord clauses output = tapes input [] [] variableWord clauses output := by
    funext k
    fin_cases k <;> simp [BinaryHeaderMachine.tapes, tapes]
  have h := BinaryHeaderMachine.headerTrace (9 : Tape) 10 11
    (by decide) (by decide) (by decide)
    .clauseStart .clauseLoop .variableStart .variableLoop (some .cleanup) program
    rfl rfl rfl rfl (tapes input [] [] [] [] [])
    (BinaryRenameLoop.clean () 0).1 n m body none
  simp only [updated] at h
  exact h

theorem outputBody_eq (formula : BinaryFormula.Formula) :
    BinaryRenameLoop.outputBody (BinaryRenameWords.tokens formula.clauses)
      (BinaryRenameWords.tokens formula.clauses) = BinaryRenameWords.body formula := by
  change ((BinaryRenameWords.literals formula.clauses).map BinaryRenameWords.token).flatMap
    (fun t => BinaryLiteralMachine.outputWord (BinaryRenameWords.tokens formula.clauses)
      t.2 t.1) = (BinaryRenameWords.literals formula.clauses).flatMap
        (BinaryRenameWords.outputLiteral (BinaryFormula.sourceNames formula))
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro literal _
  simp only [BinaryRenameWords.token, BinaryLiteralMachine.outputWord,
    BinaryLiteralMachine.index, BinaryLiteralMachine.signWord,
    BinaryRenameWords.payload_index, BinaryRenameWords.outputLiteral]
  rfl

theorem loopTrace (formula : BinaryFormula.Formula) :
    (advance machine.step)^[BinaryRenameLoop.steps (BinaryRenameWords.tokens formula.clauses)
        (BinaryRenameWords.tokens formula.clauses)]
      (some (cfg (some (.loop .entry)) (BinaryTokenMachine.tokens formula.clauses)
        (BinaryTokenMachine.tokens formula.clauses) [] [] [] [])) =
      some (cfg (some .restore) (BinaryTokenMachine.tokens formula.clauses) []
        (BinaryRenameWords.body formula).reverse (List.replicate (3 * formula.clauses.length) true)
        (List.replicate formula.clauses.length true) []) := by
  change (advance (TM2.step program))^[BinaryRenameLoop.steps
      (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)]
    (some ⟨some (.loop .entry), BinaryRenameLoop.clean () 0,
      tapes (BinaryTokenMachine.tokens formula.clauses) (BinaryTokenMachine.tokens formula.clauses)
        [] [] [] []⟩) =
    some ⟨some .restore, BinaryRenameLoop.clean () 0,
      tapes (BinaryTokenMachine.tokens formula.clauses) [] (BinaryRenameWords.body formula).reverse
        (List.replicate (3 * formula.clauses.length) true)
        (List.replicate formula.clauses.length true) []⟩
  let input := BinaryTokenMachine.tokens formula.clauses
  have updated (cursor output variableWord clauseWord : List Bool) :
      BinaryRenameLoop.loopTapes loopTapes (tapes input [] [] [] [] [])
        cursor output variableWord clauseWord =
      tapes input cursor output variableWord clauseWord [] := by
    funext k
    fin_cases k <;> simp [BinaryRenameLoop.loopTapes, loopTapes, tapes]
  have scratch (i : Fin 11) (lo : 2 ≤ i.val) (hi : i.val ≤ 7) :
      tapes input [] [] [] [] [] (loopTapes i) = [] := by
    have n0 : loopTapes i ≠ 0 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n1 : loopTapes i ≠ 1 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n8 : loopTapes i ≠ 8 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n9 : loopTapes i ≠ 9 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n10 : loopTapes i ≠ 10 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n11 : loopTapes i ≠ 11 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    simp [tapes, n0, n1, n8, n9, n10, n11]
  have run := BinaryRenameLoop.triplesTrace loopTapes loopTapes_injective Label.loop
    (some .restore) (some .reject) program (fun _ => rfl)
    (tapes input [] [] [] [] []) ()
    (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)
    formula.clauses.length (BinaryRenameWords.tokens_length formula.clauses) [] [] []
    (BinaryRenameWords.tokens_canonical formula.clauses) (fun _ h => h)
    (by change input = _; rw [BinaryRenameWords.tokens_stream]) scratch
  simp only [updated, BinaryRenameWords.tokens_stream, outputBody_eq, List.append_nil, input] at run
  exact run

def steps (formula : BinaryFormula.Formula) : Nat :=
  2 * ((BinaryTokenMachine.tokens formula.clauses).length + 1) +
    BinaryRenameLoop.steps (BinaryRenameWords.tokens formula.clauses)
      (BinaryRenameWords.tokens formula.clauses) +
    ((BinaryRenameWords.body formula).length + 1) + (4 * formula.clauses.length + 4) +
    ((BinaryTokenMachine.tokens formula.clauses).length + 1)

theorem renameTrace (formula : BinaryFormula.Formula) :
    (advance machine.step)^[steps formula]
      (some (initList machine (BinaryTokenMachine.tokens formula.clauses))) =
      some (haltList machine (formulaBits (BinaryOccurrenceRename.renamed formula))) := by
  have first := copyTrace (BinaryTokenMachine.tokens formula.clauses)
  have second := loopTrace formula
  have third := restoreTrace (BinaryTokenMachine.tokens formula.clauses)
    (BinaryRenameWords.body formula) (List.replicate (3 * formula.clauses.length) true)
    (List.replicate formula.clauses.length true)
  have fourth := headerTrace (BinaryTokenMachine.tokens formula.clauses)
    (BinaryRenameWords.body formula) (3 * formula.clauses.length) formula.clauses.length
  have fifth := cleanupTrace (BinaryTokenMachine.tokens formula.clauses)
    (encodeWord (3 * formula.clauses.length) ++ encodeWord formula.clauses.length ++
      BinaryRenameWords.body formula)
  have full := joinTrace (joinTrace (joinTrace (joinTrace first second) third) fourth) fifth
  have count : 3 * formula.clauses.length + formula.clauses.length + 4 =
      4 * formula.clauses.length + 4 := by omega
  simpa only [steps, initList_eq, haltList_eq, BinaryRenameWords.encoded_renamed, count] using full

theorem body_length_le (formula : BinaryFormula.Formula) :
    (BinaryRenameWords.body formula).length ≤
      9 * (BinaryTokenMachine.tokens formula.clauses).length ^ 2 +
        10 * (BinaryTokenMachine.tokens formula.clauses).length + 2 := by
  have initial := BinaryOccurrenceRename.renamed_encoding_bound formula
  rw [BinaryRenameWords.encoded_renamed] at initial
  simp only [List.length_append] at initial
  have count := clause_count_le_stream formula
  have square := Nat.mul_self_le_mul_self count
  nlinarith

theorem steps_le (formula : BinaryFormula.Formula) :
    steps formula ≤ timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length := by
  have loopBound := BinaryRenameLoop.steps_le
    (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)
    (fun _ h => h)
  rw [BinaryRenameWords.tokens_stream, BinaryRenameWords.tokens_length] at loopBound
  have literalCount : 3 * formula.clauses.length ≤
      (BinaryTokenMachine.tokens formula.clauses).length := by
    rw [BinaryTokenMachine.tokens_length]
    omega
  have product := Nat.mul_le_mul_left
    (BinaryRenameLoop.perLiteralBound (BinaryTokenMachine.tokens formula.clauses).length)
    literalCount
  have output := body_length_le formula
  have count := clause_count_le_stream formula
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold steps BinaryRenameLoop.perLiteralBound at *
  nlinarith

def outputsInTime (formula : BinaryFormula.Formula) :
    TM2OutputsInTime machine (BinaryTokenMachine.tokens formula.clauses)
      (some (formulaBits (BinaryOccurrenceRename.renamed formula)))
      (timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length) where
  steps := steps formula
  evals_in_steps := renameTrace formula
  steps_le_m := steps_le formula

end MinUncutGames.BinaryRenameMachine

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_Graph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Outer.Parameters
open MinUncut.Inner MinUncut.SourceBridge
open MinUncutGames MinUncutGames.Reduction MinUncutGames.Foundations

lemma sourceError_pos {J : ℕ} (P : Parameters J) : 0<P.sourceError := by
  apply lt_min (by norm_num)
  exact div_pos P.ho.2.1 (by exact_mod_cast P.t_pos)

lemma sourceError_budget {J : ℕ} (P : Parameters J) : (P.o.t:ℝ)*(P.sourceError:ℝ)≤P.o.b4 := by
  have hh := min_le_right (1/2:ℚ) (P.o.b4/P.o.t)
  have ht : (0:ℚ)<P.o.t := by exact_mod_cast P.t_pos
  have hh' : (P.o.t:ℚ)*P.sourceError≤P.o.b4 := by
    rw [mul_comm]
    exact (le_div_iff₀ ht).mp hh
  exact_mod_cast hh'

def baseTable : PCP.RoundTables.BaseTable := Classical.choose PCP.ExpanderTables.exists_base_table

lemma baseTable_certificate :
    PCP.SpectralReturn.SpectralCertificate (PCP.ExpanderTables.graph baseTable) (1/100:ℝ) :=
  Classical.choose_spec PCP.ExpanderTables.exists_base_table

end MinUncut.Outer.Parameters

end
end

end OAI
end


