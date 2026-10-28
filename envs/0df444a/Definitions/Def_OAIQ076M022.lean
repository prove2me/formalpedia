-- Prove2me | Definitions.Def_OAIQ076M022
-- name    : OAIQ076M022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:17:32.928117+00:00
-- url     : https://prove2.me/theorems/3ca576d8-0abf-4738-8200-d4e1a88568e4
-- title:
--   Definitions bundle OAIQ076M022 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 139 declarations of OpenAI's Lean: 31 definitions, 1 instance and 107 theorems. The definitions and types are `OAI.MinUncut.Costed.Arena.decoded_outputs`, `OAI.MinUncut.Costed.Arena.unboundedGraphMachine_outputs_base`, `OAI.MinUncut.Costed.Framed.embedded`, `OAI.MinUncut.Costed.Framed.execute`, `OAI.MinUncut.Costed.SourceWords.completeGraphProgram`, `OAI.MinUncut.Costed.SourceWords.completeGraphWords`, `OAI.MinUncut.Costed.SourceWords.graphStageProgram`, `OAI.MinUncut.Outer.Parameters.canonicalDemands`, `OAI.MinUncut.Outer.ProofFamily.cost`, `OAI.MinUncut.Outer.ProofFamily.finiteCost`, `OAI.MinUncut.Outer.ProofFamily.finiteErrors`, `OAI.MinUncut.Outer.ProofFamily.queryAnswer`, `OAI.MinUncut.Outer.SampleEnumeration.all`, `OAI.MinUncut.Outer.SampleEnumeration.elementary`, `OAI.MinUncut.Outer.SampleEnumeration.localEq`, `OAI.MinUncut.Outer.SampleEnumeration.semanticLocal`, `OAI.MinUncut.Outer.SampleEnumeration.semanticLocalEq`, `OAI.MinUncut.Outer.SampleEnumeration.tests`, `OAI.MinUncut.Outer.edgeSampleSecond`, `OAI.MinUncut.Outer.equationFraction`, `OAI.MinUncut.Outer.testFunctional`, `OAI.MinUncut.Outer.variableProof`, `OAI.MinUncutGames.Foundations.Complexity.MachineRegularTable.Top.Body`, `OAI.MinUncutGames.Foundations.PCP.FinalBooleanVerifier.cnf`, `OAI.MinUncutGames.Foundations.PCP.FinalBooleanVerifier.verifier`, `OAI.MinUncutGames.Foundations.PCP.FinalTableFormula.output`, `OAI.MinUncutGames.Foundations.PCP.VerifierToCNF.block`, `OAI.MinUncutGames.Foundations.PCP.VerifierToCNF.convert`, `OAI.MinUncutGames.Foundations.PCP.VerifierToCNF.eventBlock`, `OAI.MinUncutGames.Foundations.PCP.VerifierToCNF.splitLong`, `OAI.MinUncutGames.Foundations.PCP.VerifierToCNF.tautology`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_CenteredPointCorrelationPower`, `MinUncut_Analysis_SelectedProjectGaussianLocal`, `MinUncut_Encoding_DecodedGraphCore`, `MinUncut_Estimates_ActualBoxBound`, `MinUncut_Estimates_AnalyticOuter`, `MinUncut_Estimates_Assembly`, `MinUncut_Estimates_Away`, `MinUncut_Estimates_Basic2`, `MinUncut_Estimates_ComparisonSoundness`, `MinUncut_Estimates_CountedWordParser`, `MinUncut_Estimates_ExpectResampleRow`, `MinUncut_Estimates_InnerAssembly`, `MinUncut_Estimates_InnerUniform`, `MinUncut_Estimates_LiteralTestQueries`, `MinUncut_Estimates_PolynomialRecursor`, `MinUncut_Estimates_SamplerAssembly`, `MinUncut_Estimates_SamplerCost`, `MinUncut_Estimates_SingleRow`, `MinUncut_Estimates_TemplateExpressions`, `MinUncut_Estimates_UniformEquationOutput`, `MinUncut_Estimates_WeightedTestLaw`, `MinUncut_Games_JointCoefficient`, `MinUncut_Games_JointInner`, `MinUncut_Games_Sampling`, `MinUncut_Graphs_CanonicalPathGraph`, `MinUncut_Graphs_CanonicalSamplerGraph`, `MinUncut_Graphs_CompleteGraphProgram`, `MinUncut_Graphs_UnboundedGraphBase`, `MinUncut_Machines_FiberGraphMachine`, `MinUncut_Machines_GraphCoreMachine`, `MinUncut_PCP_FinalBooleanVerifier`, `MinUncut_PCP_PoweringFinalConstants`, `MinUncut_PCP_RawInitialTables`, `MinUncut_Search_FiniteQueryFamily`, `MinUncut_Search_Parameters`, `MinUncut_Search_RationalBasics`, `MinUncut_Search_SampleEnumeration`.
--
--   **Imports.** It imports the published bundle `Def_MinUncut`; the bundles `OAIQ076M014`, `OAIQ076M015`, `OAIQ076M016` and `OAIQ076M017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M028` and `OAIQ076M030`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_MinUncut
import Definitions.Def_OAIQ076M014
import Definitions.Def_OAIQ076M015
import Definitions.Def_OAIQ076M016
import Definitions.Def_OAIQ076M017

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_JointCoefficient
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma hermite_gradient_constantArray (f : FoldedProof A) (B : FaceArray A m n)
    (k : Row m n → F₂) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (x : Point m n) (I : Point m n → ℕ) :
    GaussianHermite.coeff (fun c => gradient f (constantArray k+B) σ η c x) I =
      BinaryFourier.sign ((rowCode k).val x + GaussianHermite.parity (rowCode k).val I) *
        GaussianHermite.coeff (fun c => gradient f B σ η c x) I := by
  simp only [constantArray_add, gradient_addConstantArray f B k hσ,
    GaussianHermite.coeff_const_mul, BinaryFourier.sign_add, mul_assoc]
  rw [GaussianHermite.coeff_diagonal (rowCode k).val (fun c => gradient f B σ η c x) I]

theorem joint_row_gauge (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ)
    (x : Point m n) (α : Module.Dual F₂ (FaceArray A m n)) (I : Point m n → ℕ)
    (hne : jointCoefficient f σ η x α I ≠ 0) (k : Row m n → F₂) :
    α (constantArray k) = (rowCode k).val x + GaussianHermite.parity (rowCode k).val I := by
  have ht := BinaryFourier.coefficient_translate
    (fun B : FaceArray A m n => GaussianHermite.coeff (fun c => gradient f B σ η c x) I)
    α (constantArray k)
  simp only [hermite_gradient_constantArray f _ k hσ, BinaryFourier.coefficient,
    mul_assoc, ← Finset.mul_expect] at ht
  apply sign_injective
  change _ * jointCoefficient f σ η x α I = _ * jointCoefficient f σ η x α I at ht
  exact mul_right_cancel₀ hne ht.symm

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SingleRow
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

theorem joint_local_odd (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ)
    (x : Point m n) (α : Module.Dual F₂ (FaceArray A m n)) (I : Point m n → ℕ)
    (hne : jointCoefficient f σ η x α I ≠ 0) (i : Fin m)
    (hi : ∀ u, 0 < I u → face u i ≠ face x i) :
    RowNoise.frequency α ⟨i,face x i⟩ (AffineMap.const F₂ A 1) = 1 := by
  have hh := joint_row_gauge f hσ η x α I hne (singleRow ⟨i,face x i⟩)
  rw [constantArray_singleRow, rowCode_singleRow, ite_eq_left rfl] at hh
  have hp : GaussianHermite.parity (rowCode (singleRow ⟨i,face x i⟩)).val I = 0 := by
    unfold GaussianHermite.parity
    apply Finset.sum_eq_zero
    intro u _
    by_cases hu : I u=0
    · simp [hu]
    · rw [rowCode_singleRow, ite_eq_right (hi u (Nat.pos_of_ne_zero hu)), zero_mul]
  rw [hp, add_zero] at hh
  exact hh

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_JointInner
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
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

lemma selectedProject_loss_energy (J K : Finset (Finset R × (ι → ℕ))) (hK : K ⊆ J)
    (u : (R → W) → (ι → ℝ) → ℝ) :
    jointEnergy (fun B c => selectedProject J u B c-selectedProject K u B c) =
      ∑ j ∈ J\K, jointEnergy (maskHermite j.1 j.2 u) := by
  simp_rw [selectedProject_sdiff J K hK]
  exact selectedProject_energy _ u
end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Away
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
attribute [local instance] Classical.propDecidable
variable {R W ι Ω : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [Fintype Ω]

lemma selectedProject_filter_loss (J : Finset (Finset R × (ι → ℕ)))
    (p : (Finset R × (ι → ℕ)) → Prop) (u : (R → W) → (ι → ℝ) → ℝ) :
    jointEnergy (fun B c => selectedProject J u B c-selectedProject (J.filter p) u B c) =
      ∑ j ∈ J, if p j then 0 else jointEnergy (maskHermite j.1 j.2 u) := by
  rw [selectedProject_loss_energy J (J.filter p) (Finset.filter_subset _ _)]
  have hs : J\J.filter p = J.filter (fun j => ¬p j) := by ext j; simp; aesop
  rw [hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp_all

lemma selectedProject_average_loss (J : Finset (Finset R × (ι → ℕ)))
    (p : Ω → (Finset R × (ι → ℕ)) → Prop) (u : (R → W) → (ι → ℝ) → ℝ)
    (δ : ℝ) (hp : ∀ j ∈ J, (𝔼 ω, if p ω j then (0:ℝ) else 1) ≤ δ) :
    (𝔼 ω, jointEnergy (fun B c => selectedProject J u B c-selectedProject (J.filter (p ω)) u B c)) ≤
      δ*jointEnergy (selectedProject J u) := by
  simp_rw [selectedProject_filter_loss]
  rw [Finset.expect_sum_comm, selectedProject_energy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hm (ω) : (if p ω j then (0:ℝ) else jointEnergy (maskHermite j.1 j.2 u)) =
      (if p ω j then (0:ℝ) else 1)*jointEnergy (maskHermite j.1 j.2 u) := by split_ifs <;> simp
  simp_rw [hm, ← Finset.expect_mul]
  exact mul_le_mul_of_nonneg_right (hp j hj) (jointEnergy_nonneg _)

end MinUncut.RowNoise
namespace MinUncut.Subbox
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A ι W : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]

lemma localization_energy_loss (x : ι → A) {k s r : ℕ} (hk : k ≤ Fintype.card A-1)
    (J : Finset (Finset (Row ι A) × ((ι → A) → ℕ)))
    (hJ : ∀ j ∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ r)
    (u : (Row ι A → W) → ((ι → A) → ℝ) → ℝ) :
    (𝔼 H : PointedBox x k, jointEnergy (fun B c => selectedProject J u B c-
      selectedProject (localizedSelection x H J) u B c)) ≤
        ((s+r:ℕ):ℝ)*((k:ℝ)/(Fintype.card A-1))*jointEnergy (selectedProject J u) := by
  change (𝔼 H : PointedBox x k, jointEnergy (fun B c => selectedProject J u B c-
    selectedProject (J.filter (fun j => ¬Removed H (positiveSupport j.2) j.1)) u B c)) ≤ _
  convert selectedProject_average_loss (R := Row ι A) (W := W) (ι := ι → A)
    (Ω := PointedBox x k) J (fun H j => ¬Removed H (positiveSupport j.2) j.1) u
    (((s+r:ℕ):ℝ)*((k:ℝ)/(Fintype.card A-1))) ?_ using 1
  · apply Finset.expect_congr rfl
    intro H _
    congr 1
    funext B c
    congr 2
    ext j
    simp
  · intro j hj
    have hp := removal_probability (x := x) hk (positiveSupport j.2) j.1
    have hcard : (positiveSupport j.2).card+j.1.card ≤ s+r :=
      Nat.add_le_add ((positiveSupport_card j.2).trans (hJ j hj).1) (hJ j hj).2
    have hc : (0:ℝ) ≤ (k:ℝ)/(Fintype.card A-1) :=
      div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast (Fintype.card_pos (α := A))))
    have hmul := mul_le_mul_of_nonneg_right (show ((positiveSupport j.2).card:ℝ)+j.1.card ≤ ((s+r:ℕ):ℝ) by exact_mod_cast hcard) hc
    refine le_trans ?_ (hp.trans hmul)
    apply Finset.expect_le_expect
    intro H _
    split_ifs <;> simp_all

end MinUncut.Subbox
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma joint_pair_matching (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ)
    (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n)) (p : PairClass m)
    (hp : PairAdmissible x I S p) (α : Module.Dual F₂ (FaceArray A m n))
    (hmask : mask α=S) (hne : jointCoefficient f σ η x α I ≠ 0) :
    frequency α ⟨p.val.1,face x p.val.1⟩ = frequency α ⟨p.val.2,face x p.val.2⟩ ∧
    frequency α ⟨p.val.1,face x p.val.1⟩ (AffineMap.const F₂ A 1)=1 := by
  have hij : p.val.1 ≠ p.val.2 := ne_of_lt p.property
  refine ⟨?_,joint_local_odd f hσ η x α I hne p.val.1 (fun u hu => (hp.1 u hu).1)⟩
  apply LinearMap.ext
  intro a
  have hh := joint_cylinder_gauge f σ η x α I hne p.val.1 p.val.2 hij x a
  rw [frequency_cylinder α x p.val.1 p.val.2 hij
    (fun y hy => hp.2.1 y (by rw [← hmask]; simpa [mask] using hy))
    (fun y hy => hp.2.2 y (by rw [← hmask]; simpa [mask] using hy))] at hh
  exact (BinaryFourier.add_eq_zero_iff _ _).mp hh

theorem retained_local_sum (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B C : FaceArray A m n) (hBC : ∀ t ∉ freePairRows x H p, B t=C t) (c : Point m n → ℝ) :
    selectedProject (retainedClass x H (some p) J) (fun B c => gradient f B σ η c x) B c =
      pairSlice f σ η x H p J C c (B ⟨p.val.1,face x p.val.1⟩+B ⟨p.val.2,face x p.val.2⟩) := by
  apply selectedProject_local_sum
  · intro he
    exact (ne_of_lt p.property) (congrArg Sigma.fst he)
  · exact local_free_left x H p
  · exact local_free_right x H p
  · exact retained_pair_local x H p J
  · intro j hj α hm hc
    exact (joint_pair_matching f hσ η x j.2 j.1 p
      (retained_pair_admissible x H p J j hj) α hm hc).1
  · exact hBC

end MinUncut.Inner
namespace MinUncut.GaussianHermite
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integral_psi_update (I : ι → ℕ) (x : ι) (C : ι → ℝ) (hx : 0<I x) :
    (∫ t, psi I (Function.update C x t) ∂γ)=0 := by
  simp only [psi_update,integral_mul_const,H_mean hx,zero_mul]

end MinUncut.GaussianHermite

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_CenteredPointCorrelationPower
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
open BinaryFourier RowNoise GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairSlice_odd (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (c : Point m n → ℝ) (b : Forms A) :
    pairSlice f σ η x Y p J B c (b+AffineMap.const F₂ A 1) =
      -pairSlice f σ η x Y p J B c b := by
  apply localSlice_odd
  intro j hj α hm hc
  exact (joint_pair_matching f hσ η x j.2 j.1 p
    (retained_pair_admissible x Y p J j hj) α hm hc).2

lemma pairSlice_coefficient_zero (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (c : Point m n → ℝ) (α : Module.Dual F₂ (Forms A))
    (ha : α (AffineMap.const F₂ A 1)≠1) : coefficient (pairSlice f σ η x Y p J B c) α=0 :=
  odd_coefficient_zero _ _ (pairSlice_odd f hσ η x Y p J B c) α ha

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_SelectedProjectGaussianLocal
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
lemma selectedProject_gaussian_mean (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (x : ι) (hJ : ∀ j ∈ J, 0<j.2 x)
    (B : R → W) (C : ι → ℝ) :
    (∫ t, selectedProject J u B (Function.update C x t) ∂γ)=0 := by
  unfold selectedProject
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j hj
    simp only [maskHermite_eq,integral_mul_const,integral_psi_update j.2 x C (hJ j hj),zero_mul]
  · intro j _
    simp only [maskHermite_eq]
    exact ((memLp_psi_update j.2 x C).mul_const _).integrable (by norm_num)
end MinUncut.RowNoise
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma gaussianSlice_mean (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (H : Subbox.PointedBox x k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, j.1.card < (m-(∑ u, j.2 u)).choose 2)
    (B : FaceArray A m n) (C : Point m n → ℝ) :
    (∫ t, gaussianSlice f σ η x H J B C t ∂γ)=0 :=
  selectedProject_gaussian_mean _ _ x (retained_zero_positive x H J hJ) B C
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_PolynomialRecursor
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.Arena

open Turing.ToPartrec

lemma safe_evalAction : Action.Safe evalAction := by
  apply safe_switch
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [evalZero,evalSucc,evalTail,evalCons,evalComp,evalCase,evalFix]
  all_goals first | apply Action.Safe.test | skip
  all_goals first | apply safe_alloc | apply safe_put
  all_goals first | exact small_reg _ | exact small_get _ _ | exact small_fresh |
    exact small_succ_get _ _ | exact small_pred_get _ _ | exact small_const _ (by omega)

lemma safe_returnAction : Action.Safe returnAction := by
  apply Action.Safe.test safe_halt
  apply safe_switch
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl
  all_goals simp only [retCons1,retCons2,retComp,retFix]
  all_goals first | apply Action.Safe.test | skip
  all_goals first | apply safe_alloc | apply safe_put
  all_goals first | exact small_reg _ | exact small_get _ _ | exact small_fresh | exact small_const _ (by omega)

lemma rawTick_safe (v : List ℕ) :
    (rawTick v).length≤v.length+9 ∧ maximum (rawTick v)≤ maximum v+3 := by
  apply Action.Safe.test safe_evalAction (Action.Safe.test ?_ safe_returnAction) v
  exact safe_put (small_reg 0) (small_reg 1) (small_reg 2) (small_reg 3)

end MinUncut.Costed.Arena

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

open scoped BigOperators
namespace MinUncut.PathRealization
open MinUncut.FiniteProof MinUncutGames.Foundations.Hastad.SourceOccurrences

lemma listFailure_demandList {E V : Type} [Fintype E] (D : ℕ) (w : E → ℚ)
    (d : E → Demand V) (enc : Encoding E) (s : V → Bool) :
    listFailure (demandList D w d enc) s=∑e, multiplicity D (w e)*failure (d e) s := by
  have h : ∀ es : List E,
      ((es.flatMap (fun e => List.replicate (multiplicity D (w e)) (d e))).map
        (fun d => failure d s)).sum =
        (es.map (fun e => multiplicity D (w e)*failure (d e) s)).sum := by
    intro es
    induction es with
    | nil => simp
    | cons e es ih =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_replicate,
        List.sum_replicate,nsmul_eq_mul,Nat.cast_id,List.map_cons,List.sum_cons,ih]
  unfold listFailure demandList
  rw [h]
  exact sum_enumerate enc _

end MinUncut.PathRealization

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ExpectResampleRow
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairSlice_measurable (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n) (b : Forms A) :
    Measurable (fun c => pairSlice f σ η x Y p J B c b) :=
  (selectedProject_continuous _ _ _).measurable

lemma pairSlice_row (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n)
    (c : Point m n → ℝ) (b : Forms A) :
    selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x)
      (joinRow ⟨p.val.1,face x p.val.1⟩ b (fun t => B t.val)) c =
      pairSlice f σ η x Y p J B c (B ⟨p.val.2,face x p.val.2⟩+b) := by
  have hrs : (⟨p.val.2,face x p.val.2⟩ : Row m n) ≠ ⟨p.val.1,face x p.val.1⟩ := by
    intro h
    exact (ne_of_lt p.property) (congrArg Sigma.fst h).symm
  rw [retained_local_sum f hσ η x Y p J _ B]
  · rw [joinRow_at, joinRow_other _ _ _ ⟨_,hrs⟩, add_comm]
  · intro t ht
    have htr : t≠⟨p.val.1,face x p.val.1⟩ := by
      intro he; subst t; exact ht (local_free_left x Y p)
    exact joinRow_other _ _ _ ⟨t,htr⟩

theorem pairSlice_energy_law (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (c : Point m n → ℝ) :
    (𝔼 B : FaceArray A m n, 𝔼 b : Forms A, (pairSlice f σ η x Y p J B c b)^2) =
      𝔼 B, (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x) B c)^2 := by
  let r : Row m n := ⟨p.val.1,face x p.val.1⟩
  let g : FaceArray A m n → ℝ := fun B =>
    (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x) B c)^2
  have hB (B : FaceArray A m n) :
      (𝔼 b : Forms A, g (joinRow r b (fun t => B t.val))) =
        𝔼 b : Forms A, (pairSlice f σ η x Y p J B c b)^2 := by
    calc
      _ = 𝔼 b : Forms A, (pairSlice f σ η x Y p J B c (B ⟨p.val.2,face x p.val.2⟩+b))^2 := by
        apply Finset.expect_congr rfl
        intro b _
        exact congrArg (fun t : ℝ => t^2) (pairSlice_row f hσ η x Y p J B c b)
      _ = _ := expect_translate (fun b => (pairSlice f σ η x Y p J B c b)^2) _
  have h := expect_resample_row r g
  simp_rw [hB] at h
  exact h

lemma pairSlice_atom_law (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (B : FaceArray A m n) (c : Point m n → ℝ) :
    oddAtom ⟨p.val.1,face x p.val.1⟩ (AffineMap.const F₂ A 1)
      (fun B => selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x) B c)
      (fun t => B t.val) = Slice.oddMax (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c) := by
  change Slice.oddMax (AffineMap.const F₂ A 1) (fun b => selectedProject _ _ (joinRow _ b _) c)=_
  simp only [pairSlice_row f hσ, Slice.oddMax_translate]

theorem pairSlice_atom_mean (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (c : Point m n → ℝ) :
    (𝔼 B : FaceArray A m n, Slice.oddMax (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c)) =
      𝔼 D, oddAtom ⟨p.val.1,face x p.val.1⟩ (AffineMap.const F₂ A 1)
        (fun B => selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x) B c) D := by
  simp_rw [← pairSlice_atom_law f hσ]
  exact expect_rest _ _
end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

theorem actual_pair_box_power (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (hm : 0 < m) {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (c : Point m n → ℝ)
    {H γ A₀ : ℝ} (hA : 0 < A₀) (hγ : 0 ≤ γ) :
    (𝔼 B : FaceArray A m n, faceCorrelation (pairProcessedOnBox f σ η Y p J H γ A₀ B c))^(2^m) ≤
      A₀^(2^m)*((m:ℝ)/(k+1)) + ((γ+H^2/A₀)^2*H^2)^(2^Fintype.card (CubeRows.Other p.val.1 p.val.2)) := by
  rw [pairProcessedOnBox_law]
  calc
    _ ≤ 𝔼 B : FaceArray A m n, (𝔼 Bj, 𝔼 Bi, faceCorrelation (pairField p.val.1 p.val.2
      (fun u => Slice.processed H γ A₀ (AffineMap.const F₂ A 1)
        (pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J B c)) Bj Bi))^(2^m) := Box.expect_pow_two_pow _ m
    _ ≤ 𝔼 _B : FaceArray A m n, (A₀^(2^m)*((m:ℝ)/(k+1)) +
        ((γ+H^2/A₀)^2*H^2)^(2^Fintype.card (CubeRows.Other p.val.1 p.val.2))) := by
      apply Finset.expect_le_expect
      intro B _
      rw [show (k : ℝ)+1=((k+1 : ℕ) : ℝ) by push_cast; rfl]
      apply pair_correlation_power hm (by omega) _ _ (ne_of_lt p.property) _ (γ+H^2/A₀) H A₀
        (by positivity) hA.le
      · intro u α
        exact Slice.processed_coefficient_le hA hγ _ _
          (pairSlice_coefficient_zero f hσ η (pointEmbed Y u) (pointBox Y u) p J B c) α
      · intro u
        exact Slice.processed_energy_le hA.le _ _
      · intro u b
        exact Slice.processed_abs_le hA.le _ _ b
    _ = _ := Fintype.expect_const _
end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma gaussianSlice_joint_continuous (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) :
    Continuous (fun p : (Point m n → ℝ) × ℝ => gaussianSlice f σ η x Y J B p.1 p.2) := by
  apply (selectedProject_continuous _ _ B).comp
  apply continuous_pi
  intro y
  by_cases he : y=x
  · subst y; simpa only [Function.update_self] using continuous_snd
  · simp only [Function.update_of_ne he]
    exact (continuous_apply y).comp continuous_fst

lemma centered_gaussianSlice_measurable (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (A₀ : ℝ) :
    Measurable (fun p : (Point m n → ℝ) × ℝ =>
      Slice.centeredClip γ A₀ (gaussianSlice f σ η x Y J B p.1) p.2) := by
  have hc : Continuous (fun p : (Point m n → ℝ) × ℝ =>
      Slice.clip A₀ (gaussianSlice f σ η x Y J B p.1 p.2)) := by
    unfold Slice.clip
    exact continuous_const.max ((gaussianSlice_joint_continuous f σ η x Y J B).min continuous_const)
  unfold Slice.centeredClip
  have hi : Measurable (fun C => ∫ t, Slice.clip A₀ (gaussianSlice f σ η x Y J B C t) ∂γ) :=
    hc.stronglyMeasurable.integral_prod_right.measurable
  exact hc.measurable.sub (hi.comp measurable_fst)

attribute [local irreducible] gaussianSlice Slice.centeredClip

lemma centered_gaussianSlice_diagonal_measurable (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (A₀ : ℝ) :
    Measurable (fun c : Point m n → ℝ =>
      Slice.centeredClip γ A₀ (gaussianSlice f σ η x Y J B c) (c x)) := by
  have hh := centered_gaussianSlice_measurable f σ η x Y J B A₀
  have hg : Measurable (fun c : Point m n → ℝ => (c,c x)) :=
    measurable_id.prodMk (measurable_pi_apply x)
  exact hh.comp hg

attribute [local irreducible] pointEmbed coordinateEnum

lemma zeroProcessedOnBox_measurable (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (A₀ : ℝ)
    (B : FaceArray A m n) (u : Point m (k+1)) :
    Measurable (fun c => zeroProcessedOnBox f σ η Y J A₀ B c u) := by
  simpa only [zeroProcessedOnBox] using
    centered_gaussianSlice_diagonal_measurable f σ η (pointEmbed Y u) (pointBox Y u) J B A₀

end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] pointEmbed coordinateEnum gaussianSlice Slice.centeredClip zeroProcessedOnBox faceCorrelation Finset.univ Fintype.piFinset
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

theorem actual_zero_box_power (f : FoldedProof A) (σ η : ℝ) (hm : 0 < m) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) {A₀ : ℝ} (hA : 0≤A₀)
    (B : FaceArray A m n) :
    (∫ c, faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c) ∂γpi (Point m n))^(2^m) ≤
      (2*A₀)^(2^m)*((m:ℝ)/(k+1)) := by
  let G := fun c => faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c)
  have hG : Measurable G := faceCorrelation_measurable_field _ (zeroProcessedOnBox_measurable f σ η Y J A₀ B)
  have hGb (c : Point m n → ℝ) : |G c|≤2*A₀ := by
    rw [abs_of_nonneg (faceCorrelation_nonneg _)]
    exact (faceCorrelation_le_l1 _).trans ((Finset.expect_le_expect (fun u _ =>
      zeroProcessedOnBox_abs_le f σ η Y J hA B c u)).trans_eq (Fintype.expect_const _))
  apply BoxGaussian.integral_split_power_bound γ (pointEmbed Y) (pointEmbed_injective Y) G hG hGb
    (fun c => faceCorrelation_nonneg _) (2^m)
  intro D
  change (∫ C, faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B
    (BoxGaussian.join (pointEmbed Y) (pointEmbed_injective Y) C D)) ∂γpi (Point m (k+1)))^(2^m)≤_
  simp_rw [zeroProcessedOnBox_join]
  rw [show (k : ℝ)+1=((k+1 : ℕ) : ℝ) by push_cast; rfl]
  exact centered_point_correlation_power γ _
    (fun u => Slice.centeredClip_continuous γ A₀ _
      (gaussianSlice_continuous f σ η (pointEmbed Y u) (pointBox Y u) J B _))
    (by positivity)
    (fun u t => Slice.centeredClip_abs_le hA (gaussianSlice_memLp f σ η (pointEmbed Y u) (pointBox Y u) J B _) t)
    (fun u => Slice.centeredClip_mean_zero hA (gaussianSlice_memLp f σ η (pointEmbed Y u) (pointBox Y u) J B _))
    hm (by omega)
end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] pointEmbed coordinateEnum pairSlice Slice.processed pairProcessedOnBox faceCorrelation
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

theorem actual_pair_box_bound (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (c : Point m n → ℝ)
    {H γ A₀ : ℝ} (hH : 0≤H) (hA : 0<A₀) (hγ : 0≤γ) :
    (𝔼 B : FaceArray A m n, faceCorrelation (pairProcessedOnBox f σ η Y p J H γ A₀ B c)) ≤
      A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹)+Real.sqrt (H*(γ+H^2/A₀)) := by
  have hm := pairClass_dimension p
  apply Box.cube_power_to_bound (Finset.expect_nonneg (fun B _ => faceCorrelation_nonneg _))
    hA.le hH (by positivity) (by positivity) hm
  have hh := actual_pair_box_power f hσ η (by omega) Y p J c (H := H) hA hγ
  simpa only [CubeRows.Other,CubeRows.card_other p.val.1 p.val.2 (ne_of_lt p.property),Fintype.card_fin] using hh

end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] pointEmbed coordinateEnum pairSlice Slice.processed pairProcessedOnBox faceCorrelation
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

theorem actual_pair_box_average (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    {H γ₀ A₀ : ℝ} (hH : 0≤H) (hA : 0<A₀) (hγ : 0≤γ₀) :
    (∫ c, (𝔼 B : FaceArray A m n,
      faceCorrelation (pairProcessedOnBox f σ η Y p J H γ₀ A₀ B c)) ∂γpi (Point m n)) ≤
      A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹)+Real.sqrt (H*(γ₀+H^2/A₀)) := by
  let G := fun c : Point m n → ℝ => 𝔼 B : FaceArray A m n,
    faceCorrelation (pairProcessedOnBox f σ η Y p J H γ₀ A₀ B c)
  have hm : Measurable G := by
    simp only [G,Finset.expect_eq_sum_div_card]
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro B _
    exact faceCorrelation_measurable_field _ (pairProcessedOnBox_c_measurable f σ η Y p J H γ₀ A₀ B)
  have hb c : |G c|≤A₀ := by
    rw [abs_of_nonneg (Finset.expect_nonneg (fun B _ => faceCorrelation_nonneg _))]
    calc
      _ ≤ 𝔼 _B : FaceArray A m n, A₀ := by
        apply Finset.expect_le_expect
        intro B _
        exact (faceCorrelation_le_l1 _).trans ((Finset.expect_le_expect (fun u _ =>
          pairProcessedOnBox_abs_le f σ η Y p J H γ₀ hA.le B c u)).trans_eq (Fintype.expect_const _))
      _ = _ := Fintype.expect_const _
  change (∫ c, G c ∂γpi (Point m n))≤_
  calc
    _ ≤ ∫ _c : Point m n → ℝ,
        A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹)+Real.sqrt (H*(γ₀+H^2/A₀)) ∂γpi (Point m n) := by
      apply integral_mono (Box.bounded_integrable hm.aestronglyMeasurable hb) (integrable_const _)
      intro c
      exact actual_pair_box_bound f hσ η Y p J c hH hA hγ
    _ = _ := by simp
end MinUncut.Inner

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

variable [Fintype S] [Nonempty S]

def equationFraction (equations : S → Equation Name) (s : Name → F₂) : ℝ :=
  (∑ i, if Satisfied s (equations i) then (1 : ℝ) else 0)/(Fintype.card S : ℝ)

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_InnerAssembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
variable {m n : ℕ}

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma class_localization_energy (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D) (a : Option (PairClass m)) :
    (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointEnergy (fun B c =>
      classField f σ η J a B c x-
      selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x) B c)) ≤
      ((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))*σ⁻¹^2 := by
  have : NeZero n := ⟨by omega⟩
  have hnR : 0 ≤ (n:ℝ)-1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let δ : ℝ := ((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))
  have hd : 0 ≤ δ := by dsimp [δ]; positivity
  have hx (x : Point m n) :
      (𝔼 Y : PointedBox x k, jointEnergy (fun B c => classField f σ η J a B c x-
        selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x) B c)) ≤
      δ*jointEnergy (fun B c => gradient f B σ η c x) := by
    have hh := localization_energy_loss (W := Forms A) x (by simpa using hk)
      (classSelection x a J) (fun j hj => hJ j (Finset.mem_filter.mp hj).1)
      (fun B c => gradient f B σ η c x)
    change (𝔼 Y : PointedBox x k, jointEnergy (fun B c => classField f σ η J a B c x-
        selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x) B c)) ≤
      ((s+D:ℕ):ℝ)*((k:ℝ)/(Fintype.card (Fin n)-1))*
        jointEnergy (selectedProject (classSelection x a J) (fun B c => gradient f B σ η c x)) at hh
    simp only [Fintype.card_fin] at hh
    exact hh.trans
      (mul_le_mul_of_nonneg_left
        (selectedProject_energy_le (classSelection x a J) _ (fun B => gradient_memLp f B hσ η x)) hd)
  calc
    _ ≤ 𝔼 x : Point m n, δ*jointEnergy (fun B c => gradient f B σ η c x) :=
      Finset.expect_le_expect (fun x _ => hx x)
    _ = δ*averagedEnergy (fun B c => gradient f B σ η c) := by
      rw [← Finset.mul_expect, averagedEnergy_eq_expect_joint _ (fun B x => gradient_memLp f B hσ η x)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (averagedEnergy_gradient_le f (by omega) hσ η) hd

lemma class_localization_l1 (f : FoldedProof A) {σ : ℝ} (hσ : 0<σ) (η : ℝ)
    (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D) (a : Option (PairClass m)) :
    (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointL1 (fun B c =>
      classField f σ η J a B c x-
      selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x) B c)) ≤
      σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) := by
  have : NeZero n := ⟨by omega⟩
  have hnR : 0 ≤ (n:ℝ)-1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have (x : Point m n) (i : Fin m) : Nonempty (OuterSmoothness.FixedSets (Away (x i)) k) :=
    OuterSmoothness.fixedSets_nonempty (by simpa [card_away] using hk)
  let u := fun (x : Point m n) (Y : PointedBox x k) B c =>
    classField f σ η J a B c x-
      selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x) B c
  have hu x Y B : MemLp (u x Y B) 2 (γpi (Point m n)) :=
    (classField_memLp f σ η J a B x).sub (memLp_selectedProject _ _ _)
  calc
    _ ≤ 𝔼 x : Point m n, 𝔼 Y : PointedBox x k, Real.sqrt (jointEnergy (u x Y)) :=
      Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun Y _ => jointL1_le_sqrt _ (hu x Y)))
    _ ≤ Real.sqrt (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointEnergy (u x Y)) := by
      apply le_trans (Finset.expect_le_expect (fun x _ => expect_sqrt_le _ (fun Y => jointEnergy_nonneg (u x Y))))
      exact expect_sqrt_le _ (fun x => Finset.expect_nonneg (fun Y _ => jointEnergy_nonneg (u x Y)))
    _ ≤ Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))*σ⁻¹^2) :=
      Real.sqrt_le_sqrt (class_localization_energy f hσ.ne' η hn hk J hJ a)
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (inv_nonneg.mpr hσ.le), mul_comm]
end MinUncut.Inner

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

attribute [local irreducible] gradient selectedProject retainedClass pairSlice pairProcessed Slice.processed

lemma pair_processing_loss_law (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ) (c : Point m n → ℝ) :
    (𝔼 B : FaceArray A m n, |selectedProject (retainedClass x Y (some p) J)
      (fun B c => gradient f B σ η c x) B c - pairProcessed f σ η x Y p J H γ A₀ B c|) =
    𝔼 B : FaceArray A m n, 𝔼 b : Forms A, |pairSlice f σ η x Y p J B c b -
      Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c) b| := by
  let r : Row m n := ⟨p.val.1,face x p.val.1⟩
  let s : Row m n := ⟨p.val.2,face x p.val.2⟩
  have hsr : s≠r := by
    intro h
    exact (ne_of_lt p.property) (congrArg Sigma.fst h).symm
  let L := fun B : FaceArray A m n => |selectedProject (retainedClass x Y (some p) J)
      (fun B c => gradient f B σ η c x) B c - pairProcessed f σ η x Y p J H γ A₀ B c|
  have hB (B : FaceArray A m n) :
      (𝔼 b : Forms A, L (joinRow r b (fun t => B t.val))) =
      𝔼 b : Forms A, |pairSlice f σ η x Y p J B c b -
        Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c) b| := by
    calc
      _ = 𝔼 b : Forms A, |pairSlice f σ η x Y p J B c (B s+b) -
          Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c) (B s+b)| := by
        apply Finset.expect_congr rfl
        intro b _
        dsimp only [L]
        rw [pairSlice_row f hσ]
        unfold pairProcessed
        rw [pairSlice_resample, joinRow_at, joinRow_other _ _ _ ⟨s,hsr⟩]
        rw [add_comm b]
      _ = _ := expect_translate (fun b => |pairSlice f σ η x Y p J B c b -
          Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c) b|) (B s)
  exact (expect_resample_row r L).symm.trans (Finset.expect_congr rfl (fun B _ => hB B))

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairProcessed_measurable (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ) (B : FaceArray A m n) :
    Measurable (pairProcessed f σ η x Y p J H γ A₀ B) := by
  unfold pairProcessed
  exact Slice.processed_measurable _ _ (pairSlice_measurable f σ η x Y p J B) _ _ _ _

lemma pairProcessed_memLp (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ : ℝ) {A₀ : ℝ} (hA : 0≤A₀)
    (B : FaceArray A m n) : MemLp (pairProcessed f σ η x Y p J H γ A₀ B) 2 (γpi (Point m n)) := by
  unfold pairProcessed
  exact Slice.processed_memLp _ _ (pairSlice_measurable f σ η x Y p J B) hA _

lemma pairSlice_jointEnergy (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) :
    (𝔼 B : FaceArray A m n, ∫ c, Slice.energy (pairSlice f σ η x Y p J B) c ∂γpi (Point m n)) =
      jointEnergy (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x)) := by
  rw [← integral_expect _ (fun B => Slice.energy_integrable _ (pairSlice_memLp f σ η x Y p J B))]
  change (∫ c, (𝔼 B : FaceArray A m n, 𝔼 b : Forms A,
    (pairSlice f σ η x Y p J B c b)^2) ∂γpi (Point m n)) = _
  simp_rw [pairSlice_energy_law f hσ]
  exact integral_expect _ (fun B => (memLp_selectedProject _ _ B).integrable_sq)

lemma pair_processing_loss_integral (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) {H γ A₀ : ℝ}
    (hH : 0<H) (hγ : 0<γ) (hA : 0<A₀) :
    jointL1 (fun B c => selectedProject (retainedClass x Y (some p) J)
      (fun B c => gradient f B σ η c x) B c - pairProcessed f σ η x Y p J H γ A₀ B c) ≤
      jointEnergy (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x))/H +
      Real.sqrt (jointEnergy (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x))) *
        Real.sqrt ((𝔼 B : FaceArray A m n, ∫ c, Slice.oddMax (AffineMap.const F₂ A 1)
          (pairSlice f σ η x Y p J B c) ∂γpi (Point m n))/γ) +
      jointEnergy (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x))/A₀ := by
  have hi B : Integrable (fun c => |selectedProject (retainedClass x Y (some p) J)
      (fun B c => gradient f B σ η c x) B c - pairProcessed f σ η x Y p J H γ A₀ B c|) (γpi (Point m n)) :=
    ((memLp_selectedProject _ _ _).sub (pairProcessed_memLp f σ η x Y p J H γ hA.le B)).integrable (by norm_num) |>.abs
  have hj B : Integrable (fun c => 𝔼 b : Forms A, |pairSlice f σ η x Y p J B c b -
      Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c) b|) (γpi (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    apply Integrable.div_const
    apply integrable_finsetSum
    intro b _
    exact ((pairSlice_memLp f σ η x Y p J B b).sub
      (Slice.processed_memLp _ _ (pairSlice_measurable f σ η x Y p J B) hA.le b)).integrable (by norm_num) |>.abs
  have hh := Slice.processed_average_integral_loss (μ := γpi (Point m n)) (AffineMap.const F₂ A 1)
    (pairSlice f σ η x Y p J) (pairSlice_measurable f σ η x Y p J) (pairSlice_memLp f σ η x Y p J) hH hγ hA
  rw [pairSlice_jointEnergy f hσ] at hh
  apply le_trans ?_ hh
  unfold jointL1
  rw [← integral_expect _ hi, ← integral_expect _ hj]
  exact le_of_eq (integral_congr_ae (ae_of_all _ (pair_processing_loss_law f hσ η x Y p J H γ A₀)))

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairSlice_atom_integral_law (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) :
    (𝔼 B : FaceArray A m n, ∫ c, Slice.oddMax (AffineMap.const F₂ A 1)
        (pairSlice f σ η x Y p J B c) ∂γpi (Point m n)) =
      𝔼 D, ∫ c, oddAtom ⟨p.val.1,face x p.val.1⟩ (AffineMap.const F₂ A 1)
        (fun B => selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x) B c) D ∂γpi (Point m n) := by
  rw [← integral_expect _ (fun B => (Slice.oddMax_memLp _ _
    (pairSlice_memLp f σ η x Y p J B)).integrable (by norm_num))]
  simp_rw [pairSlice_atom_mean f hσ]
  exact integral_expect _ (fun D => (memLp_oddAtom _ _ _ (memLp_selectedProject _ _) D).integrable (by norm_num))

lemma retained_energy_le (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : PointedBox x k) (a : Option (PairClass m))
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) :
    jointEnergy (selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x)) ≤
      jointEnergy (fun B c => gradient f B σ η c x) :=
  selectedProject_energy_le _ _ (fun B => gradient_memLp f B hσ η x)
end MinUncut.Inner

open scoped BigOperators
variable {m n : ℕ}

open scoped BigOperators
variable {m n : ℕ}

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient selectedProject retainedClass pairSlice pairProcessed Slice.processed
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairAtomMean_uniform_le (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k s : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, GaussianHermite.degree j.2 ≤ s) :
    pairAtomMean f σ η x Y p J ≤
      (4:ℝ)^Fintype.card (Row m n) * ((Fintype.card (Point m n)+s).choose s:ℝ) * Real.sqrt
        (𝔼 D, ∫ c, (oddAtom ⟨p.val.1,face x p.val.1⟩ (AffineMap.const F₂ A 1)
          (fun B => gradient f B σ η c x) D)^2 ∂γpi (Point m n)) := by
  unfold pairAtomMean
  rw [pairSlice_atom_integral_law f hσ]
  apply selectedProject_atom_mean_uniform s _ _ _ _ _ (fun B => gradient_memLp f B hσ η x)
  intro j hj
  apply hJ j
  unfold retainedClass classSelection at hj
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1

lemma pair_processing_loss_average (f : FoldedProof A) {σ : ℝ} (hσ : 0<σ) (η : ℝ)
    (hn : 0<n) {k : ℕ} (hk : k≤n-1) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    {H γ A₀ : ℝ} (hH : 0<H) (hγ : 0<γ) (hA : 0<A₀) :
    (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointL1 (fun B c =>
      selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x) B c -
        pairProcessed f σ η x Y p J H γ A₀ B c)) ≤
      Slice.lossBound H γ A₀ (σ⁻¹^2) (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, pairAtomMean f σ η x Y p J) := by
  have : NeZero n := ⟨by omega⟩
  have (x : Point m n) (i : Fin m) : Nonempty (OuterSmoothness.FixedSets (Away (x i)) k) :=
    OuterSmoothness.fixedSets_nonempty (by simpa [card_away] using hk)
  let E := fun (x : Point m n) (Y : PointedBox x k) =>
    jointEnergy (selectedProject (retainedClass x Y (some p) J) (fun B c => gradient f B σ η c x))
  let q := pairAtomMean f σ η (k := k) (p := p) (J := J)
  have hE x Y : 0≤E x Y := jointEnergy_nonneg _
  have hq x Y : 0≤q x Y := pairAtomMean_nonneg _ _ _ _ _ _ _
  have hcap : (𝔼 x, 𝔼 Y, E x Y) ≤ σ⁻¹^2 := by
    calc
      _ ≤ 𝔼 x : Point m n, 𝔼 _Y : PointedBox x k, jointEnergy (fun B c => gradient f B σ η c x) :=
        Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun Y _ => retained_energy_le f hσ.ne' η x Y (some p) J))
      _ = averagedEnergy (fun B c => gradient (m := m) (n := n) f B σ η c) := by
        simp only [Fintype.expect_const]
        exact (averagedEnergy_eq_expect_joint _ (fun B x => gradient_memLp f B hσ.ne' η x)).symm
      _ ≤ _ := averagedEnergy_gradient_le f hn hσ.ne' η
  calc
    _ ≤ 𝔼 x, 𝔼 Y, Slice.lossBound H γ A₀ (E x Y) (q x Y) :=
      Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun Y _ =>
        pair_processing_loss_integral f hσ.ne' η x Y p J hH hγ hA))
    _ ≤ 𝔼 x, Slice.lossBound H γ A₀ (𝔼 Y, E x Y) (𝔼 Y, q x Y) :=
      Finset.expect_le_expect (fun x _ => Slice.lossBound_expect H γ A₀ _ _ hγ.le (hE x) (hq x))
    _ ≤ Slice.lossBound H γ A₀ (𝔼 x, 𝔼 Y, E x Y) (𝔼 x, 𝔼 Y, q x Y) :=
      Slice.lossBound_expect H γ A₀ _ _ hγ.le
        (fun x => Finset.expect_nonneg (fun Y _ => hE x Y)) (fun x => Finset.expect_nonneg (fun Y _ => hq x Y))
    _ ≤ _ := Slice.lossBound_mono hH.le hγ.le hA.le hcap le_rfl
end MinUncut.Inner

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_AnalyticOuter
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

lemma weighted_pairAtomMean (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ) (hw1 : ∑ ξ, w ξ=1)
    (f : ∀ ξ, FoldedProof (A ξ)) {σ θ p : ℝ} (hσ : 0 < σ) (hθ : 0 ≤ θ) (η : ℝ)
    (hn : 0 < n) {k s : ℕ} (hk : k ≤ n-1) (r : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, GaussianHermite.degree j.2 ≤ s)
    (hp : (∑ ξ, w ξ*atomProbability (m := m) (n := n) (f ξ) σ η θ) ≤ p) :
    (∑ ξ, w ξ*(𝔼 x : Point m n, 𝔼 Y : PointedBox x k, pairAtomMean (f ξ) σ η x Y r J)) ≤
      (4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ)*
        Real.sqrt (θ^2+(m:ℝ)*p*(n^m:ℕ)/σ^2) := by
  have : NeZero n := ⟨by omega⟩
  have (x : Point m n) (i : Fin m) : Nonempty (OuterSmoothness.FixedSets (Away (x i)) k) :=
    OuterSmoothness.fixedSets_nonempty (by simpa [card_away] using hk)
  let C := (4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ)
  let E (ξ : Ξ) (x : Point m n) := 𝔼 D, ∫ c, (rowAtom (f ξ) σ η x r.val.1 D c)^2 ∂γpi (Point m n)
  have hE ξ x : 0 ≤ E ξ x := Finset.expect_nonneg (fun D _ => integral_nonneg (fun c => sq_nonneg _))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hξ (ξ : Ξ) : (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, pairAtomMean (f ξ) σ η x Y r J) ≤
      C*Real.sqrt (𝔼 x : Point m n, E ξ x) := by
    calc
      _ ≤ 𝔼 x : Point m n, 𝔼 _Y : PointedBox x k, C*Real.sqrt (E ξ x) := by
        apply Finset.expect_le_expect
        intro x _
        apply Finset.expect_le_expect
        intro Y _
        unfold E C rowAtom
        exact pairAtomMean_uniform_le (f ξ) hσ.ne' η x Y r J hJ
      _ = C*(𝔼 x : Point m n, Real.sqrt (E ξ x)) := by
        simp only [Fintype.expect_const,← Finset.mul_expect]
      _ ≤ _ := mul_le_mul_of_nonneg_left (expect_sqrt_le _ (hE ξ)) hC
  calc
    _ ≤ ∑ ξ, w ξ*(C*Real.sqrt (𝔼 x : Point m n, E ξ x)) :=
      Finset.sum_le_sum (fun ξ _ => mul_le_mul_of_nonneg_left (hξ ξ) (hw ξ))
    _ = C*(∑ ξ, w ξ*Real.sqrt (𝔼 x : Point m n, E ξ x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    _ ≤ C*Real.sqrt (∑ ξ, w ξ*(𝔼 x : Point m n, E ξ x)) :=
      mul_le_mul_of_nonneg_left (Average.weighted_sqrt _ _ hw hw1 (fun ξ => Finset.expect_nonneg (fun x _ => hE ξ x))) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (weighted_row_secondMoment V A w hw hw1 f hσ hθ η hn r.val.1 hp)) hC
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ActualBoxBound
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] pointEmbed coordinateEnum gaussianSlice Slice.centeredClip zeroProcessedOnBox faceCorrelation
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

theorem actual_zero_box_bound (f : FoldedProof A) (σ η : ℝ) (hm : 0 < m) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) {A₀ : ℝ} (hA : 0≤A₀)
    (B : FaceArray A m n) :
    (∫ c, faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c) ∂γpi (Point m n)) ≤
      2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) := by
  have hx : 0≤∫ c, faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c) ∂γpi (Point m n) :=
    integral_nonneg (fun c => faceCorrelation_nonneg _)
  have hd : 0≤(m:ℝ)/(k+1) := by positivity
  have hq : (2^m:ℕ)≠0 := by positivity
  apply (pow_le_pow_iff_left₀ hx (by positivity) hq).mp
  rw [mul_pow,Real.rpow_inv_natCast_pow hd hq]
  exact actual_zero_box_power f σ η hm Y J hA B

theorem actual_zero_box_average (f : FoldedProof A) (σ η : ℝ) (hm : 0 < m) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) {A₀ : ℝ} (hA : 0≤A₀) :
    (∫ c, (𝔼 B : FaceArray A m n,
      faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c)) ∂γpi (Point m n)) ≤
      2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) := by
  have hb (B : FaceArray A m n) (c : Point m n → ℝ) :
      |faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c)|≤2*A₀ := by
    rw [abs_of_nonneg (faceCorrelation_nonneg _)]
    exact (faceCorrelation_le_l1 _).trans ((Finset.expect_le_expect (fun u _ =>
      zeroProcessedOnBox_abs_le f σ η Y J hA B c u)).trans_eq (Fintype.expect_const _))
  rw [Box.integral_expect _ (fun B => Box.bounded_integrable
    (faceCorrelation_measurable_field _ (zeroProcessedOnBox_measurable f σ η Y J A₀ B)).aestronglyMeasurable (hb B))]
  exact (Finset.expect_le_expect (fun B _ => actual_zero_box_bound f σ η hm Y J hA B)).trans_eq
    (Fintype.expect_const _)
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_Parameters
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetFintype _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)] {m n : ℕ}

theorem source_lowGradient_energy (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ)
    (hw1 : ∑ ξ, w ξ=1) (f : ∀ ξ, FoldedProof (A ξ)) {J : ℝ} (hJ : 1 ≤ J)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : ℕ)
    (hs : ∀ k : ℕ, s+2 ≤ k → (k:ℝ)*(smoothingRho (sourceSigma J))^(2*k) ≤ 1/16)
    (h1 : (∑ ξ, w ξ*firstError (m := m) (n := n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J*(10*sourceSigma J))
    (h2 : (∑ ξ, w ξ*secondError (m := m) (n := n) (f ξ)
      ((sourceEta J)^2/(m:ℝ)) (sourceSigma J) (sourceEta J)) ≤ J*(10*(sourceEta J+sourceEta J))) :
    1/2 ≤ (∑ ξ, w ξ*averagedEnergy
      (lowGradient (m := m) (n := n) (sourceR J*m) s (f ξ) (sourceSigma J) (sourceEta J))) ∧
    (∑ ξ, w ξ*averagedEnergy
      (lowGradient (m := m) (n := n) (sourceR J*m) s (f ξ) (sourceSigma J) (sourceEta J))) ≤
        (sourceSigma J)⁻¹^2 := by
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  have hσ := sourceSigma_pos hJ
  have hη := sourceEta_pos hJ
  obtain ⟨ha,ha1,hD⟩ := source_row_rate hJ hm0
  have hL := lowGradient_energy_lower_weighted (m := m) (n := n) V A w hw hw1 f hn0 hσ.ne' hη.ne' ha ha1
    (by norm_num : (0:ℝ) ≤ 1/16) (sourceR J*m) s hD hs
  have hJ0 : J≠0 := ne_of_gt (by linarith)
  have hc1 : 4*(J*(10*sourceSigma J))=1/64 := by
    unfold sourceSigma
    field_simp
    ring
  have hc2 : 8*(sourceSigma J)⁻¹^2*(J*(10*(sourceEta J+sourceEta J)))=1/16 := by
    unfold sourceEta sourceSigma
    field_simp
    ring
  have hf1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 4)
  have hf2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 8*(sourceSigma J)⁻¹^2 by positivity)
  rw [hc1] at hf1
  rw [hc2] at hf2
  constructor
  · linarith
  · calc
      _ ≤ ∑ ξ, w ξ*(sourceSigma J)⁻¹^2 := Finset.sum_le_sum
        (fun ξ _ => mul_le_mul_of_nonneg_left
          (averagedEnergy_lowGradient_le (m := m) (sourceR J*m) s (f ξ) hn0 hσ.ne' (sourceEta J)) (hw ξ))
      _ = _ := by rw [← Finset.sum_mul,hw1,one_mul]

theorem source_lowGradient_correlation (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ)
    (hw1 : ∑ ξ, w ξ=1) (f : ∀ ξ, FoldedProof (A ξ)) {J : ℝ} (hJ : 1 ≤ J)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : ℕ)
    (hs : ∀ k : ℕ, s+2 ≤ k → (k:ℝ)*(smoothingRho (sourceSigma J))^(2*k) ≤ 1/16)
    (h1 : (∑ ξ, w ξ*firstError (m := m) (n := n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J*(10*sourceSigma J))
    (h2 : (∑ ξ, w ξ*secondError (m := m) (n := n) (f ξ)
      ((sourceEta J)^2/(m:ℝ)) (sourceSigma J) (sourceEta J)) ≤ J*(10*(sourceEta J+sourceEta J)))
    (h3 : (∑ ξ, w ξ*thirdError (m := m) (n := n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J/(Fintype.card (Code m n):ℝ)) :
    1/(4*(sourceT J:ℝ)) ≤ ∑ ξ, w ξ*averagedCorrelation
      (lowGradient (m := m) (n := n) (sourceR J*m) s (f ξ) (sourceSigma J) (sourceEta J)) := by
  have hn0 : 0 < n := by omega
  have hσ := sourceSigma_pos hJ
  have hη := sourceEta_pos hJ
  have hT : (0:ℝ) < sourceT J := by exact_mod_cast sourceT_pos hJ
  obtain ⟨hE,hE'⟩ := source_lowGradient_energy V A w hw hw1 f hJ hm hn s hs h1 h2
  have hU := lowGradient_correlation_truncated_weighted (m := m) (n := n) V A (sourceR J*m) s w hw f hn0 hσ.ne' hη hT
    (show 0 < (sourceSigma J)^2/8 by positivity)
  have he := mul_le_mul_of_nonneg_left hE'
    (show 0 ≤ (sourceSigma J)^2/8 by positivity)
  have hea : ((sourceSigma J)^2/8)*(sourceSigma J)⁻¹^2=1/8 := by field_simp
  rw [hea] at he
  have hc : (0:ℝ) < Fintype.card (Code m n) := by positivity
  have hz := mul_le_mul_of_nonneg_left h3
    (show 0 ≤ ((sourceSigma J)⁻¹^2/(4*((sourceSigma J)^2/8)*(sourceT J:ℝ)))*
      ((Fintype.card (Code m n):ℝ)/sourceEta J) by positivity)
  have hzb : ((sourceSigma J)⁻¹^2/(4*((sourceSigma J)^2/8)*(sourceT J:ℝ)))*
      ((Fintype.card (Code m n):ℝ)/sourceEta J)*(J/(Fintype.card (Code m n):ℝ)) =
      2*J/(sourceEta J*(sourceSigma J)^4*(sourceT J:ℝ)) := by
    field_simp
    ring
  rw [hzb] at hz
  have hzt : 2*J/(sourceEta J*(sourceSigma J)^4*(sourceT J:ℝ)) ≤ 1/16 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sourceT_bound hJ]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 4*(sourceT J:ℝ))).mpr
  nlinarith
end MinUncut.Inner

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Assembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
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

lemma zeroProcessed_measurable (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (A₀ : ℝ)
    (B : FaceArray A m n) : Measurable (zeroProcessed f σ η x Y J A₀ B) :=
  centered_gaussianSlice_diagonal_measurable f σ η x Y J B A₀

lemma zeroProcessed_memLp (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    {A₀ : ℝ} (hA : 0≤A₀) (B : FaceArray A m n) :
    MemLp (zeroProcessed f σ η x Y J A₀ B) 2 (γpi (Point m n)) := by
  unfold zeroProcessed gaussianSlice
  exact centered_resample_memLp x _ (selectedProject_continuous _ _ _).measurable hA

lemma zero_processing_loss_integral (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, j.1.card < (m-(∑ u, j.2 u)).choose 2)
    {A₀ : ℝ} (hA : 0<A₀) :
    jointL1 (fun B c => selectedProject (retainedClass x Y none J) (fun B c => gradient f B σ η c x) B c -
      zeroProcessed f σ η x Y J A₀ B c) ≤
      2*jointEnergy (selectedProject (retainedClass x Y none J) (fun B c => gradient f B σ η c x))/A₀ := by
  have hB (B : FaceArray A m n) := centered_resample_loss x
    (selectedProject (retainedClass x Y none J) (fun B c => gradient f B σ η c x) B)
    (selectedProject_continuous _ _ _).measurable (memLp_selectedProject _ _ _)
    (fun C => gaussianSlice_memLp f σ η x Y J B C)
    (fun C => gaussianSlice_mean f σ η x Y J hJ B C) hA
  unfold jointL1 jointEnergy
  simp only [Finset.mul_expect, Finset.expect_div]
  apply Finset.expect_le_expect
  intro B _
  unfold zeroProcessed
  exact hB B

lemma zero_processing_loss_average (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (hn : 0<n) {k : ℕ} (hk : k≤n-1)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, j.1.card < (m-(∑ u, j.2 u)).choose 2)
    {A₀ : ℝ} (hA : 0<A₀) :
    (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointL1 (fun B c =>
      selectedProject (retainedClass x Y none J) (fun B c => gradient f B σ η c x) B c -
        zeroProcessed f σ η x Y J A₀ B c)) ≤ 2*(σ⁻¹^2)/A₀ := by
  have : NeZero n := ⟨by omega⟩
  have (x : Point m n) (i : Fin m) : Nonempty (OuterSmoothness.FixedSets (Away (x i)) k) :=
    OuterSmoothness.fixedSets_nonempty (by simpa [card_away] using hk)
  calc
    _ ≤ 𝔼 x : Point m n, 𝔼 Y : PointedBox x k,
        2*jointEnergy (selectedProject (retainedClass x Y none J) (fun B c => gradient f B σ η c x))/A₀ :=
      Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun Y _ => zero_processing_loss_integral f σ η x Y J hJ hA))
    _ ≤ 𝔼 x : Point m n, 𝔼 _Y : PointedBox x k,
        2*jointEnergy (fun B c => gradient f B σ η c x)/A₀ := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.expect_le_expect
      intro Y _
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (retained_energy_le f hσ η x Y none J) (by norm_num)) hA.le
    _ = 2*averagedEnergy (fun B c => gradient (m := m) (n := n) f B σ η c)/A₀ := by
      simp only [Fintype.expect_const, ← Finset.expect_div, ← Finset.mul_expect]
      rw [averagedEnergy_eq_expect_joint _ (fun B x => gradient_memLp f B hσ η x)]
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (averagedEnergy_gradient_le f hn hσ η) (by norm_num)) hA.le

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] classField pairSlice Slice.processed gaussianSlice
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma class_correlation_processing (f : FoldedProof A) {σ : ℝ} (hσ : 0 < σ) (η : ℝ)
    (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1) (a : Option (PairClass m))
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D)
    (v : (x : Point m n) → PointedBox x k → FaceArray A m n → (Point m n → ℝ) → ℝ)
    (hvm : ∀ x Y B, Measurable (v x Y B))
    (hv : ∀ x Y B, MemLp (v x Y B) 2 (γpi (Point m n))) :
    averagedCorrelation (classField f σ η J a) ≤
      σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) +
      (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, jointL1 (fun B c =>
        selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x) B c-v x Y B c)) +
      (𝔼 Y : UnpointedBox (Fin m) (Fin n) k, 𝔼 B : FaceArray A m n,
        ∫ c, faceCorrelation (fun t : Point m (k+1) => v (pointEmbed Y t) (pointBox Y t) B c) ∂γpi (Point m n)) := by
  have hcmp := averagedCorrelation_pointed_compare hk (classField f σ η J a) v
    (classField_measurable f σ η J a) (fun B x => (classField_memLp f σ η J a B x).integrable (by norm_num))
    hvm (fun x Y B => (hv x Y B).integrable (by norm_num))
  have ht (x : Point m n) (Y : PointedBox x k) := jointL1_sub_triangle
    (fun B c => classField f σ η J a B c x)
    (selectedProject (retainedClass x Y a J) (fun B c => gradient f B σ η c x)) (v x Y)
    (fun B => classField_memLp f σ η J a B x) (memLp_selectedProject _ _) (hv x Y)
  have hta := Finset.expect_le_expect (fun x (_ : x∈(Finset.univ : Finset (Point m n))) =>
    Finset.expect_le_expect (fun Y (_ : Y∈(Finset.univ : Finset (PointedBox x k))) => ht x Y))
  simp only [Finset.expect_add_distrib] at hta
  have hl := class_localization_l1 f hσ η hn hk J hJ a
  linarith only [hcmp,hta,hl]

lemma pair_class_correlation (f : FoldedProof A) {σ : ℝ} (hσ : 0 < σ) (η : ℝ)
    (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D)
    {H γ A₀ : ℝ} (hH : 0 < H) (hγ : 0 < γ) (hA : 0 < A₀) :
    averagedCorrelation (classField f σ η J (some p)) ≤
      σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) +
      Slice.lossBound H γ A₀ (σ⁻¹^2) (𝔼 x : Point m n, 𝔼 Y : PointedBox x k, pairAtomMean f σ η x Y p J) +
      A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) + Real.sqrt (H*(γ+H^2/A₀)) := by
  have : Nonempty (OuterSmoothness.FixedSets (Fin n) (k+1)) :=
    OuterSmoothness.fixedSets_nonempty (by simp only [Fintype.card_fin]; omega)
  have hc := class_correlation_processing f hσ η hn hk (some p) J hJ
    (fun x Y => pairProcessed f σ η x Y p J H γ A₀)
    (fun x Y B => pairProcessed_measurable f σ η x Y p J H γ A₀ B)
    (fun x Y B => pairProcessed_memLp f σ η x Y p J H γ hA.le B)
  have hl := pair_processing_loss_average f hσ η (by omega : 0 < n) hk p J hH hγ hA
  have hb (Y : UnpointedBox (Fin m) (Fin n) k) :
      (𝔼 B : FaceArray A m n, ∫ c, faceCorrelation (pairProcessedOnBox f σ η Y p J H γ A₀ B c) ∂γpi (Point m n)) ≤
      A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) + Real.sqrt (H*(γ+H^2/A₀)) := by
    have hi (B : FaceArray A m n) : Integrable (fun c =>
        faceCorrelation (pairProcessedOnBox f σ η Y p J H γ A₀ B c)) (γpi (Point m n)) := by
      apply faceCorrelation_integrable _ (fun t => pairProcessedOnBox_c_measurable f σ η Y p J H γ A₀ B t)
      intro t
      exact
        (pairProcessed_memLp f σ η (pointEmbed Y t) (pointBox Y t) p J H γ hA.le B).integrable (by norm_num : (1:ENNReal) ≤ 2)
    rw [← integral_expect _ hi]
    exact actual_pair_box_average f hσ.ne' η Y p J hH.le hA hγ.le
  have hba := Finset.expect_le_expect (fun Y (_ : Y∈(Finset.univ : Finset (UnpointedBox (Fin m) (Fin n) k))) => hb Y)
  rw [Fintype.expect_const] at hba
  unfold pairProcessedOnBox at hba
  dsimp only [pairProcessed] at hc hl
  linarith only [hc,hl,hba]

lemma zero_class_correlation (f : FoldedProof A) {σ : ℝ} (hσ : 0 < σ) (η : ℝ)
    (hm : 0 < m) (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D)
    (hJ0 : ∀ j∈ J, j.1.card < (m-(∑ u, j.2 u)).choose 2)
    {A₀ : ℝ} (hA : 0 < A₀) :
    averagedCorrelation (classField f σ η J none) ≤
      σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) + 2*(σ⁻¹^2)/A₀ +
      2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) := by
  have : Nonempty (OuterSmoothness.FixedSets (Fin n) (k+1)) :=
    OuterSmoothness.fixedSets_nonempty (by simp only [Fintype.card_fin]; omega)
  have hc := class_correlation_processing f hσ η hn hk none J hJ
    (fun x Y => zeroProcessed f σ η x Y J A₀)
    (fun x Y B => zeroProcessed_measurable f σ η x Y J A₀ B)
    (fun x Y B => zeroProcessed_memLp f σ η x Y J hA.le B)
  have hl := zero_processing_loss_average f hσ.ne' η (by omega : 0 < n) hk J hJ0 hA
  have hb (Y : UnpointedBox (Fin m) (Fin n) k) :
      (𝔼 B : FaceArray A m n, ∫ c, faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c) ∂γpi (Point m n)) ≤
      2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) := by
    have hi (B : FaceArray A m n) : Integrable (fun c =>
        faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c)) (γpi (Point m n)) := by
      apply faceCorrelation_integrable _
      · intro t
        exact
          zeroProcessed_measurable f σ η (pointEmbed Y t) (pointBox Y t) J A₀ B
      · intro t
        exact
          (zeroProcessed_memLp f σ η (pointEmbed Y t) (pointBox Y t) J hA.le B).integrable (by norm_num : (1:ENNReal) ≤ 2)
    rw [← integral_expect _ hi]
    exact actual_zero_box_average f σ η hm Y J hA.le
  have hba := Finset.expect_le_expect (fun Y (_ : Y∈(Finset.univ : Finset (UnpointedBox (Fin m) (Fin n) k))) => hb Y)
  rw [Fintype.expect_const] at hba
  unfold zeroProcessedOnBox at hba
  dsimp only [zeroProcessed] at hc hl
  linarith only [hc,hl,hba]

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] oddAtom rowAtom pairAtomMean lowGradient
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)] {m n : ℕ}

lemma weighted_pair_class_correlation (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ) (hw1 : ∑ ξ, w ξ=1)
    (f : ∀ ξ, FoldedProof (A ξ)) {σ θ p : ℝ} (hσ : 0 < σ) (hθ : 0 ≤ θ) (η : ℝ)
    (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1) (r : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D)
    {H γ A₀ : ℝ} (hH : 0 < H) (hγ : 0 < γ) (hA : 0 < A₀)
    (hp : (∑ ξ, w ξ*atomProbability (m := m) (n := n) (f ξ) σ η θ) ≤ p) :
    (∑ ξ, w ξ*averagedCorrelation (classField (n := n) (f ξ) σ η J (some r))) ≤
      σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) +
      Slice.lossBound H γ A₀ (σ⁻¹^2)
        ((4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ)*
          Real.sqrt (θ^2+(m:ℝ)*p*(n^m:ℕ)/σ^2)) +
      A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) + Real.sqrt (H*(γ+H^2/A₀)) := by
  let q (ξ : Ξ) := 𝔼 x : Point m n, 𝔼 Y : PointedBox x k, pairAtomMean (f ξ) σ η x Y r J
  have hq ξ : 0 ≤ q ξ := Finset.expect_nonneg (fun x _ =>
    Finset.expect_nonneg (fun Y _ => pairAtomMean_nonneg _ _ _ _ _ _ _))
  have hcls := Finset.sum_le_sum (s := (Finset.univ : Finset Ξ)) (fun ξ _ =>
    mul_le_mul_of_nonneg_left (pair_class_correlation (f ξ) hσ η hn hk r J hJ hH hγ hA) (hw ξ))
  simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hw1,one_mul] at hcls
  rw [← mul_add] at hcls
  have hloss := Slice.lossBound_weighted H γ A₀ w (fun _ : Ξ => σ⁻¹^2) q hw hγ.le
    (fun _ => sq_nonneg _) hq
  rw [← Finset.sum_mul,hw1,one_mul] at hloss
  have hatom := weighted_pairAtomMean V A w hw hw1 f hσ hθ η (by omega) hk r J
    (fun j hj => (hJ j hj).1) hp
  have hloss' := Slice.lossBound_mono hH.le hγ.le hA.le (le_refl (σ⁻¹^2)) hatom
  dsimp only [q] at hloss
  linarith only [hcls, hloss, hloss']

lemma weighted_zero_class_correlation (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ) (hw1 : ∑ ξ, w ξ=1)
    (f : ∀ ξ, FoldedProof (A ξ)) {σ : ℝ} (hσ : 0 < σ) (η : ℝ)
    (hm : 0 < m) (hn : 2 ≤ n) {k s D : ℕ} (hk : k ≤ n-1)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j∈ J, (∑ u, j.2 u) ≤ s ∧ j.1.card ≤ D)
    (hJ0 : ∀ j∈ J, j.1.card < (m-(∑ u, j.2 u)).choose 2)
    {A₀ : ℝ} (hA : 0 < A₀) :
    (∑ ξ, w ξ*averagedCorrelation (classField (n := n) (f ξ) σ η J none)) ≤
      σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) + 2*(σ⁻¹^2)/A₀ +
      2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset Ξ)) (fun ξ _ =>
    mul_le_mul_of_nonneg_left (zero_class_correlation (f ξ) hσ η hm hn hk J hJ hJ0 hA) (hw ξ))
  rwa [← Finset.sum_mul,hw1,one_mul] at hh

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

theorem inner_atom_of_errors {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
    [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
    [∀ ξ, Fintype (A ξ)] (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ) (hw1 : ∑ ξ, w ξ=1)
    (f : ∀ ξ, FoldedProof (A ξ)) {J : ℝ} (hJ : 1 ≤ J) {m n k s : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : k ≤ n-1)
    (hs : ∀ t : ℕ, s+2 ≤ t → (t:ℝ)*(smoothingRho (sourceSigma J))^(2*t) ≤ 1/16)
    (hroom : sourceR J*m < (m-s).choose 2)
    {H γ A₀ θ p : ℝ} (hH : 0 < H) (hγ : 0 < γ) (hA : 0 < A₀) (hθ : 0 ≤ θ)
    (hloc : (sourceSigma J)⁻¹*Real.sqrt (((s+sourceR J*m:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) <
      classTarget (sourceT J) m/10)
    (henergy : (sourceSigma J)⁻¹^2/H < classTarget (sourceT J) m/10)
    (hclip : 2*((sourceSigma J)⁻¹^2)/A₀ < classTarget (sourceT J) m/10)
    (hcollision : 2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) < classTarget (sourceT J) m/10)
    (hfourth : Real.sqrt (H*(γ+H^2/A₀)) < classTarget (sourceT J) m/10)
    (hatom : Real.sqrt ((sourceSigma J)⁻¹^2)*Real.sqrt
      (((4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ)*
        Real.sqrt (θ^2+(m:ℝ)*p*(n^m:ℕ)/(sourceSigma J)^2))/γ) < classTarget (sourceT J) m/10)
    (h1 : (∑ ξ, w ξ*firstError (m := m) (n := n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J*(10*sourceSigma J))
    (h2 : (∑ ξ, w ξ*secondError (m := m) (n := n) (f ξ)
      ((sourceEta J)^2/(m:ℝ)) (sourceSigma J) (sourceEta J)) ≤ J*(10*(sourceEta J+sourceEta J)))
    (h3 : (∑ ξ, w ξ*thirdError (m := m) (n := n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J/(Fintype.card (Code m n):ℝ)) :
    p ≤ ∑ ξ, w ξ*atomProbability (m := m) (n := n) (f ξ) (sourceSigma J) (sourceEta J) θ := by
  by_contra hp
  have hp' := le_of_lt (lt_of_not_ge hp)
  have hσ := sourceSigma_pos hJ
  have hT : (0:ℝ) < sourceT J := by exact_mod_cast sourceT_pos hJ
  have hd := classTarget_pos hT m
  have heA : 0 ≤ (sourceSigma J)⁻¹^2/A₀ := by positivity
  have hcol0 : 0 ≤ A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) := by positivity
  have hclip' : (sourceSigma J)⁻¹^2/A₀ < classTarget (sourceT J) m/10 := by
    have hh : 2*((sourceSigma J)⁻¹^2/A₀) < classTarget (sourceT J) m/10 := by
      simpa only [mul_div_assoc] using hclip
    linarith only [hh,heA]
  have hcollision' : A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) < classTarget (sourceT J) m/10 := by
    have hh : 2*(A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹)) < classTarget (sourceT J) m/10 := by
      simpa only [mul_assoc] using hcollision
    linarith only [hh,hcol0]
  have hcls (a : Option (PairClass m)) :
      (∑ ξ, w ξ*averagedCorrelation (classField (n := n) (f ξ) (sourceSigma J) (sourceEta J)
        (rectangle (sourceR J*m) s) a)) < classTarget (sourceT J) m := by
    cases a with
    | none =>
      have hh := weighted_zero_class_correlation V A w hw hw1 f hσ (sourceEta J) (by omega : 0 < m)
        hn hk _ (rectangle_bounds (sourceR J*m) s) (rectangle_pair_room hroom) hA
      linarith only [hh,hloc,hclip,hcollision,hd]
    | some r =>
      have hh := weighted_pair_class_correlation V A w hw hw1 f hσ hθ (sourceEta J)
        hn hk r _ (rectangle_bounds (sourceR J*m) s) hH hγ hA hp'
      unfold Slice.lossBound at hh
      linarith only [hh,hloc,henergy,hclip',hcollision',hfourth,hatom,hd]
  have hsum : (∑ a : Option (PairClass m), ∑ ξ, w ξ*averagedCorrelation
      (classField (n := n) (f ξ) (sourceSigma J) (sourceEta J) (rectangle (sourceR J*m) s) a)) <
      (Fintype.card (Option (PairClass m)):ℝ)*classTarget (sourceT J) m := by
    calc
      _ < ∑ _a : Option (PairClass m), classTarget (sourceT J) m :=
        Finset.sum_lt_sum (fun a _ => (hcls a).le) ⟨none,Finset.mem_univ _,hcls none⟩
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [classes_times_target hT] at hsum
  have hup := weighted_lowGradient_classes (m := m) (n := n) V A w hw (sourceR J*m) s f
    (sourceSigma J) (sourceEta J)
  have hlo := source_lowGradient_correlation V A w hw hw1 f hJ hm hn s hs h1 h2 h3
  linarith only [hsum,hup,hlo]

end MinUncut.Inner

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

def edgeSampleSecond (equations : S → Equation Name) {k : ℕ} (e : EdgeSamples I S k) :
    I → SecondQuestion Name := secondQuestion (fun i => equations (e.2.1 i)) (hiddenSet e.1.val) e.2.2

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ComparisonSoundness
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
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] firstError secondError thirdError fourthError atomProbability
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

attribute [local irreducible] edgeMean

def ProofFamily.cost {J : ℝ} (P : InnerParameters J) (O : OuterParameters J P)
    (f : ProofFamily Name I) (equations : S → Equation Name) : ℝ :=
  ∑ j, f.testErrors P O equations j/budgets P O j

attribute [local irreducible] ProofFamily.fourthTotal ProofFamily.atomTotal

end MinUncut.Outer

end
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

def variableProof (y : FamilyVariable Name I → Bool) : ProofFamily Name I where
  first U := ⟨answer familyBase y (.inl U),answer_folded familyBase y (.inl U)⟩
  second Q := ⟨answer familyBase y (.inr Q),answer_folded familyBase y (.inr Q)⟩

def ProofFamily.queryAnswer (f : ProofFamily Name I) :
    (q : FamilyQuestion Name I) → (FamilyAlphabet q → Bool) → Bool
  | .inl U => (f.first U).answer
  | .inr Q => (f.second Q).answer

lemma variableProof_queryAnswer (y : FamilyVariable Name I → Bool) :
    (variableProof y).queryAnswer=answer familyBase y := by
  funext q
  cases q <;> rfl
end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_LiteralTestQueries
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof MinUncut.FiniteGaussian
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I] {m n : ℕ}

lemma comparison_failure (f : ProofFamily Name I) (q q' : FamilyQuestion Name I)
    (P : FamilyAlphabet q → Bool) (P' : FamilyAlphabet q' → Bool) :
    ((comparison q q' P P').failure f.queryAnswer:ℝ)=
      disagreement (f.queryAnswer q P) (f.queryAnswer q' P') := by
  unfold comparison QueryDemand.failure disagreement
  cases f.queryAnswer q P <;> cases f.queryAnswer q' P' <;> simp

def testFunctional (f : ProofFamily Name I) (U : I → Equation Name) (h : I → Bool)
    (pos : I → Fin 3) (B C : FaceArray (SecondAlphabet (secondQuestion U h pos)) m n)
    (z : Code m n) (t : ScoreIndex m n → Bool) : Test → ℝ
  | .first => firstTable (f.second (secondQuestion U h pos)) B t
  | .second => secondTable (f.second (secondQuestion U h pos)) B C t
  | .third => thirdTable (f.second (secondQuestion U h pos)) B z t
  | .fourth => fourthTable (f.first U) (f.second (secondQuestion U h pos))
    (pullbackFaces (projection U h pos) C) C t

lemma testQuery_failure (f : ProofFamily Name I) (U : I → Equation Name) (h : I → Bool)
    (pos : I → Fin 3) (B C : FaceArray (SecondAlphabet (secondQuestion U h pos)) m n)
    (z : Code m n) (t : ScoreIndex m n → Bool) (j : Test) :
    ((testQuery U h pos B C z t j).failure f.queryAnswer:ℝ)=testFunctional f U h pos B C z t j := by
  cases j <;> exact comparison_failure f _ _ _ _
end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_WeightedTestLaw
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.LocalTemplate.indexFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I : Type*} [Fintype I] {m n : ℕ}

lemma localWeight_sum {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (g : GridData) (a b : ℚ) (j : Test) (F : LocalSample A m n g → ℝ) :
    (∑ p, (localWeight g a b j p:ℝ)*F p)=
      (𝔼 B, 𝔼 C, 𝔼 z, ∑ q : TestCoordinates m n → Fin g.L,
        (gridWeight g q:ℝ)*(noiseWeight a B C j:ℝ)*F (B,C,z,q))/(b:ℝ) := by
  simp only [localWeight,Rat.cast_div,Rat.cast_mul,Rat.cast_inv,Rat.cast_natCast,
    Fintype.sum_prod_type,Fintype.expect_eq_sum_div_card]
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma localTest_mean (f : ProofFamily Name I) (U : I → Equation Name) (h : I → Bool)
    (pos : I → Fin 3) (g : GridData) (a σ η : ℚ) (j : Test) :
    (𝔼 B, 𝔼 C, 𝔼 z, ∑ q : TestCoordinates m n → Fin g.L,
      (gridWeight g q:ℝ)*(noiseWeight a B C j:ℝ)*
        testFunctional f U h pos B C z (rationalScoreTable σ η (fun i => midpoint g.T g.L (q i))) j)=
    match j with
    | .first => finiteFirst (m := m) (n := n) g (f.second (secondQuestion U h pos)) σ η
    | .second => finiteSecond (m := m) (n := n) g (f.second (secondQuestion U h pos)) a σ η
    | .third => finiteThird (m := m) (n := n) g (f.second (secondQuestion U h pos)) σ η
    | .fourth => finiteFourth (m := m) (n := n) g (projection U h pos)
        (f.first U) (f.second (secondQuestion U h pos)) σ η := by
  cases j
  · simp only [noiseWeight,Rat.cast_one,mul_one,testFunctional,Fintype.expect_const,
      finiteFirst,tableAverage]
  · simp only [noiseWeight,RowNoise.rationalDensity_cast,testFunctional,Fintype.expect_const,
      finiteSecond,tableAverage]
    congr 1
    funext B
    congr 1
    funext C
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  · simp only [noiseWeight,Rat.cast_one,mul_one,testFunctional,Fintype.expect_const,
      finiteThird,tableAverage]
  · simp only [noiseWeight,Rat.cast_one,mul_one,testFunctional,Fintype.expect_const,
      finiteFourth,tableAverage]
end MinUncut.Outer

namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n k : ℕ}

instance elementaryFintype (equations : S → Equation Name) (k m n : ℕ) (g : GridData) :
    Fintype (Elementary (I := I) equations k m n g) := by
  unfold Elementary
  infer_instance

lemma elementaryWeight_nonneg (equations : S → Equation Name) (g : GridData)
    (hT : 0<g.T) (hL : 0<g.L) {a b : ℚ} (ha : 0≤a) (ha1 : a≤1) (hb : 0<b)
    (j : Test) (e : Elementary (I := I) equations k m n g) :
    0≤elementaryWeight equations g a b j e :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (localWeight_nonneg g hT hL ha ha1 hb j e.2)

lemma elementary_weighted_sum (equations : S → Equation Name) (g : GridData) (a b σ η : ℚ)
    (j : Test) (f : ProofFamily Name I) :
    (∑ e : Elementary (I := I) equations k m n g,
      (elementaryWeight equations g a b j e:ℝ)*((elementaryQuery equations g σ η j e).failure f.queryAnswer:ℝ))=
    edgeMean equations k (fun U h pos =>
      (match j with
      | .first => finiteFirst (m := m) (n := n) g (f.second (secondQuestion U h pos)) σ η
      | .second => finiteSecond (m := m) (n := n) g (f.second (secondQuestion U h pos)) a σ η
      | .third => finiteThird (m := m) (n := n) g (f.second (secondQuestion U h pos)) σ η
      | .fourth => finiteFourth (m := m) (n := n) g (projection U h pos)
          (f.first U) (f.second (secondQuestion U h pos)) σ η)/(b:ℝ)) := by
  change (∑ e : Sigma _, _) = _
  rw [Fintype.sum_sigma]
  simp only [elementaryWeight,Rat.cast_mul,Rat.cast_inv,Rat.cast_natCast,mul_assoc,← Finset.mul_sum]
  trans ∑ o : OuterSample I S k, (Fintype.card (OuterSample I S k):ℝ)⁻¹*
    ((𝔼 B, 𝔼 C, 𝔼 z, ∑ q : TestCoordinates m n → Fin g.L,
       (gridWeight g q:ℝ)*(noiseWeight a B C j:ℝ)*testFunctional f
        (sampleFirst equations o) (sampleHidden o) o.2.2 B C z
        (rationalScoreTable σ η (fun i => midpoint g.T g.L (q i))) j)/(b:ℝ))
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _
    congr 1
    rw [localWeight_sum]
    simp only [elementaryQuery]
    simp_rw [testQuery_failure]
  · simp_rw [localTest_mean]
    rw [sum_invcard_mul,expect_prod_type]
    simp only [expect_prod_type,edgeMean,sampleHidden]
    cases j <;> rfl
end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalBasics
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.LocalTemplate.indexFintype _root_.OAI.MinUncut.Outer.elementaryFintype _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
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

def ProofFamily.finiteErrors {J : ℕ} (P : InnerParameters J) (O : OuterParameters J P)
    (g : GridData) (f : ProofFamily Name I) (equations : S → Equation Name) : Test → ℝ
  | .first => edgeMean equations O.k (fun U h pos => finiteFirst (m := P.m) (n := P.n) g
    (f.second (secondQuestion U h pos)) (rationalSigma J) (rationalEta J))
  | .second => edgeMean equations O.k (fun U h pos => finiteSecond (m := P.m) (n := P.n) g
    (f.second (secondQuestion U h pos)) ((sourceEta J)^2/P.m) (rationalSigma J) (rationalEta J))
  | .third => edgeMean equations O.k (fun U h pos => finiteThird (m := P.m) (n := P.n) g
    (f.second (secondQuestion U h pos)) (rationalSigma J) (rationalEta J))
  | .fourth => edgeMean equations O.k (fun U h pos => finiteFourth (m := P.m) (n := P.n) g
    (projection U h pos) (f.first U) (f.second (secondQuestion U h pos)) (rationalSigma J) (rationalEta J))

def ProofFamily.finiteCost {J : ℕ} (P : InnerParameters J) (O : OuterParameters J P)
    (g : GridData) (f : ProofFamily Name I) (equations : S → Equation Name) : ℝ :=
  ∑ j, f.finiteErrors P O g equations j / budgets P O j

attribute [local irreducible] edgeMean
end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SamplerCost
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.LocalTemplate.indexFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.innerDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.outerDataPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S]

lemma allFailure_eq {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) (g : GridData) (equations : S → Equation Name)
    (y : FamilyVariable Name I → Bool) :
    (∑ e : AllElementary (I := I) equations o.k d.m d.n g,
      (allWeight equations g (rationalRate J d) (rationalBudgets J d o) e:ℝ)*
        (PathRealization.failure (allDemand equations g (rationalSigma J) (rationalEta J) e) y:ℝ)) =
      (variableProof y).finiteCost (d.realize hJ hd) (o.realize hJ d hd ho) g equations := by
  rw [Fintype.sum_prod_type]
  unfold ProofFamily.finiteCost
  apply Finset.sum_congr rfl
  intro j _
  simp only [allWeight,allDemand,QueryDemand.failure_signed,← variableProof_queryAnswer]
  rw [elementary_weighted_sum]
  cases j <;> simp only [ProofFamily.finiteErrors,rationalBudgets_cast hJ d hd o ho,
    rationalRate_cast]
  all_goals
    change edgeMean equations o.k (fun U h pos => _ / _) =
      edgeMean equations o.k (fun U h pos => _) / _
    unfold edgeMean
    simp only [Finset.expect_div]
    rfl
end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SamplerAssembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.LocalTemplate.indexFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.innerDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.outerDataPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

namespace Parameters

lemma grid_pos {J : ℕ} (P : Parameters J) : 0<P.grid.T ∧ 0<P.grid.L := by
  have h := tableGrid_check P.d.m P.d.n (tableAccuracy J P.d P.o)
    (tableAccuracy_pos P.hJ P.d P.hd P.o P.ho)
  exact ⟨h.1,h.2.1⟩

omit [Nonempty S] in
lemma weight_nonneg {J : ℕ} (P : Parameters J) (equations : S → Equation Name) (e : P.Sample equations) :
    0≤P.weight equations e :=
  elementaryWeight_nonneg equations P.grid P.grid_pos.1 P.grid_pos.2
    (rationalRate_bounds P.hJ P.d P.hd).1 (rationalRate_bounds P.hJ P.d P.hd).2
    (rationalBudgets_pos P.hJ P.d P.hd P.o P.ho e.1) e.1 e.2

lemma weight_den {J : ℕ} (P : Parameters J) (equations : S → Equation Name) (e : P.Sample equations) :
    (P.weight equations e).den∣P.denominator S :=
  elementaryWeight_den equations (by simpa only [Fintype.card_fin] using P.k_le) _ _ _ e.1 e.2

omit [Nonempty S] in
lemma failure_eq {J : ℕ} (P : Parameters J) (equations : S → Equation Name)
    (y : FamilyVariable Name (Fin P.o.t) → Bool) :
    (∑ e, (P.weight equations e:ℝ)*(PathRealization.failure (P.demand equations e) y:ℝ))=
      (variableProof y).finiteCost (P.d.realize P.hJ P.hd) (P.o.realize P.hJ P.d P.hd P.ho) P.grid equations :=
  allFailure_eq P.hJ P.d P.hd P.o P.ho P.grid equations y

end Parameters
end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Basic2
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularTable

open _root_.Turing MachineComposition
open MinUncutGames.Foundations.PCP


namespace Top

abbrev Body := MachineRegularOriginalBody.Tape

end Top
end MinUncutGames.Foundations.Complexity.MachineRegularTable
end

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
namespace MinUncutGames.Foundations.PCP.VerifierToCNF

open Target

def splitLong {n : Nat} : List (Literal n) → List (Fin n) → List (Clause n)
  | [a, b, c], [] => [#v[a, b, c]]
  | a :: b :: rest, y :: ys =>
      #v[a, b, ⟨y, true⟩] :: splitLong (⟨y, false⟩ :: rest) ys
  | _, _ => []

def tautology {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    Clause (outputVariables V) :=
  let v := oldIndex V (V.query e ⟨0, by omega⟩)
  #v[⟨v, true⟩, ⟨v, false⟩, ⟨v, true⟩]

def block {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events)
    (p : PatternIndex q) : List (Clause (outputVariables V)) :=
  if V.accepts e (patternAt q p) then List.replicate (q - 2) (tautology V hq e)
  else splitLong (forbiddenClause V e p) (auxiliaryNames V e p)

def eventBlock {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    List (Clause (outputVariables V)) :=
  (List.finRange (patterns q).length).flatMap (block V hq e)

def convert {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) : Formula where
  «variables» := outputVariables V
  clauses := (List.finRange V.events).flatMap (eventBlock V hq)

theorem splitLong_values {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (A : Fin n → Bool) :
    (splitLong ls ys).map (fun c => c.eval A) =
      (chainView (ls.map (fun l => l.eval A)) (ys.map A)).map tripleValue := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | [_, _] => rfl
    | [a, b, c] => rfl
    | _ :: _ :: _ :: _ :: _ => rfl
  | cons y ys ih =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | a :: b :: rest =>
      have h := ih (⟨y, false⟩ :: rest)
      simp only [splitLong, List.map_cons, chainView]
      apply congrArg₂ List.cons
      · rfl
      · simpa only [List.map_cons, Literal.eval, Bool.false_eq_true, ↓reduceIte] using h

theorem splitLong_length {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (size : ls.length = ys.length + 3) : (splitLong ls ys).length = ys.length + 1 := by
  have values := congrArg List.length (splitLong_values ls ys (fun _ => false))
  simp only [List.length_map] at values
  rw [values]
  have h := chainView_length (ls.map (fun l => l.eval (fun _ => false)))
    (ys.map (fun _ => false)) (by simpa only [List.length_map] using size)
  simpa only [List.length_map] using h

theorem block_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (p : PatternIndex q) : (block V hq e p).length = q - 2 := by
  by_cases accepted : V.accepts e (patternAt q p) = true
  · simp [block, accepted]
  · simp only [block, accepted, Bool.false_eq_true, ↓reduceIte]
    have size : (forbiddenClause V e p).length = (auxiliaryNames V e p).length + 3 := by
      simp only [forbiddenClause, auxiliaryNames, List.length_ofFn]
      omega
    have h := splitLong_length (forbiddenClause V e p) (auxiliaryNames V e p) size
    have auxLength : (auxiliaryNames V e p).length = q - 3 := by simp [auxiliaryNames]
    rw [auxLength] at h
    omega

theorem eventBlock_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) : (eventBlock V hq e).length = 2 ^ q * (q - 2) := by
  rw [eventBlock, length_flatMap_constant _ _ (q - 2) (fun p _ => block_length V hq e p)]
  simp only [List.length_finRange, patterns_length]

theorem convert_clause_count {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) :
    (convert V hq).clauses.length = V.events * (2 ^ q * (q - 2)) := by
  change ((List.finRange V.events).flatMap (eventBlock V hq)).length = _
  rw [length_flatMap_constant _ _ _ (fun e _ => eventBlock_length V hq e)]
  rw [List.length_finRange]

theorem twelve_query_clause_count (V : FiniteVerifier 12) :
    (convert V (by decide)).clauses.length = V.events * 40960 := by
  simpa only [twelve_query_factor] using convert_clause_count V (by decide)

end MinUncutGames.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_FinalBooleanVerifier
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

abbrev verifier (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    VerifierToCNF.FiniteVerifier 12 where
  «variables» := n * 6
  events := m
  query := fun e i => Fin.addCases (motive := fun _ : Fin (6 + 6) => Fin (n * 6))
    (fun j : Fin 6 => bitIndex vertices (G.tail (edges.symm e)) j)
    (fun j : Fin 6 => bitIndex vertices (G.head (edges.symm e)) j) i
  accepts := fun e bits => G.accepts (edges.symm e)
    (fun j => bits (Fin.castAdd 6 j)) (fun j => bits (Fin.natAdd 6 j))

def cnf (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n) (edges : E ≃ Fin m) : Formula :=
  VerifierToCNF.convert (verifier G vertices edges) (by decide)

theorem cnf_clause_count (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) : (cnf G vertices edges).clauses.length = m * 40960 :=
  VerifierToCNF.twelve_query_clause_count (verifier G vertices edges)

theorem cnf_variable_count (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) : (cnf G vertices edges).«variables» = n * 6 + m * 36864 := by
  change n * 6 + m * (VerifierToCNF.patterns 12).length * (12 - 3) = _
  rw [VerifierToCNF.patterns_length, Nat.mul_assoc, twelve_query_auxiliary_factor]

end MinUncutGames.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringFinalConstants
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.FinalTableFormula

open Target Complexity

def output (table : GraphTables.Table) : Formula :=
  FinalBooleanVerifier.cnf (FinalCNFPattern.tableGraph table) (Equiv.refl _) (Equiv.refl _)

@[simp] theorem variable_count (table : GraphTables.Table) :
    (output table).«variables» = table.vertices * 6 + table.darts * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ (Equiv.refl _) (Equiv.refl _)

@[simp] theorem clause_count (table : GraphTables.Table) :
    (output table).clauses.length = table.darts * 40960 :=
  FinalBooleanVerifier.cnf_clause_count _ (Equiv.refl _) (Equiv.refl _)

end MinUncutGames.Foundations.PCP.FinalTableFormula

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_SampleEnumeration
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.LocalTemplate.indexFintype _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
open MinUncutGames.Foundations.Hastad.SourceOccurrences

namespace SampleEnumeration

attribute [local instance] OAI.MinUncut.Outer.SampleEnumeration.codeEq
attribute [local instance] OAI.MinUncut.Outer.SampleEnumeration.codeType
attribute [local instance] OAI.MinUncut.Outer.SampleEnumeration.formEq
local instance localEq {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (m n : ℕ) (g : GridData) :
    DecidableEq (LocalSample (SecondAlphabet Q) m n g) := by
  letI : DecidableEq (Forms (SecondAlphabet Q)) := formEq Q
  letI : DecidableEq (FaceArray (SecondAlphabet Q) m n) :=
    inferInstanceAs (DecidableEq (Row m n → Forms (SecondAlphabet Q)))
  exact fun f h => decidable_of_iff
    (f.1=h.1 ∧ f.2.1=h.2.1 ∧ f.2.2.1=h.2.2.1 ∧ f.2.2.2=h.2.2.2)
    (by constructor <;> intro he <;> aesop)

def semanticLocal {N s t : ℕ} (eqs : Fin s → Equation (Fin N)) {k : ℕ}
    (o : OuterSample (Fin t) (Fin s) k) (m n : ℕ) (g : GridData) :
    Enumeration (LocalSample (SecondAlphabet (sampleSecond eqs o)) m n g) :=
  (second_eq eqs o) ▸ localSample (second eqs o) m n g

local instance semanticLocalEq {N s t : ℕ} (eqs : Fin s → Equation (Fin N)) {k : ℕ}
    (o : OuterSample (Fin t) (Fin s) k) (m n : ℕ) (g : GridData) :
    DecidableEq (LocalSample (SecondAlphabet (sampleSecond eqs o)) m n g) :=
  (second_eq eqs o) ▸ localEq (second eqs o) m n g

def elementary {N s t : ℕ} (eqs : Fin s → Equation (Fin N)) (k m n : ℕ) (g : GridData) :
    Enumeration (Elementary (I := Fin t) eqs k m n g) :=
  (outerSample t s k).sigma (fun o => semanticLocal eqs o m n g)

def tests : Enumeration Test :=
  Enumeration.ofList [.first,.second,.third,.fourth] (by intro j; cases j <;> simp)

def all {N s t : ℕ} (eqs : Fin s → Equation (Fin N)) (k m n : ℕ) (g : GridData) :
    Enumeration (Test × Elementary (I := Fin t) eqs k m n g) :=
  tests.pair (elementary eqs k m n g)

end SampleEnumeration
end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_TemplateExpressions
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.Costed
open scoped BigOperators

lemma positiveExpr_eval (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    (positiveExpr u).eval (inputTuple F c)=
      ((((Encoding.fin u).function (slotEncoding.function Encoding.bool)).code (signature F c).positive)).val := by
  unfold positiveExpr
  apply functionExpr_eval (Encoding.fin u) (slotEncoding.function Encoding.bool)
  intro i
  apply functionExpr_eval slotEncoding Encoding.bool
  intro s
  rw [slotWord_positive,MinUncut.Outer.LocalTemplate.bool_code]
  rfl

lemma sameExpr_eval (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    (sameExpr u).eval (inputTuple F c)=
      ((((coordinateEncoding u).function ((coordinateEncoding u).function Encoding.bool)).code (signature F c).same)).val := by
  unfold sameExpr
  apply functionExpr_eval (coordinateEncoding u) ((coordinateEncoding u).function Encoding.bool)
  intro a
  apply functionExpr_eval (coordinateEncoding u) Encoding.bool
  intro b
  simp only [AExpr.eval,slotWord_name,signature,MinUncut.Outer.LocalTemplate.bool_code]
  by_cases h : nameAt (clauseAt F (c a.1)) a.2=nameAt (clauseAt F (c b.1)) b.2
  · simp only [h,ite_true,decide_true,Bool.toNat_true]
  · have hh := Fin.val_ne_of_ne h
    simp only [hh,ite_false,h,decide_false,Bool.toNat_false]

lemma signatureExpr_eval (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    (signatureExpr u).eval (inputTuple F c)=((signatureEncoding u).code (signature F c)).val := by
  simp only [signatureExpr,AExpr.eval,positiveExpr_eval,sameExpr_eval]
  rfl

lemma signatureLookup_eval (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (f : Signature u → ℕ) :
    (signatureLookup f).eval (inputTuple F c)=f (signature F c) := by
  apply MinUncut.Outer.LocalTemplate.constantTable_eval
  exact signatureExpr_eval F c

lemma sampledExpr_eval (F : Formula) {u : ℕ} (c : ClauseContext F u) (s : SlotContext u) :
    (sampledExpr s).eval (inputTuple F c)=
      ((variableEncoding F u).code (sampledVariables F c s)).val := by
  simp only [sampledExpr,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,AExpr.eval,
    AExpr.eval_pow,slotWord_name]
  rfl

lemma addressExpr_eval (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (f : Signature u → LocalKey u) :
    (addressExpr s f).eval (inputTuple F c)=
      (keyAddress F c (sampledVariables F c s) (f (signature F c))).val := by
  rw [keyAddress_number]
  simp only [addressExpr,AExpr.eval,signatureLookup_eval,sampledExpr_eval,AExpr.eval_pow]
  by_cases h0 : keyTag (f (signature F c))=0
  · simp only [h0,ite_true,Nat.one_ne_zero,ite_false,keyNumber]
  · by_cases h1 : keyTag (f (signature F c))=1 <;>
      simp only [h0,h1,ite_true,ite_false,Nat.one_ne_zero,keyNumber,inputTuple,
        Complexity.formulaWords,List.cons_append,List.nil_append,List.drop_succ_cons,
        List.drop_zero,List.headI_cons]

lemma equationExpressions_eval (F : Formula) {u D : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (t : SourceTape.TestTape (I u) (J u) D) :
    (equationExpressions s t).map (fun e=>e.eval (inputTuple F c))=
      MinUncutGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D ((c,s),t)) := by
  rw [←signature_equation]
  simp only [equationExpressions,List.map_cons,List.map_nil,addressExpr_eval,signatureLookup_eval]
  unfold mapEquation MinUncutGames.Reduction.SourceEncoding.equationWords
  congr 3
  cases ((signature F c).equation s t).rhs <;> rfl

end MinUncut.SourceTemplate

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

lemma listFailure_map {V W : Type*} (f : V → W) (ds : List (Demand V)) (s : W → Bool) :
    listFailure (ds.map (Demand.map f)) s=listFailure ds (s ∘ f) := by
  simp only [listFailure,List.map_map,Function.comp_def,failure_map]

lemma listFailure_weight {E V : Type} [Fintype E] (D : ℕ) (w : E → ℚ)
    (hw : ∀e,0≤w e) (hd : ∀e,(w e).den∣D) (d : E → Demand V)
    (enc : Encoding E) (s : V → Bool) :
    (listFailure (demandList D w d enc) s:ℝ)=(D:ℝ)*∑e,(w e:ℝ)*(failure (d e) s:ℝ) := by
  rw [listFailure_demandList,← expanded_failure]
  exact expanded_weight D w hw hd d s

end MinUncut.PathRealization

noncomputable section
namespace MinUncut.Outer.Parameters
open MinUncut.Inner MinUncut.FiniteProof MinUncut.PathRealization
attribute [local instance] Classical.propDecidable

variable {N s J : ℕ} [Nonempty (Fin s)]

def canonicalDemands (P : Parameters J) (eqs : Fin s → Equation (Fin N)) :
    List (Demand (Fin (paddedVariableEncoding N P.o.t).size)) :=
  (demandList (P.denominator (Fin s)) (P.weight eqs) (P.demand eqs)
    (SampleEnumeration.all eqs P.o.k P.d.m P.d.n P.grid).encoding).map (Demand.map variableCode)

lemma canonicalGraph_failure (P : Parameters J) (eqs : Fin s → Equation (Fin N))
    (y : Fin (paddedVariableEncoding N P.o.t).size → Bool) :
    (listFailure (P.canonicalDemands eqs) y:ℝ)=
      (P.denominator (Fin s):ℝ)*∑e,(P.weight eqs e:ℝ)*
        (failure (P.demand eqs e) (y ∘ variableCode):ℝ) := by
  unfold canonicalDemands
  rw [listFailure_map]
  exact listFailure_weight _ _ (P.weight_nonneg eqs) (P.weight_den eqs) _ _ _

end MinUncut.Outer.Parameters

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformEquationOutput
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction MinUncut.Costed
noncomputable section

lemma sourceExpressions_eval (F : Formula) {u D : ℕ} (c : ClauseContext F u) :
    (sourceExpressions u D).map (fun e=>e.eval (inputTuple F c))=
      (slotContextEncoding u).enumerate.flatMap (fun s=>
        (testTapeEncoding u D).enumerate.flatMap (fun t=>
          SourceEncoding.equationWords (sourceEquation F u D ((c,s),t)))) := by
  simp only [sourceExpressions,List.map_flatMap,equationExpressions_eval]

lemma emitted_source (F : Formula) (u D : ℕ) :
    Blocks.emitted (sourceExpressions u D) (F.clauses.length^u) (Complexity.formulaWords F)=
      (rawSourceList F u D).flatMap SourceEncoding.equationWords := by
  rw [Blocks.emitted,←GraphRegisters.finRange_vals,Hastad.SourceEnumeration.rawSourceList_flatMap]
  have hc : (clauseEncoding F u).enumerate=
      (List.finRange (F.clauses.length^u)).map (clauseEncoding F u).code.symm := by
    exact List.ofFn_eq_map
  rw [hc]
  simp only [List.flatMap_map]
  conv_rhs => erw [List.flatMap_map]
  apply congrArg (List.flatMap · (List.finRange (F.clauses.length^u)))
  funext z
  have he := sourceExpressions_eval (D:=D) F ((clauseEncoding F u).code.symm z)
  simp only [Blocks.block,inputTuple,
    Hastad.SourceEnumeration.testTapeEncoding_enumerate,List.flatMap_assoc,List.flatMap_map,
    sourceEquation] at he ⊢
  erw [Equiv.apply_symm_apply] at he
  exact he

lemma sourceVariableExpr_eval (F : Formula) (u : ℕ) :
    (sourceVariableExpr u).eval (Complexity.formulaWords F)=nBits F u := by
  simp only [sourceVariableExpr,AExpr.eval,AExpr.eval_pow,Complexity.formulaWords,List.cons_append,List.nil_append,
    List.drop_zero,List.headI_cons,List.drop_succ_cons,nBits_eq]

lemma sourceCountExpr_eval (F : Formula) (u D : ℕ) :
    (sourceCountExpr u D).eval (Complexity.formulaWords F)=(rawSourceList F u D).length := by
  have h := congrArg List.length (emitted_source F u D)
  rw [Blocks.length_emitted] at h
  have hl : ((rawSourceList F u D).flatMap SourceEncoding.equationWords).length=
      (rawSourceList F u D).length*4 := by
    simp only [List.length_flatMap,SourceEncoding.equationWords,List.length_cons,List.length_nil]
    simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
  rw [hl] at h
  simp only [sourceCountExpr,AExpr.eval,AExpr.eval_pow,Complexity.formulaWords,List.cons_append,List.nil_append,
    List.drop_zero,List.headI_cons,List.drop_succ_cons,h]
  omega

lemma sourceStageWords_spec (F : Formula) (u D : ℕ) (hD : 0<D) (hne : F.clauses≠[]) :
    ∃junk, sourceStageWords u D (Complexity.formulaWords F)=
      SourceEncoding.inputWords (sourceInput F u D hD)++junk := by
  refine ⟨Blocks.retained (sourceExpressions u D) (F.clauses.length^u) (Complexity.formulaWords F),?_⟩
  unfold sourceStageWords
  rw [sourceVariableExpr_eval,sourceCountExpr_eval]
  have ht : ((AExpr.reg 1).pow u).eval (Complexity.formulaWords F)=F.clauses.length^u := by
    simp only [AExpr.eval_pow,AExpr.eval,Complexity.formulaWords,List.cons_append,List.nil_append,
      List.drop_succ_cons,List.drop_zero,List.headI_cons]
  rw [ht,emitted_source]
  simp only [SourceEncoding.inputWords,sourceInput,sourceList_nonempty F u D hne,
    List.cons_append,List.nil_append]
end
end MinUncut.SourceTemplate

noncomputable section

open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncut.FiniteProof MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences
attribute [local instance] Classical.propDecidable

variable {t k m n : ℕ} {g : MinUncut.FiniteGaussian.GridData}

lemma generated_failure_eq {J : ℕ} (P : Parameters J) (input : SourceEncoding.Input)
    [Nonempty (Fin input.equations.length)]
    (E : Enumeration (Index (Fin P.o.t) P.o.k P.d.m P.d.n P.grid))
    (y : Fin (paddedVariableEncoding input.«variables» P.o.t).size → Bool) :
    listFailure (generatedDemands input E (rationalRate J P.d) (rationalBudgets J P.d P.o)
      (rationalSigma J) (rationalEta J)) y=
      listFailure (P.canonicalDemands (equations input)) y := by
  rw [generatedDemands_failure,Parameters.canonicalDemands,listFailure_map,listFailure_demandList]
  have he := Equiv.sum_comp (occurrence (k:=P.o.k) (m:=P.d.m) (n:=P.d.n)
    (g:=P.grid) (equations input)) (fun e=>multiplicity (P.denominator (Fin input.equations.length))
      (P.weight (equations input) e)*failure (P.demand (equations input) e) (y ∘ variableCode))
  rw [Fintype.sum_prod_type] at he
  rw [←he]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  exact (occurrence_multiplicity (equations input) (by simpa only [Fintype.card_fin] using P.k_le)
    P.grid_pos.1 P.grid_pos.2 (rationalRate_bounds P.hJ P.d P.hd).1
    (rationalRate_bounds P.hJ P.d P.hd).2 _
    (rationalBudgets_pos P.hJ P.d P.hd P.o P.ho) u e).symm
end MinUncut.Costed.SourceWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CountedWordParser
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed
open Turing.ToPartrec Polynomial
noncomputable section
variable {f e : List ℕ → List ℕ}

lemma run_until (F : PolyProgram f) (E : PolyProgram e) (L M : ℕ)
    (hsize : ∀v,(f v).length≤v.length+L ∧ Arena.maximum (f v)≤Arena.maximum v+M)
    (hstop : ∀v,(e v).headI=0 → f v=v) (v : List ℕ) (B : ℕ)
    (hend : (e (f^[B] v)).headI=0) :
    Runs (untilCode F E) v (f^[B] v) ((untilBound F E L M).eval (magnitude (B::v))) := by
  classical
  let ex : ∃i,(e (f^[i] v)).headI=0 := ⟨B,hend⟩
  let n := Nat.find ex
  have hn : n≤B := Nat.find_min' ex hend
  have hdone : (e (f^[n] v)).headI=0 := Nat.find_spec ex
  let Z := (untilStateBound L M).eval (magnitude (B::v))
  have hm : ∀i≤B,magnitude (f^[i] v)≤Z := by
    intro i hi
    simpa only [Z, untilStateBound, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one] using Arena.iterate_magnitude L M hsize B v i hi
  have he : f^[B] v=f^[n] v := iterate_at_stop hstop v n B hdone hn
  have hb : ∀i≤B,Runs (untilBody F E).code (f^[i] v)
      (if (e (f^[i] v)).headI=0 then 0::f^[i] v else 1::f^[i+1] v)
      ((untilBody F E).bound.eval Z) := by
    intro i hi
    have hh := ((untilBody F E).run (f^[i] v)).mono (evalNat_mono _ (hm i hi))
    simpa only [Function.iterate_succ_apply'] using hh
  have hr := run_fix_bounded n Z ((untilBody F E).bound.eval Z)
    (fun i hi=>hm i (hi.trans hn)) (state:=fun i=>f^[i] v) (out:=f^[n] v)
    (by intro i hi; simpa only [ite_eq_right (Nat.find_min ex hi)] using hb i (by omega))
    (by simpa only [hdone,ite_true] using hb n hn)
  rw [←he] at hr
  apply hr.mono
  have hn' : n+1 ≤ magnitude (B::v)+1 := by simp only [magnitude_cons]; omega
  have hp := Nat.mul_le_mul_right ((untilBody F E).bound.eval Z+32*(Z+3)) hn'
  simpa only [untilBound,eval_mul,eval_add,eval_comp,eval_X,eval_one,eval_C,eval_ofNat,Z] using hp
end
end MinUncut.Costed

namespace MinUncut.Costed.Arena
open Turing.ToPartrec Polynomial
noncomputable section

lemma stoppedTick_safe (v : List ℕ) :
    (stoppedTick v).length≤v.length+9 ∧ maximum (stoppedTick v)≤ maximum v+3 := by
  unfold stoppedTick
  split_ifs
  · exact ⟨by omega,by omega⟩
  · exact rawTick_safe v
lemma unboundedControl_run {c v w B} (hr : Runs c v w B) (base : Heap) :
    ∃h out,ListRep h out w ∧
      magnitude (State.mk 2 0 out 0 h).encode ≤
        (untilStateBound 9 3).eval (magnitude ((3*B+1)::(initialState c v base).encode)) ∧
      Runs unboundedControl (initialState c v base).encode (State.mk 2 0 out 0 h).encode
        ((untilBound stoppedTickProgram stopProgram 9 3).eval
          (magnitude ((3*B+1)::(initialState c v base).encode))) := by
  obtain ⟨t,ht,hc⟩:=hr
  obtain ⟨h,out,ho,he⟩:=CodeRun.interpreted hc base ht
  rw [←stoppedTick_iter_encode] at he
  refine ⟨h,out,ho,?_,?_⟩
  · rw [←he]
    simpa only [untilStateBound,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using
      iterate_magnitude 9 3 stoppedTick_safe (3*B+1) (initialState c v base).encode (3*B+1) le_rfl
  have hh:=run_until stoppedTickProgram stopProgram 9 3 stoppedTick_safe
    (by intro u hu; change stopExpr.eval u=0 at hu; simp [stoppedTick,(stop_zero u).mp hu])
    (initialState c v base).encode (3*B+1)
    (by rw [he]; change stopExpr.eval _=0; exact (stop_zero _).mpr rfl)
  simpa only [he,unboundedControl] using hh

lemma unboundedOutput_run {h p w} (ho : ListRep h p w) (B : ℕ) (hw : w.length≤B) :
    Runs unboundedOutput (OutputState.mk p h []).encode (OutputState.mk 0 h w.reverse).encode
      ((untilBound outputStepProgram PolyProgram.head 4 1).eval
        (magnitude (B::(OutputState.mk p h []).encode))) := by
  have he := ho.output_padded [] hw
  simp only [List.append_nil] at he
  have hh:=run_until outputStepProgram PolyProgram.head 4 1 outputStep_safe
    (by intro u hu; change u.headI=0 at hu; simp [outputStep,hu])
    (OutputState.mk p h []).encode B
    (by rw [he]; rfl)
  simpa only [he,unboundedOutput] using hh

end

open Turing.ToPartrec Polynomial
noncomputable section

lemma unboundedWords_run {c v w B} (hr : Runs c v w B) (hl : w.length≤B) (base : Heap) :
    ∃h,Runs unboundedWordsCode (initialState c v base).encode (w++w.reverse++2::words h)
      (unboundedWordsBound.eval (magnitude (B::(initialState c v base).encode))) ∧
      magnitude (w++w.reverse++2::words h)≤
        unboundedWordsBound.eval (magnitude (B::(initialState c v base).encode)) := by
  let M:=magnitude (B::(initialState c v base).encode)
  have hci : magnitude ((3*B+1)::(initialState c v base).encode)≤unboundedControllerInput.eval M := by
    simp only [unboundedControllerInput,eval_add,eval_mul,eval_X,eval_ofNat,M,magnitude_cons]
    omega
  obtain ⟨h,out,ho,hm0,hr0⟩:=unboundedControl_run hr base
  have hm : magnitude (State.mk 2 0 out 0 h).encode≤unboundedControllerState.eval M :=
    by simpa only [unboundedControllerState,eval_comp] using hm0.trans (evalNat_mono _ hci)
  have hc := hr0.mono (evalNat_mono _ hci)
  have hp := (prepareUnboundedProgram.run (State.mk 2 0 out 0 h).encode).mono (evalNat_mono _ hm)
  have hps := (prepareUnboundedProgram.size (State.mk 2 0 out 0 h).encode).trans (evalNat_mono _ hm)
  have hprep : prepareUnbounded (State.mk 2 0 out 0 h).encode=(OutputState.mk out h []).encode := by
    simp only [prepareUnbounded,State.encode,OutputState.encode,Expr.eval,List.cons_append,
      List.nil_append,List.drop_succ_cons,List.drop_zero,List.headI_cons]
    rfl
  rw [hprep] at hp hps
  have hp' : Runs prepareUnboundedProgram.code (State.mk 2 0 out 0 h).encode (OutputState.mk out h []).encode (unboundedPrepared.eval M) := by
    simpa only [unboundedPrepared,eval_comp] using hp
  have hps' : magnitude (OutputState.mk out h []).encode≤unboundedPrepared.eval M := by
    simpa only [unboundedPrepared,eval_comp] using hps
  have hB : B≤M := by simp only [M,magnitude_cons]; omega
  have hoi : magnitude (B::(OutputState.mk out h []).encode)≤unboundedOutputInput.eval M := by
    simp only [unboundedOutputInput,eval_add,eval_X,eval_one,magnitude_cons]
    omega
  have hout := (unboundedOutput_run ho B hl).mono (evalNat_mono _ hoi)
  have hes := ho.output_padded [] hl
  simp only [List.append_nil] at hes
  have hos : magnitude (OutputState.mk 0 h w.reverse).encode≤unboundedOutputState.eval M := by
    have hh := iterate_magnitude 4 1 outputStep_safe B (OutputState.mk out h []).encode B le_rfl
    rw [hes] at hh
    have hh' : magnitude (OutputState.mk 0 h w.reverse).encode≤
        (untilStateBound 4 1).eval (magnitude (B::(OutputState.mk out h []).encode)) := by
      simpa only [untilStateBound,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one] using hh
    simpa only [unboundedOutputState,eval_comp] using hh'.trans (evalNat_mono _ hoi)
  have hd := ((PolyProgram.drop 2).run (OutputState.mk 0 h w.reverse).encode).mono (evalNat_mono _ hos)
  have hds := ((PolyProgram.drop 2).size (OutputState.mk 0 h w.reverse).encode).trans (evalNat_mono _ hos)
  have hv := (reversePrefixProgram.run ((OutputState.mk 0 h w.reverse).encode.drop 2)).mono (evalNat_mono _ hds)
  have hvs := (reversePrefixProgram.size ((OutputState.mk 0 h w.reverse).encode.drop 2)).trans (evalNat_mono _ hds)
  have he : (prefixStep^[((OutputState.mk 0 h w.reverse).encode.drop 2).headI]
      (0::((OutputState.mk 0 h w.reverse).encode.drop 2).tail)).tail=w++w.reverse++2::words h := by
    change (prefixStep^[w.reverse.length] (0::(w.reverse++2::words h))).tail=_
    rw [reversePrefix_spec,List.reverse_reverse]
  rw [he] at hv hvs
  dsimp only [M] at *
  refine ⟨h,?_,?_⟩
  · apply (run_comp (run_comp (run_comp (run_comp hc hp') hout) hd) hv).mono
    simp only [unboundedWordsBound,eval_add,eval_comp,eval_ofNat,unboundedPrepared,
      unboundedDropped,unboundedControllerState,unboundedOutputState]
    omega
  · apply hvs.trans
    simp only [unboundedWordsBound,unboundedPrepared,unboundedDropped,unboundedControllerState,
      unboundedOutputState,eval_add,eval_comp,eval_ofNat]
    omega
end
end MinUncut.Costed.Arena

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_UnboundedGraphBase
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed.Arena
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Turing.ToPartrec Polynomial
open MinUncutGames.Foundations.Complexity
noncomputable section

def unboundedGraphMachine_outputs_base {c : Code} {v : List ℕ} {B n k : ℕ}
    {table : List Bool} {rest : List ℕ} (base : Heap)
    (hc : Runs c v (n::(table.map Bool.toNat++2::k::rest)) B)
    (hl : (n::(table.map Bool.toNat++2::k::rest)).length≤B) :
    TM2OutputsInTime unboundedGraphMachine (trList ((initialState c v base).encode))
      (some (MinUncutGames.BinaryEncoding.nameBits n++table++MinUncutGames.BinaryEncoding.nameBits k))
      (unboundedGraphTime.eval (magnitude (B::(initialState c v base).encode))) := by
  apply Classical.choice
  obtain ⟨h,hr,hm⟩ := unboundedWords_run hc hl base
  let junk := rest++(n::(table.map Bool.toNat++2::k::rest)).reverse++2::words h
  have he' : (n::(table.map Bool.toNat++2::k::rest))++
      (n::(table.map Bool.toNat++2::k::rest)).reverse++2::words h=
      n::(table.map Bool.toNat++2::k::junk) := by
    simp only [List.cons_append,List.append_assoc,junk]
  rw [he'] at hr hm
  obtain ⟨t,ht,hr⟩ := hr
  have h1 := hr.finiteMachine
  have h2 := GraphCodec.outputsInTime n k table junk
  have h2' : TM2OutputsInTime GraphCodec.machine
      ((trList (n::(table.map Bool.toNat++2::k::junk))).map id)
      (some (MinUncutGames.BinaryEncoding.nameBits n++table++MinUncutGames.BinaryEncoding.nameBits k))
      (2*bitsize (n::(table.map Bool.toNat++2::k::junk))+
        (MinUncutGames.BinaryEncoding.nameBits n++table++MinUncutGames.BinaryEncoding.nameBits k).length+2) := by
    have input_eq : @List.map (GraphCodec.machine.Γ GraphCodec.machine.k₀)
        (GraphCodec.machine.Γ GraphCodec.machine.k₀) id
        (trList (n::(table.map Bool.toNat++2::k::junk))) =
        trList (n::(table.map Bool.toNat++2::k::junk)) := List.map_id _
    simpa only [input_eq] using h2
  have hh := MachineSequential.execute (codeMachine unboundedWordsCode) GraphCodec.machine id Γ'.cons
    _ _ _ _ _ h1 h2'
  have hb := bitsize_le_magnitude (n::(table.map Bool.toNat++2::k::junk))
  have ho := GraphRegisters.codec_length_le n k table junk
  refine ⟨⟨hh.toEvalsTo,hh.steps_le_m.trans ?_⟩⟩
  change t+1+2*((trList (n::(table.map Bool.toNat++2::k::junk))).length+1)+
    (2*bitsize (n::(table.map Bool.toNat++2::k::junk))+
      (MinUncutGames.BinaryEncoding.nameBits n++table++MinUncutGames.BinaryEncoding.nameBits k).length+2)≤_
  simp only [unboundedGraphTime,eval_add,eval_mul,eval_C,eval_ofNat]
  simp only [bitsize] at hb ⊢
  omega
end
end MinUncut.Costed.Arena

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_FiberGraphMachine
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Costed.Arena
open _root_.Turing _root_.OAI.Turing Turing.ToPartrec _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Polynomial
open MinUncutGames.Foundations.Complexity MinUncutGames.BinaryEncoding

lemma exists_graph_initializer {f : ℕ → List ℕ → List ℕ} (P : ∀K,PolyProgram (f K))
    (he : Computable (fun K=>(P K).code)) :
    ∃c : Code,∀K,∃p : Polynomial ℕ,∀xs n table k junk,
      f K xs=n::((table : List Bool).map Bool.toNat++2::k::junk) →
      Nonempty (TM2OutputsInTime (initializedGraphMachine c)
        (trList (K::(encodeWords xs).map FrameDecode.symbol))
        (some (nameBits n++table++nameBits k)) (p.eval (encodeWords xs).length)) := by
  obtain ⟨c,hc⟩:=Init.exists_initializer he
  refine ⟨c,fun K=>?_⟩
  obtain ⟨p,hp⟩:=hc K
  let q:Polynomial ℕ:=p.comp (C (K+1)+C 3*X)
  let r:Polynomial ℕ:=q+1+C 2*(q+1)+unboundedGraphTime.comp ((P K).bound+1+q)
  refine ⟨r,fun xs n table k junk ho=>?_⟩
  let v:=(encodeWords xs).map FrameDecode.symbol
  let b:=Init.base (P K).code xs K v
  let w:=(initialState (P K).code xs b).encode
  have hs:magnitude (K::v)≤(C (K+1)+C 3*X : Polynomial ℕ).eval (encodeWords xs).length:=by
    have hh:=FrameDecode.magnitude_symbols (encodeWords xs)
    simp only [magnitude_cons,eval_add,eval_C,eval_mul,eval_X]
    dsimp only [v]
    omega
  have hpbound:=evalNat_mono p hs
  have hir: Runs c (K::v) w (q.eval (encodeWords xs).length):=
    (hp xs).1.mono (by simpa only [q,eval_comp] using hpbound)
  have his: magnitude w≤q.eval (encodeWords xs).length:=
    (hp xs).2.trans (by simpa only [q,eval_comp] using hpbound)
  have hg:Runs (P K).code xs (n::(table.map Bool.toNat++2::k::junk))
      ((P K).bound.eval (encodeWords xs).length):=by
    have hh:=(P K).run xs
    rw [ho,magnitude_words] at hh
    exact hh
  have hl:(n::(table.map Bool.toNat++2::k::junk)).length≤(P K).bound.eval (encodeWords xs).length:=by
    have hh:=(magnitude_length (f K xs)).trans ((P K).size xs)
    simpa only [ho,magnitude_words] using hh
  let h2:=unboundedGraphMachine_outputs_base b hg hl
  obtain ⟨t,ht,hr⟩:=hir
  let h1:=hr.finiteMachine
  let h2':TM2OutputsInTime unboundedGraphMachine ((trList w).map id)
      (some (nameBits n++table++nameBits k))
      (unboundedGraphTime.eval (magnitude ((P K).bound.eval (encodeWords xs).length::w))) := by
    have input_eq : @List.map (unboundedGraphMachine.Γ unboundedGraphMachine.k₀)
        (unboundedGraphMachine.Γ unboundedGraphMachine.k₀) id (trList w) = trList w :=
      List.map_id _
    simpa only [input_eq] using h2
  have hh:=MachineSequential.execute (codeMachine c) unboundedGraphMachine id Γ'.cons
    _ _ _ _ _ h1 h2'
  have hwb: (trList w).length≤q.eval (encodeWords xs).length:= (bitsize_le_magnitude w).trans his
  have hm:magnitude ((P K).bound.eval (encodeWords xs).length::w)≤
      (((P K).bound+1+q).eval (encodeWords xs).length):=by
    simp only [magnitude_cons,eval_add,eval_one]
    omega
  have hb:=evalNat_mono unboundedGraphTime hm
  simp only [eval_add,eval_one] at hb
  exact ⟨⟨hh.toEvalsTo,hh.steps_le_m.trans (by
    simp only [r,eval_add,eval_one,eval_mul,eval_C,eval_comp]
    change t+1+2*((trList w).length+1)+_≤_
    omega)⟩⟩
end MinUncut.Costed.Arena

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_DecodedGraphCore
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Costed.Arena
open _root_.Turing _root_.OAI.Turing Turing.ToPartrec _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Polynomial
open MinUncutGames.Foundations.Complexity MinUncutGames.BinaryEncoding

def decoded_outputs (c : Code) (K : ℕ) (v out : List Bool) (B : ℕ)
    (hr : TM2OutputsInTime (initializedGraphMachine c)
      (trList (K::v.map FrameDecode.symbol)) (some out) B) :
    TM2OutputsInTime (decodedMachine c) (nameBits K++v) (some out)
      (B+2*(nameBits K).length+3*(K+1)+4+11*v.length) := by
  let w:=trList (K::v.map FrameDecode.symbol)
  let h1:=FrameDecode.outputs K v
  let h2:TM2OutputsInTime (initializedGraphMachine c) (w.map id) (some out) B:=by
    have input_eq : @List.map ((initializedGraphMachine c).Γ (initializedGraphMachine c).k₀)
        ((initializedGraphMachine c).Γ (initializedGraphMachine c).k₀) id w = w := List.map_id _
    simpa only [input_eq] using hr
  have hh:=MachineSequential.execute FrameDecode.machine (initializedGraphMachine c)
    id Γ'.cons _ _ _ _ _ h1 h2
  have hv:=FrameDecode.magnitude_symbols v
  have hw:w.length≤K+1+3*v.length:=by
    have h:=(bitsize_le_magnitude (K::v.map FrameDecode.symbol))
    simp only [magnitude_cons] at h
    exact h.trans (by omega)
  refine ⟨hh.toEvalsTo,hh.steps_le_m.trans ?_⟩
  change 2*(nameBits K++v).length+w.length+2+2*(w.length+1)+B≤_
  simp only [List.length_append]
  omega
end MinUncut.Costed.Arena

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CompleteGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncut.FiniteProof MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Foundations.Target MinUncut.SourceTemplate GraphRegisters

variable {J : ℕ} (P : Parameters J)
  (E : Enumeration (Index (Fin P.o.t) P.o.k P.d.m P.d.n P.grid))

def graphStageProgram : PolyProgram (graphStageWords P E) :=
  GraphRegisters.rawRenderer.comp (demandStageProgram
    (localExpressions E (rationalRate J P.d) (rationalBudgets J P.d P.o)
      (rationalSigma J) (rationalEta J)) P.o.t P.denominatorCoefficient)

def completeGraphWords (u D : ℕ) (v : List ℕ) : List ℕ :=
  graphStageWords P E (sourceStageWords u D v)

def completeGraphProgram (u D : ℕ) : PolyProgram (completeGraphWords P E u D) :=
  (graphStageProgram P E).comp (sourceStageProgram u D)

lemma completeGraphWords_spec (F : Formula) (u D : ℕ) (hD : 0<D) (hne : F.clauses≠[]) :
    ∃junk,completeGraphWords P E u D (MinUncutGames.Foundations.Complexity.formulaWords F)=
      let input:=sourceInput F u D hD
      let ds := generatedDemands input E (rationalRate J P.d) (rationalBudgets J P.d P.o)
        (rationalSigma J) (rationalEta J)
      ((paddedVariableEncoding input.«variables» P.o.t).size+ds.length*3)::
        ((canonicalTable ds).map Bool.toNat++2::(5*P.denominator (Fin input.equations.length))::junk) := by
  obtain ⟨rest,hr⟩:=sourceStageWords_spec F u D hD hne
  simp only [completeGraphWords,hr]
  exact graphStageWords_spec P E _ _

end MinUncut.Costed.SourceWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_GraphCoreMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Costed.Framed
open _root_.Turing _root_.OAI.Turing MinUncutGames.Foundations.Complexity
variable (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)
def embedded (acc : List Bool) (c : M.Cfg) : (machine M ei eo).Cfg :=
  MachineEmbedding.configuration (some (.inr (some true))) none (fun _ : Unit=>acc) c
lemma read_step (b : Bool) (v acc : List Bool) :
    (machine M ei eo).step (readCfg M ei eo none (b::v) acc)=
      some (if b then readCfg M ei eo (some false) v (b::acc)
        else embedded M ei eo (b::acc) (initList M (v.map ei.symm))) := by
  change some (TM2.stepAux (extra M ei eo none) (M.initialState,none) (readTapes M ei (b::v) acc))=_
  cases b <;> simp only [extra,TM2.stepAux,read_input,List.map_cons,List.head?_cons,Option.map_some,
    Equiv.apply_symm_apply,Option.getD_some,List.tail_cons,
    Bool.cond_false,Bool.cond_true,Bool.false_eq_true,ite_false,ite_true]
  all_goals
    congr 2
    funext k
    cases k with
    | inl k =>
      by_cases h:k=M.k₀
      · subst k; simp [readTapes,initList]
      · simp [readTapes,initList,Function.update,h]
    | inr k => cases k; simp [readTapes,Function.update]
open MinUncutGames.BinaryEncoding
lemma read_frames (bits v acc : List Bool) :
    Steps (machine M ei eo).step (frame bits).length
      (readCfg M ei eo none (frame bits++v) acc)
      (embedded M ei eo ((frame bits).reverse++acc) (initList M (v.map ei.symm))) := by
  induction bits generalizing acc with
  | nil => exact steps_one (read_step M ei eo false v acc)
  | cons b bits ih =>
    have h1 := steps_one (read_step M ei eo true (b::(frame bits++v)) acc)
    have h2 := steps_one (payload_step M ei eo b (frame bits++v) (true::acc))
    have hh := steps_trans (steps_trans h1 h2) (ih (b::true::acc))
    simpa only [frame,List.cons_append,List.length_cons,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.nil_append,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh
lemma finish_step (b : Bool) (w acc : List Bool) :
    (machine M ei eo).step (embedded M ei eo (b::acc) (haltList M (w.map eo.symm)))=
      some (embedded M ei eo acc (haltList M ((b::w).map eo.symm))) := by
  change some (TM2.stepAux (extra M ei eo (some true)) (M.initialState,none)
    (MachineEmbedding.tapes (haltList M (w.map eo.symm)).stk (fun _ : Unit=>b::acc)))=_
  simp only [extra,TM2.stepAux,MachineEmbedding.tapes_inr,List.head?_cons,List.tail_cons,
    Option.isSome_some,Bool.cond_true,Option.getD_some]
  congr 2
  funext k
  cases k with
  | inl k =>
    by_cases h:k=M.k₁
    · subst k; simp [haltList,Function.update]
    · simp [haltList,Function.update,h]
  | inr k => cases k; simp [haltList,Function.update]
lemma finish_empty (w : List Bool) :
    (machine M ei eo).step (embedded M ei eo [] (haltList M (w.map eo.symm)))=
      some (haltList (machine M ei eo) (w.map eo.symm)) := by
  change some (TM2.stepAux (extra M ei eo (some true)) (M.initialState,none)
    (MachineEmbedding.tapes (haltList M (w.map eo.symm)).stk (fun _ : Unit=>[])))=_
  simp only [extra,TM2.stepAux,MachineEmbedding.tapes_inr,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false]
  congr 2
  funext k
  cases k with
  | inl k =>
    by_cases h:k=M.k₁
    · subst k
      simp [haltList,Function.update,machine]
      rfl
    · simp [haltList,Function.update,h,machine]
  | inr k => cases k; simp [Function.update,machine]
lemma finish_steps (w acc : List Bool) :
    Steps (machine M ei eo).step (acc.length+1)
      (embedded M ei eo acc (haltList M (w.map eo.symm)))
      (haltList (machine M ei eo) ((acc.reverse++w).map eo.symm)) := by
  induction acc generalizing w with
  | nil => exact steps_one (finish_empty M ei eo w)
  | cons b acc ih =>
    have hh:=steps_head (finish_step M ei eo b w acc) (ih (b::w))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

def execute (K : ℕ) (v w : List Bool) (B : ℕ)
    (h : TM2OutputsInTime M (v.map ei.symm) (some (w.map eo.symm)) B) :
    TM2OutputsInTime (machine M ei eo) ((nameBits K++v).map ei.symm)
      (some ((nameBits K++w).map eo.symm)) (B+2*(nameBits K).length+1) := by
  have hr := steps_timed (read_frames M ei eo K.bits v []) le_rfl
  simp only [List.append_nil,read_init] at hr
  let hm := MachineComposition.embeddedExecution (some (.inr (some true))) none
    (fun _ : Unit=>(nameBits K).reverse) M.m (extra M ei eo) h
  have hf := steps_timed (finish_steps M ei eo w (nameBits K).reverse) le_rfl
  simp only [List.length_reverse,List.reverse_reverse] at hf
  let hh := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hr hm
  let hh' := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hh hf
  exact ⟨hh'.toEvalsTo,by have hb:=hh'.steps_le_m; change _≤B+2*(nameBits K).length+1; simp only [nameBits] at hb ⊢; omega⟩
end MinUncut.Costed.Framed

end
end

end OAI
end


