-- Prove2me | Definitions.Def_OAIQ053K074
-- name    : OAIQ053K074
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:21:11.044159+00:00
-- url     : https://prove2.me/theorems/0672b4c5-79f9-42ca-b128-e27aa2a052af
-- title:
--   Definitions bundle OAIQ053K074 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 22 definitions, 2 instances and 11 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.CloudSpec.localGraph`, `OAI.MetricKMedian.PCP.Compiler.CloudSpec.vertexCode`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.Width`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.allLegal`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.badRoot`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.badTable`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.goodNodes`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.goodRoot`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.nodeEquiv`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.nodeOrder`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.portOrder`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.rootEquiv`, `OAI.MetricKMedian.Reduction.Enumeration.branches`, `OAI.MetricKMedian.Reduction.Enumeration.choices`, `OAI.MetricKMedian.Reduction.Program.allList`, `OAI.MetricKMedian.Reduction.Program.branchOut`, `OAI.MetricKMedian.Reduction.Program.completions`, `OAI.MetricKMedian.Reduction.Program.endpoints`, `OAI.MetricKMedian.Reduction.Program.ordinarySet`, `OAI.MetricKMedian.Reduction.Program.outcomes`, `OAI.MetricKMedian.Reduction.Program.values`, `OAI.MetricKMedian.SparsePrepared.coupled`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_PaddingSpec`, `KMedian_CookLevin_SeedInput`, `KMedian_CookLevin_TableauQueryProgram`, `KMedian_Machines_LocalCompiler`, `KMedian_Machines_LocalSpec`, `KMedian_Programs_BoundedEnumerationProgram`, `KMedian_Programs_BranchProgram`, `KMedian_Programs_RestrictionProgram`, `KMedian_Projection_RegularTable`, `KMedian_Projection_RepairProgram`, `KMedian_Projection_SeedTables`, `KMedian_Reduction_DeletionProgram`, `KMedian_Reduction_OrdinaryListProgram`, `KMedian_Reduction_ReductionOutcomesProgram`, `KMedian_Sparse_SparseCoupledPreparation`, `KMedian_Sparse_SparseOuterMoments`, `KMedian_Sparse_SparsePreparedProbability`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K063`, `OAIQ053K066`, `OAIQ053K067`, `OAIQ053K068` and `OAIQ053K069` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K077` and `OAIQ053K078`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K063
import Definitions.Def_OAIQ053K066
import Definitions.Def_OAIQ053K067
import Definitions.Def_OAIQ053K068
import Definitions.Def_OAIQ053K069

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PaddingSpec
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPaddingSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
variable (t : CSPTable A) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable def vertexCode (v : GlobalRegularization.Node (C t h)) : ℕ :=
  (ExpanderFamily.vertexEquiv _ v).val
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPPaddingSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_LocalSpec
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLocalSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder RegularProgram

variable {A : Type} [Fintype A] [DecidableEq A]
variable (t : CSPTable A) (h : t.WellFormed)
noncomputable abbrev localGraph := FlexibleCloud.regularGraph (C t h) (cloudEmbed (C t h) (EO t))
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPLocalSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_RepairProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionRepairProgram
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic RegularProgram CloudProgram
open scoped Classical

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
variable [Coding A]
omit [Inhabited A] [Coding A] in
lemma poly_legal : Poly (fun z : (CSPTable A×ℕ)×Port =>legal z.1.1 z.1.2 z.2) := by
  have hh : Poly (fun z : Finset (A×A)×Bool =>z.1.filter (fun a=>z.2=true → a.1=a.2)) := hardcoded _
  have hn : Poly (fun z : (CSPTable A×ℕ)×Port =>decide ((rotate z.1.1 z.1.2 z.2).1=z.1.2)) := by
    exact Poly.nat_eq.comp (Poly.pair (Poly.fst.comp poly_rotate) (Poly.snd.comp Poly.fst))
  apply poly_congr (hh.comp (Poly.pair poly_allowed hn))
  intro z
  simp only [decide_eq_true_eq,legal]
noncomputable def allLegal (t : CSPTable A) : Bool :=
  (List.range (global t).length).all (fun v => (Ordered.fixed Port).entries.all (fun d => decide ((legal t v d).Nonempty)))
omit [Inhabited A] [Coding A] in
lemma poly_allLegal : Poly (allLegal (A:=A)) := by
  have hh : Poly (fun s : Finset (A×A)=>decide s.Nonempty) := hardcoded _
  unfold allLegal
  apply Poly.list_all
  · apply Poly.list_all
    · exact hh.comp (poly_legal.comp (show Poly (fun z : (CSPTable A×ℕ)×Port =>z) from Poly.identity))
    · exact Automatic.Poly.const _
  · exact Poly.list_indices.comp poly_global
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPProjectionRepairProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_RegularTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionRegularTable
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic RegularProgram CloudProgram ProjectionTable
open scoped Classical

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A] [Coding A] [Hardcoded A]

variable (t : CSPTable A) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable abbrev nodeEquiv := ExpanderFamily.vertexEquiv (GlobalRegularization.depth (CloudSpec.C t h))
noncomputable def nodeOrder : Ordered (GlobalRegularization.Node (CloudSpec.C t h)) :=
  (Ordered.fin _).map (nodeEquiv t h).symm
noncomputable def rootEquiv := ((nodeEquiv t h).prodCongr (Fintype.equivFin Port)).trans finProdFinEquiv
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPProjectionRegularTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_SeedTables
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedTables
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic Amplifier ProjectionTable
open scoped Classical

noncomputable def portOrder : Ordered ProjectionSeed.Port := (Ordered.fixed (RegularProgram.Port×Bool)).prod (Ordered.fixed Bool)
noncomputable def badRoot := Fintype.equivFin ((ProjectionSeed.Degree×Bool)×Bool)
noncomputable def badTable : ProjectionTable ProjectionSeed.LeftLabel ProjectionSeed.RightLabel :=
  build ProjectionSeed.bad badRoot badNodes portOrder
variable (t : CSPTable Label) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable def goodRoot := ((rootEquiv t h).prodCongr (Fintype.equivFin Bool)).trans finProdFinEquiv
noncomputable def goodNodes := (nodeOrder t h).prod (Ordered.fixed Bool)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_SeedInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedInput
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic Amplifier ProjectionTable
open scoped Classical

noncomputable abbrev Width (n : ℕ) := (portOrder.nested n).entries.length
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedInput

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterMoments
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open SparseGridRounding (base)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem activation_variance (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m) (i : Fin n) :
    (law D c q hc hq).realIndex.variance
      (fun a => (activation D q (law D c q hc hq).states[a.val] e i:ℝ)) ≤
      ((if i∈D e then q e else 0:ℚ):ℝ) := by
  apply FiniteLaw.adjacent_variance _ _
    (m := ((if i∈D e then (base q e:ℚ) else 0:ℚ):ℝ)) ?_ ?_
    (activation_real_mean D c q hc hq e i)
  · split_ifs <;> positivity
  · intro a _
    rcases activation_adjacent D c q hc hq a e i with hh | hh
    · exact Or.inl (by exact_mod_cast hh)
    · exact Or.inr (by exact_mod_cast hh)

theorem deficit_variance (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (g : ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (i : Fin n) :
    (law D c q hc hq).realIndex.variance (fun a => (deficit D q g (law D c q hc hq).states[a.val] i:ℝ)) ≤
      (g:ℝ)^2*(targetMean D q i:ℝ) := by
  have hh := FiniteLaw.variance_sum_le (law D c q hc hq).realIndex
    (fun e a => (activation D q (law D c q hc hq).states[a.val] e i:ℝ))
    (fun e => ((if i∈D e then q e else 0:ℚ):ℝ))
    (fun e => ((if i∈D e then q e else 0:ℚ):ℝ))
    (fun e => activation_real_mean D c q hc hq e i)
    (fun e => activation_variance D c q hc hq e i)
    (fun e f hef => activation_real_pair D c q hc hq e f hef i i)
  simp only [deficit,Rat.cast_mul,Rat.cast_sum,FiniteLaw.variance_mul,targetMean]
  exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)

theorem clipping_budget (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (g : ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (δ : Fin n → ℝ) {γ : ℝ} (hg : 0 ≤ g) (hγ : 0 < γ) (hδ : ∀ i, 0 ≤ δ i)
    (hmean : ∀ i, (g:ℝ)*(targetMean D q i:ℝ)=(1+γ)*δ i)
    (hsmall : ∀ i, (1+γ)*δ i ≤ 1/4) :
    1-4*(g:ℝ)*(1+γ)/γ ≤ (law D c q hc hq).realIndex.prob (fun a =>
      (∑ i, ((deficit D q g (law D c q hc hq).states[a.val] i:ℝ)-
        min (deficit D q g (law D c q hc hq).states[a.val] i:ℝ) (1/2))) ≤ γ*∑ i,δ i) := by
  classical
  apply FiniteLaw.clipping_budget _ _ δ (by exact_mod_cast hg) hγ hδ
  · intro i
    rw [deficit_mean,hmean]
    exact hsmall i
  · intro i
    have hh := deficit_variance D c q g hc hq i
    have he : (g:ℝ)^2*(targetMean D q i:ℝ)=(g:ℝ)*(1+γ)*δ i := by
      rw [pow_two,mul_assoc,hmean]
      ring
    exact hh.trans_eq he

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePreparedProbability
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem opening_probability (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) (g : ℚ)
    (δ : Fin n → ℝ) {γ B : ℝ} (hg : 0 < g) (hγ : 0 < γ)
    (heven : Even Δ) (hunit : g*(Δ:ℚ)=1) (hδ : ∀ j,0 ≤ δ j)
    (hmean : ∀ j,(g:ℝ)*(targetMean D q j:ℝ)=(1+γ)*δ j)
    (hsmall : ∀ j,(1+γ)*δ j ≤ 1/4)
    (hplan : (g:ℝ)*(((n:ℚ)*(Δ:ℚ)+(∑ e,SparseSignedPreparation.signed D c e*q e):ℚ):ℝ)=
      B-γ*∑ j,δ j) :
    1-4*(g:ℝ)*(1+γ)/γ ≤ (SparseOuterLaw.law D c q hc hq).realIndex.prob (fun a =>
      (g:ℝ)*(opening D c q Δ (SparseOuterLaw.law D c q hc hq).states[a.val]:ℝ) ≤ B+3*(g:ℝ)) := by
  classical
  apply (SparseOuterLaw.clipping_budget D c q g hc hq δ hg.le hγ hδ hmean hsmall).trans
  apply FiniteLaw.prob_mono
  intro a ha
  have hh0 := opening_le D c q Δ hc hq a
  have hh : (opening D c q Δ (SparseOuterLaw.law D c q hc hq).states[a.val]:ℝ) ≤
      (((n:ℚ)*(Δ:ℚ)+(∑ e,SparseSignedPreparation.signed D c e*q e):ℚ):ℝ)+3+
      ∑ j,(discarded D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ) := by
    exact_mod_cast hh0
  have hhg := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ g by exact_mod_cast hg.le)
  have hdiscard : (g:ℝ)*(∑ j,(discarded D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ))=
      ∑ j,((deficit D q g (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ)-
        min (deficit D q g (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ) (1/2)) := by
    rw [mul_sum]
    exact sum_congr rfl (fun j _ => discarded_mass D q Δ _ j hg heven hunit)
  rw [mul_add,mul_add,hplan,hdiscard] at hhg
  linarith only [hhg,ha]

theorem total_deviation (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) (g : ℚ)
    (p δ : Fin n → ℝ) {γ : ℝ} (hg : 0 < g) (hγ : 0 ≤ γ)
    (heven : Even Δ) (hunit : g*(Δ:ℚ)=1) (hδ : ∀ j,0 ≤ δ j)
    (hδhalf : ∀ j,δ j ≤ 1/2) (hp : ∀ j,p j+δ j=1)
    (hmean : ∀ j,(g:ℝ)*(targetMean D q j:ℝ)=(1+γ)*δ j) (j : Fin n) :
    (SparseOuterLaw.law D c q hc hq).realIndex.expect (fun a =>
      |(g:ℝ)*(total D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ)-p j|) ≤
      γ*δ j+Real.sqrt ((g:ℝ)*(1+γ)*δ j) := by
  have hvar := SparseOuterLaw.deficit_variance D c q g hc hq j
  have he : (g:ℝ)^2*(targetMean D q j:ℝ)=(g:ℝ)*(1+γ)*δ j := by
    rw [pow_two,mul_assoc,hmean]
    ring
  rw [he] at hvar
  have hh := FiniteLaw.rescaling_noise (SparseOuterLaw.law D c q hc hq).realIndex
    (fun a => (deficit D q g (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ))
    (hδ j) (hδhalf j) hγ (show (0:ℝ) ≤ g by exact_mod_cast hg.le)
    ((SparseOuterLaw.deficit_mean D c q g hc hq j).trans (hmean j)) hvar
  apply le_trans (le_of_eq ?_) hh
  apply FiniteLaw.expect_congr_support
  intro a _
  rw [total_deficit_identity D q Δ _ j hg heven hunit]
  congr 1
  linarith only [hp j]

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCoupledPreparation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

theorem request_mean (D : Fin m → Finset (Fin n)) (a q : Fin m → ℚ) (Δ : ℕ)
    (ha : ∀ e, 0 ≤ a e ∧ a e ≤ 1) (hq : ∀ e, 0 ≤ q e) {g : ℝ} (hg : 0 ≤ g)
    (j : Fin n) (e : Fin m) :
    (SparseOuterLaw.law D a q ha hq).realIndex.expect (fun b =>
      g * (requests D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val] j e : ℝ)) ≤
      if j ∈ D e then g * (q e : ℝ) else 0 := by
  calc
    _ ≤ (SparseOuterLaw.law D a q ha hq).realIndex.expect (fun b =>
        g * (activation D q (SparseOuterLaw.law D a q ha hq).states[b.val] e j : ℝ)) := by
      apply FiniteLaw.expect_mono
      intro b
      apply mul_le_mul_of_nonneg_left _ hg
      have h := requests_le D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val] j e
      have he := activationCount_cast D q (SparseOuterLaw.law D a q ha hq).states[b.val] e j
      have hr : (requests D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val] j e : ℚ) ≤
          activation D q (SparseOuterLaw.law D a q ha hq).states[b.val] e j := by
        rw [← he]
        exact_mod_cast h
      exact_mod_cast hr
    _ = _ := by
      rw [FiniteLaw.expect_mul, activation_real_mean]
      split_ifs <;> simp

noncomputable def coupled
    (D : Fin m → Finset (Fin n)) (a q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (ha : ∀ e, 0 ≤ a e ∧ a e ≤ 1) (hq : ∀ e, 0 ≤ q e) (g : ℚ)
    (δ : Fin n → ℝ) (γ B : ℝ)
    (hg : 0 < g) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (heven : Even Δ)
    (hunit : g * (Δ : ℚ) = 1)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hδ : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1/8)
    (hpunit : ∀ j, (p j : ℝ) + δ j = 1)
    (hmean : ∀ j, (g : ℝ) * (targetMean D q j : ℝ) = (1+γ) * δ j)
    (hplan : (g : ℝ) * (((n : ℚ) * (Δ : ℚ) +
      (∑ e, SparseSignedPreparation.signed D a e * q e) : ℚ) : ℝ) = B - γ * ∑ j, δ j) :
    Preparation.CoupledLaw D (fun e => (a e : ℝ)) (fun e => (g : ℝ) * (q e : ℝ))
      P (fun i => (y i : ℝ)) (fun j => (p j : ℝ)) δ (g : ℝ) γ B Δ := by
  let μ := SparseOuterLaw.law D a q ha hq
  let z := fun b : Fin μ.length => μ.states[b.val]
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have huR : (g : ℝ) * (Δ : ℝ) = 1 := by exact_mod_cast hunit
  refine {
    Ω := Fin μ.length
    ν := μ.realIndex
    κ := fun b => SparseRescaledInner.encodedLaw P y p (total D q Δ (z b))
    O := fun b => outsideCount q (z b)
    N := fun b => nominalMass q (g : ℝ) (z b)
    R := fun b => requests D q Δ (z b)
    K := fun b => total D q Δ (z b)
    C := fun b => SparseRescaledInner.encodedCount P y p (total D q Δ (z b))
    open_cap := ?_
    open_zero := ?_
    nominal_nonneg := fun b _ e => nominalMass_nonneg q hgR.le (z b) e
    nominal_cap := fun b _ e => nominalMass_cap D a q ha hq hgR.le b e
    nominal_mean := fun e => nominalMass_mean D a q ha hq (g : ℝ) e
    nominal_variance := fun e => nominalMass_variance D a q ha hq (g : ℝ) e
    nominal_pair := fun e h heh => nominalMass_pair D a q ha hq (g : ℝ) e h heh
    request_cap := ?_
    request_target := ?_
    request_mean := fun j e => request_mean D a q Δ ha hq hgR.le j e
    exact_total := fun b j => exact_total D q Δ (z b) j
    half := fun b j => total_half D q Δ (z b) j hgR heven huR
    total_cap := fun b j => total_le D q Δ (z b) j
    total_deviation := ?_
    pieces := fun b ξ hξ => SparseRescaledInner.encoded_pieces P y p _ Δ hy hp hm
      (total_le D q Δ (z b)) ξ hξ
    piece_mean := fun b j i => SparseRescaledInner.encoded_mean P y p _ Δ (g : ℝ) hy hp hm
      (total_le D q Δ (z b)) j i
    piece_pair := fun b u v huv => SparseRescaledInner.encoded_pair P y p _ Δ (g : ℝ) hy hp hm
      (total_le D q Δ (z b)) u v huv
    piece_variance := fun b u => SparseRescaledInner.encoded_variance P y p _ Δ (g : ℝ) hy hp hm
      (total_le D q Δ (z b)) u
    budget := ?_ }
  · intro b _ e he
    have he' : q e ≤ (Δ : ℚ) := by
      have hr : (q e : ℝ) ≤ (Δ : ℝ) := (mul_le_mul_iff_right₀ hgR).mp (he.trans_eq huR.symm)
      exact_mod_cast hr
    have hcap := outsideCount_le_at D a q ha hq Δ b e he'
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hgR.le).trans_eq huR
  · intro b _ e he
    have hz : q e = 0 := by
      have hr : (q e : ℝ) = 0 := (mul_eq_zero.mp he).resolve_left hgR.ne'
      exact_mod_cast hr
    exact Nat.eq_zero_of_le_zero (outsideCount_le_at D a q ha hq 0 b e (by simp [hz]))
  · intro b _ j e
    exact (requests_le D q Δ (z b) j e).trans (activationCount_le D a q ha hq b e j)
  · intro b j e hj
    have h := requests_le D q Δ (z b) j e
    have hz := activationCount_support D a q ha hq b e j hj
    exact Nat.eq_zero_of_le_zero (h.trans_eq hz)
  · intro j
    exact total_deviation D a q Δ ha hq g (fun j => (p j : ℝ)) δ hg hγ.le heven hunit hδ
      (fun j => (hδ1 j).trans (by norm_num)) hpunit hmean j
  · have hsmall : ∀ j, (1+γ) * δ j ≤ 1/4 := by
      intro j
      calc
        _ ≤ 2 * δ j := mul_le_mul_of_nonneg_right (by linarith only [hγ1]) (hδ j)
        _ ≤ 1/4 := by linarith only [hδ1 j]
    have h := opening_probability D a q Δ ha hq g δ hg hγ heven hunit hδ hmean hsmall hplan
    simpa only [opening_cast] using h

end MetricKMedian.SparsePrepared
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BoundedEnumerationProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
 theorem maskWord_view {n : ℕ} (T : Finset (Fin n)) (ys : List (Fin n)) :
    maskWord (setView T,ys.map Fin.val)=setView ys.toFinset := by
  simp only [maskWord,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def,List.map_map,List.any_eq_true,List.mem_map,id_eq,decide_eq_true_eq,List.mem_toFinset]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,he⟩
    exact (Fin.ext (of_decide_eq_true he)) ▸ ha
  · intro hi
    exact ⟨true,⟨i,hi,by simp⟩,rfl⟩
 theorem words_map {α β : Type} (f : α → β) (c : ℕ) (xs : List α) :
    words c (xs.map f)=(words c xs).map (List.map f) := by
  induction c with
  | zero => rfl
  | succ c ih => simp only [words,List.flatMap_map,List.map_cons,List.map_nil,List.map_flatMap,ih,List.map_map,Function.comp_def]

end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RestrictionProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw )
open MetricKMedian.MaskProgram
def choices {n : ℕ} (T : Finset (Fin n)) (c : ℕ) : List (Finset (Fin n)) :=
  (words c (List.ofFn (T.orderEmbOfFin rfl))).map List.toFinset

def branches (I : Instance) (F : Finset (Fin I.n)) (a : ℕ) : List (Finset (Fin I.n)) :=
  (words a (pairs F)).map (fun ps => witnessedRestriction I F ps.toFinset)
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_DeletionProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw )
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase )
open Completion.Rational.BestProgram (card card_view)
open Enumeration

def values (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) : List ℚ :=
  (choices T c).flatMap (fun D => (List.ofFn (T.orderEmbOfFin rfl)).map (fun i =>
    rationalCost I ((T\D).erase i)-rationalCost I (T\D)))

def endpoints (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) : List (Finset (Fin I.n)) :=
  (0::values I T c).map (fun B => rationalHistory I B T c)
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_ReductionOutcomesProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw )
open Enumeration

def completions (I : Instance) (F U : Finset (Fin I.n)) (δ : ℚ) (b : ℕ) : List (Finset (Fin I.n)) :=
  (choices U b).flatMap (fun H => (choices F b).map (fun B => completionSet I F B (U\H) (rationalRadii I U) δ))

def outcomes (I : Instance) (F T : Finset (Fin I.n)) (δ : ℚ) (c b : ℕ) : List (Finset (Fin I.n)) :=
  T::(endpoints I T c).flatMap (fun U => U::completions I F U δ b)
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw )
open Completion.Rational.BestProgram (card card_view)
open Enumeration
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
def branchOut (B : Branch) : List (Finset (Fin B.original.n)) :=
  if h : B.allowed then outcomes B.original B.facilities ((B.restricted h).computedPseudo r hr p c) δ c b else []
def allList (I : Instance) : List (Finset (Fin I.n)) :=
  (branches I I.facilities a).flatMap (fun F => branchOut r hr p c b δ ⟨I,F⟩)
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_OrdinaryListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw )
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
def ordinarySet (I : Instance) : Finset (Fin I.n) :=
  if I.zeroTest then I.zeroOutput else selectList I (allList r hr p c a b δ I)
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauQueryProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauQueryProgram
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Binary Binary.Automatic Tableau Turing.TM2
open scoped Classical

variable {K : Type} {Γ : K→Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀k,Fintype (Γ k)]
variable (M : Λ→Stmt Γ Λ σ) (k0 : K)
noncomputable instance queryCoding : Coding (Query M) := finiteCoding _
noncomputable instance queryHardcoded : Hardcoded (Query M) := ⟨fun _ _ _ f => finite_function f⟩
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauQueryProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_LocalCompiler
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLocalCompiler
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace LocalCompiler
variable {X VC TC Q A : Type} [Coding X] [Coding VC] [Coding TC]
  [Fintype Q] [Fintype A] [DecidableEq A] [DecidableEq VC] [DecidableEq TC]
  [Inhabited X] [Inhabited VC] [Inhabited TC] [Inhabited Q] [Inhabited A]
  [Coding Q] [Hardcoded Q]
variable (vars : X→List VC) (tests : X→List TC) (query : X→TC→Q→VC) (accept : X→TC→Finset (Q→A))
omit [Inhabited X] [Inhabited A] in
lemma poly_table (hv : Poly vars) (ht : Poly tests)
    (hq : Poly (fun p : (X×TC)×Q => query p.1.1 p.1.2 p.2))
    (ha : Poly (fun p : X×TC => accept p.1 p.2))
    (hev : Poly (fun p : VC×VC => decide (p.1=p.2)))
    (het : Poly (fun p : TC×TC => decide (p.1=p.2))) : Poly (table vars tests query accept) := by
  have hr : Poly (fun p : (X×TC)×Q => row vars tests query accept p.1.1 p.1.2 p.2) := by
    have hvv := hv.comp (Poly.fst.comp Poly.fst : Poly (fun p : (X×TC)×Q => p.1.1))
    have htt := ht.comp (Poly.fst.comp Poly.fst : Poly (fun p : (X×TC)×Q => p.1.1))
    have hl : Poly (fun p : (X×TC)×Q => (vars p.1.1).findIdx (fun v => decide (v=query p.1.1 p.1.2 p.2))) :=
      Poly.list_findIdx (hev.comp (Poly.pair Poly.snd (hq.comp Poly.fst))) hvv
    have hi : Poly (fun p : (X×TC)×Q => (tests p.1.1).findIdx (fun u => decide (u=p.1.2))) :=
      Poly.list_findIdx (het.comp (Poly.pair Poly.snd (Poly.snd.comp (Poly.fst.comp Poly.fst)))) htt
    unfold row
    exact Poly.pair hl (Poly.pair (by fun_prop) (poly_relation.comp (Poly.pair (ha.comp Poly.fst) Poly.snd)))
  unfold table
  apply Poly.pair
  · have hvm : Poly (fun x => (vars x).map (fun _=>())) := Poly.list_map (show Poly (fun _ : X×VC => ()) from Automatic.Poly.const ()) hv
    have htm : Poly (fun x => (tests x).map (fun _=>())) := Poly.list_map (show Poly (fun _ : X×TC => ()) from Automatic.Poly.const ()) ht
    exact Poly.list_append.comp (Poly.pair hvm htm)
  · exact Poly.list_flatMap (Poly.list_map hr (Automatic.Poly.const _)) ht
end LocalCompiler
end MetricKMedian.PCP.Compiler

end Inline_PCPLocalCompiler

end OAI
end


