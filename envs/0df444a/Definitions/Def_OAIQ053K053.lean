-- Prove2me | Definitions.Def_OAIQ053K053
-- name    : OAIQ053K053
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:09:23.867495+00:00
-- url     : https://prove2.me/theorems/57a5a2c4-744f-402f-8204-cd293857a4b6
-- title:
--   Definitions bundle OAIQ053K053 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 8 definitions, 3 instances and 22 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.RawWalk.backs`, `OAI.MetricKMedian.PCP.Compiler.RawWalk.port`, `OAI.MetricKMedian.PCP.Compiler.RawWalk.vertexAt`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.LeftSize`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.leftOrder`, `OAI.MetricKMedian.PCP.ProjectionSeed.bad`, `OAI.MetricKMedian.SparseBundleEncoding.law`, `OAI.MetricKMedian.SparseRescaledInner.encodedLaw`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_CookLevin_SeedInput`, `KMedian_Machines_FiniteCoordinates`, `KMedian_Machines_FiniteFilterProgram`, `KMedian_Machines_GridTables`, `KMedian_Machines_LocalCompiler`, `KMedian_Machines_RawWalk`, `KMedian_Machines_RectTables`, `KMedian_Machines_UnaryPolynomial`, `KMedian_Projection_Seed`, `KMedian_Projection_SeedCombinators`, `KMedian_Sparse_SparseBundleEncoding`, `KMedian_Sparse_SparseCardinalFixed`, `KMedian_Sparse_SparseCardinalRounding`, `KMedian_Sparse_SparseSignedFixed`, `KMedian_Sparse_SparseSignedPartial`, `KMedian_Sparse_SparseTargetSubset`, `KMedian_Sparse_SparseWeightedPartial`, `KMedian_Sparse_SparseWeightedRounding`.
--
--   **Imports.** It imports the bundles `OAIQ053K036`, `OAIQ053K037`, `OAIQ053K044`, `OAIQ053K045`, `OAIQ053K046` and `OAIQ053K047` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K059`, `OAIQ053K060` and `OAIQ053K061`; the statement `OAI.MetricKMedian.PCP.ProjectionSeed.bad_bound_s53`; the proof of `OAI.MetricKMedian.PCP.ProjectionSeed.bad_bound_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K036
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K044
import Definitions.Def_OAIQ053K045
import Definitions.Def_OAIQ053K046
import Definitions.Def_OAIQ053K047

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_UnaryPolynomial
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPUnaryPolynomial
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic Polynomial
open scoped Classical

lemma poly_unaryPower (n : ℕ) : Poly (unaryPower n) := by
  induction n with
  | zero => exact Automatic.Poly.const _
  | succ n ih =>
    exact Poly.list_flatMap (ih.comp Poly.fst) Poly.identity
lemma poly_unaryPolynomial (p : Polynomial ℕ) :
    Poly (fun xs : List Unit => List.replicate (p.eval xs.length) ()) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    apply poly_congr (Poly.list_append.comp (Poly.pair hp hq))
    intro xs
    simp only [eval_add,List.replicate_add]
  | monomial n a =>
    have hh : Poly (fun xs : List Unit => (unaryPower n xs).flatMap (fun _ => List.replicate a ())) :=
      Poly.list_flatMap (Automatic.Poly.const _) (poly_unaryPower n)
    apply poly_congr hh
    intro xs
    apply unitList_eq_length
    rw [length_flatMap_uniform _ _ a (by intros; simp),List.length_replicate,
      unaryPower_length,eval_monomial,Nat.mul_comm]
end MetricKMedian.PCP.Compiler

end Inline_PCPUnaryPolynomial

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_FiniteCoordinates
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteCoordinates

namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

noncomputable instance functionCoding {I A : Type} [Fintype I] [Fintype A] : Coding (I → A) := finiteCoding _
end MetricKMedian.PCP.Compiler

end Inline_PCPFiniteCoordinates

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_SeedCombinators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedCombinators
namespace MetricKMedian.PCP.Compiler.SeedCombinators
open Binary Binary.Automatic

variable {T D A : Type} [Coding T] [Coding D] [Coding A]
lemma poly_source (r : T→ℕ→D→ℕ×D) (hr : Poly (fun z : (T×ℕ)×D=>r z.1.1 z.1.2 z.2)) :
    Poly (fun z : (T×ℕ)×(D×Bool)=>source r z.1.1 z.1.2 z.2) := by
  exact Poly.ite (Poly.snd.comp Poly.snd)
    (hr.comp (Poly.pair Poly.fst (Poly.fst.comp Poly.snd)))
    (Poly.pair (Poly.snd.comp Poly.fst) (Poly.fst.comp Poly.snd))
end MetricKMedian.PCP.Compiler.SeedCombinators

end Inline_PCPSeedCombinators

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Seed
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionSeed

namespace MetricKMedian.PCP
open Finset
open scoped Classical BigOperators

namespace ProjectionSeed
open Amplifier

noncomputable def bad : BiProjection ((Degree × Bool) × Bool) (Bool × Bool) LeftPort Port LeftLabel RightLabel :=
  (BiProjection.neutral Bool (Degree × Bool) (Label × Label) Label).prod BiProjection.impossible
lemma bad_consistent : bad.Consistent :=
  BiProjection.consistent_prod _ _ (BiProjection.neutral_consistent _ _ _ _) BiProjection.impossible_consistent
end ProjectionSeed
end MetricKMedian.PCP

end Inline_PCPProjectionSeed

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_SeedInput
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedInput
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic Amplifier ProjectionTable
open scoped Classical

noncomputable def leftOrder := Ordered.fixed ProjectionSeed.LeftLabel
noncomputable abbrev LeftSize (n : ℕ) := (leftOrder.nested n).entries.length
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedInput

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_FiniteFilterProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteFilterProgram
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace FiniteList
variable {A X : Type}
  [Fintype A]
  [Coding A]
  [Coding X]
  [Inhabited A]
noncomputable instance optionCoding : Coding (Option A) := finiteCoding _

end FiniteList
end MetricKMedian.PCP.Compiler

end Inline_PCPFiniteFilterProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_GridTables
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGridTables
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace CSPTable
variable {A T B : Type} [Fintype A] [Coding T] [Coding B]
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq A] [DecidableEq B]
omit [Fintype A] [Coding B] [Fintype V] [Fintype E]
  [DecidableEq E] [DecidableEq A] [DecidableEq B] in
lemma grid_build (C : BinaryCSP V E A) (seeds : List Unit) (ve : V ≃ Fin seeds.length)
    (tags : Ordered B) (ee : V × B ≃ E) (row : ℕ → B → CSPRow A)
    (hr : ∀ v b, row (ve v).val b=((ve (C.left (ee (v,b)))).val,
      (ve (C.right (ee (v,b)))).val,C.allowed (ee (v,b)))) :
    grid seeds tags.entries row=build C (Ordered.indexed ve)
      (((Ordered.indexed ve).prod tags).map ee) := by
  unfold grid build
  apply Prod.ext
  · have h : (Ordered.indexed ve).entries.map (fun _ => ())=seeds := by
      apply List.ext_getElem
      · simp only [List.length_map,Ordered.indexed_length]
      · intros; exact Subsingleton.elim _ _
    exact h.symm
  · rw [← Ordered.indexed_codes ve]
    simp only [Ordered.map,Ordered.prod,List.map_map,List.product, List.flatMap_map,
      List.map_flatMap,Function.comp_def]
    apply congrArg (fun f : V → List (CSPRow A) => (Ordered.indexed ve).entries.flatMap f)
    funext v
    apply List.map_congr_left
    intro b hb
    simp only [Ordered.indexed_index]
    exact hr v b
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPGridTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_LocalCompiler
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
variable {X VC TC Q A : Type}
  [Coding X]
  [Coding VC]
  [Coding TC]
  [Fintype Q]
  [Fintype A]
  [DecidableEq A]
  [DecidableEq VC]
  [DecidableEq TC]
  [Inhabited X]
  [Inhabited VC]
  [Inhabited TC]
  [Inhabited Q]
  [Inhabited A]
  [Coding Q]
noncomputable instance assignmentSetCoding : Coding (Finset (Q→A)) := finiteCoding _
end LocalCompiler
end MetricKMedian.PCP.Compiler

end Inline_PCPLocalCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawWalk
attribute [-instance] _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRawWalk
namespace MetricKMedian.PCP.Compiler.RawWalk
open Binary Binary.Automatic
open scoped Classical

variable {T D A : Type}
  [Coding T]
  [Fintype D]
  [Coding D]
  [Inhabited D]
variable (rotate : T → ℕ → D → ℕ × D)
variable (hp : Poly (fun p : (T × ℕ) × D => rotate p.1.1 p.1.2 p.2))
def port (cap : ℕ) (w : Fin cap → D) (n : ℕ) : D := if h:n < cap then w ⟨n,h⟩ else default
def vertexAt (cap : ℕ) (t:T) (v:ℕ) (w : Fin cap → D) : ℕ → ℕ
  | 0 => v
  | n+1 => (rotate t (vertexAt cap t v w n) (port cap w n)).1
include hp
def backs (cap : ℕ) (t:T) (v:ℕ) (w : Fin cap → D) : Fin cap → D :=
  fun i => (rotate t (vertexAt rotate cap t v w i.val) (w i)).2
omit hp
omit [Coding T] [Fintype D] [Coding D] 
variable {V : Type} (G : PortGraph V D) (code : V → ℕ)
lemma at_correct (t:T) (h : ∀ v d, rotate t (code v) d=(code (G.step v d),G.back v d))
    (cap : ℕ) (p : G.Walk cap) (n : ℕ) (hn : n ≤ cap) :
    vertexAt rotate cap t (code (p.vertex 0)) p.port n=code (p.vertex ⟨n,by omega⟩) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [vertexAt,ih (by omega)]
    simp only [port,dite_eq_left (by omega : n < cap)]
    rw [h]
    exact congrArg code (p.chain ⟨n,by omega⟩)
lemma backs_correct (t:T) (h : ∀ v d, rotate t (code v) d=(code (G.step v d),G.back v d))
    (cap : ℕ) (p : G.Walk cap) (i:Fin cap) :
    backs rotate cap t (code (p.vertex 0)) p.port i=G.back (p.vertex i.castSucc) (p.port i) := by
  unfold backs
  rw [at_correct rotate G code t h cap p i.val (Nat.le_of_lt i.isLt),h]
  rfl
end MetricKMedian.PCP.Compiler.RawWalk

end Inline_PCPRawWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RectTables
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRectTables
namespace MetricKMedian.PCP.Compiler.CSPTable
open Binary Binary.Automatic
open scoped Classical

variable {A T B : Type} [Fintype A] [Coding T] [Coding B]
variable {V E R : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq A] [DecidableEq B] [DecidableEq R]
omit [Fintype A] [Coding B] [Fintype V] [Fintype E] [DecidableEq E]
  [DecidableEq A] [DecidableEq B] [DecidableEq R] in
lemma rect_build (C : BinaryCSP V E A) (seeds roots : List Unit) (ve : V ≃ Fin seeds.length)
    (re : R ≃ Fin roots.length) (tags : Ordered B) (ee : R × B ≃ E) (row : ℕ → B → CSPRow A)
    (hr : ∀ v b, row (re v).val b=((ve (C.left (ee (v,b)))).val,
      (ve (C.right (ee (v,b)))).val,C.allowed (ee (v,b)))) :
    rect seeds roots tags.entries row=build C (Ordered.indexed ve)
      (((Ordered.indexed re).prod tags).map ee) := by
  unfold rect build
  apply Prod.ext
  · have h : (Ordered.indexed ve).entries.map (fun _ => ())=seeds := by
      apply List.ext_getElem
      · simp only [List.length_map,Ordered.indexed_length]
      · intros; exact Subsingleton.elim _ _
    exact h.symm
  · rw [← Ordered.indexed_codes re]
    simp only [Ordered.map,Ordered.prod,List.map_map,List.product,List.flatMap_map,
      List.map_flatMap,Function.comp_def]
    apply congrArg (fun f : R → List (CSPRow A) => (Ordered.indexed re).entries.flatMap f)
    funext v
    apply List.map_congr_left
    intro b hb
    simp only [Ordered.indexed_index]
    exact hr v b
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPRectTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseWeightedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedPartial
open Finset RationalWeightedStep
variable {n : ℕ}

 theorem step_mean (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (μ : SparseIntegerLaw (Vector ℚ n)) (i : Fin n) :
    (step β hβ μ).moment (fun p => point p i)=μ.moment (fun p => point p i) := by
  have hh := μ.step_moment features (probability β) (probability_unit β hβ)
    (endpoint β) (finSumFinEquiv (Sum.inl i))
  simp only [features_single] at hh
  exact hh.trans (μ.moment_congr _ _ (fun a => endpoint_mean β hβ _ i))

 theorem step_pair (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (μ : SparseIntegerLaw (Vector ℚ n)) (i j : Fin n) (hij : i ≠ j) :
    (step β hβ μ).moment (fun p => point p i*point p j) ≤
      μ.moment (fun p => point p i*point p j) := by
  have hh := μ.step_moment features (probability β) (probability_unit β hβ)
    (endpoint β) (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))
  simp only [features_pair] at hh
  exact hh.trans_le (μ.moment_mono _ _ (fun k => endpoint_pair β hβ _ i j hij))

 theorem run_mean (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (t : ℕ) (i : Fin n) :
    (run β hβ p t).moment (fun q => point q i)=point p i := by
  induction t with
  | zero => exact SparseIntegerLaw.dirac_moment _ _
  | succ t ih => rw [run,step_mean,ih]

 theorem run_pair (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (t : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (run β hβ p t).moment (fun q => point q i*point q j) ≤ point p i*point p j := by
  induction t with
  | zero => exact (SparseIntegerLaw.dirac_moment _ _).le
  | succ t ih => exact (step_pair β hβ _ i j hij).trans ih

end MetricKMedian.SparseWeightedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCardinalRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCardinalRounding
open Finset RationalWeightedStep
variable {n : ℕ}

theorem round_mean (p : Vector ℚ n) (i : Fin n) :
    (round p).moment (fun q => point q i)=point p i :=
  SparseWeightedPartial.run_mean _ _ p n i

theorem round_pair (p : Vector ℚ n) (i j : Fin n) (hij : i ≠ j) :
    (round p).moment (fun q => point q i*point q j) ≤ point p i*point p j :=
  SparseWeightedPartial.run_pair _ _ p n i j hij

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCardinalFixed
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.map_states _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedPartial
open RationalWeightedStep

theorem run_positive {n : ℕ} (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (t : ℕ) (a : Fin (run β hβ p t).length) :
    0 < (run β hβ p t).law.rational.weight a := by
  cases t with
  | zero => change 0 < ((1:ℤ):ℚ)/1; norm_num
  | succ t =>
    exact ((run β hβ p t).branch (probability β) (probability_unit β hβ)
      (endpoint β)).compressAuto_positive features a

end MetricKMedian.SparseWeightedPartial

end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBundleEncoding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBundleEncoding
open Finset
variable {n m : ℕ}

noncomputable def law (q : Fin n → Fin m → ℚ) : FiniteLaw (Fin m → Finset (Fin n)) :=
  (SparseBundles.law q).realIndex.map
    (fun a => encode q (SparseBundles.law q).states[a.val])

end MetricKMedian.SparseBundleEncoding

namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

noncomputable def encodedLaw (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) : FiniteLaw (Fin t → Finset (Fin n)) :=
  SparseBundleEncoding.law (piece P y p K)

end MetricKMedian.SparseRescaledInner
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPartial
open Finset RationalSignedStep
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

 theorem step_mean (β : Fin n → ℚ) 
    (μ : SparseIntegerLaw (Vector ℚ n)) (i : Fin n) :
    (step β μ).moment (fun p => point p i)=μ.moment (fun p => point p i) := by
  have hh := μ.step_moment features (probability β) (probability_unit β)
    (endpoint β) (finSumFinEquiv (Sum.inl i))
  simp only [features_single] at hh
  exact hh.trans (μ.moment_congr _ _ (fun a => endpoint_mean β _ i))

 theorem step_pair (β : Fin n → ℚ) 
    (μ : SparseIntegerLaw (Vector ℚ n)) (i j : Fin n) (hij : i ≠ j) :
    (step β μ).moment (fun p => point p i*point p j) ≤
      μ.moment (fun p => point p i*point p j) := by
  have hh := μ.step_moment features (probability β) (probability_unit β)
    (endpoint β) (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))
  simp only [features_pair] at hh
  exact hh.trans_le (μ.moment_mono _ _ (fun k => endpoint_pair β _ i j hij))

 theorem run_mean (β : Fin n → ℚ) 
    (p : Vector ℚ n) (t : ℕ) (i : Fin n) :
    (run β p t).moment (fun q => point q i)=point p i := by
  induction t with
  | zero => exact SparseIntegerLaw.dirac_moment _ _
  | succ t ih => rw [run,step_mean,ih]

 theorem run_pair (β : Fin n → ℚ) 
    (p : Vector ℚ n) (t : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (run β p t).moment (fun q => point q i*point q j) ≤ point p i*point p j := by
  induction t with
  | zero => exact (SparseIntegerLaw.dirac_moment _ _).le
  | succ t ih => exact (step_pair β _ i j hij).trans ih

end MetricKMedian.SparseSignedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedFixed
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedRounding
open Finset
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features)
variable {n : ℕ}

theorem positive (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (a : Fin (round u p hp).length) : 0 < (round u p hp).law.rational.weight a := by
  exact ((SparseSignedPartial.run u p n).bindIndexed (kernel u p hp)).compressAuto_positive features a

end MetricKMedian.SparseSignedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseWeightedRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedRounding
open Finset RationalWeightedStep SparseWeightedPartial
variable {n : ℕ}

theorem round_mean (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (i : Fin n) :
    (round β hβ p).moment (fun q => point q i)=point p i := by
  have hh := (run β hβ p n).step_moment features RationalLastFraction.probability
    RationalLastFraction.probability_unit RationalLastFraction.endpoint
    (finSumFinEquiv (Sum.inl i))
  simp only [features_single] at hh
  exact hh.trans (((run β hβ p n).moment_congr _ _
    (fun a => RationalLastFraction.endpoint_mean _ i)).trans (run_mean β hβ p n i))

end MetricKMedian.SparseWeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseTargetSubset
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseTargetSubset
open Finset RationalWeightedStep
variable {n : ℕ}

theorem positive (D : Finset (Fin n)) (q : ℚ) (a : Fin (law D q).length) :
    0 < (law D q).law.rational.weight a := by
  exact ((SparseWeightedPartial.run (fun _ => 1) (fun _ => by norm_num) (initial D q) n).branch
    RationalLastFraction.probability RationalLastFraction.probability_unit
    RationalLastFraction.endpoint).compressAuto_positive SparseWeightedPartial.features a

end MetricKMedian.SparseTargetSubset
end
end

end OAI
end


