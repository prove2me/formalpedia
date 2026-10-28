-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library26
-- name    : CH_ConstructibleGCH_Library26
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T08:50:11.165291+00:00
-- url     : https://prove2.me/theorems/3c9237a7-bf6b-4a90-8523-c634c33cdb98
-- title:
--   A fixed formula for uniform witness steps
-- statement:
--   A fixed first-order formula describes one uniform witness step for the particular textbook E/Df coding. This library supplies that formula and its constructor interfaces, allowing Replacement to collect the successive witness sets internally.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEUniformWitnessStep.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookDfFormulaExactLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEUniformWitnessStepFormula.lean#L1

import Definitions.Def_CH_ConstructibleAC_Library15
import Definitions.Def_CH_Constructible
import Mathlib.Data.List.Shortlex
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sigma.Lex
import Mathlib.Data.Sum.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.SetTheory.Cardinal.Basic

import Definitions.Def_CH_ConstructibleGCH_Library25
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookEUniformWitnessStep -/
section GCHSource_Work_CUGCH_TextbookEUniformWitnessStep
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# One simultaneous textbook E witness step

This file forms the actual internal request set

`(omega x (omega \ {0})) x { finite tuple graphs over seed }`

and applies Replacement to the total formula from
`TextbookEUniformWitnessFormula`.  Replacement produces both its genuine
range and its genuine Kuratowski function graph in `L`.  The resulting step
adjoins the range to the seed and simultaneously closes under every decoded
textbook E witness task.
-/

section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF
open ContinuumFormula

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## The internal request domain -/

/-- All task/prefix requests for one seed, represented by an actual set in L. -/
def textbookEUniformWitnessRequestDomain
    (seed : LCarrier.{u}) : LCarrier.{u} :=
  prodLCarrier textbookEWitnessTaskDomain
    (ContinuumFormula.internalFiniteTupleSpaces seed)

@[simp]
theorem textbookEUniformWitnessRequestDomain_val
    (seed : LCarrier.{u}) :
    (textbookEUniformWitnessRequestDomain seed).1 =
      ZFSet.prod textbookEWitnessTaskDomain.1
        (ContinuumFormula.internalFiniteTupleSpaces seed).1 :=
  rfl

@[simp]
theorem mem_textbookEUniformWitnessRequestDomain_iff
    (seed request : LCarrier.{u}) :
    request.1 ∈ (textbookEUniformWitnessRequestDomain seed).1 <->
      ∃ task prefixGraph : LCarrier.{u},
        task.1 ∈ textbookEWitnessTaskDomain.1 /\
        prefixGraph.1 ∈
          (ContinuumFormula.internalFiniteTupleSpaces seed).1 /\
        request.1 = ZFSet.pair task.1 prefixGraph.1 := by
  rw [textbookEUniformWitnessRequestDomain_val, ZFSet.mem_prod]
  constructor
  · rintro ⟨task, htask, prefixGraph, hprefixGraph, hrequest⟩
    let taskL : LCarrier.{u} :=
      ⟨task, mem_L_of_mem htask textbookEWitnessTaskDomain.2⟩
    let prefixGraphL : LCarrier.{u} :=
      ⟨prefixGraph,
        mem_L_of_mem hprefixGraph
          (ContinuumFormula.internalFiniteTupleSpaces seed).2⟩
    exact ⟨taskL, prefixGraphL, htask, hprefixGraph, hrequest⟩
  · rintro ⟨task, prefixGraph, htask, hprefixGraph, hrequest⟩
    exact ⟨task.1, htask, prefixGraph.1, hprefixGraph, hrequest⟩

/-- The canonical internal code of the task `(code, arity + 1)`. -/
def textbookEUniformTaskLCarrier (code arity : Nat) : LCarrier.{u} :=
  orderedPairLCarrier
    (TextbookNatFormula.textbookNatCodeLCarrier code)
    (TextbookNatFormula.textbookNatCodeLCarrier (arity + 1))

/-- The canonical request obtained by pairing a decoded task with a prefix. -/
def textbookEUniformRequestLCarrier
    (code arity : Nat) (prefixGraph : LCarrier.{u}) : LCarrier.{u} :=
  orderedPairLCarrier (textbookEUniformTaskLCarrier code arity) prefixGraph





/-! ## Functionality of the total formula -/

 theorem selected_property_of_formula
    {U seed prefixGraph y : LCarrier.{u}} {arity code : Nat}
    (hy :
      FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, canonicalWitnessOrder U,
          textbookEUniformRequestLCarrier code arity prefixGraph, y]) :
    y.1 ∈
        (textbookEWitnessCandidates U
          (textbookEZFLCarrier U (arity + 1) code)
          prefixGraph
          (TextbookNatFormula.textbookNatCodeLCarrier arity)).1 /\
      ∀ z : LCarrier.{u},
        z.1 ∈
          (textbookEWitnessCandidates U
            (textbookEZFLCarrier U (arity + 1) code)
            prefixGraph
            (TextbookNatFormula.textbookNatCodeLCarrier arity)).1 ->
          ¬ GraphRel (canonicalWitnessOrder U) z y := by
  have hdecoded :=
    (satisfies_textbookEUniformSelectedFormula_decoded_iff
      U seed (canonicalWitnessOrder U) prefixGraph y arity code).mp hy
  constructor
  · apply (mem_textbookEWitnessCandidates_iff
      U (textbookEZFLCarrier U (arity + 1) code)
      prefixGraph
      (TextbookNatFormula.textbookNatCodeLCarrier arity) y).mpr
    exact ⟨hdecoded.2.1, hdecoded.2.2.1⟩
  · intro z hz
    have hzData := (mem_textbookEWitnessCandidates_iff
      U (textbookEZFLCarrier U (arity + 1) code)
      prefixGraph
      (TextbookNatFormula.textbookNatCodeLCarrier arity) z).mp hz
    exact hdecoded.2.2.2 z hzData.1 hzData.2

theorem textbookEUniformSelected_unique_decoded
    (U seed prefixGraph y y' : LCarrier.{u}) (arity code : Nat)
    (hy :
      FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, canonicalWitnessOrder U,
          textbookEUniformRequestLCarrier code arity prefixGraph, y])
    (hy' :
      FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, canonicalWitnessOrder U,
          textbookEUniformRequestLCarrier code arity prefixGraph, y']) :
    y' = y := by
  have hyProperty := selected_property_of_formula hy
  have hy'Property := selected_property_of_formula hy'
  rcases existsUnique_textbookEWitnessMinimum
      U (textbookEZFLCarrier U (arity + 1) code)
      prefixGraph
      (TextbookNatFormula.textbookNatCodeLCarrier arity)
      ⟨y, hyProperty.1⟩ with
    ⟨minimum, hminimum, hunique⟩
  have hyEq : y = minimum := hunique y hyProperty
  have hy'Eq : y' = minimum := hunique y' hy'Property
  exact hy'Eq.trans hyEq.symm

 theorem uniform_total_assignment
    (U seed request output : LCarrier.{u}) :
    snoc (snoc ![U, seed, canonicalWitnessOrder U] request) output =
      ![U, seed, canonicalWitnessOrder U, request, output] := by
  funext i
  fin_cases i <;> rfl

/--
The total formula has exactly one output on every member of the internal
request domain.  The proof decodes the task only in the correctness
argument; the object-language operation itself remains the fixed formula.
-/
theorem textbookEUniformTotalFormula_existsUnique
    (seed U request : LCarrier.{u})
    (hrequest :
      request.1 ∈ (textbookEUniformWitnessRequestDomain seed).1) :
    ExistsUnique fun output : LCarrier.{u} =>
      FOFormula.Satisfies LMem textbookEUniformTotalFormula
        ![U, seed, canonicalWitnessOrder U, request, output] := by
  rcases (mem_textbookEUniformWitnessRequestDomain_iff seed request).mp
      hrequest with
    ⟨task, prefixGraph, htask, _hprefixAny, hrequestRaw⟩
  rcases (mem_textbookEWitnessTaskDomain_iff task.1).mp htask with
    ⟨code, arity, htaskRaw⟩
  have hrequestEq :
      request =
        textbookEUniformRequestLCarrier code arity prefixGraph := by
    apply Subtype.ext
    change request.1 =
      ZFSet.pair
        (ZFSet.pair (natCode code) (natCode (arity + 1)))
        prefixGraph.1
    rw [hrequestRaw, htaskRaw]
  subst request
  by_cases hselected : ∃ y : LCarrier.{u},
      FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, canonicalWitnessOrder U,
          textbookEUniformRequestLCarrier code arity prefixGraph, y]
  · rcases hselected with ⟨y, hy⟩
    refine ⟨y,
      (satisfies_textbookEUniformTotalFormula
        U seed (canonicalWitnessOrder U)
        (textbookEUniformRequestLCarrier code arity prefixGraph) y).mpr
          (Or.inl hy), ?_⟩
    intro other hother
    rcases (satisfies_textbookEUniformTotalFormula
      U seed (canonicalWitnessOrder U)
      (textbookEUniformRequestLCarrier code arity prefixGraph) other).mp
        hother with
      hotherSelected | ⟨_hotherEmpty, hnone⟩
    · exact textbookEUniformSelected_unique_decoded
        U seed prefixGraph y other arity code hy hotherSelected
    · exact (hnone ⟨y, hy⟩).elim
  · refine ⟨emptyLCarrier,
      (satisfies_textbookEUniformTotalFormula
        U seed (canonicalWitnessOrder U)
        (textbookEUniformRequestLCarrier code arity prefixGraph)
        emptyLCarrier).mpr
          (Or.inr ⟨rfl, hselected⟩), ?_⟩
    intro other hother
    rcases (satisfies_textbookEUniformTotalFormula
      U seed (canonicalWitnessOrder U)
      (textbookEUniformRequestLCarrier code arity prefixGraph) other).mp
        hother with
      hotherSelected | ⟨hotherEmpty, _hnone⟩
    · exact (hselected ⟨other, hotherSelected⟩).elim
    · exact hotherEmpty

/-! ## Replacement range and graph -/

/-- The actual range and function graph produced by uniform Replacement. -/
structure TextbookEUniformWitnessReplacementData
    (seed U : LCarrier.{u}) where
  graph : LCarrier.{u}
  range : LCarrier.{u}
  isFunctionGraph :
    IsFunctionGraph LMem graph
      (textbookEUniformWitnessRequestDomain seed) range
  mem_range_iff : ∀ output : LCarrier.{u},
    output.1 ∈ range.1 <->
      ∃ request : LCarrier.{u},
        request.1 ∈ (textbookEUniformWitnessRequestDomain seed).1 /\
        FOFormula.Satisfies LMem textbookEUniformTotalFormula
          ![U, seed, canonicalWitnessOrder U, request, output]
  graphValue_iff : ∀ request output : LCarrier.{u},
    GraphValue LMem graph request output <->
      request.1 ∈ (textbookEUniformWitnessRequestDomain seed).1 /\
      FOFormula.Satisfies LMem textbookEUniformTotalFormula
        ![U, seed, canonicalWitnessOrder U, request, output]
  rangeCovered : ∀ output : LCarrier.{u}, output.1 ∈ range.1 ->
    ∃ request : LCarrier.{u},
      request.1 ∈ (textbookEUniformWitnessRequestDomain seed).1 /\
      GraphValue LMem graph request output

/--
Replacement constructs a genuine internal range and a genuine internal
Kuratowski graph for the total request operation.
-/
theorem exists_textbookEUniformWitnessReplacementData
    (seed U : LCarrier.{u}) :
    Nonempty (TextbookEUniformWitnessReplacementData seed U) := by
  let params : Tuple LCarrier.{u} 3 :=
    ![U, seed, canonicalWitnessOrder U]
  let domain := textbookEUniformWitnessRequestDomain seed
  have hfun : ∀ request : LCarrier.{u}, request.1 ∈ domain.1 ->
      ExistsUnique fun output : LCarrier.{u} =>
        FOFormula.Satisfies LMem textbookEUniformTotalFormula
          (snoc (snoc params request) output) := by
    intro request hrequest
    simpa only [params, uniform_total_assignment] using
      textbookEUniformTotalFormula_existsUnique seed U request hrequest
  rcases exists_replacementLCarrier
      textbookEUniformTotalFormula params domain hfun with
    ⟨range, hrange⟩
  rcases exists_replacementFunctionGraphLCarrier
      textbookEUniformTotalFormula params domain hfun with
    ⟨graph, hgraph⟩
  have hvalue : ∀ request output : LCarrier.{u},
      GraphValue LMem graph request output <->
        request.1 ∈ domain.1 /\
        FOFormula.Satisfies LMem textbookEUniformTotalFormula
          ![U, seed, canonicalWitnessOrder U, request, output] := by
    intro request output
    constructor
    · rintro ⟨pair, hpairGraph, hpairIs⟩
      rcases (hgraph pair.1).mp hpairGraph with
        ⟨request', hrequest', output', houtput', hpairEq⟩
      have hpairCoordinates :=
        ZFSet.pair_inj.mp
          (hpairEq.symm.trans
            ((isKuratowskiPairOf_lCarrier_iff
              pair request output).mp hpairIs))
      have hrequestEq : request' = request :=
        Subtype.ext hpairCoordinates.1
      have houtputEq : output' = output :=
        Subtype.ext hpairCoordinates.2
      subst request'
      subst output'
      simpa only [params, uniform_total_assignment] using
        And.intro hrequest' houtput'
    · rintro ⟨hrequest, houtput⟩
      let pair := orderedPairLCarrier request output
      refine ⟨pair, ?_, ?_⟩
      · apply (hgraph pair.1).mpr
        refine ⟨request, hrequest, output, ?_, rfl⟩
        simpa only [params, uniform_total_assignment] using houtput
      · exact (isKuratowskiPairOf_lCarrier_iff
          pair request output).mpr rfl
  have hbetween : IsGraphBetween LMem graph domain range := by
    intro pair hpairGraph
    rcases (hgraph pair.1).mp hpairGraph with
      ⟨request, hrequest, output, houtput, hpairEq⟩
    have houtputRange : output.1 ∈ range.1 := by
      apply (hrange output).mpr
      exact ⟨request, hrequest, houtput⟩
    exact ⟨request, hrequest, output, houtputRange,
      (isKuratowskiPairOf_lCarrier_iff
        pair request output).mpr hpairEq⟩
  have htotal : ∀ request : LCarrier.{u}, request.1 ∈ domain.1 ->
      HasUniqueImage LMem graph request range := by
    intro request hrequest
    rcases hfun request hrequest with
      ⟨output, houtput, houtputUnique⟩
    have houtputRange : output.1 ∈ range.1 := by
      apply (hrange output).mpr
      exact ⟨request, hrequest, houtput⟩
    refine ⟨output, houtputRange,
      (hvalue request output).mpr
        ⟨hrequest, by
          simpa only [params, uniform_total_assignment] using houtput⟩,
      ?_⟩
    intro other _hotherRange hotherValue
    apply houtputUnique other
    have hother := (hvalue request other).mp hotherValue |>.2
    simpa only [params, uniform_total_assignment] using hother
  have hmemRange : ∀ output : LCarrier.{u}, output.1 ∈ range.1 <->
      ∃ request : LCarrier.{u}, request.1 ∈ domain.1 /\
        FOFormula.Satisfies LMem textbookEUniformTotalFormula
          ![U, seed, canonicalWitnessOrder U, request, output] := by
    intro output
    rw [hrange]
    simp only [params, uniform_total_assignment]
  refine ⟨{
    graph := graph
    range := range
    isFunctionGraph := ⟨hbetween, htotal⟩
    mem_range_iff := ?_
    graphValue_iff := ?_
    rangeCovered := ?_
  }⟩
  · exact hmemRange
  · intro request output
    simpa only [domain] using hvalue request output
  · intro output houtput
    rcases (hmemRange output).mp houtput with
      ⟨request, hrequest, hformula⟩
    refine ⟨request, hrequest, ?_⟩
    apply (hvalue request output).mpr
    exact ⟨hrequest, hformula⟩

/-- A canonical package of the Replacement witnesses. -/
noncomputable def textbookEUniformWitnessReplacementData
    (seed U : LCarrier.{u}) :
    TextbookEUniformWitnessReplacementData seed U :=
  Classical.choice (exists_textbookEUniformWitnessReplacementData seed U)

/-- Retain the seed and adjoin the whole uniform Replacement range. -/
def textbookEUniformWitnessStep
    (seed U : LCarrier.{u}) : LCarrier.{u} :=
  unionLCarrier seed
    (textbookEUniformWitnessReplacementData seed U).range





/-! ## Simultaneous witness closure -/

/--
One-step witness closure has separate parameter and output sets.  This is
the exact induction invariant used before taking the union of the omega
iteration.
-/
def ClosesUnderTextbookEWitnessAtFrom
    (parameters outputs : Set ZFSet.{u}) (U : ZFSet.{u})
    (arity code : Nat) : Prop :=
  ∀ (params : Tuple (ZFCarrier U) arity),
    (∀ i, (params i).1 ∈ parameters) ->
    (∃ x : ZFCarrier U,
      textbookTupleGraph (snoc params x) ∈
        textbookEZF U (natCode (arity + 1)) (natCode code)) ->
    ∃ x : ZFCarrier U,
      x.1 ∈ outputs /\
      textbookTupleGraph (snoc params x) ∈
        textbookEZF U (natCode (arity + 1)) (natCode code)







end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TextbookEUniformWitnessStep


/- Source module: Solutions.Work_CUGCH_TextbookDfFormulaExactLCarrier -/
section GCHSource_Work_CUGCH_TextbookDfFormulaExactLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Exact semantics of the textbook Df formula over L

The exact internal semantics of the textbook enumeration `E` is used with
Replacement over the genuine internal omega.  This first proves that every
fixed-arity set `textbookDfZF a n` belongs to `L`, and then identifies the
public first-order graph for `Df` with that set over `LCarrier`.
-/

section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

namespace Model

local notation "LMem" => lCarrierMem

/-! ## Replacement-range semantics over LCarrier -/

@[simp]
theorem satisfies_replacementRangeFormula_lCarrier
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (a y : LCarrier.{u}) :
    FOFormula.Satisfies LMem (replacementRangeFormula phi)
        (snoc (snoc params a) y) <->
      exists x : LCarrier.{u}, x.1 ∈ a.1 /\
        FOFormula.Satisfies LMem phi (snoc (snoc params x) y) := by
  simp only [replacementRangeFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  apply exists_congr
  intro x
  change
    (LMem (snoc (snoc (snoc params a) y) x (Fin.last (n + 2)))
          (snoc (snoc (snoc params a) y) x
            (Fin.last n).castSucc.castSucc) /\
        FOFormula.Satisfies LMem phi
          (fun i => snoc (snoc (snoc params a) y) x
            (replacementRangeRename i))) <-> _
  simp only [snoc_last, snoc_castSucc, comp_replacementRangeRename]

/-! ## The fixed-arity Df set is constructible -/

 theorem textbookEFormula_assignment
    (a n code output : LCarrier.{u}) :
    snoc (snoc ![a, n] code) output = ![a, n, code, output] := by
  funext i
  fin_cases i <;> rfl

/-- Every fixed-arity textbook definability set is an actual member of `L`.
The witness is the Replacement range of the exact `E` formula on omega. -/
theorem textbookDfZF_mem_L (a : LCarrier.{u}) (n : Nat) :
    textbookDfZF a.1 n ∈ L := by
  let nL : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier n
  let params : Tuple LCarrier.{u} 2 := ![a, nL]
  have hfun : forall code : LCarrier.{u},
      code.1 ∈ (omegaLCarrier : LCarrier.{u}).1 ->
        ExistsUnique fun output : LCarrier.{u} =>
          FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
            (snoc (snoc params code) output) := by
    intro code hcode
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode code.1).mp
        hcode with ⟨m, hcodeValue⟩
    have hcodeEq :
        code = TextbookNatFormula.textbookNatCodeLCarrier m := by
      apply Subtype.ext
      exact hcodeValue
    subst code
    let output : LCarrier.{u} := textbookEZFLCarrier a n m
    refine ⟨output, ?_, ?_⟩
    · change FOFormula.Satisfies LMem
        TextbookEFormula.textbookEZFFormula
          (snoc (snoc params
            (TextbookNatFormula.textbookNatCodeLCarrier m)) output)
      rw [show snoc (snoc params
          (TextbookNatFormula.textbookNatCodeLCarrier m)) output =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier m, output] by
        simpa only [params, nL] using textbookEFormula_assignment
          a (TextbookNatFormula.textbookNatCodeLCarrier n)
            (TextbookNatFormula.textbookNatCodeLCarrier m) output]
      exact (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a output n m).mpr rfl
    · intro other hother
      apply Subtype.ext
      have hformula :
          FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier m, other] := by
        rw [← textbookEFormula_assignment a
          (TextbookNatFormula.textbookNatCodeLCarrier n)
          (TextbookNatFormula.textbookNatCodeLCarrier m) other]
        simpa only [params, nL] using hother
      exact (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a other n m).mp hformula
  rcases exists_replacementLCarrier
      TextbookEFormula.textbookEZFFormula params omegaLCarrier hfun with
    ⟨range, hrange⟩
  have hrangeEq : range.1 = textbookDfZF a.1 n := by
    apply ZFSet.ext
    intro relation
    constructor
    · intro hrelationRange
      let relationL : LCarrier.{u} :=
        ⟨relation, mem_L_of_mem hrelationRange range.2⟩
      rcases (hrange relationL).mp hrelationRange with
        ⟨code, hcode, hformula⟩
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode code.1).mp
          hcode with ⟨m, hcodeValue⟩
      have hcodeEq :
          code = TextbookNatFormula.textbookNatCodeLCarrier m := by
        apply Subtype.ext
        exact hcodeValue
      subst code
      apply mem_textbookDfZF_iff_exists_textbookEZF.mpr
      refine ⟨m, ?_⟩
      have hformula' :
          FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier m, relationL] := by
        rw [← textbookEFormula_assignment a
          (TextbookNatFormula.textbookNatCodeLCarrier n)
          (TextbookNatFormula.textbookNatCodeLCarrier m) relationL]
        simpa only [params, nL] using hformula
      exact (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a relationL n m).mp hformula' |>.symm
    · intro hrelationDf
      rcases mem_textbookDfZF_iff_exists_textbookEZF.mp hrelationDf with
        ⟨m, hrelationValue⟩
      have hrelationL : relation ∈ L := by
        rw [← hrelationValue]
        exact textbookEZF_natCode_mem_L a.2 n m
      let relationCarrier : LCarrier.{u} := ⟨relation, hrelationL⟩
      apply (hrange relationCarrier).mpr
      let code : LCarrier.{u} :=
        TextbookNatFormula.textbookNatCodeLCarrier m
      refine ⟨code, ?_, ?_⟩
      · change (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF
        exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode m)).mpr ⟨m, rfl⟩
      · rw [show snoc (snoc params code) relationCarrier =
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier m,
              relationCarrier] by
          simpa only [params, nL, code] using textbookEFormula_assignment
            a (TextbookNatFormula.textbookNatCodeLCarrier n)
              (TextbookNatFormula.textbookNatCodeLCarrier m)
              relationCarrier]
        apply (satisfies_textbookEZFFormula_lCarrier_natCode_iff
          a relationCarrier n m).mpr
        exact hrelationValue.symm
  rw [← hrangeEq]
  exact range.2

/-- The fixed-arity Df set packaged as an `LCarrier`. -/
def textbookDfZFLCarrier (a : LCarrier.{u}) (n : Nat) : LCarrier.{u} :=
  ⟨textbookDfZF a.1 n, textbookDfZF_mem_L a n⟩

@[simp]
theorem textbookDfZFLCarrier_val (a : LCarrier.{u}) (n : Nat) :
    (textbookDfZFLCarrier a n).1 = textbookDfZF a.1 n :=
  rfl

/-! ## Exact semantics of the public Df formula -/

 theorem textbookDfRange_assignment
    (a n output omega relation : LCarrier.{u}) :
    (fun i => ![a, n, output, omega, relation]
      (TextbookDfFormula.textbookDfRangeParameters i)) =
      ![a, n, omega, relation] := by
  funext i
  fin_cases i <;> rfl

 theorem textbookDfRange_snoc_assignment
    (a n omega relation : LCarrier.{u}) :
    ![a, n, omega, relation] =
      snoc (snoc ![a, n] omega) relation := by
  funext i
  fin_cases i <;> rfl

 theorem satisfies_textbookDfRangeFormula_lCarrier_natCode_iff
    (a output relation : LCarrier.{u}) (n : Nat) :
    FOFormula.Satisfies LMem
        (FOFormula.rename TextbookDfFormula.textbookDfRangeParameters
          (replacementRangeFormula TextbookEFormula.textbookEZFFormula))
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n, output,
          omegaLCarrier, relation] <->
      exists m : Nat,
        textbookEZF a.1 (natCode n) (natCode m) = relation.1 := by
  rw [FOFormula.satisfies_rename,
    textbookDfRange_assignment,
    textbookDfRange_snoc_assignment,
    satisfies_replacementRangeFormula_lCarrier]
  constructor
  · rintro ⟨code, hcode, hformula⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode code.1).mp
        hcode with ⟨m, hcodeValue⟩
    have hcodeEq :
        code = TextbookNatFormula.textbookNatCodeLCarrier m := by
      apply Subtype.ext
      exact hcodeValue
    subst code
    refine ⟨m, ?_⟩
    have hformula' :
        FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier m, relation] := by
      rw [← textbookEFormula_assignment a
        (TextbookNatFormula.textbookNatCodeLCarrier n)
        (TextbookNatFormula.textbookNatCodeLCarrier m) relation]
      exact hformula
    exact (satisfies_textbookEZFFormula_lCarrier_natCode_iff
      a relation n m).mp hformula' |>.symm
  · rintro ⟨m, hm⟩
    let code : LCarrier.{u} :=
      TextbookNatFormula.textbookNatCodeLCarrier m
    refine ⟨code, ?_, ?_⟩
    · change (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode m)).mpr ⟨m, rfl⟩
    · rw [show snoc
          (snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n] code)
          relation =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier m, relation] by
        simpa only [code] using textbookEFormula_assignment a
          (TextbookNatFormula.textbookNatCodeLCarrier n)
            (TextbookNatFormula.textbookNatCodeLCarrier m) relation]
      apply (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a relation n m).mpr
      exact hm.symm

 theorem satisfies_textbookDfMembersFormula_lCarrier_natCode_iff
    (a output : LCarrier.{u}) (n : Nat) :
    FOFormula.Satisfies LMem
        TextbookDfFormula.textbookDfMembersFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output, omegaLCarrier] <->
      output.1 = textbookDfZF a.1 n := by
  rw [TextbookDfFormula.textbookDfMembersFormula,
    FOFormula.satisfies_all]
  constructor
  · intro hall
    apply ZFSet.ext
    intro relation
    constructor
    · intro hrelationOutput
      let relationL : LCarrier.{u} :=
        ⟨relation, mem_L_of_mem hrelationOutput output.2⟩
      have hbody := hall relationL
      have hassignment :
          snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier] relationL =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier, relationL] := by
        funext i
        fin_cases i <;> rfl
      rw [hassignment, FOFormula.satisfies_biimp] at hbody
      change (relationL.1 ∈ output.1 <->
        FOFormula.Satisfies LMem
          (FOFormula.rename
            TextbookDfFormula.textbookDfRangeParameters
            (replacementRangeFormula
              TextbookEFormula.textbookEZFFormula))
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier, relationL]) at hbody
      have hiff : relationL.1 ∈ output.1 <->
          exists m : Nat,
            textbookEZF a.1 (natCode n) (natCode m) = relationL.1 :=
        hbody.trans
          (satisfies_textbookDfRangeFormula_lCarrier_natCode_iff
            a output relationL n)
      exact mem_textbookDfZF_iff_exists_textbookEZF.mpr
        (hiff.mp hrelationOutput)
    · intro hrelationDf
      have hrelationL : relation ∈ L :=
        mem_L_of_mem hrelationDf (textbookDfZF_mem_L a n)
      let relationCarrier : LCarrier.{u} := ⟨relation, hrelationL⟩
      have hbody := hall relationCarrier
      have hassignment :
          snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier] relationCarrier =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier, relationCarrier] := by
        funext i
        fin_cases i <;> rfl
      rw [hassignment, FOFormula.satisfies_biimp] at hbody
      change (relationCarrier.1 ∈ output.1 <->
        FOFormula.Satisfies LMem
          (FOFormula.rename
            TextbookDfFormula.textbookDfRangeParameters
            (replacementRangeFormula
              TextbookEFormula.textbookEZFFormula))
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier, relationCarrier]) at hbody
      have hiff : relationCarrier.1 ∈ output.1 <->
          exists m : Nat,
            textbookEZF a.1 (natCode n) (natCode m) = relationCarrier.1 :=
        hbody.trans
          (satisfies_textbookDfRangeFormula_lCarrier_natCode_iff
            a output relationCarrier n)
      exact hiff.mpr
        (mem_textbookDfZF_iff_exists_textbookEZF.mp hrelationDf)
  · intro houtput relation
    have hassignment :
        snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output, omegaLCarrier] relation =
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output, omegaLCarrier, relation] := by
      funext i
      fin_cases i <;> rfl
    rw [hassignment, FOFormula.satisfies_biimp]
    change (relation.1 ∈ output.1 <-> _)
    rw [satisfies_textbookDfRangeFormula_lCarrier_natCode_iff]
    rw [houtput, mem_textbookDfZF_iff_exists_textbookEZF]

/-- Exact `LCarrier` semantics of the public Df graph at standard codes. -/
@[simp]
theorem satisfies_textbookDfZFFormula_lCarrier_natCode_iff
    (a output : LCarrier.{u}) (n : Nat) :
    FOFormula.Satisfies LMem TextbookDfFormula.textbookDfZFFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n, output] <->
      output.1 = textbookDfZF a.1 n := by
  rw [TextbookDfFormula.textbookDfZFFormula]
  simp only [FOFormula.Satisfies]
  constructor
  · rintro ⟨omega, homega, _hnOmega, hmembers⟩
    have homegaEq : omega = omegaLCarrier :=
      (satisfies_standardOmegaAt_lCarrier (Fin.last 3)
        (snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output] omega)).mp homega
    subst omega
    have hassignment :
        snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output] omegaLCarrier =
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output, omegaLCarrier] := by
      funext i
      fin_cases i <;> rfl
    rw [hassignment] at hmembers
    exact (satisfies_textbookDfMembersFormula_lCarrier_natCode_iff
      a output n).mp hmembers
  · intro houtput
    refine ⟨omegaLCarrier, ?_, ?_, ?_⟩
    · exact (satisfies_standardOmegaAt_lCarrier (Fin.last 3)
        (snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output] omegaLCarrier)).mpr rfl
    · change (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode n)).mpr ⟨n, rfl⟩
    · have hassignment :
          snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output] omegaLCarrier =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier] := by
        funext i
        fin_cases i <;> rfl
      rw [hassignment]
      exact (satisfies_textbookDfMembersFormula_lCarrier_natCode_iff
        a output n).mpr houtput

/-- Exact semantics on arbitrary set-coded indices. -/
@[simp]
theorem satisfies_textbookDfZFFormula_lCarrier_iff
    (a index output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookDfFormula.textbookDfZFFormula
        ![a, index, output] <->
      index.1 ∈ textbookEOmegaZF /\
        output.1 = textbookDfCodeZF a.1 index.1 := by
  constructor
  · intro hformula
    have hraw := hformula
    rw [TextbookDfFormula.textbookDfZFFormula] at hraw
    simp only [FOFormula.Satisfies] at hraw
    rcases hraw with ⟨omega, homega, hindexOmega, _hmembers⟩
    have homegaEq : omega = omegaLCarrier :=
      (satisfies_standardOmegaAt_lCarrier (Fin.last 3)
        (snoc ![a, index, output] omega)).mp homega
    subst omega
    change index.1 ∈ textbookEOmegaZF at hindexOmega
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindexOmega with ⟨n, hindexValue⟩
    have hindexEq :
        index = TextbookNatFormula.textbookNatCodeLCarrier n := by
      apply Subtype.ext
      exact hindexValue
    subst index
    refine ⟨hindexOmega, ?_⟩
    simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val,
      textbookDfCodeZF_natCode] using
        (satisfies_textbookDfZFFormula_lCarrier_natCode_iff
          a output n).mp hformula
  · rintro ⟨hindexOmega, houtput⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindexOmega with ⟨n, hindexValue⟩
    have hindexEq :
        index = TextbookNatFormula.textbookNatCodeLCarrier n := by
      apply Subtype.ext
      exact hindexValue
    subst index
    apply (satisfies_textbookDfZFFormula_lCarrier_natCode_iff
      a output n).mpr
    simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val,
      textbookDfCodeZF_natCode] using houtput

end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookDfFormulaExactLCarrier


/- Source module: Solutions.Work_CUGCH_TextbookEUniformWitnessStepFormula -/
section GCHSource_Work_CUGCH_TextbookEUniformWitnessStepFormula
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# A fixed first-order graph for the simultaneous textbook E witness step

The formula in this file does not mention the externally chosen value of
`textbookEUniformWitnessStep`.  Internally it:

1. forms the Replacement range `{current^n | n in omega}`;
2. takes its union to obtain all finite tuple graphs over `current`;
3. forms the product of the fixed task domain with that tuple set;
4. forms the Replacement range of the uniform total witness formula; and
5. takes the binary union of `current` with that range.

The exact semantics theorem identifies the unique output with the previously
constructed internal step.
-/

section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF
open ContinuumFormula

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Extensional range, union, and product formulas -/

/-- Insert the bound range member into the layout `(params,domain,range)`. -/
def replacementRangeEqRename {n : Nat} :
    Fin (n + 2) -> Fin (n + 3) :=
  Fin.lastCases (Fin.last (n + 2))
    (fun i => i.castSucc.castSucc)

 theorem comp_replacementRangeEqRename
    {A : Type u} {n : Nat}
    (params : Tuple A n) (domain range output : A) :
    (fun i =>
      snoc (snoc (snoc params domain) range) output
        (replacementRangeEqRename i)) =
      snoc (snoc params domain) output := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [replacementRangeEqRename]
  · simp [replacementRangeEqRename]

/--
Layout `(params,domain,range)`: `range` consists exactly of the outputs of
`phi` on members of `domain`.
-/
def replacementRangeEqFormula {n : Nat}
    (phi : FOFormula (n + 2)) : FOFormula (n + 2) :=
  .all
    (FOFormula.biimp
      (.mem (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc)
      (FOFormula.rename replacementRangeEqRename
        (replacementRangeFormula phi)))

@[simp]
theorem satisfies_replacementRangeEqFormula_lCarrier
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (domain range : LCarrier.{u}) :
    FOFormula.Satisfies LMem (replacementRangeEqFormula phi)
        (snoc (snoc params domain) range) <->
      ∀ output : LCarrier.{u},
        output.1 ∈ range.1 <->
          ∃ input : LCarrier.{u}, input.1 ∈ domain.1 /\
            FOFormula.Satisfies LMem phi
              (snoc (snoc params input) output) := by
  simp only [replacementRangeEqFormula, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.satisfies_rename,
    FOFormula.Satisfies, snoc_last, snoc_castSucc,
    comp_replacementRangeEqRename,
    satisfies_replacementRangeFormula_lCarrier]

/-- Layout with arbitrary coordinates: `output` is `sUnion family`. -/
def sUnionEqAt {n : Nat} (output family : Fin n) : FOFormula n :=
  .all
    (FOFormula.biimp
      (.mem (Fin.last n) output.castSucc)
      (.ex
        (.conj
          (.mem (Fin.last (n + 1)) family.castSucc.castSucc)
          (.mem (Fin.last n).castSucc (Fin.last (n + 1))))))

@[simp]
theorem satisfies_sUnionEqAt_lCarrier {n : Nat}
    (output family : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (sUnionEqAt output family) s <->
      s output = sUnionLCarrier (s family) := by
  simp only [sUnionEqAt, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.Satisfies,
    snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply Subtype.ext
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      let zL : LCarrier.{u} :=
        ⟨z, mem_L_of_mem hz (s output).2⟩
      rcases (h zL).mp hz with
        ⟨member, hmember, hzMember⟩
      exact ZFSet.mem_sUnion.mpr
        ⟨member.1, hmember, hzMember⟩
    · intro hz
      rcases ZFSet.mem_sUnion.mp hz with
        ⟨member, hmember, hzMember⟩
      let memberL : LCarrier.{u} :=
        ⟨member, mem_L_of_mem hmember (s family).2⟩
      let zL : LCarrier.{u} :=
        ⟨z, mem_L_of_mem hzMember memberL.2⟩
      exact (h zL).mpr ⟨memberL, hmember, hzMember⟩
  · intro h z
    rw [h]
    change z.1 ∈ (sUnionLCarrier (s family)).1 <->
      ∃ member : LCarrier.{u},
        member.1 ∈ (s family).1 /\ z.1 ∈ member.1
    exact mem_sUnionLCarrier_iff (s family) z

/-- Layout with arbitrary coordinates: `output = left x right`. -/
def productEqAt {n : Nat}
    (output left right : Fin n) : FOFormula n :=
  FOFormula.rename ![output, left, right]
    Godel.graphF2Formula.toFO

@[simp]
theorem satisfies_productEqAt_lCarrier {n : Nat}
    (output left right : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (productEqAt output left right) s <->
      s output = prodLCarrier (s left) (s right) := by
  rw [productEqAt, FOFormula.satisfies_rename]
  have hassign :
      (fun i => s (![output, left, right] i)) =
        ![s output, s left, s right] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign, Delta0Formula.satisfies_toFO_lCarrier_absolute]
  have hrawAssign :
      (fun i => (![s output, s left, s right] i).1) =
        ![(s output).1, (s left).1, (s right).1] := by
    funext i
    fin_cases i <;> rfl
  rw [hrawAssign, Delta0Formula.satisfies_toFO,
    Godel.satisfies_graphF2Formula]
  constructor
  · intro h
    apply Subtype.ext
    simpa only [Godel.F2, prodLCarrier_val] using h
  · intro h
    have hraw := congrArg Subtype.val h
    simpa only [Godel.F2, prodLCarrier_val] using hraw

/-- Layout with arbitrary coordinates: `output = left union right`. -/
def binaryUnionEqAt {n : Nat}
    (output left right : Fin n) : FOFormula n :=
  .all
    (FOFormula.biimp
      (.mem (Fin.last n) output.castSucc)
      (FOFormula.disj
        (.mem (Fin.last n) left.castSucc)
        (.mem (Fin.last n) right.castSucc)))

@[simp]
theorem satisfies_binaryUnionEqAt_lCarrier {n : Nat}
    (output left right : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (binaryUnionEqAt output left right) s <->
      s output = unionLCarrier (s left) (s right) := by
  simp only [binaryUnionEqAt, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.satisfies_disj,
    FOFormula.Satisfies, snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply Subtype.ext
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      let zL : LCarrier.{u} :=
        ⟨z, mem_L_of_mem hz (s output).2⟩
      exact (mem_unionLCarrier_iff (s left) (s right) zL).mpr
        ((h zL).mp hz)
    · intro hz
      let zL : LCarrier.{u} :=
        ⟨z, mem_L_of_mem hz (unionLCarrier (s left) (s right)).2⟩
      rcases (mem_unionLCarrier_iff
          (s left) (s right) zL).mp hz with
        hzLeft | hzRight
      · let zL : LCarrier.{u} :=
          ⟨z, mem_L_of_mem hzLeft (s left).2⟩
        exact (h zL).mpr (Or.inl hzLeft)
      · let zL : LCarrier.{u} :=
          ⟨z, mem_L_of_mem hzRight (s right).2⟩
        exact (h zL).mpr (Or.inr hzRight)
  · intro h z
    rw [h]
    exact mem_unionLCarrier_iff (s left) (s right) z

/-! ## The fixed step graph -/

/--
The body layout is

`[U,order,tasks,omega,current,next,tupleFamily,prefixSpaces,
  requestDomain,selectedRange]`.
-/
def textbookEUniformWitnessStepBody : FOFormula 10 :=
  .conj
    (FOFormula.rename ![(4 : Fin 10), (3 : Fin 10), (6 : Fin 10)]
      (replacementRangeEqFormula
        ContinuumFormula.finiteTupleSpaceFormula))
  <| .conj
    (sUnionEqAt (7 : Fin 10) (6 : Fin 10))
  <| .conj
    (productEqAt (8 : Fin 10) (2 : Fin 10) (7 : Fin 10))
  <| .conj
    (FOFormula.rename
      ![(0 : Fin 10), (4 : Fin 10), (1 : Fin 10),
        (8 : Fin 10), (9 : Fin 10)]
      (replacementRangeEqFormula textbookEUniformTotalFormula))
    (binaryUnionEqAt
      (5 : Fin 10) (4 : Fin 10) (9 : Fin 10))

/--
Layout `[U,order,tasks,omega,current,next]`.  The remaining four coordinates
are internally quantified intermediate sets.
-/
def textbookEUniformWitnessStepFormula : FOFormula 6 :=
  .ex <| .ex <| .ex <| .ex
    textbookEUniformWitnessStepBody

set_option maxHeartbeats 1000000 in
@[simp]
theorem satisfies_textbookEUniformWitnessStepFormula
    (U order tasks omega current next : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookEUniformWitnessStepFormula
        ![U, order, tasks, omega, current, next] <->
      ∃ tupleFamily prefixSpaces requestDomain selectedRange : LCarrier.{u},
        (∀ space : LCarrier.{u}, space.1 ∈ tupleFamily.1 <->
          ∃ index : LCarrier.{u}, index.1 ∈ omega.1 /\
            FOFormula.Satisfies LMem
              ContinuumFormula.finiteTupleSpaceFormula
              ![current, index, space]) /\
        prefixSpaces = sUnionLCarrier tupleFamily /\
        requestDomain = prodLCarrier tasks prefixSpaces /\
        (∀ output : LCarrier.{u}, output.1 ∈ selectedRange.1 <->
          ∃ request : LCarrier.{u}, request.1 ∈ requestDomain.1 /\
            FOFormula.Satisfies LMem textbookEUniformTotalFormula
              ![U, current, order, request, output]) /\
        next = unionLCarrier current selectedRange := by
  simp only [textbookEUniformWitnessStepFormula, FOFormula.Satisfies]
  apply exists_congr
  intro tupleFamily
  apply exists_congr
  intro prefixSpaces
  apply exists_congr
  intro requestDomain
  apply exists_congr
  intro selectedRange
  let assignment : Tuple LCarrier.{u} 10 :=
    snoc (snoc (snoc (snoc
      ![U, order, tasks, omega, current, next]
      tupleFamily) prefixSpaces) requestDomain) selectedRange
  change
    (FOFormula.Satisfies LMem
        (FOFormula.rename ![(4 : Fin 10), (3 : Fin 10), (6 : Fin 10)]
          (replacementRangeEqFormula
            ContinuumFormula.finiteTupleSpaceFormula)) assignment /\
      FOFormula.Satisfies LMem
        (sUnionEqAt (7 : Fin 10) (6 : Fin 10)) assignment /\
      FOFormula.Satisfies LMem
        (productEqAt (8 : Fin 10) (2 : Fin 10) (7 : Fin 10)) assignment /\
      FOFormula.Satisfies LMem
        (FOFormula.rename
          ![(0 : Fin 10), (4 : Fin 10), (1 : Fin 10),
            (8 : Fin 10), (9 : Fin 10)]
          (replacementRangeEqFormula textbookEUniformTotalFormula))
          assignment /\
      FOFormula.Satisfies LMem
        (binaryUnionEqAt
          (5 : Fin 10) (4 : Fin 10) (9 : Fin 10)) assignment) <->
      _
  simp only [FOFormula.satisfies_rename]
  have htuple :
      (fun i =>
        assignment
          (![(4 : Fin 10), (3 : Fin 10), (6 : Fin 10)] i)) =
        ![current, omega, tupleFamily] := by
    funext i
    fin_cases i <;> rfl
  have hrange :
      (fun i =>
        assignment
          (![(0 : Fin 10), (4 : Fin 10), (1 : Fin 10),
            (8 : Fin 10), (9 : Fin 10)] i)) =
        ![U, current, order, requestDomain, selectedRange] := by
    funext i
    fin_cases i <;> rfl
  rw [htuple, hrange]
  have htupleSemantics :
      FOFormula.Satisfies LMem
          (replacementRangeEqFormula
            ContinuumFormula.finiteTupleSpaceFormula)
          ![current, omega, tupleFamily] <->
        ∀ space : LCarrier.{u}, space.1 ∈ tupleFamily.1 <->
          ∃ index : LCarrier.{u}, index.1 ∈ omega.1 /\
            FOFormula.Satisfies LMem
              ContinuumFormula.finiteTupleSpaceFormula
              ![current, index, space] := by
    have h := satisfies_replacementRangeEqFormula_lCarrier
      ContinuumFormula.finiteTupleSpaceFormula
      ![current] omega tupleFamily
    have hinputAssignment :
        ∀ index space : LCarrier.{u},
          snoc (snoc ![current] index) space =
            ![current, index, space] := by
      intro index space
      funext i
      fin_cases i <;> rfl
    simpa only [hinputAssignment, show
      snoc (snoc ![current] omega) tupleFamily =
        ![current, omega, tupleFamily] by
          funext i
          fin_cases i <;> rfl] using h
  have hselectedSemantics :
      FOFormula.Satisfies LMem
          (replacementRangeEqFormula textbookEUniformTotalFormula)
          ![U, current, order, requestDomain, selectedRange] <->
        ∀ output : LCarrier.{u}, output.1 ∈ selectedRange.1 <->
          ∃ request : LCarrier.{u}, request.1 ∈ requestDomain.1 /\
            FOFormula.Satisfies LMem textbookEUniformTotalFormula
              ![U, current, order, request, output] := by
    have h := satisfies_replacementRangeEqFormula_lCarrier
      textbookEUniformTotalFormula
      ![U, current, order] requestDomain selectedRange
    have hinputAssignment :
        ∀ request output : LCarrier.{u},
          snoc (snoc ![U, current, order] request) output =
            ![U, current, order, request, output] := by
      intro request output
      funext i
      fin_cases i <;> rfl
    simpa only [hinputAssignment, show
      snoc (snoc ![U, current, order] requestDomain) selectedRange =
        ![U, current, order, requestDomain, selectedRange] by
          funext i
          fin_cases i <;> rfl] using h
  rw [htupleSemantics, hselectedSemantics]
  simp only [satisfies_sUnionEqAt_lCarrier,
    satisfies_productEqAt_lCarrier,
    satisfies_binaryUnionEqAt_lCarrier]
  have ha2 : assignment (2 : Fin 10) = tasks := by rfl
  have ha4 : assignment (4 : Fin 10) = current := by rfl
  have ha5 : assignment (5 : Fin 10) = next := by rfl
  have ha6 : assignment (6 : Fin 10) = tupleFamily := by rfl
  have ha7 : assignment (7 : Fin 10) = prefixSpaces := by rfl
  have ha8 : assignment (8 : Fin 10) = requestDomain := by rfl
  have ha9 : assignment (9 : Fin 10) = selectedRange := by rfl
  rw [ha2, ha4, ha5, ha6, ha7, ha8, ha9]

/-! ## Identification with the constructed step -/

 theorem mem_internalFiniteTupleSpaceFamily_iff_replacement
    (current space : LCarrier.{u}) :
    space.1 ∈
        (ContinuumFormula.internalFiniteTupleSpaceFamilyData current).family.1 <->
      ∃ index : LCarrier.{u},
        index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 /\
        FOFormula.Satisfies LMem
          ContinuumFormula.finiteTupleSpaceFormula
          ![current, index, space] := by
  constructor
  · intro hspace
    rcases
        (ContinuumFormula.internalFiniteTupleSpaceFamilyData current)
          |>.mem_family_iff space |>.mp hspace with
      ⟨n, hspaceEq⟩
    let index :=
      TextbookNatFormula.textbookNatCodeLCarrier n
    refine ⟨index, ?_, ?_⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode n)).mpr ⟨n, rfl⟩
    · subst space
      exact
        (ContinuumFormula.satisfies_finiteTupleSpaceFormula_natCode_iff
          current
          (ContinuumFormula.finiteTupleSpaceLCarrier current n) n).mpr
            rfl
  · rintro ⟨index, hindex, hspace⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindex with
      ⟨n, hindexRaw⟩
    have hindexEq :
        index = TextbookNatFormula.textbookNatCodeLCarrier n :=
      Subtype.ext hindexRaw
    subst index
    have hspaceRaw :
        space.1 = textbookTupleSpace current.1 n :=
      (ContinuumFormula.satisfies_finiteTupleSpaceFormula_natCode_iff
        current space n).mp hspace
    have hspaceEq :
        space = ContinuumFormula.finiteTupleSpaceLCarrier current n :=
      Subtype.ext hspaceRaw
    exact
      (ContinuumFormula.internalFiniteTupleSpaceFamilyData current)
        |>.mem_family_iff space |>.mpr ⟨n, hspaceEq⟩

 theorem tupleFamily_eq_internal
    (current tupleFamily : LCarrier.{u})
    (hfamily : ∀ space : LCarrier.{u}, space.1 ∈ tupleFamily.1 <->
      ∃ index : LCarrier.{u},
        index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 /\
        FOFormula.Satisfies LMem
          ContinuumFormula.finiteTupleSpaceFormula
          ![current, index, space]) :
    tupleFamily =
      (ContinuumFormula.internalFiniteTupleSpaceFamilyData current).family := by
  apply Subtype.ext
  apply ZFSet.ext
  intro space
  constructor
  · intro hspace
    let spaceL : LCarrier.{u} :=
      ⟨space, mem_L_of_mem hspace tupleFamily.2⟩
    exact
      (mem_internalFiniteTupleSpaceFamily_iff_replacement
        current spaceL).mpr ((hfamily spaceL).mp hspace)
  · intro hspace
    let spaceL : LCarrier.{u} :=
      ⟨space,
        mem_L_of_mem hspace
          (ContinuumFormula.internalFiniteTupleSpaceFamilyData
            current).family.2⟩
    exact (hfamily spaceL).mpr
      ((mem_internalFiniteTupleSpaceFamily_iff_replacement
        current spaceL).mp hspace)

 theorem selectedRange_eq_internal
    (U current selectedRange : LCarrier.{u})
    (hrange : ∀ output : LCarrier.{u}, output.1 ∈ selectedRange.1 <->
      ∃ request : LCarrier.{u},
        request.1 ∈
          (textbookEUniformWitnessRequestDomain current).1 /\
        FOFormula.Satisfies LMem textbookEUniformTotalFormula
          ![U, current, canonicalWitnessOrder U, request, output]) :
    selectedRange =
      (textbookEUniformWitnessReplacementData current U).range := by
  apply Subtype.ext
  apply ZFSet.ext
  intro output
  constructor
  · intro houtput
    let outputL : LCarrier.{u} :=
      ⟨output, mem_L_of_mem houtput selectedRange.2⟩
    exact
      (textbookEUniformWitnessReplacementData current U)
        |>.mem_range_iff outputL |>.mpr ((hrange outputL).mp houtput)
  · intro houtput
    let outputL : LCarrier.{u} :=
      ⟨output,
        mem_L_of_mem houtput
          (textbookEUniformWitnessReplacementData current U).range.2⟩
    exact (hrange outputL).mpr
      ((textbookEUniformWitnessReplacementData current U)
        |>.mem_range_iff outputL |>.mp houtput)

/-- Exact LCarrier semantics of the fixed graph at its canonical parameters. -/
@[simp]
theorem satisfies_textbookEUniformWitnessStepFormula_iff
    (U current next : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookEUniformWitnessStepFormula
        ![U, canonicalWitnessOrder U, textbookEWitnessTaskDomain,
          omegaLCarrier, current, next] <->
      next = textbookEUniformWitnessStep current U := by
  rw [satisfies_textbookEUniformWitnessStepFormula]
  constructor
  · rintro ⟨tupleFamily, prefixSpaces, requestDomain, selectedRange,
      htupleFamily, hprefixSpaces, hrequestDomain, hselectedRange, hnext⟩
    have htupleEq :=
      tupleFamily_eq_internal current tupleFamily htupleFamily
    have hprefixEq :
        prefixSpaces =
          ContinuumFormula.internalFiniteTupleSpaces current := by
      rw [hprefixSpaces, htupleEq]
      rfl
    have hrequestEq :
        requestDomain =
          textbookEUniformWitnessRequestDomain current := by
      rw [hrequestDomain, hprefixEq]
      rfl
    have hselectedSpec : ∀ output : LCarrier.{u},
        output.1 ∈ selectedRange.1 <->
          ∃ request : LCarrier.{u},
            request.1 ∈
              (textbookEUniformWitnessRequestDomain current).1 /\
            FOFormula.Satisfies LMem textbookEUniformTotalFormula
              ![U, current, canonicalWitnessOrder U, request, output] := by
      simpa only [hrequestEq] using hselectedRange
    have hselectedEq :=
      selectedRange_eq_internal U current selectedRange hselectedSpec
    rw [hnext, hselectedEq]
    rfl
  · intro hnext
    subst next
    refine
      ⟨(ContinuumFormula.internalFiniteTupleSpaceFamilyData current).family,
        ContinuumFormula.internalFiniteTupleSpaces current,
        textbookEUniformWitnessRequestDomain current,
        (textbookEUniformWitnessReplacementData current U).range,
        ?_, rfl, rfl, ?_, rfl⟩
    · exact mem_internalFiniteTupleSpaceFamily_iff_replacement current
    · exact
        (textbookEUniformWitnessReplacementData current U).mem_range_iff



end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TextbookEUniformWitnessStepFormula


