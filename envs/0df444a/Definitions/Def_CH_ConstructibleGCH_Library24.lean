-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library24
-- name    : CH_ConstructibleGCH_Library24
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T08:33:33.167485+00:00
-- url     : https://prove2.me/theorems/8fcb19eb-ece8-4918-b0d7-e3e365aee03e
-- title:
--   Coded row histories and constructible local graphs
-- statement:
--   A coded row history records the local evaluations used by textbook E. This library supplies the row-entry and history interfaces and the constructible local graph data needed to collect those evaluations internally.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookELocalDomainLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookELocalSolutionDecodeLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookELocalSolutionLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookERowHistoryAlgebra.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookERowEntryFormula.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookERowHistoryConstructible.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookELocalGraphConstructible.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library23
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookELocalDomainLCarrier -/
section GCHSource_Work_CUGCH_TextbookELocalDomainLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Local domains for the textbook E recursion in L

The textbook recursion relation compares only the first natural coordinate.
Consequently every iterated predecessor of `<m,n>` is already an immediate
predecessor, and its predecessor closure is exactly `m x omega`.  This file
identifies the generic local recursion domain with the concrete set
`{<m,n>} union (m x omega)` and proves that it belongs to `L`.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## Transitivity of the textbook relation -/

theorem textbookERelation_transitive
    {left middle right : ZFSet.{u}}
    (hlm : ClassRel TextbookERelation left middle)
    (hmr : ClassRel TextbookERelation middle right) :
    ClassRel TextbookERelation left right := by
  rw [classRel_textbookERelation_iff] at hlm hmr ⊢
  rcases hlm with
    ⟨i, k, m, n, hi, hk, hm, hn, hleft, hmiddle, him⟩
  rcases hmr with
    ⟨m', n', r, s, hm', hn', hr, hs, hmiddle', hright, hmr'⟩
  have hcoordinates : m = m' ∧ n = n' := by
    apply ZFSet.pair_inj.mp
    exact hmiddle.symm.trans hmiddle'
  have hrOrdinal : r.IsOrdinal :=
    (ZFSet.isOrdinal_toZFSet (Ordinal.omega0 : Ordinal.{u})).mem hr
  have hir : i ∈ r := by
    exact hrOrdinal.isTransitive.mem_trans him
      (by simpa only [hcoordinates.1] using hmr')
  exact ⟨i, k, r, s, hi, hk, hr, hs, hleft, hright, hir⟩

/-! ## Collapse of all finite predecessor layers -/

 theorem textbookE_predecessorLayer_subset_first
    {m n : ZFSet.{u}} (hm : m ∈ textbookEOmegaZF)
    (hn : n ∈ textbookEOmegaZF) :
    ∀ stage : Nat,
      predecessorLayer TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn (ZFSet.pair m n) stage ⊆
        ZFSet.prod m textbookEOmegaZF := by
  intro stage
  induction stage with
  | zero =>
      intro z hz
      rw [predecessorLayer_zero] at hz
      have hzSpec :=
        (displayedPredecessors_spec
          textbookERelation_hasSetPredecessorsOn
          (mem_textbookEDomain_iff.mpr ⟨m, hm, n, hn, rfl⟩) z).mp hz
      exact (textbookE_predecessorSet hm hn z).mpr hzSpec
  | succ stage ih =>
      intro z hz
      rcases (mem_predecessorLayer_succ_iff
          textbookERelation_hasSetPredecessorsOn
          (mem_textbookEDomain_iff.mpr ⟨m, hm, n, hn, rfl⟩)
          stage).mp hz with
        ⟨y, hyLayer, hzDomain, hzy⟩
      have hyFirst : y ∈ ZFSet.prod m textbookEOmegaZF := ih hyLayer
      have hySpec := (textbookE_predecessorSet hm hn y).mp hyFirst
      exact (textbookE_predecessorSet hm hn z).mpr
        ⟨hzDomain, textbookERelation_transitive hzy hySpec.2⟩

/-- For the textbook relation, all iterated predecessors are already in the
first predecessor set `m x omega`. -/
theorem textbookE_predecessorClosure_eq
    {m n : ZFSet.{u}} (hm : m ∈ textbookEOmegaZF)
    (hn : n ∈ textbookEOmegaZF) :
    predecessorClosure TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn (ZFSet.pair m n) =
      ZFSet.prod m textbookEOmegaZF := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    rcases mem_predecessorClosure_iff.mp hz with ⟨stage, hzStage⟩
    exact textbookE_predecessorLayer_subset_first hm hn stage hzStage
  · intro hz
    apply mem_predecessorClosure_iff.mpr
    refine ⟨0, ?_⟩
    rw [predecessorLayer_zero]
    apply (displayedPredecessors_spec
      textbookERelation_hasSetPredecessorsOn
      (mem_textbookEDomain_iff.mpr ⟨m, hm, n, hn, rfl⟩) z).mpr
    exact (textbookE_predecessorSet hm hn z).mp hz

/-- The generic local domain at `<m,n>` is the concrete one-point extension
of `m x omega`. -/
theorem textbookE_localRecursionDomain_eq
    {m n : ZFSet.{u}} (hm : m ∈ textbookEOmegaZF)
    (hn : n ∈ textbookEOmegaZF) :
    localRecursionDomain TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn (ZFSet.pair m n) =
      insert (ZFSet.pair m n) (ZFSet.prod m textbookEOmegaZF) := by
  apply ZFSet.ext
  intro z
  rw [mem_localRecursionDomain_iff,
    textbookE_predecessorClosure_eq hm hn,
    ZFSet.mem_insert_iff]

/-! ## Constructibility of the local domain -/

/-- The local recursion domain at every standard coded key is an actual
member of `L`. -/
theorem textbookE_localRecursionDomain_natCode_mem_L
    (m n : Nat) :
    localRecursionDomain TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn
        (ZFSet.pair (natCode m : ZFSet.{u})
          (natCode n : ZFSet.{u})) ∈ L := by
  have hm : (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 m)
  have hn : (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n)
  have hdomain := textbookE_localRecursionDomain_eq
    (m := (natCode m : ZFSet.{u}))
    (n := (natCode n : ZFSet.{u})) hm hn
  rw [hdomain]
  have hkey : ZFSet.pair (natCode m) (natCode n) ∈ L :=
    orderedPair_mem_L (natCode_mem_L m) (natCode_mem_L n)
  let mL : Model.LCarrier.{u} := ⟨natCode m, natCode_mem_L m⟩
  have hproduct : ZFSet.prod (natCode m) textbookEOmegaZF ∈ L := by
    simpa only [mL, Model.prodLCarrier_val, Model.omegaLCarrier,
      textbookEOmegaZF] using
      (Model.prodLCarrier mL Model.omegaLCarrier).2
  rw [ZFSet.insert_eq]
  exact union_mem_L (singleton_mem_L hkey) hproduct

namespace Model

local notation "LMem" => lCarrierMem

/-! ## Packaged keys and local domains -/

/-- The standard textbook recursion key `<m,n>` as an actual element of
`L`. -/
def textbookEKeyLCarrier (m n : Nat) : LCarrier.{u} :=
  orderedPairLCarrier
    ⟨natCode m, natCode_mem_L m⟩
    ⟨natCode n, natCode_mem_L n⟩

@[simp]
theorem textbookEKeyLCarrier_val (m n : Nat) :
    (textbookEKeyLCarrier m n : LCarrier.{u}).1 =
      ZFSet.pair (natCode m) (natCode n) :=
  rfl

theorem textbookEKeyLCarrier_mem_domain (m n : Nat) :
    (textbookEKeyLCarrier m n : LCarrier.{u}).1 ∈ TextbookEDomain := by
  apply mem_textbookEDomain_iff.mpr
  refine ⟨natCode m, ?_, natCode n, ?_, rfl⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 m)
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n)

/-- The concrete local domain at a standard textbook key, packaged as an
actual member of `L`. -/
def textbookELocalDomainLCarrier (m n : Nat) : LCarrier.{u} :=
  ⟨localRecursionDomain TextbookEDomain TextbookERelation
      textbookERelation_hasSetPredecessorsOn
      (ZFSet.pair (natCode m) (natCode n)),
    textbookE_localRecursionDomain_natCode_mem_L m n⟩

@[simp]
theorem textbookELocalDomainLCarrier_val (m n : Nat) :
    (textbookELocalDomainLCarrier m n : LCarrier.{u}).1 =
      localRecursionDomain TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn
        (ZFSet.pair (natCode m) (natCode n)) :=
  rfl

/-! ## Exact semantics of the least-closed-set formula -/

@[simp]
theorem satisfies_textbookELocalDomainFormula_lCarrier
    (a domain : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem
        (localDomainFormula
          TextbookEFormula.textbookEDomainWithParamFormula
          TextbookEFormula.textbookERelationWithParamFormula)
        ![a, textbookEKeyLCarrier m n, domain] ↔
      domain.1 = (textbookELocalDomainLCarrier m n).1 := by
  let key : LCarrier.{u} := textbookEKeyLCarrier m n
  have hclass : ∀ z : LCarrier.{u},
      FOFormula.Satisfies LMem
          TextbookEFormula.textbookEDomainWithParamFormula
          (snoc ![a] z) ↔ z.1 ∈ TextbookEDomain := by
    intro z
    have hassign : snoc ![a] z = ![a, z] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign,
      satisfies_textbookEDomainWithParamFormula_lCarrier]
  have hrelationFormula : ∀ y z : LCarrier.{u},
      FOFormula.Satisfies LMem
          TextbookEFormula.textbookERelationWithParamFormula
          (snoc (snoc ![a] y) z) ↔
        ClassRel TextbookERelation y.1 z.1 := by
    intro y z
    have hassign : snoc (snoc ![a] y) z = ![a, y, z] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign,
      satisfies_textbookERelationWithParamFormula_lCarrier]
  have hsemantic :=
    satisfies_localDomainFormula_lCarrier_iff_eq_localRecursionDomain
      TextbookEFormula.textbookEDomainWithParamFormula
      TextbookEFormula.textbookERelationWithParamFormula
      ![a] hclass hrelationFormula
      textbookERelation_isRelationOn
      textbookERelation_hasSetPredecessorsOn
      textbookERelation_predecessorsClosedIn_L
      (x := key) (domain := domain)
      (textbookEKeyLCarrier_mem_domain m n)
      (textbookE_localRecursionDomain_natCode_mem_L m n)
  have hassign : snoc (snoc ![a] key) domain =
      ![a, textbookEKeyLCarrier m n, domain] := by
    funext i
    fin_cases i <;> rfl
  simpa only [hassign, key, textbookEKeyLCarrier_val,
    textbookELocalDomainLCarrier_val] using
    hsemantic

end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookELocalDomainLCarrier


/- Source module: Solutions.Work_CUGCH_TextbookELocalSolutionDecodeLCarrier -/
section GCHSource_Work_CUGCH_TextbookELocalSolutionDecodeLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Decoding textbook E local solutions over L

An `LCarrier` graph satisfying the unchanged textbook local-solution formula
is decoded into an actual `TextbookLocalSolution`.  The textbook agreement
theorem then identifies every value of that graph with `textbookEByKey`.
-/

section

open Set

universe u

namespace Constructible

noncomputable section

open FiniteSequenceZF

namespace Model

local notation "LMem" => lCarrierMem

/-- Every `LCarrier` graph satisfying the textbook E local-solution formula
at a standard key decodes to the literal local solution used in the textbook
recursion theorem. -/
theorem exists_textbookELocalSolution_of_satisfies_lCarrier
    (a graph : LCarrier.{u}) (m n : Nat)
    (hformula : FOFormula.Satisfies LMem
      (localSolutionFormula
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        TextbookEFormula.textbookEStepFormula)
      ![a, textbookEKeyLCarrier m n, graph]) :
    exists solution : TextbookLocalSolution
        TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn
        (textbookEStep a.1) (textbookEKeyLCarrier m n).1,
      solution.graph = graph.1 := by
  classical
  let key : LCarrier.{u} := textbookEKeyLCarrier m n
  let localDom : LCarrier.{u} := textbookELocalDomainLCarrier m n
  have hformula' : FOFormula.Satisfies LMem
      (localSolutionFormula
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        TextbookEFormula.textbookEStepFormula)
      (snoc (snoc ![a] key) graph) := by
    have hassign : snoc (snoc ![a] key) graph = ![a, key, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    simpa only [key] using hformula
  rcases (satisfies_localSolutionFormula_lCarrier_iff
      TextbookEFormula.textbookEDomainWithParamFormula
      TextbookEFormula.textbookERelationWithParamFormula
      TextbookEFormula.textbookEStepFormula ![a] key graph).mp
      hformula' with
    ⟨domain, hdomainFormula, hfunction, hsteps⟩
  have hdomainAssignment :
      snoc (snoc ![a] key) domain = ![a, key, domain] := by
    funext i
    fin_cases i <;> rfl
  have hdomainRaw : domain.1 = localDom.1 := by
    apply (satisfies_textbookELocalDomainFormula_lCarrier
      a domain m n).mp
    rw [← hdomainAssignment]
    simpa only [key] using hdomainFormula
  have hdomainEq : domain = localDom := Subtype.ext hdomainRaw
  subst domain
  let d : ZFSet.{u} := localDom.1
  have hdL : d ∈ L := localDom.2
  let asCarrier : forall t : ZFSet.{u}, t ∈ d -> LCarrier.{u} :=
    fun t ht => ⟨t, mem_L_of_mem ht hdL⟩
  have hfunctionTotal : forall t : ZFSet.{u}, forall ht : t ∈ d,
      exists value : LCarrier.{u},
        ZFSet.pair t value.1 ∈ graph.1 /\
          forall other : LCarrier.{u},
            ZFSet.pair t other.1 ∈ graph.1 -> other = value := by
    intro t ht
    have htLocal : (asCarrier t ht).1 ∈ localDom.1 := by
      simpa only [d, asCarrier] using ht
    simpa only [asCarrier] using hfunction.1 (asCarrier t ht) htLocal
  let chosenValue (t : ZFSet.{u}) (ht : t ∈ d) : LCarrier.{u} :=
    Classical.choose (hfunctionTotal t ht)
  let value : ZFSet.{u} -> ZFSet.{u} := fun t =>
    if ht : t ∈ d then (chosenValue t ht).1 else ∅
  have hchosenSpec (t : ZFSet.{u}) (ht : t ∈ d) :
      ZFSet.pair t (chosenValue t ht).1 ∈ graph.1 /\
        forall other : LCarrier.{u},
          ZFSet.pair t other.1 ∈ graph.1 ->
            other = chosenValue t ht :=
    Classical.choose_spec (hfunctionTotal t ht)
  have hvalueEqChosen (t : ZFSet.{u}) (ht : t ∈ d) :
      value t = (chosenValue t ht).1 := by
    simp only [value, dif_pos ht]
  have hvalueSpec (t : ZFSet.{u}) (ht : t ∈ d) :
      ZFSet.pair t (value t) ∈ graph.1 /\
        forall other : LCarrier.{u},
          ZFSet.pair t other.1 ∈ graph.1 ->
            other.1 = value t := by
    constructor
    · rw [hvalueEqChosen t ht]
      exact (hchosenSpec t ht).1
    · intro other hother
      have hotherEq := (hchosenSpec t ht).2 other hother
      rw [hotherEq, hvalueEqChosen t ht]
  have hvalueL (t : ZFSet.{u}) (ht : t ∈ d) : value t ∈ L := by
    rw [hvalueEqChosen t ht]
    exact (chosenValue t ht).2
  have hgraphEq : graph.1 = predecessorRestrictionGraph d value := by
    apply ZFSet.ext
    intro pair
    constructor
    · intro hpairGraph
      let pairL : LCarrier.{u} :=
        ⟨pair, mem_L_of_mem hpairGraph graph.2⟩
      rcases hfunction.2 pairL hpairGraph with
        ⟨input, hinputD, output, hpairEq⟩
      have hinputD' : input.1 ∈ d := by
        simpa only [d] using hinputD
      have houtputEq : output.1 = value input.1 :=
        (hvalueSpec input.1 hinputD').2 output (by
          rw [← hpairEq]
          exact hpairGraph)
      apply mem_predecessorRestrictionGraph_iff.mpr
      refine ⟨input.1, hinputD', ?_⟩
      rw [← houtputEq]
      exact hpairEq.symm
    · intro hpairRestriction
      rcases mem_predecessorRestrictionGraph_iff.mp hpairRestriction with
        ⟨input, hinputD, hpairEq⟩
      rw [← hpairEq]
      exact (hvalueSpec input hinputD).1
  have hkeyDomain : key.1 ∈ TextbookEDomain := by
    simpa only [key] using textbookEKeyLCarrier_mem_domain m n
  have hsatisfies : SatisfiesTextbookLocalRecursion
      TextbookEDomain TextbookERelation
      textbookERelation_hasSetPredecessorsOn
      (textbookEStep a.1) key.1 value := by
    intro top htopD
    have htopD' : top ∈ d := by
      simpa only [d, localDom, key,
        textbookELocalDomainLCarrier_val,
        textbookEKeyLCarrier_val] using htopD
    let topL : LCarrier.{u} := asCarrier top htopD'
    have htopLocal : topL.1 ∈ localDom.1 := by
      simpa only [topL, asCarrier, d] using htopD'
    rcases hsteps topL htopLocal with
      ⟨restriction, output, hrestriction, houtputGraph, hstepFormula⟩
    have htopA : top ∈ TextbookEDomain :=
      localRecursionDomain_subset
        textbookERelation_hasSetPredecessorsOn hkeyDomain htopD
    have hrestrictionEq : restriction.1 =
        predecessorRestrictionGraph
          (displayedPredecessors TextbookEDomain TextbookERelation
            textbookERelation_hasSetPredecessorsOn top) value := by
      apply ZFSet.ext
      intro pair
      constructor
      · intro hpairRestriction
        let pairL : LCarrier.{u} :=
          ⟨pair, mem_L_of_mem hpairRestriction restriction.2⟩
        rcases (hrestriction pairL).mp hpairRestriction with
          ⟨hpairGraph, input, output', hpairEq,
            hinputFormula, hrelationFormula⟩
        have hinputAssignment : snoc ![a] input = ![a, input] := by
          funext i
          fin_cases i <;> rfl
        have hinputA : input.1 ∈ TextbookEDomain := by
          apply (satisfies_textbookEDomainWithParamFormula_lCarrier
            a input).mp
          simpa only [hinputAssignment] using hinputFormula
        have hrelationAssignment :
            snoc (snoc ![a] input) topL = ![a, input, topL] := by
          funext i
          fin_cases i <;> rfl
        have hinputTop : ClassRel TextbookERelation input.1 top := by
          apply (satisfies_textbookERelationWithParamFormula_lCarrier
            a input topL).mp
          simpa only [hrelationAssignment, topL, asCarrier] using
            hrelationFormula
        have hinputPred : input.1 ∈
            displayedPredecessors TextbookEDomain TextbookERelation
              textbookERelation_hasSetPredecessorsOn top :=
          (displayedPredecessors_spec
            textbookERelation_hasSetPredecessorsOn htopA input.1).mpr
              ⟨hinputA, hinputTop⟩
        have hinputD : input.1 ∈ d := by
          apply localRecursionDomain_predecessorClosed
            textbookERelation_isRelationOn
            textbookERelation_hasSetPredecessorsOn hkeyDomain htopD'
          exact hinputTop
        have houtputEq : output'.1 = value input.1 :=
          (hvalueSpec input.1 hinputD).2 output' (by
            rw [hpairEq] at hpairGraph
            exact hpairGraph)
        apply mem_predecessorRestrictionGraph_iff.mpr
        refine ⟨input.1, hinputPred, ?_⟩
        rw [← houtputEq]
        simpa only [pairL] using hpairEq.symm
      · intro hpairExpected
        rcases mem_predecessorRestrictionGraph_iff.mp hpairExpected with
          ⟨input, hinputPred, hpairEq⟩
        have hinputSpec :=
          (displayedPredecessors_spec
            textbookERelation_hasSetPredecessorsOn htopA input).mp
              hinputPred
        have hinputD : input ∈ d := by
          apply localRecursionDomain_predecessorClosed
            textbookERelation_isRelationOn
            textbookERelation_hasSetPredecessorsOn hkeyDomain htopD'
          exact hinputSpec.2
        let inputL : LCarrier.{u} := asCarrier input hinputD
        let valueL : LCarrier.{u} := ⟨value input, hvalueL input hinputD⟩
        let pairL : LCarrier.{u} := orderedPairLCarrier inputL valueL
        have hpairMembership : pairL.1 ∈ restriction.1 := by
          apply (hrestriction pairL).mpr
          refine ⟨?_, inputL, valueL, ?_, ?_, ?_⟩
          · simpa only [pairL, orderedPairLCarrier_val, inputL, valueL]
              using (hvalueSpec input hinputD).1
          · simp only [pairL, orderedPairLCarrier_val, inputL, valueL]
          · have hinputAssignment : snoc ![a] inputL = ![a, inputL] := by
              funext i
              fin_cases i <;> rfl
            rw [hinputAssignment]
            exact (satisfies_textbookEDomainWithParamFormula_lCarrier
              a inputL).mpr hinputSpec.1
          · have hrelationAssignment :
                snoc (snoc ![a] inputL) topL =
                  ![a, inputL, topL] := by
              funext i
              fin_cases i <;> rfl
            rw [hrelationAssignment]
            apply (satisfies_textbookERelationWithParamFormula_lCarrier
              a inputL topL).mpr
            simpa only [inputL, topL, asCarrier] using hinputSpec.2
        rw [← hpairEq]
        simpa only [pairL, orderedPairLCarrier_val, inputL, valueL] using
          hpairMembership
    have houtputEq : output.1 = value top :=
      (hvalueSpec top htopD').2 output (by
        simpa only [topL, asCarrier] using houtputGraph)
    have hstepAssignment :
        snoc (snoc (snoc ![a] topL) restriction) output =
          ![a, topL, restriction, output] := by
      funext i
      fin_cases i <;> rfl
    have hstepSemantic :=
      (satisfies_textbookEStepFormula_lCarrier_iff
        a topL restriction output).mp (by
          rw [← hstepAssignment]
          exact hstepFormula)
    have hstepEq : output.1 = textbookEStep a.1 top restriction.1 := by
      simpa only [topL, asCarrier] using hstepSemantic.2
    rw [← houtputEq, hstepEq, hrestrictionEq]
  let solution : TextbookLocalSolution
      TextbookEDomain TextbookERelation
      textbookERelation_hasSetPredecessorsOn
      (textbookEStep a.1) key.1 :=
    { value := value
      graph := graph.1
      graph_eq := hgraphEq
      satisfies := hsatisfies }
  let solution' : TextbookLocalSolution
      TextbookEDomain TextbookERelation
      textbookERelation_hasSetPredecessorsOn
      (textbookEStep a.1) (textbookEKeyLCarrier m n).1 := by
    simpa only [key] using solution
  refine ⟨solution', ?_⟩
  simp only [solution', solution]

/-- Every value displayed by a formula-satisfying local graph is the value
of the textbook global recursion. -/
theorem textbookEByKey_eq_of_satisfies_localSolution_lCarrier
    (a graph output : LCarrier.{u}) (m n : Nat)
    (hformula : FOFormula.Satisfies LMem
      (localSolutionFormula
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        TextbookEFormula.textbookEStepFormula)
      ![a, textbookEKeyLCarrier m n, graph])
    (hvalue : ZFSet.pair (textbookEKeyLCarrier m n).1 output.1 ∈
      graph.1) :
    output.1 = textbookEByKey a.1 (textbookEKeyLCarrier m n).1 := by
  rcases exists_textbookELocalSolution_of_satisfies_lCarrier
      a graph m n hformula with ⟨solution, hsolutionGraph⟩
  have hvalueRestriction :
      ZFSet.pair (textbookEKeyLCarrier m n).1 output.1 ∈
        predecessorRestrictionGraph
          (localRecursionDomain TextbookEDomain TextbookERelation
            textbookERelation_hasSetPredecessorsOn
            (textbookEKeyLCarrier m n).1) solution.value := by
    rw [← solution.graph_eq, hsolutionGraph]
    exact hvalue
  rcases mem_predecessorRestrictionGraph_iff.mp hvalueRestriction with
    ⟨source, _hsource, hpair⟩
  have hcoordinates := ZFSet.pair_inj.mp hpair
  have hlocalValue : output.1 =
      solution.value (textbookEKeyLCarrier m n).1 := by
    rw [hcoordinates.1] at hcoordinates
    exact hcoordinates.2.symm
  have hkeyDomain := textbookEKeyLCarrier_mem_domain m n
  have htopLocal : (textbookEKeyLCarrier m n).1 ∈
      localRecursionDomain TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn
        (textbookEKeyLCarrier m n).1 :=
    mem_localRecursionDomain_iff.mpr (Or.inl rfl)
  have hagree :=
    textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
      textbookERelation_isWellFoundedSetLikeOn
      (textbookEStep a.1) hkeyDomain solution htopLocal
  exact hlocalValue.trans (by
    simpa only [textbookEByKey] using hagree.symm)

end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookELocalSolutionDecodeLCarrier


/- Source module: Solutions.Work_CUGCH_TextbookELocalSolutionLCarrier -/
section GCHSource_Work_CUGCH_TextbookELocalSolutionLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Canonical local E solutions over L

This file verifies the unmodified textbook `localSolutionFormula` for the
actual restriction of `textbookEByKey` to a standard local recursion domain.
Every graph in the proof is an element of `LCarrier`: the local graph is an
explicit hypothesis, and each predecessor restriction is obtained by
Separation from that graph.
-/

section

universe u

namespace Constructible

open FiniteSequenceZF

namespace Model

noncomputable section

local notation "LMem" => lCarrierMem

 theorem textbookEByKey_mem_L_of_mem_local_graph
    (a graph : LCarrier.{u}) (m n : Nat)
    (hgraph :
      graph.1 =
        predecessorRestrictionGraph
          (textbookELocalDomainLCarrier m n).1
          (textbookEByKey a.1))
    {x : ZFSet.{u}}
    (hx : x ∈ (textbookELocalDomainLCarrier m n).1) :
    textbookEByKey a.1 x ∈ L := by
  have hpairGraph :
      ZFSet.pair x (textbookEByKey a.1 x) ∈ graph.1 := by
    rw [hgraph]
    exact pair_mem_predecessorRestrictionGraph
      (textbookEByKey a.1) hx
  have hpairL :
      ZFSet.pair x (textbookEByKey a.1 x) ∈ L :=
    mem_L_of_mem hpairGraph graph.2
  have hunorderedPair :
      ({x, textbookEByKey a.1 x} : ZFSet.{u}) ∈
        ZFSet.pair x (textbookEByKey a.1 x) := by
    simp [ZFSet.pair]
  have hunorderedPairL :
      ({x, textbookEByKey a.1 x} : ZFSet.{u}) ∈ L :=
    mem_L_of_mem hunorderedPair hpairL
  exact mem_L_of_mem (by simp) hunorderedPairL

 theorem formulaRestriction_textbookEByKey_eq
    (a graph top : LCarrier.{u}) (m n : Nat)
    (hgraph :
      graph.1 =
        predecessorRestrictionGraph
          (textbookELocalDomainLCarrier m n).1
          (textbookEByKey a.1))
    (htop : top.1 ∈ (textbookELocalDomainLCarrier m n).1) :
    (formulaRestrictionLCarrier
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        ![a] graph top).1 =
      predecessorRestrictionGraph
        (displayedPredecessors TextbookEDomain TextbookERelation
          textbookERelation_isWellFoundedSetLikeOn.2.2 top.1)
        (textbookEByKey a.1) := by
  have hkeyDomain :
      (textbookEKeyLCarrier m n).1 ∈ TextbookEDomain :=
    textbookEKeyLCarrier_mem_domain m n
  have htopDomain : top.1 ∈ TextbookEDomain := by
    exact localRecursionDomain_subset
      textbookERelation_hasSetPredecessorsOn hkeyDomain htop
  apply ZFSet.ext
  intro pair
  constructor
  · intro hpair
    rcases
        (mem_formulaRestrictionLCarrier_raw_iff
          TextbookEFormula.textbookEDomainWithParamFormula
          TextbookEFormula.textbookERelationWithParamFormula
          ![a] graph top pair).mp hpair with
      ⟨hpairGraph, input, output, hpairEq, hinputFormula,
        hrelationFormula⟩
    have hinputDomain : input.1 ∈ TextbookEDomain := by
      have hassign : snoc ![a] input = ![a, input] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign,
        satisfies_textbookEDomainWithParamFormula_lCarrier] at hinputFormula
      exact hinputFormula
    have hinputRelation :
        ClassRel TextbookERelation input.1 top.1 := by
      have hassign :
          snoc (snoc ![a] input) top = ![a, input, top] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign,
        satisfies_textbookERelationWithParamFormula_lCarrier] at hrelationFormula
      exact hrelationFormula
    have hinputPredecessor :
        input.1 ∈
          displayedPredecessors TextbookEDomain TextbookERelation
            textbookERelation_isWellFoundedSetLikeOn.2.2 top.1 :=
      (displayedPredecessors_spec
        textbookERelation_isWellFoundedSetLikeOn.2.2
        htopDomain input.1).mpr
        ⟨hinputDomain, hinputRelation⟩
    rw [hgraph] at hpairGraph
    rcases mem_predecessorRestrictionGraph_iff.mp hpairGraph with
      ⟨x, _hx, hgraphPair⟩
    have hcoordinates :=
      ZFSet.pair_inj.mp (hgraphPair.trans hpairEq)
    have hvalue :
        textbookEByKey a.1 input.1 = output.1 := by
      calc
        textbookEByKey a.1 input.1 =
            textbookEByKey a.1 x :=
          congrArg (textbookEByKey a.1) hcoordinates.1.symm
        _ = output.1 := hcoordinates.2
    apply mem_predecessorRestrictionGraph_iff.mpr
    refine ⟨input.1, hinputPredecessor, ?_⟩
    calc
      ZFSet.pair input.1 (textbookEByKey a.1 input.1) =
          ZFSet.pair input.1 output.1 := by rw [hvalue]
      _ = pair := hpairEq.symm
  · intro hpair
    rcases mem_predecessorRestrictionGraph_iff.mp hpair with
      ⟨input, hinputPredecessor, hpairEq⟩
    have hinputSpec :=
      (displayedPredecessors_spec
        textbookERelation_isWellFoundedSetLikeOn.2.2
        htopDomain input).mp hinputPredecessor
    have hinputLocal :
        input ∈ (textbookELocalDomainLCarrier m n).1 := by
      exact localRecursionDomain_predecessorClosed
        textbookERelation_isRelationOn
        textbookERelation_hasSetPredecessorsOn hkeyDomain
        htop hinputSpec.2
    have hpairGraph : pair ∈ graph.1 := by
      rw [hgraph]
      apply mem_predecessorRestrictionGraph_iff.mpr
      exact ⟨input, hinputLocal, hpairEq⟩
    let inputL : LCarrier.{u} :=
      ⟨input, mem_L_of_mem hinputLocal
        (textbookELocalDomainLCarrier m n).2⟩
    let outputL : LCarrier.{u} :=
      ⟨textbookEByKey a.1 input,
        textbookEByKey_mem_L_of_mem_local_graph
          a graph m n hgraph hinputLocal⟩
    apply
      (mem_formulaRestrictionLCarrier_raw_iff
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        ![a] graph top pair).mpr
    refine ⟨hpairGraph, inputL, outputL, hpairEq.symm, ?_, ?_⟩
    · have hassign : snoc ![a] inputL = ![a, inputL] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign,
        satisfies_textbookEDomainWithParamFormula_lCarrier]
      exact hinputSpec.1
    · have hassign :
          snoc (snoc ![a] inputL) top = ![a, inputL, top] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign,
        satisfies_textbookERelationWithParamFormula_lCarrier]
      exact hinputSpec.2

/-- The actual restriction graph of `textbookEByKey` on the canonical local
domain satisfies the exact textbook local-solution formula.  The hypothesis
does not merely assert an external graph predicate: `graph` is an actual
member of `LCarrier` whose underlying `ZFSet` is the displayed restriction
graph. -/
theorem textbookECanonicalLocalGraph_satisfies_localSolution
    (a graph : LCarrier.{u}) (m n : Nat)
    (hgraph :
      graph.1 =
        predecessorRestrictionGraph
          (textbookELocalDomainLCarrier m n).1
          (textbookEByKey a.1)) :
    FOFormula.Satisfies LMem
      (localSolutionFormula
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        TextbookEFormula.textbookEStepFormula)
      ![a, textbookEKeyLCarrier m n, graph] := by
  let domain : LCarrier.{u} := textbookELocalDomainLCarrier m n
  let key : LCarrier.{u} := textbookEKeyLCarrier m n
  apply
    (satisfies_localSolutionFormula_lCarrier_iff
      TextbookEFormula.textbookEDomainWithParamFormula
      TextbookEFormula.textbookERelationWithParamFormula
      TextbookEFormula.textbookEStepFormula
      ![a] key graph).mpr
  refine ⟨domain, ?_, ?_, ?_⟩
  · have hassign :
        snoc (snoc ![a] key) domain =
          ![a, textbookEKeyLCarrier m n, domain] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    apply
      (satisfies_textbookELocalDomainFormula_lCarrier
        a domain m n).mpr
    rfl
  · constructor
    · intro input hinput
      let value : LCarrier.{u} :=
        ⟨textbookEByKey a.1 input.1,
          textbookEByKey_mem_L_of_mem_local_graph
            a graph m n hgraph hinput⟩
      refine ⟨value, ?_, ?_⟩
      · rw [hgraph]
        exact pair_mem_predecessorRestrictionGraph
          (textbookEByKey a.1) hinput
      · intro other hother
        rw [hgraph] at hother
        rcases mem_predecessorRestrictionGraph_iff.mp hother with
          ⟨x, _hx, hpair⟩
        have hcoordinates := ZFSet.pair_inj.mp hpair
        apply Subtype.ext
        calc
          other.1 = textbookEByKey a.1 x :=
            hcoordinates.2.symm
          _ = textbookEByKey a.1 input.1 :=
            congrArg (textbookEByKey a.1) hcoordinates.1
          _ = value.1 := rfl
    · intro pair hpair
      rw [hgraph] at hpair
      rcases mem_predecessorRestrictionGraph_iff.mp hpair with
        ⟨input, hinput, hpairEq⟩
      let inputL : LCarrier.{u} :=
        ⟨input, mem_L_of_mem hinput domain.2⟩
      let value : LCarrier.{u} :=
        ⟨textbookEByKey a.1 input,
          textbookEByKey_mem_L_of_mem_local_graph
            a graph m n hgraph hinput⟩
      refine ⟨inputL, hinput, value, ?_⟩
      exact hpairEq.symm
  · intro top htop
    let restriction : LCarrier.{u} :=
      formulaRestrictionLCarrier
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        ![a] graph top
    have htopDomain : top.1 ∈ TextbookEDomain := by
      exact localRecursionDomain_subset
        textbookERelation_hasSetPredecessorsOn
        (textbookEKeyLCarrier_mem_domain m n) htop
    let value : LCarrier.{u} :=
      ⟨textbookEByKey a.1 top.1,
        textbookEByKey_mem_L_of_mem_local_graph
          a graph m n hgraph htop⟩
    refine ⟨restriction, value, ?_, ?_, ?_⟩
    · intro pair
      exact
        mem_formulaRestrictionLCarrier_iff
          TextbookEFormula.textbookEDomainWithParamFormula
          TextbookEFormula.textbookERelationWithParamFormula
          ![a] graph top pair
    · rw [hgraph]
      exact pair_mem_predecessorRestrictionGraph
        (textbookEByKey a.1) htop
    · have hrestriction :
          restriction.1 =
            predecessorRestrictionGraph
              (displayedPredecessors TextbookEDomain TextbookERelation
                textbookERelation_isWellFoundedSetLikeOn.2.2 top.1)
              (textbookEByKey a.1) := by
        exact formulaRestriction_textbookEByKey_eq
          a graph top m n hgraph htop
      have hrecursion :=
        textbookEByKey_satisfies_classRecursion a.1 top.1 htopDomain
      have hassign :
          snoc (snoc (snoc ![a] top) restriction) value =
            ![a, top, restriction, value] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign,
        satisfies_textbookEStepFormula_lCarrier_iff]
      refine ⟨htopDomain, ?_⟩
      change
        textbookEByKey a.1 top.1 =
          textbookEStep a.1 top.1 restriction.1
      rw [hrestriction]
      exact hrecursion

end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_TextbookELocalSolutionLCarrier


/- Source module: Solutions.Work_CUGCH_TextbookERowHistoryAlgebra -/
section GCHSource_Work_CUGCH_TextbookERowHistoryAlgebra
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Row algebra for the textbook E history

The recursion defining the textbook enumeration `E(a,n,m)` is organized in
rows.  Before row `m` is evaluated, its predecessor domain is the actual
set-coded product `m x omega`.  Passing from `m` to `m + 1` adjoins exactly
the row `{m} x omega`.

This file records that decomposition directly for actual Kuratowski
restriction graphs.  Every domain and graph below is a `ZFSet`; external
`Set ZFSet` predicates are not used as history objects.
-/

section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## Restriction graphs over unions -/

/-- Restricting a function to an internal union is the internal union of
the two restriction graphs. -/
theorem predecessorRestrictionGraph_union
    (left right : ZFSet.{u}) (f : ZFSet.{u} -> ZFSet.{u}) :
    predecessorRestrictionGraph (left ∪ right) f =
      predecessorRestrictionGraph left f ∪
        predecessorRestrictionGraph right f := by
  apply ZFSet.ext
  intro pair
  constructor
  · intro hpair
    rcases mem_predecessorRestrictionGraph_iff.mp hpair with
      ⟨x, hx, rfl⟩
    rcases ZFSet.mem_union.mp hx with hxLeft | hxRight
    · exact ZFSet.mem_union.mpr
        (Or.inl (pair_mem_predecessorRestrictionGraph f hxLeft))
    · exact ZFSet.mem_union.mpr
        (Or.inr (pair_mem_predecessorRestrictionGraph f hxRight))
  · intro hpair
    rcases ZFSet.mem_union.mp hpair with hpairLeft | hpairRight
    · rcases mem_predecessorRestrictionGraph_iff.mp hpairLeft with
        ⟨x, hx, rfl⟩
      exact pair_mem_predecessorRestrictionGraph f
        (ZFSet.mem_union.mpr (Or.inl hx))
    · rcases mem_predecessorRestrictionGraph_iff.mp hpairRight with
        ⟨x, hx, rfl⟩
      exact pair_mem_predecessorRestrictionGraph f
        (ZFSet.mem_union.mpr (Or.inr hx))

/-! ## The set-coded row -/

/-- The actual set-coded `m`-th row `{m} x omega`. -/
def textbookERowDomainZF (m : Nat) : ZFSet.{u} :=
  ZFSet.prod ({natCode m} : ZFSet.{u}) textbookEOmegaZF

@[simp]
theorem mem_textbookERowDomainZF_iff
    {m : Nat} {key : ZFSet.{u}} :
    key ∈ textbookERowDomainZF m ↔
      ∃ n : ZFSet.{u}, n ∈ textbookEOmegaZF ∧
        key = ZFSet.pair (natCode m) n := by
  rw [textbookERowDomainZF, ZFSet.mem_prod]
  constructor
  · rintro ⟨i, hi, n, hn, hkey⟩
    have hiEq : i = (natCode m : ZFSet.{u}) := by
      simpa only [ZFSet.mem_singleton] using hi
    subst i
    exact ⟨n, hn, hkey⟩
  · rintro ⟨n, hn, hkey⟩
    exact ⟨natCode m, by simp, n, hn, hkey⟩

/-- The actual Kuratowski graph contributed by row `m`. -/
def textbookERowRestrictionGraph
    (m : Nat) (f : ZFSet.{u} -> ZFSet.{u}) : ZFSet.{u} :=
  predecessorRestrictionGraph (textbookERowDomainZF m) f

@[simp]
theorem mem_textbookERowRestrictionGraph_iff
    {m : Nat} {f : ZFSet.{u} -> ZFSet.{u}} {pair : ZFSet.{u}} :
    pair ∈ textbookERowRestrictionGraph m f ↔
      ∃ n : ZFSet.{u}, n ∈ textbookEOmegaZF ∧
        ZFSet.pair
          (ZFSet.pair (natCode m) n)
          (f (ZFSet.pair (natCode m) n)) = pair := by
  rw [textbookERowRestrictionGraph,
    mem_predecessorRestrictionGraph_iff]
  constructor
  · rintro ⟨key, hkey, rfl⟩
    rcases mem_textbookERowDomainZF_iff.mp hkey with
      ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨ZFSet.pair (natCode m) n,
      mem_textbookERowDomainZF_iff.mpr ⟨n, hn, rfl⟩, rfl⟩

/-! ## Zero and successor histories -/

/-- The predecessor domain before row zero is empty. -/
@[simp]
theorem textbookEPredecessorDomain_zero :
    ZFSet.prod (natCode 0 : ZFSet.{u}) textbookEOmegaZF = ∅ := by
  apply ZFSet.ext
  intro key
  constructor
  · intro hkey
    rcases ZFSet.mem_prod.mp hkey with ⟨i, hi, _n, _hn, _hkey⟩
    have hiEmpty : i ∈ (∅ : ZFSet.{u}) := by
      simpa only [natCode, Nat.cast_zero, Ordinal.toZFSet_zero] using hi
    exact (ZFSet.notMem_empty i hiEmpty).elim
  · intro hkey
    exact (ZFSet.notMem_empty key hkey).elim

/-- The predecessor restriction graph before row zero is empty. -/
@[simp]
theorem predecessorRestrictionGraph_textbookE_zero
    (f : ZFSet.{u} -> ZFSet.{u}) :
    predecessorRestrictionGraph
        (ZFSet.prod (natCode 0) textbookEOmegaZF) f =
      ∅ := by
  rw [textbookEPredecessorDomain_zero]
  apply ZFSet.ext
  intro pair
  constructor
  · intro hpair
    rcases mem_predecessorRestrictionGraph_iff.mp hpair with
      ⟨x, hx, _⟩
    exact (ZFSet.notMem_empty x hx).elim
  · intro hpair
    exact (ZFSet.notMem_empty pair hpair).elim

/-- The predecessor domain for row `m + 1` is the old predecessor domain
plus the whole `m`-th row. -/
theorem textbookEPredecessorDomain_succ (m : Nat) :
    ZFSet.prod (natCode (m + 1) : ZFSet.{u}) textbookEOmegaZF =
      ZFSet.prod (natCode m) textbookEOmegaZF ∪
        textbookERowDomainZF m := by
  apply ZFSet.ext
  intro key
  constructor
  · intro hkey
    rcases ZFSet.mem_prod.mp hkey with ⟨i, hi, n, hn, hkeyEq⟩
    rw [natCode_succ_eq_insert, ZFSet.mem_insert_iff] at hi
    rcases hi with hiEq | hiOld
    · apply ZFSet.mem_union.mpr
      right
      apply mem_textbookERowDomainZF_iff.mpr
      exact ⟨n, hn, hkeyEq.trans (by rw [hiEq])⟩
    · apply ZFSet.mem_union.mpr
      left
      exact ZFSet.mem_prod.mpr ⟨i, hiOld, n, hn, hkeyEq⟩
  · intro hkey
    rcases ZFSet.mem_union.mp hkey with hkeyOld | hkeyRow
    · rcases ZFSet.mem_prod.mp hkeyOld with
        ⟨i, hi, n, hn, hkeyEq⟩
      apply ZFSet.mem_prod.mpr
      refine ⟨i, ?_, n, hn, hkeyEq⟩
      rw [natCode_succ_eq_insert, ZFSet.mem_insert_iff]
      exact Or.inr hi
    · rcases mem_textbookERowDomainZF_iff.mp hkeyRow with
        ⟨n, hn, hkeyEq⟩
      apply ZFSet.mem_prod.mpr
      refine ⟨natCode m, ?_, n, hn, hkeyEq⟩
      rw [natCode_succ_eq_insert, ZFSet.mem_insert_iff]
      exact Or.inl rfl

/-- Passing to row `m + 1` extends the old restriction graph by exactly the
actual graph contributed by row `m`. -/
theorem predecessorRestrictionGraph_textbookE_succ
    (m : Nat) (f : ZFSet.{u} -> ZFSet.{u}) :
    predecessorRestrictionGraph
        (ZFSet.prod (natCode (m + 1)) textbookEOmegaZF) f =
      predecessorRestrictionGraph
          (ZFSet.prod (natCode m) textbookEOmegaZF) f ∪
        textbookERowRestrictionGraph m f := by
  rw [textbookEPredecessorDomain_succ,
    predecessorRestrictionGraph_union,
    textbookERowRestrictionGraph]

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookERowHistoryAlgebra


/- Source module: Solutions.Work_CUGCH_TextbookERowEntryFormula -/
section GCHSource_Work_CUGCH_TextbookERowEntryFormula
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# A uniform row-entry formula for the textbook E recursion

With fixed parameters `[a,history,m]`, input `n`, and output `entry`, the
formula in this file asserts

`entry = <<m,n>, textbookEStep(a,<m,n>,history)>`.

At this layer the step predicate is left visible.  Its exact `LCarrier`
semantics is a separate theorem; the present file proves only the exact
coordinate and Kuratowski-pair semantics needed before Replacement can be
applied over internal omega.
-/

section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Coordinates -/

/-- Rename the step layout `[a,key,history,output]` into the two-witness
context extending `[a,history,m,n,entry]`. -/
def textbookERowStepRename : Fin 4 → Fin 7 :=
  ![(0 : Fin 5).castSucc.castSucc,
    (Fin.last 5).castSucc,
    (1 : Fin 5).castSucc.castSucc,
    Fin.last 6]

theorem comp_textbookERowStepRename
    (a history m n entry key output : LCarrier.{u}) :
  (fun i => snoc (snoc ![a, history, m, n, entry] key) output
      (textbookERowStepRename i)) =
      ![a, key, history, output] := by
  funext i
  fin_cases i
  · change snoc (snoc ![a, history, m, n, entry] key) output
      ((0 : Fin 5).castSucc.castSucc) = a
    rw [snoc_castSucc, snoc_castSucc]
    rfl
  · change snoc (snoc ![a, history, m, n, entry] key) output
      ((Fin.last 5).castSucc) = key
    rw [snoc_castSucc, snoc_last]
  · change snoc (snoc ![a, history, m, n, entry] key) output
      ((1 : Fin 5).castSucc.castSucc) = history
    rw [snoc_castSucc, snoc_castSucc]
    rfl
  · change snoc (snoc ![a, history, m, n, entry] key) output
      (Fin.last 6) = output
    rw [snoc_last]

/-- In the seven-variable witness context, `key = <m,n>`. -/
def textbookERowKeyPairDelta : Delta0Formula 7 :=
  Delta0Formula.kuratowskiPairEqAt
    (Fin.last 5).castSucc
    (2 : Fin 5).castSucc.castSucc
    (3 : Fin 5).castSucc.castSucc

/-- In the same context, `entry = <key,output>`. -/
def textbookERowEntryPairDelta : Delta0Formula 7 :=
  Delta0Formula.kuratowskiPairEqAt
    (4 : Fin 5).castSucc.castSucc
    (Fin.last 5).castSucc
    (Fin.last 6)

@[simp]
theorem satisfies_textbookERowKeyPairDelta
    (a history m n entry key output : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookERowKeyPairDelta.toFO
        (snoc (snoc ![a, history, m, n, entry] key) output) ↔
      key.1 = ZFSet.pair m.1 n.1 := by
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    textbookERowKeyPairDelta,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  change key.1 = ZFSet.pair m.1 n.1 ↔ _
  rfl

@[simp]
theorem satisfies_textbookERowEntryPairDelta
    (a history m n entry key output : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookERowEntryPairDelta.toFO
        (snoc (snoc ![a, history, m, n, entry] key) output) ↔
      entry.1 = ZFSet.pair key.1 output.1 := by
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    textbookERowEntryPairDelta,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  change entry.1 = ZFSet.pair key.1 output.1 ↔ _
  rfl

/-! ## The row-entry formula -/

/-- Layout `[a,history,m,n,entry]`.  The two witnesses are the key and its
step value. -/
def textbookERowEntryFormula : FOFormula 5 :=
  .ex (.ex
    (.conj textbookERowKeyPairDelta.toFO
      (.conj
        (FOFormula.rename textbookERowStepRename
          TextbookEFormula.textbookEStepFormula)
        textbookERowEntryPairDelta.toFO)))

@[simp]
theorem satisfies_textbookERowEntryFormula
    (a history m n entry : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookERowEntryFormula
        ![a, history, m, n, entry] ↔
      ∃ key output : LCarrier.{u},
        key.1 = ZFSet.pair m.1 n.1 ∧
          FOFormula.Satisfies LMem
            TextbookEFormula.textbookEStepFormula
            ![a, key, history, output] ∧
          entry.1 = ZFSet.pair key.1 output.1 := by
  simp only [textbookERowEntryFormula, FOFormula.Satisfies]
  apply exists_congr
  intro key
  apply exists_congr
  intro output
  rw [satisfies_textbookERowKeyPairDelta,
    FOFormula.satisfies_rename,
    comp_textbookERowStepRename,
    satisfies_textbookERowEntryPairDelta]

/-- A unique step output yields a unique row entry.  This is the exact
functionality adapter needed by Replacement over internal omega. -/
theorem existsUnique_textbookERowEntryFormula_of_step
    (a history m n : LCarrier.{u})
    (hstep : ExistsUnique fun output : LCarrier.{u} =>
      FOFormula.Satisfies LMem
        TextbookEFormula.textbookEStepFormula
        ![a, orderedPairLCarrier m n, history, output]) :
    ExistsUnique fun entry : LCarrier.{u} =>
      FOFormula.Satisfies LMem textbookERowEntryFormula
        ![a, history, m, n, entry] := by
  rcases hstep with ⟨output, houtput, houtputUnique⟩
  let key : LCarrier.{u} := orderedPairLCarrier m n
  let entry : LCarrier.{u} := orderedPairLCarrier key output
  refine ⟨entry, ?_, ?_⟩
  · apply (satisfies_textbookERowEntryFormula
      a history m n entry).mpr
    exact ⟨key, output, rfl, houtput, rfl⟩
  · intro other hother
    rcases (satisfies_textbookERowEntryFormula
        a history m n other).mp hother with
      ⟨otherKey, otherOutput, hkey, hotherOutput, hentry⟩
    have hkeyEq : otherKey = key := by
      apply Subtype.ext
      exact hkey
    have houtputEq : otherOutput = output := by
      apply houtputUnique otherOutput
      simpa only [key, hkeyEq] using hotherOutput
    apply Subtype.ext
    rw [hentry, hkeyEq, houtputEq]
    rfl

/-- If the step formula is functional at every internal natural input,
Replacement collects the complete row of history entries as one actual
member of `L`.  The row elements are entries themselves, not pairs of the
form `<n,entry>`. -/
theorem exists_textbookERowEntryFamily
    (a history m : LCarrier.{u})
    (hstep : ∀ n : LCarrier.{u}, n.1 ∈ omegaLCarrier.1 →
      ExistsUnique fun output : LCarrier.{u} =>
        FOFormula.Satisfies LMem
          TextbookEFormula.textbookEStepFormula
          ![a, orderedPairLCarrier m n, history, output]) :
    ∃ row : LCarrier.{u}, ∀ entry : LCarrier.{u},
      entry.1 ∈ row.1 ↔
        ∃ n : LCarrier.{u}, n.1 ∈ omegaLCarrier.1 ∧
          FOFormula.Satisfies LMem textbookERowEntryFormula
            ![a, history, m, n, entry] := by
  have hfun : ∀ n : LCarrier.{u}, n.1 ∈ omegaLCarrier.1 →
      ExistsUnique fun entry : LCarrier.{u} =>
        FOFormula.Satisfies LMem textbookERowEntryFormula
          (snoc (snoc ![a, history, m] n) entry) := by
    intro n hn
    have hunique := existsUnique_textbookERowEntryFormula_of_step
      a history m n (hstep n hn)
    have hassign (entry : LCarrier.{u}) :
        snoc (snoc ![a, history, m] n) entry =
          ![a, history, m, n, entry] := by
      funext i
      fin_cases i <;> rfl
    simpa only [hassign] using hunique
  rcases exists_replacementLCarrier textbookERowEntryFormula
      ![a, history, m] omegaLCarrier hfun with
    ⟨row, hrow⟩
  refine ⟨row, ?_⟩
  intro entry
  rw [hrow]
  apply exists_congr
  intro n
  apply and_congr_right
  intro _hn
  have hassign : snoc (snoc ![a, history, m] n) entry =
      ![a, history, m, n, entry] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TextbookERowEntryFormula


/- Source module: Solutions.Work_CUGCH_TextbookERowHistoryConstructible -/
section GCHSource_Work_CUGCH_TextbookERowHistoryConstructible
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Constructible row histories for the textbook E recursion

The history available before row `m` is the actual Kuratowski restriction
graph of the ambient recursive solution on `m x omega`.  This file proves,
by induction on the external natural number `m`, that this graph is an
element of `L`.

At the successor step, Replacement over the internal omega collects the
actual entries of the next row.  The recursion equation and the exact
predecessor-set computation identify that row with the corresponding
restriction of `textbookEByKey`.  Thus no external function graph is used
as an internal history witness.
-/

section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

 theorem natCode_mem_textbookEOmega_rowHistory (m : Nat) :
    (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF := by
  exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
    (natCode m)).mpr ⟨m, rfl⟩

/-- On a key in row `m`, the ambient recursion equation uses exactly the
history restricted to `m x omega`. -/
 theorem textbookEByKey_eq_step_rowHistory
    (a : ZFSet.{u}) (m : Nat) {n : ZFSet.{u}}
    (hn : n ∈ textbookEOmegaZF) :
    textbookEByKey a (ZFSet.pair (natCode m) n) =
      textbookEStep a (ZFSet.pair (natCode m) n)
        (predecessorRestrictionGraph
          (ZFSet.prod (natCode m) textbookEOmegaZF)
          (textbookEByKey a)) := by
  have hm : (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
    natCode_mem_textbookEOmega_rowHistory m
  have hkey :
      ZFSet.pair (natCode m : ZFSet.{u}) n ∈ TextbookEDomain :=
    (pair_mem_textbookEDomain_iff (natCode m) n).mpr ⟨hm, hn⟩
  have hpredecessors :
      ZFSet.prod (natCode m : ZFSet.{u}) textbookEOmegaZF =
        displayedPredecessors TextbookEDomain TextbookERelation
          textbookERelation_isWellFoundedSetLikeOn.2.2
          (ZFSet.pair (natCode m) n) :=
    eq_displayedPredecessors_of_isPredecessorSet
      textbookERelation_isWellFoundedSetLikeOn.2.2 hkey
      (textbookE_predecessorSet hm hn)
  rw [textbookEByKey_eq a hkey, ← hpredecessors]

namespace Model

local notation "LMem" => lCarrierMem

/-- The complete history before any standard row is an actual element of
`L`.  Its elements are precisely the Kuratowski graph pairs of
`textbookEByKey` whose first coordinate is below `m`. -/
theorem textbookEPredecessorRestrictionGraph_mem_L
    (a : LCarrier.{u}) (m : Nat) :
    predecessorRestrictionGraph
        (ZFSet.prod (natCode m) textbookEOmegaZF)
        (textbookEByKey a.1) ∈ L := by
  induction m with
  | zero =>
      rw [predecessorRestrictionGraph_textbookE_zero]
      exact empty_mem_L
  | succ m ih =>
      let historyZF : ZFSet.{u} :=
        predecessorRestrictionGraph
          (ZFSet.prod (natCode m) textbookEOmegaZF)
          (textbookEByKey a.1)
      let history : LCarrier.{u} := ⟨historyZF, ih⟩
      let mL : LCarrier.{u} := ⟨natCode m, natCode_mem_L m⟩
      have hstep :
          ∀ n : LCarrier.{u}, n.1 ∈ omegaLCarrier.1 →
            ExistsUnique fun output : LCarrier.{u} =>
              FOFormula.Satisfies LMem
                TextbookEFormula.textbookEStepFormula
                ![a, orderedPairLCarrier mL n, history, output] := by
        intro n hn
        have hmOmega :
            (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
          natCode_mem_textbookEOmega_rowHistory m
        have hkeyDomain :
            (orderedPairLCarrier mL n).1 ∈ TextbookEDomain := by
          apply (pair_mem_textbookEDomain_iff (natCode m) n.1).mpr
          exact ⟨hmOmega, hn⟩
        let output : LCarrier.{u} :=
          textbookEStepLCarrier a (orderedPairLCarrier mL n)
            history hkeyDomain
        refine ⟨output, ?_, ?_⟩
        · apply (satisfies_textbookEStepFormula_lCarrier_iff
            a (orderedPairLCarrier mL n) history output).mpr
          exact ⟨hkeyDomain, rfl⟩
        · intro other hother
          have hotherSem :=
            (satisfies_textbookEStepFormula_lCarrier_iff
              a (orderedPairLCarrier mL n) history other).mp hother
          apply Subtype.ext
          simpa only [output, textbookEStepLCarrier_val] using hotherSem.2
      rcases exists_textbookERowEntryFamily a history mL hstep with
        ⟨row, hrow⟩
      have hrowEq :
          row.1 =
            textbookERowRestrictionGraph m (textbookEByKey a.1) := by
        apply ZFSet.ext
        intro pair
        constructor
        · intro hpair
          let entry : LCarrier.{u} :=
            ⟨pair, mem_L_of_mem hpair row.2⟩
          rcases (hrow entry).mp hpair with
            ⟨n, hnOmega, hentryFormula⟩
          rcases (satisfies_textbookERowEntryFormula
              a history mL n entry).mp hentryFormula with
            ⟨key, output, hkey, houtputFormula, hentry⟩
          have houtput :=
            (satisfies_textbookEStepFormula_lCarrier_iff
              a key history output).mp houtputFormula
          have hrecursion :=
            textbookEByKey_eq_step_rowHistory a.1 m hnOmega
          have houtputEq :
              output.1 =
                textbookEByKey a.1
                  (ZFSet.pair (natCode m) n.1) := by
            calc
              output.1 =
                  textbookEStep a.1 key.1 history.1 :=
                houtput.2
              _ = textbookEStep a.1
                    (ZFSet.pair (natCode m) n.1)
                    (predecessorRestrictionGraph
                      (ZFSet.prod (natCode m) textbookEOmegaZF)
                      (textbookEByKey a.1)) := by
                  rw [hkey]
              _ = textbookEByKey a.1
                    (ZFSet.pair (natCode m) n.1) :=
                hrecursion.symm
          apply mem_textbookERowRestrictionGraph_iff.mpr
          refine ⟨n.1, hnOmega, ?_⟩
          simpa only [hkey, houtputEq] using hentry.symm
        · intro hpair
          rcases mem_textbookERowRestrictionGraph_iff.mp hpair with
            ⟨n, hnOmega, hpair⟩
          have hnL : n ∈ L :=
            mem_L_of_mem hnOmega omegaLCarrier.2
          let nL : LCarrier.{u} := ⟨n, hnL⟩
          have hmOmega :
              (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
            natCode_mem_textbookEOmega_rowHistory m
          have hkeyDomain :
              (orderedPairLCarrier mL nL).1 ∈ TextbookEDomain := by
            apply (pair_mem_textbookEDomain_iff (natCode m) n).mpr
            exact ⟨hmOmega, hnOmega⟩
          let output : LCarrier.{u} :=
            textbookEStepLCarrier a (orderedPairLCarrier mL nL)
              history hkeyDomain
          let entry : LCarrier.{u} :=
            orderedPairLCarrier (orderedPairLCarrier mL nL) output
          have houtputFormula :
              FOFormula.Satisfies LMem
                TextbookEFormula.textbookEStepFormula
                ![a, orderedPairLCarrier mL nL, history, output] := by
            apply (satisfies_textbookEStepFormula_lCarrier_iff
              a (orderedPairLCarrier mL nL) history output).mpr
            exact ⟨hkeyDomain, rfl⟩
          have hentryFormula :
              FOFormula.Satisfies LMem textbookERowEntryFormula
                ![a, history, mL, nL, entry] := by
            apply (satisfies_textbookERowEntryFormula
              a history mL nL entry).mpr
            exact ⟨orderedPairLCarrier mL nL, output, rfl,
              houtputFormula, rfl⟩
          have hentryMem : entry.1 ∈ row.1 :=
            (hrow entry).mpr ⟨nL, hnOmega, hentryFormula⟩
          have hrecursion :=
            textbookEByKey_eq_step_rowHistory a.1 m hnOmega
          have hentryEq :
              entry.1 =
                ZFSet.pair
                  (ZFSet.pair (natCode m) n)
                  (textbookEByKey a.1
                    (ZFSet.pair (natCode m) n)) := by
            change
              ZFSet.pair (ZFSet.pair (natCode m) n)
                  (textbookEStep a.1
                    (ZFSet.pair (natCode m) n) history.1) =
                ZFSet.pair (ZFSet.pair (natCode m) n)
                  (textbookEByKey a.1
                    (ZFSet.pair (natCode m) n))
            rw [show history.1 =
                predecessorRestrictionGraph
                  (ZFSet.prod (natCode m) textbookEOmegaZF)
                  (textbookEByKey a.1) by rfl,
              ← hrecursion]
          rw [← hpair]
          simpa only [hentryEq] using hentryMem
      rw [predecessorRestrictionGraph_textbookE_succ, ← hrowEq]
      exact union_mem_L ih row.2

end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookERowHistoryConstructible


/- Source module: Solutions.Work_CUGCH_TextbookELocalGraphConstructible -/
section GCHSource_Work_CUGCH_TextbookELocalGraphConstructible
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Constructible local graphs for the textbook E recursion

The local graph at `<m,n>` is the restriction of `textbookEByKey` to the
literal textbook local domain `{<m,n>} union (m x omega)`.  This file proves
that the whole graph is an actual element of `L`.
-/

section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-- Restriction to a one-point domain is the corresponding one-point graph. -/
theorem predecessorRestrictionGraph_singleton
    (x : ZFSet.{u}) (f : ZFSet.{u} -> ZFSet.{u}) :
    predecessorRestrictionGraph ({x} : ZFSet.{u}) f =
      ({ZFSet.pair x (f x)} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro pair
  constructor
  · intro hpair
    rcases mem_predecessorRestrictionGraph_iff.mp hpair with
      ⟨source, hsource, hsourcePair⟩
    have hsourceEq : source = x := by
      simpa only [ZFSet.mem_singleton] using hsource
    subst source
    rw [ZFSet.mem_singleton]
    exact hsourcePair.symm
  · intro hpair
    have hpairEq : pair = ZFSet.pair x (f x) := by
      simpa only [ZFSet.mem_singleton] using hpair
    apply mem_predecessorRestrictionGraph_iff.mpr
    exact ⟨x, by simp, hpairEq.symm⟩

namespace Model

/-- The literal restriction graph on the local domain of a standard key is
an actual member of `L`. -/
theorem textbookELocalRestrictionGraph_mem_L
    (a : LCarrier.{u}) (m n : Nat) :
    predecessorRestrictionGraph
        (textbookELocalDomainLCarrier m n).1
        (textbookEByKey a.1) ∈ L := by
  have hm : (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 m)
  have hn : (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n)
  have hdomain := textbookE_localRecursionDomain_eq
    (m := (natCode m : ZFSet.{u}))
    (n := (natCode n : ZFSet.{u})) hm hn
  have hhistory := textbookEPredecessorRestrictionGraph_mem_L a m
  have hkeyL : ZFSet.pair (natCode m) (natCode n) ∈ L :=
    orderedPair_mem_L (natCode_mem_L m) (natCode_mem_L n)
  have hvalueL :
      textbookEByKey a.1 (ZFSet.pair (natCode m) (natCode n)) ∈ L := by
    simpa only [textbookEZF] using
      (textbookEZF_natCode_mem_L a.2 n m)
  have hentryL :
      ZFSet.pair
          (ZFSet.pair (natCode m) (natCode n))
          (textbookEByKey a.1
            (ZFSet.pair (natCode m) (natCode n))) ∈ L :=
    orderedPair_mem_L hkeyL hvalueL
  rw [textbookELocalDomainLCarrier_val, hdomain, ZFSet.insert_eq,
    predecessorRestrictionGraph_union,
    predecessorRestrictionGraph_singleton]
  exact union_mem_L (singleton_mem_L hentryL) hhistory

/-- The canonical local graph, packaged as an actual `LCarrier`. -/
def textbookELocalGraphLCarrier
    (a : LCarrier.{u}) (m n : Nat) : LCarrier.{u} :=
  ⟨predecessorRestrictionGraph
      (textbookELocalDomainLCarrier m n).1
      (textbookEByKey a.1),
    textbookELocalRestrictionGraph_mem_L a m n⟩

@[simp]
theorem textbookELocalGraphLCarrier_val
    (a : LCarrier.{u}) (m n : Nat) :
    (textbookELocalGraphLCarrier a m n).1 =
      predecessorRestrictionGraph
        (textbookELocalDomainLCarrier m n).1
        (textbookEByKey a.1) :=
  rfl

end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookELocalGraphConstructible


