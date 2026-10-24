-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library14
-- name    : CH_ConstructibleAC_Library14
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T01:38:49.536853+00:00
-- url     : https://prove2.me/theorems/116a750e-5212-4a8f-874c-799a62ad1436
-- title:
--   Coherent recursion of constructible well-orders
-- statement:
--   Compatible well-order graphs on earlier stages have a coherent union at a limit, and the successor construction extends the preceding order. This library supplies the stage-state uniqueness and recursion data and the constructor proofs needed to build coherent histories of these graphs. The resulting history data assigns a constructible internal well-order graph to each constructible stage; the separate choice proof consumes that data.
--
--   The original formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). The Prove2Me packaging preserves the original copyright notices. This module includes supporting proofs needed by its definitions and constructor data.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageStateUniqueness.lean#L1-L564; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageHistoryRecursion.lean#L1-L409; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CoherentLimitOrder.lean#L1-L322; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageZeroInternalOrder.lean#L1-L36; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CoherentStageGraphExtension.lean#L1-L304; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageHistoryCoherence.lean#L1-L139; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageHistoryGraphSystem.lean#L1-L178

import Definitions.Def_CH_ConstructibleAC_Library13
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

/-!
# Adaptation of Zike Liu's constructible-universe Choice proof

Original formalization: Copyright (c) 2026 Zike Liu, Apache-2.0.
Source: https://github.com/05-02-07/lean-constructible-universe
Commit: 7f5a7d03d63d9769172f17350bbe8303996e5b53.
All original per-file copyright notices are retained below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

This credit concerns the Prove2Me adaptation and semantic bridge. The original
well-ordering formalization is by Zike Liu, credited above and in each source section.
-/

set_option autoImplicit false


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageStateUniqueness -/
section CUAdapterModule92
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Uniqueness of ordinal-indexed stage states

The local history rule is deterministic on canonical ordinal indices.  This
file first normalizes the zero, successor, and limit cases, then uses ordinal
induction to compare states coming from different valid internal histories.
-/


universe u

namespace Constructible.Model

noncomputable section

/-- The empty carrier cannot be a von Neumann successor. -/
 theorem emptyLCarrier_ne_insert_self (predecessor : LCarrier.{u}) :
    ¬emptyLCarrier.1 = insert predecessor.1 predecessor.1 := by
  intro h
  have hmem : predecessor.1 ∈ emptyLCarrier.1 := by
    rw [h]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  exact not_mem_emptyLCarrier predecessor hmem

/-- A valid history through a later ordinal remains valid through every
earlier ordinal. -/
theorem ValidStageHistory.restrictOrdinal
    {history : LCarrier.{u}} {alpha beta : Ordinal.{u}}
    (hvalid : ValidStageHistory history (ordinalLCarrier beta))
    (halpha : alpha ≤ beta) :
    ValidStageHistory history (ordinalLCarrier alpha) := by
  intro index hindex
  apply hvalid index
  rcases hindex with hindex | rfl
  · left
    exact Ordinal.toZFSet_monotone halpha hindex
  · rcases halpha.eq_or_lt with rfl | halpha
    · exact Or.inr rfl
    · exact Or.inl
        ((ordinalLCarrier_mem_ordinalLCarrier_iff beta alpha).mpr halpha)

/-- An entry in a valid history gives a `StageStateAt` witness at every
canonical earlier bound. -/
theorem stageStateAt_of_validHistory
    {history index stage relation : LCarrier.{u}}
    {alpha beta : Ordinal.{u}}
    (hindex : index = ordinalLCarrier alpha)
    (halpha : alpha ≤ beta)
    (hvalid : ValidStageHistory history (ordinalLCarrier beta))
    (hentry : HistoryEntry history index stage relation) :
    StageStateAt index stage relation := by
  subst index
  exact ⟨history, hvalid.restrictOrdinal halpha, hentry⟩

/-- At its bound, validity transfers the local rule to any entry there. -/
theorem ValidStageHistory.localState_of_entry
    {history bound stage relation : LCarrier.{u}}
    (hvalid : ValidStageHistory history bound)
    (hentry : HistoryEntry history bound stage relation) :
    HistoryLocalState history bound stage relation := by
  rcases hvalid bound (Or.inr rfl) with
    ⟨chosenStage, chosenRelation, _hchosen, hunique, hlocal⟩
  have hcoordinates := hunique stage relation hentry
  simpa only [hcoordinates.1, hcoordinates.2] using hlocal

/-- The zero-index local rule has exactly the empty stage and empty graph. -/
theorem historyLocalState_zero_iff
    (history stage relation : LCarrier.{u}) :
    HistoryLocalState history (ordinalLCarrier 0) stage relation ↔
      stage = emptyLCarrier ∧ relation = emptyLCarrier := by
  rw [ordinalLCarrier_zero]
  constructor
  · rintro (hbase | hsuccessor | hlimit)
    · exact ⟨hbase.2.1, hbase.2.2⟩
    · rcases hsuccessor with
        ⟨predecessorIndex, _predecessorStage, _predecessorRelation,
          hpredecessor, _⟩
      exact (emptyLCarrier_ne_insert_self predecessorIndex hpredecessor).elim
    · exact (hlimit.1.1 rfl).elim
  · rintro ⟨rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl, rfl⟩

/-- At a canonical successor index, only the successor branch of the local
rule is possible, and its predecessor index is canonical. -/
theorem historyLocalState_successor_iff
    (history : LCarrier.{u}) (alpha : Ordinal.{u})
    (stage relation : LCarrier.{u}) :
    HistoryLocalState history (ordinalLCarrier (Order.succ alpha))
        stage relation ↔
      ∃ predecessorStage predecessorRelation : LCarrier.{u},
        HistoryEntry history (ordinalLCarrier alpha)
          predecessorStage predecessorRelation ∧
        stage.1 = Godel.godelDef predecessorStage.1 ∧
        relation = canonicalSuccessorStateRelation
          predecessorStage predecessorRelation stage := by
  constructor
  · rintro (hbase | hsuccessor | hlimit)
    · have hcodes :
          ordinalLCarrier (Order.succ alpha) = ordinalLCarrier 0 :=
        hbase.1.trans ordinalLCarrier_zero.symm
      have hordinal : Order.succ alpha = 0 :=
        ordinalLCarrier_injective hcodes
      exact (Order.succ_ne_bot alpha hordinal).elim
    · rcases hsuccessor with
        ⟨predecessorIndex, predecessorStage, predecessorRelation,
          hpredecessor, hentry, hstage, hrelation⟩
      have hindex :=
        (ordinalLCarrier_successor_predecessor_iff
          alpha predecessorIndex).mp hpredecessor
      subst predecessorIndex
      exact ⟨predecessorStage, predecessorRelation,
        hentry, hstage, hrelation⟩
    · have hpredecessor :
          ∃ predecessor : LCarrier.{u},
            (ordinalLCarrier (Order.succ alpha)).1 =
              insert predecessor.1 predecessor.1 :=
        ⟨ordinalLCarrier alpha, ordinalLCarrier_succ_val alpha⟩
      exact (hlimit.1.2 hpredecessor).elim
  · rintro ⟨predecessorStage, predecessorRelation,
      hentry, hstage, hrelation⟩
    exact Or.inr (Or.inl
      ⟨ordinalLCarrier alpha, predecessorStage, predecessorRelation,
        ordinalLCarrier_succ_val alpha, hentry, hstage, hrelation⟩)

/-- At a nonzero limit ordinal, only the two union clauses remain. -/
theorem historyLocalState_limit_iff
    (history : LCarrier.{u}) {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit) (stage relation : LCarrier.{u}) :
    HistoryLocalState history (ordinalLCarrier limit) stage relation ↔
      HistoryLimitState history (ordinalLCarrier limit) stage relation := by
  constructor
  · rintro (hbase | hsuccessor | hlimit)
    · have hcodes : ordinalLCarrier limit = ordinalLCarrier 0 :=
        hbase.1.trans ordinalLCarrier_zero.symm
      have hordinal : limit = 0 := ordinalLCarrier_injective hcodes
      exact (hl.ne_bot hordinal).elim
    · rcases hsuccessor with
        ⟨predecessorIndex, _predecessorStage, _predecessorRelation,
          hpredecessor, _⟩
      exact (ordinalLCarrier_limit_no_predecessor hl
        ⟨predecessorIndex, hpredecessor⟩).elim
    · exact hlimit.2
  · intro hlimit
    refine Or.inr (Or.inr ⟨?_, hlimit⟩)
    constructor
    · intro hzero
      have hcodes : ordinalLCarrier limit = ordinalLCarrier 0 :=
        hzero.trans ordinalLCarrier_zero.symm
      exact hl.ne_bot (ordinalLCarrier_injective hcodes)
    · exact ordinalLCarrier_limit_no_predecessor hl

/-- States at a canonical ordinal index are independent of the valid
internal history used to witness them. -/
theorem stageStateAt_ordinal_outputs_unique (ordinal : Ordinal.{u}) :
    ∀ {stage relation otherStage otherRelation : LCarrier.{u}},
      StageStateAt (ordinalLCarrier ordinal) stage relation →
      StageStateAt (ordinalLCarrier ordinal) otherStage otherRelation →
      stage = otherStage ∧ relation = otherRelation := by
  induction ordinal using Ordinal.limitRecOn with
  | zero =>
      intro stage relation otherStage otherRelation hstate hother
      rcases hstate with ⟨history, hvalid, hentry⟩
      rcases hother with ⟨otherHistory, hotherValid, hotherEntry⟩
      have hlocal := hvalid.localState_of_entry hentry
      have hotherLocal := hotherValid.localState_of_entry hotherEntry
      have houtputs :=
        (historyLocalState_zero_iff history stage relation).mp hlocal
      have hotherOutputs :=
        (historyLocalState_zero_iff
          otherHistory otherStage otherRelation).mp hotherLocal
      exact
        ⟨houtputs.1.trans hotherOutputs.1.symm,
          houtputs.2.trans hotherOutputs.2.symm⟩
  | add_one alpha ih =>
      rw [← Order.succ_eq_add_one]
      intro stage relation otherStage otherRelation hstate hother
      rcases hstate with ⟨history, hvalid, hentry⟩
      rcases hother with ⟨otherHistory, hotherValid, hotherEntry⟩
      have hlocal := hvalid.localState_of_entry hentry
      have hotherLocal := hotherValid.localState_of_entry hotherEntry
      rcases (historyLocalState_successor_iff
          history alpha stage relation).mp hlocal with
        ⟨predecessorStage, predecessorRelation, predecessorEntry,
          hstage, hrelation⟩
      rcases (historyLocalState_successor_iff
          otherHistory alpha otherStage otherRelation).mp hotherLocal with
        ⟨otherPredecessorStage, otherPredecessorRelation,
          otherPredecessorEntry, hotherStage, hotherRelation⟩
      have hpredecessorState :
          StageStateAt (ordinalLCarrier alpha)
            predecessorStage predecessorRelation :=
        stageStateAt_of_validHistory rfl (Order.le_succ alpha)
          hvalid predecessorEntry
      have hotherPredecessorState :
          StageStateAt (ordinalLCarrier alpha)
            otherPredecessorStage otherPredecessorRelation :=
        stageStateAt_of_validHistory rfl (Order.le_succ alpha)
          hotherValid otherPredecessorEntry
      have hpredecessor := ih hpredecessorState hotherPredecessorState
      have hstageEq : stage = otherStage := by
        apply Subtype.ext
        calc
          stage.1 = Godel.godelDef predecessorStage.1 := hstage
          _ = Godel.godelDef otherPredecessorStage.1 := by
            rw [hpredecessor.1]
          _ = otherStage.1 := hotherStage.symm
      have hrelationEq : relation = otherRelation := by
        calc
          relation = canonicalSuccessorStateRelation
              predecessorStage predecessorRelation stage := hrelation
          _ = canonicalSuccessorStateRelation
              otherPredecessorStage otherPredecessorRelation
                otherStage := by
            rw [hpredecessor.1, hpredecessor.2, hstageEq]
          _ = otherRelation := hotherRelation.symm
      exact ⟨hstageEq, hrelationEq⟩
  | limit limit hl ih =>
      intro stage relation otherStage otherRelation hstate hother
      rcases hstate with ⟨history, hvalid, hentry⟩
      rcases hother with ⟨otherHistory, hotherValid, hotherEntry⟩
      have hlocal := hvalid.localState_of_entry hentry
      have hotherLocal := hotherValid.localState_of_entry hotherEntry
      have hlimit :=
        (historyLocalState_limit_iff history hl stage relation).mp hlocal
      have hotherLimit :=
        (historyLocalState_limit_iff
          otherHistory hl otherStage otherRelation).mp hotherLocal
      have hstageEq : stage = otherStage := by
        apply lCarrier_extensionality
        intro z
        constructor
        · intro hz
          rcases (hlimit.1 z).mp hz with
            ⟨earlierIndex, hindex, earlierStage, earlierRelation,
              hearlierEntry, hzEarlier⟩
          rcases exists_eq_ordinalLCarrier_of_mem hindex with
            ⟨earlierOrdinal, hearlierOrdinal, rfl⟩
          rcases hotherValid (ordinalLCarrier earlierOrdinal)
              (Or.inl hindex) with
            ⟨targetStage, targetRelation, htargetEntry,
              _htargetUnique, _htargetLocal⟩
          have hearlierState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                earlierStage earlierRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hvalid hearlierEntry
          have htargetState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                targetStage targetRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hotherValid htargetEntry
          have houtputs :=
            ih earlierOrdinal hearlierOrdinal hearlierState htargetState
          apply (hotherLimit.1 z).mpr
          refine ⟨ordinalLCarrier earlierOrdinal, hindex,
            targetStage, targetRelation, htargetEntry, ?_⟩
          simpa only [houtputs.1] using hzEarlier
        · intro hz
          rcases (hotherLimit.1 z).mp hz with
            ⟨earlierIndex, hindex, earlierStage, earlierRelation,
              hearlierEntry, hzEarlier⟩
          rcases exists_eq_ordinalLCarrier_of_mem hindex with
            ⟨earlierOrdinal, hearlierOrdinal, rfl⟩
          rcases hvalid (ordinalLCarrier earlierOrdinal)
              (Or.inl hindex) with
            ⟨targetStage, targetRelation, htargetEntry,
              _htargetUnique, _htargetLocal⟩
          have hearlierState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                earlierStage earlierRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hotherValid hearlierEntry
          have htargetState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                targetStage targetRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hvalid htargetEntry
          have houtputs :=
            ih earlierOrdinal hearlierOrdinal hearlierState htargetState
          apply (hlimit.1 z).mpr
          refine ⟨ordinalLCarrier earlierOrdinal, hindex,
            targetStage, targetRelation, htargetEntry, ?_⟩
          simpa only [houtputs.1] using hzEarlier
      have hrelationEq : relation = otherRelation := by
        apply lCarrier_extensionality
        intro z
        constructor
        · intro hz
          rcases (hlimit.2 z).mp hz with
            ⟨earlierIndex, hindex, earlierStage, earlierRelation,
              hearlierEntry, hzEarlier⟩
          rcases exists_eq_ordinalLCarrier_of_mem hindex with
            ⟨earlierOrdinal, hearlierOrdinal, rfl⟩
          rcases hotherValid (ordinalLCarrier earlierOrdinal)
              (Or.inl hindex) with
            ⟨targetStage, targetRelation, htargetEntry,
              _htargetUnique, _htargetLocal⟩
          have hearlierState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                earlierStage earlierRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hvalid hearlierEntry
          have htargetState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                targetStage targetRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hotherValid htargetEntry
          have houtputs :=
            ih earlierOrdinal hearlierOrdinal hearlierState htargetState
          apply (hotherLimit.2 z).mpr
          refine ⟨ordinalLCarrier earlierOrdinal, hindex,
            targetStage, targetRelation, htargetEntry, ?_⟩
          simpa only [houtputs.2] using hzEarlier
        · intro hz
          rcases (hotherLimit.2 z).mp hz with
            ⟨earlierIndex, hindex, earlierStage, earlierRelation,
              hearlierEntry, hzEarlier⟩
          rcases exists_eq_ordinalLCarrier_of_mem hindex with
            ⟨earlierOrdinal, hearlierOrdinal, rfl⟩
          rcases hvalid (ordinalLCarrier earlierOrdinal)
              (Or.inl hindex) with
            ⟨targetStage, targetRelation, htargetEntry,
              _htargetUnique, _htargetLocal⟩
          have hearlierState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                earlierStage earlierRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hotherValid hearlierEntry
          have htargetState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                targetStage targetRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hvalid htargetEntry
          have houtputs :=
            ih earlierOrdinal hearlierOrdinal hearlierState htargetState
          apply (hlimit.2 z).mpr
          refine ⟨ordinalLCarrier earlierOrdinal, hindex,
            targetStage, targetRelation, htargetEntry, ?_⟩
          simpa only [houtputs.2] using hzEarlier
      exact ⟨hstageEq, hrelationEq⟩

/-- Pair-valued form of ordinal state uniqueness, used by Replacement. -/
theorem stageStateAt_ordinal_pair_unique
    (ordinal : Ordinal.{u})
    {output other : LCarrier.{u} × LCarrier.{u}}
    (houtput : StageStateAt (ordinalLCarrier ordinal)
      output.1 output.2)
    (hother : StageStateAt (ordinalLCarrier ordinal)
      other.1 other.2) :
    other = output := by
  have hcoordinates :=
    stageStateAt_ordinal_outputs_unique ordinal hother houtput
  exact Prod.ext hcoordinates.1 hcoordinates.2

/-- Within a valid ordinal-bounded history, lookup at a canonical earlier
index is equivalent to the history-independent `StageStateAt` predicate. -/
theorem historyEntry_iff_stageStateAt_of_validOrdinal
    {history : LCarrier.{u}} {alpha beta : Ordinal.{u}}
    (hvalid : ValidStageHistory history (ordinalLCarrier beta))
    (halpha : alpha ≤ beta) (stage relation : LCarrier.{u}) :
    HistoryEntry history (ordinalLCarrier alpha) stage relation ↔
      StageStateAt (ordinalLCarrier alpha) stage relation := by
  constructor
  · intro hentry
    exact stageStateAt_of_validHistory rfl halpha hvalid hentry
  · intro hstate
    have hbound :
        (ordinalLCarrier alpha).1 ∈ (ordinalLCarrier beta).1 ∨
          ordinalLCarrier alpha = ordinalLCarrier beta := by
      rcases halpha.eq_or_lt with rfl | halpha
      · exact Or.inr rfl
      · exact Or.inl
          ((ordinalLCarrier_mem_ordinalLCarrier_iff beta alpha).mpr halpha)
    rcases hvalid (ordinalLCarrier alpha) hbound with
      ⟨chosenStage, chosenRelation, hchosenEntry,
        _hchosenUnique, _hchosenLocal⟩
    have hchosenState :
        StageStateAt (ordinalLCarrier alpha)
          chosenStage chosenRelation :=
      stageStateAt_of_validHistory rfl halpha hvalid hchosenEntry
    have houtputs :=
      stageStateAt_ordinal_outputs_unique alpha hstate hchosenState
    simpa only [houtputs.1, houtputs.2] using hchosenEntry

/-- Changing a history without changing any entry below the current index
preserves the local recursion rule. -/
theorem historyLocalState_of_entriesBelow
    {first second index stage relation : LCarrier.{u}}
    (hentries : ∀ earlierIndex : LCarrier.{u},
      earlierIndex.1 ∈ index.1 →
      ∀ earlierStage earlierRelation : LCarrier.{u},
        HistoryEntry first earlierIndex earlierStage earlierRelation ↔
          HistoryEntry second earlierIndex earlierStage earlierRelation)
    (hlocal : HistoryLocalState first index stage relation) :
    HistoryLocalState second index stage relation := by
  rcases hlocal with hbase | hsuccessor | hlimit
  · exact Or.inl hbase
  · rcases hsuccessor with
      ⟨predecessorIndex, predecessorStage, predecessorRelation,
        hpredecessor, hentry, hstage, hrelation⟩
    have hpredecessorMem : predecessorIndex.1 ∈ index.1 := by
      rw [hpredecessor]
      exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
    exact Or.inr (Or.inl
      ⟨predecessorIndex, predecessorStage, predecessorRelation,
        hpredecessor,
        (hentries predecessorIndex hpredecessorMem
          predecessorStage predecessorRelation).mp hentry,
        hstage, hrelation⟩)
  · refine Or.inr (Or.inr ⟨hlimit.1, ?_⟩)
    constructor
    · intro z
      constructor
      · intro hz
        rcases (hlimit.2.1 z).mp hz with
          ⟨earlierIndex, hindex, earlierStage, earlierRelation,
            hentry, hzEarlier⟩
        exact ⟨earlierIndex, hindex, earlierStage, earlierRelation,
          (hentries earlierIndex hindex
            earlierStage earlierRelation).mp hentry,
          hzEarlier⟩
      · rintro ⟨earlierIndex, hindex, earlierStage, earlierRelation,
          hentry, hzEarlier⟩
        apply (hlimit.2.1 z).mpr
        exact ⟨earlierIndex, hindex, earlierStage, earlierRelation,
          (hentries earlierIndex hindex
            earlierStage earlierRelation).mpr hentry,
          hzEarlier⟩
    · intro z
      constructor
      · intro hz
        rcases (hlimit.2.2 z).mp hz with
          ⟨earlierIndex, hindex, earlierStage, earlierRelation,
            hentry, hzEarlier⟩
        exact ⟨earlierIndex, hindex, earlierStage, earlierRelation,
          (hentries earlierIndex hindex
            earlierStage earlierRelation).mp hentry,
          hzEarlier⟩
      · rintro ⟨earlierIndex, hindex, earlierStage, earlierRelation,
          hentry, hzEarlier⟩
        apply (hlimit.2.2 z).mpr
        exact ⟨earlierIndex, hindex, earlierStage, earlierRelation,
          (hentries earlierIndex hindex
            earlierStage earlierRelation).mpr hentry,
          hzEarlier⟩

/-- Symmetric form of history invariance below an index. -/
theorem historyLocalState_congr_entriesBelow
    {first second index stage relation : LCarrier.{u}}
    (hentries : ∀ earlierIndex : LCarrier.{u},
      earlierIndex.1 ∈ index.1 →
      ∀ earlierStage earlierRelation : LCarrier.{u},
        HistoryEntry first earlierIndex earlierStage earlierRelation ↔
          HistoryEntry second earlierIndex earlierStage earlierRelation) :
    HistoryLocalState first index stage relation ↔
      HistoryLocalState second index stage relation := by
  constructor
  · exact historyLocalState_of_entriesBelow hentries
  · apply historyLocalState_of_entriesBelow
    intro earlierIndex hindex earlierStage earlierRelation
    exact (hentries earlierIndex hindex
      earlierStage earlierRelation).symm

/-- A Replacement-generated family of all earlier states becomes a valid
history through `bound` after adjoining one locally correct top state. -/
theorem validStageHistory_addTop_of_family
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound)
    (history : LCarrier.{u})
    (hhistory : ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier bound).1 ∧
            StageEntryAt index entry)
    (topStage topRelation : LCarrier.{u})
    (htopLocal : HistoryLocalState
      (addHistoryEntry history (ordinalLCarrier bound)
        topStage topRelation)
      (ordinalLCarrier bound) topStage topRelation) :
    ValidStageHistory
      (addHistoryEntry history (ordinalLCarrier bound)
        topStage topRelation)
      (ordinalLCarrier bound) := by
  intro index hindex
  rcases hindex with hindex | rfl
  · rcases exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    rcases hstates ordinal hordinal with
      ⟨⟨stage, relation⟩, hstate, _hstateUnique⟩
    refine ⟨stage, relation, ?_, ?_, ?_⟩
    · apply (historyEntry_addTop_iff_of_stageEntryFamily
        hhistory topStage topRelation
        (ordinalLCarrier ordinal) stage relation).mpr
      exact Or.inl ⟨hindex, hstate⟩
    · intro otherStage otherRelation hotherEntry
      rcases (historyEntry_addTop_iff_of_stageEntryFamily
          hhistory topStage topRelation
          (ordinalLCarrier ordinal) otherStage otherRelation).mp
          hotherEntry with hold | htop
      · exact stageStateAt_ordinal_outputs_unique
          ordinal hold.2 hstate
      · have hordinalEq : ordinal = bound :=
          ordinalLCarrier_injective htop.1
        exact ((ne_of_lt hordinal) hordinalEq).elim
    · rcases hstate with
        ⟨witnessHistory, hwitnessValid, hwitnessEntry⟩
      have hwitnessLocal :=
        hwitnessValid.localState_of_entry hwitnessEntry
      have hagree : ∀ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ (ordinalLCarrier ordinal).1 →
          ∀ earlierStage earlierRelation : LCarrier.{u},
            HistoryEntry witnessHistory earlierIndex
                earlierStage earlierRelation ↔
              HistoryEntry
                (addHistoryEntry history (ordinalLCarrier bound)
                  topStage topRelation)
                earlierIndex earlierStage earlierRelation := by
        intro earlierIndex hearlierIndex earlierStage earlierRelation
        rcases exists_eq_ordinalLCarrier_of_mem hearlierIndex with
          ⟨earlierOrdinal, hearlierOrdinal, rfl⟩
        have hearlierBound : earlierOrdinal < bound :=
          hearlierOrdinal.trans hordinal
        have hearlierMemBound :
            (ordinalLCarrier earlierOrdinal).1 ∈
              (ordinalLCarrier bound).1 :=
          (ordinalLCarrier_mem_ordinalLCarrier_iff
            bound earlierOrdinal).mpr hearlierBound
        have hearlierNeBound :
            ordinalLCarrier earlierOrdinal ≠ ordinalLCarrier bound := by
          intro heq
          exact (ne_of_lt hearlierBound)
            (ordinalLCarrier_injective heq)
        rw [historyEntry_iff_stageStateAt_of_validOrdinal
          hwitnessValid hearlierOrdinal.le]
        rw [historyEntry_addTop_iff_of_stageEntryFamily
          hhistory]
        simp only [hearlierMemBound, true_and,
          hearlierNeBound, false_and, or_false]
      exact (historyLocalState_congr_entriesBelow hagree).mp
        hwitnessLocal
  · refine ⟨topStage, topRelation, ?_, ?_, htopLocal⟩
    · apply (historyEntry_addTop_iff_of_stageEntryFamily
        hhistory topStage topRelation
        (ordinalLCarrier bound) topStage topRelation).mpr
      exact Or.inr ⟨rfl, rfl, rfl⟩
    · intro otherStage otherRelation hotherEntry
      rcases (historyEntry_addTop_iff_of_stageEntryFamily
          hhistory topStage topRelation
          (ordinalLCarrier bound) otherStage otherRelation).mp
          hotherEntry with hold | htop
      · exact (ZFSet.mem_irrefl _ hold.1).elim
      · exact ⟨htop.2.1, htop.2.2⟩

end

end Constructible.Model
end CUAdapterModule92



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryRecursion -/
section CUAdapterModule93
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internal transfinite recursion of constructible-stage histories

At every ordinal this file constructs an actual `LCarrier` history together
with its top relation.  The history is valid through the canonical ordinal
index, and its top stage coordinate is exactly `stageLCarrier ordinal`.
-/


universe u

namespace Constructible.Model

noncomputable section

/-- The internal history and top relation constructed at one ordinal. -/
structure StageHistoryData (ordinal : Ordinal.{u}) where
  /-- The internally represented stage history. -/
  history : LCarrier.{u}
  /-- The internally represented top-stage relation. -/
  relation : LCarrier.{u}
  valid : ValidStageHistory history (ordinalLCarrier ordinal)
  topEntry : HistoryEntry history (ordinalLCarrier ordinal)
    (stageLCarrier ordinal) relation

/-- A history datum supplies the corresponding history-independent state. -/
theorem StageHistoryData.state {ordinal : Ordinal.{u}}
    (data : StageHistoryData ordinal) :
    StageStateAt (ordinalLCarrier ordinal)
      (stageLCarrier ordinal) data.relation :=
  ⟨data.history, data.valid, data.topEntry⟩

/-- The state supplied by a history datum is the unique state at its index. -/
theorem StageHistoryData.existsUniqueState {ordinal : Ordinal.{u}}
    (data : StageHistoryData ordinal) :
    ∃! output : LCarrier.{u} × LCarrier.{u},
      StageStateAt (ordinalLCarrier ordinal) output.1 output.2 := by
  refine ⟨(stageLCarrier ordinal, data.relation), data.state, ?_⟩
  intro other hother
  exact stageStateAt_ordinal_pair_unique ordinal data.state hother

/-- A datum through `alpha` supplies unique states below `alpha + 1`. -/
theorem StageHistoryData.uniqueStatesBelowSucc
    {alpha : Ordinal.{u}} (data : StageHistoryData alpha) :
    UniqueStageStatesBelow (Order.succ alpha) := by
  intro ordinal hordinal
  have hle : ordinal ≤ alpha := Order.lt_succ_iff.mp hordinal
  have hbound :
      (ordinalLCarrier ordinal).1 ∈ (ordinalLCarrier alpha).1 ∨
        ordinalLCarrier ordinal = ordinalLCarrier alpha := by
    rcases hle.eq_or_lt with rfl | hlt
    · exact Or.inr rfl
    · exact Or.inl
        ((ordinalLCarrier_mem_ordinalLCarrier_iff alpha ordinal).mpr hlt)
  rcases data.valid (ordinalLCarrier ordinal) hbound with
    ⟨stage, relation, hentry, _hunique, _hlocal⟩
  have hstate : StageStateAt (ordinalLCarrier ordinal) stage relation :=
    stageStateAt_of_validHistory rfl hle data.valid hentry
  refine ⟨(stage, relation), hstate, ?_⟩
  intro other hother
  exact stageStateAt_ordinal_pair_unique ordinal hstate hother

/-- A family of earlier history data supplies unique states below a limit. -/
theorem uniqueStageStatesBelow_of_historyData
    {bound : Ordinal.{u}}
    (data : ∀ ordinal < bound, StageHistoryData ordinal) :
    UniqueStageStatesBelow bound := by
  intro ordinal hordinal
  exact (data ordinal hordinal).existsUniqueState

@[simp]
theorem stageLCarrier_zero :
    stageLCarrier (0 : Ordinal.{u}) = emptyLCarrier := by
  apply Subtype.ext
  change LStageZF (0 : Ordinal.{u}) = (∅ : ZFSet.{u})
  exact LStageZF_zero

/-- The unique zero state, represented by a one-entry internal history. -/
def zeroStageHistoryData : StageHistoryData (0 : Ordinal.{u}) := by
  let history : LCarrier.{u} := emptyLCarrier
  let extended := addHistoryEntry history (ordinalLCarrier 0)
    (stageLCarrier 0) emptyLCarrier
  have hstates : UniqueStageStatesBelow (0 : Ordinal.{u}) := by
    intro ordinal hordinal
    exact (not_lt_of_ge bot_le hordinal).elim
  have hhistory : ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier (0 : Ordinal.{u})).1 ∧
            StageEntryAt index entry := by
    intro entry
    constructor
    · intro hentry
      exact (not_mem_emptyLCarrier entry hentry).elim
    · rintro ⟨index, hindex, _hstate⟩
      exact (not_mem_emptyLCarrier index
        (by simpa only [ordinalLCarrier_zero] using hindex)).elim
  have htopLocal : HistoryLocalState extended (ordinalLCarrier 0)
      (stageLCarrier 0) emptyLCarrier := by
    apply (historyLocalState_zero_iff
      extended (stageLCarrier 0) emptyLCarrier).mpr
    exact ⟨stageLCarrier_zero, rfl⟩
  have hvalid : ValidStageHistory extended (ordinalLCarrier 0) :=
    validStageHistory_addTop_of_family 0 hstates history hhistory
      (stageLCarrier 0) emptyLCarrier htopLocal
  have htopEntry : HistoryEntry extended (ordinalLCarrier 0)
      (stageLCarrier 0) emptyLCarrier := by
    apply (historyEntry_addTop_iff_of_stageEntryFamily
      hhistory (stageLCarrier 0) emptyLCarrier
      (ordinalLCarrier 0) (stageLCarrier 0) emptyLCarrier).mpr
    exact Or.inr ⟨rfl, rfl, rfl⟩
  exact
    { history := extended
      relation := emptyLCarrier
      valid := hvalid
      topEntry := htopEntry }

/-- The successor datum obtained from the canonical deterministic graph
extension and an internally replaced family of all previous entries. -/
def successorStageHistoryData (alpha : Ordinal.{u})
    (previous : StageHistoryData alpha) :
    StageHistoryData (alpha + 1) := by
  rw [← Order.succ_eq_add_one]
  let hstates : UniqueStageStatesBelow (Order.succ alpha) :=
    previous.uniqueStatesBelowSucc
  let history : LCarrier.{u} :=
    stageEntryFamily (Order.succ alpha) hstates
  have hhistory : ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier (Order.succ alpha)).1 ∧
            StageEntryAt index entry :=
    mem_stageEntryFamily_iff (Order.succ alpha) hstates
  let nextRelation := canonicalSuccessorRelation alpha previous.relation
  let extended := addHistoryEntry history
    (ordinalLCarrier (Order.succ alpha))
    (stageLCarrier (Order.succ alpha)) nextRelation
  have hpredecessorEntry : HistoryEntry extended
      (ordinalLCarrier alpha) (stageLCarrier alpha) previous.relation := by
    apply (historyEntry_addTop_iff_of_stageEntryFamily
      hhistory (stageLCarrier (Order.succ alpha)) nextRelation
      (ordinalLCarrier alpha) (stageLCarrier alpha)
      previous.relation).mpr
    exact Or.inl
      ⟨(ordinalLCarrier_mem_ordinalLCarrier_iff
          (Order.succ alpha) alpha).mpr (Order.lt_succ alpha),
        previous.state⟩
  have hstage : (stageLCarrier (Order.succ alpha)).1 =
      Godel.godelDef (stageLCarrier alpha).1 := by
    simp only [stageLCarrier_val, LStageZF_succ,
      Godel.DefZF_eq_godelDef (LStageZF_isTransitive alpha)]
  have htopLocal : HistoryLocalState extended
      (ordinalLCarrier (Order.succ alpha))
      (stageLCarrier (Order.succ alpha)) nextRelation := by
    apply (historyLocalState_successor_iff extended alpha
      (stageLCarrier (Order.succ alpha)) nextRelation).mpr
    refine ⟨stageLCarrier alpha, previous.relation,
      hpredecessorEntry, hstage, ?_⟩
    rfl
  have hvalid : ValidStageHistory extended
      (ordinalLCarrier (Order.succ alpha)) :=
    validStageHistory_addTop_of_family (Order.succ alpha) hstates
      history hhistory (stageLCarrier (Order.succ alpha))
      nextRelation htopLocal
  have htopEntry : HistoryEntry extended
      (ordinalLCarrier (Order.succ alpha))
      (stageLCarrier (Order.succ alpha)) nextRelation := by
    apply (historyEntry_addTop_iff_of_stageEntryFamily
      hhistory (stageLCarrier (Order.succ alpha)) nextRelation
      (ordinalLCarrier (Order.succ alpha))
      (stageLCarrier (Order.succ alpha)) nextRelation).mpr
    exact Or.inr ⟨rfl, rfl, rfl⟩
  exact
    { history := extended
      relation := nextRelation
      valid := hvalid
      topEntry := htopEntry }

@[simp]
theorem successorStageHistoryData_relation (alpha : Ordinal.{u})
    (previous : StageHistoryData alpha) :
    (successorStageHistoryData alpha previous).relation =
      canonicalSuccessorRelation alpha previous.relation := by
  rfl

/-- At a nonzero limit, Replacement internalizes both the complete earlier
entry family and the complete earlier relation family.  Their internal union
is the top relation. -/
def limitStageHistoryData {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit)
    (previous : ∀ ordinal < limit, StageHistoryData ordinal) :
    StageHistoryData limit := by
  let hstates : UniqueStageStatesBelow limit :=
    uniqueStageStatesBelow_of_historyData previous
  let history : LCarrier.{u} := stageEntryFamily limit hstates
  have hhistory : ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier limit).1 ∧
            StageEntryAt index entry :=
    mem_stageEntryFamily_iff limit hstates
  let family : LCarrier.{u} := stageRelationFamily limit hstates
  have hfamily : ∀ relation : LCarrier.{u},
      relation.1 ∈ family.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier limit).1 ∧
            StageRelationAt index relation :=
    mem_stageRelationFamily_iff limit hstates
  let topRelation := sUnionLCarrier family
  let extended := addHistoryEntry history (ordinalLCarrier limit)
    (stageLCarrier limit) topRelation
  have hstageUnion : ∀ z : LCarrier.{u},
      z.1 ∈ (stageLCarrier limit).1 ↔
        ∃ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ (ordinalLCarrier limit).1 ∧
            ∃ earlierStage earlierRelation : LCarrier.{u},
              HistoryEntry extended earlierIndex
                earlierStage earlierRelation ∧
              z.1 ∈ earlierStage.1 := by
    intro z
    constructor
    · intro hz
      have hzLimit : z.1 ∈ LStageZF limit := by
        simpa only [stageLCarrier_val] using hz
      rcases (mem_LStageZF_limit_iff hl).mp hzLimit with
        ⟨ordinal, hordinal, hzOrdinal⟩
      let data := previous ordinal hordinal
      have hindex :
          (ordinalLCarrier ordinal).1 ∈
            (ordinalLCarrier limit).1 :=
        (ordinalLCarrier_mem_ordinalLCarrier_iff
          limit ordinal).mpr hordinal
      have hentry : HistoryEntry extended (ordinalLCarrier ordinal)
          (stageLCarrier ordinal) data.relation := by
        apply (historyEntry_addTop_iff_of_stageEntryFamily
          hhistory (stageLCarrier limit) topRelation
          (ordinalLCarrier ordinal) (stageLCarrier ordinal)
          data.relation).mpr
        exact Or.inl ⟨hindex, data.state⟩
      refine ⟨ordinalLCarrier ordinal, hindex,
        stageLCarrier ordinal, data.relation, hentry, ?_⟩
      simpa only [stageLCarrier_val] using hzOrdinal
    · rintro ⟨earlierIndex, hindex, earlierStage, earlierRelation,
        hentry, hzEarlier⟩
      rcases exists_eq_ordinalLCarrier_of_mem hindex with
        ⟨ordinal, hordinal, rfl⟩
      rcases (historyEntry_addTop_iff_of_stageEntryFamily
          hhistory (stageLCarrier limit) topRelation
          (ordinalLCarrier ordinal) earlierStage earlierRelation).mp
          hentry with hold | htop
      · have hcanonical := (previous ordinal hordinal).state
        have houtputs := stageStateAt_ordinal_outputs_unique
          ordinal hold.2 hcanonical
        have hzOrdinal : z.1 ∈ LStageZF ordinal := by
          simpa only [houtputs.1, stageLCarrier_val] using hzEarlier
        have hzLimit : z.1 ∈ LStageZF limit :=
          LStageZF_mono hordinal.le hzOrdinal
        simpa only [stageLCarrier_val] using hzLimit
      · have hordinalEq : ordinal = limit :=
          ordinalLCarrier_injective htop.1
        exact ((ne_of_lt hordinal) hordinalEq).elim
  have hrelationUnion : ∀ z : LCarrier.{u},
      z.1 ∈ topRelation.1 ↔
        ∃ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ (ordinalLCarrier limit).1 ∧
            ∃ earlierStage earlierRelation : LCarrier.{u},
              HistoryEntry extended earlierIndex
                earlierStage earlierRelation ∧
              z.1 ∈ earlierRelation.1 := by
    intro z
    constructor
    · intro hz
      rcases (mem_sUnionLCarrier_iff family z).mp hz with
        ⟨earlierRelation, hrelationFamily, hzEarlier⟩
      rcases (hfamily earlierRelation).mp hrelationFamily with
        ⟨earlierIndex, hindex, earlierStage, hstate⟩
      have hentry : HistoryEntry extended earlierIndex
          earlierStage earlierRelation := by
        apply (historyEntry_addTop_iff_of_stageEntryFamily
          hhistory (stageLCarrier limit) topRelation
          earlierIndex earlierStage earlierRelation).mpr
        exact Or.inl ⟨hindex, hstate⟩
      exact ⟨earlierIndex, hindex, earlierStage, earlierRelation,
        hentry, hzEarlier⟩
    · rintro ⟨earlierIndex, hindex, earlierStage, earlierRelation,
        hentry, hzEarlier⟩
      rcases (historyEntry_addTop_iff_of_stageEntryFamily
          hhistory (stageLCarrier limit) topRelation
          earlierIndex earlierStage earlierRelation).mp hentry with
        hold | htop
      · apply (mem_sUnionLCarrier_iff family z).mpr
        refine ⟨earlierRelation, ?_, hzEarlier⟩
        apply (hfamily earlierRelation).mpr
        exact ⟨earlierIndex, hindex, earlierStage, hold.2⟩
      · rw [htop.1] at hindex
        exact (ZFSet.mem_irrefl _ hindex).elim
  have htopLimit : HistoryLimitState extended
      (ordinalLCarrier limit) (stageLCarrier limit) topRelation :=
    ⟨hstageUnion, hrelationUnion⟩
  have htopLocal : HistoryLocalState extended
      (ordinalLCarrier limit) (stageLCarrier limit) topRelation :=
    (historyLocalState_limit_iff extended hl
      (stageLCarrier limit) topRelation).mpr htopLimit
  have hvalid : ValidStageHistory extended (ordinalLCarrier limit) :=
    validStageHistory_addTop_of_family limit hstates history hhistory
      (stageLCarrier limit) topRelation htopLocal
  have htopEntry : HistoryEntry extended (ordinalLCarrier limit)
      (stageLCarrier limit) topRelation := by
    apply (historyEntry_addTop_iff_of_stageEntryFamily
      hhistory (stageLCarrier limit) topRelation
      (ordinalLCarrier limit) (stageLCarrier limit) topRelation).mpr
    exact Or.inr ⟨rfl, rfl, rfl⟩
  exact
    { history := extended
      relation := topRelation
      valid := hvalid
      topEntry := htopEntry }

@[simp]
theorem limitStageHistoryData_relation {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit)
    (previous : ∀ ordinal < limit, StageHistoryData ordinal) :
    (limitStageHistoryData hl previous).relation =
      sUnionLCarrier
        (stageRelationFamily limit
          (uniqueStageStatesBelow_of_historyData previous)) := by
  rfl

@[simp]
theorem zeroStageHistoryData_relation :
    zeroStageHistoryData.relation = (emptyLCarrier : LCarrier.{u}) := by
  rfl

/-- The complete ordinal recursion of internal stage histories. -/
noncomputable def stageHistoryData (ordinal : Ordinal.{u}) :
    StageHistoryData ordinal :=
  Ordinal.limitRecOn ordinal
    zeroStageHistoryData
    successorStageHistoryData
    (fun _limit hl previous => limitStageHistoryData hl previous)

@[simp]
theorem stageHistoryData_zero :
    stageHistoryData (0 : Ordinal.{u}) = zeroStageHistoryData := by
  rw [stageHistoryData, Ordinal.limitRecOn_zero]

@[simp]
theorem stageHistoryData_add_one (ordinal : Ordinal.{u}) :
    stageHistoryData (ordinal + 1) =
      successorStageHistoryData ordinal (stageHistoryData ordinal) := by
  exact Ordinal.limitRecOn_add_one ..

@[simp]
theorem stageHistoryData_limit {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit) :
    stageHistoryData limit =
      limitStageHistoryData hl
        (fun ordinal _hordinal => stageHistoryData ordinal) := by
  simp only [stageHistoryData,
    Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem stageHistoryData_relation_zero :
    (stageHistoryData (0 : Ordinal.{u})).relation = emptyLCarrier := by
  rw [stageHistoryData_zero, zeroStageHistoryData_relation]

@[simp]
theorem stageHistoryData_relation_succ (ordinal : Ordinal.{u}) :
    (stageHistoryData (Order.succ ordinal)).relation =
      canonicalSuccessorRelation ordinal
        (stageHistoryData ordinal).relation := by
  rw [Order.succ_eq_add_one, stageHistoryData_add_one,
    successorStageHistoryData_relation]

theorem stageHistoryData_relation_limit {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit) :
    (stageHistoryData limit).relation =
      sUnionLCarrier
        (stageRelationFamily limit
          (uniqueStageStatesBelow_of_historyData
            (fun ordinal _hordinal => stageHistoryData ordinal))) := by
  rw [stageHistoryData_limit hl, limitStageHistoryData_relation]





end

end Constructible.Model
end CUAdapterModule93



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.CoherentLimitOrder -/
section CUAdapterModule94
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Coherent unions of internally represented stage orders

At a limit stage, a union of arbitrary external well-orders is not enough.
This file records the exact coherence and initial-segment hypotheses under
which the union relation well-orders the limit carrier.  If the family of
graphs is itself represented by a constructible set, its internal union is
then the required graph in `L`.
-/


open Set

universe u

namespace Constructible.Model

noncomputable section

/-- Include the internal carrier of an earlier stage into a later one. -/
def internalStageInclusion {alpha beta : Ordinal.{u}}
    (h : alpha ≤ beta) :
    InternalCarrier (stageLCarrier alpha) ->
      InternalCarrier (stageLCarrier beta) :=
  fun x => ⟨x.1, LStageZF_mono h x.2⟩

@[simp]
theorem internalStageInclusion_val {alpha beta : Ordinal.{u}}
    (h : alpha ≤ beta)
    (x : InternalCarrier (stageLCarrier alpha)) :
    (internalStageInclusion h x).1 = x.1 := rfl



/--
A coherent system of supported stage graphs below `limit`.  Coherence says
later graphs restrict to earlier graphs; `initial` says every earlier stage
is an initial segment of every later order.
-/
structure CoherentStageGraphSystem (limit : Ordinal.{u})
    (graphs : Set.Iio limit -> LCarrier.{u}) : Prop where
  wellOrders : ∀ beta : Set.Iio limit,
    InternallyWellOrders (graphs beta) (stageLCarrier beta.1)
  supported : ∀ beta : Set.Iio limit, ∀ x y : LCarrier.{u},
    GraphRel (graphs beta) x y ->
      x.1 ∈ LStageZF beta.1 ∧ y.1 ∈ LStageZF beta.1
  coherent : ∀ beta gamma : Set.Iio limit, beta.1 ≤ gamma.1 ->
    ∀ x y : LCarrier.{u},
      x.1 ∈ LStageZF beta.1 -> y.1 ∈ LStageZF beta.1 ->
        (GraphRel (graphs gamma) x y ↔ GraphRel (graphs beta) x y)
  initial : ∀ beta gamma : Set.Iio limit, beta.1 ≤ gamma.1 ->
    ∀ x y : LCarrier.{u},
      x.1 ∈ LStageZF beta.1 -> y.1 ∈ LStageZF gamma.1 ->
        GraphRel (graphs gamma) y x -> y.1 ∈ LStageZF beta.1

/-- The external union of all stage relations below a limit. -/
def coherentLimitRel {limit : Ordinal.{u}}
    (graphs : Set.Iio limit -> LCarrier.{u}) :
    InternalCarrier (stageLCarrier limit) ->
      InternalCarrier (stageLCarrier limit) -> Prop :=
  fun x y => ∃ beta : Set.Iio limit,
    GraphRel (graphs beta) x.1 y.1

 theorem commonStageBelowLimit {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit)
    (x y : InternalCarrier (stageLCarrier limit)) :
    ∃ beta : Set.Iio limit,
      x.1.1 ∈ LStageZF beta.1 ∧ y.1.1 ∈ LStageZF beta.1 := by
  rcases (mem_LStageZF_limit_iff hl).mp x.2 with ⟨alpha, ha, hx⟩
  rcases (mem_LStageZF_limit_iff hl).mp y.2 with ⟨beta, hb, hy⟩
  let gamma : Set.Iio limit := ⟨max alpha beta, max_lt ha hb⟩
  refine ⟨gamma, ?_, ?_⟩
  · exact LStageZF_mono (le_max_left alpha beta) hx
  · exact LStageZF_mono (le_max_right alpha beta) hy

/-- Coherent initial-segment unions are well-orders on the limit carrier. -/
theorem coherentLimitRel_isWellOrder {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit)
    (graphs : Set.Iio limit -> LCarrier.{u})
    (hsystem : CoherentStageGraphSystem limit graphs) :
    IsWellOrder (InternalCarrier (stageLCarrier limit))
      (coherentLimitRel graphs) := by
  refine
    { wf := ?_
      trichotomous := ?_ }
  · apply WellFounded.wellFounded_iff_has_min.mpr
    intro candidates hcandidates
    rcases hcandidates with ⟨chosen, hchosen⟩
    rcases (mem_LStageZF_limit_iff hl).mp chosen.2 with
      ⟨betaRaw, hbetaLimit, hchosenBeta⟩
    let beta : Set.Iio limit := ⟨betaRaw, hbetaLimit⟩
    let chosenBeta : InternalCarrier (stageLCarrier beta.1) :=
      ⟨chosen.1, hchosenBeta⟩
    let localCandidates : Set
        (InternalCarrier (stageLCarrier beta.1)) :=
      {x | internalStageInclusion hbetaLimit.le x ∈ candidates}
    have hlocalNonempty : localCandidates.Nonempty := by
      refine ⟨chosenBeta, ?_⟩
      have hinclusion :
          internalStageInclusion hbetaLimit.le chosenBeta = chosen := by
        apply Subtype.ext
        rfl
      change internalStageInclusion hbetaLimit.le chosenBeta ∈ candidates
      simpa only [hinclusion] using hchosen
    letI : IsWellOrder (InternalCarrier (stageLCarrier beta.1))
        (graphRelOn (graphs beta) (stageLCarrier beta.1)) :=
      hsystem.wellOrders beta
    rcases (IsWellFounded.wf : WellFounded
        (graphRelOn (graphs beta) (stageLCarrier beta.1))).has_min
        localCandidates hlocalNonempty with
      ⟨minimum, hminimum, hminimal⟩
    let limitMinimum : InternalCarrier (stageLCarrier limit) :=
      internalStageInclusion hbetaLimit.le minimum
    refine ⟨limitMinimum, hminimum, ?_⟩
    intro y hyCandidates hyBelow
    rcases hyBelow with ⟨gamma, hyBelowGamma⟩
    have hsupportGamma :=
      hsystem.supported gamma y.1 limitMinimum.1 hyBelowGamma
    have hdeltaLimit : max beta.1 gamma.1 < limit :=
      max_lt beta.2 gamma.2
    let delta : Set.Iio limit :=
      ⟨max beta.1 gamma.1, hdeltaLimit⟩
    have hbetaDelta : beta.1 ≤ delta.1 :=
      le_max_left beta.1 gamma.1
    have hgammaDelta : gamma.1 ≤ delta.1 :=
      le_max_right beta.1 gamma.1
    have hyBelowDelta :
        GraphRel (graphs delta) y.1 limitMinimum.1 :=
      (hsystem.coherent gamma delta hgammaDelta y.1 limitMinimum.1
        hsupportGamma.1 hsupportGamma.2).mpr hyBelowGamma
    have hyDelta : y.1.1 ∈ LStageZF delta.1 :=
      LStageZF_mono hgammaDelta hsupportGamma.1
    have hyBeta : y.1.1 ∈ LStageZF beta.1 :=
      hsystem.initial beta delta hbetaDelta limitMinimum.1 y.1
        minimum.2 hyDelta hyBelowDelta
    have hyBelowBeta :
        GraphRel (graphs beta) y.1 limitMinimum.1 :=
      (hsystem.coherent beta delta hbetaDelta y.1 limitMinimum.1
        hyBeta minimum.2).mp hyBelowDelta
    let yBeta : InternalCarrier (stageLCarrier beta.1) :=
      ⟨y.1, hyBeta⟩
    have hyLocal : yBeta ∈ localCandidates := by
      have hinclusion :
          internalStageInclusion hbetaLimit.le yBeta = y := by
        apply Subtype.ext
        rfl
      change internalStageInclusion hbetaLimit.le yBeta ∈ candidates
      simpa only [hinclusion] using hyCandidates
    exact hminimal yBeta hyLocal hyBelowBeta
  · intro x y hnxy hnyx
    rcases commonStageBelowLimit hl x y with ⟨beta, hx, hy⟩
    let xBeta : InternalCarrier (stageLCarrier beta.1) := ⟨x.1, hx⟩
    let yBeta : InternalCarrier (stageLCarrier beta.1) := ⟨y.1, hy⟩
    letI : IsWellOrder (InternalCarrier (stageLCarrier beta.1))
        (graphRelOn (graphs beta) (stageLCarrier beta.1)) :=
      hsystem.wellOrders beta
    rcases trichotomous_of
        (graphRelOn (graphs beta) (stageLCarrier beta.1))
        xBeta yBeta with hxy | hxy | hyx
    · exact (hnxy ⟨beta, hxy⟩).elim
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun z : InternalCarrier (stageLCarrier beta.1) => z.1.1) hxy
    · exact (hnyx ⟨beta, hyx⟩).elim

/-! ## Internalizing the union graph -/

/-- A constructible set represents precisely the range of the graph system. -/
def RepresentsStageGraphFamily {limit : Ordinal.{u}}
    (graphs : Set.Iio limit -> LCarrier.{u})
    (family : LCarrier.{u}) : Prop :=
  ∀ relation : LCarrier.{u}, relation.1 ∈ family.1 ↔
    ∃ beta : Set.Iio limit, relation = graphs beta

/-- Membership in the internal union is exactly membership in one stage
graph, provided `family` represents the graph range. -/
theorem graphRel_sUnion_family_iff {limit : Ordinal.{u}}
    (graphs : Set.Iio limit -> LCarrier.{u})
    (family : LCarrier.{u})
    (hfamily : RepresentsStageGraphFamily graphs family)
    (x y : LCarrier.{u}) :
    GraphRel (sUnionLCarrier family) x y ↔
      ∃ beta : Set.Iio limit, GraphRel (graphs beta) x y := by
  change (orderedPairLCarrier x y).1 ∈ (sUnionLCarrier family).1 ↔ _
  rw [mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨relation, hrelation, hpair⟩
    rcases (hfamily relation).mp hrelation with ⟨beta, rfl⟩
    exact ⟨beta, hpair⟩
  · rintro ⟨beta, hpair⟩
    exact ⟨graphs beta, (hfamily (graphs beta)).mpr ⟨beta, rfl⟩, hpair⟩

/-- A constructibly represented coherent graph family gives an internal
well-order of the limit stage. -/
theorem internallyWellOrders_limit_of_coherentFamily
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    (graphs : Set.Iio limit -> LCarrier.{u})
    (hsystem : CoherentStageGraphSystem limit graphs)
    (family : LCarrier.{u})
    (hfamily : RepresentsStageGraphFamily graphs family) :
    InternallyWellOrders (sUnionLCarrier family) (stageLCarrier limit) := by
  have heq :
      graphRelOn (sUnionLCarrier family) (stageLCarrier limit) =
        coherentLimitRel graphs := by
    funext x y
    apply propext
    exact graphRel_sUnion_family_iff graphs family hfamily x.1 y.1
  rw [InternallyWellOrders, heq]
  exact coherentLimitRel_isWellOrder hl graphs hsystem

/-! ## Retaining coherence after the limit step -/

/-- The data needed to adjoin the union graph at a limit stage to the
preceding coherent system. -/
structure LimitOrderExtension (limit : Ordinal.{u})
    (graphs : Set.Iio limit → LCarrier.{u}) where
  /-- The relation extending the coherent system to the limit stage. -/
  nextRelation : LCarrier.{u}
  wellOrders : InternallyWellOrders nextRelation (stageLCarrier limit)
  supported : ∀ x y : LCarrier.{u}, GraphRel nextRelation x y →
    x.1 ∈ LStageZF limit ∧ y.1 ∈ LStageZF limit
  agreesOnEarlier : ∀ beta : Set.Iio limit, ∀ x y : LCarrier.{u},
    x.1 ∈ LStageZF beta.1 → y.1 ∈ LStageZF beta.1 →
      (GraphRel nextRelation x y ↔ GraphRel (graphs beta) x y)
  earlierIsInitial : ∀ beta : Set.Iio limit, ∀ x y : LCarrier.{u},
    x.1 ∈ LStageZF beta.1 → y.1 ∈ LStageZF limit →
      GraphRel nextRelation y x → y.1 ∈ LStageZF beta.1

/-- A constructibly represented coherent family has a canonical union which
retains support, coherence, and every earlier initial segment. -/
def coherentLimitOrderExtension
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    (graphs : Set.Iio limit → LCarrier.{u})
    (hsystem : CoherentStageGraphSystem limit graphs)
    (family : LCarrier.{u})
    (hfamily : RepresentsStageGraphFamily graphs family) :
    LimitOrderExtension limit graphs where
  nextRelation := sUnionLCarrier family
  wellOrders :=
    internallyWellOrders_limit_of_coherentFamily
      hl graphs hsystem family hfamily
  supported := by
    intro x y hxy
    rcases (graphRel_sUnion_family_iff
        graphs family hfamily x y).mp hxy with ⟨beta, hbeta⟩
    have hsupported := hsystem.supported beta x y hbeta
    exact
      ⟨LStageZF_mono beta.2.le hsupported.1,
        LStageZF_mono beta.2.le hsupported.2⟩
  agreesOnEarlier := by
    intro beta x y hx hy
    constructor
    · intro hlimit
      rcases (graphRel_sUnion_family_iff
          graphs family hfamily x y).mp hlimit with ⟨gamma, hgamma⟩
      let delta : Set.Iio limit :=
        ⟨max beta.1 gamma.1, by
          change max beta.1 gamma.1 < limit
          exact max_lt beta.2 gamma.2⟩
      have hgammaDelta : gamma.1 ≤ delta.1 :=
        le_max_right beta.1 gamma.1
      have hbetaDelta : beta.1 ≤ delta.1 :=
        le_max_left beta.1 gamma.1
      have hgammaSupport := hsystem.supported gamma x y hgamma
      have hdelta : GraphRel (graphs delta) x y :=
        (hsystem.coherent gamma delta hgammaDelta x y
          hgammaSupport.1 hgammaSupport.2).mpr hgamma
      exact (hsystem.coherent beta delta hbetaDelta x y hx hy).mp hdelta
    · intro hbeta
      exact (graphRel_sUnion_family_iff
        graphs family hfamily x y).mpr ⟨beta, hbeta⟩
  earlierIsInitial := by
    intro beta x y hx _hyLimit hyx
    rcases (graphRel_sUnion_family_iff
        graphs family hfamily y x).mp hyx with ⟨gamma, hgamma⟩
    let delta : Set.Iio limit :=
      ⟨max beta.1 gamma.1, by
        change max beta.1 gamma.1 < limit
        exact max_lt beta.2 gamma.2⟩
    have hgammaDelta : gamma.1 ≤ delta.1 :=
      le_max_right beta.1 gamma.1
    have hbetaDelta : beta.1 ≤ delta.1 :=
      le_max_left beta.1 gamma.1
    have hgammaSupport := hsystem.supported gamma y x hgamma
    have hdelta : GraphRel (graphs delta) y x :=
      (hsystem.coherent gamma delta hgammaDelta y x
        hgammaSupport.1 hgammaSupport.2).mpr hgamma
    have hyDelta : y.1 ∈ LStageZF delta.1 :=
      LStageZF_mono hgammaDelta hgammaSupport.1
    exact hsystem.initial beta delta hbetaDelta x y hx hyDelta hdelta

@[simp]
theorem coherentLimitOrderExtension_nextRelation
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    (graphs : Set.Iio limit → LCarrier.{u})
    (hsystem : CoherentStageGraphSystem limit graphs)
    (family : LCarrier.{u})
    (hfamily : RepresentsStageGraphFamily graphs family) :
    (coherentLimitOrderExtension hl graphs hsystem family hfamily).nextRelation =
      sUnionLCarrier family :=
  rfl

end

end Constructible.Model
end CUAdapterModule94



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageZeroInternalOrder -/
section CUAdapterModule95
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The internally represented order on the zero constructible stage

The carrier of `L_0` is empty, so the empty constructible set represents its
unique strict well-order.
-/


universe u

namespace Constructible.Model



end Constructible.Model
end CUAdapterModule95



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.CoherentStageGraphExtension -/
section CUAdapterModule96
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Adjoining one graph to a coherent stage system

Successor and limit constructions both produce a graph at one new ordinal,
together with support, agreement, and initial-segment facts relative to all
earlier stages.  This file packages that common interface and proves that
adjoining such a graph preserves the complete coherent-system invariant.
-/


open Set

universe u

namespace Constructible.Model

noncomputable section

/-- The data required to adjoin a graph at `alpha` to a system below
`alpha`. -/
structure StageGraphExtension (alpha : Ordinal.{u})
    (graphs : Set.Iio alpha → LCarrier.{u}) where
  /-- The relation adjoined at the new stage. -/
  nextRelation : LCarrier.{u}
  wellOrders : InternallyWellOrders nextRelation (stageLCarrier alpha)
  supported : ∀ x y : LCarrier.{u}, GraphRel nextRelation x y →
    x.1 ∈ LStageZF alpha ∧ y.1 ∈ LStageZF alpha
  agreesOnEarlier : ∀ beta : Set.Iio alpha, ∀ x y : LCarrier.{u},
    x.1 ∈ LStageZF beta.1 → y.1 ∈ LStageZF beta.1 →
      (GraphRel nextRelation x y ↔ GraphRel (graphs beta) x y)
  earlierIsInitial : ∀ beta : Set.Iio alpha, ∀ x y : LCarrier.{u},
    x.1 ∈ LStageZF beta.1 → y.1 ∈ LStageZF alpha →
      GraphRel nextRelation y x → y.1 ∈ LStageZF beta.1

/-- Extend a graph family below `alpha` by one value at `alpha`. -/
def appendStageGraph (alpha : Ordinal.{u})
    (graphs : Set.Iio alpha → LCarrier.{u})
    (nextRelation : LCarrier.{u}) :
    Set.Iio (Order.succ alpha) → LCarrier.{u} :=
  fun beta =>
    if hbeta : beta.1 < alpha then
      graphs ⟨beta.1, hbeta⟩
    else nextRelation

/-- The last index below `alpha + 1`. -/
def lastStageIndex (alpha : Ordinal.{u}) : Set.Iio (Order.succ alpha) :=
  ⟨alpha, Order.lt_succ alpha⟩

@[simp]
theorem lastStageIndex_val (alpha : Ordinal.{u}) :
    (lastStageIndex alpha).1 = alpha :=
  rfl

@[simp]
theorem appendStageGraph_last (alpha : Ordinal.{u})
    (graphs : Set.Iio alpha → LCarrier.{u})
    (nextRelation : LCarrier.{u}) :
    appendStageGraph alpha graphs nextRelation (lastStageIndex alpha) =
      nextRelation := by
  simp [appendStageGraph, lastStageIndex]

@[simp]
theorem appendStageGraph_earlier (alpha : Ordinal.{u})
    (graphs : Set.Iio alpha → LCarrier.{u})
    (nextRelation : LCarrier.{u}) (beta : Set.Iio alpha) :
    appendStageGraph alpha graphs nextRelation
        ⟨beta.1, lt_trans beta.2 (Order.lt_succ alpha)⟩ =
      graphs beta := by
  have hbeta : beta.1 < alpha := beta.2
  rw [appendStageGraph, dif_pos hbeta]



/-- A coherent constructible union at a limit is a generic stage
extension. -/
def LimitOrderExtension.toStageGraphExtension
    {limit : Ordinal.{u}} {graphs : Set.Iio limit → LCarrier.{u}}
    (extension : LimitOrderExtension limit graphs) :
    StageGraphExtension limit graphs where
  nextRelation := extension.nextRelation
  wellOrders := extension.wellOrders
  supported := extension.supported
  agreesOnEarlier := extension.agreesOnEarlier
  earlierIsInitial := extension.earlierIsInitial

/-- The represented union construction in the generic extension form. -/
def coherentLimitStageGraphExtension
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    (graphs : Set.Iio limit → LCarrier.{u})
    (hsystem : CoherentStageGraphSystem limit graphs)
    (family : LCarrier.{u})
    (hfamily : RepresentsStageGraphFamily graphs family) :
    StageGraphExtension limit graphs :=
  (coherentLimitOrderExtension hl graphs hsystem family hfamily).toStageGraphExtension

/-! ## The zero and successor extensions -/

theorem false_of_mem_Iio_zero
    (beta : Set.Iio (0 : Ordinal.{u})) : False := by
  exact (not_lt_of_ge bot_le) (Set.mem_Iio.mp beta.2)

/-- There are no stage indices below zero. -/
def emptyStageGraphFamily :
    Set.Iio (0 : Ordinal.{u}) → LCarrier.{u} :=
  fun beta => (false_of_mem_Iio_zero beta).elim



/-- The empty graph is a valid extension at stage zero. -/
def zeroStageGraphExtension :
    StageGraphExtension (0 : Ordinal.{u}) emptyStageGraphFamily where
  nextRelation := emptyLCarrier
  wellOrders := by
    rw [InternallyWellOrders]
    refine
      { wf := WellFounded.intro (fun x => ?_)
        trichotomous := fun x => ?_ }
    · have hx : x.1.1 ∈ (∅ : ZFSet.{u}) := by
        simpa only [stageLCarrier_val, LStageZF_zero] using x.2
      exact (ZFSet.notMem_empty x.1.1 hx).elim
    · have hx : x.1.1 ∈ (∅ : ZFSet.{u}) := by
        simpa only [stageLCarrier_val, LStageZF_zero] using x.2
      exact (ZFSet.notMem_empty x.1.1 hx).elim
  supported := by
    intro x y hxy
    change ZFSet.pair x.1 y.1 ∈ (∅ : ZFSet.{u}) at hxy
    exact (ZFSet.notMem_empty _ hxy).elim
  agreesOnEarlier := by
    intro beta
    exact (false_of_mem_Iio_zero beta).elim
  earlierIsInitial := by
    intro beta
    exact (false_of_mem_Iio_zero beta).elim



/-- At a successor, the canonical formula graph extends the top graph of the
existing system and hence agrees with every earlier graph. -/
def canonicalSuccessorStageGraphExtension
    (alpha : Ordinal.{u})
    (graphs : Set.Iio (Order.succ alpha) → LCarrier.{u})
    (hsystem : CoherentStageGraphSystem (Order.succ alpha) graphs) :
    StageGraphExtension (Order.succ alpha) graphs := by
  let top : Set.Iio (Order.succ alpha) := lastStageIndex alpha
  let previous : LCarrier.{u} := graphs top
  have hprevious :
      InternallyWellOrders previous (stageLCarrier alpha) := by
    simpa only [previous, top, lastStageIndex_val] using
      hsystem.wellOrders top
  let next := canonicalSuccessorOrderExtension alpha previous hprevious
  refine
    { nextRelation := next.nextRelation
      wellOrders := next.wellOrders
      supported := next.supported
      agreesOnEarlier := ?_
      earlierIsInitial := ?_ }
  · intro beta x y hx hy
    have hbetaAlpha : beta.1 ≤ alpha :=
      Order.lt_succ_iff.mp beta.2
    have hxAlpha : x.1 ∈ LStageZF alpha :=
      LStageZF_mono hbetaAlpha hx
    have hyAlpha : y.1 ∈ LStageZF alpha :=
      LStageZF_mono hbetaAlpha hy
    exact (next.agreesOnOld x y hxAlpha hyAlpha).trans
      (hsystem.coherent beta top hbetaAlpha x y hx hy)
  · intro beta x y hx hy hyx
    have hbetaAlpha : beta.1 ≤ alpha :=
      Order.lt_succ_iff.mp beta.2
    have hxAlpha : x.1 ∈ LStageZF alpha :=
      LStageZF_mono hbetaAlpha hx
    have hyAlpha : y.1 ∈ LStageZF alpha :=
      next.oldIsInitial x y hxAlpha hy hyx
    have hyxPrevious : GraphRel previous y x :=
      (next.agreesOnOld y x hyAlpha hxAlpha).mp hyx
    exact hsystem.initial beta top hbetaAlpha x y
      hx hyAlpha hyxPrevious



end

end Constructible.Model
end CUAdapterModule96



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryCoherence -/
section CUAdapterModule97
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Coherence of the internally recursive stage graphs

The relation coordinate of `stageHistoryData` is now assembled into a graph
system.  Successors use the canonical extension theorem and limits use the
internally represented relation family constructed by Replacement.
-/


universe u

namespace Constructible.Model

noncomputable section

/-- The recursively constructed graph at every ordinal below `bound`. -/
def historyStageGraphs (bound : Ordinal.{u}) :
    Set.Iio bound → LCarrier.{u} :=
  fun ordinal => (stageHistoryData ordinal.1).relation

@[simp]
theorem historyStageGraphs_apply (bound : Ordinal.{u})
    (ordinal : Set.Iio bound) :
    historyStageGraphs bound ordinal =
      (stageHistoryData ordinal.1).relation :=
  rfl

/-- The internal relation family used at a limit represents exactly the
range of the recursively constructed earlier graphs. -/
theorem stageRelationFamily_represents_historyStageGraphs
    (limit : Ordinal.{u}) :
    RepresentsStageGraphFamily (historyStageGraphs limit)
      (stageRelationFamily limit
        (uniqueStageStatesBelow_of_historyData
          (fun ordinal _hordinal => stageHistoryData ordinal))) := by
  let hstates : UniqueStageStatesBelow limit :=
    uniqueStageStatesBelow_of_historyData
      (fun ordinal _hordinal => stageHistoryData ordinal)
  intro relation
  rw [show stageRelationFamily limit
      (uniqueStageStatesBelow_of_historyData
        (fun ordinal _hordinal => stageHistoryData ordinal)) =
      stageRelationFamily limit hstates by rfl]
  rw [mem_stageRelationFamily_iff]
  constructor
  · rintro ⟨index, hindex, stage, hstate⟩
    rcases exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    have hcanonical := (stageHistoryData ordinal).state
    have houtputs := stageStateAt_ordinal_outputs_unique
      ordinal hstate hcanonical
    refine ⟨⟨ordinal, hordinal⟩, ?_⟩
    exact houtputs.2
  · rintro ⟨ordinal, rfl⟩
    refine ⟨ordinalLCarrier ordinal.1, ?_, ?_⟩
    · exact (ordinalLCarrier_mem_ordinalLCarrier_iff
        limit ordinal.1).mpr ordinal.2
    · exact ⟨stageLCarrier ordinal.1,
        (stageHistoryData ordinal.1).state⟩

/-- A stage extension together with the fact that its graph is exactly the
relation selected by the history recursion. -/
structure HistoryStageGraphExtension (ordinal : Ordinal.{u})
    (graphs : Set.Iio ordinal → LCarrier.{u}) where
  /-- The coherent graph extension supplied at this stage. -/
  extension : StageGraphExtension ordinal graphs
  nextRelation_eq : extension.nextRelation =
    (stageHistoryData ordinal).relation

/-- In every ordinal case, the recursive relation is a valid coherent
extension of all earlier recursive graphs. -/
theorem historyStageGraphExtension_nonempty (ordinal : Ordinal.{u})
    (hsystem : CoherentStageGraphSystem ordinal
      (historyStageGraphs ordinal)) :
    Nonempty
      (HistoryStageGraphExtension ordinal
        (historyStageGraphs ordinal)) := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit ordinal with
    hzero | hsuccessor | hlimit
  · subst ordinal
    let extension : StageGraphExtension (0 : Ordinal.{u})
        (historyStageGraphs 0) :=
      { nextRelation := emptyLCarrier
        wellOrders := zeroStageGraphExtension.wellOrders
        supported := zeroStageGraphExtension.supported
        agreesOnEarlier := by
          intro beta
          exact (not_lt_of_ge bot_le (Set.mem_Iio.mp beta.2)).elim
        earlierIsInitial := by
          intro beta
          exact (not_lt_of_ge bot_le (Set.mem_Iio.mp beta.2)).elim }
    exact ⟨
      { extension := extension
        nextRelation_eq := by
          change emptyLCarrier = (stageHistoryData 0).relation
          exact stageHistoryData_relation_zero.symm }⟩
  · rcases hsuccessor with ⟨alpha, rfl⟩
    let extension := canonicalSuccessorStageGraphExtension alpha
      (historyStageGraphs (Order.succ alpha)) hsystem
    refine ⟨
      { extension := extension
        nextRelation_eq := ?_ }⟩
    rw [stageHistoryData_relation_succ]
    rfl
  · let family := stageRelationFamily ordinal
      (uniqueStageStatesBelow_of_historyData
        (fun beta _hbeta => stageHistoryData beta))
    have hfamily : RepresentsStageGraphFamily
        (historyStageGraphs ordinal) family :=
      stageRelationFamily_represents_historyStageGraphs ordinal
    let extension := coherentLimitStageGraphExtension hlimit
      (historyStageGraphs ordinal) hsystem family hfamily
    refine ⟨
      { extension := extension
        nextRelation_eq := ?_ }⟩
    rw [stageHistoryData_relation_limit hlimit]
    rfl

/-- A chosen coherent extension.  Its equality field fixes the chosen graph
to the relation produced by `stageHistoryData`. -/
noncomputable def historyStageGraphExtension (ordinal : Ordinal.{u})
    (hsystem : CoherentStageGraphSystem ordinal
      (historyStageGraphs ordinal)) :
    HistoryStageGraphExtension ordinal (historyStageGraphs ordinal) :=
  Classical.choice (historyStageGraphExtension_nonempty ordinal hsystem)

end

end Constructible.Model
end CUAdapterModule97



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryGraphSystem -/
section CUAdapterModule98
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The coherent graph system generated by stage histories

The local extension theorem is iterated over all ordinals.  At a limit bound,
each required pair of graphs already occurs together in the coherent system
through the successor of the later index.
-/


open Set

universe u

namespace Constructible.Model

noncomputable section



@[simp]
theorem historyStageGraphs_last (alpha : Ordinal.{u}) :
    historyStageGraphs (Order.succ alpha) (lastStageIndex alpha) =
      (stageHistoryData alpha).relation :=
  rfl









end

end Constructible.Model
end CUAdapterModule98



/-! # Bridge to the existing Prove2Me constructible universe -/


