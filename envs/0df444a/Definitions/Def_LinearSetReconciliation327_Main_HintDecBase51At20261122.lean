-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintDecBase51At20261122
-- name    : LinearSetReconciliation327_Main_HintDecBase51At20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T15:43:35.029551+00:00
-- url     : https://prove2.me/theorems/8790859a-5fff-47a6-8daf-5895f7219d6d
-- title:
--   The two-window `DownBlkSemAtW` contract of Theorem 5.1's decoder (position-aware)
-- statement:
--   A copy of the project's `HintDecBase51_at` bundle (with the single import re-pointed from the unpublished `HintNativeRoot20261120` module to the published `Bundle51_09`, which contains `HintNativeRoot`'s declarations), published as a `Definitions` node so that the two-window contract `DownBlkSemAtW` of Theorem 5.1's decoder is importable.  It defines the position-aware decoder entry (`hintNativeRootAt` and its prologue), the window contract `DownBlkSemAtW` (a `Sem`-level run of the decoder from an arbitrary payload base and `det` base, with its frame and two-window memory premises), and proves the contract's basic consequences and non-vacuity.  Definitions and proved lemmas only; no `sorry`, no new axiom; axiom audit `[propext, Classical.choice, Quot.sound]`; local `cpl` 20 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's column stage and Theorem 5.1's decoder (the two-window `DownBlkSemAtW` contract).

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_09
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
namespace LinearSetReconciliation327.Main

/-!
# `HintDecBase`: a position-aware Theorem 5.1 decoder prologue

Theorem 5.1's decoder `hintNativeRoot S` locates its whole deterministic table through the
*absolute* entry `det[3]` in three places (`hintRootHintArgs`, `hintRootControlInit`,
`hintRootEmitArgs`).  Theorem 6.5's column stage has to run the decoder on a block whose table sits
at a `det` base `δ` and whose payload sits at a memory base `β`.

This file builds the repaired prologue.  The convention of the caller's per-block table is the one
forced by the classification of `HintRootSlotKind`:

* slot `3` of the child table holds `header - δ` (a pointer relative to the table base), so that
  the decoder can read `det (δ + 3)` and add `δ`;
* the `det`-index slot (`header + 12`) holds the *absolute* index `table`;
* the memory-address slots (`header + 9, 11, 14, 15`) hold `β`-rebased addresses;
* the scalar slots (`header + 10, 13`) are unchanged.

Two corrections to the naive "add `r14` at all three sites" recipe are needed and are made here:
`hintNormalizeSetup` overwrites `r14` by `control` (`hintNormalizeSetup_spec`), so `r14` is *not*
the `det` base any more at the second site; and the whole dispatch clobbers every register except
`r14` (which it keeps equal to `control`), so the `det` base cannot be kept in a register across
the dispatch either.  The repaired sites therefore

1. copy `r14` into `r12` at the first site (`r12` is preserved by the normalise stage),
2. use `r12` at the second site and store it into the spare memory word `control + 3`,
3. reload it from `control + 3` at the third site.

At `δ = β = 0` every added instruction is a no-op on 5.1's own start state (`r12 = 0`) and the
stored value is `0`, so the *semantic* clauses of the old prologue lemmas are recovered verbatim.
-/

/-! ## 1. The three position-aware sites -/

/-- Site 1: `r6 := det (δ+3) + δ = header`, then `r9 := det (header+11) = control` and the spare
word `control + 3` is set to `δ` (this is how the base survives the dispatch); finally
`r0 := r1 + β`, `r1 := r2`. -/
def hintRootHintArgsAt : List Instr :=
  [.imm 3 3, .add 3 3 14, .qDet 6 3, .add 6 6 14,
    .imm 3 11, .add 3 6 3, .qDet 9 3,
    .imm 13 3, .add 3 9 13, .store 3 14,
    .imm 3 0, .add 0 1 15, .add 1 2 3]

/-- Site 2: `δ` is reloaded from the spare word `control + 3` (the dispatch keeps `r14 = control`),
then `r6 := det (δ+3) + δ = header`; the table and the count go to `control`, `control + 1` as
before. -/
def hintRootControlInitAt : List Instr :=
  [.imm 3 3, .add 3 14 3, .load 3 3,
    .imm 9 3, .add 9 3 9, .qDet 6 9, .add 6 6 3,
    .imm 3 12, .add 3 6 3, .qDet 9 3, .store 14 9,
    .imm 3 13, .add 3 6 3, .qDet 9 3,
    .imm 15 1, .add 3 14 15, .store 3 9]

/-- Site 3: `δ` is reloaded from `control + 3`, then `r7 := det (δ+3) + δ = header` and the three
arguments `listBase`, `resultMap`, `N` are read from `header + 15, + 14, + 10`. -/
def hintRootEmitArgsAt : List Instr :=
  [.imm 3 3, .add 3 14 3, .load 3 3,
    .imm 9 3, .add 9 3 9, .qDet 7 9, .add 7 7 3,
    .imm 15 1, .imm 3 15, .add 3 7 3, .qDet 4 3,
    .imm 3 14, .add 3 7 3, .qDet 5 3, .imm 3 10, .add 3 7 3, .qDet 6 3]

@[simp] theorem hintRootHintArgsAt_length : hintRootHintArgsAt.length = 13 := rfl
@[simp] theorem hintRootControlInitAt_length : hintRootControlInitAt.length = 17 := rfl
@[simp] theorem hintRootEmitArgsAt_length : hintRootEmitArgsAt.length = 17 := rfl

/-! ## 2. The rebased header structure -/

/-- `HintRootHeader` with the entry read relocated: the child table lives at `det` base `δ`, its
slot `3` holds the *relative* header offset `header - δ`, and the header block itself is still the
sixteen absolute slots `header + k` that `HintNormalizeTable` and the dispatch use.  At `δ = 0`
this is exactly `HintRootHeader`. -/
structure HintRootHeaderAt (E : RAMEnv) (δ header control hintMap resultMap listBase table count N : ℕ) :
    Prop where
  word : 15 < 2 ^ E.W
  span : header + 15 < 2 ^ E.W
  delta_span : δ + 15 < 2 ^ E.W
  delta_le : δ ≤ header
  entry : E.det (δ + 3) = header - δ
  control_span : control + 2 < 2 ^ E.W
  scratch_span : control + 3 < 2 ^ E.W
  normalize : HintNormalizeTable E header hintMap N control
  dispatch_table : E.det (header + 12) = table
  dispatch_count : E.det (header + 13) = count
  result_address : E.det (header + 14) = resultMap
  list_address : E.det (header + 15) = listBase
  table_fit : table < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  result_fit : resultMap < 2 ^ E.W
  list_fit : listBase < 2 ^ E.W

theorem HintRootHeaderAt.toZero {E : RAMEnv} {header control hintMap resultMap listBase table count N : ℕ}
    (h : HintRootHeaderAt E 0 header control hintMap resultMap listBase table count N) :
    HintRootHeader E header control hintMap resultMap listBase table count N :=
  { word := h.word
    span := h.span
    anchor := by simpa using h.entry
    control_span := h.control_span
    normalize := h.normalize
    dispatch_table := h.dispatch_table
    dispatch_count := h.dispatch_count
    result_address := h.result_address
    list_address := h.list_address
    table_fit := h.table_fit
    count_fit := h.count_fit
    result_fit := h.result_fit
    list_fit := h.list_fit }

/-! ## 3. The three re-pointed prologue lemmas -/

theorem hintRootHintArgsAt_spec (E : RAMEnv) (state : RAMState)
    (δ β header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (hDelta : state.regs 14 = δ) (hBeta : state.regs 15 = β)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W)
    (hBetaSource : β + state.regs 1 < 2 ^ E.W) :
    let out := runBlock hintRootHintArgsAt E state
    out.pc = state.pc + 13 ∧ out.mem = Function.update state.mem (control + 3) δ ∧
      out.regs 6 = header ∧ out.regs 0 = β + state.regs 1 ∧ out.regs 1 = state.regs 2 := by
  have hSpan := hdr.span
  have hDeltaSpan := hdr.delta_span
  have hDeltaLe := hdr.delta_le
  have hEntry := hdr.entry
  have hControl := hdr.normalize.control_address
  have hScratchSpan := hdr.scratch_span
  have h3 : 3 < 2 ^ E.W := by omega
  have hHdr : header < 2 ^ E.W := by omega
  have hD : δ < 2 ^ E.W := by omega
  have hA11 : header + 11 < 2 ^ E.W := by omega
  have hC3 : control + 3 < 2 ^ E.W := by omega
  have hIdx3 : (3 + δ) % 2 ^ E.W = δ + 3 := by
    rw [Nat.add_comm 3 δ, Nat.mod_eq_of_lt (by omega)]
  have hHead : (header - δ + δ) % 2 ^ E.W = header := by
    rw [show header - δ + δ = header by omega, Nat.mod_eq_of_lt hHdr]
  have hA11v : (header + 11) % 2 ^ E.W = header + 11 := Nat.mod_eq_of_lt hA11
  have hCtrl : E.det (header + 11) % 2 ^ E.W = control := by
    rw [hControl, Nat.mod_eq_of_lt (by omega)]
  have hC3v : (control + 3) % 2 ^ E.W = control + 3 := Nat.mod_eq_of_lt hC3
  have hBeta1 : (state.regs 1 + β) % 2 ^ E.W = β + state.regs 1 := by
    rw [Nat.add_comm (state.regs 1) β, Nat.mod_eq_of_lt (by omega)]
  have hZero : (0 + 0) % 2 ^ E.W = 0 := by simp
  simp [hintRootHintArgsAt, runBlock, execInstr, hDelta, hBeta, hdr.entry, Nat.mod_eq_of_lt h3,
    hIdx3, hHead, hA11v, hCtrl, hC3v, hBeta1, Nat.mod_eq_of_lt hD, Nat.mod_eq_of_lt hSource,
    Nat.mod_eq_of_lt hLength, Nat.mod_eq_of_lt hBetaSource]

theorem hintRootControlInitAt_spec (E : RAMEnv) (state : RAMState)
    (δ header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (hCtx : state.regs 14 = control) (hScratch : state.mem (control + 3) = δ) :
    let out := runBlock hintRootControlInitAt E state
    out.pc = state.pc + 17 ∧
      out.mem = Function.update (Function.update state.mem control table) (control + 1) count ∧
      HintDispatchData control table count (state.mem (control + 2)) out := by
  have hSpan := hdr.span
  have hDeltaSpan := hdr.delta_span
  have hDeltaLe := hdr.delta_le
  have hEntry := hdr.entry
  have hCtrlSpan := hdr.control_span
  have hScratchSpan := hdr.scratch_span
  have hTableFit := hdr.table_fit
  have hCountFit := hdr.count_fit
  have h3 : 3 < 2 ^ E.W := by omega
  have hHdr : header < 2 ^ E.W := by omega
  have hD : δ < 2 ^ E.W := by omega
  have hA12 : header + 12 < 2 ^ E.W := by omega
  have hA13 : header + 13 < 2 ^ E.W := by omega
  have hC1 : control + 1 < 2 ^ E.W := by omega
  have hC3 : control + 3 < 2 ^ E.W := by omega
  have hIdxC : (3 + control) % 2 ^ E.W = control + 3 := by
    rw [Nat.add_comm 3 control, Nat.mod_eq_of_lt (by omega)]
  have hDv : state.mem (control + 3) % 2 ^ E.W = δ := by
    rw [hScratch, Nat.mod_eq_of_lt hD]
  have hD3v : (δ + 3) % 2 ^ E.W = δ + 3 := Nat.mod_eq_of_lt (by omega)
  have hHead : (header - δ + δ) % 2 ^ E.W = header := by
    rw [show header - δ + δ = header by omega, Nat.mod_eq_of_lt hHdr]
  have hC1v : (control + 1) % 2 ^ E.W = control + 1 := Nat.mod_eq_of_lt hC1
  have hA12v : (header + 12) % 2 ^ E.W = header + 12 := Nat.mod_eq_of_lt hA12
  have hA13v : (header + 13) % 2 ^ E.W = header + 13 := Nat.mod_eq_of_lt hA13
  have hC3v : (control + 3) % 2 ^ E.W = control + 3 := Nat.mod_eq_of_lt hC3
  have hMem3 : state.mem ((control + 3) % 2 ^ E.W) = δ := by
    rw [hC3v, hScratch]
  have hV12 : (header - δ + δ + 12) % 2 ^ E.W = header + 12 := by
    rw [show header - δ + δ + 12 = header + 12 by omega, hA12v]
  have hV13 : (header - δ + δ + 13) % 2 ^ E.W = header + 13 := by
    rw [show header - δ + δ + 13 = header + 13 by omega, hA13v]
  have hTbl : E.det (header + 12) % 2 ^ E.W = table := by
    rw [hdr.dispatch_table, Nat.mod_eq_of_lt hTableFit]
  have hCnt : E.det (header + 13) % 2 ^ E.W = count := by
    rw [hdr.dispatch_count, Nat.mod_eq_of_lt hCountFit]
  have hc10 : control + 1 ≠ control := by omega
  have hc02 : control + 2 ≠ control := by omega
  have hc21 : control + 2 ≠ control + 1 := by omega
  have hOne : 1 < 2 ^ E.W := by omega
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintRootControlInitAt, runBlock, execInstr, hCtx, hdr.entry, hIdxC, hMem3, hD3v, hHead,
      hC1v, hA12v, hA13v, hV12, hV13, hTbl, hCnt, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt hOne,
      Function.update_of_ne hc10, Function.update_of_ne hc02, Function.update_of_ne hc21]

theorem hintRootEmitArgsAt_spec (E : RAMEnv) (state : RAMState)
    (δ header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (hCtx : state.regs 14 = control) (hScratch : state.mem (control + 3) = δ) :
    let out := runBlock hintRootEmitArgsAt E state
    out.pc = state.pc + 17 ∧ out.mem = state.mem ∧ out.regs 14 = state.regs 14 ∧
      HintEmitArgs listBase resultMap N out := by
  have hWord := hdr.word
  have hSpan := hdr.span
  have hDeltaSpan := hdr.delta_span
  have hDeltaLe := hdr.delta_le
  have hEntry := hdr.entry
  have hControl := hdr.normalize.control_address
  have hCountValue := hdr.normalize.count_value
  have hResultFit := hdr.result_fit
  have hListFit := hdr.list_fit
  have h3 : 3 < 2 ^ E.W := by omega
  have hHdr : header < 2 ^ E.W := by omega
  have hD : δ < 2 ^ E.W := by omega
  have hD3 : δ + 3 < 2 ^ E.W := by omega
  have hA10 : header + 10 < 2 ^ E.W := by omega
  have hA14 : header + 14 < 2 ^ E.W := by omega
  have hA15 : header + 15 < 2 ^ E.W := by omega
  have hNormSpan := hdr.normalize.dest_span
  have hScratchSpan := hdr.scratch_span
  have hNFit : N < 2 ^ E.W := by omega
  have hC3 : control + 3 < 2 ^ E.W := by omega
  have hOne : 1 < 2 ^ E.W := by omega
  have hFifteen : 15 < 2 ^ E.W := by omega
  have hIdxC : (3 + control) % 2 ^ E.W = control + 3 := by
    rw [Nat.add_comm 3 control, Nat.mod_eq_of_lt (by omega)]
  have hC3v : (control + 3) % 2 ^ E.W = control + 3 := Nat.mod_eq_of_lt hC3
  have hDv : (δ + 3 + 0) % 2 ^ E.W = δ + 3 := by
    simp only [Nat.add_zero]
    exact Nat.mod_eq_of_lt hD3
  have hRel : (header - δ + δ) % 2 ^ E.W = header := by
    rw [show header - δ + δ = header by omega, Nat.mod_eq_of_lt hHdr]
  have hNine : (δ + 3 + 3) % 2 ^ E.W = δ + 3 + 3 := Nat.mod_eq_of_lt (by omega)
  have hA15v : (header + 15) % 2 ^ E.W = header + 15 := Nat.mod_eq_of_lt hA15
  have hA14v : (header + 14) % 2 ^ E.W = header + 14 := Nat.mod_eq_of_lt hA14
  have hA10v : (header + 10) % 2 ^ E.W = header + 10 := Nat.mod_eq_of_lt hA10
  have hList : E.det (header + 15) % 2 ^ E.W = listBase := by
    rw [hdr.list_address, Nat.mod_eq_of_lt hListFit]
  have hResult : E.det (header + 14) % 2 ^ E.W = resultMap := by
    rw [hdr.result_address, Nat.mod_eq_of_lt hResultFit]
  have hCount : E.det (header + 10) % 2 ^ E.W = N := by
    rw [hCountValue, Nat.mod_eq_of_lt hNFit]
  refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintRootEmitArgsAt, runBlock, execInstr, hCtx, hScratch, hdr.entry, hIdxC, hC3v, hDv,
      hRel, hNine, hA15v, hA14v, hA10v, hList, hResult, hCount, Nat.mod_eq_of_lt h3,
      Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hFifteen]

/-! ## 4. The `δ = β = 0` specialisation recovers the old statements -/

/-- At `δ = β = 0` the first site returns the same control-flow-relevant outputs as 5.1's
`hintRootHintArgs` (`r6 = header`, `r0 = r1`, `r1 = r2`); its only memory effect is to zero the
spare word `control + 3`, and it uses `r9`/`r13` as scratch. -/
theorem hintRootHintArgsAt_zero (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeaderAt E 0 header control hintMap resultMap listBase table count N)
    (h14 : state.regs 14 = 0) (h15 : state.regs 15 = 0)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W) :
    let out := runBlock hintRootHintArgsAt E state
    out.regs 6 = header ∧ out.regs 0 = state.regs 1 ∧ out.regs 1 = state.regs 2 ∧
      out.mem = Function.update state.mem (control + 3) 0 := by
  have hOut := hintRootHintArgsAt_spec E state 0 0 header control hintMap resultMap listBase
    table count N hdr h14 h15 hSource hLength (by simpa using hSource)
  obtain ⟨-, hMem, hHead, hSrc, hLen⟩ := hOut
  exact ⟨hHead, by simpa using hSrc, hLen, hMem⟩

/-- At `δ = 0` the second site recovers 5.1's memory update and `HintDispatchData` conclusion
verbatim; only the pc offset grows with the longer instruction list. -/
theorem hintRootControlInitAt_zero (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeaderAt E 0 header control hintMap resultMap listBase table count N)
    (hCtx : state.regs 14 = control) (hScratch : state.mem (control + 3) = 0) :
    let out := runBlock hintRootControlInitAt E state
    out.pc = state.pc + 17 ∧
      out.mem = Function.update (Function.update state.mem control table) (control + 1) count ∧
      HintDispatchData control table count (state.mem (control + 2)) out :=
  hintRootControlInitAt_spec E state 0 header control hintMap resultMap listBase table count N
    hdr hCtx (by simpa using hScratch)

/-- At `δ = 0` with an empty spare word the third site is 5.1's `hintRootEmitArgs` as far as the
statement is concerned: same memory, same `HintEmitArgs`, same `r14`; only the pc offset grows
with the longer instruction list. -/
theorem hintRootEmitArgsAt_zero (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeaderAt E 0 header control hintMap resultMap listBase table count N)
    (hCtx : state.regs 14 = control) (hScratch : state.mem (control + 3) = 0) :
    let out := runBlock hintRootEmitArgsAt E state
    out.pc = state.pc + 17 ∧ out.mem = state.mem ∧ out.regs 14 = state.regs 14 ∧
      HintEmitArgs listBase resultMap N out :=
  hintRootEmitArgsAt_spec E state 0 header control hintMap resultMap listBase table count N hdr
    hCtx (by simpa using hScratch)

/-! ## 5. The naive "add `r14` at the second site" edit is wrong -/

/-- The literal recipe of the task at site 2: read `det (r14 + 3)` and add `r14` to the value. -/
def hintRootControlInitR14 : List Instr :=
  [.imm 3 3, .add 3 3 14, .qDet 6 3, .add 6 6 14,
    .imm 3 12, .add 3 6 3, .qDet 9 3, .store 14 9,
    .imm 15 1, .add 3 3 15, .qDet 9 3, .add 3 14 15, .store 3 9]

/-- `hintNormalizeSetup` leaves `r14 = control`, so at the second site the tag "`r14` is the `det`
base" has already been destroyed by 5.1's own normalise prologue. -/
theorem hintRootControlInitR14_reads_control (E : RAMEnv) (state : RAMState)
    (δ header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (hCtx : state.regs 14 = control) (h3 : 3 < 2 ^ E.W) :
    (runBlock hintRootControlInitR14 E state).regs 6 =
      (E.det (control + 3) + control) % 2 ^ E.W := by
  have hScratchSpan := hdr.scratch_span
  have hC3 : control + 3 < 2 ^ E.W := by omega
  have hIdxC : (3 + control) % 2 ^ E.W = control + 3 := by
    rw [Nat.add_comm 3 control, Nat.mod_eq_of_lt (by omega)]
  simp [hintRootControlInitR14, runBlock, execInstr, hCtx, Nat.mod_eq_of_lt h3, hIdxC,
    Nat.mod_eq_of_lt hC3]

/-- Hence the literal edit reads the table at `control + 3`, not at `δ + 3`: whenever that entry
differs from the true header the literal site returns the wrong header. -/
theorem hintRootControlInitR14_wrong (E : RAMEnv) (state : RAMState)
    (δ header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (hCtx : state.regs 14 = control) (h3 : 3 < 2 ^ E.W)
    (hNe : (E.det (control + 3) + control) % 2 ^ E.W ≠ header) :
    (runBlock hintRootControlInitR14 E state).regs 6 ≠ header := by
  rw [hintRootControlInitR14_reads_control E state δ header control hintMap resultMap listBase
    table count N hdr hCtx h3]
  exact hNe

/-! ## 6. The assembled decoder `Stmt` and its run contract -/

def hintRootEnterAt : Stmt :=
  .seq (.code hintRootHintArgsAt) (.seq hintNormalizeStmt (.code hintRootControlInitAt))
def hintRootExitAt : Stmt := .seq (.code hintRootEmitArgsAt) hintEmitResult

@[simp] theorem hintRootEnterAt_len : hintRootEnterAt.len = 70 := rfl
@[simp] theorem hintRootExitAt_len : hintRootExitAt.len = 30 := rfl

/-- The same action list as 5.1's `hintNativeActions`, with the CR action's baked entry shifted
by the fourteen extra prologue instructions (`56 → 70`, so the switch base `75 → 89`). -/
def hintNativeActionsAt (S : CRSourceBundle) : List Stmt :=
  hintActionsWithCR S 89 hintNativeOtherActions hintNormalizeStmt

def hintNativeRootAt (S : CRSourceBundle) : Stmt :=
  .seq hintRootEnterAt (.seq (hintDispatchStmt (hintNativeActionsAt S)) hintRootExitAt)

def hintNativeProgramAt (S : CRSourceBundle) : Program := (hintNativeRootAt S).compile 0 ++ [.halt]

theorem hintNativeRootAt_at (S : CRSourceBundle) :
    At (hintNativeProgramAt S) 0 ((hintNativeRootAt S).compile 0) := by
  intro i hi
  simp only [hintNativeProgramAt, Nat.zero_add, List.getElem?_append_left hi]

theorem hintNativeRootAt_halt (S : CRSourceBundle) (state : RAMState)
    (hPc : state.pc = (hintNativeRootAt S).len) : Halted (hintNativeProgramAt S) state := by
  unfold Halted
  rw [hPc, ← Stmt.length_compile (hintNativeRootAt S) 0]
  simp [hintNativeProgramAt]

/-! ## 7. The re-pointed enter contract -/

theorem hintRootEnterAt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (δ β header control hintMap resultMap listBase table count N base : ℕ)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (hDelta : state.regs 14 = δ) (hBeta : state.regs 15 = β)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W)
    (hBetaSource : β + state.regs 1 < 2 ^ E.W)
    (hSpan : β + state.regs 1 + min (state.regs 2) N ≤ 2 ^ E.W)
    (hSeparate : β + state.regs 1 + min (state.regs 2) N ≤ hintMap ∨
      hintMap + N < β + state.regs 1)
    (hControl : control + 2 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSep : control + 4 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSource : ∀ i < min (state.regs 2) N, β + state.regs 1 + i ≠ control + 3)
    (hAt : At P base (hintRootEnterAt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 70) state (fun k out => k ≤ 20 * N + 54 ∧
      HintDispatchData control table count (out.mem (control + 2)) out ∧
      out.mem (control + 3) = δ ∧
      (∀ q < N, out.mem (hintMap + q) =
        hintStampValue E (β + state.regs 1) (min (state.regs 2) N) state.mem q) ∧
      (∀ address, (address < hintMap ∨ hintMap + N < address) →
        address ≠ control → address ≠ control + 1 → address ≠ control + 3 →
        out.mem address = state.mem address)) := by
  obtain ⟨hArgsAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintRootHintArgsAt at hArgsAt
  change At P (base + 13) ((Stmt.seq hintNormalizeStmt (.code hintRootControlInitAt)).compile
    (base + 13)) at hRestAt
  obtain ⟨hNormalizeAt, hControlAt⟩ := At.seqStmt hRestAt
  change At P (base + 13) (hintNormalizeStmt.compile (base + 13)) at hNormalizeAt
  change At P (base + 53) hintRootControlInitAt at hControlAt
  have hSetup := hintRootHintArgsAt_spec E state δ β header control hintMap resultMap listBase
    table count N hdr hDelta hBeta hSource hLength hBetaSource
  generalize hs : runBlock hintRootHintArgsAt E state = entered at hSetup
  obtain ⟨hSetupPc, hSetupMem, hHead, hSrc, hCount⟩ := hSetup
  have hRunSetup : (step P E)^[13] state = entered := by
    have hh := iterate_runBlock_of_at P E hintRootHintArgsAt state (by rwa [hPc])
      (by simp [hintRootHintArgsAt, NoBranch, Instr.NoBranchI])
    rw [hs] at hh
    exact hh
  obtain ⟨_, kn, marked, hRunN, hPcN, hCost, hCtxN, hHints, hFrame⟩ :=
    hintNormalizeStmt_sem P E entered header hintMap N control (base + 13) hdr.normalize hHead
      (hSrc.symm ▸ hBetaSource) (by rw [hSrc, hCount]; exact hSpan)
      (by rw [hSrc, hCount]; exact hSeparate) hNormalizeAt (by omega)
  have hScratchFirst : entered.mem (control + 3) = δ := by
    rw [hSetupMem]
    simp
  have hScratchMarked : marked.mem (control + 3) = δ := by
    have hOut := hFrame (control + 3) (by
      rcases hScratchSep with h | h
      · left; omega
      · right; omega)
    exact hOut.trans hScratchFirst
  have hEnteredEq : ∀ a, a ≠ control + 3 → entered.mem a = state.mem a := by
    intro a ha
    rw [hSetupMem]
    simp only [Function.update_apply]
    rw [if_neg ha]
  have hFinal := hintRootControlInitAt_spec E marked δ header control hintMap resultMap listBase
    table count N hdr hCtxN hScratchMarked
  generalize hf : runBlock hintRootControlInitAt E marked = out at hFinal
  obtain ⟨hFinalPc, hFinalMem, hCtrl⟩ := hFinal
  have hRunFinal : (step P E)^[17] marked = out := by
    have hh := iterate_runBlock_of_at P E hintRootControlInitAt marked (by rwa [hPcN])
      (by simp [hintRootControlInitAt, NoBranch, Instr.NoBranchI])
    rw [hf] at hh
    exact hh
  have hStampEq : ∀ q, hintStampValue E (entered.regs 0) (min (entered.regs 1) N) entered.mem q
      = hintStampValue E (β + state.regs 1) (min (state.regs 2) N) state.mem q := by
    intro q
    rw [hSrc, hCount]
    apply hintTruth_congr
    constructor
    · rintro ⟨i, hi, hval⟩
      exact ⟨i, hi, (hEnteredEq _ (hScratchSource i hi)) ▸ hval⟩
    · rintro ⟨i, hi, hval⟩
      exact ⟨i, hi, (hEnteredEq _ (hScratchSource i hi)) ▸ hval⟩
  have hCursorEq : out.mem (control + 2) = marked.mem (control + 2) := by
    rw [hFinalMem]
    rw [Function.update_of_ne (by omega : control + 2 ≠ control + 1),
      Function.update_of_ne (by omega : control + 2 ≠ control)]
  have hCtrl' : HintDispatchData control table count (out.mem (control + 2)) out := by
    rw [hCursorEq]
    exact hCtrl
  refine ⟨hPc, 17 + (kn + 13), out, hintIterate_then (step P E)
      (hintIterate_then (step P E) hRunSetup hRunN) hRunFinal, by omega, ?_⟩
  refine ⟨by omega, hCtrl', ?_, ?_, ?_⟩
  · rw [hFinalMem, Function.update_of_ne (by omega : control + 3 ≠ control + 1),
      Function.update_of_ne (by omega : control + 3 ≠ control), hScratchMarked]
  · intro q hq
    have hA : hintMap + q ≠ control := by rcases hControl with h | h <;> omega
    have hB : hintMap + q ≠ control + 1 := by rcases hControl with h | h <;> omega
    rw [hFinalMem, Function.update_of_ne hB, Function.update_of_ne hA,
      hHints q hq, hStampEq q]
  · intro addr hAway hA hB hC
    rw [hFinalMem, Function.update_of_ne hB, Function.update_of_ne hA]
    exact (hFrame addr hAway).trans (hEnteredEq addr hC)

/-! ## 8. The re-pointed exit contract -/

theorem hintRootExitAt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (δ header control hintMap resultMap listBase table count N base : ℕ)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (hCtx : state.regs 14 = control) (hScratch : state.mem (control + 3) = δ)
    (hSep : listBase + N ≤ resultMap) (hBitsSpan : resultMap + N ≤ 2 ^ E.W)
    (accept : ℕ → Bool)
    (hBits : ∀ q < N, state.mem (resultMap + q) = if accept q then 1 else 0)
    (hAt : At P base (hintRootExitAt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 30) state (fun k out => k ≤ 9 * N + 23 ∧
      outList out = hintGatherList accept N ∧ CRMemFrame listBase (listBase + N) state.mem out.mem) := by
  obtain ⟨hArgsAt, hEmitAt⟩ := At.seqStmt hAt
  change At P base hintRootEmitArgsAt at hArgsAt
  change At P (base + 17) (hintEmitResult.compile (base + 17)) at hEmitAt
  have hSetup := hintRootEmitArgsAt_spec E state δ header control hintMap resultMap listBase
    table count N hdr hCtx hScratch
  generalize hs : runBlock hintRootEmitArgsAt E state = ready at hSetup
  obtain ⟨hReady, hMem, _, hArgs⟩ := hSetup
  have hRunSetup : (step P E)^[17] state = ready := by
    have h := iterate_runBlock_of_at P E hintRootEmitArgsAt state (by rwa [hPc])
      (by simp [hintRootEmitArgsAt, NoBranch, Instr.NoBranchI])
    rw [hs] at h
    exact h
  have hWidth := hdr.word
  have hN := hdr.normalize.dest_span
  have hInput : HintEmitSource E listBase resultMap N accept ready.mem := by
    refine ⟨by omega, by omega, hSep, by omega, ?_, ?_⟩
    · intro q hq; omega
    · rw [hMem]; exact hBits
  obtain ⟨_, k, out, hRun, hEnd, hCost, _, hList, hFrame⟩ :=
    hintEmitResult_sem P E ready listBase resultMap N (base + 17) accept hInput hdr.list_fit hArgs
      hEmitAt (by omega)
  refine ⟨hPc, k + 17, out, hintIterate_then (step P E) hRunSetup hRun, by omega, ?_⟩
  refine ⟨by omega, hList, hMem ▸ hFrame⟩

/-! ## 9. The full decoder run -/

theorem hintNativeRootAt_sem (S : CRSourceBundle) (E : RAMEnv) (state : RAMState)
    (δ β header control hintMap resultMap listBase table N : ℕ) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (accept : ℕ → Bool)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table events.length N)
    (hPc : state.pc = 0) (hWordState : UpWordState E state)
    (hDelta : state.regs 14 = δ) (hBeta : state.regs 15 = β)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W)
    (hBetaSource : β + state.regs 1 < 2 ^ E.W)
    (hSpan : β + state.regs 1 + min (state.regs 2) N ≤ 2 ^ E.W)
    (hSeparate : β + state.regs 1 + min (state.regs 2) N ≤ hintMap ∨
      hintMap + N < β + state.regs 1)
    (hControl : control + 2 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSep : control + 4 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSource : ∀ i < min (state.regs 2) N, β + state.regs 1 + i ≠ control + 3)
    (hOut : listBase + N ≤ resultMap) (hOutSpan : resultMap + N ≤ 2 ^ E.W)
    (hTable : HintDispatchTable E table events)
    (hTags : ∀ j : Fin events.length, events[j.val].1 < (hintNativeActionsAt S).length)
    (hInit : ∀ mem,
      (∀ q < N, mem (hintMap + q) = hintStampValue E (β + state.regs 1)
        (min (state.regs 2) N) state.mem q) →
      (∀ address, (address < hintMap ∨ hintMap + N < address) →
        address ≠ control → address ≠ control + 1 → address ≠ control + 3 →
        mem address = state.mem address) →
      mem (control + 3) = δ → I 0 mem)
    (hCursor : ∀ n mem cursor, I n mem → I n (Function.update mem (control + 2) cursor))
    (hScratchI : ∀ n mem, I n mem → mem (control + 3) = δ)
    (hActions : HintLocatedActions (hintNativeProgramAt S) E control table 89
      (hintNativeActionsAt S) events budget I)
    (hFinal : ∀ mem, I events.length mem → ∀ q < N,
      mem (resultMap + q) = if accept q then 1 else 0) :
    Sem (hintNativeProgramAt S) E 0 (hintNativeRootAt S).len state (fun k out =>
      k ≤ hintDispatchBudget (hintNativeActionsAt S) events.length budget + 29 * N + 86 ∧
      outList out = hintGatherList accept N) := by
  let P := hintNativeProgramAt S
  let actions := hintNativeActionsAt S
  let dispatch := hintDispatchStmt actions
  obtain ⟨hEnterAt, hRestAt⟩ := At.seqStmt (hintNativeRootAt_at S)
  change At P 0 (hintRootEnterAt.compile 0) at hEnterAt
  change At P 70 ((Stmt.seq dispatch hintRootExitAt).compile 70) at hRestAt
  obtain ⟨hDispatchAt, hExitAt⟩ := At.seqStmt hRestAt
  change At P 70 (dispatch.compile 70) at hDispatchAt
  change At P (70 + dispatch.len) (hintRootExitAt.compile (70 + dispatch.len)) at hExitAt
  obtain ⟨_, ke, first, hRunFirst, hFirstPc, hFirstCost, hData, hScratchFirst, hHints, hFrame⟩ :=
    hintRootEnterAt_sem P E state δ β header control hintMap resultMap listBase table
      events.length N 0 hdr hDelta hBeta hSource hLength hBetaSource hSpan hSeparate hControl
      hScratchSep hScratchSource hEnterAt hPc
  have hWord := hdr.word
  have hWordFirst : UpWordState E first := hRunFirst ▸ upIterate_word_bound P E state ke hWordState
  obtain ⟨_, kd, middle, hRunDispatch, hMiddlePc, hDispatchCost, hInv, hMiddleData⟩ :=
    hintLocatedDispatch_sem P E first control table 70 (first.mem (control + 2))
      actions events budget I (by omega) hdr.control_span hdr.count_fit hTable hTags hData
      (hInit _ hHints hFrame hScratchFirst) hWordFirst hCursor hActions hDispatchAt hFirstPc
  have hMiddleCtx : middle.regs 14 = control := hMiddleData.context
  have hMiddleScratch : middle.mem (control + 3) = δ := hScratchI _ _ hInv
  obtain ⟨_, ko, out, hRunExit, hEnd, hExitCost, hList, _⟩ :=
    hintRootExitAt_sem P E middle δ header control hintMap resultMap listBase table
      events.length N (70 + dispatch.len) hdr hMiddleCtx hMiddleScratch hOut hOutSpan accept
      (hFinal _ hInv) hExitAt hMiddlePc
  refine ⟨hPc, ko + (kd + ke), out, hintIterate_then (step P E)
    (hintIterate_then (step P E) hRunFirst hRunDispatch) hRunExit, ?_, ?_⟩
  · change out.pc = 70 + (dispatch.len + 30)
    omega
  · refine ⟨?_, hList⟩
    change ko + (kd + ke) ≤ hintDispatchBudget actions events.length budget + 29 * N + 86
    omega

/-! ## 10. `HaltsWithin` at 5.1's own bound -/

theorem hintNativeRootAt_haltsWithin (S : CRSourceBundle) (E : RAMEnv) (state : RAMState)
    (δ β header control hintMap resultMap listBase table N : ℕ) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (accept : ℕ → Bool)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table events.length N)
    (hPc : state.pc = 0) (hWordState : UpWordState E state)
    (hDelta : state.regs 14 = δ) (hBeta : state.regs 15 = β)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W)
    (hBetaSource : β + state.regs 1 < 2 ^ E.W)
    (hSpan : β + state.regs 1 + min (state.regs 2) N ≤ 2 ^ E.W)
    (hSeparate : β + state.regs 1 + min (state.regs 2) N ≤ hintMap ∨
      hintMap + N < β + state.regs 1)
    (hControl : control + 2 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSep : control + 4 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSource : ∀ i < min (state.regs 2) N, β + state.regs 1 + i ≠ control + 3)
    (hOut : listBase + N ≤ resultMap) (hOutSpan : resultMap + N ≤ 2 ^ E.W)
    (hTable : HintDispatchTable E table events)
    (hTags : ∀ j : Fin events.length, events[j.val].1 < (hintNativeActionsAt S).length)
    (hInit : ∀ mem,
      (∀ q < N, mem (hintMap + q) = hintStampValue E (β + state.regs 1)
        (min (state.regs 2) N) state.mem q) →
      (∀ address, (address < hintMap ∨ hintMap + N < address) →
        address ≠ control → address ≠ control + 1 → address ≠ control + 3 →
        mem address = state.mem address) →
      mem (control + 3) = δ → I 0 mem)
    (hCursor : ∀ n mem cursor, I n mem → I n (Function.update mem (control + 2) cursor))
    (hScratchI : ∀ n mem, I n mem → mem (control + 3) = δ)
    (hActions : HintLocatedActions (hintNativeProgramAt S) E control table 89
      (hintNativeActionsAt S) events budget I)
    (hFinal : ∀ mem, I events.length mem → ∀ q < N,
      mem (resultMap + q) = if accept q then 1 else 0) :
    ∃ out, HaltsWithin (hintNativeProgramAt S) E
      (hintDispatchBudget (hintNativeActionsAt S) events.length budget + 29 * N + 86) state out := by
  obtain ⟨-, k, out, hstep, hpc, hcost, -⟩ :=
    hintNativeRootAt_sem S E state δ β header control hintMap resultMap listBase table N events
      budget I accept hdr hPc hWordState hDelta hBeta hSource hLength hBetaSource hSpan
      hSeparate hControl hScratchSep hScratchSource hOut hOutSpan hTable hTags hInit hCursor
      hScratchI hActions hFinal
  exact ⟨out, k, by exact_mod_cast hcost, hstep, hintNativeRootAt_halt S out hpc⟩

/-! ## 11. The exported composable contract -/

/-- **The contract exactly as published** (node `HintDecBase20261122`, id
`31701c4d-599c-40af-968f-80990517c61d`), under a non-clashing name: this is the shape that
`downBlkSemAtPublished_hintNativeRootAt_false` refutes for the real decoder.  The amended, satisfiable
contracts are `DownBlkSemAtSingle` (§14, one window) and `DownBlkSemAtW` (§15, two windows).  It is the
published `DownBlkSem` shape with the caller's per-child table *pinned* by `HintRootHeaderAt`
(a `∀ dt` with only a window equation cannot make the decoder finish in a table-independent
bound: the normalise count and the dispatch count are table scalars).  The `det` base is `δ` and
the payload base `β`; the output clause is dropped (6.5's column stage gets correctness from
`hint_decode_correct`) and the two-sided frame is kept. -/
def DownBlkSemAtPublished (Sdec : Stmt) (E : RAMEnv) (T : ℝ) (Bw : ℕ) {N Ms : ℕ}
    (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)) : Prop :=
  ∀ (G : Program) (base δ β : ℕ), β + wordsOf E.W Ms ≤ 2 ^ E.W →
  ∀ (header control hintMap resultMap listBase table count : ℕ)
    (y : Fin Ms → ZMod 2) (J : List ℕ) (s : RAMState),
    At G base (Sdec.compile base) → s.pc = base → δ + Bw ≤ 2 ^ E.W →
    HintRootHeaderAt E δ header control hintMap resultMap listBase table count N →
    s.regs 14 = δ → s.regs 15 = β →
    (∀ q < wordsOf E.W Ms, s.mem (β + q) = packMem E.W y q) →
    ∃ (k : ℕ) (out : RAMState), (k : ℝ) ≤ T ∧ (step G E)^[k] s = out ∧
      out.pc = base + Sdec.len ∧
      (∀ a, a < β ∨ β + wordsOf E.W Ms ≤ a → out.mem a = s.mem a)

/-- **Non-vacuity: the `δ = β = 0` instance of `DownBlkSemAt` is 5.1's own halting conjunct.**
At the standard `decoderStart` state (every register but `r0` is `0`), the header at `δ = 0` is an
ordinary `HintRootHeader`, the table window is `E.det`, and the conclusion is exactly
`∃ s', HaltsWithin (Sdec.compile 0 ++ [halt]) E T (decoderStart E.W y J) s'`. -/
theorem downBlkSemAtPublished_betaZero {Sdec : Stmt} {E : RAMEnv} {T : ℝ} {Bw N Ms : ℕ}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (h : DownBlkSemAtPublished Sdec E T Bw Hs) (hBw : Bw ≤ 2 ^ E.W)
    (hfit : wordsOf E.W Ms ≤ 2 ^ E.W)
    (header control hintMap resultMap listBase table count : ℕ)
    (hdr : HintRootHeaderAt E 0 header control hintMap resultMap listBase table count N)
    (y : Fin Ms → ZMod 2) (J : List ℕ) :
    ∃ s', HaltsWithin (Sdec.compile 0 ++ [Instr.halt]) E T (decoderStart E.W y J) s' := by
  let G : Program := Sdec.compile 0 ++ [Instr.halt]
  have hAt : At G 0 (Sdec.compile 0) := by
    intro r hr
    simpa [G] using List.getElem?_append_left (l₁ := Sdec.compile 0) (l₂ := [Instr.halt])
      (by simpa using hr)
  have hpc : (decoderStart E.W y J).pc = 0 := rfl
  have h14 : (decoderStart E.W y J).regs 14 = 0 := rfl
  have h15 : (decoderStart E.W y J).regs 15 = 0 := rfl
  have hmem : ∀ q < wordsOf E.W Ms, (decoderStart E.W y J).mem (0 + q) = packMem E.W y q := by
    intro q hq
    simp [decoderStart, initState, hintMem, hq]
  obtain ⟨k, out, hk, hstep, hpcOut, -⟩ :=
    h G 0 0 0 (by simpa using hfit) header control hintMap resultMap listBase table count
      y J (decoderStart E.W y J) hAt hpc (by simpa using hBw) hdr h14 h15 hmem
  have hlen : (Sdec.compile 0).length = Sdec.len := Stmt.length_compile Sdec 0
  have hhalt : G[out.pc]? = some Instr.halt := by
    rw [hpcOut, show 0 + Sdec.len = Sdec.len by omega]
    rw [List.getElem?_append_right (by omega : (Sdec.compile 0).length ≤ Sdec.len)]
    simp [hlen]
  refine ⟨out, k, hk, hstep, ?_⟩
  unfold Halted
  rw [hhalt]
  trivial

/-! ## 12. The dispatch frame, and the full-decoder frame

`hintLocatedDispatch_sem` returns the invariant `I` at the end of the dispatch but says nothing about
addresses the invariant does not mention.  The frame of the *whole* decoder is therefore exactly the
frame carried by `I`: if every `I n mem` agrees with the start memory outside a window, so does the
dispatch.  The same then holds for the whole `hintNativeRootAt`, because the enter and exit stages are
already framed and their written regions (the `hintMap` block, the `control` block, the `listBase`
block) sit inside the window. -/

/-- **The dispatch frame.**  If the invariant `I` pins the memory outside the window `[β, β+w)` to
the start memory, then the dispatch preserves the same frame. -/
theorem hintLocatedDispatch_sem_frame (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base old β w : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events)
    (hTags : ∀ j : Fin events.length, events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length old state)
    (hInv : I 0 state.mem) (hWordState : UpWordState E state)
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintLocatedActions P E control table (base + 19) actions events budget I)
    (hAt : At P base ((hintDispatchStmt actions).compile base)) (hPc : state.pc = base)
    (hIFrame : ∀ n memory, I n memory → ∀ a, a < β ∨ β + w ≤ a → memory a = state.mem a) :
    Sem P E base (base + (hintDispatchStmt actions).len) state (fun k out =>
      k ≤ hintDispatchBudget actions events.length budget + 9 ∧ I events.length out.mem ∧
      HintDispatchData control table events.length events.length out ∧
      (∀ a, a < β ∨ β + w ≤ a → out.mem a = state.mem a)) := by
  obtain ⟨hPc', k, out, hRun, hEnd, hCost, hInvOut, hDataOut⟩ :=
    hintLocatedDispatch_sem P E state control table base old actions events budget I hWord hControl
      hCount hTable hTags hData hInv hWordState hCursor hActions hAt hPc
  exact ⟨hPc', k, out, hRun, hEnd, hCost, hInvOut, hDataOut, hIFrame _ _ hInvOut⟩

/-- **The full-decoder frame.**  `hintNativeRootAt_sem`, with the two-sided frame of the published
`DownBlkSem` added.  The hypotheses say that the decoder's own written regions lie inside the window
`[β, β+w)`: the `hintMap` block `[hintMap, hintMap+N)`, the four `control` words
`{control, …, control+3}`, and the emitted list block `[listBase, listBase+N)`.  The dispatched
actions are covered by `hIFrame`, the per-action frame obligation the caller discharges together with
`hActions`. -/
theorem hintNativeRootAt_sem_frame (S : CRSourceBundle) (E : RAMEnv) (state : RAMState)
    (δ β w header control hintMap resultMap listBase table N : ℕ) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (accept : ℕ → Bool)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table events.length N)
    (hPc : state.pc = 0) (hWordState : UpWordState E state)
    (hDelta : state.regs 14 = δ) (hBeta : state.regs 15 = β)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W)
    (hBetaSource : β + state.regs 1 < 2 ^ E.W)
    (hSpan : β + state.regs 1 + min (state.regs 2) N ≤ 2 ^ E.W)
    (hSeparate : β + state.regs 1 + min (state.regs 2) N ≤ hintMap ∨
      hintMap + N < β + state.regs 1)
    (hControl : control + 2 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSep : control + 4 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSource : ∀ i < min (state.regs 2) N, β + state.regs 1 + i ≠ control + 3)
    (hOut : listBase + N ≤ resultMap) (hOutSpan : resultMap + N ≤ 2 ^ E.W)
    (hTable : HintDispatchTable E table events)
    (hTags : ∀ j : Fin events.length, events[j.val].1 < (hintNativeActionsAt S).length)
    (hInit : ∀ mem,
      (∀ q < N, mem (hintMap + q) = hintStampValue E (β + state.regs 1)
        (min (state.regs 2) N) state.mem q) →
      (∀ address, (address < hintMap ∨ hintMap + N < address) →
        address ≠ control → address ≠ control + 1 → address ≠ control + 3 →
        mem address = state.mem address) →
      mem (control + 3) = δ → I 0 mem)
    (hCursor : ∀ n mem cursor, I n mem → I n (Function.update mem (control + 2) cursor))
    (hScratchI : ∀ n mem, I n mem → mem (control + 3) = δ)
    (hActions : HintLocatedActions (hintNativeProgramAt S) E control table 89
      (hintNativeActionsAt S) events budget I)
    (hFinal : ∀ mem, I events.length mem → ∀ q < N,
      mem (resultMap + q) = if accept q then 1 else 0)
    (hWinHint : β ≤ hintMap) (hWinHintTop : hintMap + N < β + w)
    (hWinControl : β ≤ control) (hWinControlTop : control + 4 ≤ β + w)
    (hWinList : β ≤ listBase) (hWinListTop : listBase + N ≤ β + w)
    (hIFrame : ∀ n mem, I n mem → ∀ a, a < β ∨ β + w ≤ a → mem a = state.mem a) :
    Sem (hintNativeProgramAt S) E 0 (hintNativeRootAt S).len state (fun k out =>
      k ≤ hintDispatchBudget (hintNativeActionsAt S) events.length budget + 29 * N + 86 ∧
      outList out = hintGatherList accept N ∧
      (∀ a, a < β ∨ β + w ≤ a → out.mem a = state.mem a)) := by
  let P := hintNativeProgramAt S
  let actions := hintNativeActionsAt S
  let dispatch := hintDispatchStmt actions
  obtain ⟨hEnterAt, hRestAt⟩ := At.seqStmt (hintNativeRootAt_at S)
  change At P 0 (hintRootEnterAt.compile 0) at hEnterAt
  change At P 70 ((Stmt.seq dispatch hintRootExitAt).compile 70) at hRestAt
  obtain ⟨hDispatchAt, hExitAt⟩ := At.seqStmt hRestAt
  change At P 70 (dispatch.compile 70) at hDispatchAt
  change At P (70 + dispatch.len) (hintRootExitAt.compile (70 + dispatch.len)) at hExitAt
  obtain ⟨_, ke, first, hRunFirst, hFirstPc, hFirstCost, hData, hScratchFirst, hHints, hFrame⟩ :=
    hintRootEnterAt_sem P E state δ β header control hintMap resultMap listBase table
      events.length N 0 hdr hDelta hBeta hSource hLength hBetaSource hSpan hSeparate hControl
      hScratchSep hScratchSource hEnterAt hPc
  have hWord := hdr.word
  have hWordFirst : UpWordState E first := hRunFirst ▸ upIterate_word_bound P E state ke hWordState
  -- the enter frame, translated to the window
  have hFirstFrame : ∀ a, a < β ∨ β + w ≤ a → first.mem a = state.mem a := by
    intro a ha
    refine hFrame a ?_ ?_ ?_ ?_
    · rcases ha with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · omega
    · omega
    · omega
  obtain ⟨_, kd, middle, hRunDispatch, hMiddlePc, hDispatchCost, hInv, hMiddleData,
      hDispatchFrame⟩ :=
    hintLocatedDispatch_sem_frame P E first control table 70 (first.mem (control + 2)) β w
      actions events budget I (by omega) hdr.control_span hdr.count_fit hTable hTags hData
      (hInit _ hHints hFrame hScratchFirst) hWordFirst hCursor hActions hDispatchAt hFirstPc
      (fun n mem hI a ha => (hIFrame n mem hI a ha).trans (hFirstFrame a ha).symm)
  have hMiddleCtx : middle.regs 14 = control := hMiddleData.context
  have hMiddleScratch : middle.mem (control + 3) = δ := hScratchI _ _ hInv
  obtain ⟨_, ko, out, hRunExit, hEnd, hExitCost, hList, hExitFrame⟩ :=
    hintRootExitAt_sem P E middle δ header control hintMap resultMap listBase table
      events.length N (70 + dispatch.len) hdr hMiddleCtx hMiddleScratch hOut hOutSpan accept
      (hFinal _ hInv) hExitAt hMiddlePc
  -- the exit frame, translated to the window
  have hOutFrame : ∀ a, a < β ∨ β + w ≤ a → out.mem a = state.mem a := by
    intro a ha
    refine (hExitFrame a ?_).trans ((hDispatchFrame a ha).trans (hFirstFrame a ha))
    rcases ha with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  refine ⟨hPc, ko + (kd + ke), out, hintIterate_then (step P E)
    (hintIterate_then (step P E) hRunFirst hRunDispatch) hRunExit, ?_, ?_, hList, hOutFrame⟩
  · change out.pc = 70 + (dispatch.len + 30)
    omega
  · change ko + (kd + ke) ≤ hintDispatchBudget actions events.length budget + 29 * N + 86
    omega

/-- The frame in the vocabulary of the published contract: the window is the payload window
`[β, β + wordsOf E.W Ms)`. -/
theorem hintNativeRootAt_sem_frame_words (S : CRSourceBundle) (E : RAMEnv) (state : RAMState)
    (δ β header control hintMap resultMap listBase table N Ms : ℕ) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (accept : ℕ → Bool)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table events.length N)
    (hPc : state.pc = 0) (hWordState : UpWordState E state)
    (hDelta : state.regs 14 = δ) (hBeta : state.regs 15 = β)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W)
    (hBetaSource : β + state.regs 1 < 2 ^ E.W)
    (hSpan : β + state.regs 1 + min (state.regs 2) N ≤ 2 ^ E.W)
    (hSeparate : β + state.regs 1 + min (state.regs 2) N ≤ hintMap ∨
      hintMap + N < β + state.regs 1)
    (hControl : control + 2 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSep : control + 4 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSource : ∀ i < min (state.regs 2) N, β + state.regs 1 + i ≠ control + 3)
    (hOut : listBase + N ≤ resultMap) (hOutSpan : resultMap + N ≤ 2 ^ E.W)
    (hTable : HintDispatchTable E table events)
    (hTags : ∀ j : Fin events.length, events[j.val].1 < (hintNativeActionsAt S).length)
    (hInit : ∀ mem,
      (∀ q < N, mem (hintMap + q) = hintStampValue E (β + state.regs 1)
        (min (state.regs 2) N) state.mem q) →
      (∀ address, (address < hintMap ∨ hintMap + N < address) →
        address ≠ control → address ≠ control + 1 → address ≠ control + 3 →
        mem address = state.mem address) →
      mem (control + 3) = δ → I 0 mem)
    (hCursor : ∀ n mem cursor, I n mem → I n (Function.update mem (control + 2) cursor))
    (hScratchI : ∀ n mem, I n mem → mem (control + 3) = δ)
    (hActions : HintLocatedActions (hintNativeProgramAt S) E control table 89
      (hintNativeActionsAt S) events budget I)
    (hFinal : ∀ mem, I events.length mem → ∀ q < N,
      mem (resultMap + q) = if accept q then 1 else 0)
    (hWinHint : β ≤ hintMap) (hWinHintTop : hintMap + N < β + wordsOf E.W Ms)
    (hWinControl : β ≤ control) (hWinControlTop : control + 4 ≤ β + wordsOf E.W Ms)
    (hWinList : β ≤ listBase) (hWinListTop : listBase + N ≤ β + wordsOf E.W Ms)
    (hIFrame : ∀ n mem, I n mem → ∀ a, a < β ∨ β + wordsOf E.W Ms ≤ a →
      mem a = state.mem a) :
    Sem (hintNativeProgramAt S) E 0 (hintNativeRootAt S).len state (fun k out =>
      k ≤ hintDispatchBudget (hintNativeActionsAt S) events.length budget + 29 * N + 86 ∧
      outList out = hintGatherList accept N ∧
      (∀ a, a < β ∨ β + wordsOf E.W Ms ≤ a → out.mem a = state.mem a)) :=
  hintNativeRootAt_sem_frame S E state δ β (wordsOf E.W Ms) header control hintMap resultMap
    listBase table N events budget I accept hdr hPc hWordState hDelta hBeta hSource hLength
    hBetaSource hSpan hSeparate hControl hScratchSep hScratchSource hOut hOutSpan hTable hTags
    hInit hCursor hScratchI hActions hFinal hWinHint hWinHintTop hWinControl hWinControlTop
    hWinList hWinListTop hIFrame

/-- **The scratch word survives the run.**  At `N = 0` the exit stage preserves *every* address (its
frame is `CRMemFrame listBase listBase`), and the dispatch keeps the invariant, so the word
`control + 3` that the enter stage set to `δ` still holds `δ` at the end.  This is the fact that the
published contract's frame, applied to an address the decoder definitely writes, contradicts. -/
theorem hintNativeRootAt_sem_scratch (S : CRSourceBundle) (E : RAMEnv) (state : RAMState)
    (δ β header control hintMap resultMap listBase table N : ℕ) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (accept : ℕ → Bool)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table events.length N)
    (hPc : state.pc = 0) (hWordState : UpWordState E state)
    (hDelta : state.regs 14 = δ) (hBeta : state.regs 15 = β)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W)
    (hBetaSource : β + state.regs 1 < 2 ^ E.W)
    (hSpan : β + state.regs 1 + min (state.regs 2) N ≤ 2 ^ E.W)
    (hSeparate : β + state.regs 1 + min (state.regs 2) N ≤ hintMap ∨
      hintMap + N < β + state.regs 1)
    (hControl : control + 2 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSep : control + 4 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSource : ∀ i < min (state.regs 2) N, β + state.regs 1 + i ≠ control + 3)
    (hOut : listBase + N ≤ resultMap) (hOutSpan : resultMap + N ≤ 2 ^ E.W)
    (hTable : HintDispatchTable E table events)
    (hTags : ∀ j : Fin events.length, events[j.val].1 < (hintNativeActionsAt S).length)
    (hInit : ∀ mem,
      (∀ q < N, mem (hintMap + q) = hintStampValue E (β + state.regs 1)
        (min (state.regs 2) N) state.mem q) →
      (∀ address, (address < hintMap ∨ hintMap + N < address) →
        address ≠ control → address ≠ control + 1 → address ≠ control + 3 →
        mem address = state.mem address) →
      mem (control + 3) = δ → I 0 mem)
    (hCursor : ∀ n mem cursor, I n mem → I n (Function.update mem (control + 2) cursor))
    (hScratchI : ∀ n mem, I n mem → mem (control + 3) = δ)
    (hActions : HintLocatedActions (hintNativeProgramAt S) E control table 89
      (hintNativeActionsAt S) events budget I)
    (hFinal : ∀ mem, I events.length mem → ∀ q < N,
      mem (resultMap + q) = if accept q then 1 else 0)
    (hListBig : control + 3 < listBase) :
    Sem (hintNativeProgramAt S) E 0 (hintNativeRootAt S).len state (fun k out =>
      out.mem (control + 3) = δ) := by
  let P := hintNativeProgramAt S
  let actions := hintNativeActionsAt S
  let dispatch := hintDispatchStmt actions
  obtain ⟨hEnterAt, hRestAt⟩ := At.seqStmt (hintNativeRootAt_at S)
  change At P 0 (hintRootEnterAt.compile 0) at hEnterAt
  change At P 70 ((Stmt.seq dispatch hintRootExitAt).compile 70) at hRestAt
  obtain ⟨hDispatchAt, hExitAt⟩ := At.seqStmt hRestAt
  change At P 70 (dispatch.compile 70) at hDispatchAt
  change At P (70 + dispatch.len) (hintRootExitAt.compile (70 + dispatch.len)) at hExitAt
  obtain ⟨_, ke, first, hRunFirst, hFirstPc, -, hData, hScratchFirst, hHints, hFrame⟩ :=
    hintRootEnterAt_sem P E state δ β header control hintMap resultMap listBase table
      events.length N 0 hdr hDelta hBeta hSource hLength hBetaSource hSpan hSeparate hControl
      hScratchSep hScratchSource hEnterAt hPc
  have hWord := hdr.word
  have hWordFirst : UpWordState E first := hRunFirst ▸ upIterate_word_bound P E state ke hWordState
  obtain ⟨_, kd, middle, hRunDispatch, hMiddlePc, -, hInv, hMiddleData⟩ :=
    hintLocatedDispatch_sem P E first control table 70 (first.mem (control + 2))
      actions events budget I (by omega) hdr.control_span hdr.count_fit hTable hTags hData
      (hInit _ hHints hFrame hScratchFirst) hWordFirst hCursor hActions hDispatchAt hFirstPc
  have hMiddleCtx : middle.regs 14 = control := hMiddleData.context
  have hMiddleScratch : middle.mem (control + 3) = δ := hScratchI _ _ hInv
  obtain ⟨_, ko, out, hRunExit, hEnd, -, hList, hExitFrame⟩ :=
    hintRootExitAt_sem P E middle δ header control hintMap resultMap listBase table
      events.length N (70 + dispatch.len) hdr hMiddleCtx hMiddleScratch hOut hOutSpan accept
      (hFinal _ hInv) hExitAt hMiddlePc
  refine ⟨hPc, ko + (kd + ke), out, hintIterate_then (step P E)
    (hintIterate_then (step P E) hRunFirst hRunDispatch) hRunExit, ?_, ?_⟩
  · change out.pc = 70 + (dispatch.len + 30)
    omega
  · change out.mem (control + 3) = δ
    rw [hExitFrame _ (Or.inl hListBig), hMiddleScratch]

/-! ## 13. The published frame is not a consequence of the program: a machine-checked obstruction

The frame clause of `DownBlkSemAt` quantifies over the caller's `hintMap`, `control`, `resultMap`,
`listBase`, and over `β`, with no hypothesis relating them.  The decoder, however, *writes* the
`hintMap` block, the `control` block and the `listBase` block, so the frame can only hold if those
regions happen to sit inside the payload window `[β, β + wordsOf E.W Ms)` — which the contract does
not say.  The theorems below make that precise: at a concrete environment the run writes the scratch
word `control + 3` (which the enter stage sets to `δ` and the remaining stages only ever preserve),
while an instantiation with `Ms = 0` (empty window) makes the contract's frame demand that the same
word be unchanged. -/

/-- A `halt` is a fixed point of `step`. -/
theorem step_halt_self_at {P : Program} {E : RAMEnv} {s : RAMState}
    (h : P[s.pc]? = some Instr.halt) : step P E s = s := by
  simp [step, h]

/-- A run that reaches a `halt` never moves again. -/
theorem iterate_halt_self_at {P : Program} {E : RAMEnv} {s : RAMState}
    (h : P[s.pc]? = some Instr.halt) (k : ℕ) : (step P E)^[k] s = s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      exact step_halt_self_at h

/-- Two runs of the same deterministic machine that both end at a `halt` end in the same state. -/
theorem iterate_eq_of_halt {P : Program} {E : RAMEnv} {s out out' : RAMState} {k k' : ℕ}
    (h : P[out.pc]? = some Instr.halt) (h' : P[out'.pc]? = some Instr.halt)
    (hk : (step P E)^[k] s = out) (hk' : (step P E)^[k'] s = out') : out = out' := by
  rcases le_total k k' with hle | hle
  · have h2 : out' = (step P E)^[k' - k] out := by
      calc out' = (step P E)^[k'] s := hk'.symm
        _ = (step P E)^[k' - k + k] s :=
            congrArg (fun j => (step P E)^[j] s) (by omega)
        _ = (step P E)^[k' - k] ((step P E)^[k] s) :=
            Function.iterate_add_apply (step P E) (k' - k) k s
        _ = (step P E)^[k' - k] out := by rw [hk]
    rw [iterate_halt_self_at h] at h2
    exact h2.symm
  · have h2 : out = (step P E)^[k - k'] out' := by
      calc out = (step P E)^[k] s := hk.symm
        _ = (step P E)^[k - k' + k'] s :=
            congrArg (fun j => (step P E)^[j] s) (by omega)
        _ = (step P E)^[k - k'] ((step P E)^[k'] s) :=
            Function.iterate_add_apply (step P E) (k - k') k' s
        _ = (step P E)^[k - k'] out' := by rw [hk']
    rw [iterate_halt_self_at h'] at h2
    exact h2

/-- The concrete `det` table of the obstruction: `δ = 5`, `header = 32`, `control = 0`,
`hintMap = 4`, `resultMap = listBase = 10`, `table = 20`, `count = N = 0`. -/
def downBlkRefDet : ℕ → ℕ :=
  fun n => if n = 8 then 27 else if n = 41 then 4 else if n = 42 then 0 else
    if n = 43 then 0 else if n = 44 then 20 else if n = 45 then 0 else
      if n = 46 then 10 else if n = 47 then 10 else 0

/-- The word width is `8`. -/
def downBlkRefEnv : RAMEnv := detEnv 8 downBlkRefDet

/-- The start state: `r14 = 5`, every other register `0`, zero memory. -/
def downBlkRefState : RAMState :=
  { pc := 0, regs := fun r => if r = (14 : Fin 16) then 5 else 0, mem := fun _ => 0 }

theorem downBlkRef_normalize : HintNormalizeTable downBlkRefEnv 32 4 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [downBlkRefEnv, detEnv, downBlkRefDet]

theorem downBlkRef_header : HintRootHeaderAt downBlkRefEnv 5 32 0 4 10 10 20 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, downBlkRef_normalize, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [downBlkRefEnv, detEnv, downBlkRefDet]

theorem downBlkRef_wordState : UpWordState downBlkRefEnv downBlkRefState := by
  refine ⟨?_, ?_⟩
  · intro r
    dsimp [downBlkRefState, downBlkRefEnv, detEnv]
    split_ifs <;> norm_num
  · intro a
    dsimp [downBlkRefState]
    norm_num

/-- **The run of the real decoder at the obstruction's data.**  It ends at the trailing `halt` with
`5` still in the scratch word `3 = control + 3`. -/
theorem downBlkRef_run (S : CRSourceBundle) :
    ∃ (k : ℕ) (out : RAMState),
      (step (hintNativeProgramAt S) downBlkRefEnv)^[k] downBlkRefState = out ∧
      out.pc = (hintNativeRootAt S).len ∧ out.mem 3 = 5 := by
  obtain ⟨-, k, out, hstep, hpc, hmem⟩ :=
    hintNativeRootAt_sem_scratch S downBlkRefEnv downBlkRefState 5 0 32 0 4 10 10 20 0
      [] (fun _ => 0) (fun _ mem => mem 3 = 5) (fun _ => true) downBlkRef_header rfl
      downBlkRef_wordState
      (by simp [downBlkRefState]) (by simp [downBlkRefState])
      (by simp [downBlkRefState]) (by simp [downBlkRefState])
      (by simp [downBlkRefState]) (by simp [downBlkRefState])
      (by simp [downBlkRefState]) (by simp [downBlkRefState])
      (by simp [downBlkRefState]) (by simp [downBlkRefState])
      (by norm_num) (by norm_num [downBlkRefEnv, detEnv])
      (by refine ⟨by norm_num [downBlkRefEnv, detEnv], ?_, ?_, ?_⟩ <;>
            intro j <;> exact absurd j.isLt (by simp))
      (by intro j; exact absurd j.isLt (by simp))
      (by intro mem _ _ h; simpa using h)
      (by intro n mem c h; rw [Function.update_of_ne (by decide : (3 : ℕ) ≠ 0 + 2)]; exact h)
      (by intro n mem h; exact h)
      (by intro j; exact absurd j.isLt (by simp))
      (by intro mem _ q hq; omega)
      (by norm_num)
  exact ⟨k, out, hstep, hpc, by simpa using hmem⟩

/-- **The published `DownBlkSemAt` is false for the real decoder.**  Take one payload word
(`Ms = 1`, `β = 0`, so the window is `{0}`), a degenerate header (`N = 0`, `Bw = 0`) and the
zero payload; then the frame of `DownBlkSemAt` demands that the whole memory except address `0` be
preserved, while the decoder writes `δ = 5` into the scratch word `control + 3 = 3`. -/
theorem downBlkSemAtPublished_hintNativeRootAt_false (S : CRSourceBundle) (T : ℝ)
    {N Ms : ℕ} (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2))
    (hN : N = 0) (hMs : Ms = 1) :
    ¬ DownBlkSemAtPublished (hintNativeRootAt S) downBlkRefEnv T 0 Hs := by
  intro hc
  subst hN
  subst hMs
  obtain ⟨k, out, hstep, hpc, hmem⟩ := downBlkRef_run S
  obtain ⟨k', out', -, hstep', hpc', hframe'⟩ :=
    hc (hintNativeProgramAt S) 0 5 0 (by norm_num [wordsOf, downBlkRefEnv, detEnv])
      32 0 4 10 10 20 0 (0 : Fin 1 → ZMod 2) [] downBlkRefState (hintNativeRootAt_at S) rfl
      (by norm_num [downBlkRefEnv, detEnv]) downBlkRef_header rfl rfl
      (by
        intro q hq
        have hq0 : q = 0 := by simpa [wordsOf, downBlkRefEnv, detEnv] using hq
        subst hq0
        simp [packMem, downBlkRefState])
  have hhaltAt : (hintNativeProgramAt S)[(hintNativeRootAt S).len]? = some Instr.halt := by
    have hlen : ((hintNativeRootAt S).compile 0).length = (hintNativeRootAt S).len :=
      Stmt.length_compile _ 0
    simp only [hintNativeProgramAt]
    rw [← hlen, List.getElem?_append_right (by omega :
      ((hintNativeRootAt S).compile 0).length ≤ ((hintNativeRootAt S).compile 0).length)]
    simp
  have hpc'' : out'.pc = (hintNativeRootAt S).len := by rw [hpc']; omega
  have houtEq : out' = out :=
    iterate_eq_of_halt (by rw [hpc'']; exact hhaltAt) (by rw [hpc]; exact hhaltAt) hstep' hstep
  have hframe := hframe' 3 (Or.inr (by norm_num [wordsOf, downBlkRefEnv, detEnv]))
  rw [houtEq] at hframe
  have hzero : downBlkRefState.mem 3 = 0 := rfl
  rw [hzero] at hframe
  omega

/-! ## 14. The single-window amendment (superseded by §15)

The published `DownBlkSemAt` (`DownBlkSemAtPublished` above) measures the frame against the *payload*
width `wordsOf E.W Ms`, but the decoder writes three further blocks — the `hintMap` bitmap of `N`
words, the four `control` words and the emitted `listBase` block of `N` words — so no containment
hypothesis can make the frame true.  The amendment makes the window a *parameter*: `w` is the
caller's block footprint, `wordsOf E.W Ms ≤ w` says it contains the payload, and the six containments
place the decoder's own blocks inside it.  The `hintMap` containment is **strict**
(`hintMap + N < β + w`): the normalise stage's frame is `CRMemFrame hintMap (hintMap + N + 1)`, i.e.
it may write `hintMap + N`, which at equality would fall exactly on the window boundary and break the
frame. -/

/-- **The amended per-block decoder contract.**  `w` is the caller's block footprint; `I` is the
caller's dispatch invariant, whose frame is the seventh premise. -/
def DownBlkSemAtSingle (Sdec : Stmt) (E : RAMEnv) (T : ℝ) (Bw w : ℕ)
    (I : ℕ → (ℕ → ℕ) → Prop) {N Ms : ℕ}
    (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)) : Prop :=
  ∀ (G : Program) (base δ β : ℕ), wordsOf E.W Ms ≤ w → β + w ≤ 2 ^ E.W →
  ∀ (header control hintMap resultMap listBase table count : ℕ)
    (y : Fin Ms → ZMod 2) (J : List ℕ) (s : RAMState),
    At G base (Sdec.compile base) → s.pc = base → δ + Bw ≤ 2 ^ E.W →
    HintRootHeaderAt E δ header control hintMap resultMap listBase table count N →
    s.regs 14 = δ → s.regs 15 = β →
    (∀ q < wordsOf E.W Ms, s.mem (β + q) = packMem E.W y q) →
    β ≤ hintMap → hintMap + N < β + w →
    β ≤ control → control + 4 ≤ β + w →
    β ≤ listBase → listBase + N ≤ β + w →
    (∀ n mem, I n mem → ∀ a, a < β ∨ β + w ≤ a → mem a = s.mem a) →
    ∃ (k : ℕ) (out : RAMState), (k : ℝ) ≤ T ∧ (step G E)^[k] s = out ∧
      out.pc = base + Sdec.len ∧
      (∀ a, a < β ∨ β + w ≤ a → out.mem a = s.mem a)

/-- **The `δ = β = 0` reduction of the amended contract is still 5.1's own halting conjunct.** -/
theorem downBlkSemAtSingle_betaZero {Sdec : Stmt} {E : RAMEnv} {T : ℝ} {Bw w N Ms : ℕ}
    {I : ℕ → (ℕ → ℕ) → Prop}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (h : DownBlkSemAtSingle Sdec E T Bw w I Hs) (hBw : Bw ≤ 2 ^ E.W)
    (hfit : wordsOf E.W Ms ≤ w) (hW : w ≤ 2 ^ E.W)
    (y : Fin Ms → ZMod 2) (J : List ℕ)
    (header control hintMap resultMap listBase table count : ℕ)
    (hdr : HintRootHeaderAt E 0 header control hintMap resultMap listBase table count N)
    (hHintTop : hintMap + N < w) (hControlTop : control + 4 ≤ w)
    (hListTop : listBase + N ≤ w)
    (hI : ∀ n mem, I n mem → ∀ a, a < 0 ∨ 0 + w ≤ a →
      mem a = (decoderStart E.W y J).mem a) :
    ∃ s', HaltsWithin (Sdec.compile 0 ++ [Instr.halt]) E T (decoderStart E.W y J) s' := by
  let G : Program := Sdec.compile 0 ++ [Instr.halt]
  have hAt : At G 0 (Sdec.compile 0) := by
    intro r hr
    simpa [G] using List.getElem?_append_left (l₁ := Sdec.compile 0) (l₂ := [Instr.halt])
      (by simpa using hr)
  have hpc : (decoderStart E.W y J).pc = 0 := rfl
  have h14 : (decoderStart E.W y J).regs 14 = 0 := rfl
  have h15 : (decoderStart E.W y J).regs 15 = 0 := rfl
  have hmem : ∀ q < wordsOf E.W Ms, (decoderStart E.W y J).mem (0 + q) = packMem E.W y q := by
    intro q hq
    simp [decoderStart, initState, hintMem, hq]
  obtain ⟨k, out, hk, hstep, hpcOut, -⟩ :=
    h G 0 0 0 hfit (by simpa using hW) header control hintMap resultMap listBase table count
      y J (decoderStart E.W y J) hAt hpc (by simpa using hBw) hdr h14 h15 hmem
      (by omega) (by simpa using hHintTop) (by omega) (by simpa using hControlTop)
      (by omega) (by simpa using hListTop) hI
  have hlen : (Sdec.compile 0).length = Sdec.len := Stmt.length_compile Sdec 0
  have hhalt : G[out.pc]? = some Instr.halt := by
    rw [hpcOut, show 0 + Sdec.len = Sdec.len by omega]
    rw [List.getElem?_append_right (by omega : (Sdec.compile 0).length ≤ Sdec.len)]
    simp [hlen]
  exact ⟨out, k, hk, hstep, by unfold Halted; rw [hhalt]; trivial⟩

/-- **How large the footprint must be.**  The six containments alone force `w` to hold the `hintMap`
block with one word of slack, the four `control` words and the `listBase` block: `w ≥ N + 1` and
`w ≥ 4` (and `w ≥ N` from the list block).  Nothing else is forced: if the payload already needs more
words than that, no extra room is required. -/
theorem footprint_bounds_single {β w N : ℕ} {hintMap control listBase : ℕ}
    (hHint : β ≤ hintMap) (hHintTop : hintMap + N < β + w)
    (hControl : β ≤ control) (hControlTop : control + 4 ≤ β + w)
    (hList : β ≤ listBase) (hListTop : listBase + N ≤ β + w) :
    N + 1 ≤ w ∧ 4 ≤ w ∧ N ≤ w := by
  omega

/-- **The footprint with the blocks laid out consecutively after the payload.**  If `hintMap`'s block
is followed by the control block, which is followed by the list block, then the window must hold all
of them: `w ≥ 2 * N + 4`. -/
theorem footprint_bounds_packed_single {β w N : ℕ} {hintMap control listBase : ℕ}
    (hHint : β ≤ hintMap) (hHintTop : hintMap + N < β + w)
    (hPacked₁ : hintMap + N ≤ control) (hPacked₂ : control + 4 ≤ listBase)
    (hListTop : listBase + N ≤ β + w) :
    2 * N + 4 ≤ w := by
  omega

/-! ### Non-vacuity of the amended contract -/

/-- The `det` table of the non-vacuity witness: `δ = 5`, `header = 32`, `hintMap = 2`,
`N = 4`, `control = 7`, `table = 20`, `count = 0`, `resultMap = 20`, `listBase = 12`. -/
def winDet : ℕ → ℕ :=
  fun n => if n = 8 then 27 else if n = 41 then 2 else if n = 42 then 4 else
    if n = 43 then 7 else if n = 44 then 20 else if n = 45 then 0 else
      if n = 46 then 20 else if n = 47 then 12 else 0

def winEnv : RAMEnv := detEnv 8 winDet

/-- A genuinely non-zero payload: the first of the eight syndrome bits is set. -/
def winY : Fin 8 → ZMod 2 := fun i => if i = (0 : Fin 8) then 1 else 0

theorem winY_ne_zero : winY ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 8)
  simp [winY] at h0

theorem winNormalize : HintNormalizeTable winEnv 32 2 4 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [winEnv, detEnv, winDet]

theorem winHeader : HintRootHeaderAt winEnv 5 32 7 2 20 12 20 0 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, winNormalize, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [winEnv, detEnv, winDet]

/-- **The amended contract's premises are jointly satisfiable with a real (non-zero) payload.**  The
footprint is `w = 20` against a payload of `wordsOf 8 8 = 1` word — the `19` extra words are the
`hintMap`/`control`/`listBase` blocks, i.e. the extra is `Θ(N)`, not `Θ(Ms)`. -/
theorem downBlkSemAtSingle_premises_nonvacuous :
    ∃ (E : RAMEnv) (δ β w header control hintMap resultMap listBase table count N Ms : ℕ)
      (y : Fin Ms → ZMod 2),
      y ≠ 0 ∧ wordsOf E.W Ms ≤ w ∧ β + w ≤ 2 ^ E.W ∧
      HintRootHeaderAt E δ header control hintMap resultMap listBase table count N ∧
      β ≤ hintMap ∧ hintMap + N < β + w ∧
      β ≤ control ∧ control + 4 ≤ β + w ∧
      β ≤ listBase ∧ listBase + N ≤ β + w := by
  refine ⟨winEnv, 5, 0, 20, 32, 7, 2, 20, 12, 20, 0, 4, 8, winY, winY_ne_zero, ?_, ?_, winHeader,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [wordsOf, winEnv, detEnv]

/-- **An inhabitant of the amended contract.**  For a program that leaves memory alone the frame is
immediate; what the witness shows is that the amended statement is consistent (the published one is
not, by `downBlkSemAtPublished_hintNativeRootAt_false`).  A *closed* inhabitant for the real decoder
is impossible for the same reason as before — the contract's premises do not include the driver
hypotheses (`hSource`, `hWordState`, `hActions`, …), so the decoder's own export is the conditional
`hintNativeRootAt_sem_frame`, and `DownBlkSemAtSingle` is meant to be *assumed* by 6.5's column stage in
the same way as `UpBlkSem`/`CrSem`. -/
theorem downBlkSemAtSingle_nonvacuous (E : RAMEnv) {T : ℝ} (hT : 0 ≤ T) (Bw w N Ms : ℕ)
    (I : ℕ → (ℕ → ℕ) → Prop)
    (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)) :
    DownBlkSemAtSingle (.code []) E T Bw w I Hs := by
  intro G base δ β hfit hspan header control hintMap resultMap listBase table count y J s
    hAt hpc hfit' hdr h14 h15 hmem h1 h2 h3 h4 h5 h6 hI
  refine ⟨0, s, by simpa using hT, rfl, ?_, fun a _ => rfl⟩
  rw [hpc]
  simp [Stmt.len]

/-! ## 15. The two-window contract: one shared workspace for all children

The single-window amendment of §14 forces the payload and the decoder's own blocks into one interval,
which makes the block `Θ(N)` words even though the payload is only `Θ(N / lg n)` words; applied to
`ℓ` children that would multiply 6.5's sketch length by `Θ(lg n)`.  The decoder's workspace is however
*transient*: the children are decoded one after the other, so a single workspace can serve all of
them, provided the contract separates the two intervals

* the **payload window** `[β, β + ms)`, which holds the stored syndrome and must survive, and
* the **workspace window** `[γ, γ + ws)`, which holds the `hintMap` bitmap, the four `control` words
  and the emitted `listBase` block, and may be overwritten freely between children.

The frame that is *true* of the decoder is "nothing outside the workspace changes".  A frame stated
over the payload window *alone* would be false here: the two windows are disjoint, so the workspace
lies outside the payload window, yet the decoder writes it.  The payload clause is instead a
*consequence* of the workspace frame plus disjointness, and the theorems below state both, because
the payload clause is what 6.5 needs. -/

/-- **The two-window frame of the whole decoder.**  Nothing outside the workspace `[γ, γ+ws)`
changes, and the payload window `[β, β+ms)` — disjoint from it — is preserved. -/
theorem hintNativeRootAt_sem_ws_frame (S : CRSourceBundle) (E : RAMEnv) (state : RAMState)
    (δ β γ ms ws header control hintMap resultMap listBase table N : ℕ) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (accept : ℕ → Bool)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table events.length N)
    (hPc : state.pc = 0) (hWordState : UpWordState E state)
    (hDelta : state.regs 14 = δ) (hBeta : state.regs 15 = β)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W)
    (hBetaSource : β + state.regs 1 < 2 ^ E.W)
    (hSpan : β + state.regs 1 + min (state.regs 2) N ≤ 2 ^ E.W)
    (hSeparate : β + state.regs 1 + min (state.regs 2) N ≤ hintMap ∨
      hintMap + N < β + state.regs 1)
    (hControl : control + 2 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSep : control + 4 ≤ hintMap ∨ hintMap + N < control)
    (hScratchSource : ∀ i < min (state.regs 2) N, β + state.regs 1 + i ≠ control + 3)
    (hOut : listBase + N ≤ resultMap) (hOutSpan : resultMap + N ≤ 2 ^ E.W)
    (hTable : HintDispatchTable E table events)
    (hTags : ∀ j : Fin events.length, events[j.val].1 < (hintNativeActionsAt S).length)
    (hInit : ∀ mem,
      (∀ q < N, mem (hintMap + q) = hintStampValue E (β + state.regs 1)
        (min (state.regs 2) N) state.mem q) →
      (∀ address, (address < hintMap ∨ hintMap + N < address) →
        address ≠ control → address ≠ control + 1 → address ≠ control + 3 →
        mem address = state.mem address) →
      mem (control + 3) = δ → I 0 mem)
    (hCursor : ∀ n mem cursor, I n mem → I n (Function.update mem (control + 2) cursor))
    (hScratchI : ∀ n mem, I n mem → mem (control + 3) = δ)
    (hActions : HintLocatedActions (hintNativeProgramAt S) E control table 89
      (hintNativeActionsAt S) events budget I)
    (hFinal : ∀ mem, I events.length mem → ∀ q < N,
      mem (resultMap + q) = if accept q then 1 else 0)
    (hWinHint : γ ≤ hintMap) (hWinHintTop : hintMap + N < γ + ws)
    (hWinControl : γ ≤ control) (hWinControlTop : control + 4 ≤ γ + ws)
    (hWinList : γ ≤ listBase) (hWinListTop : listBase + N ≤ γ + ws)
    (hDisj : β + ms ≤ γ ∨ γ + ws ≤ β)
    (hIFrame : ∀ n mem, I n mem → ∀ a, a < γ ∨ γ + ws ≤ a → mem a = state.mem a) :
    Sem (hintNativeProgramAt S) E 0 (hintNativeRootAt S).len state (fun k out =>
      k ≤ hintDispatchBudget (hintNativeActionsAt S) events.length budget + 29 * N + 86 ∧
      outList out = hintGatherList accept N ∧
      (∀ a, a < γ ∨ γ + ws ≤ a → out.mem a = state.mem a) ∧
      (∀ a, β ≤ a → a < β + ms → out.mem a = state.mem a)) := by
  let P := hintNativeProgramAt S
  let actions := hintNativeActionsAt S
  let dispatch := hintDispatchStmt actions
  obtain ⟨hEnterAt, hRestAt⟩ := At.seqStmt (hintNativeRootAt_at S)
  change At P 0 (hintRootEnterAt.compile 0) at hEnterAt
  change At P 70 ((Stmt.seq dispatch hintRootExitAt).compile 70) at hRestAt
  obtain ⟨hDispatchAt, hExitAt⟩ := At.seqStmt hRestAt
  change At P 70 (dispatch.compile 70) at hDispatchAt
  change At P (70 + dispatch.len) (hintRootExitAt.compile (70 + dispatch.len)) at hExitAt
  obtain ⟨_, ke, first, hRunFirst, hFirstPc, hFirstCost, hData, hScratchFirst, hHints, hFrame⟩ :=
    hintRootEnterAt_sem P E state δ β header control hintMap resultMap listBase table
      events.length N 0 hdr hDelta hBeta hSource hLength hBetaSource hSpan hSeparate hControl
      hScratchSep hScratchSource hEnterAt hPc
  have hWord := hdr.word
  have hWordFirst : UpWordState E first := hRunFirst ▸ upIterate_word_bound P E state ke hWordState
  -- the enter frame, translated to the workspace window
  have hFirstFrame : ∀ a, a < γ ∨ γ + ws ≤ a → first.mem a = state.mem a := by
    intro a ha
    refine hFrame a ?_ ?_ ?_ ?_
    · rcases ha with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · omega
    · omega
    · omega
  obtain ⟨_, kd, middle, hRunDispatch, hMiddlePc, hDispatchCost, hInv, hMiddleData,
      hDispatchFrame⟩ :=
    hintLocatedDispatch_sem_frame P E first control table 70 (first.mem (control + 2)) γ ws
      actions events budget I (by omega) hdr.control_span hdr.count_fit hTable hTags hData
      (hInit _ hHints hFrame hScratchFirst) hWordFirst hCursor hActions hDispatchAt hFirstPc
      (fun n mem hI a ha => (hIFrame n mem hI a ha).trans (hFirstFrame a ha).symm)
  have hMiddleCtx : middle.regs 14 = control := hMiddleData.context
  have hMiddleScratch : middle.mem (control + 3) = δ := hScratchI _ _ hInv
  obtain ⟨_, ko, out, hRunExit, hEnd, hExitCost, hList, hExitFrame⟩ :=
    hintRootExitAt_sem P E middle δ header control hintMap resultMap listBase table
      events.length N (70 + dispatch.len) hdr hMiddleCtx hMiddleScratch hOut hOutSpan accept
      (hFinal _ hInv) hExitAt hMiddlePc
  -- the exit frame, translated to the workspace window
  have hOutFrame : ∀ a, a < γ ∨ γ + ws ≤ a → out.mem a = state.mem a := by
    intro a ha
    refine (hExitFrame a ?_).trans ((hDispatchFrame a ha).trans (hFirstFrame a ha))
    rcases ha with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  -- the payload window is disjoint from the workspace, hence untouched
  have hPayload : ∀ a, β ≤ a → a < β + ms → out.mem a = state.mem a := by
    intro a ha hb
    refine hOutFrame a ?_
    rcases hDisj with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  refine ⟨hPc, ko + (kd + ke), out, hintIterate_then (step P E)
    (hintIterate_then (step P E) hRunFirst hRunDispatch) hRunExit, ?_, ?_, hList, hOutFrame,
    hPayload⟩
  · change out.pc = 70 + (dispatch.len + 30)
    omega
  · change ko + (kd + ke) ≤ hintDispatchBudget actions events.length budget + 29 * N + 86
    omega

/-- **The amended two-window contract.**  `ms` is the caller's stored-payload extent (only
`wordsOf E.W Ms ≤ ms` is needed), `ws` the shared workspace extent.  The decoder writes only inside
`[γ, γ + ws)`, and the payload window `[β, β + ms)` — required disjoint — is preserved. -/
def DownBlkSemAtW (Sdec : Stmt) (E : RAMEnv) (T : ℝ) (Bw ms ws : ℕ)
    (I : ℕ → (ℕ → ℕ) → Prop) {N Ms : ℕ}
    (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)) : Prop :=
  ∀ (G : Program) (base δ β γ : ℕ),
    wordsOf E.W Ms ≤ ms → β + ms ≤ 2 ^ E.W → ws ≤ 2 ^ E.W → γ + ws ≤ 2 ^ E.W →
  ∀ (header control hintMap resultMap listBase table count : ℕ)
    (y : Fin Ms → ZMod 2) (J : List ℕ) (s : RAMState),
    At G base (Sdec.compile base) → s.pc = base → δ + Bw ≤ 2 ^ E.W →
    HintRootHeaderAt E δ header control hintMap resultMap listBase table count N →
    s.regs 14 = δ → s.regs 15 = β →
    (∀ q < wordsOf E.W Ms, s.mem (β + q) = packMem E.W y q) →
    γ ≤ hintMap → hintMap + N < γ + ws →
    γ ≤ control → control + 4 ≤ γ + ws →
    γ ≤ listBase → listBase + N ≤ γ + ws →
    (β + ms ≤ γ ∨ γ + ws ≤ β) →
    (∀ n mem, I n mem → ∀ a, a < γ ∨ γ + ws ≤ a → mem a = s.mem a) →
    ∃ (k : ℕ) (out : RAMState), (k : ℝ) ≤ T ∧ (step G E)^[k] s = out ∧
      out.pc = base + Sdec.len ∧
      (∀ a, a < γ ∨ γ + ws ≤ a → out.mem a = s.mem a) ∧
      (∀ a, β ≤ a → a < β + ms → out.mem a = s.mem a)

/-- **The `δ = β = 0` reduction of the two-window contract is still 5.1's halting conjunct.**  The
payload sits at `0`, the workspace right after it at `ms`; both frame clauses are dropped. -/
theorem downBlkSemAtW_betaZero {Sdec : Stmt} {E : RAMEnv} {T : ℝ} {Bw ms ws N Ms : ℕ}
    {I : ℕ → (ℕ → ℕ) → Prop}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (h : DownBlkSemAtW Sdec E T Bw ms ws I Hs) (hBw : Bw ≤ 2 ^ E.W)
    (hfit : wordsOf E.W Ms ≤ ms) (hms : ms ≤ 2 ^ E.W) (hws : ws ≤ 2 ^ E.W)
    (hms_ws : ms + ws ≤ 2 ^ E.W)
    (y : Fin Ms → ZMod 2) (J : List ℕ)
    (header control hintMap resultMap listBase table count : ℕ)
    (hdr : HintRootHeaderAt E 0 header control hintMap resultMap listBase table count N)
    (hHint : ms ≤ hintMap) (hHintTop : hintMap + N < ms + ws)
    (hControl : ms ≤ control) (hControlTop : control + 4 ≤ ms + ws)
    (hList : ms ≤ listBase) (hListTop : listBase + N ≤ ms + ws)
    (hI : ∀ n mem, I n mem → ∀ a, a < ms ∨ ms + ws ≤ a →
      mem a = (decoderStart E.W y J).mem a) :
    ∃ s', HaltsWithin (Sdec.compile 0 ++ [Instr.halt]) E T (decoderStart E.W y J) s' := by
  let G : Program := Sdec.compile 0 ++ [Instr.halt]
  have hAt : At G 0 (Sdec.compile 0) := by
    intro r hr
    simpa [G] using List.getElem?_append_left (l₁ := Sdec.compile 0) (l₂ := [Instr.halt])
      (by simpa using hr)
  have hpc : (decoderStart E.W y J).pc = 0 := rfl
  have h14 : (decoderStart E.W y J).regs 14 = 0 := rfl
  have h15 : (decoderStart E.W y J).regs 15 = 0 := rfl
  have hmem : ∀ q < wordsOf E.W Ms, (decoderStart E.W y J).mem (0 + q) = packMem E.W y q := by
    intro q hq
    simp [decoderStart, initState, hintMem, hq]
  have hspan : 0 + ms ≤ 2 ^ E.W := by simpa using hms
  have hspan' : 0 + ws ≤ 2 ^ E.W := by simpa using hws
  obtain ⟨k, out, hk, hstep, hpcOut, -, -⟩ :=
    h G 0 0 0 ms hfit (by simpa using hms) hws (by simpa using hms_ws)
      header control hintMap resultMap listBase table count y J (decoderStart E.W y J)
      hAt hpc (by simpa using hBw) hdr h14 h15 hmem
      (by simpa using hHint) (by simpa using hHintTop)
      (by simpa using hControl) (by simpa using hControlTop)
      (by simpa using hList) (by simpa using hListTop)
      (by
        rcases Nat.zero_le ms with h
        exact Or.inl (by simpa using h))
      hI
  have hlen : (Sdec.compile 0).length = Sdec.len := Stmt.length_compile Sdec 0
  have hhalt : G[out.pc]? = some Instr.halt := by
    rw [hpcOut, show 0 + Sdec.len = Sdec.len by omega]
    rw [List.getElem?_append_right (by omega : (Sdec.compile 0).length ≤ Sdec.len)]
    simp [hlen]
  exact ⟨out, k, hk, hstep, by unfold Halted; rw [hhalt]; trivial⟩

/-- **The workspace size the contract forces.**  From the six containments alone: `N + 1 ≤ ws`
(the `hintMap` block plus the one-word slack that `hintMap + N < γ + ws` requires), `4 ≤ ws` (the
control block) and `N ≤ ws` (the list block). -/
theorem ws_bounds {γ ws N : ℕ} {hintMap control listBase : ℕ}
    (hHint : γ ≤ hintMap) (hHintTop : hintMap + N < γ + ws)
    (hControl : γ ≤ control) (hControlTop : control + 4 ≤ γ + ws)
    (hList : γ ≤ listBase) (hListTop : listBase + N ≤ γ + ws) :
    N + 1 ≤ ws ∧ 4 ≤ ws ∧ N ≤ ws := by
  omega

/-- **The workspace size with the three blocks packed consecutively** (the layout 6.5's column loop
should use): `hintMap`'s block (with its boundary word), then the four control words, then the
emitted list.  Then `2 * N + 5 ≤ ws`.  Dropping the boundary word gives `2 * N + 4`, which is only
sound if `hintMap + N` is never written — the published normalise frame does not give that. -/
theorem ws_bounds_packed {γ ws N : ℕ} {hintMap control listBase : ℕ}
    (hHint : γ ≤ hintMap) (hPacked₁ : hintMap + N < control) (hPacked₂ : control + 4 ≤ listBase)
    (hListTop : listBase + N ≤ γ + ws) :
    2 * N + 5 ≤ ws := by
  omega

/-! ### Non-vacuity of the two-window contract -/

/-- The two-window premise set is satisfiable with a **non-zero payload** and **disjoint windows**:
payload at `β = 100` (`ms = 1` word, `wordsOf 8 8 = 1`), workspace at `γ = 0` (`ws = 20`), the
decoder's blocks at `hintMap = 2`, `control = 7`, `listBase = 12`, `N = 4`, and `y = winY ≠ 0`. -/
theorem downBlkSemAtW_premises_nonvacuous :
    ∃ (E : RAMEnv) (δ β γ ms ws header control hintMap resultMap listBase table count N Ms : ℕ)
      (y : Fin Ms → ZMod 2),
      y ≠ 0 ∧ wordsOf E.W Ms ≤ ms ∧ β + ms ≤ 2 ^ E.W ∧ ws ≤ 2 ^ E.W ∧ γ + ws ≤ 2 ^ E.W ∧
      HintRootHeaderAt E δ header control hintMap resultMap listBase table count N ∧
      γ ≤ hintMap ∧ hintMap + N < γ + ws ∧
      γ ≤ control ∧ control + 4 ≤ γ + ws ∧
      γ ≤ listBase ∧ listBase + N ≤ γ + ws ∧
      (β + ms ≤ γ ∨ γ + ws ≤ β) := by
  refine ⟨winEnv, 5, 100, 0, 1, 20, 32, 7, 2, 20, 12, 20, 0, 4, 8, winY, winY_ne_zero,
    ?_, ?_, ?_, ?_, winHeader, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [wordsOf, winEnv, detEnv]

/-- **An inhabitant of the two-window contract.**  For a program that leaves memory alone both frame
clauses are immediate; what the witness shows is that the amended statement is consistent (the
published one is not, by `downBlkSemAtPublished_hintNativeRootAt_false`).  A *closed* inhabitant for
the real decoder is impossible for the same reason as before — the contract's premises do not include
the driver hypotheses (`hSource`, `hWordState`, `hActions`, …), so the decoder's own export is
`hintNativeRootAt_sem_ws_frame`, and `DownBlkSemAtW` is meant to be *assumed* by 6.5's column stage
in the same way as `UpBlkSem`/`CrSem`. -/
theorem downBlkSemAtW_nonvacuous (E : RAMEnv) {T : ℝ} (hT : 0 ≤ T) (Bw ms ws N Ms : ℕ)
    (I : ℕ → (ℕ → ℕ) → Prop)
    (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)) :
    DownBlkSemAtW (.code []) E T Bw ms ws I Hs := by
  intro G base δ β γ h1 h2 h3 h4 header control hintMap resultMap listBase table count y J s
    hAt hpc hfit hdr h14 h15 hmem h5 h6 h7 h8 h9 h10 hdisj hI
  refine ⟨0, s, by simpa using hT, rfl, ?_, (fun a _ => rfl), (fun a _ _ => rfl)⟩
  rw [hpc]
  simp [Stmt.len]

/-! ## 16. Why the literal two-window shape is false

The two-window amendment as first proposed keeps the frame over the *payload* window,
`∀ a, a < β ∨ β + ms ≤ a → out.mem a = s.mem a`.  With the windows disjoint the workspace lies
outside that window, so the clause demands that the workspace be preserved — while the decoder writes
it.  The refutation below is the same mechanism as
`downBlkSemAtPublished_hintNativeRootAt_false`: at `ms = Ms = 0` the payload window is empty, the
frame covers every address, and the decoder demonstrably writes the scratch word `control + 3`.  The
same argument applies at the non-vacuity witness of §15 (`β = 100`, `γ = 0`, `hintMap = 2`,
`control = 7`), where the written address `10 = control + 3` satisfies `10 < β = 100` and is thus
inside the payload-window frame's range. -/

/-- **The literal two-window shape** (frame over the payload window only), as proposed. -/
def DownBlkSemAtLiteral (Sdec : Stmt) (E : RAMEnv) (T : ℝ) (Bw ms ws : ℕ)
    (I : ℕ → (ℕ → ℕ) → Prop) {N Ms : ℕ}
    (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)) : Prop :=
  ∀ (G : Program) (base δ β γ : ℕ),
    wordsOf E.W Ms ≤ ms → β + ms ≤ 2 ^ E.W → ws ≤ 2 ^ E.W → γ + ws ≤ 2 ^ E.W →
  ∀ (header control hintMap resultMap listBase table count : ℕ)
    (y : Fin Ms → ZMod 2) (J : List ℕ) (s : RAMState),
    At G base (Sdec.compile base) → s.pc = base → δ + Bw ≤ 2 ^ E.W →
    HintRootHeaderAt E δ header control hintMap resultMap listBase table count N →
    s.regs 14 = δ → s.regs 15 = β →
    (∀ q < wordsOf E.W Ms, s.mem (β + q) = packMem E.W y q) →
    γ ≤ hintMap → hintMap + N < γ + ws →
    γ ≤ control → control + 4 ≤ γ + ws →
    γ ≤ listBase → listBase + N ≤ γ + ws →
    (β + ms ≤ γ ∨ γ + ws ≤ β) →
    (∀ n mem, I n mem → ∀ a, a < β ∨ β + ms ≤ a → mem a = s.mem a) →
    ∃ (k : ℕ) (out : RAMState), (k : ℝ) ≤ T ∧ (step G E)^[k] s = out ∧
      out.pc = base + Sdec.len ∧
      (∀ a, a < β ∨ β + ms ≤ a → out.mem a = s.mem a)

/-- **The literal form is false for the real decoder.**  At `β = ms = Ms = 0` the payload window is
empty (its hypothesis is vacuous) and disjointness holds at `γ = 0`; the workspace window
`[0, 12)` contains the decoder's blocks, and the frame over the empty payload window then demands
that the scratch word `control + 3 = 3` be preserved, which the run refutes. -/
theorem downBlkSemAtLiteral_false (S : CRSourceBundle) (T : ℝ) :
    ¬ DownBlkSemAtLiteral (hintNativeRootAt S) downBlkRefEnv T 0 0 12
        (fun _ mem => ∀ a, mem a = downBlkRefState.mem a)
        (N := 0) (Ms := 0)
        (0 : (Fin 0 → ZMod 2) →ₗ[ZMod 2] (Fin 0 → ZMod 2)) := by
  intro hc
  obtain ⟨k, out, hstep, hpc, hmem⟩ := downBlkRef_run S
  obtain ⟨k', out', -, hstep', hpc', hframe'⟩ :=
    hc (hintNativeProgramAt S) 0 5 0 0
      (by norm_num [wordsOf, downBlkRefEnv, detEnv]) (by norm_num [downBlkRefEnv, detEnv])
      (by norm_num [downBlkRefEnv, detEnv])
      (by norm_num [downBlkRefEnv, detEnv])
      32 0 4 10 10 20 0 (fun i => i.elim0) [] downBlkRefState (hintNativeRootAt_at S) rfl
      (by norm_num [downBlkRefEnv, detEnv]) downBlkRef_header rfl rfl
      (by intro q hq; simp [wordsOf, downBlkRefEnv, detEnv] at hq)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by intro n mem h a _; exact h a)
  have hhaltAt : (hintNativeProgramAt S)[(hintNativeRootAt S).len]? = some Instr.halt := by
    have hlen : ((hintNativeRootAt S).compile 0).length = (hintNativeRootAt S).len :=
      Stmt.length_compile _ 0
    simp only [hintNativeProgramAt]
    rw [← hlen, List.getElem?_append_right (by omega :
      ((hintNativeRootAt S).compile 0).length ≤ ((hintNativeRootAt S).compile 0).length)]
    simp
  have hpc'' : out'.pc = (hintNativeRootAt S).len := by rw [hpc']; omega
  have houtEq : out' = out :=
    iterate_eq_of_halt (by rw [hpc'']; exact hhaltAt) (by rw [hpc]; exact hhaltAt) hstep' hstep
  have hframe := hframe' 3 (Or.inr (by norm_num))
  rw [houtEq] at hframe
  have hzero : downBlkRefState.mem 3 = 0 := rfl
  rw [hzero] at hframe
  omega






#print axioms LinearSetReconciliation327.Main.hintRootHintArgsAt_spec
#print axioms LinearSetReconciliation327.Main.hintRootControlInitAt_spec
#print axioms LinearSetReconciliation327.Main.hintRootEmitArgsAt_spec
#print axioms LinearSetReconciliation327.Main.hintRootEnterAt_sem
#print axioms LinearSetReconciliation327.Main.hintRootExitAt_sem
#print axioms LinearSetReconciliation327.Main.hintNativeRootAt_sem
#print axioms LinearSetReconciliation327.Main.hintNativeRootAt_haltsWithin
#print axioms LinearSetReconciliation327.Main.downBlkSemAtPublished_betaZero
#print axioms LinearSetReconciliation327.Main.hintLocatedDispatch_sem_frame
#print axioms LinearSetReconciliation327.Main.hintNativeRootAt_sem_frame
#print axioms LinearSetReconciliation327.Main.hintNativeRootAt_sem_frame_words
#print axioms LinearSetReconciliation327.Main.hintNativeRootAt_sem_scratch
#print axioms LinearSetReconciliation327.Main.downBlkRef_run
#print axioms LinearSetReconciliation327.Main.downBlkSemAtPublished_hintNativeRootAt_false
#print axioms LinearSetReconciliation327.Main.downBlkSemAtSingle_betaZero
#print axioms LinearSetReconciliation327.Main.footprint_bounds_single
#print axioms LinearSetReconciliation327.Main.footprint_bounds_packed_single
#print axioms LinearSetReconciliation327.Main.downBlkSemAtSingle_premises_nonvacuous
#print axioms LinearSetReconciliation327.Main.downBlkSemAtSingle_nonvacuous
#print axioms LinearSetReconciliation327.Main.hintNativeRootAt_sem_ws_frame
#print axioms LinearSetReconciliation327.Main.downBlkSemAtW_betaZero
#print axioms LinearSetReconciliation327.Main.ws_bounds
#print axioms LinearSetReconciliation327.Main.ws_bounds_packed
#print axioms LinearSetReconciliation327.Main.downBlkSemAtW_premises_nonvacuous
#print axioms LinearSetReconciliation327.Main.downBlkSemAtW_nonvacuous
#print axioms LinearSetReconciliation327.Main.downBlkSemAtLiteral_false


