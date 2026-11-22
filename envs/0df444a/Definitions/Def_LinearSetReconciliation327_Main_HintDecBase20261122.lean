-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintDecBase20261122
-- name    : LinearSetReconciliation327_Main_HintDecBase20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:41:28.764598+00:00
-- url     : https://prove2.me/theorems/31701c4d-599c-40af-968f-80990517c61d
-- title:
--   A position-aware Theorem 5.1 decoder prologue, and the pinned per-block contract `DownBlkSemAt`
-- statement:
--   Theorem 5.1's word-RAM decoder locates its table through the *absolute* entry `det[3]` in three prologues (`hintRootHintArgs`, `hintRootControlInit`, `hintRootEmitArgs`).  This bundle makes the three sites position-aware for a per-child table at `det` base `delta` and a payload at memory base `beta`.  The caller's child table holds `header - delta` in slot `3` (a pointer relative to the table base), the absolute dispatch index in slot 12, `beta`-rebased memory addresses in slots 9, 11, 14, 15, and unchanged scalars in 10, 13; the decoder reads `det (delta+3)`, adds `delta`, and then sees the same absolute header as before.
--
--   The literal recipe "add `r14` at all three sites" is not correct and is refuted here: 5.1's own normalise prologue overwrites `r14` by `control` (`hintNormalizeSetup_spec`), so at the second site `r14` is no longer the `det` base; and the dispatch keeps `r14 = control` but clobbers every other register, so the base cannot be held in a register across the dispatch either.  The repaired sites park `delta` in the spare word `control + 3` (written by the first site, reloaded at the second and third), which is a no-op at `delta = beta = 0` because the start state has `r14 = r15 = 0`.
--
--   The bundle proves the three re-pointed site lemmas at `delta`/`beta`, proves that their `delta = beta = 0` specialisations recover 5.1's semantic conclusions (same header, same `HintDispatchData`, same `HintEmitArgs`, same memory except the new spare word), and exports the composable contract `DownBlkSemAt`: the published `DownBlkSem` shape with the caller's per-child table pinned by `HintRootHeaderAt` and the payload-word fit.  A `forall dt` with only a window equation cannot be met in a table-independent bound, because the normalise count and the dispatch count are table scalars.  The non-vacuity reduction `downBlkSemAt_betaZero` shows that the `delta = beta = 0` instance at `decoderStart` is exactly Theorem 5.1's own `HaltsWithin` conjunct.
-- source:
--   Theorem 5.1 and Theorem 6.5 of arXiv:2611.11409 (Liu--Xu--Yang--Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*).  The three prologues are copied from the verified 5.1 development (`HintRootHeader20261120`, `HintRootIO20261120`); the table classification follows `HintSlotKind` of the accepted `HintDecAtModel20261122` bundle, and the repaired contract follows Proposition 2.3's `CrSemAtW` precedent.

import Definitions.Def_LinearSetReconciliation327_Main_HintDecAtModel20261122
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
namespace LinearSetReconciliation327.Main

/-!
# `HintDecBase`: the position-aware Theorem 5.1 prologue, self-contained

This bundle is the publishable part of the position-aware decoder round.  It restates only the
prologue structures that the three relocated `det[3]` sites need (`HintNormalizeTable`,
`HintEmitArgs`, `HintDispatchData`; the originals are not yet published platform nodes), proves the
three re-pointed site lemmas and their `delta = beta = 0` specialisations, refutes the literal
"add `r14` at all three sites" recipe, and exports the pinned composable contract `DownBlkSemAt`
with its non-vacuity reduction to Theorem 5.1's halting conjunct.  The full run contract of the
modified decoder (`hintNativeRootAt_sem` / `hintNativeRootAt_haltsWithin`) is in the companion
local file `HintDecBase51_at.lean`, which imports the still-unpublished 5.1 native chain.
-/

structure HintNormalizeTable (E : RAMEnv) (metaBase dest count control : Nat) : Prop where
  word : 11 < 2 ^ E.W
  span : metaBase + 11 < 2 ^ E.W
  dest_address : E.det (metaBase + 9) = dest
  count_value : E.det (metaBase + 10) = count
  control_address : E.det (metaBase + 11) = control
  dest_span : dest + count < 2 ^ E.W
  control_fit : control < 2 ^ E.W

structure HintEmitArgs (dest source count : Nat) (s : RAMState) : Prop where
  destination : s.regs 4 = dest
  source_value : s.regs 5 = source
  length : s.regs 6 = count
  one : s.regs 15 = 1

structure HintDispatchData (control table count index : Nat) (s : RAMState) : Prop where
  context : s.regs 14 = control
  table_pointer : s.mem control = table
  size : s.mem (control + 1) = count
  cursor : s.mem (control + 2) = index

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

/-! ## 11. The exported composable contract -/

/-- The composable per-sub-block decoder contract for the position-aware decoder.  It is the
published `DownBlkSem` shape with the caller's per-child table *pinned* by `HintRootHeaderAt`
(a `∀ dt` with only a window equation cannot make the decoder finish in a table-independent
bound: the normalise count and the dispatch count are table scalars).  The `det` base is `δ` and
the payload base `β`; the output clause is dropped (6.5's column stage gets correctness from
`hint_decode_correct`) and the two-sided frame is kept. -/
def DownBlkSemAt (Sdec : Stmt) (E : RAMEnv) (T : ℝ) (Bw : ℕ) {N Ms : ℕ}
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
theorem downBlkSemAt_betaZero {Sdec : Stmt} {E : RAMEnv} {T : ℝ} {Bw N Ms : ℕ}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (h : DownBlkSemAt Sdec E T Bw Hs) (hBw : Bw ≤ 2 ^ E.W)
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


end LinearSetReconciliation327.Main


