-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_InitStageZ20261122
-- name    : LinearSetReconciliation327_Main_InitStageZ20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T15:30:42.772721+00:00
-- url     : https://prove2.me/theorems/1f2e40e7-abde-43b2-b6fa-09cc1c42cb4b
-- title:
--   Theorem 6.5's prologue at the `Definitions` level: `SinitZ`, cost 30, lands on `zRowIn`
-- statement:
--   The 21-instruction prologue of Theorem 6.5's decoder, restated and proved at the `Definitions` level (`stageRun_init`, cost 21, post `InitOK`; `stageRun_init_rowIn`, post `RowIn d`).  Because the real row precondition `zRowIn` pins every non-loop register to `0` while the header read leaves nine header registers set, the bundle adds the nine-instruction `zeroHdrCode`; `SinitZ.len = 30` and `stageRun_initZ_rowIn` proves the adjusted prologue lands on `zRowIn` at cost 30 with **no extra hypothesis** (the payload word bound is derived from the decoder's start state).  Each later stage re-reads the header from `det`, so clearing the registers loses nothing.  Axiom-clean; local `cpl` 8 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's column stage and Theorem 5.1's decoder (the two-window `DownBlkSemAtW` contract).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_RowStage2Mirror20261122

/-!
# `InitStageZ` — Theorem 6.5's prologue, at the `Definitions` level

`zzz21/sol/stages_check.lean` proved `stageRun_init` for the 21-instruction prologue `Sinit`
(cost exactly `21`, post `InitOK`), but that file lives on the `Solutions` side and is not
importable.  This bundle restates the program and the run at the `Definitions` level and connects
it to the row stage of `zTopDecStmt`:

* `stageRun_init` — the prologue run inside `zProgDecOfTop`, cost `21`, post `InitOK`;
* `stageRun_init_rowIn` — the same run with the row field's post `RowIn d`, given
  `E.det 0 % 2^W = d` (the header's `d` is the row count);
* `SinitZ` — the prologue followed by the nine-instruction `zeroHdrCode`, which clears the nine
  header registers `r3, r4, r6, r9, r10, r11, r12, r13, r15` that the header read leaves behind.
  The real row precondition `zRowIn` pins **all** non-loop registers to `0`, so the verbatim
  21-instruction prologue cannot land on it; the adjustment is `+9` instructions
  (cost `30 = 21 + 9`).  The nine header registers are re-read from `det` by every later stage
  (`asmDst`, `resDst`, ...), so clearing them loses nothing.
* `stageRun_initZ_rowIn` — the adjusted prologue lands on `zRowIn` at cost `30`, with no extra
  hypothesis (the word bound `packMem < 2^W` is proved from the decoder's start state).

No file is modified; imports are `Mathlib` and one `Definitions.Def_*` bundle.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace W65C

open RSD

/-! ## 1. The `det` header slots (verbatim from `zzz21/sol/stages_check.lean`) -/

/-- `det` slot 0: the row count `d`. -/
def hdrD : ℕ := 0
/-- `det` slot 1: the column count `ℓ`. -/
def hdrEll : ℕ := 1
/-- `det` slot 2: the universe `n`. -/
def hdrN : ℕ := 2
/-- `det` slot 3: payload base of the row decoder's outputs. -/
def hdrRowBase : ℕ := 3
/-- `det` slot 4: payload base of the column decoders' outputs. -/
def hdrColBase : ℕ := 4
/-- `det` slot 5: base of the assembled candidate array. -/
def hdrAsmBase : ℕ := 5
/-- `det` slot 6: base of the residual array. -/
def hdrResBase : ℕ := 6
/-- `det` slot 7: payload base of the `CR` call. -/
def hdrCrBase : ℕ := 7
/-- `det` slot 8: the regime tag. -/
def hdrTag : ℕ := 8

/-! ## 2. `Sinit`: the 21-instruction prologue (verbatim) -/

/-- The prologue's instruction list: nine `(imm, tbl)` header reads, then `r1, r7, r8 := 0`. -/
def initCode : List Instr :=
  [ iImm r9 hdrD, iTbl r2 r9,
    iImm r9 hdrEll, iTbl r3 r9,
    iImm r9 hdrN, iTbl r4 r9,
    iImm r9 hdrRowBase, iTbl r11 r9,
    iImm r9 hdrColBase, iTbl r12 r9,
    iImm r9 hdrAsmBase, iTbl r13 r9,
    iImm r9 hdrResBase, iTbl r10 r9,
    iImm r9 hdrCrBase, iTbl r15 r9,
    iImm r9 hdrTag, iTbl r6 r9,
    iImm r1 0, iImm r7 0, iImm r8 0 ]

/-- The prologue as a `Stmt`. -/
def Sinit : Stmt := .code initCode

/-- `Sinit`'s postcondition (verbatim from `stages_check`). -/
def InitOK (E : RAMEnv) : RAMState → Prop := fun s =>
  s.regs 1 = 0 ∧ s.regs 2 = E.det hdrD % 2 ^ E.W ∧ s.regs 3 = E.det hdrEll % 2 ^ E.W

lemma initCode_noBranch : NoBranch initCode := by
  simp [initCode, NoBranch, Instr.NoBranchI]

lemma initCode_length : initCode.length = 21 := rfl

lemma Sinit_len : Sinit.len = 21 := rfl

/-! ## 3. The prologue run inside `zTopDecStmt` -/

/-- **The prologue runs, at cost exactly its length (21).**  This is `stageRun_init` of
`zzz21/sol/stages_check.lean`, re-pointed to the `zTopDecStmt` pipeline (its first block is
`Sinit`, and `zDRowBase Sinit` is where the row loop starts). -/
theorem stageRun_init {E : RAMEnv} {W M ell : ℕ} {Srow Sdec Sassem Sres Scr : Stmt}
    {y : Fin M → ZMod 2} (hW : 1 < 2 ^ E.W) :
    StageRun (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E 0 (zDRowBase Sinit)
      ((initCode.length : ℕ) : ℝ) (fun s => s = decoderStart W y []) (InitOK E) := by
  intro s hpc _
  have hAtAll : At (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) 0
      ((zTopDecStmt Sinit Srow Sdec Sassem Sres Scr ell).compile 0) := At.compile_top _
  have hAt : At (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) 0 initCode := by
    have h := at_seq_left (a := Sinit)
      (b := Stmt.seq (topLoop Srow)
        (Stmt.seq (zDispatch ell) (Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr)))))
      hAtAll
    simpa [Sinit, Stmt.compile] using h
  have hsem := Sem.block (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E 0 initCode s hAt
    initCode_noBranch hpc
  obtain ⟨-, k, s', hstep, hpc', hk, hs'⟩ := hsem
  have hkR : (k : ℝ) ≤ (initCode.length : ℝ) := by rw [hk]
  have hpcR : s'.pc = zDRowBase Sinit := by
    rw [hpc']
    simp only [zDRowBase, Sinit, Stmt.len]
  exact ⟨k, s', hkR, hstep, hpcR, by
    rw [hs']
    have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
    refine ⟨?_, ?_, ?_⟩
    · simp [initCode, runBlock_cons, runBlock_nil, execInstr]
    · simp [initCode, runBlock_cons, runBlock_nil, execInstr, hdrD]
    · simp [initCode, runBlock_cons, runBlock_nil, execInstr, hdrEll, h1]⟩

/-- Under the width bound the prologue's postcondition *is* the row loop's guard `RowIn`. -/
theorem initOK_rowIn {E : RAMEnv} {d : ℕ} {s : RAMState}
    (h : InitOK E s) (hdet : E.det hdrD % 2 ^ E.W = d) : RowIn d s := by
  obtain ⟨h1, h2, -⟩ := h
  exact ⟨h1, h2.trans hdet⟩

/-- **The `init` field's `StageRun`**: cost `21`, post `RowIn d`, with `d` the header's row count.
No hypothesis on the program or on the state beyond `s = decoderStart` and the width bound. -/
theorem stageRun_init_rowIn {E : RAMEnv} {W M ell d : ℕ} {Srow Sdec Sassem Sres Scr : Stmt}
    {y : Fin M → ZMod 2} (hW : 1 < 2 ^ E.W)
    (hdet : E.det hdrD % 2 ^ E.W = d) :
    StageRun (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E 0 (zDRowBase Sinit)
      ((initCode.length : ℕ) : ℝ) (fun s => s = decoderStart W y []) (RowIn d) :=
  C8R.stageRun_post (stageRun_init (E := E) (W := W) (M := M) (ell := ell)
    (Srow := Srow) (Sdec := Sdec) (Sassem := Sassem) (Sres := Sres) (Scr := Scr)
    (y := y) hW)
    (fun s hs => initOK_rowIn hs (by simpa [hdrD] using hdet))

/-! ## 4. The adjusted prologue `SinitZ`, landing on `zRowIn` -/

/-- The nine-instruction tail that clears the header registers the prologue read.  `zRowIn`'s
register component pins every register except `r1, r2, r7` to `0`. -/
def zeroHdrCode : List Instr :=
  [ iImm r3 0, iImm r4 0, iImm r6 0, iImm r9 0, iImm r10 0,
    iImm r11 0, iImm r12 0, iImm r13 0, iImm r15 0 ]

/-- The adjusted prologue: the 21-instruction header read, then the nine clears. -/
def SinitZ : Stmt := .code (initCode ++ zeroHdrCode)

lemma zeroHdrCode_noBranch : NoBranch zeroHdrCode := by
  simp [zeroHdrCode, NoBranch, Instr.NoBranchI]

lemma initCodeZ_noBranch : NoBranch (initCode ++ zeroHdrCode) := by
  simp [initCode, zeroHdrCode, NoBranch, Instr.NoBranchI]

lemma initCodeZ_length : (initCode ++ zeroHdrCode).length = 30 := by
  simp [initCode, zeroHdrCode]

lemma SinitZ_len : SinitZ.len = 30 := by
  simp [SinitZ, initCode, zeroHdrCode, Stmt.len]

/-- The register part of `SinitZ`'s effect on the decoder's start state, in the literal shape
`zLoopHeads` uses. -/
theorem runBlock_initZ_regs {E : RAMEnv} {W M d : ℕ} (hW : 1 < 2 ^ E.W) (hd : d < 2 ^ E.W)
    (hdet : E.det hdrD % 2 ^ E.W = d) (y : Fin M → ZMod 2) :
    (runBlock (initCode ++ zeroHdrCode) E (decoderStart W y [])).regs =
      fun i => if i = r1 then 0 else if i = r2 then d else if i = r7 then 0 else 0 := by
  have hdet' : E.det 0 % 2 ^ E.W = d := by simpa [hdrD] using hdet
  rw [runBlock_append]
  simp only [zeroHdrCode, runBlock_cons, runBlock_nil, execInstr]
  funext i
  fin_cases i <;>
    simp [initCode, runBlock_cons, runBlock_nil, execInstr, hdrD, hdrEll, hdrN,
      hdrRowBase, hdrColBase, hdrAsmBase, hdrResBase, hdrCrBase, hdrTag, hdet',
      Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hW, Nat.zero_mod, decoderStart, initState]

/-- **The adjusted prologue lands on `zRowIn`**, at cost `30 = 21 + 9`.  No extra hypothesis: the
word bound on the start state's memory is proved (`hintMem` is either `packMem < 2^W` or `0`). -/
theorem stageRun_initZ_rowIn {E : RAMEnv} {M ell d : ℕ} {Srow Sdec Sassem Sres Scr : Stmt}
    {y : Fin M → ZMod 2} (hW : 1 < 2 ^ E.W) (hd : d < 2 ^ E.W)
    (hdet : E.det hdrD % 2 ^ E.W = d) :
    StageRun (zProgDecOfTop SinitZ Srow Sdec Sassem Sres Scr ell) E 0 (zDRowBase SinitZ)
      ((initCode ++ zeroHdrCode).length : ℝ) (fun s => s = decoderStart E.W y [])
      (zRowIn SinitZ E d (fun _ a => (decoderStart E.W y []).mem a)) := by
  intro s hpc hpre
  subst hpre
  have hWpos : 0 < E.W := by
    rcases Nat.eq_zero_or_pos E.W with h | h
    · rw [h] at hW; simp at hW
    · exact h
  have hAtAll : At (zProgDecOfTop SinitZ Srow Sdec Sassem Sres Scr ell) 0
      ((zTopDecStmt SinitZ Srow Sdec Sassem Sres Scr ell).compile 0) := At.compile_top _
  have hAt : At (zProgDecOfTop SinitZ Srow Sdec Sassem Sres Scr ell) 0
      (initCode ++ zeroHdrCode) := by
    have h := at_seq_left (a := SinitZ)
      (b := Stmt.seq (topLoop Srow)
        (Stmt.seq (zDispatch ell) (Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr)))))
      hAtAll
    simpa [SinitZ, Stmt.compile] using h
  have hsem := Sem.block (zProgDecOfTop SinitZ Srow Sdec Sassem Sres Scr ell) E 0
    (initCode ++ zeroHdrCode) (decoderStart E.W y []) hAt initCodeZ_noBranch rfl
  obtain ⟨-, k, s', hstep, hpc', hk, hs'⟩ := hsem
  have hkR : (k : ℝ) ≤ ((initCode ++ zeroHdrCode).length : ℝ) := by rw [hk]
  have hpcR : s'.pc = zDRowBase SinitZ := by
    rw [hpc']
    simp only [zDRowBase, SinitZ, Stmt.len]
  refine ⟨k, s', hkR, hstep, hpcR, ?_⟩
  rw [hs'] at hpcR ⊢
  refine ⟨?_, ?_⟩
  · have hregs := runBlock_initZ_regs (E := E) (W := E.W) (M := M) (d := d) hW hd hdet y
    refine zRamState_eq_of ?_ ?_ ?_
    · simpa [zRowHeads, zLoopHeads] using hpcR
    · intro i
      exact congrFun hregs i
    · rfl
  · intro j hj i hi
    show (decoderStart E.W y []).mem (RDec.rowPayBase E j + i) < 2 ^ E.W
    rw [decoderStart, initState]
    simp only [hintMem]
    split_ifs with hlt
    · exact C8R.RP.packMem_lt E.W hWpos y _
    · exact Nat.two_pow_pos E.W

end W65C
end LinearSetReconciliation327.Main


