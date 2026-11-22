-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrPipeline20261122
-- name    : LinearSetReconciliation327_Main_CrPipeline20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T07:40:33.741055+00:00
-- url     : https://prove2.me/theorems/14531ef2-1cc3-4da0-b44b-c63f175f3e27
-- title:
--   Theorem 6.5's CR stage, closed: upkSetup, the four-block layout, and the decoder-free composed StageRun
-- statement:
--   **Theorem 6.5's CR stage, closed end to end: the unpack's entry registers, the repack, and the merge, with no decoder-side hypothesis beyond Proposition 2.3's own statement.**
--
--   The CR stage of the top-level decoder was, until now, `seq` of 2.3's decoder and the merge.  That is not a well-formed pipeline: 2.3's decoder clobbers `r0 ... r15`, so after it only the output window `(r0, r1) = (bb, bl)` is meaningful, while the unpack block `upkStmt` needs seven registers set, and the merge needs the estimate `x̂` as an explicit coordinate list.
--
--   **§1-2. `upkSetup`, five instructions.**  `upkSetup W xbase m ab ob` is `[iImm r4 ab, iImm r5 ob, iImm r6 m, iImm r2 xbase, iImm r3 W]`.  `upkSetup_run` is the `runBlock` equation (four word bounds make the immediate loads exact; `W < 2^W` is `Nat.lt_two_pow_self`, so `E.W` needs no hypothesis), `stageRun_upkSetup` is the stage contract — five steps from `CrUpkSetupIn` to the published `UpkIn`.
--
--   **§3. The address arithmetic.**  The CR block becomes `CrStage4 Sdec23 W xbase m ab ob = seq (seq Sdec23 upkSetupStmt) (seq upkStmt mrgStmtFull)`, so `CrStage4_len`: its length is the decoder's `+ 122`, and `dEnd_decStmt404`: at 2.3's own decoder `dEnd = dCrBase + 404`, i.e. `282 + 5 + 31 + 86`.  Four `At` facts place the decoder at `dCrBase`, the setup at `dCrBase + 282`, the unpack at `dCrBase + 287` and the merge at `dCrBase + 318` (`at_crStage4_decStmt_setup/_upk/_mrg`), plus the generic forms in `Sdec23.len`.
--
--   **§4. The unpack's memory footprint.**  `upkMem_frame_wide` bounds the scan's writes by the loop counter, and `upk_halts_frame` is the published `upk_halts` with one added conjunct: the exit memory is exactly `upkMem`, so every cell outside `[ab, ab + m·W + 1)` is the entry memory.  This is what lets the decoder's output window survive the repack.
--
--   **§5. From 2.3's conclusion to the merge's entry.**  `CrDecOut` names what 2.3's run hands over — the output window, the decoded set as a duplicate-free output list, the payload frame `HoldsVecPad` (the packed estimate intact in `m` words) and the window's word bound; `crDecOut_of_outputsSupport` is the bridge from the published `OutputsSupport`.  `crMergeInD_of_upk` proves that `UpkOut` plus the frame gives the corrected merge entry predicate `CrMergeInD` — the residual list is the decoder's own, and the merge's five arguments are the unpack's epilogue's.
--
--   **§6. The composed stage.**  `stageRun_crPipeline` proves the whole block from `dCrBase` to `dEnd` inside `progDecOfTop`, at cost `Tdec + 5 + (16·m·W + 17) + mrgCost al bl`, concluding `OutListIs s' (x̂ △ S)`.  Its only decoder-side hypothesis is 2.3's own statement read through `CrDecOut` (its `OutputsSupport`, the output window, the payload frame, the window's word bound); the previous round's `hdec` — which demanded the full merge entry predicate at `dCrBase + 282`, i.e. the very registers and list the decoder destroys — is gone.
--
--   **Formalization Note** Definitions and fully proved lemmas only: no `sorry`, no `admit`, no new axiom; `#print axioms` of every declaration is `[propext, Classical.choice, Quot.sound]`.  The imports are `Mathlib` and two published `Definitions` bundles, so no `Solutions.*` and no `Theorems.*` mirror can smuggle `sorryAx` in.  The proof of the published `upk_halts` is copied byte-identically from `Def_…_CrUnpackRun20261122` (146 lines; `gen_upkframe.py` asserts the span is a substring and patches exactly three lines: the name, the added conjunct, and the final refiner).  The whole node elaborates in 6 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's `cr` stage, Proposition 2.3 and §9.2.  Builds on the published `Def_…_CrStage20261122`, `Def_…_CrStageDec20261122`, `Def_…_CrMergeD20261122` and `Def_…_CrUnpackRun20261122`.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrMergeD20261122
import Definitions.Def_LinearSetReconciliation327_Main_CrUnpackRun20261122

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace CRS

/-! ## 1. `upkSetup` — the five instructions that set the unpack's entry registers -/

/-- **The setup block.**  `UpkIn` pins seven registers; 2.3's decoder hands over
`(r0, r1) = (bb, bl)` and clobbers the rest, so exactly five are missing: `r2 = xbase`,
`r3 = W`, `r4 = ab`, `r5 = ob`, `r6 = m`.  Five immediate loads set them, so the block is
five instructions long whatever the constants are.

(`r5` holds `ob` on entry; `upkPre` computes `r5 := r3 * r6 = m·W` inside `upkStmt`, and copies
`ob` into `r14` before overwriting `r5`.) -/
def upkSetup (W xbase m ab ob : ℕ) : List Instr :=
  [iImm r4 ab, iImm r5 ob, iImm r6 m, iImm r2 xbase, iImm r3 W]

theorem upkSetup_length (W xbase m ab ob : ℕ) : (upkSetup W xbase m ab ob).length = 5 := rfl

theorem upkSetup_noBranch (W xbase m ab ob : ℕ) : NoBranch (upkSetup W xbase m ab ob) := by
  simp [upkSetup, NoBranch, Instr.NoBranchI]

/-- The register file `upkSetup` leaves: five cells replaced, everything else untouched. -/
def upkSetupRegs (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) : Fin 16 → ℕ :=
  fun d =>
    if d = r2 then xbase
    else if d = r3 then E.W
    else if d = r4 then ab
    else if d = r5 then ob
    else if d = r6 then m
    else s.regs d

/-- The state `upkSetup` leaves (program counter and memory unchanged). -/
def upkSetupSt (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) : RAMState where
  pc := s.pc
  regs := upkSetupRegs E xbase m ab ob s
  mem := s.mem

theorem upkSetupSt_pc (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) :
    (upkSetupSt E xbase m ab ob s).pc = s.pc := rfl

theorem upkSetupSt_mem (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) :
    (upkSetupSt E xbase m ab ob s).mem = s.mem := rfl

theorem upkSetupSt_r0 (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) :
    (upkSetupSt E xbase m ab ob s).regs 0 = s.regs 0 := by
  simp [upkSetupSt, upkSetupRegs]

theorem upkSetupSt_r1 (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) :
    (upkSetupSt E xbase m ab ob s).regs 1 = s.regs 1 := by
  simp [upkSetupSt, upkSetupRegs]

theorem upkSetupSt_r2 (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) :
    (upkSetupSt E xbase m ab ob s).regs 2 = xbase := by
  simp [upkSetupSt, upkSetupRegs]

theorem upkSetupSt_r3 (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) :
    (upkSetupSt E xbase m ab ob s).regs 3 = E.W := by
  simp [upkSetupSt, upkSetupRegs]

theorem upkSetupSt_r4 (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) :
    (upkSetupSt E xbase m ab ob s).regs 4 = ab := by
  simp [upkSetupSt, upkSetupRegs]

theorem upkSetupSt_r5 (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) :
    (upkSetupSt E xbase m ab ob s).regs 5 = ob := by
  simp [upkSetupSt, upkSetupRegs]

theorem upkSetupSt_r6 (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) :
    (upkSetupSt E xbase m ab ob s).regs 6 = m := by
  simp [upkSetupSt, upkSetupRegs]

theorem upkSetupSt_r10 (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) :
    (upkSetupSt E xbase m ab ob s).regs r10 = s.regs r10 := by
  simp [upkSetupSt, upkSetupRegs]

theorem upkSetupSt_r15 (E : RAMEnv) (xbase m ab ob : ℕ) (s : RAMState) :
    (upkSetupSt E xbase m ab ob s).regs r15 = s.regs r15 := by
  simp [upkSetupSt, upkSetupRegs]

theorem withPc_self {k : ℕ} {s : RAMState} (h : s.pc = k) : ({ s with pc := k } : RAMState) = s := by
  cases s with
  | mk p r m => rw [← h]

/-- **The setup block, as a `runBlock` equation.**  Four word bounds make the immediate loads
exact; `W < 2^W` is `Nat.lt_two_pow_self`, so `E.W` needs no hypothesis. -/
theorem upkSetup_run (E : RAMEnv) (k : ℕ) (s : RAMState) (xbase m ab ob : ℕ)
    (hx : xbase < 2 ^ E.W) (hab : ab < 2 ^ E.W) (hob : ob < 2 ^ E.W) (hm : m < 2 ^ E.W) :
    runBlock (upkSetup E.W xbase m ab ob) E { s with pc := k }
      = upkSetupSt E xbase m ab ob { s with pc := k + 5 } := by
  have hW : E.W < 2 ^ E.W := Nat.lt_two_pow_self
  apply ramState_eq_of
  · rw [runBlock_pc _ E _ (upkSetup_noBranch _ _ _ _ _)]
    simp [upkSetup_length, upkSetupSt, upkSetupRegs]
  · rfl
  · intro d
    fin_cases d <;>
      simp only [upkSetup, upkSetupSt, upkSetupRegs, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero,
        Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hab,
        Nat.mod_eq_of_lt hob, Nat.mod_eq_of_lt hm, if_true, if_false, ↓reduceIte]

/-! ## 2. The setup as a pipeline stage -/

/-- `HoldsVecPad` only looks at memory. -/
theorem holdsVecPad_congr_mem {W m base : ℕ} {y : Fin (W * m) → ZMod 2} {s s' : RAMState}
    (h : s.mem = s'.mem) (hp : C8R.HoldsVecPad W m base s y) :
    C8R.HoldsVecPad W m base s' y := by
  unfold C8R.HoldsVecPad at hp ⊢
  rw [← h]; exact hp

/-- What the setup consumes: 2.3's output window `(r0, r1) = (bb, bl)` and the payload frame
`HoldsVecPad` (the packed estimate, intact in `m` words). -/
def CrUpkSetupIn (E : RAMEnv) (xbase m bb bl : ℕ) (y : Fin (E.W * m) → ZMod 2)
    (s : RAMState) : Prop :=
  s.regs 0 = bb ∧ s.regs 1 = bl ∧ C8R.HoldsVecPad E.W m xbase s y

/-- **The setup is a `StageRun`**: five steps, from `CrUpkSetupIn` to `UpkIn`. -/
theorem stageRun_upkSetup {G : Program} {E : RAMEnv} {base xbase m ab bb bl ob : ℕ}
    {y : Fin (E.W * m) → ZMod 2}
    (hAt : At G base (upkSetup E.W xbase m ab ob))
    (hx : xbase < 2 ^ E.W) (hab : ab < 2 ^ E.W) (hob : ob < 2 ^ E.W) (hm : m < 2 ^ E.W) :
    StageRun G E base (base + 5) (5 : ℝ) (CrUpkSetupIn E xbase m bb bl y)
      (UpkIn E xbase m ab bb bl ob y) := by
  intro s hpc hIn
  obtain ⟨h0, h1, hpad⟩ := hIn
  have hb := Sem.block G E base (upkSetup E.W xbase m ab ob) s hAt
    (upkSetup_noBranch _ _ _ _ _) hpc
  rw [upkSetup_length] at hb
  obtain ⟨-, k, s', hstep, hpc', hk, hs'⟩ := hb
  have hrun : runBlock (upkSetup E.W xbase m ab ob) E s
      = upkSetupSt E xbase m ab ob { s with pc := base + 5 } := by
    have h2 := upkSetup_run E base s xbase m ab ob hx hab hob hm
    rw [withPc_self hpc] at h2
    exact h2
  refine ⟨k, s', by rw [hk]; norm_num, hstep, hpc', ?_⟩
  have hs2 : s' = upkSetupSt E xbase m ab ob { s with pc := base + 5 } := by
    rw [hs', hrun]
  rw [hs2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [upkSetupSt_r0]; exact h0
  · rw [upkSetupSt_r1]; exact h1
  · exact upkSetupSt_r2 E xbase m ab ob _
  · exact upkSetupSt_r3 E xbase m ab ob _
  · exact upkSetupSt_r4 E xbase m ab ob _
  · exact upkSetupSt_r5 E xbase m ab ob _
  · exact upkSetupSt_r6 E xbase m ab ob _
  · exact holdsVecPad_congr_mem (by rw [upkSetupSt_mem]) hpad

/-! ## 3. The four-block layout: 282 + 5 + 31 + 86 = 404 -/

/-- The setup as a `Stmt`. -/
abbrev upkSetupStmt (W xbase m ab ob : ℕ) : Stmt := .code (upkSetup W xbase m ab ob)

theorem upkSetupStmt_len (W xbase m ab ob : ℕ) : (upkSetupStmt W xbase m ab ob).len = 5 := rfl

theorem upkSetupStmt_compile (W xbase m ab ob : ℕ) (base : ℕ) :
    (upkSetupStmt W xbase m ab ob).compile base = upkSetup W xbase m ab ob := rfl

theorem upkSetupStmt_noJump (W xbase m ab ob : ℕ) :
    sNoJumpB (upkSetupStmt W xbase m ab ob) = true := rfl

theorem upkSetupStmt_haltFree (W xbase m ab ob : ℕ) :
    sHaltFreeB (upkSetupStmt W xbase m ab ob) = true := rfl

/-- **The CR stage with the setup in it**: 2.3's decoder, then the setup, the unpack and the merge.

`(282 + 5) + (31 + 86)`: the grouping is what the `At` peeling below follows. -/
abbrev CrStage4 (Sdec23 : Stmt) (W xbase m ab ob : ℕ) : Stmt :=
  .seq (.seq Sdec23 (upkSetupStmt W xbase m ab ob)) (.seq upkStmt RMR.mrgStmtFull)

/-- **`282 + 5 + 31 + 86 = 404` in one line**: the composite is the decoder plus `122`. -/
theorem CrStage4_len (Sdec23 : Stmt) (W xbase m ab ob : ℕ) :
    (CrStage4 Sdec23 W xbase m ab ob).len = Sdec23.len + 122 := by
  simp [CrStage4, Stmt.len, upkSetupStmt_len, upkStmt_len, RMR.mrgStmtFull_len, upkSetup_length]

/-- The rewritten address arithmetic: `dEnd` is `dCrBase` plus the four blocks' lengths. -/
theorem dEnd_crStage4 (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) (W xbase m ab ob : ℕ) :
    dEnd Sinit Srow Sdec Sassem Sres (CrStage4 Sdec23 W xbase m ab ob)
      = dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len + 122 := by
  show dCrBase Sinit Srow Sdec Sassem Sres + (CrStage4 Sdec23 W xbase m ab ob).len = _
  rw [CrStage4_len]
  omega

/-- **`dEnd = dCrBase + 404`** at 2.3's own decoder: `282 + 5 + 31 + 86`. -/
theorem dEnd_decStmt404 (Sinit Srow Sdec Sassem Sres : Stmt) (W xbase m ab ob : ℕ) :
    dEnd Sinit Srow Sdec Sassem Sres (CrStage4 decStmt W xbase m ab ob)
      = dCrBase Sinit Srow Sdec Sassem Sres + 404 := by
  rw [dEnd_crStage4, decStmt_len]
  try norm_num

section Peel

theorem At.addr {P : Program} {a a' : ℕ} {l : List Instr} (h : At P a l) (e : a = a') : At P a' l := by
  subst e; exact h

theorem At.peelL {P : Program} {base : ℕ} {A B : Stmt}
    (h : At P base (Stmt.compile (Stmt.seq A B) base)) : At P base (Stmt.compile A base) :=
  (At.append.mp h).1

theorem At.peelR {P : Program} {base : ℕ} {A B : Stmt}
    (h : At P base (Stmt.compile (Stmt.seq A B) base)) :
    At P (base + A.len) (Stmt.compile B (base + A.len)) := by
  have h' : At P base ((Stmt.compile A base) ++ Stmt.compile B (base + A.len)) := h
  have h2 : At P (base + (Stmt.compile A base).length) (Stmt.compile B (base + A.len)) :=
    (At.append.mp h').2
  rwa [Stmt.length_compile] at h2

end Peel

/-- The composite at `dCrBase`. -/
theorem at_crStage4 (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) (W xbase m ab ob : ℕ) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 Sdec23 W xbase m ab ob))
      (dCrBase Sinit Srow Sdec Sassem Sres)
      (Stmt.compile (CrStage4 Sdec23 W xbase m ab ob) (dCrBase Sinit Srow Sdec Sassem Sres)) :=
  at_cr_seq Sinit Srow Sdec Sassem Sres (CrStage4 Sdec23 W xbase m ab ob)

/-- 2.3's decoder at `dCrBase`. -/
theorem at_crStage4_dec (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) (W xbase m ab ob : ℕ) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 Sdec23 W xbase m ab ob))
      (dCrBase Sinit Srow Sdec Sassem Sres)
      (Sdec23.compile (dCrBase Sinit Srow Sdec Sassem Sres)) :=
  At.peelL (A := Sdec23) (B := upkSetupStmt W xbase m ab ob)
    (At.peelL (A := Stmt.seq Sdec23 (upkSetupStmt W xbase m ab ob))
      (B := Stmt.seq upkStmt RMR.mrgStmtFull)
      (at_crStage4 Sinit Srow Sdec Sassem Sres Sdec23 W xbase m ab ob))

/-- **The setup at `dCrBase + 282`.** -/
theorem at_crStage4_setup (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) (W xbase m ab ob : ℕ) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 Sdec23 W xbase m ab ob))
      (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len)
      (upkSetup W xbase m ab ob) :=
  At.peelR (A := Sdec23) (B := upkSetupStmt W xbase m ab ob)
    (At.peelL (A := Stmt.seq Sdec23 (upkSetupStmt W xbase m ab ob))
      (B := Stmt.seq upkStmt RMR.mrgStmtFull)
      (at_crStage4 Sinit Srow Sdec Sassem Sres Sdec23 W xbase m ab ob))

/-- The unpack, at `dCrBase + 282 + 5`. -/
theorem at_crStage4_upk (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) (W xbase m ab ob : ℕ) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 Sdec23 W xbase m ab ob))
      (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len + 5)
      (upkStmt.compile (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len + 5)) :=
  At.addr (At.peelL (A := upkStmt) (B := RMR.mrgStmtFull)
    (At.peelR (A := Stmt.seq Sdec23 (upkSetupStmt W xbase m ab ob))
      (B := Stmt.seq upkStmt RMR.mrgStmtFull)
      (at_crStage4 Sinit Srow Sdec Sassem Sres Sdec23 W xbase m ab ob)))
    (by simp [Stmt.len, upkSetupStmt_len, upkStmt_len]; try omega)

/-- **The merge at `dCrBase + 282 + 5 + 31`.** -/
theorem at_crStage4_mrg (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) (W xbase m ab ob : ℕ) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 Sdec23 W xbase m ab ob))
      (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len + 5 + 31)
      (RMR.mrgStmtFull.compile (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len + 5 + 31)) :=
  At.addr (At.peelR (A := upkStmt) (B := RMR.mrgStmtFull)
    (At.peelR (A := Stmt.seq Sdec23 (upkSetupStmt W xbase m ab ob))
      (B := Stmt.seq upkStmt RMR.mrgStmtFull)
      (at_crStage4 Sinit Srow Sdec Sassem Sres Sdec23 W xbase m ab ob)))
    (by simp [Stmt.len, upkSetupStmt_len, upkStmt_len]; try omega)

/-- The merge at `dCrBase + 318`, at 2.3's own decoder. -/
theorem at_crStage4_decStmt_mrg (Sinit Srow Sdec Sassem Sres : Stmt) (W xbase m ab ob : ℕ) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 decStmt W xbase m ab ob))
      (dCrBase Sinit Srow Sdec Sassem Sres + 318)
      (RMR.mrgStmtFull.compile (dCrBase Sinit Srow Sdec Sassem Sres + 318)) :=
  At.addr (at_crStage4_mrg Sinit Srow Sdec Sassem Sres decStmt W xbase m ab ob)
    (by rw [decStmt_len])

/-- The setup at `dCrBase + 282`, at 2.3's own decoder. -/
theorem at_crStage4_decStmt_setup (Sinit Srow Sdec Sassem Sres : Stmt) (W xbase m ab ob : ℕ) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 decStmt W xbase m ab ob))
      (dCrBase Sinit Srow Sdec Sassem Sres + 282)
      (upkSetup W xbase m ab ob) :=
  At.addr (at_crStage4_setup Sinit Srow Sdec Sassem Sres decStmt W xbase m ab ob)
    (by rw [decStmt_len])

/-- The unpack at `dCrBase + 287`, at 2.3's own decoder. -/
theorem at_crStage4_decStmt_upk (Sinit Srow Sdec Sassem Sres : Stmt) (W xbase m ab ob : ℕ) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 decStmt W xbase m ab ob))
      (dCrBase Sinit Srow Sdec Sassem Sres + 287)
      (upkStmt.compile (dCrBase Sinit Srow Sdec Sassem Sres + 287)) :=
  At.addr (at_crStage4_upk Sinit Srow Sdec Sassem Sres decStmt W xbase m ab ob)
    (by rw [decStmt_len]; try norm_num)

/-- The arithmetic in one line. -/
theorem crStage4_arith : (282 : ℕ) + 5 + 31 + 86 = 404 := by norm_num

/-! ## 4. The unpack's memory footprint -/

/-- **The scan writes only inside `[ab, ab + j + 1)`.**  `upkMem_frame` bounds the range by the
list length `#upkList`; this is the same statement with the list length replaced by the loop count
`j`, which is what a caller knows. -/
theorem upkMem_frame_wide (W xbase : ℕ) (m0 : ℕ → ℕ) (ab j a : ℕ)
    (ha : a < ab ∨ ab + (j + 1) ≤ a) : upkMem W xbase m0 ab j a = m0 a :=
  upkMem_frame W xbase m0 ab j a (by
    rcases ha with h | h
    · exact Or.inl h
    · exact Or.inr (by have := upkList_length_le W xbase m0 j; omega))

theorem upk_halts_frame (E : RAMEnv) (xbase m ab bb bl ob : ℕ) (y : Fin (E.W * m) → ZMod 2)
    (s : RAMState) (hIn : UpkIn E xbase m ab bb bl ob y s) (hpc0 : s.pc = 0)
    (hW : 1 < 2 ^ E.W) (hWm : E.W * m < 2 ^ E.W) (hdisj : xbase + m ≤ ab)
    (hab : ab + E.W * m + 1 < 2 ^ E.W) (hbb : bb < 2 ^ E.W) (hbl : bl < 2 ^ E.W)
    (hob : ob < 2 ^ E.W) :
    ∃ s' : RAMState,
      HaltsWithin (programOfStatement upkStmt) E ((16 * (E.W * m) + 17 : ℕ) : ℝ) s s' ∧
        UpkOut E.W m xbase ab bb bl ob y s' ∧
        s'.mem = upkMem E.W xbase s.mem ab (E.W * m) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, hpad⟩ := hIn
  have hWpos : 0 < E.W := by
    rcases Nat.eq_zero_or_pos E.W with h | h
    · rw [h] at hW; simp at hW
    · exact h
  have hwords : wordsOf E.W (E.W * m) = m := C8R.asm_words_eq_padded E.W m hWpos
  -- (1) the prologue
  have hpre : Sem (programOfStatement upkStmt) E 0 11 s
      (fun k s' => k = 11 ∧
        s' = { upkSt E.W 11 s xbase m ab bb bl ob 0 with pc := 11 }) := by
    have hb := Sem.block (programOfStatement upkStmt) E 0 upkPre s upk_at_pre
      upkPre_noBranch hpc0
    rw [show (0 : ℕ) + upkPre.length = 11 from by rw [upkPre_length]] at hb
    refine Sem.mono hb (fun k s' h => ?_)
    obtain ⟨hk, rfl⟩ := h
    rw [upkPre_length] at hk
    have hs : ({ s with pc := 0 } : RAMState) = s := by
      simpa [withPc] using withPc_congr hpc0
    refine ⟨hk, ?_⟩
    conv_lhs => rw [← hs]
    rw [upkPre_run E 0 s xbase m ab bb bl ob h0 h1 h2 h3 h4 h5 h6 hW hWm hbb hbl hob]
  -- (2) the scan loop
  have hloop : Sem (programOfStatement upkStmt) E 11 27
      (upkSt E.W 11 s xbase m ab bb bl ob 0)
      (fun k s' => k ≤ 2 + 16 * (E.W * m) ∧
        s' = { runBlock upkCond.code E (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))
                with pc := 27 }) := by
    have hl := sem_loop (programOfStatement upkStmt) E 11 upkCond (.code upkBody)
      upk_at_loop hW (E.W * m) (fun j => upkSt E.W 11 s xbase m ab bb bl ob j)
      (fun _ => 14) (fun j => rfl)
      (fun j hj => by
        show (upkSt E.W 11 s xbase m ab bb bl ob j).regs r0
            < (upkSt E.W 11 s xbase m ab bb bl ob j).regs r5
        rw [upkSt_r0, upkSt_r5]
        exact hj)
      (fun hcontra => by
        have h' : (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m)).regs r0
            < (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m)).regs r5 := hcontra
        rw [upkSt_r0, upkSt_r5] at h'
        omega)
      (fun j hj => by
        have hjw : j / E.W < m := by
          rw [Nat.div_lt_iff_lt_mul hWpos, Nat.mul_comm]
          exact hj
        have hword : s.mem (xbase + j / E.W) < 2 ^ E.W := by
          rw [hpad _ (by rw [hwords]; exact hjw)]
          exact C8R.RP.packMem_lt E.W hWpos y (j / E.W)
        simpa [upkCond, Cond.code] using
          upk_body_step E s xbase m ab bb bl ob j hW hj hWm hdisj hab hword)
    rw [show (11 : ℕ) + upkCond.code.length + (Stmt.code upkBody).len + 2 = 27 from by
      simp [upkCond, Cond.code, Stmt.len, upkBody]] at hl
    refine Sem.mono hl (fun k s' h => ⟨?_, h.2⟩)
    have hk := h.1
    rw [show upkCond.code.length = 1 from rfl] at hk
    have hsum : (1 : ℕ) + 1 + ∑ j ∈ Finset.range (E.W * m), (1 + 1 + 14)
        = 2 + 16 * (E.W * m) := by
      rw [sum_range_const16]
    rw [hsum] at hk
    exact hk
  -- (3) the epilogue
  have hleg : Sem (programOfStatement upkStmt) E 27 31
      { runBlock upkCond.code E (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m)) with pc := 27 }
      (fun k s' => k = 4 ∧ s' = upkEpi E xbase m ab bb bl ob s) := by
    have hb := Sem.block (programOfStatement upkStmt) E 27 upkEpilogue
      { runBlock upkCond.code E (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m)) with pc := 27 }
      upk_at_epi upkEpilogue_noBranch rfl
    rw [show (27 : ℕ) + upkEpilogue.length = 31 from by rw [upkEpilogue_length]] at hb
    have hr1 : (runBlock upkCond.code E
        (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))).regs 1 < 2 ^ E.W := by
      rw [upkHead_exit_regs E 11 s xbase m ab bb bl ob r1 (by decide), upkSt_r1]
      exact lt_of_le_of_lt (upkList_length_le E.W xbase s.mem (E.W * m)) (by omega)
    have hr4 : (runBlock upkCond.code E
        (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))).regs 4 < 2 ^ E.W := by
      rw [upkHead_exit_regs E 11 s xbase m ab bb bl ob r4 (by decide), upkSt_r4]
      exact lt_of_le_of_lt (Nat.le_add_right ab (E.W * m)) (by omega)
    have hr12 : (runBlock upkCond.code E
        (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))).regs r12 < 2 ^ E.W := by
      rw [upkHead_exit_regs E 11 s xbase m ab bb bl ob r12 (by decide), upkSt_r12]
      exact hbb
    have hr13 : (runBlock upkCond.code E
        (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))).regs r13 < 2 ^ E.W := by
      rw [upkHead_exit_regs E 11 s xbase m ab bb bl ob r13 (by decide), upkSt_r13]
      exact hbl
    rw [upkEpilogue_run E 27 _ hr1 hr4 hr12 hr13] at hb
    exact hb
  -- (4) glue
  obtain ⟨-, k1, s1, hstep1, hpc1, hk1, hs1⟩ := hpre
  have hloop' : Sem (programOfStatement upkStmt) E 11 27 s1
      (fun k s' => k ≤ 2 + 16 * (E.W * m) ∧
        s' = { runBlock upkCond.code E (upkSt E.W 11 s xbase m ab bb bl ob (E.W * m))
                with pc := 27 }) := by
    rw [hs1, upkSt_withPc]
    exact hloop
  obtain ⟨-, k2, s2, hstep2, hpc2, hk2, hs2⟩ := hloop'
  have hleg' : Sem (programOfStatement upkStmt) E 27 31 s2
      (fun k s' => k = 4 ∧ s' = upkEpi E xbase m ab bb bl ob s) := by
    rw [hs2]
    exact hleg
  obtain ⟨-, k3, s3, hstep3, hpc3, hk3, hs3⟩ := hleg'
  refine ⟨s3, ⟨k1 + k2 + k3, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have h1' : (k1 : ℝ) = 11 := by exact_mod_cast hk1
    have h2' : (k2 : ℝ) ≤ 2 + 16 * ((E.W * m : ℕ) : ℝ) := by exact_mod_cast hk2
    have h3' : (k3 : ℝ) = 4 := by exact_mod_cast hk3
    have hcast : ((k1 + k2 + k3 : ℕ) : ℝ) = (k1 : ℝ) + (k2 : ℝ) + (k3 : ℝ) := by
      push_cast
      ring
    have hrhs : ((16 * (E.W * m) + 17 : ℕ) : ℝ) = 16 * ((E.W * m : ℕ) : ℝ) + 17 := by
      push_cast
      ring
    rw [hcast, hrhs]
    linarith
  · have e : k1 + k2 + k3 = k3 + (k2 + k1) := by omega
    rw [e, Function.iterate_add_apply, Function.iterate_add_apply, hstep1, hstep2, hstep3]
  · rw [hs3]
    have hpc : (upkEpi E xbase m ab bb bl ob s).pc = upkStmt.len := by
      rw [upkEpi_pc, upkStmt_len]
    simp only [Halted, hpc, upk_halt_at]
  · rw [hs3]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r12 (by decide), upkSt_r12]
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r13 (by decide), upkSt_r13]
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r4 (by decide), upkSt_r4]
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r1 (by decide), upkSt_r1,
        upkList_eq_packedSupp' hWpos hpad]
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r12 (by decide), upkSt_r12]
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r13 (by decide), upkSt_r13]
    · simp [upkEpi, upkHead_exit_regs E 11 s xbase m ab bb bl ob r14 (by decide), upkSt_r14]
    · intro j hj
      have hj' : j < m := by rwa [hwords] at hj
      have hmem : (upkEpi E xbase m ab bb bl ob s).mem
          = upkMem E.W xbase s.mem ab (E.W * m) := by
        rw [upkEpi_mem, upkHead_exit_mem]
        exact upkSt_mem E.W 11 s xbase m ab bb bl ob (E.W * m)
      rw [hmem, upkMem_frame E.W xbase s.mem ab (E.W * m) (xbase + j) (Or.inl (by omega))]
      exact hpad j (by rw [hwords]; exact hj')
    · rw [upkEpi_mem, upkHead_exit_mem, upkSt_mem]
      exact upk_mList E xbase m ab y s hWpos hpad
  · rw [hs3, upkEpi_mem, upkHead_exit_mem, upkSt_mem]

/-- The scan's exit memory, read off the framed run: everything outside
`[ab, ab + m·W + 1)` is the entry memory. -/
theorem upkMem_frame_full (E : RAMEnv) (xbase m ab : ℕ) (m0 : ℕ → ℕ) (a : ℕ)
    (ha : a < ab ∨ ab + (E.W * m + 1) ≤ a) :
    upkMem E.W xbase m0 ab (E.W * m) a = m0 a :=
  upkMem_frame_wide E.W xbase m0 ab (E.W * m) a ha

/-! ## 5. From 2.3's own statement to the merge's entry predicate -/

theorem withPc_zero_idem (k : ℕ) (s : RAMState) :
    (withPc k (withPc 0 s) : RAMState) = withPc k s := rfl

/-- What 2.3's run hands over at `dCrBase + 282`: the output window `(r0, r1) = (bb, bl)`, the
decoded set `S` as the duplicate-free output list, the packed estimate intact in `m` words at
`xbase` (the payload frame), the window's word bound, and the word sizes. -/
def CrDecOut (E : RAMEnv) (xbase m bb bl : ℕ) (y : Fin (E.W * m) → ZMod 2)
    (S : Finset ℕ) (t : RAMState) : Prop :=
  t.regs 0 = bb ∧ t.regs 1 = bl ∧
    C8R.HoldsVecPad E.W m xbase t y ∧
    (outList t).Nodup ∧ (outList t).toFinset = S ∧
    (∀ p, p < bl → t.mem (bb + p) < 2 ^ E.W) ∧
    bl < 2 ^ E.W ∧ bb + bl ≤ 2 ^ E.W

/-- **The bridge from 2.3's published conclusion.**  `OutputsSupport` plus the window and the
payload frame is `CrDecOut`; this is the only place the published statement is read. -/
theorem crDecOut_of_outputsSupport {E : RAMEnv} {N : ℕ} {x : Fin N → ZMod 2}
    {xbase m bb bl : ℕ} {y : Fin (E.W * m) → ZMod 2} {t : RAMState}
    (h : OutputsSupport t x) (h0 : t.regs 0 = bb) (h1 : t.regs 1 = bl)
    (hpad : C8R.HoldsVecPad E.W m xbase t y)
    (hval : ∀ p, p < bl → t.mem (bb + p) < 2 ^ E.W)
    (hbl : bl < 2 ^ E.W) (hbbbl : bb + bl ≤ 2 ^ E.W) :
    CrDecOut E xbase m bb bl y
      ((Finset.univ.filter fun i : Fin N => x i = 1).image Fin.val) t := by
  refine ⟨h0, h1, hpad, h.1, ?_, hval, hbl, hbbbl⟩
  ext v
  rw [List.mem_toFinset, h.2 v]
  constructor
  · rintro ⟨i, rfl, hi⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨i, rfl, (Finset.mem_filter.mp hi).2⟩

theorem packedSupp_nodup (W m : ℕ) (y : Fin (W * m) → ZMod 2) :
    (packedSupp W m y).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem packedSupp_lt (W m : ℕ) (y : Fin (W * m) → ZMod 2) :
    ∀ v ∈ packedSupp W m y, v < W * m := by
  intro v hv
  unfold packedSupp at hv
  exact List.mem_range.mp (List.mem_of_mem_filter hv)

theorem packedSupp_length_le (W m : ℕ) (y : Fin (W * m) → ZMod 2) :
    (packedSupp W m y).length ≤ W * m :=
  le_trans (List.length_filter_le _ _) (by simp)

theorem mList_getD (m0 : ℕ → ℕ) (b len p : ℕ) (hp : p < len) :
    (RMR.mList m0 b len).getD p 0 = m0 (b + p) := by
  unfold RMR.mList
  rw [List.getD_eq_getElem _ 0 (by simp [hp])]
  simp [hp]

/-- **`UpkOut` plus the decoder's window gives `CrMergeInD`.**  The unpack writes only inside
`[ab, ab + m·W + 1)`; the disjointness conjunct of `CrMergeInD` puts the decoder's output window
`[bb, bb + bl)` outside it, so the residual list survives the repack. -/
theorem crMergeInD_of_upk {E : RAMEnv} {xbase m ab bb bl ob : ℕ} {y : Fin (E.W * m) → ZMod 2}
    {S : Finset ℕ} {s t : RAMState}
    (hOut : UpkOut E.W m xbase ab bb bl ob y t)
    (hmem : t.mem = upkMem E.W xbase s.mem ab (E.W * m))
    (h0 : s.regs 0 = bb) (h1 : s.regs 1 = bl)
    (hsnd : (outList s).Nodup) (hsS : (outList s).toFinset = S)
    (hval : ∀ p, p < bl → s.mem (bb + p) < 2 ^ E.W)
    (hWm : E.W * m < 2 ^ E.W)
    (hdisj : bb + bl ≤ ab ∨ ab + (m * E.W + 1) ≤ bb)
    (halw : (packedSupp E.W m y).length < 2 ^ E.W)
    (habal : ab + (packedSupp E.W m y).length ≤ 2 ^ E.W)
    (hbl : bl < 2 ^ E.W) (hbbbl : bb + bl ≤ 2 ^ E.W)
    (hobig : ob + ((packedSupp E.W m y).length + bl) + 1 < 2 ^ E.W)
    (hAob : ab + (packedSupp E.W m y).length ≤ ob) (hBob : bb + bl ≤ ob) :
    CrMergeInD E ab (packedSupp E.W m y).length bb bl ob m (packedSupp E.W m y) S t := by
  obtain ⟨ht0, ht1, h10, h11, h12, h13, h14, -, hmlist⟩ := hOut
  have hdisjw : bb + bl ≤ ab ∨ ab + (E.W * m + 1) ≤ bb := by
    rcases hdisj with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [Nat.mul_comm] at h; exact h)
  have hout_t : outList t = RMR.mList t.mem bb bl := by
    simp only [outList, RMR.mList, ht0, ht1]
  have hout_s : outList s = RMR.mList s.mem bb bl := by
    simp only [outList, RMR.mList, h0, h1]
  have hframe : RMR.mList t.mem bb bl = RMR.mList s.mem bb bl := by
    simp only [RMR.mList]
    refine List.map_congr_left (fun i hi => ?_)
    have hib : i < bl := List.mem_range.mp hi
    rw [hmem, upkMem_frame_full E xbase m ab s.mem (bb + i) ?_]
    rcases hdisjw with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  refine ⟨⟨h10, h11, h12, h13, h14, ht0, ht1, hmlist, ?_, ?_, packedSupp_nodup E.W m y,
    ?_, ?_, halw, hbl, habal, hbbbl, hobig, Or.inl hAob, Or.inl hBob⟩, hdisj⟩
  · rw [hout_t, hframe, ← hout_s]; exact hsnd
  · rw [hout_t, hframe, ← hout_s]; exact hsS
  · intro p hp
    rw [← mList_getD t.mem ab (packedSupp E.W m y).length p hp, hmlist]
    exact lt_of_lt_of_le
      (packedSupp_lt E.W m y _ (by
        rw [List.getD_eq_getElem _ 0 hp]; exact List.getElem_mem _)) hWm.le
  · intro p hp
    rw [hmem]
    rw [upkMem_frame_full E xbase m ab s.mem (bb + p) (by
      rcases hdisjw with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))]
    exact hval p hp

/-! ## 6. The composed stage: decoder · setup · unpack · merge -/

/-- **The composed `cr` stage, with no decoder-side hypothesis beyond 2.3's own statement.**

The decoder's half is exactly `cr23_decoding` read through `CrDecOut` (its `OutputsSupport`
conclusion, the output window, the payload frame and the window's word bound); the setup, the
unpack and the merge are the three published blocks.  The output is the symmetric difference of
the repacked estimate with the decoded residual. -/
theorem stageRun_crPipeline (Sinit Srow Sdec Sassem Sres : Stmt) (E : RAMEnv)
    {xbase m ab bb bl ob : ℕ} {y : Fin (E.W * m) → ZMod 2} {S xhat : Finset ℕ} {Tdec : ℝ}
    {Pre : RAMState → Prop}
    (hdec : ∀ s : RAMState, s.pc = 0 →
      Pre (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement decStmt) E Tdec s s' ∧
        CrDecOut E xbase m bb bl y S
          (withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len) s'))
    (hxhat : (packedSupp E.W m y).toFinset = xhat)
    (hW : 1 < 2 ^ E.W) (hWm : E.W * m < 2 ^ E.W) (hxdisj : xbase + m ≤ ab)
    (hab : ab + E.W * m + 1 < 2 ^ E.W) (hbb : bb < 2 ^ E.W) (hbl : bl < 2 ^ E.W)
    (hob : ob < 2 ^ E.W) (hdisj : bb + bl ≤ ab ∨ ab + (m * E.W + 1) ≤ bb)
    (hobig : ob + ((packedSupp E.W m y).length + bl) + 1 < 2 ^ E.W)
    (hAob : ab + (packedSupp E.W m y).length ≤ ob) (hBob : bb + bl ≤ ob) :
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob)) E
      (dCrBase Sinit Srow Sdec Sassem Sres)
      (dEnd Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob))
      (Tdec + 5 + ((16 * (E.W * m) + 17 : ℕ) : ℝ) + RMR.mrgCost (packedSupp E.W m y).length bl)
      Pre (fun s' => OutListIs s' (symmDiff xhat S)) := by
  intro t htpc hPre
  -- word bounds read off the block arithmetic
  have hxw : xbase < 2 ^ E.W := by omega
  have hmw : m < 2 ^ E.W := by omega
  have habw : ab < 2 ^ E.W := by omega
  have halw : (packedSupp E.W m y).length < 2 ^ E.W := by
    have := packedSupp_length_le E.W m y; omega
  have habal : ab + (packedSupp E.W m y).length ≤ 2 ^ E.W := by
    have := packedSupp_length_le E.W m y; omega
  -- 1. 2.3's decoder, relocated to `dCrBase`
  obtain ⟨s1, ⟨k1, hk1, hrun1, hhalt1⟩, hD1⟩ :=
    hdec (withPc 0 t) rfl
      (by
        rw [show (withPc (dCrBase Sinit Srow Sdec Sassem Sres) (withPc 0 t) : RAMState) = t
          from withPc_self htpc]
        exact hPre)
  have hhalt1' : s1.pc = decStmt.len := haltPc_of_haltFree decStmt_haltFree hhalt1
  obtain ⟨k1', hk1', hstep1⟩ := run_transport
    (G := progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob))
    (S := decStmt) (base := dCrBase Sinit Srow Sdec Sassem Sres) (T := Tdec)
    (s := withPc 0 t) (s' := s1)
    (at_crStage4_dec Sinit Srow Sdec Sassem Sres decStmt E.W xbase m ab ob)
    decStmt_noJump ⟨k1, hk1, hrun1, hhalt1⟩ rfl hhalt1'
  have hs1 : (withPc (dCrBase Sinit Srow Sdec Sassem Sres) (withPc 0 t) : RAMState) = t :=
    withPc_self htpc
  rw [hs1] at hstep1
  -- 2. the setup, with its (empty) memory footprint
  obtain ⟨h0, h1, hpad, hnd, hset, hval, hblw, hbbbl⟩ := hD1
  obtain ⟨-, k2, s2, hstep2, hpc2, hk2, hs2⟩ := by
    have := Sem.block
      (progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob)) E
      (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len) (upkSetup E.W xbase m ab ob)
      (withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len) s1)
      (at_crStage4_setup Sinit Srow Sdec Sassem Sres decStmt E.W xbase m ab ob)
      (upkSetup_noBranch _ _ _ _ _) rfl
    rwa [upkSetup_length] at this
  have hs2' : s2 = upkSetupSt E xbase m ab ob
      (withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len + 5) s1) := by
    rw [hs2]
    have h := upkSetup_run E (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len)
      (withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len) s1) xbase m ab ob
      hxw habw hob hmw
    simpa only [withPc] using h
  have hs2mem : s2.mem = s1.mem := by
    rw [hs2']
    rfl
  have hIn2 : UpkIn E xbase m ab bb bl ob y s2 := by
    rw [hs2']
    refine ⟨?_, ?_, upkSetupSt_r2 E xbase m ab ob _, upkSetupSt_r3 E xbase m ab ob _,
      upkSetupSt_r4 E xbase m ab ob _, upkSetupSt_r5 E xbase m ab ob _,
      upkSetupSt_r6 E xbase m ab ob _,
      holdsVecPad_congr_mem (by rfl :
        (withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len) s1).mem
          = (upkSetupSt E xbase m ab ob
              (withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len + 5) s1)).mem) hpad⟩
    · rw [upkSetupSt_r0]; exact h0
    · rw [upkSetupSt_r1]; exact h1
  -- 3. the unpack, with its memory footprint
  obtain ⟨s3, ⟨k3, hk3, hrun3, hhalt3⟩, hOut3, hmem3⟩ :=
    upk_halts_frame E xbase m ab bb bl ob y (withPc 0 s2) hIn2 rfl hW hWm hxdisj hab hbb hbl hob
  have hhalt3' : s3.pc = upkStmt.len := haltPc_of_haltFree upkStmt_haltFreeB hhalt3
  obtain ⟨k3', hk3', hstep3⟩ := run_transport
    (G := progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob))
    (S := upkStmt) (base := dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len + 5)
    (T := ((16 * (E.W * m) + 17 : ℕ) : ℝ)) (s := withPc 0 s2) (s' := s3)
    (at_crStage4_upk Sinit Srow Sdec Sassem Sres decStmt E.W xbase m ab ob)
    upkStmt_noJumpB ⟨k3, hk3, hrun3, hhalt3⟩ rfl hhalt3'
  have hs3 : (withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len + 5)
      (withPc 0 s2) : RAMState) = s2 := withPc_self hpc2
  rw [hs3] at hstep3
  -- 4. the merge
  have hmem31 : s3.mem = upkMem E.W xbase s1.mem ab (E.W * m) := by
    have h3 := hmem3
    have h2 : (withPc 0 s2).mem = s1.mem := by
      show s2.mem = s1.mem
      exact hs2mem
    rw [h3, h2]
  obtain ⟨him, -⟩ : CrMergeInD E ab (packedSupp E.W m y).length bb bl ob m
      (packedSupp E.W m y) S (withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len + 5 + 31) s3)
      ∧ True :=
    ⟨crMergeInD_of_upk (s := s1) (E := E) (xbase := xbase) (m := m) (ab := ab) (bb := bb)
      (bl := bl) (ob := ob) (y := y) (S := S) hOut3 hmem31 h0 h1 hnd hset hval hWm hdisj
      halw habal hblw hbbbl hobig hAob hBob, trivial⟩
  obtain ⟨k4, s4, hk4, hstep4, hpc4, hpost⟩ :=
    stageRun_mergeAtD (G := progDecOfTop Sinit Srow Sdec Sassem Sres
        (CrStage4 decStmt E.W xbase m ab ob))
      (E := E) (base := dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len + 5 + 31)
      (ab := ab) (al := (packedSupp E.W m y).length) (bb := bb) (bl := bl) (ob := ob) (m := m)
      (Lx := packedSupp E.W m y) (S := S) (xhat := xhat)
      (at_crStage4_mrg Sinit Srow Sdec Sassem Sres decStmt E.W xbase m ab ob) hW hxhat
      (withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len + 5 + 31) s3) rfl him
  -- 5. glue the four runs
  refine ⟨k1' + k2 + k3' + k4, s4, ?_, ?_, ?_, hpost⟩
  · have e1 : (k1' : ℝ) ≤ Tdec := hk1'
    have e2 : (k2 : ℝ) ≤ 5 := by rw [hk2]; norm_num
    have e3 : (k3' : ℝ) ≤ ((16 * (E.W * m) + 17 : ℕ) : ℝ) := hk3'
    have e4 : (k4 : ℝ) ≤ RMR.mrgCost (packedSupp E.W m y).length bl := hk4
    have hcast : ((k1' + k2 + k3' + k4 : ℕ) : ℝ)
        = (k1' : ℝ) + (k2 : ℝ) + (k3' : ℝ) + (k4 : ℝ) := by push_cast; ring
    rw [hcast]; linarith
  · rw [upkStmt_len] at hstep3
    rw [show k1' + k2 + k3' + k4 = k4 + (k3' + (k2 + k1')) from by omega,
      Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
      hstep1, hstep2, hstep3, hstep4]
  · rw [hpc4, dEnd_crStage4, RMR.mrgStmtFull_len]
    try omega

end CRS
end LinearSetReconciliation327.Main


