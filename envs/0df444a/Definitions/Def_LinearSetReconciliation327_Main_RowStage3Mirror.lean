-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_RowStage3Mirror
-- name    : LinearSetReconciliation327_Main_RowStage3Mirror
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T09:37:19.798357+00:00
-- url     : https://prove2.me/theorems/a8c39333-eb41-4cef-a582-75319f30e2bc
-- title:
--   Row-chain mirror: the real row stage on the `DecoderLemmas` side (old-layout `RDec`)
-- statement:
--   A byte-identical re-host of `…_RowStage3Pay20261122` with only the `import` lines replaced (`P21DetBndComp`→`DecoderLemmas`, `P21BndAuxPay`→`P21BndAux20261122`, `RowStage2Pay`→`RowStage2Mirror20261122`).  The declarations `zSaveCode`/`zRestoreCode`/`zReloadCode`/`zSetupCode`, `zRowStage_real` and their proofs are copied verbatim; no proof changed.  NOTE: the identifier `rowPayBase` resolves to the `DecoderLemmas`-side `RDec` table version, because the `Pay` layout re-defines the whole `RDec` layer under names that already exist in this environment (see the `RowDecodePay` duplicate-name audit).  This module is therefore the faithful mirror of the *old-layout* row stage, not of the `Pay` arithmetic-progression layout; a `Pay` mirror would require renaming the `RDec` layer.  Definitions and proved lemmas only; local `cpl` 6 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Theorem 1.1 (the top-level decoder); the project's verified row-stage development.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Definitions.Def_LinearSetReconciliation327_Main_P21BndAux20261122
import Definitions.Def_LinearSetReconciliation327_Main_RowStage2Mirror20261122
/-!
# `RowStage3` — the row loop's per-iteration body with the real decoder and repack

The control flow is the one proved in `Def_..._RowStage2Mirror20261122` (`zProgDecOfTop`,
`zLoopHeads`, `stageRun_counted_loop_le`, `zRowStage_dispatch`).  This bundle supplies the
per-iteration `hbody` from the real stage programs:

* `clear` + reload + `stage` (the `RLR` splice, from the mirror of `rowloop/RowLoop.lean`);
* the real Proposition 2.1 decoder `pinsketchRunStmt t w β`, relocated from base `0` to its
  address inside the row body by `CRS.run_transport` and `pinsketch_decoding_at_bounded`
  (the byte-identical mirror of the proved submission `tmp23/Sol_p21_decode_at_bnd.lean`);
* the real repack loop `RDec.repackStmt` (`RDL.repackStageRun`), with the exact exit state from
  `RDL.repackLoop_sem` (the published `StageRun` forgets the registers; the row loop needs them);
* `d65Inc` and the loop's trailing `jmp`.

No existing file is modified.  The mirrors `RowLoop`, `RowStage2` and the decoder are byte-identical
copies; the only `sorryAx` in the development comes from the two published `Theorems.Thm_*`
statement mirrors that `pinsketch_decoding_at_bounded` uses (platform-proved).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace RSD3

open R66 RDec RMR RSD

/-! ## 3. Straight-line glue: save `j`, `d` to memory; restore them and zero the rest -/

/-- The register shape just before `d65Inc`: counter `j`, bound `d`, everything else zero. -/
def zPreIncRegs (j d : ℕ) : Fin 16 → ℕ :=
  fun i => if i = r1 then j else if i = r2 then d else 0

/-- Save the loop counter and the bound into two cells above the row outputs. -/
def zSaveCode (cell : ℕ) : List Instr :=
  [iImm r15 cell, iSt r15 r1, iImm r15 (cell + 1), iSt r15 r2]

/-- Zero every register, then reload the counter and the bound from the two cells. -/
def zRestoreCode (cell : ℕ) : List Instr :=
  zeroRegsCode ++ [iImm r15 cell, iLd r1 r15, iImm r15 (cell + 1), iLd r2 r15, iImm r15 0]

theorem zSaveCode_length (cell : ℕ) : (zSaveCode cell).length = 4 := rfl

theorem zRestoreCode_length (cell : ℕ) : (zRestoreCode cell).length = 21 := by
  simp [zRestoreCode, zeroRegsCode]

theorem zSave_run (E : RAMEnv) (pc cell : ℕ) (r : Fin 16 → ℕ) (m : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hcell : cell < 2 ^ E.W) (hcell1 : cell + 1 < 2 ^ E.W) :
    runBlock (zSaveCode cell) E ⟨pc, r, m⟩
      = ⟨pc + 4, Function.update r r15 (cell + 1),
          Function.update (Function.update m cell (r r1)) (cell + 1) (r r2)⟩ := by
  simp [zSaveCode, runBlock, execInstr, Function.update_self, Function.update_of_ne,
    Nat.mod_eq_of_lt hcell, Nat.mod_eq_of_lt hcell1, Nat.add_assoc]

theorem zRestore_run (E : RAMEnv) (pc cell j d : ℕ) (r : Fin 16 → ℕ) (m : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hcell : cell < 2 ^ E.W) (hcell1 : cell + 1 < 2 ^ E.W)
    (hj : m cell = j) (hd : m (cell + 1) = d) (hjw : j < 2 ^ E.W) (hdw : d < 2 ^ E.W) :
    runBlock (zRestoreCode cell) E ⟨pc, r, m⟩ = ⟨pc + 21, zPreIncRegs j d, m⟩ := by
  rw [show zRestoreCode cell = zeroRegsCode ++
    [iImm r15 cell, iLd r1 r15, iImm r15 (cell + 1), iLd r2 r15, iImm r15 0] from rfl,
    runBlock_append, zeroRegsCode_run]
  simp [runBlock, execInstr, zPreIncRegs, Function.update_self, Function.update_of_ne,
    Nat.mod_eq_of_lt hcell, Nat.mod_eq_of_lt hcell1, hj, hd, Nat.mod_eq_of_lt hjw,
    Nat.mod_eq_of_lt hdw, Nat.add_assoc]
  funext i
  fin_cases i <;>
    simp [zPreIncRegs, zeroRegs, Function.update_self, Function.update_of_ne, Fin.ext_iff]

/-- One counter step from the restored state: `d65Inc` lands on the head family at `j+1`. -/
theorem zD65Inc_pre (E : RAMEnv) (pc a d j : ℕ) (m : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hjw : j + 1 < 2 ^ E.W) :
    runBlock d65Inc E ⟨pc, zPreIncRegs j d, m⟩
      = ⟨pc + 2, (zLoopHeads a d (fun _ => m) (j + 1)).regs, m⟩ := by
  rw [zD65Inc_run E pc (zPreIncRegs j d) m hW (Nat.mod_eq_of_lt hW)]
  refine zRamState_eq_of rfl ?_ rfl
  intro i
  fin_cases i <;>
    simp [zPreIncRegs, zLoopHeads, Function.update_self, Function.update_of_ne,
      Nat.mod_eq_of_lt hjw]

/-- Reload the loop counter from the saved cell (the clear has clobbered every register). -/
def zReloadCode (cell : ℕ) : List Instr := [iImm r15 cell, iLd r1 r15]

theorem zReloadCode_length (cell : ℕ) : (zReloadCode cell).length = 2 := rfl

/-- The two-instruction reload's concrete run. -/
theorem zReload_run (E : RAMEnv) (pc cell : ℕ) (r : Fin 16 → ℕ) (m : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hcell : cell < 2 ^ E.W) :
    runBlock (zReloadCode cell) E ⟨pc, r, m⟩
      = ⟨pc + 2, Function.update (Function.update r r15 (cell % 2 ^ E.W)) r1 (m (cell % 2 ^ E.W) % 2 ^ E.W), m⟩ := by
  simp [zReloadCode, runBlock, execInstr, Function.update_self, Function.update_of_ne,
    Nat.mod_eq_of_lt hcell, Nat.add_assoc]

/-- **Clear, reload `r1 := j` from the saved cell, then stage** — the pre-decode half of the
generic (non-unrolled) row body.  This is `RLR.clearReloadStage_sem` with the immediate `iImm r1 j`
replaced by the memory load the loop body can actually use. -/
theorem zClearReloadStage_sem {P : Program} {E : RAMEnv} {pc t j K cell : ℕ} {s : RAMState}
    (hAtClear : At P pc (Stmt.compile (clearFull 0 (decoderAllocEnd t)) pc))
    (hAtReload : At P (pc + 15) (zReloadCode cell))
    (hAtStage : At P (pc + 17) (Stmt.compile stageStmt (pc + 17)))
    (hW : 1 < 2 ^ E.W) (hW16 : 16 < 2 ^ E.W) (hK : decoderAllocEnd t < 2 ^ E.W)
    (hcell : cell < 2 ^ E.W) (hcellge : decoderAllocEnd t ≤ cell)
    (hcellj : s.mem cell = j) (hjw : j < 2 ^ E.W)
    (hpc : s.pc = pc)
    (hdst : stageBase E + stageLen E ≤ 2 ^ E.W)
    (hsrc : rowPayBase E j + stageLen E ≤ 2 ^ E.W)
    (hword : ∀ i, i < stageLen E → s.mem (rowPayBase E j + i) < 2 ^ E.W)
    (hdisj : rowPayBase E j + stageLen E ≤ stageBase E ∨
      stageBase E + stageLen E ≤ rowPayBase E j)
    (hβK : stageBase E + stageLen E ≤ K) (hKle : K ≤ decoderAllocEnd t)
    (hKrow : K ≤ rowPayBase E j) :
    ∃ k s', k ≤ 17 + 8 * decoderAllocEnd t + stageCost E ∧ (step P E)^[k] s = s' ∧
      s'.pc = pc + 17 + stageStmt.len ∧ s'.regs = zeroRegs ∧
      (∀ a, stageLen E ≤ a → a < stageBase E → s'.mem a = 0) ∧
      (∀ a, stageBase E + stageLen E ≤ a → a < K → s'.mem a = 0) ∧
      (∀ a, decoderAllocEnd t ≤ a → s'.mem a = s.mem a) ∧
      s'.mem = writeArray (stageBase E) (clearMem 0 s.mem (decoderAllocEnd t))
        (fun i => clearMem 0 s.mem (decoderAllocEnd t) (rowPayBase E j + i)) (stageLen E) := by
  obtain ⟨k₁, s₁, hk₁, hstep₁, hmem₁, hpc₁⟩ :=
    clearScratch_mem_eq (P := P) (E := E) (pc := pc) (t := t) (s := s) hAtClear hW hK hpc
  obtain ⟨p₁, rg₁, mm₁⟩ := s₁
  dsimp only at hpc₁ hmem₁
  have hcell' : cell % 2 ^ E.W = cell := Nat.mod_eq_of_lt hcell
  have hmemcell : mm₁ cell = j := by
    rw [hmem₁]
    rw [clearMem_frame 0 s.mem (decoderAllocEnd t) cell (Or.inr (by omega))]
    exact hcellj
  have hblock : Sem P E (pc + 15) (pc + 17) ⟨pc + 15, rg₁, mm₁⟩
      (fun k z => k = 2 ∧ z = ⟨pc + 17,
        Function.update (Function.update rg₁ r15 cell) r1 j, mm₁⟩) := by
    have hb := Sem.block P E (pc + 15) (zReloadCode cell) ⟨pc + 15, rg₁, mm₁⟩ hAtReload
      (by simp [zReloadCode, NoBranch, Instr.NoBranchI]) rfl
    refine Sem.mono hb ?_
    intro k z hz
    obtain ⟨hk, rfl⟩ := hz
    refine ⟨hk, ?_⟩
    rw [zReload_run E (pc + 15) cell rg₁ mm₁ hW hcell]
    simp only [hcell', hmemcell, Nat.mod_eq_of_lt hjw]
  obtain ⟨-, k₂, s₂, hstep₂, hpc₂, hk₂, hstate₂⟩ :=
    R66.Sem.trans_le
      (Sem.mono hblock (fun k z hz => ⟨le_of_eq hz.1, hz.2⟩))
      (stage_mem_writeArray (P := P) (E := E) (pc := pc + 17) (j := j) (m := mm₁)
        (r := Function.update (Function.update rg₁ r15 cell) r1 j) hAtStage hW hW16 rfl hdst hsrc
        (by
          intro i hi
          rw [hmem₁]
          by_cases hc : rowPayBase E j + i < decoderAllocEnd t
          · rw [show clearMem 0 s.mem (decoderAllocEnd t) (rowPayBase E j + i) = 0 from by
              simpa using clearMem_get 0 s.mem (decoderAllocEnd t) (rowPayBase E j + i) hc]
            exact Nat.two_pow_pos E.W
          · rw [clearMem_frame 0 s.mem (decoderAllocEnd t) (rowPayBase E j + i) (Or.inr (by omega))]
            exact hword i hi)
        hdisj)
  refine ⟨k₁ + k₂, s₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hstep₁,
      show (⟨p₁, rg₁, mm₁⟩ : RAMState) = ⟨pc + 15, rg₁, mm₁⟩ from by rw [hpc₁], hstep₂]
  · rw [hstate₂]
  · rw [hstate₂]
  · intro a hLa haβ
    rw [hstate₂, hmem₁]
    show writeArray (stageBase E) (clearMem 0 s.mem (decoderAllocEnd t))
      (fun i => clearMem 0 s.mem (decoderAllocEnd t) (rowPayBase E j + i)) (stageLen E) a = 0
    rw [writeArray_frame (stageBase E) (clearMem 0 s.mem (decoderAllocEnd t)) _ (stageLen E) a
      (Or.inl haβ)]
    exact (by simpa using clearMem_get 0 s.mem (decoderAllocEnd t) a (by omega))
  · intro a ha haK
    rw [hstate₂, hmem₁]
    show writeArray (stageBase E) (clearMem 0 s.mem (decoderAllocEnd t))
      (fun i => clearMem 0 s.mem (decoderAllocEnd t) (rowPayBase E j + i)) (stageLen E) a = 0
    rw [writeArray_frame (stageBase E) (clearMem 0 s.mem (decoderAllocEnd t)) _ (stageLen E) a
      (Or.inr ha)]
    exact (by simpa using clearMem_get 0 s.mem (decoderAllocEnd t) a (by omega))
  · intro a ha
    rw [hstate₂, hmem₁]
    show writeArray (stageBase E) (clearMem 0 s.mem (decoderAllocEnd t))
      (fun i => clearMem 0 s.mem (decoderAllocEnd t) (rowPayBase E j + i)) (stageLen E) a = s.mem a
    rw [writeArray_frame (stageBase E) (clearMem 0 s.mem (decoderAllocEnd t)) _ (stageLen E) a
      (Or.inr (by omega))]
    exact clearMem_frame 0 s.mem (decoderAllocEnd t) a (Or.inr (by omega))
  · rw [hstate₂, hmem₁]

/-- The 16-instruction register setup between the decoder's `decoderPost` and `RepackPre`: it copies
the decoded list base/length to `r7`/`r8`, computes `W`, `wordsOf W R`, the row slot of the *saved*
counter `j` (not of the decoded length), and zeroes the repack cursor `r0`. -/
def zSetupCode (cell : ℕ) : List Instr :=
  [iBor r7 r0 r0, iBor r8 r1 r1,
   iImm r15 12, iTbl r11 r15,
   iImm r15 2, iTbl r6 r15,
   iAdd r6 r6 r11, iImm r15 1, iSub r6 r6 r15, iDiv r6 r6 r11,
   iImm r15 cell, iLd r15 r15,
   iMul r15 r6 r15,
   iImm r14 3, iTbl r5 r14, iAdd r5 r5 r15,
   iImm r0 0]

theorem zSetupCode_length (cell : ℕ) : (zSetupCode cell).length = 17 := rfl

/-! ## 4. The `d`-fold row loop over a *state predicate* (no memory family)

The published loop rule (`zTopLoopHeads_stageRun`) is phrased with a family `s j` and therefore
needs a fixed memory sequence `M`.  The real body's memory is not a parameter: it is the machine's
own memory after decoding and repacking row `j`.  The induction below carries an arbitrary state
predicate `Inv j m` instead, and proves the loop directly.  No `M` appears. -/

/-- The register shape of the row-loop head at iteration `j` (the `zLoopHeads` registers). -/
def zHeadsRegs (j d : ℕ) : Fin 16 → ℕ :=
  fun i => if i = r1 then j else if i = r2 then d
    else if i = r7 then (if j = 0 then 0 else 1) else 0

theorem zHeadsRegs_r1 (j d : ℕ) : zHeadsRegs j d r1 = j := by
  simp [zHeadsRegs]

theorem zHeadsRegs_r2 (j d : ℕ) : zHeadsRegs j d r2 = d := by
  simp [zHeadsRegs]

theorem zHeadsRegs_r7 (j d : ℕ) : zHeadsRegs j d r7 = (if j = 0 then 0 else 1) := by
  simp [zHeadsRegs]

theorem zLoopHeads_regs_heads (a d : ℕ) (M : ℕ → ℕ → ℕ) (j : ℕ) :
    (zLoopHeads a d M j).regs = zHeadsRegs j d := rfl

/-- **The row loop, inducted over `d` with a state predicate.**  `hbody` is the real per-iteration
body: from any head state at `a` with the right registers and `Inv j`, the body (test included)
returns to `a` with the registers of iteration `j+1` and `Inv (j+1)`.  The conclusion has no memory
family: the exit state satisfies `Inv d`, `r1 = d`, `r2 = d`. -/
theorem zRowLoop_inv_stageRun {P : Program} {E : RAMEnv} {a : ℕ} {b : Stmt} {d K : ℕ}
    {Inv : ℕ → (ℕ → ℕ) → Prop} {s0 : RAMState}
    (hAt : At P a (Stmt.compile (Stmt.loop d65Cond b) a)) (hW : 1 < 2 ^ E.W)
    (hstart : s0.pc = a) (hstartRegs : s0.regs = zHeadsRegs 0 d) (hstartInv : Inv 0 s0.mem)
    (hbody : ∀ j < d, ∀ t : RAMState, t.pc = a → t.regs = zHeadsRegs j d → Inv j t.mem →
      ∃ (s' : RAMState) (k : ℕ), k ≤ K ∧
        (step P E)^[k] { runBlock d65Cond.code E t with pc := a + d65Cond.code.length + 1 } = s' ∧
        s'.pc = a ∧ s'.regs = zHeadsRegs (j + 1) d ∧ Inv (j + 1) s'.mem) :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ (d : ℝ) * ((K : ℝ) + 2) + 3 ∧
      (step P E)^[k] s0 = s' ∧
      s'.pc = a + d65Cond.code.length + b.len + 2 ∧
      s'.regs 1 = d ∧ s'.regs 2 = d ∧ Inv d s'.mem := by
  classical
  let next : ℕ → RAMState → RAMState := fun j prev =>
    if h : j < d then
      if hp : prev.pc = a ∧ prev.regs = zHeadsRegs j d ∧ Inv j prev.mem then
        Classical.choose (hbody j h prev hp.1 hp.2.1 hp.2.2)
      else prev
    else prev
  let s : ℕ → RAMState := fun j => Nat.rec s0 next j
  have hchoose : ∀ (j : ℕ) (hj : j < d),
      ∀ (ih : (s j).pc = a ∧ (s j).regs = zHeadsRegs j d ∧ Inv j (s j).mem),
      s (j + 1) = Classical.choose (hbody j hj (s j) ih.1 ih.2.1 ih.2.2) := by
    intro j hj ih
    show next j (s j) = _
    dsimp only [next]
    rw [dif_pos hj, dif_pos ih]
  have hS : ∀ j ≤ d, (s j).pc = a ∧ (s j).regs = zHeadsRegs j d ∧ Inv j (s j).mem := by
    intro j hj
    induction j with
    | zero =>
        simpa [s] using (show s0.pc = a ∧ s0.regs = zHeadsRegs 0 d ∧ Inv 0 s0.mem from
          ⟨hstart, hstartRegs, hstartInv⟩)
    | succ j ih =>
        have hj' : j < d := by omega
        have ih' := ih (by omega)
        rw [hchoose j hj' ih']
        obtain ⟨k, hk, hstep, hpc, hregs, hinv⟩ :=
          Classical.choose_spec (hbody j hj' (s j) ih'.1 ih'.2.1 ih'.2.2)
        exact ⟨hpc, hregs, hinv⟩
  have hpcAll : ∀ j, (s j).pc = a := by
    intro j
    by_cases hj : j ≤ d
    · exact (hS j hj).1
    · have hconst : ∀ m, s (d + m) = s d := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            have h : ¬ d + m < d := by omega
            show next (d + m) (s (d + m)) = s d
            dsimp only [next]
            rw [dif_neg h]
            exact ih
      obtain ⟨m, rfl⟩ : ∃ m, j = d + m := ⟨j - d, by omega⟩
      rw [hconst m]
      exact (hS d le_rfl).1
  have hgo : ∀ j < d, d65Cond.eval (s j) := by
    intro j hj
    have h1 : (s j).regs r1 = j := by rw [(hS j (by omega)).2.1, zHeadsRegs_r1]
    have h2 : (s j).regs r2 = d := by rw [(hS j (by omega)).2.1, zHeadsRegs_r2]
    simp [d65Cond, Cond.eval, h1, h2, hj]
  have hstop : ¬ d65Cond.eval (s d) := by
    have h1 : (s d).regs r1 = d := by rw [(hS d le_rfl).2.1, zHeadsRegs_r1]
    have h2 : (s d).regs r2 = d := by rw [(hS d le_rfl).2.1, zHeadsRegs_r2]
    simp [d65Cond, Cond.eval, h1, h2]
  have hbodySem : ∀ j < d, Sem P E (a + d65Cond.code.length + 1) a
      { runBlock d65Cond.code E (s j) with pc := a + d65Cond.code.length + 1 }
      (fun k s' => k ≤ K ∧ s' = s (j + 1)) := by
    intro j hj
    have ih := hS j (by omega)
    obtain ⟨k, hk, hstep, hpc, -, -⟩ :=
      Classical.choose_spec (hbody j hj (s j) ih.1 ih.2.1 ih.2.2)
    refine ⟨rfl, k, Classical.choose (hbody j hj (s j) ih.1 ih.2.1 ih.2.2), hstep, hpc,
      ⟨hk, (hchoose j hj ih).symm⟩⟩
  obtain ⟨k, s', hk, hstep, hpc, hst⟩ :=
    stageRun_counted_loop_le (P := P) (E := E) (a := a) (c := d65Cond) (b := b) (n := d)
      (s := s) (cost := fun _ => K) (K := (K : ℝ)) hAt hW hpcAll hgo hstop hbodySem
      (fun _ _ => le_refl _) (by positivity)
  refine ⟨k, s', ?_, hstep, ?_, ?_, ?_, ?_⟩
  · rw [zD65Cond_code_length] at hk
    norm_num at hk ⊢
    exact hk
  · rw [hst]
  · rw [hst]
    change (runBlock d65Cond.code E (s d)).regs 1 = d
    rw [(zCond_regs_pres E (s d)).1, (hS d le_rfl).2.1, zHeadsRegs_r1]
  · rw [hst]
    change (runBlock d65Cond.code E (s d)).regs 2 = d
    rw [(zCond_regs_pres E (s d)).2, (hS d le_rfl).2.1, zHeadsRegs_r2]
  · rw [hst]
    change Inv d (runBlock d65Cond.code E (s d)).mem
    rw [zCond_mem]
    exact (hS d le_rfl).2.2

/-! ## 5. The real per-iteration cost -/

/-- The body's cost with the real stages (all costs at their published upper bounds):
save `4` + clear/reload/stage `17 + 8·decoderAllocEnd t + stageCost E` + decoder
`PDB + 24L + 40` + setup `17` + repack `20Λ + 20` + restore `21` + `d65Inc` `2` + `jmp` `1`.
With `L = stageLen E`, `stageCost E = 12L + 32` and `decoderAllocEnd t = 8t² + 44t + 144`,
this is `64t² + 352t + 36L + PDB + 20Λ + 1306`. -/
theorem zRowBody_cost (t L Pd len : ℕ) :
    4 + (17 + 8 * decoderAllocEnd t + (12 * L + 32)) + (Pd + 24 * L + 40) + 17
      + (20 * len + 20) + 21 + 2 + 1
      = 64 * t * t + 352 * t + 36 * L + Pd + 20 * len + 1306 := by
  rw [decoderAllocEnd_eq]
  ring

/-- The same cost without the loop's trailing `jmp` (the loop rule adds the trailing jump and the
test itself): `64t² + 352t + 36L + PDB + 20Λ + 1305`. -/
theorem zRowBody_cost_iter (t L Pd len : ℕ) :
    4 + (17 + 8 * decoderAllocEnd t + (12 * L + 32)) + (Pd + 24 * L + 40) + 17
      + (20 * len + 20) + 21 + 2
      = 64 * t * t + 352 * t + 36 * L + Pd + 20 * len + 1305 := by
  rw [decoderAllocEnd_eq]
  ring

/-! ## 5. The row stage with a real `RowOut` post and no memory family -/

/-- The row-output content of a memory: every row `< d` has *some* bitmap packed at its slot. -/
def zRowsOut (E : RAMEnv) (R d : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ r < d, ∃ x : Fin R → ZMod 2, RowOut E R r x m

/-- The row invariant: all row payloads are intact, previous rows have their `RowOut`, and the
current-and-future row slots are still zero.  It mentions no memory family `M`; it is a predicate on
the machine's own memory at iteration `j`. -/
def zRowInv (E : RAMEnv) (R d t w : ℕ) (y : Fin d → Fin (t * w) → ZMod 2) (j : ℕ)
    (m : ℕ → ℕ) : Prop :=
  (∀ (r : ℕ) (hr : r < d) (i : ℕ) (hi : i < stageLen E), m (rowPayBase E r + i) = packMem (8 * w) (y ⟨r, hr⟩) i) ∧
  (∀ r < j, ∃ x : Fin R → ZMod 2, RowOut E R r x m) ∧
  (∀ r, j ≤ r → r < d → ∀ i < wordsOf E.W R, m (rowSlot E R r + i) = 0)

/-- **The row stage end to end, with the real body and a `RowOut` post.**  The only remaining
hypothesis is the per-iteration body step `hbody` (the composition of the real stages); the loop is
closed by `zRowLoop_inv_stageRun`, and the dispatch by `zDispatch_ColIn`.  No memory family appears. -/
theorem zRowStage_real {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {d K R t w ell : ℕ} {y : Fin d → Fin (t * w) → ZMod 2}
    (hW : 1 < 2 ^ E.W) (hell : ell < 2 ^ E.W)
    (hbody : ∀ j < d, ∀ s : RAMState, s.pc = zDRowBase Sinit →
      s.regs = zHeadsRegs j d → zRowInv E R d t w y j s.mem →
      ∃ (s' : RAMState) (k : ℕ), k ≤ K ∧
        (step (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E)^[k]
          { runBlock d65Cond.code E s with pc := zDRowBase Sinit + d65Cond.code.length + 1 } = s' ∧
        s'.pc = zDRowBase Sinit ∧ s'.regs = zHeadsRegs (j + 1) d ∧
        zRowInv E R d t w y (j + 1) s'.mem) :
    StageRun (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E
      (zDRowBase Sinit) (zDColHead Sinit Srow ell)
      ((d : ℝ) * ((K : ℝ) + 2) + 5)
      (fun s => s.regs = zHeadsRegs 0 d ∧ zRowInv E R d t w y 0 s.mem)
      (fun s => zRowsOut E R d s.mem ∧ ColIn ell s) := by
  intro s hpc hInv
  obtain ⟨k₁, s₁, hk₁, hstep₁, hpc₁, h1, h2, hinv₁⟩ :=
    zRowLoop_inv_stageRun (P := zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) (E := E)
      (a := zDRowBase Sinit) (b := .seq Srow (.code d65Inc)) (d := d) (K := K)
      (Inv := zRowInv E R d t w y) (s0 := s)
      (zAt_row_loopD Sinit Srow Sdec Sassem Sres Scr ell) hW hpc hInv.1 hInv.2 hbody
  have hpcCol : s₁.pc = zDColBase Sinit Srow := by
    rw [hpc₁]
    show zDRowBase Sinit + d65Cond.code.length + (Stmt.seq Srow (.code d65Inc)).len + 2
      = zDColBase Sinit Srow
    simp only [zDColBase, topLoop, Stmt.len]
    omega
  obtain ⟨-, k₂, s₂, hstep₂, hp₂, hk₂, hcol, hm₂⟩ :=
    zDispatch_ColIn (P := zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell)
      (pc := zDColBase Sinit Srow) (ell := ell) (s := s₁)
      (zAt_dispatch_codeD Sinit Srow Sdec Sassem Sres Scr ell) hpcCol hW hell
  refine ⟨k₁ + k₂, s₂, ?_, ?_, hp₂, ?_⟩
  · have hk₂' : (k₂ : ℝ) = 2 := by exact_mod_cast hk₂
    push_cast
    linarith
  · rw [Nat.add_comm, Function.iterate_add_apply, hstep₁, hstep₂]
  · refine ⟨?_, hcol⟩
    intro r hr
    obtain ⟨x, hx⟩ := hinv₁.2.1 r hr
    exact ⟨x, by rw [hm₂]; exact hx⟩

end RSD3
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.RSD3.zSave_run
#print axioms LinearSetReconciliation327.Main.RSD3.zRestore_run
#print axioms LinearSetReconciliation327.Main.RSD3.zD65Inc_pre
#print axioms LinearSetReconciliation327.Main.RSD3.zClearReloadStage_sem
#print axioms LinearSetReconciliation327.Main.RSD3.zRowLoop_inv_stageRun
#print axioms LinearSetReconciliation327.Main.RSD3.zRowBody_cost
#print axioms LinearSetReconciliation327.Main.RSD3.zRowBody_cost_iter
#print axioms LinearSetReconciliation327.Main.RSD3.zRowStage_real


