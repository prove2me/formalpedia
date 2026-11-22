-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_08
-- name    : LinearSetReconciliation327_Main_Bundle51_08
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T14:06:46.563858+00:00
-- url     : https://prove2.me/theorems/b40848c3-be65-462d-b6a1-6c3a7cbb3434
-- title:
--   LinearSetReconciliation327 — Bundle51_08
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_08` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintCRListCorrect20261120
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_07

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_08
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintDetCopy20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintStampBody20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintStamp20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNormalizeSetup20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNormalize20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintCRNode20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintEmitBody20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRootHeader20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintEmit20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintEmitFinish20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRootIO20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintStageBit20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintStage20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintUnpackBody20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintUnpack20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintUnpackAction20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintStageAction20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowRecord20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRunRow20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintWriteColumn20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintDetCopy20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDetCopyBody : List Instr :=
  [.add 3 5 0, .qDet 9 3, .add 3 4 0, .store 3 9, .add 0 0 15]

def hintDetCopyLoop : Stmt := .loop (.lt 2 0 6) (.code hintDetCopyBody)
def hintDetCopyStmt : Stmt := .seq (.code [.imm 0 0]) hintDetCopyLoop

structure HintDetCopyArgs (dest source count : ℕ) (state : RAMState) : Prop where
  destination : state.regs 4 = dest
  source_value : state.regs 5 = source
  length : state.regs 6 = count
  one : state.regs 15 = 1

structure HintDetCopyPre (E : RAMEnv) (dest source count : ℕ) : Prop where
  word : 1 < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  destination : dest + count ≤ 2 ^ E.W
  source_span : source + count ≤ 2 ^ E.W
  values : ∀ i < count, E.det (source + i) < 2 ^ E.W

structure HintDetCopyInv (E : RAMEnv) (dest source count index : ℕ)
    (initial : RAMState) (state : RAMState) : Prop where
  args : HintDetCopyArgs dest source count state
  position : state.regs 0 = index
  context : state.regs 14 = initial.regs 14
  data : ∀ i < index, state.mem (dest + i) = E.det (source + i)
  frame : CRMemFrame dest (dest + count) initial.mem state.mem

theorem hintDetCopyBody_spec (E : RAMEnv) (state initial : RAMState)
    (dest source count i : ℕ) (pre : HintDetCopyPre E dest source count)
    (inv : HintDetCopyInv E dest source count i initial state) (hi : i < count) :
    HintDetCopyInv E dest source count (i + 1) initial (runBlock hintDetCopyBody E state) := by
  classical
  have hd : dest + i < 2 ^ E.W := by have := pre.destination; omega
  have hs : source + i < 2 ^ E.W := by have := pre.source_span; omega
  have hn : i + 1 < 2 ^ E.W := by have := pre.count_fit; omega
  have hval := pre.values i hi
  have hMem : (runBlock hintDetCopyBody E state).mem =
      Function.update state.mem (dest + i) (E.det (source + i)) := by
    simp [hintDetCopyBody, runBlock, execInstr, inv.position, inv.args.source_value, inv.args.destination,
      Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hval]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa [hintDetCopyBody, runBlock, execInstr] using inv.args.destination
  · simpa [hintDetCopyBody, runBlock, execInstr] using inv.args.source_value
  · simpa [hintDetCopyBody, runBlock, execInstr] using inv.args.length
  · simpa [hintDetCopyBody, runBlock, execInstr] using inv.args.one
  · simp [hintDetCopyBody, runBlock, execInstr, inv.position, inv.args.one, Nat.mod_eq_of_lt hn]
  · simpa [hintDetCopyBody, runBlock, execInstr] using inv.context
  · intro j hj
    by_cases h : j = i
    · subst j; simp [hMem]
    · rw [hMem, Function.update_of_ne (by omega : dest + j ≠ dest + i)]
      exact inv.data j (by omega)
  · intro address hAway
    have hne : address ≠ dest + i := by rcases hAway with h | h <;> omega
    rw [hMem, Function.update_of_ne hne, inv.frame address hAway]

theorem hintDetCopyLoop_sem (P : Program) (E : RAMEnv) (state initial : RAMState)
    (dest source count base : ℕ) (pre : HintDetCopyPre E dest source count)
    (inv : HintDetCopyInv E dest source count 0 initial state)
    (hAt : At P base (hintDetCopyLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 8) state (fun k out => k ≤ 8 * count + 2 ∧
      HintDetCopyInv E dest source count count initial out) := by
  let I : ℕ → RAMState → Prop := fun left s => ∃ i, i + left = count ∧
    HintDetCopyInv E dest source count i initial s
  have hIpc : ∀ left s pc, I left s → I left {s with pc := pc} := by
    rintro left s pc ⟨i, hi, h⟩
    exact ⟨i, hi, ⟨⟨h.args.destination, h.args.source_value, h.args.length, h.args.one⟩,
      h.position, h.context, h.data, h.frame⟩⟩
  have hTest : ∀ left s, I left s → I left (runBlock (Cond.lt 2 0 6).code E s) := by
    rintro left s ⟨i, hi, h⟩
    refine ⟨i, hi, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, h.data, h.frame⟩⟩
    all_goals simp [Cond.code, runBlock, execInstr, h.args.destination, h.args.source_value,
      h.args.length, h.args.one, h.position, h.context]
  have hGo : ∀ left s, I (left + 1) s → (Cond.lt 2 0 6).eval s := by
    rintro left s ⟨i, hi, h⟩
    change s.regs 0 < s.regs 6
    rw [h.position, h.args.length]; omega
  have hStop : ∀ s, I 0 s → ¬ (Cond.lt 2 0 6).eval s := by
    rintro s ⟨i, hi, h⟩
    change ¬ s.regs 0 < s.regs 6
    rw [h.position, h.args.length]; omega
  have hBodyAt : At P (base + 2) hintDetCopyBody := (at_loop hAt).2.2.1
  have hBody : ∀ left s, I (left + 1) s → s.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintDetCopyBody).len) s
        (fun k out => k ≤ 5 ∧ I left out) := by
    rintro left s ⟨i, hi, h⟩ hStart
    have hp : s.pc = base + 2 := by exact hStart
    have hNative := Sem.block P E (base + 2) hintDetCopyBody s hBodyAt
      (by simp [hintDetCopyBody, NoBranch, Instr.NoBranchI]) hp
    apply Sem.mono hNative
    rintro k out ⟨hk, rfl⟩
    exact ⟨hk.le, i + 1, by omega, hintDetCopyBody_spec E s initial dest source count i pre h (by omega)⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintDetCopyBody) hAt pre.word I 5
    hIpc hTest hGo hStop hBody count state ⟨0, by omega, inv⟩ hPc
  apply Sem.mono hNative
  rintro k out ⟨hk, i, hi, h⟩
  have he : i = count := by omega
  exact ⟨hk, he ▸ h⟩

theorem hintDetCopyStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source count base : ℕ) (pre : HintDetCopyPre E dest source count)
    (args : HintDetCopyArgs dest source count state)
    (hAt : At P base (hintDetCopyStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 9) state (fun k out => k ≤ 8 * count + 3 ∧
      HintDetCopyInv E dest source count count state out) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  let mid := runBlock [.imm 0 0] E state
  have hRunI : (step P E)^[1] state = mid :=
    iterate_runBlock_of_at P E [.imm 0 0] state (by rwa [hPc])
      (by simp [NoBranch, Instr.NoBranchI])
  have hInv : HintDetCopyInv E dest source count 0 state mid := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, (by omega), fun _ _ => rfl⟩
    all_goals simp [mid, runBlock, execInstr, args.destination, args.source_value, args.length, args.one]
  have hPcI : mid.pc = base + 1 := by simp [mid, runBlock, execInstr, hPc]
  obtain ⟨_, k, out, hRun, hEnd, hk, h⟩ :=
    hintDetCopyLoop_sem P E mid state dest source count (base + 1) pre hInv hLoopAt hPcI
  exact ⟨hPc, k + 1, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega, h⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDetCopyStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintDetCopy20261120

section -- Def_LinearSetReconciliation327_Main_HintStampBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- Mark one list entry in a bitmap. Entries outside the coordinate range mark the
reserved cell immediately after the bitmap. -/
def hintStampBody : List Instr :=
  [.add 3 5 0, .load 9 3, .lt 10 9 7, .mul 9 9 10, .bxor 10 10 15,
    .mul 10 7 10, .add 9 9 10, .add 3 4 9, .store 3 15, .add 0 0 15]

structure HintStampArgs (dest source count N : ℕ) (s : RAMState) : Prop where
  destination : s.regs 4 = dest
  source_value : s.regs 5 = source
  length : s.regs 6 = count
  limit : s.regs 7 = N
  one : s.regs 15 = 1

theorem hintStampBody_spec (E : RAMEnv) (s : RAMState) (dest source count N j q : ℕ)
    (hWord : 1 < 2 ^ E.W) (hSrc : source + j < 2 ^ E.W) (hEnd : dest + N < 2 ^ E.W)
    (hNext : j + 1 < 2 ^ E.W)
    (args : HintStampArgs dest source count N s) (hIndex : s.regs 0 = j)
    (hRead : s.mem (source + j) % 2 ^ E.W = q) :
    let out := runBlock hintStampBody E s
    out.pc = s.pc + 10 ∧ out.regs 0 = j + 1 ∧ HintStampArgs dest source count N out ∧
      out.regs 14 = s.regs 14 ∧ out.mem = Function.update s.mem (dest + min q N) 1 := by
  have hUniverse : N < 2 ^ E.W := by omega
  have hQ : q < 2 ^ E.W := by
    rw [← hRead]
    exact Nat.mod_lt _ (by omega)
  by_cases h : q < N
  · have hDest : dest + q < 2 ^ E.W := by omega
    rw [Nat.min_eq_left h.le]
    refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp [hintStampBody, runBlock, execInstr, args.destination, args.source_value, args.length, args.limit,
        args.one, hIndex, hRead, h, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hSrc,
        Nat.mod_eq_of_lt hQ, Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hNext]
  · rw [Nat.min_eq_right (by omega)]
    refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp [hintStampBody, runBlock, execInstr, args.destination, args.source_value, args.length, args.limit,
        args.one, hIndex, hRead, h, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hSrc,
        Nat.mod_eq_of_lt hUniverse, Nat.mod_eq_of_lt hEnd, Nat.mod_eq_of_lt hNext]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStampBody_spec
end -- Def_LinearSetReconciliation327_Main_HintStampBody20261120

section -- Def_LinearSetReconciliation327_Main_HintStamp20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintStampLoop : Stmt := .loop (.lt 2 0 6) (.code hintStampBody)
def hintStampStmt : Stmt := .seq (.code [.imm 0 0]) hintStampLoop

noncomputable def hintStampValue (E : RAMEnv) (source index : ℕ) (memory : ℕ → ℕ) (q : ℕ) : ℕ :=
  hintTruth (∃ i < index, memory (source + i) % 2 ^ E.W = q)

structure HintStampPre (E : RAMEnv) (dest source count N : ℕ) : Prop where
  word : 1 < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  destination : dest + N < 2 ^ E.W
  source_span : source + count ≤ 2 ^ E.W
  separate : source + count ≤ dest ∨ dest + N < source

structure HintStampInv (E : RAMEnv) (dest source count N index : ℕ)
    (initial : RAMState) (state : RAMState) : Prop where
  args : HintStampArgs dest source count N state
  position : state.regs 0 = index
  context : state.regs 14 = initial.regs 14
  data : ∀ q < N, state.mem (dest + q) = hintStampValue E source index initial.mem q
  frame : CRMemFrame dest (dest + N + 1) initial.mem state.mem

theorem hintStampInv_step (E : RAMEnv) (state initial : RAMState)
    (dest source count N i : ℕ) (pre : HintStampPre E dest source count N)
    (inv : HintStampInv E dest source count N i initial state) (hi : i < count) :
    HintStampInv E dest source count N (i + 1) initial (runBlock hintStampBody E state) := by
  classical
  let coord := initial.mem (source + i) % 2 ^ E.W
  have hs : source + i < 2 ^ E.W := by have := pre.source_span; omega
  have hn : i + 1 < 2 ^ E.W := by have := pre.count_fit; omega
  have hCoord : state.mem (source + i) % 2 ^ E.W = coord := by
    unfold coord
    rw [inv.frame]
    rcases pre.separate with h | h <;> omega
  obtain ⟨_, hIter, hArgs, hCtx, hMem⟩ := hintStampBody_spec E state dest source count N i coord
    pre.word hs pre.destination hn inv.args inv.position hCoord
  have hMinLe : min coord N ≤ N := min_le_right _ _
  refine ⟨hArgs, hIter, hCtx.trans inv.context, ?_, ?_⟩
  · intro q hq
    have hStep : hintStampValue E source (i + 1) initial.mem q =
        if q = coord then 1 else hintStampValue E source i initial.mem q := by
      unfold hintStampValue
      by_cases he : q = coord
      · subst q
        have hw : ∃ j < i + 1, initial.mem (source + j) % 2 ^ E.W = coord := ⟨i, by omega, rfl⟩
        simp only [hintTruth, if_pos hw, if_true]
      · rw [if_neg he]
        apply hintTruth_congr
        constructor
        · rintro ⟨j, hj, hv⟩
          have hne : j ≠ i := by intro h; subst j; exact he hv.symm
          exact ⟨j, by omega, hv⟩
        · rintro ⟨j, hj, hv⟩
          exact ⟨j, by omega, hv⟩
    rw [hStep, hMem]
    by_cases he : q = coord
    · subst q
      simp [Nat.min_eq_left hq.le]
    · have hh : dest + q ≠ dest + min coord N := by
        by_cases h : coord ≤ N
        · rw [Nat.min_eq_left h]; omega
        · rw [Nat.min_eq_right (by omega)]; omega
      rw [Function.update_of_ne hh, if_neg he, inv.data q hq]
  · intro address hAway
    have hne : address ≠ dest + min coord N := by rcases hAway with h | h <;> omega
    rw [hMem, Function.update_of_ne hne, inv.frame address hAway]

theorem hintStampLoop_sem (P : Program) (E : RAMEnv) (state initial : RAMState)
    (dest source count N base : ℕ) (pre : HintStampPre E dest source count N)
    (inv : HintStampInv E dest source count N 0 initial state)
    (hAt : At P base (hintStampLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 13) state (fun k out => k ≤ 13 * count + 2 ∧
      HintStampInv E dest source count N count initial out) := by
  let I : ℕ → RAMState → Prop := fun left s => ∃ i, i + left = count ∧
    HintStampInv E dest source count N i initial s
  have hIpc : ∀ left s pc, I left s → I left {s with pc := pc} := by
    rintro left s pc ⟨i, hi, h⟩
    exact ⟨i, hi, ⟨⟨h.args.destination, h.args.source_value, h.args.length, h.args.limit, h.args.one⟩,
      h.position, h.context, h.data, h.frame⟩⟩
  have hTest : ∀ left s, I left s → I left (runBlock (Cond.lt 2 0 6).code E s) := by
    rintro left s ⟨i, hi, h⟩
    refine ⟨i, hi, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, h.data, h.frame⟩⟩
    all_goals simp [Cond.code, runBlock, execInstr, h.args.destination, h.args.source_value,
      h.args.length, h.args.limit, h.args.one, h.position, h.context]
  have hGo : ∀ left s, I (left + 1) s → (Cond.lt 2 0 6).eval s := by
    rintro left s ⟨i, hi, h⟩
    change s.regs 0 < s.regs 6
    rw [h.position, h.args.length]; omega
  have hStop : ∀ s, I 0 s → ¬ (Cond.lt 2 0 6).eval s := by
    rintro s ⟨i, hi, h⟩
    change ¬ s.regs 0 < s.regs 6
    rw [h.position, h.args.length]; omega
  have hBodyAt : At P (base + 2) hintStampBody := (at_loop hAt).2.2.1
  have hBody : ∀ left s, I (left + 1) s → s.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintStampBody).len) s
        (fun k out => k ≤ 10 ∧ I left out) := by
    rintro left s ⟨i, hi, h⟩ hStart
    have hp : s.pc = base + 2 := by exact hStart
    have hNative := Sem.block P E (base + 2) hintStampBody s hBodyAt
      (by simp [hintStampBody, NoBranch, Instr.NoBranchI]) hp
    apply Sem.mono hNative
    rintro k out ⟨hk, rfl⟩
    exact ⟨hk.le, i + 1, by omega, hintStampInv_step E s initial dest source count N i pre h (by omega)⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintStampBody) hAt pre.word I 10
    hIpc hTest hGo hStop hBody count state ⟨0, by omega, inv⟩ hPc
  apply Sem.mono hNative
  rintro k out ⟨hk, i, hi, h⟩
  have he : i = count := by omega
  exact ⟨hk, he ▸ h⟩

theorem hintStampStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source count N base : ℕ) (pre : HintStampPre E dest source count N)
    (args : HintStampArgs dest source count N state)
    (hClear : ∀ q < N, state.mem (dest + q) = 0)
    (hAt : At P base (hintStampStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 14) state (fun k out => k ≤ 13 * count + 3 ∧
      HintStampInv E dest source count N count state out) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  let mid := runBlock [.imm 0 0] E state
  have hRunI : (step P E)^[1] state = mid :=
    iterate_runBlock_of_at P E [.imm 0 0] state (by rwa [hPc])
      (by simp [NoBranch, Instr.NoBranchI])
  have hInv : HintStampInv E dest source count N 0 state mid := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, fun _ _ => rfl⟩
    all_goals simp [mid, runBlock, execInstr, args.destination, args.source_value, args.length, args.limit, args.one]
    intro q hq
    simpa [hintStampValue, hintTruth, mid, runBlock, execInstr] using hClear q hq
  have hPcI : mid.pc = base + 1 := by simp [mid, runBlock, execInstr, hPc]
  obtain ⟨_, k, out, hRun, hEnd, hk, h⟩ :=
    hintStampLoop_sem P E mid state dest source count N (base + 1) pre hInv hLoopAt hPcI
  exact ⟨hPc, k + 1, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega, h⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStampStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintStamp20261120

section -- Def_LinearSetReconciliation327_Main_HintNormalizeSetup20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintNormalizeTable (E : RAMEnv) (metaBase dest count control : ℕ) : Prop where
  word : 11 < 2 ^ E.W
  span : metaBase + 11 < 2 ^ E.W
  dest_address : E.det (metaBase + 9) = dest
  count_value : E.det (metaBase + 10) = count
  control_address : E.det (metaBase + 11) = control
  dest_span : dest + count < 2 ^ E.W
  control_fit : control < 2 ^ E.W

def hintNormalizeSetup : List Instr :=
  [.imm 13 0, .add 5 0 13, .imm 15 1, .imm 3 9, .add 3 6 3, .qDet 4 3,
    .add 3 3 15, .qDet 6 3, .add 3 3 15, .qDet 14 3, .imm 7 1, .imm 8 0]

def hintNormalizeClamp : List Instr :=
  [.add 7 6 8, .lt 10 1 7, .mul 6 1 10, .bxor 10 10 15, .mul 10 7 10, .add 6 6 10]

theorem hintNormalizeSetup_spec (E : RAMEnv) (state : RAMState) (metaBase dest count control : ℕ)
    (layout : HintNormalizeTable E metaBase dest count control) (hMeta : state.regs 6 = metaBase)
    (hSourceFit : state.regs 0 < 2 ^ E.W) :
    let out := runBlock hintNormalizeSetup E state
    out.pc = state.pc + 12 ∧
      out.regs 5 = state.regs 0 ∧ out.regs 1 = state.regs 1 ∧ out.regs 14 = control ∧
      out.mem = state.mem ∧ HintFillParams dest 1 count 0 out := by
  have hs := layout.span
  have hWord := layout.word
  have hDest := layout.dest_span
  have hOne : 1 < 2 ^ E.W := by omega
  have h9 : 9 < 2 ^ E.W := by omega
  have hMeta9 : metaBase + 9 < 2 ^ E.W := by omega
  have hMeta10 : metaBase + 9 + 1 < 2 ^ E.W := by omega
  have hMeta11 : metaBase + 9 + 1 + 1 < 2 ^ E.W := by omega
  have hD : dest < 2 ^ E.W := by omega
  have hN : count < 2 ^ E.W := by omega
  refine ⟨?_, ?_, ?_, ?_, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintNormalizeSetup, runBlock, execInstr, hMeta, layout.dest_address, layout.count_value,
      layout.control_address, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt h9, Nat.mod_eq_of_lt hMeta9,
      Nat.mod_eq_of_lt hMeta10, Nat.mod_eq_of_lt hMeta11, Nat.mod_eq_of_lt hD, Nat.mod_eq_of_lt hN,
      Nat.mod_eq_of_lt layout.control_fit, Nat.mod_eq_of_lt hSourceFit]

theorem hintNormalizeClamp_spec (E : RAMEnv) (state : RAMState) (dest source count raw : ℕ)
    (hWord : 1 < 2 ^ E.W) (hN : count < 2 ^ E.W) (hSource : state.regs 5 = source)
    (hRaw : state.regs 1 = raw) (hFill : HintFillParams dest 1 count 0 state) :
    let out := runBlock hintNormalizeClamp E state
    out.pc = state.pc + 6 ∧ out.mem = state.mem ∧ out.regs 14 = state.regs 14 ∧
      HintStampArgs dest source (min raw count) count out := by
  have hZero : state.regs 8 = 0 := hFill.fill_value
  by_cases h : raw < count
  · have hr : raw < 2 ^ E.W := by omega
    rw [Nat.min_eq_left h.le]
    refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      simp [hintNormalizeClamp, runBlock, execInstr, hSource, hRaw, hFill.dest_value, hFill.count_value,
        hFill.one_value, hZero, h, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hr]
  · rw [Nat.min_eq_right (by omega)]
    refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      simp [hintNormalizeClamp, runBlock, execInstr, hSource, hRaw, hFill.dest_value, hFill.count_value,
        hFill.one_value, hZero, h, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hN]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNormalizeSetup_spec
#print axioms LinearSetReconciliation327.Main.hintNormalizeClamp_spec
end -- Def_LinearSetReconciliation327_Main_HintNormalizeSetup20261120

section -- Def_LinearSetReconciliation327_Main_HintNormalize20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintNormalizeStmt : Stmt := .seq (.code hintNormalizeSetup)
  (.seq hintFillStmt (.seq (.code hintNormalizeClamp) hintStampStmt))

/-- Convert a possibly malformed output list into an in-range bitmap in bounded
time. The list is clipped to the universe size before the scan. -/
theorem hintNormalizeStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (metaBase dest N control base : ℕ) (layout : HintNormalizeTable E metaBase dest N control)
    (hMeta : state.regs 6 = metaBase) (hSource : state.regs 0 < 2 ^ E.W)
    (hSpan : state.regs 0 + min (state.regs 1) N ≤ 2 ^ E.W)
    (hSeparate : state.regs 0 + min (state.regs 1) N ≤ dest ∨ dest + N < state.regs 0)
    (hAt : At P base (hintNormalizeStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 40) state (fun k out => k ≤ 20 * N + 24 ∧
      out.regs 14 = control ∧
      (∀ q < N, out.mem (dest + q) = hintStampValue E (state.regs 0) (min (state.regs 1) N) state.mem q) ∧
      CRMemFrame dest (dest + N + 1) state.mem out.mem) := by
  let source := state.regs 0
  let raw := state.regs 1
  have hD := layout.dest_span
  have hN : N < 2 ^ E.W := by omega
  have hWord : 1 < 2 ^ E.W := by have := layout.word; omega
  obtain ⟨hSetupAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintNormalizeSetup at hSetupAt
  change At P (base + 12) ((Stmt.seq hintFillStmt
    (.seq (.code hintNormalizeClamp) hintStampStmt)).compile (base + 12)) at hRestAt
  obtain ⟨hClearAt, hClampStampAt⟩ := At.seqStmt hRestAt
  change At P (base + 12) (hintFillStmt.compile (base + 12)) at hClearAt
  change At P (base + 20) ((Stmt.seq (.code hintNormalizeClamp) hintStampStmt).compile (base + 20)) at hClampStampAt
  obtain ⟨hClampAt, hStampAt⟩ := At.seqStmt hClampStampAt
  change At P (base + 20) hintNormalizeClamp at hClampAt
  change At P (base + 26) (hintStampStmt.compile (base + 26)) at hStampAt
  have hSetup := hintNormalizeSetup_spec E state metaBase dest N control layout hMeta hSource
  generalize hSetupEq : runBlock hintNormalizeSetup E state = setup at hSetup
  obtain ⟨hSetupPc, hSetupSrc, hSetupRaw, hSetupCtx, hSetupMem, hFill⟩ := hSetup
  have hRunSetup : (step P E)^[12] state = setup := by
    have hh := iterate_runBlock_of_at P E hintNormalizeSetup state (by rwa [hPc])
      (by simp [hintNormalizeSetup, NoBranch, Instr.NoBranchI])
    rw [hSetupEq] at hh
    exact hh
  obtain ⟨_, kc, cleared, hRunClear, hClearPc, hClearCost, _, hClearMem, hFillClear, hClearFrame, hClearRegs⟩ :=
    hintFillStmt_sem P E setup dest 1 N (base + 12) 0 hWord hN (by intro j hj; simp; omega) hClearAt
      (by omega) hFill
  have hClamp := hintNormalizeClamp_spec E cleared dest source N raw hWord hN
    ((hClearRegs 5 (by decide) (by decide) (by decide)).trans hSetupSrc)
    ((hClearRegs 1 (by decide) (by decide) (by decide)).trans hSetupRaw) hFillClear
  generalize hClampEq : runBlock hintNormalizeClamp E cleared = clamped at hClamp
  obtain ⟨hClampPc, hClampMem, hClampCtx, hClampArgs⟩ := hClamp
  have hRunClamp : (step P E)^[6] cleared = clamped := by
    have hh := iterate_runBlock_of_at P E hintNormalizeClamp cleared (by rwa [hClearPc])
      (by simp [hintNormalizeClamp, NoBranch, Instr.NoBranchI])
    rw [hClampEq] at hh
    exact hh
  have hClear (q : ℕ) (hq : q < N) : clamped.mem (dest + q) = 0 := by
    rw [hClampMem, hClearMem]
    have hIn : dest + q ∈ hintFillPositions dest 1 N := Finset.mem_image.mpr
      ⟨q, Finset.mem_range.mpr hq, by simp⟩
    simp [hintFillMem, hIn]
  have hSeparate' : source + min raw N ≤ dest ∨ dest + N < source := hSeparate
  have hClampFrame : CRMemFrame dest (dest + N) state.mem clamped.mem := by
    intro addr hAway
    rw [hClampMem, hClearFrame, hSetupMem]
    intro hIn
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hIn
    have hq' := Finset.mem_range.mp hq
    simp at he
    rcases hAway with h | h <;> omega
  have hPre : HintStampPre E dest source (min raw N) N :=
    ⟨hWord, (min_le_right _ _).trans_lt hN, hD, hSpan, hSeparate'⟩
  obtain ⟨_, ks, out, hRunStamp, hEnd, hCost, hFinal⟩ :=
    hintStampStmt_sem P E clamped dest source (min raw N) N (base + 26) hPre hClampArgs hClear hStampAt
      (by omega)
  have hMin := min_le_right raw N
  refine ⟨hPc, ks + (6 + (kc + 12)), out,
    hintIterate_then (step P E) (hintIterate_then (step P E)
      (hintIterate_then (step P E) hRunSetup hRunClear) hRunClamp) hRunStamp,
    by omega, by omega, hFinal.context.trans (hClampCtx.trans
      ((hClearRegs 14 (by decide) (by decide) (by decide)).trans hSetupCtx)), ?_, ?_⟩
  · intro q hq
    rw [hFinal.data q hq]
    apply hintTruth_congr
    have hRead (i : ℕ) (hi : i < min raw N) :
        clamped.mem (source + i) = state.mem (source + i) :=
      hClampFrame _ (by rcases hSeparate' with h | h <;> omega)
    constructor
    · rintro ⟨i, hi, hv⟩
      exact ⟨i, hi, by rwa [hRead i hi] at hv⟩
    · rintro ⟨i, hi, hv⟩
      exact ⟨i, hi, by rwa [hRead i hi]⟩
  · intro addr hAway
    exact (hFinal.frame addr hAway).trans (hClampFrame addr (by rcases hAway with h | h <;> omega))

theorem hintNormalize_support {N : ℕ} (E : RAMEnv) (state : RAMState) (x : Fin N → ZMod 2)
    (hWidth : N < 2 ^ E.W) (hOut : OutputsSupport state x) (i : Fin N) :
    hintStampValue E (state.regs 0) (min (state.regs 1) N) state.mem i.val = (x i).val := by
  classical
  have hSub : (outList state).toFinset ⊆ Finset.range N := by
    intro v hv
    obtain ⟨j, rfl, _⟩ := (hOut.2 v).mp (List.mem_toFinset.mp hv)
    exact Finset.mem_range.mpr j.isLt
  have hCount : state.regs 1 ≤ N := by
    have hc := Finset.card_le_card hSub
    rw [List.toFinset_card_of_nodup hOut.1, Finset.card_range] at hc
    simpa only [outList, List.length_map, List.length_range] using hc
  rw [Nat.min_eq_left hCount]
  have hc i (hi : i < state.regs 1) : state.mem (state.regs 0 + i) < 2 ^ E.W := by
    have hx : state.mem (state.regs 0 + i) ∈ outList state :=
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    exact (Finset.mem_range.mp (hSub (List.mem_toFinset.mpr hx))).trans hWidth
  have hMem : (∃ j < state.regs 1, state.mem (state.regs 0 + j) % 2 ^ E.W = i.val) ↔
      i.val ∈ outList state := by
    constructor
    · rintro ⟨j, hj, hq⟩
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, by simpa only [Nat.mod_eq_of_lt (hc j hj)] using hq⟩
    · rintro hj
      obtain ⟨j, hj, hq⟩ := List.mem_map.mp hj
      have hj' := List.mem_range.mp hj
      exact ⟨j, hj', by simpa only [Nat.mod_eq_of_lt (hc j hj')] using hq⟩
  have hEq : i.val ∈ outList state ↔ x i = 1 := by
    rw [hOut.2]
    constructor
    · rintro ⟨j, hj, h⟩
      rw [← Fin.ext hj]
      exact h
    · exact fun h => ⟨i, rfl, h⟩
  unfold hintStampValue
  rw [hintTruth_congr (hMem.trans hEq)]
  have hBinary : ∀ bit : ZMod 2, bit = 0 ∨ bit = 1 := by decide
  rcases hBinary (x i) with hZero | hOne
  · simp [hintTruth, hZero]
  · rw [hOne, hintTruth, if_pos rfl]
    decide

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNormalizeStmt_sem
#print axioms LinearSetReconciliation327.Main.hintNormalize_support
end -- Def_LinearSetReconciliation327_Main_HintNormalize20261120

section -- Def_LinearSetReconciliation327_Main_HintCRNode20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintCRNodeArea where
  offset : ℕ
  registers : ℕ
  memory : ℕ
  table : ℕ
  log : ℕ
  descriptor : ℕ
  destination : ℕ
  control : ℕ

structure HintCRNodePre (S : CRSourceBundle) (E : RAMEnv) (N t : ℕ) (A : HintCRNodeArea) : Prop where
  universe_pos : 1 ≤ N
  sparse_bound : t ≤ N
  spill : CRSimLayout E (S.data N t).W A.registers A.memory A.table A.log
    (crSourceSteps S N t) (S.data N t).det
  call_header : CRCallHeader E A.descriptor (S.data N t).W (S.data N t).R A.offset A.registers
    A.memory A.table A.log (crSourceSteps S N t)
  normalization : HintNormalizeTable E A.descriptor A.destination N A.control
  output_before : A.destination + N < A.registers
  input_span : A.offset + (S.data N t).R < 2 ^ E.W
  input_before : (A.offset + (S.data N t).R) / E.W < A.memory

noncomputable def hintCRNodeBudget (S : CRSourceBundle) (N t : ℕ) : ℕ :=
  17 * (S.data N t).R + 16 * crSourceSteps S N t + 20 * N + 148

def HintCRNodeFrame (S : CRSourceBundle) (A : HintCRNodeArea) (N t : ℕ)
    (initial final : ℕ → ℕ) : Prop :=
  ∀ addr, (addr < A.destination ∨ A.destination + N < addr) →
    (addr < A.registers ∨ A.log + crSourceSteps S N t + 1 ≤ addr) → final addr = initial addr

theorem hintCRNodeCompose_sem (S : CRSourceBundle) (P : Program) (E : RAMEnv) (state : RAMState)
    (A : HintCRNodeArea) (N t entry endPc : ℕ) (Raw : RAMState → Prop)
    (Goal : (ℕ → ℕ) → Prop) (pre : HintCRNodePre S E N t A)
    (hPc : state.pc = entry)
    (hCore : Sem P E entry (entry + (crSourceInputCode S entry).length) state (fun k out =>
      k ≤ 17 * (S.data N t).R + 16 * crSourceSteps S N t + 124 ∧
      HintCRListSpan (S.data N t).W A.memory out ∧ out.regs 1 ≤ 2 ^ (S.data N t).W ∧
      out.regs 6 = A.descriptor ∧ CRMemFrame A.registers (A.log + crSourceSteps S N t + 1) state.mem out.mem ∧ Raw out))
    (hNormalize : At P (entry + (crSourceInputCode S entry).length)
      (hintNormalizeStmt.compile (entry + (crSourceInputCode S entry).length)))
    (hEnd : endPc = entry + (crSourceInputCode S entry).length + 40)
    (hGoal : ∀ raw out : RAMState, Raw raw →
      (∀ q < N, out.mem (A.destination + q) =
        hintStampValue E (raw.regs 0) (min (raw.regs 1) N) raw.mem q) → Goal out.mem) :
    Sem P E entry endPc state (fun k out => k ≤ hintCRNodeBudget S N t ∧
      out.regs 14 = A.control ∧ HintCRNodeFrame S A N t state.mem out.mem ∧ Goal out.mem) := by
  obtain ⟨_, kc, raw, hRun, hCorePc, hCost, hShape, hMax, hMeta, hFrame, hRaw⟩ := hCore
  have hFile := pre.spill.file_before
  have hLog := pre.spill.mem_before_log
  have hTop := pre.spill.log_word
  have hBefore := pre.output_before
  have hPow : 2 ^ ((S.data N t).W + 1) = 2 ^ (S.data N t).W + 2 ^ (S.data N t).W := by
    rw [pow_succ]
    omega
  rw [hPow] at hLog
  have hMin : min (raw.regs 1) N ≤ raw.regs 1 := min_le_left _ _
  have hBound : raw.regs 0 < 2 ^ E.W ∧ raw.regs 0 + min (raw.regs 1) N ≤ 2 ^ E.W ∧
      (raw.regs 0 + min (raw.regs 1) N ≤ A.destination ∨ A.destination + N < raw.regs 0) := by
    rcases hShape with ⟨hZero, hEmpty⟩ | ⟨hMemory, hMemoryEnd⟩
    · rw [hZero, hEmpty]
      simp
    · exact ⟨by omega, by omega, Or.inr (by omega)⟩
  obtain ⟨_, kn, out, hRunN, hPcN, hCostN, hCtx, hBitmap, hFrameN⟩ :=
    hintNormalizeStmt_sem P E raw A.descriptor A.destination N A.control
      (entry + (crSourceInputCode S entry).length) pre.normalization hMeta hBound.1 hBound.2.1
      hBound.2.2 hNormalize hCorePc
  refine ⟨hPc, kn + kc, out, hintIterate_then (step P E) hRun hRunN, hPcN.trans hEnd.symm,
    ?_, hCtx, ?_, hGoal raw out hRaw hBitmap⟩
  · unfold hintCRNodeBudget
    omega
  · intro address hOutside hOutsideCR
    exact (hFrameN address (by rcases hOutside with h | h <;> omega)).trans (hFrame address hOutsideCR)

theorem hintCRNode_total (S : CRSourceBundle) (P : Program) (E : RAMEnv) (state : RAMState)
    (A : HintCRNodeArea) (N t entry switchBase : ℕ) (other : List Stmt) (act : Stmt)
    (pre : HintCRNodePre S E N t A)
    (hPc : state.pc = entry) (hMeta : state.regs 6 = A.descriptor)
    (hFresh : ∀ addr, addr ≤ 2 ^ ((S.data N t).W + 1) → state.mem (A.memory + addr) = 0)
    (hSelect : (hintActionsWithCR S switchBase other hintNormalizeStmt)[other.length]? = some act)
    (hEntry : entry = hintActionEntry (hintActionsWithCR S switchBase other hintNormalizeStmt) switchBase other.length)
    (hAt : At P entry (act.compile entry)) :
    Sem P E entry (entry + act.len) state (fun k out => k ≤ hintCRNodeBudget S N t ∧
      out.regs 14 = A.control ∧ HintCRNodeFrame S A N t state.mem out.mem ∧
      (∀ q < N, out.mem (A.destination + q) = 0 ∨ out.mem (A.destination + q) = 1)) := by
  obtain ⟨hEnd, hCore, hFinish⟩ := hintCRAction_parts S P switchBase other hintNormalizeStmt act entry
    hSelect hEntry hAt
  let y : Fin (S.data N t).R → ZMod 2 := fun i =>
    if bitAt state.mem E.W 0 (A.offset + i.val) = 1 then 1 else 0
  have hInput (i : Fin (S.data N t).R) :
      bitAt state.mem E.W 0 (A.offset + i.val) = if y i = 1 then 1 else 0 := by
    have hb : bitAt state.mem E.W 0 (A.offset + i.val) < 2 := by
      unfold bitAt
      exact Nat.mod_lt _ (by decide)
    by_cases h : bitAt state.mem E.W 0 (A.offset + i.val) = 1
    · simp [y, h]
    · have hz : bitAt state.mem E.W 0 (A.offset + i.val) = 0 := by omega
      simp [y, hz]
  have hCoreRun := hintCRCodeList_total S P E N t A.offset A.registers A.memory A.table A.log A.descriptor
    entry state y pre.universe_pos pre.sparse_bound pre.spill hMeta (by have := pre.normalization.span; omega)
    pre.call_header pre.input_span pre.input_before hInput hFresh hCore hPc
  apply hintCRNodeCompose_sem S P E state A N t entry (entry + act.len) (fun _ => True)
    (fun mem => ∀ q < N, mem (A.destination + q) = 0 ∨ mem (A.destination + q) = 1) pre hPc
    (Sem.mono hCoreRun (by
      rintro k out ⟨hk, hs, hn, h6, hf⟩
      exact ⟨hk, hs, hn, h6.trans hMeta, hf, trivial⟩)) hFinish
  · rw [hEnd]
    change entry + ((crSourceInputCode S entry).length + 40) = _
    omega
  · intro raw out _ hBitmap q hq
    rw [hBitmap q hq]
    unfold hintStampValue hintTruth
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem hintCRNode_correct (S : CRSourceBundle) (P : Program) (E : RAMEnv) (state : RAMState)
    (A : HintCRNodeArea) (N t entry switchBase : ℕ) (other : List Stmt) (act : Stmt)
    (x : Fin N → ZMod 2) (pre : HintCRNodePre S E N t A)
    (hSupport : (Finset.univ.filter fun i => x i = 1).card ≤ t)
    (hPc : state.pc = entry) (hMeta : state.regs 6 = A.descriptor)
    (hInput : ∀ i : Fin (S.data N t).R, bitAt state.mem E.W 0 (A.offset + i.val) =
      if (S.data N t).H x i = 1 then 1 else 0)
    (hFresh : ∀ addr, addr ≤ 2 ^ ((S.data N t).W + 1) → state.mem (A.memory + addr) = 0)
    (hSelect : (hintActionsWithCR S switchBase other hintNormalizeStmt)[other.length]? = some act)
    (hEntry : entry = hintActionEntry (hintActionsWithCR S switchBase other hintNormalizeStmt) switchBase other.length)
    (hAt : At P entry (act.compile entry)) :
    Sem P E entry (entry + act.len) state (fun k out => k ≤ hintCRNodeBudget S N t ∧
      out.regs 14 = A.control ∧ HintCRNodeFrame S A N t state.mem out.mem ∧
      (∀ i : Fin N, out.mem (A.destination + i.val) = (x i).val)) := by
  obtain ⟨hEnd, hCore, hFinish⟩ := hintCRAction_parts S P switchBase other hintNormalizeStmt act entry
    hSelect hEntry hAt
  have hCoreRun := hintCRCodeList_correct S P E N t A.offset A.registers A.memory A.table A.log A.descriptor
    entry state x pre.universe_pos pre.sparse_bound hSupport pre.spill hMeta
    (by have := pre.normalization.span; omega) pre.call_header pre.input_span pre.input_before hInput hFresh hCore hPc
  apply hintCRNodeCompose_sem S P E state A N t entry (entry + act.len) (fun raw => OutputsSupport raw x)
    (fun mem => ∀ i : Fin N, mem (A.destination + i.val) = (x i).val) pre hPc
    (Sem.mono hCoreRun (by
      rintro k out ⟨hk, hs, hn, hout, h6, hf⟩
      exact ⟨hk, hs, hn, h6.trans hMeta, hf, hout⟩)) hFinish
  · rw [hEnd]
    change entry + ((crSourceInputCode S entry).length + 40) = _
    omega
  · intro raw out hOut hBitmap i
    rw [hBitmap i.val i.isLt]
    exact hintNormalize_support E raw x (by have := pre.normalization.dest_span; omega) hOut i

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCRNode_total
#print axioms LinearSetReconciliation327.Main.hintCRNode_correct
end -- Def_LinearSetReconciliation327_Main_HintCRNode20261120

section -- Def_LinearSetReconciliation327_Main_HintEmitBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintEmitBody : List Instr :=
  [.add 3 5 0, .load 9 3, .add 3 4 1, .store 3 0, .add 1 1 9, .add 0 0 15]

structure HintEmitArgs (dest source count : ℕ) (s : RAMState) : Prop where
  destination : s.regs 4 = dest
  source_value : s.regs 5 = source
  length : s.regs 6 = count
  one : s.regs 15 = 1

theorem hintEmitBody_spec (E : RAMEnv) (s : RAMState) (dest source count q used flag : ℕ)
    (args : HintEmitArgs dest source count s) (hQ : s.regs 0 = q) (hUsed : s.regs 1 = used)
    (hSource : source + q < 2 ^ E.W) (hDest : dest + used < 2 ^ E.W)
    (hRead : s.mem (source + q) = flag) (hFlag : flag < 2 ^ E.W)
    (hNext : q + 1 < 2 ^ E.W) (hUsedNext : used + flag < 2 ^ E.W) :
    let out := runBlock hintEmitBody E s
    out.pc = s.pc + 6 ∧ out.mem = Function.update s.mem (dest + used) q ∧
      out.regs 0 = q + 1 ∧ out.regs 1 = used + flag ∧ HintEmitArgs dest source count out ∧
      out.regs 14 = s.regs 14 := by
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [hintEmitBody, runBlock, execInstr, args.destination, args.source_value, args.length, args.one,
      hQ, hUsed, hRead, Nat.mod_eq_of_lt hSource, Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hFlag,
      Nat.mod_eq_of_lt hNext, Nat.mod_eq_of_lt hUsedNext]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintEmitBody_spec
end -- Def_LinearSetReconciliation327_Main_HintEmitBody20261120

section -- Def_LinearSetReconciliation327_Main_HintRootHeader20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- Decoder metadata within the existing sixteen-word header located by det[3].
The updater's own table slots retain their original interpretation. -/
structure HintRootHeader (E : RAMEnv) (header control hintMap resultMap listBase table count N : ℕ) : Prop where
  word : 15 < 2 ^ E.W
  span : header + 15 < 2 ^ E.W
  anchor : E.det 3 = header
  control_span : control + 2 < 2 ^ E.W
  normalize : HintNormalizeTable E header hintMap N control
  dispatch_table : E.det (header + 12) = table
  dispatch_count : E.det (header + 13) = count
  result_address : E.det (header + 14) = resultMap
  list_address : E.det (header + 15) = listBase
  table_fit : table < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  result_fit : resultMap < 2 ^ E.W
  list_fit : listBase < 2 ^ E.W

def hintRootHintArgs : List Instr :=
  [.imm 3 3, .qDet 6 3, .imm 3 0, .add 0 1 3, .add 1 2 3]

def hintRootControlInit : List Instr :=
  [.imm 3 3, .qDet 6 3, .imm 3 12, .add 3 6 3, .qDet 9 3, .store 14 9,
    .imm 15 1, .add 3 3 15, .qDet 9 3, .add 3 14 15, .store 3 9]

def hintRootEmitArgs : List Instr :=
  [.imm 3 3, .qDet 7 3, .imm 15 1, .imm 3 15, .add 3 7 3, .qDet 4 3,
    .imm 3 14, .add 3 7 3, .qDet 5 3, .imm 3 10, .add 3 7 3, .qDet 6 3]

theorem hintRootHintArgs_spec (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeader E header control hintMap resultMap listBase table count N)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W) :
    let out := runBlock hintRootHintArgs E state
    out.pc = state.pc + 5 ∧ out.mem = state.mem ∧
      out.regs 6 = header ∧ out.regs 0 = state.regs 1 ∧ out.regs 1 = state.regs 2 := by
  have hWord := hdr.word
  have hSpan := hdr.span
  have h3 : 3 < 2 ^ E.W := by omega
  have hHdr : header < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_, ?_⟩ <;>
    simp [hintRootHintArgs, runBlock, execInstr, hdr.anchor, Nat.mod_eq_of_lt h3,
      Nat.mod_eq_of_lt hHdr, Nat.mod_eq_of_lt hSource, Nat.mod_eq_of_lt hLength]

theorem hintRootControlInit_spec (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeader E header control hintMap resultMap listBase table count N)
    (hCtx : state.regs 14 = control) :
    let out := runBlock hintRootControlInit E state
    out.pc = state.pc + 11 ∧
      out.mem = Function.update (Function.update state.mem control table) (control + 1) count ∧
      HintDispatchData control table count (state.mem (control + 2)) out := by
  have hSpan := hdr.span
  have hWord := hdr.word
  have hCtrlSpan := hdr.control_span
  have h1 : 1 < 2 ^ E.W := by omega
  have h3 : 3 < 2 ^ E.W := by omega
  have h12 : 12 < 2 ^ E.W := by omega
  have hHdr : header < 2 ^ E.W := by omega
  have hA12 : header + 12 < 2 ^ E.W := by omega
  have hA13 : header + 12 + 1 < 2 ^ E.W := by omega
  have hA1 : control + 1 < 2 ^ E.W := by omega
  have hc1 : control ≠ control + 1 := by omega
  have hc2 : control + 2 ≠ control := by omega
  have hc21 : control + 2 ≠ control + 1 := by omega
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintRootControlInit, runBlock, execInstr, hCtx, hdr.anchor, hdr.dispatch_table, hdr.dispatch_count,
      Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h12, Nat.mod_eq_of_lt hHdr,
      Nat.mod_eq_of_lt hA12, Nat.mod_eq_of_lt hA13, Nat.mod_eq_of_lt hA1,
      Nat.mod_eq_of_lt hdr.table_fit, Nat.mod_eq_of_lt hdr.count_fit,
      Function.update_of_ne hc1, Function.update_of_ne hc2, Function.update_of_ne hc21]

theorem hintRootEmitArgs_spec (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeader E header control hintMap resultMap listBase table count N) :
    let out := runBlock hintRootEmitArgs E state
    out.pc = state.pc + 12 ∧ out.mem = state.mem ∧ out.regs 14 = state.regs 14 ∧
      HintEmitArgs listBase resultMap N out := by
  have hWidth := hdr.word
  have hSpan := hdr.span
  have hN := hdr.normalize.dest_span
  have h1 : 1 < 2 ^ E.W := by omega
  have h3 : 3 < 2 ^ E.W := by omega
  have h10 : 10 < 2 ^ E.W := by omega
  have h14 : 14 < 2 ^ E.W := by omega
  have hHdr : header < 2 ^ E.W := by omega
  have hA10 : header + 10 < 2 ^ E.W := by omega
  have hA14 : header + 14 < 2 ^ E.W := by omega
  have hNFit : N < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintRootEmitArgs, runBlock, execInstr, hdr.anchor, hdr.result_address, hdr.list_address,
      hdr.normalize.count_value, Nat.mod_eq_of_lt hWidth, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3,
      Nat.mod_eq_of_lt h10, Nat.mod_eq_of_lt h14, Nat.mod_eq_of_lt hHdr, Nat.mod_eq_of_lt hA10,
      Nat.mod_eq_of_lt hA14, Nat.mod_eq_of_lt hSpan, Nat.mod_eq_of_lt hNFit,
      Nat.mod_eq_of_lt hdr.result_fit, Nat.mod_eq_of_lt hdr.list_fit]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRootHintArgs_spec
#print axioms LinearSetReconciliation327.Main.hintRootControlInit_spec
#print axioms LinearSetReconciliation327.Main.hintRootEmitArgs_spec
end -- Def_LinearSetReconciliation327_Main_HintRootHeader20261120

section -- Def_LinearSetReconciliation327_Main_HintEmit20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintEmitSource (E : RAMEnv) (dest source count : ℕ)
    (accept : ℕ → Bool) (original : ℕ → ℕ) : Prop where
  word : 1 < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  dest_end : dest + count ≤ source
  destination_fit : dest + count ≤ 2 ^ E.W
  source_fit : ∀ q < count, source + q < 2 ^ E.W
  hint_bit : ∀ q < count, original (source + q) = if accept q then 1 else 0

structure HintEmitInv (dest source count q : ℕ) (accept : ℕ → Bool)
    (original : ℕ → ℕ) (s : RAMState) : Prop where
  args : HintEmitArgs dest source count s
  index : s.regs 0 = q
  used : s.regs 1 = (hintGatherList accept q).length
  stored : ∀ (i : ℕ) (hi : i < (hintGatherList accept q).length),
    s.mem (dest + i) = (hintGatherList accept q)[i]
  frame : CRMemFrame dest (dest + count) original s.mem

theorem hintEmitInv_step (E : RAMEnv) (s : RAMState)
    (dest source count q : ℕ) (accept : ℕ → Bool) (original : ℕ → ℕ)
    (hSource : HintEmitSource E dest source count accept original)
    (hq : q < count) (hInv : HintEmitInv dest source count q accept original s) :
    let out := runBlock hintEmitBody E s
    HintEmitInv dest source count (q + 1) accept original out ∧ out.regs 14 = s.regs 14 := by
  let L := hintGatherList accept q
  let flag : ℕ := if accept q then 1 else 0
  have hLen : L.length ≤ q := hintGatherList_length_le accept q
  have hCount := hSource.count_fit
  have hDest := hSource.destination_fit
  have hEnd := hSource.dest_end
  have hWord := hSource.word
  have hFlag : flag ≤ 1 := by dsimp [flag]; split <;> omega
  have hRead : s.mem (source + q) = flag :=
    (hInv.frame _ (Or.inr (by omega))).trans (hSource.hint_bit q hq)
  have hBlock := hintEmitBody_spec E s dest source count q L.length flag
    hInv.args hInv.index hInv.used (hSource.source_fit q hq) (by omega) hRead (by omega) (by omega) (by omega)
  generalize hExec : runBlock hintEmitBody E s = out at hBlock
  obtain ⟨_, hMem, hQ, hUsed, hArgs, hCtx⟩ := hBlock
  have hSucc : hintGatherList accept (q + 1) = L ++ (if accept q then [q] else []) :=
    hintGatherList_succ accept q
  refine ⟨⟨hArgs, hQ, ?_, ?_, ?_⟩, hCtx⟩
  · rw [hUsed, hSucc]
    cases hb : accept q <;> simp [flag, hb]
  · intro i hi
    rw [hMem]
    have transfer (a b : List ℕ) (heq : a = b) (j : ℕ) (hj : j < a.length) :
        a[j] = b[j]'(heq ▸ hj) := by
      subst b
      rfl
    have hAt : ∀ (j : ℕ) (hj : j < (hintGatherList accept (q + 1)).length),
        (hintGatherList accept (q + 1))[j] = (L ++ (if accept q then [q] else []))[j]'(hSucc ▸ hj) := by
      intro j hj
      exact transfer _ _ hSucc j hj
    rw [hAt i hi]
    by_cases hOld : i < L.length
    · rw [Function.update_of_ne (by omega : dest + i ≠ dest + L.length)]
      rw [List.getElem_append_left hOld]
      exact hInv.stored i hOld
    · have hNew : i = L.length := by
        have hh := hintGatherList_length_le accept (q + 1)
        have hLen' : (hintGatherList accept (q + 1)).length ≤ L.length + 1 := by
          rw [hSucc]
          cases hb : accept q <;> simp [hb]
        omega
      have hYes : accept q = true := by
        cases hb : accept q with
        | false =>
          have hEqLen : (hintGatherList accept (q + 1)).length = L.length := by simp [hSucc, hb]
          omega
        | true => rfl
      subst i
      simp [hYes]
  · intro addr hAway
    have hNe : addr ≠ dest + L.length := by rcases hAway with hBefore | hAfter <;> omega
    rw [hMem, Function.update_of_ne hNe, hInv.frame addr hAway]


theorem HintEmitInv.pc {dest source count q : ℕ}
    {accept : ℕ → Bool} {original : ℕ → ℕ} {s : RAMState}
    (h : HintEmitInv dest source count q accept original s) (pc : ℕ) :
    HintEmitInv dest source count q accept original {s with pc := pc} :=
  ⟨⟨h.args.destination, h.args.source_value, h.args.length, h.args.one⟩, h.index, h.used, h.stored, h.frame⟩

theorem HintEmitInv.test {dest source count q : ℕ}
    {accept : ℕ → Bool} {original : ℕ → ℕ} {s : RAMState}
    (h : HintEmitInv dest source count q accept original s) (E : RAMEnv) :
    HintEmitInv dest source count q accept original (runBlock (Cond.lt 2 0 6).code E s) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using h.args.destination
  · simpa [Cond.code, runBlock, execInstr] using h.args.source_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.length
  · simpa [Cond.code, runBlock, execInstr] using h.args.one
  · simpa [Cond.code, runBlock, execInstr] using h.index
  · simpa [Cond.code, runBlock, execInstr] using h.used
  · simpa [Cond.code, runBlock, execInstr] using h.stored
  · simpa [Cond.code, runBlock, execInstr] using h.frame

def hintEmitLoop : Stmt := .loop (.lt 2 0 6) (.code hintEmitBody)

theorem hintEmitLoop_len : hintEmitLoop.len = 9 := rfl

theorem hintEmitLoop_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source count base : ℕ) (accept : ℕ → Bool) (original : ℕ → ℕ)
    (hSource : HintEmitSource E dest source count accept original)
    (hInv : HintEmitInv dest source count 0 accept original state)
    (hAt : At P base (hintEmitLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 9) state (fun k out => k ≤ 9 * count + 2 ∧
      HintEmitInv dest source count count accept original out ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ q, q + left = count ∧
    HintEmitInv dest source count q accept original st ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) hintEmitBody := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨q, hQ, hData, hCtx⟩ := hI
    exact ⟨q, hQ, hData.pc pc, hCtx⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 0 6).code E st) := by
    intro left st hI
    obtain ⟨q, hQ, hData, hCtx⟩ := hI
    exact ⟨q, hQ, hData.test E, by simpa [Cond.code, runBlock, execInstr] using hCtx⟩
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 0 6).eval st := by
    intro left st hI
    obtain ⟨q, hQ, hData, _⟩ := hI
    change st.regs 0 < st.regs 6
    rw [hData.index, hData.args.length]; omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 0 6).eval st := by
    intro st hI
    obtain ⟨q, hQ, hData, _⟩ := hI
    change ¬ st.regs 0 < st.regs 6
    rw [hData.index, hData.args.length]; omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintEmitBody).len) st
        (fun k out => k ≤ 6 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨q, hQ, hData, hCtx⟩ := hI
    have hStep := hintEmitInv_step E st dest source count q accept original hSource
      (by omega) hData
    generalize hMid : runBlock hintEmitBody E st = mid at hStep
    have hNative := Sem.block P E (base + 2) hintEmitBody st hBodyAt
      (by simp [hintEmitBody, NoBranch, Instr.NoBranchI]) hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hOut⟩ := hOut
    rw [hMid] at hOut
    subst out
    exact ⟨hCost.le, q + 1, by omega, hStep.1, hStep.2.trans hCtx⟩
  have hInitial : I count state := ⟨0, by omega, hInv, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintEmitBody) hAt hSource.word I 6
    hIpc hItest hGo hStop hBody count state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, q, hQ, hFinal, hCtx⟩ := hOut
  have hEq : q = count := by omega
  rw [hEq] at hFinal
  exact ⟨hCost, hFinal, hCtx⟩

def hintEmitInit : List Instr := [.imm 0 0, .imm 1 0]
def hintEmitStmt : Stmt := .seq (.code hintEmitInit) hintEmitLoop

theorem hintEmitStmt_len : hintEmitStmt.len = 11 := rfl

/-- Write the support of an explicit bitmap in increasing order. The output
buffer reserves enough space for all indices, including tentative writes. -/
theorem hintEmitStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source count base : ℕ) (accept : ℕ → Bool)
    (hSource : HintEmitSource E dest source count accept state.mem)
    (hArgs : HintEmitArgs dest source count state)
    (hAt : At P base (hintEmitStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 11) state (fun k out => k ≤ 9 * count + 4 ∧
      HintEmitInv dest source count count accept state.mem out ∧ out.regs 14 = state.regs 14) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintEmitInit at hInitAt
  change At P (base + 2) (hintEmitLoop.compile (base + 2)) at hLoopAt
  have hInit : let out := runBlock hintEmitInit E state
      out.pc = state.pc + 2 ∧ out.regs 14 = state.regs 14 ∧
      HintEmitInv dest source count 0 accept state.mem out := by
    refine ⟨?_, ?_, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
    · simp [hintEmitInit, runBlock, execInstr]
    · simp [hintEmitInit, runBlock, execInstr]
    · simpa [hintEmitInit, runBlock, execInstr] using hArgs.destination
    · simpa [hintEmitInit, runBlock, execInstr] using hArgs.source_value
    · simpa [hintEmitInit, runBlock, execInstr] using hArgs.length
    · simpa [hintEmitInit, runBlock, execInstr] using hArgs.one
    · simp [hintEmitInit, runBlock, execInstr]
    · simp [hintEmitInit, runBlock, execInstr, hintGatherList]
    · intro i hi
      simp [hintGatherList] at hi
    · intro addr hAway
      rfl
  generalize hI : runBlock hintEmitInit E state = mid at hInit
  obtain ⟨hPcI, hCtxI, hInvI⟩ := hInit
  have hRunI : (step P E)^[2] state = mid := by
    have hh := iterate_runBlock_of_at P E hintEmitInit state (by rwa [hPc])
      (by simp [hintEmitInit, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  obtain ⟨_, k, out, hRun, hPcOut, hCost, hInvOut, hCtx⟩ :=
    hintEmitLoop_sem P E mid dest source count (base + 2) accept state.mem
      hSource hInvI hLoopAt (by omega)
  exact ⟨hPc, k + 2, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega,
    hInvOut, hCtx.trans hCtxI⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintEmitStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintEmit20261120

section -- Def_LinearSetReconciliation327_Main_HintEmitFinish20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintEmitFinish : List Instr := [.imm 3 0, .add 0 4 3]
def hintEmitResult : Stmt := .seq hintEmitStmt (.code hintEmitFinish)

theorem hintEmitResult_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source count base : ℕ) (accept : ℕ → Bool)
    (hSource : HintEmitSource E dest source count accept state.mem) (hFit : dest < 2 ^ E.W)
    (hArgs : HintEmitArgs dest source count state)
    (hAt : At P base (hintEmitResult.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 13) state (fun k out => k ≤ 9 * count + 6 ∧
      out.regs 14 = state.regs 14 ∧ outList out = hintGatherList accept count ∧
      CRMemFrame dest (dest + count) state.mem out.mem) := by
  obtain ⟨hEmitAt, hFinishAt⟩ := At.seqStmt hAt
  change At P base (hintEmitStmt.compile base) at hEmitAt
  change At P (base + 11) hintEmitFinish at hFinishAt
  obtain ⟨_, k, mid, hRun, hPcMid, hCost, hInv, hContext⟩ :=
    hintEmitStmt_sem P E state dest source count base accept hSource hArgs hEmitAt hPc
  let out := runBlock hintEmitFinish E mid
  have hRunF : (step P E)^[2] mid = out :=
    iterate_runBlock_of_at P E hintEmitFinish mid (by rwa [hPcMid])
      (by simp [hintEmitFinish, NoBranch, Instr.NoBranchI])
  have hOutPc : out.pc = base + 13 := by simp [out, hintEmitFinish, runBlock, execInstr, hPcMid]
  have hCtx : out.regs 14 = state.regs 14 := by simp [out, hintEmitFinish, runBlock, execInstr, hContext]
  have hPointer : out.regs 0 = dest := by
    simp [out, hintEmitFinish, runBlock, execInstr, hInv.args.destination, Nat.mod_eq_of_lt hFit]
  have hCount : out.regs 1 = (hintGatherList accept count).length := by
    simp [out, hintEmitFinish, runBlock, execInstr, hInv.used]
  refine ⟨hPc, 2 + k, out, hintIterate_then (step P E) hRun hRunF, hOutPc, by omega, hCtx, ?_, hInv.frame⟩
  apply List.ext_getElem
  · simp [outList, hCount]
  · intro j hJ hJ'
    have hMem : out.mem = mid.mem := rfl
    simpa [outList, hPointer, hMem] using hInv.stored j hJ'

theorem hintEmitResult_support {N : ℕ} (state : RAMState) (x : Fin N → ZMod 2) (accept : ℕ → Bool)
    (hAccept : ∀ i : Fin N, accept i.val = true ↔ x i = 1)
    (hList : outList state = hintGatherList accept N) : OutputsSupport state x := by
  rw [OutputsSupport, hList]
  constructor
  · exact List.Nodup.filter _ List.nodup_range
  · intro j
    simp only [hintGatherList, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨hj, hA⟩
      exact ⟨⟨j, hj⟩, rfl, (hAccept ⟨j, hj⟩).mp hA⟩
    · rintro ⟨i, rfl, hI⟩
      exact ⟨i.isLt, (hAccept i).mpr hI⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintEmitResult_sem
#print axioms LinearSetReconciliation327.Main.hintEmitResult_support
end -- Def_LinearSetReconciliation327_Main_HintEmitFinish20261120

section -- Def_LinearSetReconciliation327_Main_HintRootIO20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRootEnter : Stmt :=
  .seq (.code hintRootHintArgs) (.seq hintNormalizeStmt (.code hintRootControlInit))
def hintRootExit : Stmt := .seq (.code hintRootEmitArgs) hintEmitResult

theorem hintRootEnter_len : hintRootEnter.len = 56 := rfl
theorem hintRootExit_len : hintRootExit.len = 25 := rfl

theorem hintRootEnter_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N base : ℕ)
    (hdr : HintRootHeader E header control hintMap resultMap listBase table count N)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W)
    (hSpan : state.regs 1 + min (state.regs 2) N ≤ 2 ^ E.W)
    (hSeparate : state.regs 1 + min (state.regs 2) N ≤ hintMap ∨ hintMap + N < state.regs 1)
    (hControl : control + 2 ≤ hintMap ∨ hintMap + N < control)
    (hAt : At P base (hintRootEnter.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 56) state (fun k out => k ≤ 20 * N + 40 ∧
      HintDispatchData control table count (out.mem (control + 2)) out ∧
      (∀ q < N, out.mem (hintMap + q) = hintStampValue E (state.regs 1) (min (state.regs 2) N) state.mem q) ∧
      (∀ address, (address < hintMap ∨ hintMap + N < address) →
        address ≠ control → address ≠ control + 1 → out.mem address = state.mem address)) := by
  obtain ⟨hArgsAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintRootHintArgs at hArgsAt
  change At P (base + 5) ((Stmt.seq hintNormalizeStmt (.code hintRootControlInit)).compile (base + 5))
    at hRestAt
  obtain ⟨hNormalizeAt, hControlAt⟩ := At.seqStmt hRestAt
  change At P (base + 5) (hintNormalizeStmt.compile (base + 5)) at hNormalizeAt
  change At P (base + 45) hintRootControlInit at hControlAt
  have hSetup := hintRootHintArgs_spec E state header control hintMap resultMap listBase table count N hdr hSource hLength
  generalize hs : runBlock hintRootHintArgs E state = entered at hSetup
  obtain ⟨hSetupPc, hSetupMem, hHead, hSrc, hCount⟩ := hSetup
  have hRunSetup : (step P E)^[5] state = entered := by
    have hh := iterate_runBlock_of_at P E hintRootHintArgs state (by rwa [hPc])
      (by simp [hintRootHintArgs, NoBranch, Instr.NoBranchI])
    rw [hs] at hh
    exact hh
  obtain ⟨_, kn, marked, hRunN, hPcN, hCost, hCtxN, hHints, hFrame⟩ :=
    hintNormalizeStmt_sem P E entered header hintMap N control (base + 5) hdr.normalize hHead
      (hSrc.symm ▸ hSource) (by rw [hSrc, hCount]; exact hSpan)
      (by rw [hSrc, hCount]; exact hSeparate) hNormalizeAt (by omega)
  have hFinal := hintRootControlInit_spec E marked header control hintMap resultMap listBase table count N hdr hCtxN
  generalize hf : runBlock hintRootControlInit E marked = out at hFinal
  obtain ⟨hFinalPc, hFinalMem, hCtrl⟩ := hFinal
  have hRunFinal : (step P E)^[11] marked = out := by
    have hh := iterate_runBlock_of_at P E hintRootControlInit marked (by rwa [hPcN])
      (by simp [hintRootControlInit, NoBranch, Instr.NoBranchI])
    rw [hf] at hh
    exact hh
  refine ⟨hPc, 11 + (kn + 5), out, hintIterate_then (step P E)
      (hintIterate_then (step P E) hRunSetup hRunN) hRunFinal,
    by omega, by omega, ⟨hCtrl.context, hCtrl.table_pointer, hCtrl.size, rfl⟩, ?_, ?_⟩
  · intro q hq
    have hA : hintMap + q ≠ control := by rcases hControl with h | h <;> omega
    have hB : hintMap + q ≠ control + 1 := by rcases hControl with h | h <;> omega
    rw [hFinalMem, Function.update_of_ne hB, Function.update_of_ne hA, hHints q hq, hSrc, hCount, hSetupMem]
  · intro addr hAway hA hB
    rw [hFinalMem, Function.update_of_ne hB, Function.update_of_ne hA,
      hFrame addr (by rcases hAway with h | h <;> omega), hSetupMem]

theorem hintRootExit_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N base : ℕ)
    (hdr : HintRootHeader E header control hintMap resultMap listBase table count N)
    (hSep : listBase + N ≤ resultMap) (hBitsSpan : resultMap + N ≤ 2 ^ E.W)
    (accept : ℕ → Bool)
    (hBits : ∀ q < N, state.mem (resultMap + q) = if accept q then 1 else 0)
    (hAt : At P base (hintRootExit.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 25) state (fun k out => k ≤ 9 * N + 18 ∧
      outList out = hintGatherList accept N ∧ CRMemFrame listBase (listBase + N) state.mem out.mem) := by
  obtain ⟨hArgsAt, hEmitAt⟩ := At.seqStmt hAt
  change At P base hintRootEmitArgs at hArgsAt
  change At P (base + 12) (hintEmitResult.compile (base + 12)) at hEmitAt
  have hSetup := hintRootEmitArgs_spec E state header control hintMap resultMap listBase table count N hdr
  generalize hs : runBlock hintRootEmitArgs E state = ready at hSetup
  obtain ⟨hReady, hMem, _, hArgs⟩ := hSetup
  have hRunSetup : (step P E)^[12] state = ready := by
    have h := iterate_runBlock_of_at P E hintRootEmitArgs state (by rwa [hPc])
      (by simp [hintRootEmitArgs, NoBranch, Instr.NoBranchI])
    rw [hs] at h
    exact h
  have hWidth := hdr.word
  have hN := hdr.normalize.dest_span
  have hInput : HintEmitSource E listBase resultMap N accept ready.mem := by
    refine ⟨by omega, by omega, hSep, by omega, ?_, ?_⟩
    · intro q hq; omega
    · rw [hMem]
      exact hBits
  obtain ⟨_, k, out, hRun, hEnd, hCost, _, hList, hFrame⟩ :=
    hintEmitResult_sem P E ready listBase resultMap N (base + 12) accept hInput hdr.list_fit hArgs
      hEmitAt (by omega)
  exact ⟨hPc, k + 12, out, hintIterate_then (step P E) hRunSetup hRun, by omega, by omega, hList, hMem ▸ hFrame⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRootEnter_sem
#print axioms LinearSetReconciliation327.Main.hintRootExit_sem
end -- Def_LinearSetReconciliation327_Main_HintRootIO20261120

section -- Def_LinearSetReconciliation327_Main_HintStageBit20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintStageWrite_spec (E : RAMEnv) (p : RAMState) (w memBase k : ℕ)
    (hw : 0 < w) (hWide : w ≤ E.W) (hWidth : p.regs 7 = w) (hBase : p.regs 9 = memBase)
    (hCounter : p.regs 12 = k) (hOne : p.regs 15 = 1) (hBit : p.regs 0 ≤ 1)
    (hAddr : memBase + k / w < 2 ^ E.W) (hNext : k + 1 < 2 ^ E.W)
    (hSum : p.mem (memBase + k / w) + p.regs 0 * 2 ^ (k % w) < 2 ^ E.W) :
    let out := runBlock crWriteInputBit E p
    out.pc = p.pc + 8 ∧ out.regs 12 = k + 1 ∧
      out.mem = Function.update p.mem (memBase + k / w)
        (p.mem (memBase + k / w) + p.regs 0 * 2 ^ (k % w)) ∧
      ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 12 → out.regs r = p.regs r := by
  have hPow : 2 ^ (k % w) < 2 ^ E.W :=
    Nat.pow_lt_pow_right (by norm_num) ((Nat.mod_lt k hw).trans_le hWide)
  have hMask : p.regs 0 * 2 ^ (k % w) < 2 ^ E.W := by
    calc p.regs 0 * 2 ^ (k % w) ≤ 1 * 2 ^ (k % w) := Nat.mul_le_mul_right _ hBit
         _ = 2 ^ (k % w) := one_mul _
         _ < 2 ^ E.W := hPow
  have hOld : p.mem (memBase + k / w) < 2 ^ E.W := (Nat.le_add_right _ _).trans_lt hSum
  have hK : k < 2 ^ E.W := by omega
  have hDiv : k / w < 2 ^ E.W := (Nat.div_le_self _ _).trans_lt hK
  have hMod : k % w < 2 ^ E.W := (Nat.mod_lt k hw).trans
    (hWide.trans_lt (Nat.lt_two_pow_self (n := E.W)))
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [crWriteInputBit, runBlock, execInstr, Nat.add_assoc]
  · simp [crWriteInputBit, runBlock, execInstr, Function.update, hCounter, hOne, Nat.mod_eq_of_lt hNext]
  · simp [crWriteInputBit, runBlock, execInstr, Function.update, hWidth, hBase, hCounter,
      Nat.mod_eq_of_lt hMod, Nat.mod_eq_of_lt hMask, Nat.mod_eq_of_lt hDiv,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hOld, Nat.mod_eq_of_lt hSum]
  · intro r hr0 hr1 hr2 hr3 hr12
    simp [crWriteInputBit, runBlock, execInstr, Function.update, hr0, hr1, hr2, hr3, hr12]

structure HintStageArgs (E : RAMEnv) (w M off memBase : ℕ) (p : RAMState) : Prop where
  offset : p.regs 5 = off
  source_width : p.regs 7 = w
  mem_base : p.regs 9 = memBase
  physical_width : p.regs 11 = E.W
  two : p.regs 13 = 2
  rows : p.regs 6 = M
  one : p.regs 15 = 1

structure HintStageInv (E : RAMEnv) (w M off memBase : ℕ) (y : Fin M → ZMod 2)
    (original : ℕ → ℕ) (k : ℕ) (p : RAMState) : Prop where
  params : HintStageArgs E w M off memBase p
  counter : p.regs 12 = k
  packed : ∀ a < wordsOf w M, p.mem (memBase + a) = packMem w (crPackPrefix y k) a
  frame : CRMemFrame memBase (memBase + wordsOf w M) original p.mem

theorem hintStageBit_spec (E : RAMEnv) (p : RAMState) (w M off memBase k : ℕ)
    (y : Fin M → ZMod 2) (original : ℕ → ℕ) (hw : 0 < w) (hWide : w ≤ E.W)
    (hSpan : off + M < 2 ^ E.W) (hMem : memBase + wordsOf w M ≤ 2 ^ E.W)
    (hBelow : (off + M) / E.W < memBase)
    (hBits : ∀ i : Fin M, bitAt original E.W 0 (off + i.val) = if y i = 1 then 1 else 0)
    (hInv : HintStageInv E w M off memBase y original k p) (hk : k < M) :
    let out := runBlock crCopyInputBit E p
    out.pc = p.pc + 14 ∧ HintStageInv E w M off memBase y original (k + 1) out ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 12 → out.regs r = p.regs r) ∧
      out.mem = Function.update p.mem (memBase + k / w) (packMem w (crPackPrefix y (k + 1)) (k / w)) := by
  let bit : ℕ := if y ⟨k, hk⟩ = 1 then 1 else 0
  have hBit : bit ≤ 1 := by dsimp [bit]; split_ifs <;> omega
  have hIndex : p.regs 5 + p.regs 12 < 2 ^ E.W := by rw [hInv.params.offset, hInv.counter]; omega
  have hNext : k + 1 < 2 ^ E.W := by omega
  have hAddressBound : k / w < wordsOf w M := crBit_div_lt_words hw hk
  have hAddr : memBase + k / w < 2 ^ E.W := by omega
  have hReadBelow : (off + k) / E.W < memBase :=
    (Nat.div_le_div_right (by omega : off + k ≤ off + M)).trans_lt hBelow
  have hInput : bitAt p.mem E.W 0 (p.regs 5 + p.regs 12) = bit := by
    rw [hInv.params.offset, hInv.counter]
    have hLow : p.mem (0 + (off + k) / E.W) = original (0 + (off + k) / E.W) := by
      simpa only [Nat.zero_add] using hInv.frame _ (Or.inl hReadBelow)
    unfold bitAt
    rw [hLow]
    exact hBits ⟨k, hk⟩
  generalize hu : runBlock crReadInputBit E p = u
  have hU := crReadInputBit_spec E p (by omega) hInv.params.physical_width hInv.params.two hIndex
  rw [hu] at hU
  obtain ⟨hUpc, hUmem, hU0, hU1, hU2, hUfr⟩ := hU
  have hUbit : u.regs 0 = bit := hU0.trans hInput
  have hU7 : u.regs 7 = w := (hUfr 7 (by decide) (by decide) (by decide)).trans hInv.params.source_width
  have hU9 : u.regs 9 = memBase := (hUfr 9 (by decide) (by decide) (by decide)).trans hInv.params.mem_base
  have hU12 : u.regs 12 = k := (hUfr 12 (by decide) (by decide) (by decide)).trans hInv.counter
  have hU15 : u.regs 15 = 1 := (hUfr 15 (by decide) (by decide) (by decide)).trans hInv.params.one
  have hMask : bit * 2 ^ (k % w) = if y ⟨k, hk⟩ = 1 then 2 ^ (k % w) else 0 := by
    dsimp [bit]
    split_ifs <;> simp
  have hSumEq : u.mem (memBase + k / w) + u.regs 0 * 2 ^ (k % w) =
      packMem w (crPackPrefix y (k + 1)) (k / w) := by
    rw [hUmem, hUbit, hMask, hInv.packed _ hAddressBound, crPackPrefix_step w y k hk]
    simp
  have hSum : u.mem (memBase + k / w) + u.regs 0 * 2 ^ (k % w) < 2 ^ E.W := by
    rw [hSumEq]
    exact (packMem_lt w hw _ _).trans_le (Nat.pow_le_pow_right (by norm_num) hWide)
  generalize ho : runBlock crWriteInputBit E u = out
  have hO := hintStageWrite_spec E u w memBase k hw hWide hU7 hU9 hU12 hU15
    (by rw [hUbit]; exact hBit) hAddr hNext hSum
  rw [ho] at hO
  obtain ⟨hOpc, hO12, hOmem, hOfr⟩ := hO
  have hFrame : ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 12 → out.regs r = p.regs r := by
    intro r hr0 hr1 hr2 hr3 hr12
    exact (hOfr r hr0 hr1 hr2 hr3 hr12).trans (hUfr r hr0 hr1 hr2)
  have hMemOut : out.mem = Function.update p.mem (memBase + k / w)
      (p.mem (memBase + k / w) + if y ⟨k, hk⟩ = 1 then 2 ^ (k % w) else 0) := by
    rw [hOmem, hUmem, hUbit, hMask]
  have hExact : out.mem = Function.update p.mem (memBase + k / w)
      (packMem w (crPackPrefix y (k + 1)) (k / w)) := by
    rw [hOmem, hSumEq, hUmem]
  have hRun : runBlock crCopyInputBit E p = out := by rw [crCopyInputBit, runBlock_append, hu, ho]
  dsimp only
  rw [hRun]
  refine ⟨by omega, ?_, hFrame, hExact⟩
  refine ⟨?_, hO12, ?_, ?_⟩
  · exact ⟨(hFrame 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.offset,
      (hFrame 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.source_width,
      (hFrame 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.mem_base,
      (hFrame 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.physical_width,
      (hFrame 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.two,
      (hFrame 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.rows,
      (hFrame 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.one⟩
  · intro a ha
    rw [hMemOut]
    exact crPackPrefix_store hw y k hk memBase (wordsOf w M - 1) p.mem (by omega)
      (fun t ht => hInv.packed t (by omega)) a (by omega)
  · intro a ha
    have hNe : a ≠ memBase + k / w := by
      rcases ha with h | h
      · exact Nat.ne_of_lt (h.trans_le (Nat.le_add_right _ _))
      · exact Nat.ne_of_gt ((Nat.add_lt_add_left hAddressBound memBase).trans_le h)
    rw [hMemOut, Function.update_of_ne hNe, hInv.frame a ha]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStageBit_spec
end -- Def_LinearSetReconciliation327_Main_HintStageBit20261120

section -- Def_LinearSetReconciliation327_Main_HintStage20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintStageLoop : Stmt := .loop (.lt 2 12 6) (.code crCopyInputBit)
def hintStageStmt : Stmt := .seq (.code [.imm 12 0]) hintStageLoop

structure HintStagePre (E : RAMEnv) (w count off dest : ℕ) : Prop where
  word : 1 < 2 ^ E.W
  width_pos : 0 < w
  width_le : w ≤ E.W
  input_span : off + count < 2 ^ E.W
  destination : dest + wordsOf w count ≤ 2 ^ E.W
  separate : (off + count) / E.W < dest

theorem hintStageLoop_sem (P : Program) (E : RAMEnv) (state initial : RAMState)
    (w count off dest base : ℕ) (pre : HintStagePre E w count off dest)
    (y : Fin count → ZMod 2) (hBits : ∀ i : Fin count,
      bitAt initial.mem E.W 0 (off + i.val) = if y i = 1 then 1 else 0)
    (inv : HintStageInv E w count off dest y initial.mem 0 state)
    (hContext : state.regs 14 = initial.regs 14)
    (hAt : At P base (hintStageLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 17) state (fun k out => k ≤ 17 * count + 2 ∧
      HintStageInv E w count off dest y initial.mem count out ∧ out.regs 14 = initial.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left s => ∃ i, i + left = count ∧
    HintStageInv E w count off dest y initial.mem i s ∧ s.regs 14 = initial.regs 14
  have hIpc : ∀ left s pc, I left s → I left {s with pc := pc} := by
    rintro left s pc ⟨i, hi, h, hc⟩
    exact ⟨i, hi, ⟨⟨h.params.offset, h.params.source_width, h.params.mem_base, h.params.physical_width,
      h.params.two, h.params.rows, h.params.one⟩,
      h.counter, h.packed, h.frame⟩, hc⟩
  have hTest : ∀ left s, I left s → I left (runBlock (Cond.lt 2 12 6).code E s) := by
    rintro left s ⟨i, hi, h, hc⟩
    refine ⟨i, hi, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, h.packed, h.frame⟩, ?_⟩
    all_goals simp [Cond.code, runBlock, execInstr, h.params.offset, h.params.source_width, h.params.mem_base, h.params.physical_width,
      h.params.two, h.params.rows, h.params.one, h.counter, hc]
  have hGo : ∀ left s, I (left + 1) s → (Cond.lt 2 12 6).eval s := by
    rintro left s ⟨i, hi, h, hc⟩
    change s.regs 12 < s.regs 6
    rw [h.counter, h.params.rows]; omega
  have hStop : ∀ s, I 0 s → ¬ (Cond.lt 2 12 6).eval s := by
    rintro s ⟨i, hi, h, hc⟩
    change ¬ s.regs 12 < s.regs 6
    rw [h.counter, h.params.rows]; omega
  have hBodyAt : At P (base + 2) crCopyInputBit := (at_loop hAt).2.2.1
  have hBody : ∀ left s, I (left + 1) s → s.pc = base + (Cond.lt 2 12 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 12 6).code.length + 1)
        (base + (Cond.lt 2 12 6).code.length + 1 + (Stmt.code crCopyInputBit).len) s
        (fun k out => k ≤ 14 ∧ I left out) := by
    rintro left s ⟨i, hi, h, hc⟩ hStart
    have hp : s.pc = base + 2 := by exact hStart
    have hNative := Sem.block P E (base + 2) crCopyInputBit s hBodyAt
      (by simp [crCopyInputBit, crReadInputBit, crWriteInputBit, NoBranch, Instr.NoBranchI]) hp
    apply Sem.mono hNative
    rintro k out ⟨hk, rfl⟩
    obtain ⟨_, hNext, hRegs, _⟩ := hintStageBit_spec E s w count off dest i y initial.mem
      pre.width_pos pre.width_le pre.input_span pre.destination pre.separate hBits h (by omega)
    exact ⟨hk.le, i + 1, by omega, hNext, (hRegs 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 12 6) (.code crCopyInputBit) hAt pre.word I 14
    hIpc hTest hGo hStop hBody count state ⟨0, by omega, inv, hContext⟩ hPc
  apply Sem.mono hNative
  rintro k out ⟨hk, i, hi, h, hc⟩
  have he : i = count := by omega
  exact ⟨hk, he ▸ h, hc⟩

theorem hintStageStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (w count off dest base : ℕ) (pre : HintStagePre E w count off dest)
    (y : Fin count → ZMod 2) (args : HintStageArgs E w count off dest state)
    (hBits : ∀ i : Fin count, bitAt state.mem E.W 0 (off + i.val) = if y i = 1 then 1 else 0)
    (hClear : ∀ a < wordsOf w count, state.mem (dest + a) = 0)
    (hAt : At P base (hintStageStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 18) state (fun k out => k ≤ 17 * count + 3 ∧
      (∀ a < wordsOf w count, out.mem (dest + a) = packMem w y a) ∧
      out.regs 14 = state.regs 14 ∧ CRMemFrame dest (dest + wordsOf w count) state.mem out.mem) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  let mid := runBlock [.imm 12 0] E state
  have hRunI : (step P E)^[1] state = mid :=
    iterate_runBlock_of_at P E [.imm 12 0] state (by rwa [hPc])
      (by simp [NoBranch, Instr.NoBranchI])
  have hInv : HintStageInv E w count off dest y state.mem 0 mid := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun _ _ => rfl⟩
    all_goals simp [mid, runBlock, execInstr, args.offset, args.source_width, args.mem_base,
      args.physical_width, args.two, args.rows, args.one]
    intro a ha
    simpa [crPackPrefix, packMem, mid, runBlock, execInstr] using hClear a ha
  have hPcI : mid.pc = base + 1 := by simp [mid, runBlock, execInstr, hPc]
  obtain ⟨_, k, out, hRun, hEnd, hk, h, hc⟩ :=
    hintStageLoop_sem P E mid state w count off dest (base + 1) pre y hBits hInv rfl hLoopAt hPcI
  refine ⟨hPc, k + 1, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega, ?_, hc, h.frame⟩
  have hPrefix : crPackPrefix y count = y := by
    funext i
    exact if_pos i.isLt
  simpa only [hPrefix] using h.packed

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStageStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintStage20261120

section -- Def_LinearSetReconciliation327_Main_HintUnpackBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintUnpackWrite : List Instr := [.add 3 4 12, .store 3 0, .add 12 12 15]
def hintUnpackBody : List Instr := crReadInputBit ++ hintUnpackWrite

structure HintUnpackArgs (E : RAMEnv) (dest offset count : ℕ) (s : RAMState) : Prop where
  destination : s.regs 4 = dest
  offset_value : s.regs 5 = offset
  length : s.regs 6 = count
  width : s.regs 11 = E.W
  two : s.regs 13 = 2
  one : s.regs 15 = 1

theorem hintUnpackBody_spec (E : RAMEnv) (s : RAMState) (dest offset count i : ℕ)
    (hWidth : 0 < E.W) (hD : dest + i < 2 ^ E.W)
    (hS : offset + i < 2 ^ E.W) (hNext : i + 1 < 2 ^ E.W)
    (args : HintUnpackArgs E dest offset count s) (hIndex : s.regs 12 = i) :
    let out := runBlock hintUnpackBody E s
    out.pc = s.pc + 9 ∧ out.regs 12 = i + 1 ∧ HintUnpackArgs E dest offset count out ∧
      out.regs 14 = s.regs 14 ∧
      out.mem = Function.update s.mem (dest + i) (bitAt s.mem E.W 0 (offset + i)) := by
  have read := crReadInputBit_spec E s hWidth args.width args.two (by rw [args.offset_value, hIndex]; exact hS)
  generalize hr : runBlock crReadInputBit E s = mid at read
  obtain ⟨hPc, hMem, hBit, _, _, hRegs⟩ := read
  have hMid4 := (hRegs 4 (by decide) (by decide) (by decide)).trans args.destination
  have hMid12 := (hRegs 12 (by decide) (by decide) (by decide)).trans hIndex
  have hMid15 := (hRegs 15 (by decide) (by decide) (by decide)).trans args.one
  have hMid0 : mid.regs 0 = bitAt s.mem E.W 0 (offset + i) := by
    rw [hBit, args.offset_value, hIndex]
  dsimp only
  rw [hintUnpackBody, runBlock_append, hr]
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [hintUnpackWrite, runBlock, execInstr, hPc]
  · simp [hintUnpackWrite, runBlock, execInstr, hMid12, hMid15, Nat.mod_eq_of_lt hNext]
  · simpa [hintUnpackWrite, runBlock, execInstr] using hMid4
  · simpa [hintUnpackWrite, runBlock, execInstr] using (hRegs 5 (by decide) (by decide) (by decide)).trans args.offset_value
  · simpa [hintUnpackWrite, runBlock, execInstr] using (hRegs 6 (by decide) (by decide) (by decide)).trans args.length
  · simpa [hintUnpackWrite, runBlock, execInstr] using (hRegs 11 (by decide) (by decide) (by decide)).trans args.width
  · simpa [hintUnpackWrite, runBlock, execInstr] using (hRegs 13 (by decide) (by decide) (by decide)).trans args.two
  · simpa [hintUnpackWrite, runBlock, execInstr] using hMid15
  · simpa [hintUnpackWrite, runBlock, execInstr] using hRegs 14 (by decide) (by decide) (by decide)
  · simp [hintUnpackWrite, runBlock, execInstr, hMid4, hMid12, hMid0, hMem, Nat.mod_eq_of_lt hD]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintUnpackBody_spec
end -- Def_LinearSetReconciliation327_Main_HintUnpackBody20261120

section -- Def_LinearSetReconciliation327_Main_HintUnpack20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintUnpackLoop : Stmt := .loop (.lt 2 12 6) (.code hintUnpackBody)
def hintUnpackStmt : Stmt := .seq (.code [.imm 12 0]) hintUnpackLoop

structure HintUnpackPre (E : RAMEnv) (dest offset count : ℕ) : Prop where
  positive : 0 < E.W
  word : 1 < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  destination : dest + count ≤ 2 ^ E.W
  offset_span : offset + count ≤ 2 ^ E.W
  input_before : (offset + count) / E.W < dest

structure HintUnpackInv (E : RAMEnv) (dest offset count index : ℕ)
    (initial : RAMState) (state : RAMState) : Prop where
  args : HintUnpackArgs E dest offset count state
  position : state.regs 12 = index
  context : state.regs 14 = initial.regs 14
  data : ∀ i < index, state.mem (dest + i) = bitAt initial.mem E.W 0 (offset + i)
  frame : CRMemFrame dest (dest + count) initial.mem state.mem

theorem hintUnpackInv_step (E : RAMEnv) (state initial : RAMState)
    (dest offset count i : ℕ) (pre : HintUnpackPre E dest offset count)
    (inv : HintUnpackInv E dest offset count i initial state) (hi : i < count) :
    HintUnpackInv E dest offset count (i + 1) initial (runBlock hintUnpackBody E state) := by
  classical
  have hd : dest + i < 2 ^ E.W := by have := pre.destination; omega
  have hs : offset + i < 2 ^ E.W := by have := pre.offset_span; omega
  have hn : i + 1 < 2 ^ E.W := by have := pre.count_fit; omega
  have hRead : bitAt state.mem E.W 0 (offset + i) = bitAt initial.mem E.W 0 (offset + i) := by
    unfold bitAt
    rw [Nat.zero_add, inv.frame]
    apply Or.inl
    exact (Nat.div_le_div_right (by omega : offset + i ≤ offset + count)).trans_lt pre.input_before
  obtain ⟨_, hIter, hArgs, hCtx, hMem⟩ :=
    hintUnpackBody_spec E state dest offset count i pre.positive hd hs hn inv.args inv.position
  refine ⟨hArgs, hIter, hCtx.trans inv.context, ?_, ?_⟩
  · intro j hj
    by_cases h : j = i
    · subst j; simp [hMem, hRead]
    · rw [hMem, Function.update_of_ne (by omega : dest + j ≠ dest + i)]
      exact inv.data j (by omega)
  · intro address hAway
    have hne : address ≠ dest + i := by rcases hAway with h | h <;> omega
    rw [hMem, Function.update_of_ne hne, inv.frame address hAway]

theorem hintUnpackLoop_sem (P : Program) (E : RAMEnv) (state initial : RAMState)
    (dest offset count base : ℕ) (pre : HintUnpackPre E dest offset count)
    (inv : HintUnpackInv E dest offset count 0 initial state)
    (hAt : At P base (hintUnpackLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 12) state (fun k out => k ≤ 12 * count + 2 ∧
      HintUnpackInv E dest offset count count initial out) := by
  let I : ℕ → RAMState → Prop := fun left s => ∃ i, i + left = count ∧
    HintUnpackInv E dest offset count i initial s
  have hIpc : ∀ left s pc, I left s → I left {s with pc := pc} := by
    rintro left s pc ⟨i, hi, h⟩
    exact ⟨i, hi, ⟨⟨h.args.destination, h.args.offset_value, h.args.length,
      h.args.width, h.args.two, h.args.one⟩,
      h.position, h.context, h.data, h.frame⟩⟩
  have hTest : ∀ left s, I left s → I left (runBlock (Cond.lt 2 12 6).code E s) := by
    rintro left s ⟨i, hi, h⟩
    refine ⟨i, hi, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, h.data, h.frame⟩⟩
    all_goals simp [Cond.code, runBlock, execInstr, h.args.destination, h.args.offset_value,
      h.args.length, h.args.width, h.args.two, h.args.one, h.position, h.context]
  have hGo : ∀ left s, I (left + 1) s → (Cond.lt 2 12 6).eval s := by
    rintro left s ⟨i, hi, h⟩
    change s.regs 12 < s.regs 6
    rw [h.position, h.args.length]; omega
  have hStop : ∀ s, I 0 s → ¬ (Cond.lt 2 12 6).eval s := by
    rintro s ⟨i, hi, h⟩
    change ¬ s.regs 12 < s.regs 6
    rw [h.position, h.args.length]; omega
  have hBodyAt : At P (base + 2) hintUnpackBody := (at_loop hAt).2.2.1
  have hBody : ∀ left s, I (left + 1) s → s.pc = base + (Cond.lt 2 12 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 12 6).code.length + 1)
        (base + (Cond.lt 2 12 6).code.length + 1 + (Stmt.code hintUnpackBody).len) s
        (fun k out => k ≤ 9 ∧ I left out) := by
    rintro left s ⟨i, hi, h⟩ hStart
    have hp : s.pc = base + 2 := by exact hStart
    have hNative := Sem.block P E (base + 2) hintUnpackBody s hBodyAt
      (by simp [hintUnpackBody, crReadInputBit, hintUnpackWrite, NoBranch, Instr.NoBranchI]) hp
    apply Sem.mono hNative
    rintro k out ⟨hk, rfl⟩
    exact ⟨hk.le, i + 1, by omega, hintUnpackInv_step E s initial dest offset count i pre h (by omega)⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 12 6) (.code hintUnpackBody) hAt pre.word I 9
    hIpc hTest hGo hStop hBody count state ⟨0, by omega, inv⟩ hPc
  apply Sem.mono hNative
  rintro k out ⟨hk, i, hi, h⟩
  have he : i = count := by omega
  exact ⟨hk, he ▸ h⟩

theorem hintUnpackStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest offset count base : ℕ) (pre : HintUnpackPre E dest offset count)
    (args : HintUnpackArgs E dest offset count state)
    (hAt : At P base (hintUnpackStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 13) state (fun k out => k ≤ 12 * count + 3 ∧
      HintUnpackInv E dest offset count count state out) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  let mid := runBlock [.imm 12 0] E state
  have hRunI : (step P E)^[1] state = mid :=
    iterate_runBlock_of_at P E [.imm 12 0] state (by rwa [hPc])
      (by simp [NoBranch, Instr.NoBranchI])
  have hInv : HintUnpackInv E dest offset count 0 state mid := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, (by omega), fun _ _ => rfl⟩
    all_goals simp [mid, runBlock, execInstr, args.destination, args.offset_value, args.length, args.width, args.two, args.one]
  have hPcI : mid.pc = base + 1 := by simp [mid, runBlock, execInstr, hPc]
  obtain ⟨_, k, out, hRun, hEnd, hk, h⟩ :=
    hintUnpackLoop_sem P E mid state dest offset count (base + 1) pre hInv hLoopAt hPcI
  exact ⟨hPc, k + 1, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega, h⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintUnpackStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintUnpack20261120

section -- Def_LinearSetReconciliation327_Main_HintUnpackAction20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintUnpackSetup : List Instr :=
  [.imm 15 1, .qDet 4 6, .add 3 6 15, .qDet 5 3, .add 3 3 15, .qDet 11 3,
    .add 3 3 15, .qDet 6 3, .imm 13 2]

def hintUnpackAction : Stmt := .seq (.code hintUnpackSetup) hintUnpackStmt

structure HintUnpackTable (E : RAMEnv) (descriptor dest offset count : ℕ) : Prop where
  word : 2 < 2 ^ E.W
  table_span : descriptor + 3 < 2 ^ E.W
  dest_fit : dest < 2 ^ E.W
  offset_fit : offset < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  dest_address : E.det descriptor = dest
  offset_value : E.det (descriptor + 1) = offset
  word_width : E.det (descriptor + 2) = E.W
  length : E.det (descriptor + 3) = count

theorem hintUnpackSetup_spec (E : RAMEnv) (s : RAMState) (descriptor dest offset count : ℕ)
    (hTable : HintUnpackTable E descriptor dest offset count) (hArg : s.regs 6 = descriptor) :
    let out := runBlock hintUnpackSetup E s
    out.pc = s.pc + 9 ∧ out.mem = s.mem ∧ out.regs 14 = s.regs 14 ∧ HintUnpackArgs E dest offset count out := by
  have hSpan := hTable.table_span
  have hWord := hTable.word
  have hOne : 1 < 2 ^ E.W := by omega
  have h1 : descriptor + 1 < 2 ^ E.W := by omega
  have h2 : descriptor + 1 + 1 < 2 ^ E.W := by omega
  have h3 : descriptor + 1 + 1 + 1 < 2 ^ E.W := by omega
  have hWidth : E.W < 2 ^ E.W := Nat.lt_two_pow_self
  refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintUnpackSetup, runBlock, execInstr, hArg, hTable.dest_address, hTable.offset_value,
      hTable.word_width, hTable.length, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt hTable.dest_fit, Nat.mod_eq_of_lt hTable.offset_fit,
      Nat.mod_eq_of_lt hTable.count_fit, Nat.mod_eq_of_lt hWidth]

theorem hintUnpackAction_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (descriptor dest offset count base : ℕ) (hTable : HintUnpackTable E descriptor dest offset count)
    (hArg : state.regs 6 = descriptor) (pre : HintUnpackPre E dest offset count)
    (hAt : At P base (hintUnpackAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 22) state (fun k out => k ≤ 12 * count + 12 ∧
      out.regs 14 = state.regs 14 ∧
      (∀ i < count, out.mem (dest + i) = bitAt state.mem E.W 0 (offset + i)) ∧
      CRMemFrame dest (dest + count) state.mem out.mem) := by
  obtain ⟨hSetupAt, hUnpackAt⟩ := At.seqStmt hAt
  change At P base hintUnpackSetup at hSetupAt
  change At P (base + 9) (hintUnpackStmt.compile (base + 9)) at hUnpackAt
  have hSetup := hintUnpackSetup_spec E state descriptor dest offset count hTable hArg
  generalize hS : runBlock hintUnpackSetup E state = start at hSetup
  obtain ⟨hStart, hMem, hCtx, hArgs⟩ := hSetup
  have hRunSetup : (step P E)^[9] state = start := by
    have hh := iterate_runBlock_of_at P E hintUnpackSetup state (by rwa [hPc])
      (by simp [hintUnpackSetup, NoBranch, Instr.NoBranchI])
    rw [hS] at hh
    exact hh
  obtain ⟨_, k, out, hRun, hEnd, hTime, hOut⟩ :=
    hintUnpackStmt_sem P E start dest offset count (base + 9) pre hArgs hUnpackAt (by omega)
  refine ⟨hPc, k + 9, out, hintIterate_then (step P E) hRunSetup hRun, by omega, by omega,
    hOut.context.trans hCtx, ?_, hMem ▸ hOut.frame⟩
  intro i hi
  rw [hOut.data i hi, hMem]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintUnpackAction_sem
end -- Def_LinearSetReconciliation327_Main_HintUnpackAction20261120

section -- Def_LinearSetReconciliation327_Main_HintStageAction20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintStageSetup : List Instr :=
  [.imm 15 1, .qDet 9 6, .add 3 6 15, .qDet 5 3, .add 3 3 15, .qDet 7 3, .qDet 11 3,
    .add 3 3 15, .qDet 6 3, .imm 13 2]

def hintStageAction : Stmt := .seq (.code hintStageSetup) hintStageStmt

theorem hintStageSetup_spec (E : RAMEnv) (s : RAMState) (descriptor dest offset count : ℕ)
    (hTable : HintUnpackTable E descriptor dest offset count) (hArg : s.regs 6 = descriptor) :
    let out := runBlock hintStageSetup E s
    out.pc = s.pc + 10 ∧ out.mem = s.mem ∧ out.regs 14 = s.regs 14 ∧ HintStageArgs E E.W count offset dest out := by
  have hSpan := hTable.table_span
  have hWord := hTable.word
  have hOne : 1 < 2 ^ E.W := by omega
  have h1 : descriptor + 1 < 2 ^ E.W := by omega
  have h2 : descriptor + 1 + 1 < 2 ^ E.W := by omega
  have h3 : descriptor + 1 + 1 + 1 < 2 ^ E.W := by omega
  have hWidth : E.W < 2 ^ E.W := Nat.lt_two_pow_self
  refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintStageSetup, runBlock, execInstr, hArg, hTable.dest_address, hTable.offset_value,
      hTable.word_width, hTable.length, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt hTable.dest_fit, Nat.mod_eq_of_lt hTable.offset_fit,
      Nat.mod_eq_of_lt hTable.count_fit, Nat.mod_eq_of_lt hWidth]

theorem hintStageAction_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (descriptor dest offset count base : ℕ) (hTable : HintUnpackTable E descriptor dest offset count)
    (hArg : state.regs 6 = descriptor) (pre : HintStagePre E E.W count offset dest)
    (y : Fin count → ZMod 2)
    (hBits : ∀ i : Fin count, bitAt state.mem E.W 0 (offset + i.val) = if y i = 1 then 1 else 0)
    (hFresh : ∀ a < wordsOf E.W count, state.mem (dest + a) = 0)
    (hAt : At P base (hintStageAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 28) state (fun k out => k ≤ 17 * count + 13 ∧
      out.regs 14 = state.regs 14 ∧
      (∀ a < wordsOf E.W count, out.mem (dest + a) = packMem E.W y a) ∧
      CRMemFrame dest (dest + wordsOf E.W count) state.mem out.mem) := by
  obtain ⟨hSetupAt, hStageAt⟩ := At.seqStmt hAt
  change At P base hintStageSetup at hSetupAt
  change At P (base + 10) (hintStageStmt.compile (base + 10)) at hStageAt
  have hSetup := hintStageSetup_spec E state descriptor dest offset count hTable hArg
  generalize hS : runBlock hintStageSetup E state = mid at hSetup
  obtain ⟨hMid, hMem, hCtx, hArgs⟩ := hSetup
  have hRunSetup : (step P E)^[10] state = mid := by
    have hh := iterate_runBlock_of_at P E hintStageSetup state (by rwa [hPc])
      (by simp [hintStageSetup, NoBranch, Instr.NoBranchI])
    rw [hS] at hh
    exact hh
  obtain ⟨_, k, out, hRun, hEnd, hTime, hOut, hContext, hFrame⟩ :=
    hintStageStmt_sem P E mid E.W count offset dest (base + 10) pre y hArgs
      (by rw [hMem]; exact hBits) (by rw [hMem]; exact hFresh) hStageAt (by omega)
  exact ⟨hPc, k + 10, out, hintIterate_then (step P E) hRunSetup hRun, by omega, by omega,
    hContext.trans hCtx, hOut, hMem ▸ hFrame⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStageAction_sem
end -- Def_LinearSetReconciliation327_Main_HintStageAction20261120

section -- Def_LinearSetReconciliation327_Main_HintRowRecord20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintRowRecord (E : RAMEnv) (descriptor parent : ℕ) (fields : ℕ → ℕ) : Prop where
  word : 30 < 2 ^ E.W
  table_span : descriptor + 31 ≤ 2 ^ E.W
  memory_span : parent + 30 ≤ 2 ^ E.W
  address : E.det descriptor = parent
  data : ∀ i < 30, E.det (descriptor + 1 + i) = fields i
  fits : ∀ i < 30, fields i < 2 ^ E.W

def hintRowRecordArgs : List Instr :=
  [.imm 15 1, .qDet 4 6, .add 5 6 15, .imm 6 30]

def hintRowRecordCopy : Stmt := .seq (.code hintRowRecordArgs) hintDetCopyStmt

theorem hintRowRecordCopy_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (descriptor parent base : ℕ) (fields : ℕ → ℕ)
    (rec : HintRowRecord E descriptor parent fields) (hArg : state.regs 6 = descriptor)
    (hAt : At P base (hintRowRecordCopy.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 13) state (fun k out => k ≤ 247 ∧
      out.regs 14 = state.regs 14 ∧ out.regs 4 = parent ∧
      (∀ i < 30, out.mem (parent + i) = fields i) ∧
      CRMemFrame parent (parent + 30) state.mem out.mem) := by
  obtain ⟨hArgsAt, hCopyAt⟩ := At.seqStmt hAt
  change At P base hintRowRecordArgs at hArgsAt
  change At P (base + 4) (hintDetCopyStmt.compile (base + 4)) at hCopyAt
  let mid := runBlock hintRowRecordArgs E state
  have hWord := rec.word
  have hp : parent < 2 ^ E.W := by have := rec.memory_span; omega
  have hs : descriptor + 1 < 2 ^ E.W := by have := rec.table_span; omega
  have hOne : 1 < 2 ^ E.W := by omega
  have hArgs : HintDetCopyArgs parent (descriptor + 1) 30 mid := by
    constructor <;> simp [mid, hintRowRecordArgs, runBlock, execInstr, hArg, rec.address,
      Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hs]
  have hCopyPre : HintDetCopyPre E parent (descriptor + 1) 30 := by
    refine ⟨hOne, hWord, rec.memory_span, ?_, ?_⟩
    · have := rec.table_span; omega
    · intro i hi
      rw [rec.data i hi]
      exact rec.fits i hi
  have hRunArgs : (step P E)^[4] state = mid :=
    iterate_runBlock_of_at P E hintRowRecordArgs state (by rwa [hPc])
      (by simp [hintRowRecordArgs, NoBranch, Instr.NoBranchI])
  have hPcArgs : mid.pc = base + 4 := by simp [mid, hintRowRecordArgs, runBlock, execInstr, hPc]
  obtain ⟨_, k, out, hRun, hEnd, hCost, h⟩ :=
    hintDetCopyStmt_sem P E mid parent (descriptor + 1) 30 (base + 4) hCopyPre hArgs hCopyAt hPcArgs
  have hC : mid.regs 14 = state.regs 14 := by simp [mid, hintRowRecordArgs, runBlock, execInstr]
  exact ⟨hPc, k + 4, out, hintIterate_then (step P E) hRunArgs hRun, by omega, by omega,
    h.context.trans hC, h.args.destination, fun i hi => (h.data i hi).trans (rec.data i hi), h.frame⟩

def hintRowEnterCode : List Instr :=
  [.imm 15 1, .add 3 4 15, .load 9 3, .sub 9 9 15, .store 9 14, .imm 3 16, .add 14 4 3]

def hintRowLeaveCode : List Instr :=
  [.imm 3 15, .sub 3 14 3, .load 9 3, .imm 15 1, .sub 9 9 15, .load 14 9]

theorem hintRowEnterCode_spec (E : RAMEnv) (state : RAMState) (parent bitmap control : ℕ)
    (hWord : 16 < 2 ^ E.W) (hParent : parent + 16 < 2 ^ E.W)
    (hBitmap : bitmap < 2 ^ E.W) (hPos : 0 < bitmap)
    (hDest : state.regs 4 = parent) (hContext : state.regs 14 = control)
    (hPointer : state.mem (parent + 1) = bitmap) :
    let out := runBlock hintRowEnterCode E state
    out.pc = state.pc + 7 ∧ out.regs 14 = parent + 16 ∧
      out.mem = Function.update state.mem (bitmap - 1) control := by
  have hw : 1 < 2 ^ E.W := by omega
  have hA : parent + 1 < 2 ^ E.W := by omega
  have hSub : bitmap + 2 ^ E.W - 1 = (bitmap - 1) + 2 ^ E.W := by omega
  have hBack : bitmap - 1 < 2 ^ E.W := by omega
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [hintRowEnterCode, runBlock, execInstr, hDest, hPointer, hContext, hSub,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hParent,
      Nat.mod_eq_of_lt hBack, Nat.mod_eq_of_lt hBitmap]

theorem hintRowLeaveCode_spec (E : RAMEnv) (state : RAMState) (parent bitmap control : ℕ)
    (hWord : 16 < 2 ^ E.W) (hParent : parent + 16 < 2 ^ E.W)
    (hBitmap : bitmap < 2 ^ E.W) (hPos : 0 < bitmap) (hCtrl : control < 2 ^ E.W)
    (hContext : state.regs 14 = parent + 16)
    (hPointer : state.mem (parent + 1) = bitmap) (hSaved : state.mem (bitmap - 1) = control) :
    let out := runBlock hintRowLeaveCode E state
    out.pc = state.pc + 6 ∧ out.regs 14 = control ∧ out.mem = state.mem := by
  have hw : 1 < 2 ^ E.W := by omega
  have hw15 : 15 < 2 ^ E.W := by omega
  have hA : parent + 1 < 2 ^ E.W := by omega
  have hFirst : parent + 16 + 2 ^ E.W - 15 = (parent + 1) + 2 ^ E.W := by omega
  have hSub : bitmap + 2 ^ E.W - 1 = (bitmap - 1) + 2 ^ E.W := by omega
  have hBack : bitmap - 1 < 2 ^ E.W := by omega
  refine ⟨?_, ?_, rfl⟩ <;>
    simp [hintRowLeaveCode, runBlock, execInstr, hContext, hPointer, hSaved, hFirst, hSub,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hw15, Nat.mod_eq_of_lt hA,
      Nat.mod_eq_of_lt hBack, Nat.mod_eq_of_lt hBitmap, Nat.mod_eq_of_lt hCtrl]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowRecordCopy_sem
#print axioms LinearSetReconciliation327.Main.hintRowEnterCode_spec
#print axioms LinearSetReconciliation327.Main.hintRowLeaveCode_spec
end -- Def_LinearSetReconciliation327_Main_HintRowRecord20261120

section -- Def_LinearSetReconciliation327_Main_HintRunRow20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRunRowStmt (row : Stmt) : Stmt :=
  .seq hintRowRecordCopy (.seq (.code hintRowEnterCode) (.seq row (.code hintRowLeaveCode)))

theorem hintRunRowStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (row : Stmt) (descriptor parent bitmap control base budget : ℕ) (fields : ℕ → ℕ)
    (Q : (ℕ → ℕ) → Prop)
    (rec : HintRowRecord E descriptor parent fields) (hArg : state.regs 6 = descriptor)
    (hBitmap : fields 1 = bitmap) (hPos : 0 < bitmap) (hSeparate : bitmap ≤ parent)
    (hContext : state.regs 14 = control) (hControl : control < 2 ^ E.W)
    (hAt : At P base ((hintRunRowStmt row).compile base)) (hPc : state.pc = base)
    (hWork : ∀ st, At P (base + 20) (row.compile (base + 20)) → st.pc = base + 20 →
      st.regs 14 = parent + 16 →
      (∀ i < 30, st.mem (parent + i) = fields i) → st.mem (bitmap - 1) = control →
      (∀ addr, (addr < parent ∨ parent + 30 ≤ addr) → addr ≠ bitmap - 1 → st.mem addr = state.mem addr) →
      Sem P E (base + 20) (base + 20 + row.len) st (fun k out => k ≤ budget ∧
        out.regs 14 = parent + 16 ∧ out.mem (parent + 1) = bitmap ∧
        out.mem (bitmap - 1) = control ∧ Q out.mem)) :
    Sem P E base (base + (hintRunRowStmt row).len) state (fun k out =>
      k ≤ budget + 260 ∧ out.regs 14 = control ∧ Q out.mem) := by
  have hWord := rec.word
  have hSpan := rec.memory_span
  have hBitmapFit : bitmap < 2 ^ E.W := (hBitmap ▸ rec.fits 1 (by decide))
  have hParent : parent + 16 < 2 ^ E.W := by omega
  obtain ⟨hCopyAt, hRestAt⟩ := At.seqStmt hAt
  change At P base (hintRowRecordCopy.compile base) at hCopyAt
  change At P (base + 13) ((Stmt.seq (.code hintRowEnterCode)
    (.seq row (.code hintRowLeaveCode))).compile (base + 13)) at hRestAt
  obtain ⟨hEnterAt, hWorkLeaveAt⟩ := At.seqStmt hRestAt
  change At P (base + 13) hintRowEnterCode at hEnterAt
  change At P (base + 20) ((Stmt.seq row (.code hintRowLeaveCode)).compile (base + 20)) at hWorkLeaveAt
  obtain ⟨hWorkAt, hLeaveAt⟩ := At.seqStmt hWorkLeaveAt
  change At P (base + 20) (row.compile (base + 20)) at hWorkAt
  change At P (base + 20 + row.len) hintRowLeaveCode at hLeaveAt
  obtain ⟨_, kCopy, copied, hRunCopy, hPcCopy, hKCopy, hCtrlCopy, hParentCopy, hData, hFrame⟩ :=
    hintRowRecordCopy_sem P E state descriptor parent base fields rec hArg hCopyAt hPc
  have hEnter := hintRowEnterCode_spec E copied parent bitmap control (by omega) hParent hBitmapFit
    hPos hParentCopy (hCtrlCopy.trans hContext) ((hData 1 (by decide)).trans hBitmap)
  generalize hE : runBlock hintRowEnterCode E copied = entered at hEnter
  obtain ⟨hPcEnter, hContextEnter, hMemEnter⟩ := hEnter
  have hRunEnter : (step P E)^[7] copied = entered := by
    have hh := iterate_runBlock_of_at P E hintRowEnterCode copied (by rwa [hPcCopy])
      (by simp [hintRowEnterCode, NoBranch, Instr.NoBranchI])
    rw [hE] at hh
    exact hh
  have hDataEnter : ∀ i < 30, entered.mem (parent + i) = fields i := by
    intro i hi
    rw [hMemEnter, Function.update_of_ne (by omega : parent + i ≠ bitmap - 1)]
    exact hData i hi
  have hSaved : entered.mem (bitmap - 1) = control := by rw [hMemEnter]; simp
  have hFrameEnter (addr : ℕ) (hAway : addr < parent ∨ parent + 30 ≤ addr)
      (hOther : addr ≠ bitmap - 1) : entered.mem addr = state.mem addr := by
    rw [hMemEnter, Function.update_of_ne hOther, hFrame addr hAway]
  obtain ⟨_, kWork, done, hRunWork, hPcWork, hKWork, hContextWork, hPtrWork, hSavedWork, hResult⟩ :=
    hWork entered hWorkAt (by omega) hContextEnter hDataEnter hSaved hFrameEnter
  have hLeave := hintRowLeaveCode_spec E done parent bitmap control (by omega) hParent hBitmapFit
    hPos hControl hContextWork hPtrWork hSavedWork
  generalize hL : runBlock hintRowLeaveCode E done = out at hLeave
  obtain ⟨hPcLeave, hContextLeave, hMemLeave⟩ := hLeave
  have hRunLeave : (step P E)^[6] done = out := by
    have hh := iterate_runBlock_of_at P E hintRowLeaveCode done (by rwa [hPcWork])
      (by simp [hintRowLeaveCode, NoBranch, Instr.NoBranchI])
    rw [hL] at hh
    exact hh
  refine ⟨hPc, 6 + (kWork + (7 + kCopy)), out,
    hintIterate_then (step P E) (hintIterate_then (step P E)
      (hintIterate_then (step P E) hRunCopy hRunEnter) hRunWork) hRunLeave, ?_, by omega,
    hContextLeave, hMemLeave ▸ hResult⟩
  change out.pc = base + (13 + (7 + (row.len + 6)))
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRunRowStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintRunRow20261120

section -- Def_LinearSetReconciliation327_Main_HintWriteColumn20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintPredictionBits : List Instr :=
  [.imm 15 1, .imm 9 2, .lt 6 1 15, .lt 7 15 1, .add 6 6 7, .bxor 7 6 15,
    .mod 8 8 9, .mul 8 8 7]

theorem hintPredictionBits_spec (E : RAMEnv) (state : RAMState) (hWord : 2 < 2 ^ E.W) :
    let out := runBlock hintPredictionBits E state
    out.pc = state.pc + 8 ∧ out.mem = state.mem ∧
      out.regs 6 = hintTruth (hintRowOutput state = none) ∧
      out.regs 8 = hintTruth (hintRowOutput state = some 1) ∧
      out.regs 14 = state.regs 14 := by
  classical
  have hOne : 1 < 2 ^ E.W := by omega
  have hBit : state.regs 8 % 2 < 2 ^ E.W := (Nat.mod_lt _ (by decide)).trans hWord
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp [hintPredictionBits, runBlock, execInstr]
  · by_cases hLt : state.regs 1 < 1
    · have hNot : ¬ 1 < state.regs 1 := by omega
      have hNe : state.regs 1 ≠ 1 := by omega
      simp [hintPredictionBits, runBlock, execInstr, hLt, hNot, hNe, hintRowOutput,
        hintTruth, Nat.mod_eq_of_lt hOne]
    · by_cases hGt : 1 < state.regs 1
      · have hNe : state.regs 1 ≠ 1 := by omega
        simp [hintPredictionBits, runBlock, execInstr, hLt, hGt, hNe, hintRowOutput,
          hintTruth, Nat.mod_eq_of_lt hOne]
      · have hEq : state.regs 1 = 1 := by omega
        simp [hintPredictionBits, runBlock, execInstr, hEq, hintRowOutput, hintTruth, Nat.mod_eq_of_lt hOne]
  · by_cases hLt : state.regs 1 < 1
    · have hNot : ¬ 1 < state.regs 1 := by omega
      have hNe : state.regs 1 ≠ 1 := by omega
      simp [hintPredictionBits, runBlock, execInstr, hLt, hNot, hNe, hintRowOutput, hintTruth,
        Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hWord]
    · by_cases hGt : 1 < state.regs 1
      · have hNe : state.regs 1 ≠ 1 := by omega
        simp [hintPredictionBits, runBlock, execInstr, hLt, hGt, hNe, hintRowOutput, hintTruth,
          Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hWord]
      · have hEq : state.regs 1 = 1 := by omega
        have hCast : ((state.regs 8 : ZMod 2) = 1) ↔ state.regs 8 % 2 = 1 := by
          constructor
          · intro h
            have hOneVal : (1 : ZMod 2).val = 1 := rfl
            simpa only [ZMod.val_natCast, hOneVal] using congrArg ZMod.val h
          · intro h
            apply ZMod.val_injective
            rw [ZMod.val_natCast, h]
            rfl
        have hMod : state.regs 8 % 2 = 0 ∨ state.regs 8 % 2 = 1 := by have := Nat.mod_lt (state.regs 8) (by decide : 0 < 2); omega
        rcases hMod with h | h <;>
          simp [hintPredictionBits, runBlock, execInstr, hEq, hintRowOutput, hintTruth,
            hCast, h, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hWord]
  · simp [hintPredictionBits, runBlock, execInstr]


def hintWriteColumnTail : List Instr :=
  hintParentLoad 4 14 ++ hintParentLoad 5 15 ++ hintParentLoad 10 27 ++
    [.add 4 4 10, .add 5 5 10, .store 4 8, .store 5 6]
def hintWriteColumnCode : List Instr := hintPredictionBits ++ hintScanParent ++ hintWriteColumnTail

theorem hintWriteColumnCode_length : hintWriteColumnCode.length = 23 := rfl

theorem hintWriteColumnTail_spec (E : RAMEnv) (s : RAMState) (parent prediction abstention row bit blank : ℕ)
    (hSpan : parent + 29 < 2 ^ E.W) (h11 : s.regs 11 = parent) (h14 : s.regs 14 = parent + 16)
    (h8 : s.regs 8 = bit) (h6 : s.regs 6 = blank)
    (hReadPred : s.mem (parent + 14) = prediction) (hReadAbst : s.mem (parent + 15) = abstention)
    (hReadRow : s.mem (parent + 27) = row)
    (hPredFit : prediction + row < 2 ^ E.W) (hAbstFit : abstention + row < 2 ^ E.W) :
    let out := runBlock hintWriteColumnTail E s
    out.pc = s.pc + 13 ∧
      out.mem = Function.update (Function.update s.mem (prediction + row) bit) (abstention + row) blank ∧
      out.regs 14 = parent + 16 := by
  have h14Fit : 14 < 2 ^ E.W := by omega
  have h15Fit : 15 < 2 ^ E.W := by omega
  have h27Fit : 27 < 2 ^ E.W := by omega
  have hA14 : parent + 14 < 2 ^ E.W := by omega
  have hA15 : parent + 15 < 2 ^ E.W := by omega
  have hA27 : parent + 27 < 2 ^ E.W := by omega
  have hPFit : prediction < 2 ^ E.W := by omega
  have hAFit : abstention < 2 ^ E.W := by omega
  have hRFit : row < 2 ^ E.W := by omega
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [hintWriteColumnTail, hintParentLoad, runBlock, execInstr, h11, h14, h8, h6,
      hReadPred, hReadAbst, hReadRow,
      Nat.mod_eq_of_lt h14Fit, Nat.mod_eq_of_lt h15Fit, Nat.mod_eq_of_lt h27Fit,
      Nat.mod_eq_of_lt hA14, Nat.mod_eq_of_lt hA15, Nat.mod_eq_of_lt hA27,
      Nat.mod_eq_of_lt hPFit, Nat.mod_eq_of_lt hAFit, Nat.mod_eq_of_lt hRFit,
      Nat.mod_eq_of_lt hPredFit, Nat.mod_eq_of_lt hAbstFit]

theorem hintWriteColumnCode_spec (E : RAMEnv) (state : RAMState) (parent prediction abstention row : ℕ)
    (hSpan : parent + 29 < 2 ^ E.W) (hCtx : state.regs 14 = parent + 16)
    (hReadPred : state.mem (parent + 14) = prediction) (hReadAbst : state.mem (parent + 15) = abstention)
    (hReadRow : state.mem (parent + 27) = row)
    (hPredFit : prediction + row < 2 ^ E.W) (hAbstFit : abstention + row < 2 ^ E.W) :
    let out := runBlock hintWriteColumnCode E state
    out.pc = state.pc + 23 ∧
      out.mem = Function.update
        (Function.update state.mem (prediction + row) (hintTruth (hintRowOutput state = some 1)))
        (abstention + row) (hintTruth (hintRowOutput state = none)) ∧ out.regs 14 = parent + 16 := by
  have hBits := hintPredictionBits_spec E state (by omega)
  generalize hB : runBlock hintPredictionBits E state = sB at hBits
  obtain ⟨hPcB, hMemB, h6, h8, hCtxB⟩ := hBits
  have hP := hintScanParent_spec E sB parent (by omega) (hCtxB.trans hCtx)
  have h6P : (runBlock hintScanParent E sB).regs 6 = sB.regs 6 := by simp [hintScanParent, runBlock, execInstr]
  have h8P : (runBlock hintScanParent E sB).regs 8 = sB.regs 8 := by simp [hintScanParent, runBlock, execInstr]
  generalize hPExec : runBlock hintScanParent E sB = sP at hP h6P h8P
  obtain ⟨hPcP, hMemP, h11P, h14P⟩ := hP
  have hTail := hintWriteColumnTail_spec E sP parent prediction abstention row
    (hintTruth (hintRowOutput state = some 1)) (hintTruth (hintRowOutput state = none)) hSpan
    h11P h14P (h8P.trans h8) (h6P.trans h6)
    (by rw [hMemP, hMemB]; exact hReadPred) (by rw [hMemP, hMemB]; exact hReadAbst)
    (by rw [hMemP, hMemB]; exact hReadRow) hPredFit hAbstFit
  generalize hT : runBlock hintWriteColumnTail E sP = out at hTail
  obtain ⟨hPcT, hMemT, hCtxT⟩ := hTail
  have hRun : runBlock hintWriteColumnCode E state = out := by
    rw [hintWriteColumnCode, runBlock_append, runBlock_append, hB, hPExec, hT]
  rw [hRun]
  exact ⟨by omega, by rw [hMemT, hMemP, hMemB], hCtxT⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintWriteColumnCode_spec
end -- Def_LinearSetReconciliation327_Main_HintWriteColumn20261120


