-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintRowCopy20261120
-- name    : LinearSetReconciliation327_Main_HintRowCopy20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:49:53.099027+00:00
-- url     : https://prove2.me/theorems/492900c1-40e0-433a-a2f3-020017f30061
-- title:
--   LinearSetReconciliation327 — HintRowCopy (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintRowCopy20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowOps20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintCopyMem (original : ℕ → ℕ) (dest : ℕ) (f : ℕ → ZMod 2) (k : ℕ) : ℕ → ℕ :=
  hintAxpyMem original dest 0 f (fun _ => 0) k

theorem hintCopyMem_zero (original : ℕ → ℕ) (dest : ℕ) (f : ℕ → ZMod 2) :
    hintCopyMem original dest f 0 = original := hintAxpyMem_zero _ _ _ _ _

theorem hintCopyMem_succ (original : ℕ → ℕ) (dest : ℕ) (f : ℕ → ZMod 2) (k : ℕ) :
    Function.update (hintCopyMem original dest f k) (dest + k) (f k).val = hintCopyMem original dest f (k + 1) := by
  simpa only [hintCopyMem, zero_mul, add_zero] using hintAxpyMem_succ original dest 0 f (fun _ => 0) k

structure HintCopyParams (dest src stride count : ℕ) (state : RAMState) : Prop where
  dest_value : state.regs 4 = dest
  src_value : state.regs 5 = src
  stride_value : state.regs 7 = stride
  count_value : state.regs 6 = count
  one_value : state.regs 15 = 1

structure HintCopyInv (dest src stride count : ℕ) (f : ℕ → ZMod 2) (k : ℕ)
    (original : ℕ → ℕ) (state : RAMState) : Prop where
  params : HintCopyParams dest src stride count state
  counter : state.regs 0 = k
  memory : state.mem = hintCopyMem original dest f k

def hintCopyBody : List Instr :=
  [.mul 3 0 7, .add 3 5 3, .load 9 3, .add 3 4 0, .store 3 9, .add 0 0 15]
def hintCopyBodyResult (state : RAMState) (dest k : ℕ) (f : ℕ → ZMod 2) : RAMState :=
  { state with
    pc := state.pc + 6
    mem := Function.update state.mem (dest + k) (f k).val
    regs := Function.update (Function.update (Function.update state.regs 3 (dest + k)) 9 (f k).val) 0 (k + 1) }

theorem hintCopyBody_spec (E : RAMEnv) (state : RAMState) (dest src stride count k : ℕ) (f : ℕ → ZMod 2)
    (hParams : HintCopyParams dest src stride count state) (hCounter : state.regs 0 = k)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W) (hk : k < count)
    (hDest : dest + k < 2 ^ E.W) (hSrc : src + k * stride < 2 ^ E.W)
    (hF : state.mem (src + k * stride) = (f k).val) :
    runBlock hintCopyBody E state = hintCopyBodyResult state dest k f := by
  have hMul : k * stride < 2 ^ E.W := by omega
  have hNext : k + 1 < 2 ^ E.W := by omega
  have hBitBound := (ZMod.val_lt (f k)).trans_le hWord
  apply crState_ext
  · simp [hintCopyBody, hintCopyBodyResult, runBlock, execInstr, Nat.add_assoc]
  · funext r
    simp [hintCopyBody, hintCopyBodyResult, runBlock, execInstr, hParams.dest_value,
      hParams.src_value, hParams.stride_value, hParams.one_value, hCounter,
      Nat.mod_eq_of_lt hMul, Nat.mod_eq_of_lt hSrc, Nat.mod_eq_of_lt hDest,
      hF, Nat.mod_eq_of_lt hBitBound, Nat.mod_eq_of_lt hNext]
    by_cases h0 : r = 0 <;> by_cases h3 : r = 3 <;> by_cases h9 : r = 9 <;> simp [h0, h3, h9]
  · simp [hintCopyBody, hintCopyBodyResult, runBlock, execInstr, hParams.dest_value,
      hParams.src_value, hParams.stride_value, hCounter, Nat.mod_eq_of_lt hMul,
      Nat.mod_eq_of_lt hSrc, Nat.mod_eq_of_lt hDest, hF, Nat.mod_eq_of_lt hBitBound]

theorem hintCopyBody_transition (E : RAMEnv) (state : RAMState) (dest src stride count k : ℕ)
    (f : ℕ → ZMod 2) (original : ℕ → ℕ) (hInv : HintCopyInv dest src stride count f k original state)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W) (hk : k < count)
    (hDest : dest + k < 2 ^ E.W) (hSrc : src + k * stride < 2 ^ E.W)
    (hSourceOutside : src + k * stride < dest ∨ dest + count ≤ src + k * stride)
    (hF : original (src + k * stride) = (f k).val) :
    let out := runBlock hintCopyBody E state
    out.pc = state.pc + 6 ∧ HintCopyInv dest src stride count f (k + 1) original out ∧
      (∀ r, r ≠ 0 → r ≠ 2 → r ≠ 3 → r ≠ 9 → out.regs r = state.regs r) := by
  have hOutside : ¬ (dest ≤ src + k * stride ∧ src + k * stride < dest + k) := by
    rcases hSourceOutside with hBefore | hAfter <;> omega
  have hRead : state.mem (src + k * stride) = (f k).val := by
    rw [hInv.memory]
    simpa only [hintCopyMem, hintAxpyMem, if_neg hOutside] using hF
  have hSpec := hintCopyBody_spec E state dest src stride count k f hInv.params hInv.counter hWord hCount hk hDest hSrc hRead
  dsimp only
  rw [hSpec]
  refine ⟨rfl, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hintCopyBodyResult] using hInv.params.dest_value
    · simpa [hintCopyBodyResult] using hInv.params.src_value
    · simpa [hintCopyBodyResult] using hInv.params.stride_value
    · simpa [hintCopyBodyResult] using hInv.params.count_value
    · simpa [hintCopyBodyResult] using hInv.params.one_value
  · simp [hintCopyBodyResult]
  · change Function.update state.mem (dest + k) (f k).val = _
    rw [hInv.memory, hintCopyMem_succ]
  · intro r h0 h2 h3 h9
    simp only [hintCopyBodyResult, Function.update_of_ne h0, Function.update_of_ne h9, Function.update_of_ne h3]

def hintCopyLoop (base done : ℕ) : List Instr :=
  [.lt 2 0 6, .jz 2 done] ++ (hintCopyBody ++ [.jmp base])
theorem hintCopyBody_length : hintCopyBody.length = 6 := rfl

theorem hintCopyInv_pc {dest src stride count k pc : ℕ} {f : ℕ → ZMod 2}
    {original : ℕ → ℕ} {state : RAMState} (h : HintCopyInv dest src stride count f k original state) :
    HintCopyInv dest src stride count f k original {state with pc := pc} :=
  ⟨⟨h.params.dest_value, h.params.src_value, h.params.stride_value, h.params.count_value,
    h.params.one_value⟩, h.counter, h.memory⟩

theorem hintCopyInv_reg2 {dest src stride count k pc bit : ℕ} {f : ℕ → ZMod 2}
    {original : ℕ → ℕ} {state : RAMState} (h : HintCopyInv dest src stride count f k original state) :
    HintCopyInv dest src stride count f k original {state with pc := pc, regs := Function.update state.regs 2 bit} := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, h.memory⟩
  · simpa using h.params.dest_value
  · simpa using h.params.src_value
  · simpa using h.params.stride_value
  · simpa using h.params.count_value
  · simpa using h.params.one_value
  · simpa using h.counter

theorem hintCopy_guard (P : Program) (E : RAMEnv) (p : RAMState) (base done k M : ℕ)
    (hAt : At P base (hintCopyLoop base done)) (hPc : p.pc = base)
    (hCounter : p.regs 0 = k) (hRows : p.regs 6 = M) (hW : 0 < E.W) :
    (step P E)^[2] p =
      {p with pc := if k < M then base + 2 else done, regs := Function.update p.regs 2 (if k < M then 1 else 0)} := by
  have hF0 : P[p.pc]? = some (.lt 2 0 6) := by
    have h := hAt 0 (by simp [hintCopyLoop, hintCopyBody_length])
    simpa only [hintCopyLoop, List.cons_append, List.nil_append, List.getElem?_cons_zero, Nat.add_zero, hPc] using h
  have hF1 : P[p.pc + 1]? = some (.jz 2 done) := by
    have h := hAt 1 (by simp [hintCopyLoop, hintCopyBody_length])
    simpa only [hintCopyLoop, List.cons_append, List.nil_append, List.getElem?_cons_succ,
      List.getElem?_cons_zero, hPc] using h
  have hOne : 1 < 2 ^ E.W := by
    have hPow : 2 ^ 1 ≤ 2 ^ E.W := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact (by decide : 1 < 2 ^ 1).trans_le hPow
  have hMask : (if k < M then 1 else 0) % 2 ^ E.W = if k < M then 1 else 0 := by
    split_ifs <;> simp [Nat.mod_eq_of_lt hOne]
  have hFirst : step P E p =
      {p with pc := p.pc + 1, regs := Function.update p.regs 2 (if k < M then 1 else 0)} := by
    rw [crStep_fetch P E p _ hF0]
    simp only [execInstr, hCounter, hRows, hMask]
  change step P E (step P E p) = _
  rw [hFirst, crStep_fetch P E {p with pc := p.pc + 1, regs := Function.update p.regs 2 (if k < M then 1 else 0)} _ hF1]
  by_cases hk : k < M <;> simp [execInstr, hk, hPc, Nat.add_assoc]
theorem hintCopy_iteration (P : Program) (E : RAMEnv) (state : RAMState)
    (dest src stride count k base done : ℕ) (f : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hDest : ∀ j < count, dest + j < 2 ^ E.W) (hSrc : ∀ j < count, src + j * stride < 2 ^ E.W)
    (hSourceOutside : ∀ j < count, src + j * stride < dest ∨ dest + count ≤ src + j * stride)
    (hF : ∀ j < count, original (src + j * stride) = (f j).val)
    (hAt : At P base (hintCopyLoop base done)) (hPc : state.pc = base)
    (hInv : HintCopyInv dest src stride count f k original state) (hk : k < count) :
    ∃ out : RAMState, (step P E)^[9] state = out ∧ out.pc = base ∧
      HintCopyInv dest src stride count f (k + 1) original out ∧
      (∀ r, r ≠ 0 → r ≠ 2 → r ≠ 3 → r ≠ 9 → out.regs r = state.regs r) := by
  let q := {state with pc := base + 2, regs := Function.update state.regs 2 1}
  have hGuard : (step P E)^[2] state = q := by
    have h := hintCopy_guard P E state base done k count hAt hPc hInv.counter hInv.params.count_value
      (by apply Nat.pos_of_ne_zero; intro hz; simpa [hz] using hWord)
    simpa only [if_pos hk] using h
  have hQ : HintCopyInv dest src stride count f k original q := hintCopyInv_reg2 hInv
  have hTail := crAt_suffix P base [.lt 2 0 6, .jz 2 done] (hintCopyBody ++ [.jmp base]) hAt
  have hTailQ : At P q.pc (hintCopyBody ++ [.jmp base]) := by simpa using hTail
  have hBodyAt := crAt_prefix P q.pc hintCopyBody [.jmp base] hTailQ
  have hEnd := crAt_suffix P q.pc hintCopyBody [.jmp base] hTailQ
  have hJump : P[q.pc + hintCopyBody.length]? = some (.jmp base) := by
    simpa only [Nat.add_zero, List.getElem?_cons_zero] using hEnd 0 (by simp)
  have hNo : NoBranch hintCopyBody := by simp [hintCopyBody, NoBranch, Instr.NoBranchI]
  have hExec := crExecute_body_jump P E q hintCopyBody base hNo hBodyAt hJump
  generalize hu : runBlock hintCopyBody E q = u at hExec
  have hBody := hintCopyBody_transition E q dest src stride count k f original hQ hWord hCount hk
    (hDest k hk) (hSrc k hk) (hSourceOutside k hk) (hF k hk)
  rw [hu] at hBody
  obtain ⟨_, hInvU, hFrame⟩ := hBody
  let out := {u with pc := base}
  refine ⟨out, ?_, rfl, hintCopyInv_pc hInvU, ?_⟩
  · rw [show 9 = 7 + 2 by omega, Function.iterate_add_apply, hGuard]
    simpa only [hintCopyBody_length] using hExec
  · intro r h0 h2 h3 h9
    exact (hFrame r h0 h2 h3 h9).trans (by simp only [q, Function.update_of_ne h2])

theorem hintCopy_remaining (P : Program) (E : RAMEnv)
    (dest src stride count base done : ℕ) (f : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hDest : ∀ j < count, dest + j < 2 ^ E.W) (hSrc : ∀ j < count, src + j * stride < 2 ^ E.W)
    (hSourceOutside : ∀ j < count, src + j * stride < dest ∨ dest + count ≤ src + j * stride)
    (hF : ∀ j < count, original (src + j * stride) = (f j).val)
    (hAt : At P base (hintCopyLoop base done)) :
    ∀ (left k : ℕ) (state : RAMState), k + left = count → state.pc = base →
      HintCopyInv dest src stride count f k original state →
      ∃ out : RAMState, (step P E)^[9 * left + 2] state = out ∧ out.pc = done ∧
        HintCopyInv dest src stride count f count original out ∧
        (∀ r, r ≠ 0 → r ≠ 2 → r ≠ 3 → r ≠ 9 → out.regs r = state.regs r) := by
  intro left
  induction left with
  | zero =>
      intro k state hK hPc hInv
      have hk : k = count := by omega
      let out := {state with pc := done, regs := Function.update state.regs 2 0}
      have hGuard := hintCopy_guard P E state base done k count hAt hPc hInv.counter hInv.params.count_value
        (by apply Nat.pos_of_ne_zero; intro hz; simpa [hz] using hWord)
      have hRun : (step P E)^[2] state = out := by simpa only [hk, lt_self_iff_false, if_false] using hGuard
      refine ⟨out, hRun, rfl, ?_, ?_⟩
      · rw [hk] at hInv
        exact hintCopyInv_reg2 hInv
      · intro r _ h2 _ _
        exact Function.update_of_ne h2 _ _
  | succ left ih =>
      intro k state hK hPc hInv
      have hk : k < count := by omega
      obtain ⟨mid, hRun, hMidPc, hMidInv, hFrame⟩ :=
        hintCopy_iteration P E state dest src stride count k base done f original hWord hCount hDest hSrc
          hSourceOutside hF hAt hPc hInv hk
      obtain ⟨out, hRun', hOutPc, hOutInv, hFrame'⟩ := ih (k + 1) mid (by omega) hMidPc hMidInv
      refine ⟨out, ?_, hOutPc, hOutInv, ?_⟩
      · rw [show 9 * (left + 1) + 2 = (9 * left + 2) + 9 by omega, Function.iterate_add_apply, hRun, hRun']
      · intro r h0 h2 h3 h9
        exact (hFrame' r h0 h2 h3 h9).trans (hFrame r h0 h2 h3 h9)

def hintCopyStmt : Stmt := .seq (.code [.imm 0 0]) (.loop (.lt 2 0 6) (.code hintCopyBody))
theorem hintCopyStmt_len : hintCopyStmt.len = 10 := rfl

theorem hintCopyLoop_compile (base : ℕ) :
    (Stmt.loop (.lt 2 0 6) (.code hintCopyBody)).compile base = hintCopyLoop base (base + 9) := rfl

theorem hintCopyStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest src stride count base : ℕ) (f : ℕ → ZMod 2)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hDest : ∀ j < count, dest + j < 2 ^ E.W) (hSrc : ∀ j < count, src + j * stride < 2 ^ E.W)
    (hSourceOutside : ∀ j < count, src + j * stride < dest ∨ dest + count ≤ src + j * stride)
    (hF : ∀ j < count, state.mem (src + j * stride) = (f j).val)
    (hAt : At P base (hintCopyStmt.compile base)) (hPc : state.pc = base)
    (hParams : HintCopyParams dest src stride count state) :
    Sem P E base (base + 10) state (fun k out => k = 9 * count + 3 ∧
      out.regs 0 = count ∧ out.mem = hintCopyMem state.mem dest f count ∧
      HintCopyParams dest src stride count out ∧
      (∀ addr, (addr < dest ∨ dest + count ≤ addr) → out.mem addr = state.mem addr) ∧
      (∀ r, r ≠ 0 → r ≠ 2 → r ≠ 3 → r ≠ 9 → out.regs r = state.regs r)) := by
  obtain ⟨hAtInit, hAtLoop⟩ := At.seqStmt hAt
  have hLoop : At P (base + 1) (hintCopyLoop (base + 1) (base + 10)) := by
    simpa only [Stmt.len, List.length_cons, List.length_nil, hintCopyLoop_compile, Nat.add_assoc] using hAtLoop
  let q := {state with pc := state.pc + 1, regs := Function.update state.regs 0 0}
  have hFetch : P[state.pc]? = some (.imm 0 0) := by
    have hh := hAtInit 0 (by simp [Stmt.compile])
    simpa only [Stmt.compile, List.getElem?_cons_zero, Nat.add_zero, hPc] using hh
  have hRunInit : step P E state = q := by
    rw [crStep_fetch P E state _ hFetch]
    simp only [q, execInstr, Nat.zero_mod]
  have hQ : HintCopyInv dest src stride count f 0 state.mem q := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simpa [q] using hParams.dest_value
    · simpa [q] using hParams.src_value
    · simpa [q] using hParams.stride_value
    · simpa [q] using hParams.count_value
    · simpa [q] using hParams.one_value
    · simp [q]
    · exact (hintCopyMem_zero state.mem dest f).symm
  have hQPc : q.pc = base + 1 := by change state.pc + 1 = _; rw [hPc]
  obtain ⟨out, hRunLoop, hOutPc, hOutInv, hFrame⟩ := hintCopy_remaining P E
    dest src stride count (base + 1) (base + 10) f state.mem hWord hCount hDest hSrc hSourceOutside hF hLoop
    count 0 q (by omega) hQPc hQ
  refine ⟨hPc, 9 * count + 3, out, ?_, hOutPc, rfl, hOutInv.counter,
    hOutInv.memory, hOutInv.params, ?_, ?_⟩
  · rw [show 9 * count + 3 = (9 * count + 2) + 1 by omega, Function.iterate_add_apply]
    change (step P E)^[9 * count + 2] (step P E state) = out
    rw [hRunInit, hRunLoop]
  · intro addr hOutside
    rw [hOutInv.memory]
    exact if_neg (by rcases hOutside with hBefore | hAfter <;> omega)
  · intro r h0 h2 h3 h9
    exact (hFrame r h0 h2 h3 h9).trans (by simp only [q, Function.update_of_ne h0])

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCopyStmt_sem


