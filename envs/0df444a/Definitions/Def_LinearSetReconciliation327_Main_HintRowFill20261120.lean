-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintRowFill20261120
-- name    : LinearSetReconciliation327_Main_HintRowFill20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:38:22.963879+00:00
-- url     : https://prove2.me/theorems/c189f434-f309-47df-9d26-14cf9efd47df
-- title:
--   LinearSetReconciliation327 — HintRowFill (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintRowFill20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowOps20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFillPositions (dest stride count : ℕ) : Finset ℕ :=
  (Finset.range count).image (fun i => dest + i * stride)

def hintFillMem (original : ℕ → ℕ) (dest stride count : ℕ) (value : ZMod 2) (addr : ℕ) : ℕ :=
  if addr ∈ hintFillPositions dest stride count then value.val else original addr

theorem hintFillPositions_succ (dest stride k : ℕ) :
    hintFillPositions dest stride (k + 1) = insert (dest + k * stride) (hintFillPositions dest stride k) := by
  ext addr
  simp only [hintFillPositions, Finset.mem_image, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi, hPos⟩
    by_cases hEq : i = k
    · exact Or.inl (by simpa only [hEq] using hPos.symm)
    · exact Or.inr ⟨i, by omega, hPos⟩
  · rintro (hEq | ⟨i, hi, hPos⟩)
    · exact ⟨k, by omega, hEq.symm⟩
    · exact ⟨i, by omega, hPos⟩

theorem hintFillMem_zero (original : ℕ → ℕ) (dest stride : ℕ) (value : ZMod 2) :
    hintFillMem original dest stride 0 value = original := by
  funext addr
  simp [hintFillMem, hintFillPositions]

theorem hintFillMem_succ (original : ℕ → ℕ) (dest stride k : ℕ) (value : ZMod 2) :
    Function.update (hintFillMem original dest stride k value) (dest + k * stride) value.val =
      hintFillMem original dest stride (k + 1) value := by
  funext addr
  by_cases hEq : addr = dest + k * stride
  · subst addr
    simp only [Function.update_self, hintFillMem, hintFillPositions_succ, Finset.mem_insert_self, if_true]
  · rw [Function.update_of_ne hEq]
    simp only [hintFillMem, hintFillPositions_succ, Finset.mem_insert, hEq, false_or]

structure HintFillParams (dest stride count : ℕ) (value : ZMod 2) (state : RAMState) : Prop where
  dest_value : state.regs 4 = dest
  stride_value : state.regs 7 = stride
  count_value : state.regs 6 = count
  fill_value : state.regs 8 = value.val
  one_value : state.regs 15 = 1

structure HintFillInv (dest stride count : ℕ) (value : ZMod 2) (k : ℕ)
    (original : ℕ → ℕ) (state : RAMState) : Prop where
  params : HintFillParams dest stride count value state
  counter : state.regs 0 = k
  memory : state.mem = hintFillMem original dest stride k value

def hintFillBody : List Instr := [.mul 3 0 7, .add 3 4 3, .store 3 8, .add 0 0 15]
def hintFillBodyResult (state : RAMState) (dest stride k : ℕ) (value : ZMod 2) : RAMState :=
  { state with
    pc := state.pc + 4
    mem := Function.update state.mem (dest + k * stride) value.val
    regs := Function.update (Function.update state.regs 3 (dest + k * stride)) 0 (k + 1) }

theorem hintFillBody_spec (E : RAMEnv) (state : RAMState) (dest stride count k : ℕ) (value : ZMod 2)
    (hParams : HintFillParams dest stride count value state) (hCounter : state.regs 0 = k)
    (hCount : count < 2 ^ E.W) (hk : k < count) (hAddr : dest + k * stride < 2 ^ E.W) :
    runBlock hintFillBody E state = hintFillBodyResult state dest stride k value := by
  have hMul : k * stride < 2 ^ E.W := by omega
  have hNext : k + 1 < 2 ^ E.W := by omega
  apply crState_ext
  · simp [hintFillBody, hintFillBodyResult, runBlock, execInstr, Nat.add_assoc]
  · funext r
    simp [hintFillBody, hintFillBodyResult, runBlock, execInstr, hParams.dest_value,
      hParams.stride_value, hParams.one_value, hCounter, Nat.mod_eq_of_lt hMul,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hNext]
  · simp [hintFillBody, hintFillBodyResult, runBlock, execInstr, hParams.dest_value,
      hParams.stride_value, hParams.fill_value, hCounter, Nat.mod_eq_of_lt hMul, Nat.mod_eq_of_lt hAddr]

theorem hintFillBody_transition (E : RAMEnv) (state : RAMState) (dest stride count k : ℕ)
    (value : ZMod 2) (original : ℕ → ℕ) (hInv : HintFillInv dest stride count value k original state)
    (hCount : count < 2 ^ E.W) (hk : k < count) (hAddr : dest + k * stride < 2 ^ E.W) :
    let out := runBlock hintFillBody E state
    out.pc = state.pc + 4 ∧ HintFillInv dest stride count value (k + 1) original out ∧
      (∀ r, r ≠ 0 → r ≠ 2 → r ≠ 3 → out.regs r = state.regs r) := by
  have hSpec := hintFillBody_spec E state dest stride count k value hInv.params hInv.counter hCount hk hAddr
  dsimp only
  rw [hSpec]
  refine ⟨rfl, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hintFillBodyResult] using hInv.params.dest_value
    · simpa [hintFillBodyResult] using hInv.params.stride_value
    · simpa [hintFillBodyResult] using hInv.params.count_value
    · simpa [hintFillBodyResult] using hInv.params.fill_value
    · simpa [hintFillBodyResult] using hInv.params.one_value
  · simp [hintFillBodyResult]
  · change Function.update state.mem (dest + k * stride) value.val = _
    rw [hInv.memory, hintFillMem_succ]
  · intro r h0 h2 h3
    simp only [hintFillBodyResult, Function.update_of_ne h0, Function.update_of_ne h3]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintFillLoop (base done : ℕ) : List Instr :=
  [.lt 2 0 6, .jz 2 done] ++ (hintFillBody ++ [.jmp base])
theorem hintFillBody_length : hintFillBody.length = 4 := rfl

theorem hintFillInv_pc {dest stride count k pc : ℕ} {value : ZMod 2}
    {original : ℕ → ℕ} {state : RAMState} (h : HintFillInv dest stride count value k original state) :
    HintFillInv dest stride count value k original {state with pc := pc} :=
  ⟨⟨h.params.dest_value, h.params.stride_value, h.params.count_value, h.params.fill_value,
    h.params.one_value⟩, h.counter, h.memory⟩

theorem hintFillInv_reg2 {dest stride count k pc bit : ℕ} {value : ZMod 2}
    {original : ℕ → ℕ} {state : RAMState} (h : HintFillInv dest stride count value k original state) :
    HintFillInv dest stride count value k original {state with pc := pc, regs := Function.update state.regs 2 bit} := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, h.memory⟩
  · simpa using h.params.dest_value
  · simpa using h.params.stride_value
  · simpa using h.params.count_value
  · simpa using h.params.fill_value
  · simpa using h.params.one_value
  · simpa using h.counter

theorem hintFill_guard (P : Program) (E : RAMEnv) (p : RAMState) (base done k M : ℕ)
    (hAt : At P base (hintFillLoop base done)) (hPc : p.pc = base)
    (hCounter : p.regs 0 = k) (hRows : p.regs 6 = M) (hW : 0 < E.W) :
    (step P E)^[2] p =
      {p with pc := if k < M then base + 2 else done, regs := Function.update p.regs 2 (if k < M then 1 else 0)} := by
  have hF0 : P[p.pc]? = some (.lt 2 0 6) := by
    have h := hAt 0 (by simp [hintFillLoop, hintFillBody_length])
    simpa only [hintFillLoop, List.cons_append, List.nil_append, List.getElem?_cons_zero, Nat.add_zero, hPc] using h
  have hF1 : P[p.pc + 1]? = some (.jz 2 done) := by
    have h := hAt 1 (by simp [hintFillLoop, hintFillBody_length])
    simpa only [hintFillLoop, List.cons_append, List.nil_append, List.getElem?_cons_succ,
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
theorem hintFill_iteration (P : Program) (E : RAMEnv) (state : RAMState)
    (dest stride count k base done : ℕ) (value : ZMod 2) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hAddr : ∀ j < count, dest + j * stride < 2 ^ E.W)
    (hAt : At P base (hintFillLoop base done)) (hPc : state.pc = base)
    (hInv : HintFillInv dest stride count value k original state) (hk : k < count) :
    ∃ out : RAMState, (step P E)^[7] state = out ∧ out.pc = base ∧
      HintFillInv dest stride count value (k + 1) original out ∧
      (∀ r, r ≠ 0 → r ≠ 2 → r ≠ 3 → out.regs r = state.regs r) := by
  let q := {state with pc := base + 2, regs := Function.update state.regs 2 1}
  have hGuard : (step P E)^[2] state = q := by
    have h := hintFill_guard P E state base done k count hAt hPc hInv.counter hInv.params.count_value
      (by apply Nat.pos_of_ne_zero; intro hz; simpa [hz] using hWord)
    simpa only [if_pos hk] using h
  have hQ : HintFillInv dest stride count value k original q := hintFillInv_reg2 hInv
  have hTail := crAt_suffix P base [.lt 2 0 6, .jz 2 done] (hintFillBody ++ [.jmp base]) hAt
  have hTailQ : At P q.pc (hintFillBody ++ [.jmp base]) := by simpa using hTail
  have hBodyAt := crAt_prefix P q.pc hintFillBody [.jmp base] hTailQ
  have hEnd := crAt_suffix P q.pc hintFillBody [.jmp base] hTailQ
  have hJump : P[q.pc + hintFillBody.length]? = some (.jmp base) := by
    simpa only [Nat.add_zero, List.getElem?_cons_zero] using hEnd 0 (by simp)
  have hNo : NoBranch hintFillBody := by simp [hintFillBody, NoBranch, Instr.NoBranchI]
  have hExec := crExecute_body_jump P E q hintFillBody base hNo hBodyAt hJump
  generalize hu : runBlock hintFillBody E q = u at hExec
  have hBody := hintFillBody_transition E q dest stride count k value original hQ hCount hk (hAddr k hk)
  rw [hu] at hBody
  obtain ⟨_, hInvU, hFrame⟩ := hBody
  let out := {u with pc := base}
  refine ⟨out, ?_, rfl, hintFillInv_pc hInvU, ?_⟩
  · rw [show 7 = 5 + 2 by omega, Function.iterate_add_apply, hGuard]
    simpa only [hintFillBody_length] using hExec
  · intro r h0 h2 h3
    exact (hFrame r h0 h2 h3).trans (by simp only [q, Function.update_of_ne h2])

theorem hintFill_remaining (P : Program) (E : RAMEnv)
    (dest stride count base done : ℕ) (value : ZMod 2) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hAddr : ∀ j < count, dest + j * stride < 2 ^ E.W)
    (hAt : At P base (hintFillLoop base done)) :
    ∀ (left k : ℕ) (state : RAMState), k + left = count → state.pc = base →
      HintFillInv dest stride count value k original state →
      ∃ out : RAMState, (step P E)^[7 * left + 2] state = out ∧ out.pc = done ∧
        HintFillInv dest stride count value count original out ∧
        (∀ r, r ≠ 0 → r ≠ 2 → r ≠ 3 → out.regs r = state.regs r) := by
  intro left
  induction left with
  | zero =>
      intro k state hK hPc hInv
      have hk : k = count := by omega
      let out := {state with pc := done, regs := Function.update state.regs 2 0}
      have hGuard := hintFill_guard P E state base done k count hAt hPc hInv.counter hInv.params.count_value
        (by apply Nat.pos_of_ne_zero; intro hz; simpa [hz] using hWord)
      have hRun : (step P E)^[2] state = out := by simpa only [hk, lt_self_iff_false, if_false] using hGuard
      refine ⟨out, hRun, rfl, ?_, ?_⟩
      · rw [hk] at hInv
        exact hintFillInv_reg2 hInv
      · intro r _ h2 _
        exact Function.update_of_ne h2 _ _
  | succ left ih =>
      intro k state hK hPc hInv
      have hk : k < count := by omega
      obtain ⟨mid, hRun, hMidPc, hMidInv, hFrame⟩ :=
        hintFill_iteration P E state dest stride count k base done value original hWord hCount hAddr hAt hPc hInv hk
      obtain ⟨out, hRun', hOutPc, hOutInv, hFrame'⟩ := ih (k + 1) mid (by omega) hMidPc hMidInv
      refine ⟨out, ?_, hOutPc, hOutInv, ?_⟩
      · rw [show 7 * (left + 1) + 2 = (7 * left + 2) + 7 by omega, Function.iterate_add_apply, hRun, hRun']
      · intro r h0 h2 h3
        exact (hFrame' r h0 h2 h3).trans (hFrame r h0 h2 h3)

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintFillStmt : Stmt := .seq (.code [.imm 0 0]) (.loop (.lt 2 0 6) (.code hintFillBody))
theorem hintFillStmt_len : hintFillStmt.len = 8 := rfl

theorem hintFillLoop_compile (base : ℕ) :
    (Stmt.loop (.lt 2 0 6) (.code hintFillBody)).compile base = hintFillLoop base (base + 7) := rfl

theorem hintFillStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest stride count base : ℕ) (value : ZMod 2)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hAddr : ∀ j < count, dest + j * stride < 2 ^ E.W)
    (hAt : At P base (hintFillStmt.compile base)) (hPc : state.pc = base)
    (hParams : HintFillParams dest stride count value state) :
    Sem P E base (base + 8) state (fun k out => k = 7 * count + 3 ∧
      out.regs 0 = count ∧ out.mem = hintFillMem state.mem dest stride count value ∧
      HintFillParams dest stride count value out ∧
      (∀ addr, addr ∉ hintFillPositions dest stride count → out.mem addr = state.mem addr) ∧
      (∀ r, r ≠ 0 → r ≠ 2 → r ≠ 3 → out.regs r = state.regs r)) := by
  obtain ⟨hAtInit, hAtLoop⟩ := At.seqStmt hAt
  have hLoop : At P (base + 1) (hintFillLoop (base + 1) (base + 8)) := by
    simpa only [Stmt.len, List.length_cons, List.length_nil, hintFillLoop_compile, Nat.add_assoc] using hAtLoop
  let q := {state with pc := state.pc + 1, regs := Function.update state.regs 0 0}
  have hFetch : P[state.pc]? = some (.imm 0 0) := by
    have hh := hAtInit 0 (by simp [Stmt.compile])
    simpa only [Stmt.compile, List.getElem?_cons_zero, Nat.add_zero, hPc] using hh
  have hRunInit : step P E state = q := by
    rw [crStep_fetch P E state _ hFetch]
    simp only [q, execInstr, Nat.zero_mod]
  have hQ : HintFillInv dest stride count value 0 state.mem q := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simpa [q] using hParams.dest_value
    · simpa [q] using hParams.stride_value
    · simpa [q] using hParams.count_value
    · simpa [q] using hParams.fill_value
    · simpa [q] using hParams.one_value
    · simp [q]
    · exact (hintFillMem_zero state.mem dest stride value).symm
  have hQPc : q.pc = base + 1 := by change state.pc + 1 = _; rw [hPc]
  obtain ⟨out, hRunLoop, hOutPc, hOutInv, hFrame⟩ := hintFill_remaining P E
    dest stride count (base + 1) (base + 8) value state.mem hWord hCount hAddr hLoop
    count 0 q (by omega) hQPc hQ
  refine ⟨hPc, 7 * count + 3, out, ?_, hOutPc, rfl, hOutInv.counter,
    hOutInv.memory, hOutInv.params, ?_, ?_⟩
  · rw [show 7 * count + 3 = (7 * count + 2) + 1 by omega, Function.iterate_add_apply]
    change (step P E)^[7 * count + 2] (step P E state) = out
    rw [hRunInit, hRunLoop]
  · intro addr hOutside
    rw [hOutInv.memory]
    exact if_neg hOutside
  · intro r h0 h2 h3
    exact (hFrame r h0 h2 h3).trans (by simp only [q, Function.update_of_ne h0])

theorem hintFillPositions_contiguous (dest count addr : ℕ) :
    addr ∈ hintFillPositions dest 1 count ↔ dest ≤ addr ∧ addr < dest + count := by
  simp only [hintFillPositions, Finset.mem_image, Finset.mem_range, Nat.mul_one]
  constructor
  · rintro ⟨i, hi, hEq⟩
    omega
  · rintro ⟨hLo, hHi⟩
    exact ⟨addr - dest, by omega, by omega⟩

theorem hintFillPositions_diagonal (dest n s t : ℕ) (hs : s < n) (ht : t < n) :
    dest + s * n + t ∈ hintFillPositions dest (n + 1) n ↔ s = t := by
  simp only [hintFillPositions, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, hEq⟩
    have hBase : i * n + i = s * n + t := by
      have hEq' : dest + (i * n + i) = dest + (s * n + t) := by
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hEq
      exact Nat.add_left_cancel hEq'
    have hn : 0 < n := by omega
    have hMod := congrArg (fun z => z % n) hBase
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod,
      Nat.zero_add, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt ht] at hMod
    have hSame : i = s := by
      by_contra hNe
      rcases lt_or_gt_of_ne hNe with hLess | hGreater
      · have hMul := Nat.mul_lt_mul_of_pos_right hLess hn
        omega
      · have hMul := Nat.mul_lt_mul_of_pos_right hGreater hn
        omega
    omega
  · intro hEq
    refine ⟨s, hs, ?_⟩
    rw [← hEq]
    ring

theorem hintFill_identity_cells (original : ℕ → ℕ) (dest n s t : ℕ) (hs : s < n) (ht : t < n) :
    hintFillMem (hintFillMem original dest 1 (n * n) 0) dest (n + 1) n 1 (dest + s * n + t) =
      if s = t then 1 else 0 := by
  have hBound : s * n + t < n * n := by
    have hMul := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hs)
    rw [Nat.succ_mul] at hMul
    omega
  have hClear : dest + s * n + t ∈ hintFillPositions dest 1 (n * n) :=
    (hintFillPositions_contiguous _ _ _).mpr (by omega)
  have hOne : (1 : ZMod 2).val = 1 := by decide
  simp [hintFillMem, hintFillPositions_diagonal dest n s t hs ht, hClear, hOne]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFillStmt_sem
#print axioms LinearSetReconciliation327.Main.hintFill_identity_cells


