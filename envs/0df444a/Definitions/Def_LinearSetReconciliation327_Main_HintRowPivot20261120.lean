-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintRowPivot20261120
-- name    : LinearSetReconciliation327_Main_HintRowPivot20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T10:07:00.001612+00:00
-- url     : https://prove2.me/theorems/c988cebf-67e9-4967-8cc8-ad8f3b206e29
-- title:
--   LinearSetReconciliation327 — HintRowPivot (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintRowPivot20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowOps20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintPivotLast (f : ℕ → ZMod 2) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if f k = 1 then k + 1 else hintPivotLast f k

theorem hintPivotLast_le (f : ℕ → ZMod 2) (k : ℕ) : hintPivotLast f k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [hintPivotLast]
      split_ifs <;> omega

theorem hintPivotLast_zero_iff (f : ℕ → ZMod 2) (k : ℕ) :
    hintPivotLast f k = 0 ↔ ∀ i < k, f i = 0 := by
  have hTwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  induction k with
  | zero => simp [hintPivotLast]
  | succ k ih =>
      by_cases hBit : f k = 1
      · simp only [hintPivotLast, if_pos hBit]
        constructor
        · intro hh
          omega
        · intro hh
          have hZero := hh k (by omega)
          exact (zero_ne_one (hZero.symm.trans hBit)).elim
      · have hZero : f k = 0 := (hTwo (f k)).resolve_right hBit
        rw [hintPivotLast, if_neg hBit]
        constructor
        · intro hLast i hi
          have hh := ih.mp hLast
          by_cases hEq : i = k
          · simpa only [hEq] using hZero
          · exact hh i (by omega)
        · intro hh
          apply ih.mpr
          intro i hi
          exact hh i (by omega)

theorem hintPivotLast_good (f : ℕ → ZMod 2) (k : ℕ) (hNonzero : hintPivotLast f k ≠ 0) :
    hintPivotLast f k - 1 < k ∧ f (hintPivotLast f k - 1) = 1 := by
  induction k with
  | zero => simp [hintPivotLast] at hNonzero
  | succ k ih =>
      by_cases hBit : f k = 1
      · simpa only [hintPivotLast, if_pos hBit, Nat.add_sub_cancel] using And.intro (Nat.lt_succ_self k) hBit
      · have hPrev : hintPivotLast f k ≠ 0 := by simpa only [hintPivotLast, if_neg hBit] using hNonzero
        have hh := ih hPrev
        simpa only [hintPivotLast, if_neg hBit] using And.intro (hh.1.trans (Nat.lt_succ_self k)) hh.2

structure HintPivotParams (vec count : ℕ) (state : RAMState) : Prop where
  vec_value : state.regs 4 = vec
  count_value : state.regs 6 = count
  one_value : state.regs 15 = 1

structure HintPivotInv (vec count : ℕ) (f : ℕ → ZMod 2) (k : ℕ)
    (original : ℕ → ℕ) (state : RAMState) : Prop where
  params : HintPivotParams vec count state
  counter : state.regs 0 = k
  pivot_value : state.regs 1 = hintPivotLast f k
  memory : state.mem = original

def hintPivotBody : List Instr :=
  [.add 3 4 0, .load 9 3, .add 10 0 15, .mul 10 10 9,
    .sub 11 15 9, .mul 1 1 11, .add 1 1 10, .add 0 0 15]

def hintPivotBodyResult (state : RAMState) (vec k : ℕ) (f : ℕ → ZMod 2) : RAMState :=
  {state with pc := state.pc + 8, regs :=
    Function.update (Function.update (Function.update (Function.update (Function.update (Function.update state.regs
      3 (vec + k)) 9 (f k).val) 10 (if f k = 1 then k + 1 else 0))
      11 (if f k = 1 then 0 else 1)) 1 (hintPivotLast f (k + 1))) 0 (k + 1)}

theorem hintPivotBody_spec (E : RAMEnv) (state : RAMState) (vec count k : ℕ)
    (f : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hInv : HintPivotInv vec count f k original state)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W) (hk : k < count)
    (hAddr : vec + k < 2 ^ E.W) (hF : original (vec + k) = (f k).val) :
    runBlock hintPivotBody E state = hintPivotBodyResult state vec k f := by
  have hNext : k + 1 < 2 ^ E.W := by omega
  have hPrev : hintPivotLast f k < 2 ^ E.W := (hintPivotLast_le f k).trans_lt (hk.trans hCount)
  have hOne : (1 : ZMod 2).val = 1 := by decide
  have hTwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hBitBound : (f k).val < 2 ^ E.W := (ZMod.val_lt (f k)).trans_le hWord
  have hCandidate : ((k + 1) * (f k).val) % 2 ^ E.W = if f k = 1 then k + 1 else 0 := by
    rcases hTwo (f k) with hBit | hBit <;> simp [hBit, hOne, Nat.mod_eq_of_lt hNext]
  have hFlip : (1 + 2 ^ E.W - (f k).val) % 2 ^ E.W = if f k = 1 then 0 else 1 := by
    rcases hTwo (f k) with hBit | hBit <;>
      simp [hBit, hOne, Nat.add_mod, Nat.mod_eq_of_lt hWord, Nat.add_sub_cancel_left]
  have hOld : (hintPivotLast f k * (if f k = 1 then 0 else 1)) % 2 ^ E.W =
      if f k = 1 then 0 else hintPivotLast f k := by
    by_cases hBit : f k = 1 <;> simp [hBit, Nat.mod_eq_of_lt hPrev]
  have hAcc : ((if f k = 1 then 0 else hintPivotLast f k) + (if f k = 1 then k + 1 else 0)) % 2 ^ E.W =
      hintPivotLast f (k + 1) := by
    by_cases hBit : f k = 1 <;> simp [hintPivotLast, hBit, Nat.mod_eq_of_lt hPrev, Nat.mod_eq_of_lt hNext]
  apply crState_ext
  · simp [hintPivotBody, hintPivotBodyResult, runBlock, execInstr, Nat.add_assoc]
  · funext r
    fin_cases r <;>
      simp [hintPivotBody, hintPivotBodyResult, runBlock, execInstr, hInv.params.vec_value,
        hInv.params.one_value, hInv.counter, hInv.pivot_value, hInv.memory, Nat.mod_eq_of_lt hAddr,
        hF, Nat.mod_eq_of_lt hBitBound, Nat.mod_eq_of_lt hNext, hCandidate, hFlip, hOld, hAcc]
  · rfl

theorem hintPivotBody_invariant (E : RAMEnv) (state : RAMState) (vec count k : ℕ)
    (f : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hInv : HintPivotInv vec count f k original state)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W) (hk : k < count)
    (hAddr : vec + k < 2 ^ E.W) (hF : original (vec + k) = (f k).val) :
    HintPivotInv vec count f (k + 1) original (runBlock hintPivotBody E state) := by
  rw [hintPivotBody_spec E state vec count k f original hInv hWord hCount hk hAddr hF]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, hInv.memory⟩
  · simpa [hintPivotBodyResult] using hInv.params.vec_value
  · simpa [hintPivotBodyResult] using hInv.params.count_value
  · simpa [hintPivotBodyResult] using hInv.params.one_value
  · simp [hintPivotBodyResult]
  · simp [hintPivotBodyResult]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintPivotLoop (base done : ℕ) : List Instr :=
  [.lt 2 0 6, .jz 2 done] ++ (hintPivotBody ++ [.jmp base])
theorem hintPivotBody_length : hintPivotBody.length = 8 := rfl

theorem hintPivotInv_pc {vec count k pc : ℕ} {f : ℕ → ZMod 2}
    {original : ℕ → ℕ} {state : RAMState} (h : HintPivotInv vec count f k original state) :
    HintPivotInv vec count f k original {state with pc := pc} :=
  ⟨⟨h.params.vec_value, h.params.count_value, h.params.one_value⟩, h.counter, h.pivot_value, h.memory⟩

theorem hintPivotInv_reg2 {vec count k pc value : ℕ} {f : ℕ → ZMod 2}
    {original : ℕ → ℕ} {state : RAMState} (h : HintPivotInv vec count f k original state) :
    HintPivotInv vec count f k original {state with pc := pc, regs := Function.update state.regs 2 value} := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, h.memory⟩
  · simpa using h.params.vec_value
  · simpa using h.params.count_value
  · simpa using h.params.one_value
  · simpa using h.counter
  · simpa using h.pivot_value

theorem hintPivot_guard (P : Program) (E : RAMEnv) (p : RAMState) (base done k M : ℕ)
    (hAt : At P base (hintPivotLoop base done)) (hPc : p.pc = base)
    (hCounter : p.regs 0 = k) (hRows : p.regs 6 = M) (hW : 0 < E.W) :
    (step P E)^[2] p =
      {p with pc := if k < M then base + 2 else done, regs := Function.update p.regs 2 (if k < M then 1 else 0)} := by
  have hF0 : P[p.pc]? = some (.lt 2 0 6) := by
    have h := hAt 0 (by simp [hintPivotLoop, hintPivotBody_length])
    simpa only [hintPivotLoop, List.cons_append, List.nil_append, List.getElem?_cons_zero, Nat.add_zero, hPc] using h
  have hF1 : P[p.pc + 1]? = some (.jz 2 done) := by
    have h := hAt 1 (by simp [hintPivotLoop, hintPivotBody_length])
    simpa only [hintPivotLoop, List.cons_append, List.nil_append, List.getElem?_cons_succ,
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
theorem hintPivot_iteration (P : Program) (E : RAMEnv) (p : RAMState)
    (vec count k base done : ℕ) (f : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hAddr : ∀ j < count, vec + j < 2 ^ E.W)
    (hF : ∀ j < count, original (vec + j) = (f j).val)
    (hAt : At P base (hintPivotLoop base done)) (hPc : p.pc = base)
    (hInv : HintPivotInv vec count f k original p) (hk : k < count) :
    ∃ out : RAMState, (step P E)^[11] p = out ∧ out.pc = base ∧
      HintPivotInv vec count f (k + 1) original out ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = p.regs r) := by
  let q := {p with pc := base + 2, regs := Function.update p.regs 2 1}
  have hGuard : (step P E)^[2] p = q := by
    have h := hintPivot_guard P E p base done k count hAt hPc hInv.counter hInv.params.count_value
      (by apply Nat.pos_of_ne_zero; intro hz; simpa [hz] using hWord)
    simpa only [if_pos hk] using h
  have hQ : HintPivotInv vec count f k original q := hintPivotInv_reg2 hInv
  have hTail := crAt_suffix P base [.lt 2 0 6, .jz 2 done] (hintPivotBody ++ [.jmp base]) hAt
  have hTailQ : At P q.pc (hintPivotBody ++ [.jmp base]) := by simpa using hTail
  have hBodyAt := crAt_prefix P q.pc hintPivotBody [.jmp base] hTailQ
  have hEnd := crAt_suffix P q.pc hintPivotBody [.jmp base] hTailQ
  have hJump : P[q.pc + hintPivotBody.length]? = some (.jmp base) := by
    simpa only [Nat.add_zero, List.getElem?_cons_zero] using hEnd 0 (by simp)
  have hNo : NoBranch hintPivotBody := by simp [hintPivotBody, NoBranch, Instr.NoBranchI]
  have hExec := crExecute_body_jump P E q hintPivotBody base hNo hBodyAt hJump
  generalize hu : runBlock hintPivotBody E q = u at hExec
  have hBody := hintPivotBody_invariant E q vec count k f original hQ hWord hCount hk
    (hAddr k hk) (hF k hk)
  have hSpec := hintPivotBody_spec E q vec count k f original hQ hWord hCount hk
    (hAddr k hk) (hF k hk)
  rw [hu] at hBody hSpec
  let out := {u with pc := base}
  refine ⟨out, ?_, rfl, hintPivotInv_pc hBody, ?_⟩
  · rw [show 11 = 9 + 2 by omega, Function.iterate_add_apply, hGuard]
    simpa only [hintPivotBody_length] using hExec
  · intro r h0 h1 h2 h3 h9 h10 h11
    change u.regs r = p.regs r
    rw [hSpec]
    simp only [hintPivotBodyResult, q, Function.update_of_ne h0, Function.update_of_ne h1,
      Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h9,
      Function.update_of_ne h10, Function.update_of_ne h11]

/-- Exact running time for the actual dot-product loop, with no memory writes. -/
theorem hintPivot_remaining (P : Program) (E : RAMEnv)
    (vec count base done : ℕ) (f : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hAddr : ∀ j < count, vec + j < 2 ^ E.W)
    (hF : ∀ j < count, original (vec + j) = (f j).val)
    (hAt : At P base (hintPivotLoop base done)) :
    ∀ (left k : ℕ) (p : RAMState), k + left = count → p.pc = base →
      HintPivotInv vec count f k original p →
      ∃ out : RAMState, (step P E)^[11 * left + 2] p = out ∧ out.pc = done ∧
        HintPivotInv vec count f count original out ∧
        (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = p.regs r) := by
  intro left
  induction left with
  | zero =>
      intro k p hK hPc hInv
      have hk : k = count := by omega
      let out := {p with pc := done, regs := Function.update p.regs 2 0}
      have hGuard := hintPivot_guard P E p base done k count hAt hPc hInv.counter hInv.params.count_value
        (by apply Nat.pos_of_ne_zero; intro hz; simpa [hz] using hWord)
      have hRun : (step P E)^[2] p = out := by simpa only [hk, lt_self_iff_false, if_false] using hGuard
      refine ⟨out, hRun, rfl, ?_, ?_⟩
      · rw [hk] at hInv
        exact hintPivotInv_reg2 hInv
      · intro r _ _ h2 _ _ _ _
        exact Function.update_of_ne h2 _ _
  | succ left ih =>
      intro k p hK hPc hInv
      have hk : k < count := by omega
      obtain ⟨mid, hRun, hMidPc, hMidInv, hFrame⟩ :=
        hintPivot_iteration P E p vec count k base done f original hWord hCount hAddr hF hAt hPc hInv hk
      obtain ⟨out, hRun', hOutPc, hOutInv, hFrame'⟩ := ih (k + 1) mid (by omega) hMidPc hMidInv
      refine ⟨out, ?_, hOutPc, hOutInv, ?_⟩
      · rw [show 11 * (left + 1) + 2 = (11 * left + 2) + 11 by omega, Function.iterate_add_apply, hRun, hRun']
      · intro r h0 h1 h2 h3 h9 h10 h11
        exact (hFrame' r h0 h1 h2 h3 h9 h10 h11).trans (hFrame r h0 h1 h2 h3 h9 h10 h11)

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintPivotStmt : Stmt := .seq (.code [.imm 0 0, .imm 1 0]) (.loop (.lt 2 0 6) (.code hintPivotBody))
theorem hintPivotStmt_len : hintPivotStmt.len = 13 := rfl

theorem hintPivotLoop_compile (base : ℕ) :
    (Stmt.loop (.lt 2 0 6) (.code hintPivotBody)).compile base = hintPivotLoop base (base + 11) := rfl

/-- A native complete pivot scan, with a fixed running time for all vectors. -/
theorem hintPivotStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (vec count base : ℕ) (f : ℕ → ZMod 2)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hAddr : ∀ j < count, vec + j < 2 ^ E.W)
    (hF : ∀ j < count, state.mem (vec + j) = (f j).val)
    (hAt : At P base (hintPivotStmt.compile base)) (hPc : state.pc = base)
    (hParams : HintPivotParams vec count state) :
    Sem P E base (base + 13) state (fun k out => k = 11 * count + 4 ∧
      out.regs 0 = count ∧ out.regs 1 = hintPivotLast f count ∧ out.mem = state.mem ∧
      HintPivotParams vec count out ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = state.regs r)) := by
  obtain ⟨hAtInit, hAtLoop⟩ := At.seqStmt hAt
  have hLoop : At P (base + 2) (hintPivotLoop (base + 2) (base + 13)) := by
    simpa only [Stmt.len, List.length_cons, List.length_nil, hintPivotLoop_compile, Nat.add_assoc] using hAtLoop
  have hInitAt : At P state.pc [.imm 0 0, .imm 1 0] := by rw [hPc]; exact hAtInit
  let q : RAMState := {state with pc := state.pc + 2, regs := Function.update (Function.update state.regs 0 0) 1 0}
  have hInit : runBlock [.imm 0 0, .imm 1 0] E state = q := by
    apply crState_ext
    · simp [q, runBlock, execInstr, Nat.add_assoc]
    · rfl
    · rfl
  have hRunInit : (step P E)^[2] state = q := by
    have hh := iterate_runBlock_of_at P E [.imm 0 0, .imm 1 0] state hInitAt (by simp [NoBranch, Instr.NoBranchI])
    simpa only [List.length_cons, List.length_nil, hInit] using hh
  have hQ : HintPivotInv vec count f 0 state.mem q := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, rfl⟩
    · simpa [q] using hParams.vec_value
    · simpa [q] using hParams.count_value
    · simpa [q] using hParams.one_value
    · simp [q]
    · simp [q, hintPivotLast]
  have hQPc : q.pc = base + 2 := by change state.pc + 2 = _; rw [hPc]
  obtain ⟨out, hRunLoop, hOutPc, hOutInv, hFrame⟩ := hintPivot_remaining P E
    vec count (base + 2) (base + 13) f state.mem hWord hCount hAddr hF hLoop
    count 0 q (by omega) hQPc hQ
  refine ⟨hPc, 11 * count + 4, out, ?_, hOutPc, rfl, hOutInv.counter, hOutInv.pivot_value,
    hOutInv.memory, hOutInv.params, ?_⟩
  · rw [show 11 * count + 4 = (11 * count + 2) + 2 by omega, Function.iterate_add_apply, hRunInit, hRunLoop]
  · intro r h0 h1 h2 h3 h9 h10 h11
    exact (hFrame r h0 h1 h2 h3 h9 h10 h11).trans (by simp only [q, Function.update_of_ne h1, Function.update_of_ne h0])

/-- A zero result certifies a zero vector; a nonzero result is one plus a valid
    nonzero coordinate. All surrounding memory remains unchanged. -/
theorem hintPivotStmt_find_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (vec count base : ℕ) (f : ℕ → ZMod 2)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hAddr : ∀ j < count, vec + j < 2 ^ E.W)
    (hF : ∀ j < count, state.mem (vec + j) = (f j).val)
    (hAt : At P base (hintPivotStmt.compile base)) (hPc : state.pc = base)
    (hParams : HintPivotParams vec count state) :
    Sem P E base (base + 13) state (fun k out => k = 11 * count + 4 ∧ out.mem = state.mem ∧
      out.regs 1 ≤ count ∧ (out.regs 1 = 0 ↔ ∀ j < count, f j = 0) ∧
      (out.regs 1 ≠ 0 → out.regs 1 - 1 < count ∧ f (out.regs 1 - 1) = 1) ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = state.regs r)) := by
  apply Sem.mono (hintPivotStmt_sem P E state vec count base f hWord hCount hAddr hF hAt hPc hParams)
  intro k out hOut
  obtain ⟨hK, _, hPivot, hMem, _, hFrame⟩ := hOut
  refine ⟨hK, hMem, ?_, ?_, ?_, hFrame⟩
  · rw [hPivot]
    exact hintPivotLast_le f count
  · simpa only [hPivot] using hintPivotLast_zero_iff f count
  · rw [hPivot]
    exact hintPivotLast_good f count

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPivotStmt_find_sem


