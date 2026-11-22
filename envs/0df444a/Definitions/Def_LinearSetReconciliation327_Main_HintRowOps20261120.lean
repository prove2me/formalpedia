-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintRowOps20261120
-- name    : LinearSetReconciliation327_Main_HintRowOps20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:34:49.510824+00:00
-- url     : https://prove2.me/theorems/7a7516f9-c724-413b-8ed8-7d1f7616d81e
-- title:
--   LinearSetReconciliation327 — HintRowOps (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintRowOps20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowDot20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDotLoop (base done : ℕ) : List Instr :=
  [.lt 2 0 6, .jz 2 done] ++ (hintDotBody ++ [.jmp base])
theorem hintDotBody_length : hintDotBody.length = 8 := rfl

theorem hintDotInv_pc {vec mat count stride k pc : ℕ} {f g : ℕ → ZMod 2}
    {original : ℕ → ℕ} {p : RAMState} (h : HintDotInv vec mat count stride f g k original p) :
    HintDotInv vec mat count stride f g k original {p with pc := pc} :=
  ⟨⟨h.params.vec_value, h.params.mat_value, h.params.count_value, h.params.stride_value,
    h.params.one_value⟩, h.counter, h.sum_value, h.memory⟩

theorem hintDotInv_reg2 {vec mat count stride k pc value : ℕ} {f g : ℕ → ZMod 2}
    {original : ℕ → ℕ} {p : RAMState} (h : HintDotInv vec mat count stride f g k original p) :
    HintDotInv vec mat count stride f g k original {p with pc := pc, regs := Function.update p.regs 2 value} := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, h.memory⟩
  · simpa using h.params.vec_value
  · simpa using h.params.mat_value
  · simpa using h.params.count_value
  · simpa using h.params.stride_value
  · simpa using h.params.one_value
  · simpa using h.counter
  · simpa using h.sum_value

theorem hintDot_guard (P : Program) (E : RAMEnv) (p : RAMState) (base done k M : ℕ)
    (hAt : At P base (hintDotLoop base done)) (hPc : p.pc = base)
    (hCounter : p.regs 0 = k) (hRows : p.regs 6 = M) (hW : 0 < E.W) :
    (step P E)^[2] p =
      {p with pc := if k < M then base + 2 else done, regs := Function.update p.regs 2 (if k < M then 1 else 0)} := by
  have hF0 : P[p.pc]? = some (.lt 2 0 6) := by
    have h := hAt 0 (by simp [hintDotLoop, hintDotBody_length])
    simpa only [hintDotLoop, List.cons_append, List.nil_append, List.getElem?_cons_zero, Nat.add_zero, hPc] using h
  have hF1 : P[p.pc + 1]? = some (.jz 2 done) := by
    have h := hAt 1 (by simp [hintDotLoop, hintDotBody_length])
    simpa only [hintDotLoop, List.cons_append, List.nil_append, List.getElem?_cons_succ,
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
theorem hintDot_iteration (P : Program) (E : RAMEnv) (p : RAMState)
    (vec mat count stride k base done : ℕ) (f g : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hVec : ∀ j < count, vec + j < 2 ^ E.W) (hMat : ∀ j < count, mat + j * stride < 2 ^ E.W)
    (hF : ∀ j < count, original (mat + j * stride) = (f j).val)
    (hG : ∀ j < count, original (vec + j) = (g j).val)
    (hAt : At P base (hintDotLoop base done)) (hPc : p.pc = base)
    (hInv : HintDotInv vec mat count stride f g k original p) (hk : k < count) :
    ∃ out : RAMState, (step P E)^[11] p = out ∧ out.pc = base ∧
      HintDotInv vec mat count stride f g (k + 1) original out ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = p.regs r) := by
  let q := {p with pc := base + 2, regs := Function.update p.regs 2 1}
  have hGuard : (step P E)^[2] p = q := by
    have h := hintDot_guard P E p base done k count hAt hPc hInv.counter hInv.params.count_value
      (by apply Nat.pos_of_ne_zero; intro hz; simpa [hz] using hWord)
    simpa only [if_pos hk] using h
  have hQ : HintDotInv vec mat count stride f g k original q := hintDotInv_reg2 hInv
  have hTail := crAt_suffix P base [.lt 2 0 6, .jz 2 done] (hintDotBody ++ [.jmp base]) hAt
  have hTailQ : At P q.pc (hintDotBody ++ [.jmp base]) := by simpa using hTail
  have hBodyAt := crAt_prefix P q.pc hintDotBody [.jmp base] hTailQ
  have hEnd := crAt_suffix P q.pc hintDotBody [.jmp base] hTailQ
  have hJump : P[q.pc + hintDotBody.length]? = some (.jmp base) := by
    simpa only [Nat.add_zero, List.getElem?_cons_zero] using hEnd 0 (by simp)
  have hNo : NoBranch hintDotBody := by simp [hintDotBody, NoBranch, Instr.NoBranchI]
  have hExec := crExecute_body_jump P E q hintDotBody base hNo hBodyAt hJump
  generalize hu : runBlock hintDotBody E q = u at hExec
  have hBody := hintDotBody_invariant E q vec mat count stride k f g original hQ hWord hCount hk
    (hVec k hk) (hMat k hk) (hF k hk) (hG k hk)
  have hSpec := hintDotBody_spec E q vec mat count stride k f g original hQ hWord hCount hk
    (hVec k hk) (hMat k hk) (hF k hk) (hG k hk)
  rw [hu] at hBody hSpec
  let out := {u with pc := base}
  refine ⟨out, ?_, rfl, hintDotInv_pc hBody, ?_⟩
  · rw [show 11 = 9 + 2 by omega, Function.iterate_add_apply, hGuard]
    simpa only [hintDotBody_length] using hExec
  · intro r h0 h1 h2 h3 h9 h10 h11
    change u.regs r = p.regs r
    rw [hSpec]
    simp only [hintDotBodyResult, q, Function.update_of_ne h0, Function.update_of_ne h1,
      Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h9,
      Function.update_of_ne h10, Function.update_of_ne h11]

/-- Exact running time for the actual dot-product loop, with no memory writes. -/
theorem hintDot_remaining (P : Program) (E : RAMEnv)
    (vec mat count stride base done : ℕ) (f g : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hVec : ∀ j < count, vec + j < 2 ^ E.W) (hMat : ∀ j < count, mat + j * stride < 2 ^ E.W)
    (hF : ∀ j < count, original (mat + j * stride) = (f j).val)
    (hG : ∀ j < count, original (vec + j) = (g j).val)
    (hAt : At P base (hintDotLoop base done)) :
    ∀ (left k : ℕ) (p : RAMState), k + left = count → p.pc = base →
      HintDotInv vec mat count stride f g k original p →
      ∃ out : RAMState, (step P E)^[11 * left + 2] p = out ∧ out.pc = done ∧
        HintDotInv vec mat count stride f g count original out ∧
        (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = p.regs r) := by
  intro left
  induction left with
  | zero =>
      intro k p hK hPc hInv
      have hk : k = count := by omega
      let out := {p with pc := done, regs := Function.update p.regs 2 0}
      have hGuard := hintDot_guard P E p base done k count hAt hPc hInv.counter hInv.params.count_value
        (by apply Nat.pos_of_ne_zero; intro hz; simpa [hz] using hWord)
      have hRun : (step P E)^[2] p = out := by simpa only [hk, lt_self_iff_false, if_false] using hGuard
      refine ⟨out, hRun, rfl, ?_, ?_⟩
      · rw [hk] at hInv
        exact hintDotInv_reg2 hInv
      · intro r _ _ h2 _ _ _ _
        exact Function.update_of_ne h2 _ _
  | succ left ih =>
      intro k p hK hPc hInv
      have hk : k < count := by omega
      obtain ⟨mid, hRun, hMidPc, hMidInv, hFrame⟩ :=
        hintDot_iteration P E p vec mat count stride k base done f g original hWord hCount hVec hMat hF hG hAt hPc hInv hk
      obtain ⟨out, hRun', hOutPc, hOutInv, hFrame'⟩ := ih (k + 1) mid (by omega) hMidPc hMidInv
      refine ⟨out, ?_, hOutPc, hOutInv, ?_⟩
      · rw [show 11 * (left + 1) + 2 = (11 * left + 2) + 11 by omega, Function.iterate_add_apply, hRun, hRun']
      · intro r h0 h1 h2 h3 h9 h10 h11
        exact (hFrame' r h0 h1 h2 h3 h9 h10 h11).trans (hFrame r h0 h1 h2 h3 h9 h10 h11)

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintDotStmt : Stmt := .seq (.code [.imm 0 0, .imm 1 0]) (.loop (.lt 2 0 6) (.code hintDotBody))
theorem hintDotStmt_len : hintDotStmt.len = 13 := rfl

theorem hintDotLoop_compile (base : ℕ) :
    (Stmt.loop (.lt 2 0 6) (.code hintDotBody)).compile base = hintDotLoop base (base + 11) := rfl

/-- A composable dot product in the fixed physical RAM environment. Inputs may
    have arbitrary surrounding memory; this block never writes memory. -/
theorem hintDotStmt_sem (P : Program) (E : RAMEnv) (p : RAMState)
    (vec mat count stride base : ℕ) (f g : ℕ → ZMod 2)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hVec : ∀ j < count, vec + j < 2 ^ E.W) (hMat : ∀ j < count, mat + j * stride < 2 ^ E.W)
    (hF : ∀ j < count, p.mem (mat + j * stride) = (f j).val)
    (hG : ∀ j < count, p.mem (vec + j) = (g j).val)
    (hAt : At P base (hintDotStmt.compile base)) (hPc : p.pc = base)
    (hParams : HintDotParams vec mat count stride p) :
    Sem P E base (base + 13) p (fun k out => k = 11 * count + 4 ∧
      out.regs 0 = count ∧ out.regs 1 = (hintDotSum f g count).val ∧ out.mem = p.mem ∧
      HintDotParams vec mat count stride out ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = p.regs r)) := by
  obtain ⟨hAtInit, hAtLoop⟩ := At.seqStmt hAt
  have hLoop : At P (base + 2) (hintDotLoop (base + 2) (base + 13)) := by
    simpa only [Stmt.len, List.length_cons, List.length_nil, hintDotLoop_compile, Nat.add_assoc] using hAtLoop
  have hInitAt : At P p.pc [.imm 0 0, .imm 1 0] := by rw [hPc]; exact hAtInit
  let q : RAMState := {p with pc := p.pc + 2, regs := Function.update (Function.update p.regs 0 0) 1 0}
  have hInit : runBlock [.imm 0 0, .imm 1 0] E p = q := by
    apply crState_ext
    · simp [q, runBlock, execInstr, Nat.add_assoc]
    · rfl
    · rfl
  have hRunInit : (step P E)^[2] p = q := by
    have hh := iterate_runBlock_of_at P E [.imm 0 0, .imm 1 0] p hInitAt (by simp [NoBranch, Instr.NoBranchI])
    simpa only [List.length_cons, List.length_nil, hInit] using hh
  have hQ : HintDotInv vec mat count stride f g 0 p.mem q := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, rfl⟩
    · simpa only [q, Function.update_of_ne (by decide : (4 : Fin 16) ≠ 1),
        Function.update_of_ne (by decide : (4 : Fin 16) ≠ 0)] using hParams.vec_value
    · simpa only [q, Function.update_of_ne (by decide : (5 : Fin 16) ≠ 1),
        Function.update_of_ne (by decide : (5 : Fin 16) ≠ 0)] using hParams.mat_value
    · simpa only [q, Function.update_of_ne (by decide : (6 : Fin 16) ≠ 1),
        Function.update_of_ne (by decide : (6 : Fin 16) ≠ 0)] using hParams.count_value
    · simpa only [q, Function.update_of_ne (by decide : (7 : Fin 16) ≠ 1),
        Function.update_of_ne (by decide : (7 : Fin 16) ≠ 0)] using hParams.stride_value
    · simpa only [q, Function.update_of_ne (by decide : (15 : Fin 16) ≠ 1),
        Function.update_of_ne (by decide : (15 : Fin 16) ≠ 0)] using hParams.one_value
    · simp [q]
    · simp [q, hintDotSum]
  have hQPc : q.pc = base + 2 := by change p.pc + 2 = _; rw [hPc]
  obtain ⟨out, hRunLoop, hOutPc, hOutInv, hFrame⟩ := hintDot_remaining P E
    vec mat count stride (base + 2) (base + 13) f g p.mem hWord hCount hVec hMat hF hG hLoop
    count 0 q (by omega) hQPc hQ
  refine ⟨hPc, 11 * count + 4, out, ?_, hOutPc, rfl, hOutInv.counter, hOutInv.sum_value,
    hOutInv.memory, hOutInv.params, ?_⟩
  · rw [show 11 * count + 4 = (11 * count + 2) + 2 by omega, Function.iterate_add_apply, hRunInit, hRunLoop]
  · intro r h0 h1 h2 h3 h9 h10 h11
    exact (hFrame r h0 h1 h2 h3 h9 h10 h11).trans (by simp only [q, Function.update_of_ne h1, Function.update_of_ne h0])

end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintAxpyParams (dest src count : ℕ) (scale : ZMod 2) (p : RAMState) : Prop where
  dest_value : p.regs 4 = dest
  src_value : p.regs 5 = src
  count_value : p.regs 6 = count
  scale_value : p.regs 8 = scale.val
  one_value : p.regs 15 = 1

def hintAxpyBody : List Instr :=
  [.add 3 4 0, .load 9 3, .add 10 5 0, .load 10 10, .mul 11 8 10,
    .bxor 9 9 11, .store 3 9, .add 0 0 15]

def hintAxpyBodyResult (p : RAMState) (dest k : ℕ) (scale : ZMod 2) (f g : ℕ → ZMod 2) : RAMState :=
  { p with
    pc := p.pc + 8
    mem := Function.update p.mem (dest + k) (f k + scale * g k).val
    regs :=
    Function.update (Function.update (Function.update (Function.update (Function.update p.regs
      3 (dest + k)) 10 (g k).val) 11 (scale * g k).val) 9 (f k + scale * g k).val) 0 (k + 1)}

theorem hintAxpyBody_spec (E : RAMEnv) (p : RAMState) (dest src count k : ℕ)
    (scale : ZMod 2) (f g : ℕ → ZMod 2)
    (hParams : HintAxpyParams dest src count scale p) (hCounter : p.regs 0 = k)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W) (hk : k < count)
    (hDest : dest + k < 2 ^ E.W) (hSrc : src + k < 2 ^ E.W)
    (hF : p.mem (dest + k) = (f k).val) (hG : p.mem (src + k) = (g k).val) :
    runBlock hintAxpyBody E p = hintAxpyBodyResult p dest k scale f g := by
  have hNext : k + 1 < 2 ^ E.W := by omega
  have hFBound : (f k).val < 2 ^ E.W := (ZMod.val_lt (f k)).trans_le hWord
  have hGBound : (g k).val < 2 ^ E.W := (ZMod.val_lt (g k)).trans_le hWord
  have hProdBound : (scale * g k).val < 2 ^ E.W := (ZMod.val_lt (scale * g k)).trans_le hWord
  have hSumBound : (f k + scale * g k).val < 2 ^ E.W := (ZMod.val_lt (f k + scale * g k)).trans_le hWord
  apply crState_ext
  · simp [hintAxpyBody, hintAxpyBodyResult, runBlock, execInstr, Nat.add_assoc]
  · funext r
    fin_cases r <;>
      simp [hintAxpyBody, hintAxpyBodyResult, runBlock, execInstr, hParams.dest_value,
        hParams.src_value, hParams.scale_value, hParams.one_value, hCounter,
        Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hSrc, hF, hG,
        Nat.mod_eq_of_lt hFBound, Nat.mod_eq_of_lt hGBound, hintBit_mul,
        Nat.mod_eq_of_lt hProdBound, hintBit_xor, Nat.mod_eq_of_lt hSumBound, Nat.mod_eq_of_lt hNext]
  · simp [hintAxpyBody, hintAxpyBodyResult, runBlock, execInstr, hParams.dest_value,
      hParams.src_value, hParams.scale_value, hParams.one_value, hCounter,
      Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hSrc, hF, hG,
      Nat.mod_eq_of_lt hFBound, Nat.mod_eq_of_lt hGBound, hintBit_mul,
      Nat.mod_eq_of_lt hProdBound, hintBit_xor, Nat.mod_eq_of_lt hSumBound]

def hintAxpyMem (original : ℕ → ℕ) (dest : ℕ) (scale : ZMod 2)
    (f g : ℕ → ZMod 2) (k addr : ℕ) : ℕ :=
  if dest ≤ addr ∧ addr < dest + k then (f (addr - dest) + scale * g (addr - dest)).val else original addr

theorem hintAxpyMem_zero (original : ℕ → ℕ) (dest : ℕ) (scale : ZMod 2) (f g : ℕ → ZMod 2) :
    hintAxpyMem original dest scale f g 0 = original := by
  funext addr
  simp only [hintAxpyMem, Nat.add_zero]
  rw [if_neg (by omega)]

theorem hintAxpyMem_succ (original : ℕ → ℕ) (dest : ℕ) (scale : ZMod 2) (f g : ℕ → ZMod 2) (k : ℕ) :
    Function.update (hintAxpyMem original dest scale f g k) (dest + k) (f k + scale * g k).val =
      hintAxpyMem original dest scale f g (k + 1) := by
  funext addr
  by_cases hEq : addr = dest + k
  · subst addr
    simp [hintAxpyMem, Nat.add_sub_cancel_left]
  · rw [Function.update_of_ne hEq]
    unfold hintAxpyMem
    by_cases hOld : dest ≤ addr ∧ addr < dest + k
    · rw [if_pos hOld, if_pos (by omega)]
    · rw [if_neg hOld, if_neg (by omega)]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

structure HintAxpyInv (dest src count : ℕ) (scale : ZMod 2) (f g : ℕ → ZMod 2) (k : ℕ)
    (original : ℕ → ℕ) (p : RAMState) : Prop where
  params : HintAxpyParams dest src count scale p
  counter : p.regs 0 = k
  memory : p.mem = hintAxpyMem original dest scale f g k

theorem hintAxpyBody_transition (E : RAMEnv) (p : RAMState) (dest src count : ℕ) (scale : ZMod 2) (k : ℕ)
    (f g : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hInv : HintAxpyInv dest src count scale f g k original p)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W) (hk : k < count)
    (hDest : dest + k < 2 ^ E.W) (hSrc : src + k < 2 ^ E.W)
    (hSeparate : dest + count ≤ src ∨ src + count ≤ dest)
    (hF : original (dest + k) = (f k).val) (hG : original (src + k) = (g k).val) :
    let out := runBlock hintAxpyBody E p
    out.pc = p.pc + 8 ∧ HintAxpyInv dest src count scale f g (k + 1) original out ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = p.regs r) := by
  have hAtDest : p.mem (dest + k) = (f k).val := by
    rw [hInv.memory]
    simpa only [hintAxpyMem, lt_self_iff_false, and_false, if_false] using hF
  have hOutsideSrc : ¬ (dest ≤ src + k ∧ src + k < dest + k) := by
    rcases hSeparate with hSep | hSep <;> omega
  have hAtSrc : p.mem (src + k) = (g k).val := by
    rw [hInv.memory]
    simpa only [hintAxpyMem, if_neg hOutsideSrc] using hG
  have hSpec := hintAxpyBody_spec E p dest src count k scale f g hInv.params hInv.counter
    hWord hCount hk hDest hSrc hAtDest hAtSrc
  dsimp only
  rw [hSpec]
  refine ⟨rfl, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hintAxpyBodyResult] using hInv.params.dest_value
    · simpa [hintAxpyBodyResult] using hInv.params.src_value
    · simpa [hintAxpyBodyResult] using hInv.params.count_value
    · simpa [hintAxpyBodyResult] using hInv.params.scale_value
    · simpa [hintAxpyBodyResult] using hInv.params.one_value
  · simp [hintAxpyBodyResult]
  · change Function.update p.mem (dest + k) (f k + scale * g k).val = _
    rw [hInv.memory, hintAxpyMem_succ]
  · intro r h0 h1 h2 h3 h9 h10 h11
    simp only [hintAxpyBodyResult, Function.update_of_ne h0, Function.update_of_ne h9,
      Function.update_of_ne h11, Function.update_of_ne h10, Function.update_of_ne h3]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintAxpyLoop (base done : ℕ) : List Instr :=
  [.lt 2 0 6, .jz 2 done] ++ (hintAxpyBody ++ [.jmp base])
theorem hintAxpyBody_length : hintAxpyBody.length = 8 := rfl

theorem hintAxpyInv_pc {dest src count k pc : ℕ} {scale : ZMod 2} {f g : ℕ → ZMod 2}
    {original : ℕ → ℕ} {p : RAMState} (h : HintAxpyInv dest src count scale f g k original p) :
    HintAxpyInv dest src count scale f g k original {p with pc := pc} :=
  ⟨⟨h.params.dest_value, h.params.src_value, h.params.count_value, h.params.scale_value,
    h.params.one_value⟩, h.counter, h.memory⟩

theorem hintAxpyInv_reg2 {dest src count k pc value : ℕ} {scale : ZMod 2} {f g : ℕ → ZMod 2}
    {original : ℕ → ℕ} {p : RAMState} (h : HintAxpyInv dest src count scale f g k original p) :
    HintAxpyInv dest src count scale f g k original {p with pc := pc, regs := Function.update p.regs 2 value} := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, h.memory⟩
  · simpa using h.params.dest_value
  · simpa using h.params.src_value
  · simpa using h.params.count_value
  · simpa using h.params.scale_value
  · simpa using h.params.one_value
  · simpa using h.counter

theorem hintAxpy_guard (P : Program) (E : RAMEnv) (p : RAMState) (base done k M : ℕ)
    (hAt : At P base (hintAxpyLoop base done)) (hPc : p.pc = base)
    (hCounter : p.regs 0 = k) (hRows : p.regs 6 = M) (hW : 0 < E.W) :
    (step P E)^[2] p =
      {p with pc := if k < M then base + 2 else done, regs := Function.update p.regs 2 (if k < M then 1 else 0)} := by
  have hF0 : P[p.pc]? = some (.lt 2 0 6) := by
    have h := hAt 0 (by simp [hintAxpyLoop, hintAxpyBody_length])
    simpa only [hintAxpyLoop, List.cons_append, List.nil_append, List.getElem?_cons_zero, Nat.add_zero, hPc] using h
  have hF1 : P[p.pc + 1]? = some (.jz 2 done) := by
    have h := hAt 1 (by simp [hintAxpyLoop, hintAxpyBody_length])
    simpa only [hintAxpyLoop, List.cons_append, List.nil_append, List.getElem?_cons_succ,
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
theorem hintAxpy_iteration (P : Program) (E : RAMEnv) (p : RAMState)
    (dest src count : ℕ) (scale : ZMod 2) (k base done : ℕ) (f g : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hDest : ∀ j < count, dest + j < 2 ^ E.W) (hSrc : ∀ j < count, src + j < 2 ^ E.W)
    (hF : ∀ j < count, original (dest + j) = (f j).val)
    (hG : ∀ j < count, original (src + j) = (g j).val)
    (hSeparate : dest + count ≤ src ∨ src + count ≤ dest)
    (hAt : At P base (hintAxpyLoop base done)) (hPc : p.pc = base)
    (hInv : HintAxpyInv dest src count scale f g k original p) (hk : k < count) :
    ∃ out : RAMState, (step P E)^[11] p = out ∧ out.pc = base ∧
      HintAxpyInv dest src count scale f g (k + 1) original out ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = p.regs r) := by
  let q := {p with pc := base + 2, regs := Function.update p.regs 2 1}
  have hGuard : (step P E)^[2] p = q := by
    have h := hintAxpy_guard P E p base done k count hAt hPc hInv.counter hInv.params.count_value
      (by apply Nat.pos_of_ne_zero; intro hz; simpa [hz] using hWord)
    simpa only [if_pos hk] using h
  have hQ : HintAxpyInv dest src count scale f g k original q := hintAxpyInv_reg2 hInv
  have hTail := crAt_suffix P base [.lt 2 0 6, .jz 2 done] (hintAxpyBody ++ [.jmp base]) hAt
  have hTailQ : At P q.pc (hintAxpyBody ++ [.jmp base]) := by simpa using hTail
  have hBodyAt := crAt_prefix P q.pc hintAxpyBody [.jmp base] hTailQ
  have hEnd := crAt_suffix P q.pc hintAxpyBody [.jmp base] hTailQ
  have hJump : P[q.pc + hintAxpyBody.length]? = some (.jmp base) := by
    simpa only [Nat.add_zero, List.getElem?_cons_zero] using hEnd 0 (by simp)
  have hNo : NoBranch hintAxpyBody := by simp [hintAxpyBody, NoBranch, Instr.NoBranchI]
  have hExec := crExecute_body_jump P E q hintAxpyBody base hNo hBodyAt hJump
  generalize hu : runBlock hintAxpyBody E q = u at hExec
  have hBody := hintAxpyBody_transition E q dest src count scale k f g original hQ hWord hCount hk
    (hDest k hk) (hSrc k hk) hSeparate (hF k hk) (hG k hk)
  rw [hu] at hBody
  obtain ⟨_, hInvU, hFrame⟩ := hBody
  let out := {u with pc := base}
  refine ⟨out, ?_, rfl, hintAxpyInv_pc hInvU, ?_⟩
  · rw [show 11 = 9 + 2 by omega, Function.iterate_add_apply, hGuard]
    simpa only [hintAxpyBody_length] using hExec
  · intro r h0 h1 h2 h3 h9 h10 h11
    exact (hFrame r h0 h1 h2 h3 h9 h10 h11).trans (by simp only [q, Function.update_of_ne h2])

theorem hintAxpy_remaining (P : Program) (E : RAMEnv)
    (dest src count : ℕ) (scale : ZMod 2) (base done : ℕ) (f g : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hDest : ∀ j < count, dest + j < 2 ^ E.W) (hSrc : ∀ j < count, src + j < 2 ^ E.W)
    (hF : ∀ j < count, original (dest + j) = (f j).val)
    (hG : ∀ j < count, original (src + j) = (g j).val)
    (hSeparate : dest + count ≤ src ∨ src + count ≤ dest)
    (hAt : At P base (hintAxpyLoop base done)) :
    ∀ (left k : ℕ) (p : RAMState), k + left = count → p.pc = base →
      HintAxpyInv dest src count scale f g k original p →
      ∃ out : RAMState, (step P E)^[11 * left + 2] p = out ∧ out.pc = done ∧
        HintAxpyInv dest src count scale f g count original out ∧
        (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = p.regs r) := by

  intro left
  induction left with
  | zero =>
      intro k p hK hPc hInv
      have hk : k = count := by omega
      let out := {p with pc := done, regs := Function.update p.regs 2 0}
      have hGuard := hintAxpy_guard P E p base done k count hAt hPc hInv.counter hInv.params.count_value
        (by apply Nat.pos_of_ne_zero; intro hz; simpa [hz] using hWord)
      have hRun : (step P E)^[2] p = out := by simpa only [hk, lt_self_iff_false, if_false] using hGuard
      refine ⟨out, hRun, rfl, ?_, ?_⟩
      · rw [hk] at hInv
        exact hintAxpyInv_reg2 hInv
      · intro r _ _ h2 _ _ _ _
        exact Function.update_of_ne h2 _ _
  | succ left ih =>
      intro k p hK hPc hInv
      have hk : k < count := by omega
      obtain ⟨mid, hRun, hMidPc, hMidInv, hFrame⟩ :=
        hintAxpy_iteration P E p dest src count scale k base done f g original hWord hCount hDest hSrc hF hG hSeparate hAt hPc hInv hk
      obtain ⟨out, hRun', hOutPc, hOutInv, hFrame'⟩ := ih (k + 1) mid (by omega) hMidPc hMidInv
      refine ⟨out, ?_, hOutPc, hOutInv, ?_⟩
      · rw [show 11 * (left + 1) + 2 = (11 * left + 2) + 11 by omega, Function.iterate_add_apply, hRun, hRun']
      · intro r h0 h1 h2 h3 h9 h10 h11
        exact (hFrame' r h0 h1 h2 h3 h9 h10 h11).trans (hFrame r h0 h1 h2 h3 h9 h10 h11)

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintAxpyStmt : Stmt := .seq (.code [.imm 0 0, .imm 1 0]) (.loop (.lt 2 0 6) (.code hintAxpyBody))
theorem hintAxpyStmt_len : hintAxpyStmt.len = 13 := rfl

theorem hintAxpyLoop_compile (base : ℕ) :
    (Stmt.loop (.lt 2 0 6) (.code hintAxpyBody)).compile base = hintAxpyLoop base (base + 11) := rfl

/-- A composable binary row update in the same physical environment as its
    caller, with exact writes and a full frame outside the destination vector. -/
theorem hintAxpyStmt_sem (P : Program) (E : RAMEnv) (p : RAMState)
    (dest src count base : ℕ) (scale : ZMod 2) (f g : ℕ → ZMod 2)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hDest : ∀ j < count, dest + j < 2 ^ E.W) (hSrc : ∀ j < count, src + j < 2 ^ E.W)
    (hF : ∀ j < count, p.mem (dest + j) = (f j).val)
    (hG : ∀ j < count, p.mem (src + j) = (g j).val)
    (hSeparate : dest + count ≤ src ∨ src + count ≤ dest)
    (hAt : At P base (hintAxpyStmt.compile base)) (hPc : p.pc = base)
    (hParams : HintAxpyParams dest src count scale p) :
    Sem P E base (base + 13) p (fun k out => k = 11 * count + 4 ∧
      out.regs 0 = count ∧ out.mem = hintAxpyMem p.mem dest scale f g count ∧
      HintAxpyParams dest src count scale out ∧
      (∀ addr, (addr < dest ∨ dest + count ≤ addr) → out.mem addr = p.mem addr) ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = p.regs r)) := by
  obtain ⟨hAtInit, hAtLoop⟩ := At.seqStmt hAt
  have hLoop : At P (base + 2) (hintAxpyLoop (base + 2) (base + 13)) := by
    simpa only [Stmt.len, List.length_cons, List.length_nil, hintAxpyLoop_compile, Nat.add_assoc] using hAtLoop
  have hInitAt : At P p.pc [.imm 0 0, .imm 1 0] := by rw [hPc]; exact hAtInit
  let q : RAMState := {p with pc := p.pc + 2, regs := Function.update (Function.update p.regs 0 0) 1 0}
  have hInit : runBlock [.imm 0 0, .imm 1 0] E p = q := by
    apply crState_ext
    · simp [q, runBlock, execInstr, Nat.add_assoc]
    · rfl
    · rfl
  have hRunInit : (step P E)^[2] p = q := by
    have hh := iterate_runBlock_of_at P E [.imm 0 0, .imm 1 0] p hInitAt (by simp [NoBranch, Instr.NoBranchI])
    simpa only [List.length_cons, List.length_nil, hInit] using hh
  have hQ : HintAxpyInv dest src count scale f g 0 p.mem q := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simpa only [q, Function.update_of_ne (by decide : (4 : Fin 16) ≠ 1),
        Function.update_of_ne (by decide : (4 : Fin 16) ≠ 0)] using hParams.dest_value
    · simpa only [q, Function.update_of_ne (by decide : (5 : Fin 16) ≠ 1),
        Function.update_of_ne (by decide : (5 : Fin 16) ≠ 0)] using hParams.src_value
    · simpa only [q, Function.update_of_ne (by decide : (6 : Fin 16) ≠ 1),
        Function.update_of_ne (by decide : (6 : Fin 16) ≠ 0)] using hParams.count_value
    · simpa only [q, Function.update_of_ne (by decide : (8 : Fin 16) ≠ 1),
        Function.update_of_ne (by decide : (8 : Fin 16) ≠ 0)] using hParams.scale_value
    · simpa only [q, Function.update_of_ne (by decide : (15 : Fin 16) ≠ 1),
        Function.update_of_ne (by decide : (15 : Fin 16) ≠ 0)] using hParams.one_value
    · simp [q]
    · exact (hintAxpyMem_zero p.mem dest scale f g).symm
  have hQPc : q.pc = base + 2 := by change p.pc + 2 = _; rw [hPc]
  obtain ⟨out, hRunLoop, hOutPc, hOutInv, hFrame⟩ := hintAxpy_remaining P E
    dest src count scale (base + 2) (base + 13) f g p.mem hWord hCount hDest hSrc hF hG hSeparate hLoop
    count 0 q (by omega) hQPc hQ
  refine ⟨hPc, 11 * count + 4, out, ?_, hOutPc, rfl, hOutInv.counter,
    hOutInv.memory, hOutInv.params, ?_, ?_⟩
  · rw [show 11 * count + 4 = (11 * count + 2) + 2 by omega, Function.iterate_add_apply, hRunInit, hRunLoop]
  · intro addr hOutside
    rw [hOutInv.memory]
    exact if_neg (by rcases hOutside with hBefore | hAfter <;> omega)
  · intro r h0 h1 h2 h3 h9 h10 h11
    exact (hFrame r h0 h1 h2 h3 h9 h10 h11).trans (by simp only [q, Function.update_of_ne h1, Function.update_of_ne h0])

end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.hintDotStmt_sem
#print axioms LinearSetReconciliation327.Main.hintAxpyStmt_sem


