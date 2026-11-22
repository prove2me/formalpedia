-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintRowMatVec20261120
-- name    : LinearSetReconciliation327_Main_HintRowMatVec20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:54:33.300785+00:00
-- url     : https://prove2.me/theorems/205d5702-7a2f-4bee-bb28-5fe4656716b6
-- title:
--   LinearSetReconciliation327 — HintRowMatVec (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintRowMatVec20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowCopy20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintLoopFuel20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintMatVecProduct (width : ℕ) (f : ℕ → ℕ → ZMod 2) (g : ℕ → ZMod 2) (r : ℕ) : ZMod 2 :=
  hintDotSum (f r) g width

structure HintMatVecArgs (matrix vec output width rows j : ℕ) (state : RAMState) : Prop where
  vec_value : state.regs 4 = vec
  mat_value : state.regs 5 = matrix + j * width
  width_value : state.regs 6 = width
  stride_value : state.regs 7 = 1
  output_value : state.regs 8 = output
  rows_value : state.regs 13 = rows
  one_value : state.regs 15 = 1
  counter : state.regs 12 = j

def HintMatVecData (output width : ℕ) (f : ℕ → ℕ → ZMod 2) (g : ℕ → ZMod 2)
    (j : ℕ) (original : ℕ → ℕ) (state : RAMState) : Prop :=
  state.mem = hintCopyMem original output (hintMatVecProduct width f g) j

theorem hintCopyMem_read_frame (original : ℕ → ℕ) (dest : ℕ) (f : ℕ → ZMod 2)
    (prefixLen total addr : ℕ) (hPrefix : prefixLen ≤ total) (hOutside : addr < dest ∨ dest + total ≤ addr) :
    hintCopyMem original dest f prefixLen addr = original addr := by
  unfold hintCopyMem hintAxpyMem
  exact if_neg (by rcases hOutside with hBefore | hAfter <;> omega)

def hintMatVecPost : List Instr := [.add 3 8 12, .store 3 1, .add 5 5 6, .add 12 12 15]
def hintMatVecBody : Stmt := .seq hintDotStmt (.code hintMatVecPost)
theorem hintMatVecBody_len : hintMatVecBody.len = 17 := rfl

def hintMatVecPostResult (state : RAMState) (matrix output width j : ℕ) (value : ZMod 2) : RAMState :=
  { state with
    pc := state.pc + 4
    mem := Function.update state.mem (output + j) value.val
    regs := Function.update (Function.update (Function.update state.regs 3 (output + j))
      5 (matrix + (j + 1) * width)) 12 (j + 1) }

theorem hintMatVecPost_spec (E : RAMEnv) (state : RAMState) (matrix output width j : ℕ) (value : ZMod 2)
    (h8 : state.regs 8 = output) (h12 : state.regs 12 = j) (h5 : state.regs 5 = matrix + j * width)
    (h6 : state.regs 6 = width) (h15 : state.regs 15 = 1) (h1 : state.regs 1 = value.val)
    (hOut : output + j < 2 ^ E.W) (hNext : matrix + (j + 1) * width < 2 ^ E.W) (hCount : j + 1 < 2 ^ E.W) :
    runBlock hintMatVecPost E state = hintMatVecPostResult state matrix output width j value := by
  have hAdd : matrix + j * width + width = matrix + (j + 1) * width := by ring
  apply crState_ext
  · simp [hintMatVecPost, hintMatVecPostResult, runBlock, execInstr, Nat.add_assoc]
  · funext r
    simp [hintMatVecPost, hintMatVecPostResult, runBlock, execInstr, h8, h12, h5, h6, h15,
      Nat.mod_eq_of_lt hOut, hAdd, Nat.mod_eq_of_lt hNext, Nat.mod_eq_of_lt hCount]
  · simp [hintMatVecPost, hintMatVecPostResult, runBlock, execInstr, h8, h12, h1, Nat.mod_eq_of_lt hOut]

theorem hintMatVecBody_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (matrix vec output width rows j base : ℕ) (f : ℕ → ℕ → ZMod 2) (g : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hData : HintMatVecData output width f g j original state)
    (hArgs : HintMatVecArgs matrix vec output width rows j state) (hj : j < rows)
    (hWord : 1 < 2 ^ E.W) (hWidth : width < 2 ^ E.W) (hRows : rows < 2 ^ E.W)
    (hMatrixSpan : matrix + rows * width < 2 ^ E.W) (hVecSpan : vec + width < 2 ^ E.W)
    (hOutSpan : output + rows < 2 ^ E.W)
    (hMatrix : ∀ r < rows, ∀ t < width, original (matrix + r * width + t) = (f r t).val)
    (hVector : ∀ t < width, original (vec + t) = (g t).val)
    (hMatrixSeparate : matrix + rows * width ≤ output ∨ output + rows ≤ matrix)
    (hVecSeparate : vec + width ≤ output ∨ output + rows ≤ vec)
    (hAt : At P base (hintMatVecBody.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 17) state (fun k out => k = 11 * width + 8 ∧
      HintMatVecData output width f g (j + 1) original out ∧
      HintMatVecArgs matrix vec output width rows (j + 1) out ∧ out.regs 14 = state.regs 14) := by
  have hRowEnd : matrix + j * width + width ≤ matrix + rows * width := by
    have hMul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hj)
    simpa only [Nat.succ_mul, Nat.add_assoc] using Nat.add_le_add_left hMul matrix
  have hMatrixNow : ∀ t < width, state.mem (matrix + j * width + t * 1) = (f j t).val := by
    intro t ht
    have hOutside : matrix + j * width + t < output ∨ output + rows ≤ matrix + j * width + t := by
      rcases hMatrixSeparate with hBefore | hAfter
      · exact Or.inl (by omega)
      · exact Or.inr (hAfter.trans (by omega))
    rw [Nat.mul_one, hData, hintCopyMem_read_frame original output _ j rows _ (by omega) hOutside]
    exact hMatrix j hj t ht
  have hVectorNow : ∀ t < width, state.mem (vec + t) = (g t).val := by
    intro t ht
    have hOutside : vec + t < output ∨ output + rows ≤ vec + t := by
      rcases hVecSeparate with hBefore | hAfter
      · exact Or.inl (by omega)
      · exact Or.inr (hAfter.trans (Nat.le_add_right _ _))
    rw [hData, hintCopyMem_read_frame original output _ j rows _ (by omega) hOutside]
    exact hVector t ht
  obtain ⟨hDotAt, hPostAt⟩ := At.seqStmt hAt
  have hPostAt' : At P (base + 13) hintMatVecPost := by
    simpa only [Stmt.compile, hintDotStmt_len] using hPostAt
  have hParams : HintDotParams vec (matrix + j * width) width 1 state :=
    ⟨hArgs.vec_value, hArgs.mat_value, hArgs.width_value, hArgs.stride_value, hArgs.one_value⟩
  obtain ⟨_, kDot, mid, hRunDot, hMidPc, hCost, _, h1, hMem, hMidParams, hRegs⟩ :=
    hintDotStmt_sem P E state vec (matrix + j * width) width 1 base (f j) g hWord hWidth
      (by intro t ht; omega) (by intro t ht; simp only [Nat.mul_one]; omega)
      hMatrixNow hVectorNow hDotAt hPc hParams
  have h8 : mid.regs 8 = output := (hRegs 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hArgs.output_value
  have h12 : mid.regs 12 = j := (hRegs 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hArgs.counter
  have h13 : mid.regs 13 = rows := (hRegs 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hArgs.rows_value
  have h14 := hRegs 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hNext : matrix + (j + 1) * width < 2 ^ E.W :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right width (Nat.succ_le_of_lt hj)) matrix).trans_lt hMatrixSpan
  have hPostSpec := hintMatVecPost_spec E mid matrix output width j (hintMatVecProduct width f g j)
    h8 h12 hMidParams.mat_value hMidParams.count_value hMidParams.one_value h1 (by omega) hNext (by omega)
  let out := hintMatVecPostResult mid matrix output width j (hintMatVecProduct width f g j)
  have hRunPost : (step P E)^[4] mid = out := by
    have hAtMid : At P mid.pc hintMatVecPost := by rw [hMidPc]; exact hPostAt'
    have hh := iterate_runBlock_of_at P E hintMatVecPost mid hAtMid (by simp [hintMatVecPost, NoBranch, Instr.NoBranchI])
    simpa only [show hintMatVecPost.length = 4 from rfl, hPostSpec] using hh
  have hOutData : HintMatVecData output width f g (j + 1) original out := by
    change Function.update mid.mem (output + j) (hintMatVecProduct width f g j).val = _
    rw [hMem, hData, hintCopyMem_succ]
  have hOutArgs : HintMatVecArgs matrix vec output width rows (j + 1) out := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [out, hintMatVecPostResult] using hMidParams.vec_value
    · simp [out, hintMatVecPostResult]
    · simpa [out, hintMatVecPostResult] using hMidParams.count_value
    · simpa [out, hintMatVecPostResult] using hMidParams.stride_value
    · simpa [out, hintMatVecPostResult] using h8
    · simpa [out, hintMatVecPostResult] using h13
    · simpa [out, hintMatVecPostResult] using hMidParams.one_value
    · simp [out, hintMatVecPostResult]
  refine ⟨hPc, 4 + kDot, out, ?_, ?_, by omega, hOutData, hOutArgs, ?_⟩
  · rw [Function.iterate_add_apply, hRunDot, hRunPost]
  · change mid.pc + 4 = base + 17
    rw [hMidPc] <;> omega
  · simpa [out, hintMatVecPostResult] using h14

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

theorem hintMatVecArgs_pc {matrix vec output width rows j pc : ℕ} {state : RAMState}
    (h : HintMatVecArgs matrix vec output width rows j state) :
    HintMatVecArgs matrix vec output width rows j {state with pc := pc} :=
  ⟨h.vec_value, h.mat_value, h.width_value, h.stride_value, h.output_value, h.rows_value, h.one_value, h.counter⟩

theorem hintMatVecArgs_test {matrix vec output width rows j : ℕ} {state : RAMState}
    (E : RAMEnv) (h : HintMatVecArgs matrix vec output width rows j state) :
    HintMatVecArgs matrix vec output width rows j (runBlock (Cond.lt 2 12 13).code E state) := by
  constructor
  · simpa [Cond.code, runBlock, execInstr] using h.vec_value
  · simpa [Cond.code, runBlock, execInstr] using h.mat_value
  · simpa [Cond.code, runBlock, execInstr] using h.width_value
  · simpa [Cond.code, runBlock, execInstr] using h.stride_value
  · simpa [Cond.code, runBlock, execInstr] using h.output_value
  · simpa [Cond.code, runBlock, execInstr] using h.rows_value
  · simpa [Cond.code, runBlock, execInstr] using h.one_value
  · simpa [Cond.code, runBlock, execInstr] using h.counter

structure HintMatVecSetup (matrix vec output width rows : ℕ) (state : RAMState) : Prop where
  vec_value : state.regs 4 = vec
  mat_value : state.regs 5 = matrix
  width_value : state.regs 6 = width
  stride_value : state.regs 7 = 1
  output_value : state.regs 8 = output
  rows_value : state.regs 13 = rows
  one_value : state.regs 15 = 1

def hintMatVecStmt : Stmt := .seq (.code [.imm 12 0]) (.loop (.lt 2 12 13) hintMatVecBody)
theorem hintMatVecStmt_len : hintMatVecStmt.len = 21 := rfl

theorem hintMatVecStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (matrix vec output width rows base : ℕ) (f : ℕ → ℕ → ZMod 2) (g : ℕ → ZMod 2)
    (hWord : 1 < 2 ^ E.W) (hWidth : width < 2 ^ E.W) (hRows : rows < 2 ^ E.W)
    (hMatrixSpan : matrix + rows * width < 2 ^ E.W) (hVecSpan : vec + width < 2 ^ E.W)
    (hOutSpan : output + rows < 2 ^ E.W)
    (hMatrix : ∀ r < rows, ∀ t < width, state.mem (matrix + r * width + t) = (f r t).val)
    (hVector : ∀ t < width, state.mem (vec + t) = (g t).val)
    (hMatrixSeparate : matrix + rows * width ≤ output ∨ output + rows ≤ matrix)
    (hVecSeparate : vec + width ≤ output ∨ output + rows ≤ vec)
    (hAt : At P base (hintMatVecStmt.compile base)) (hPc : state.pc = base)
    (hSetup : HintMatVecSetup matrix vec output width rows state) :
    Sem P E base (base + 21) state (fun k out => k ≤ (11 * width + 11) * rows + 3 ∧
      out.mem = hintCopyMem state.mem output (hintMatVecProduct width f g) rows ∧
      (∀ r < rows, out.mem (output + r) = (hintMatVecProduct width f g r).val) ∧
      (∀ addr, (addr < output ∨ output + rows ≤ addr) → out.mem addr = state.mem addr) ∧
      HintMatVecArgs matrix vec output width rows rows out ∧ out.regs 14 = state.regs 14) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  let head := base + 1
  have hLoopAt' : At P head ((Stmt.loop (.lt 2 12 13) hintMatVecBody).compile head) := hLoopAt
  have hBodyAt : At P (head + 2) (hintMatVecBody.compile (head + 2)) := by
    simpa only [Cond.code, List.length_cons, List.length_nil] using (at_loop hLoopAt').2.2.1
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = rows ∧
    HintMatVecData output width f g j state.mem st ∧ HintMatVecArgs matrix vec output width rows j st ∧
    st.regs 14 = state.regs 14
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, hData, hArgs, h14⟩ := hI
    exact ⟨j, hJ, hData, hintMatVecArgs_pc hArgs, h14⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 12 13).code E st) := by
    intro left st hI
    obtain ⟨j, hJ, hData, hArgs, h14⟩ := hI
    refine ⟨j, hJ, hData, hintMatVecArgs_test E hArgs, ?_⟩
    simpa [Cond.code, runBlock, execInstr] using h14
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 12 13).eval st := by
    intro left st hI
    obtain ⟨j, hJ, _, hArgs, _⟩ := hI
    change st.regs 12 < st.regs 13
    rw [hArgs.counter, hArgs.rows_value]
    omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 12 13).eval st := by
    intro st hI
    obtain ⟨j, hJ, _, hArgs, _⟩ := hI
    change ¬ st.regs 12 < st.regs 13
    rw [hArgs.counter, hArgs.rows_value]
    omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = head + (Cond.lt 2 12 13).code.length + 1 →
      Sem P E (head + (Cond.lt 2 12 13).code.length + 1)
        (head + (Cond.lt 2 12 13).code.length + 1 + hintMatVecBody.len) st
        (fun k out => k ≤ 11 * width + 8 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, hData, hArgs, h14⟩ := hI
    have hj : j < rows := by omega
    have hNative := hintMatVecBody_sem P E st matrix vec output width rows j (head + 2) f g state.mem
      hData hArgs hj hWord hWidth hRows hMatrixSpan hVecSpan hOutSpan hMatrix hVector
      hMatrixSeparate hVecSeparate hBodyAt hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hK, hOutData, hOutArgs, hOut14⟩ := hOut
    exact ⟨hK.le, j + 1, by omega, hOutData, hOutArgs, hOut14.trans h14⟩
  let q := {state with pc := state.pc + 1, regs := Function.update state.regs 12 0}
  have hFetch : P[state.pc]? = some (.imm 12 0) := by
    have hh := hInitAt 0 (by simp [Stmt.compile])
    simpa only [Stmt.compile, List.getElem?_cons_zero, Nat.add_zero, hPc] using hh
  have hRunInit : step P E state = q := by
    rw [crStep_fetch P E state _ hFetch]
    simp only [q, execInstr, Nat.zero_mod]
  have hQData : HintMatVecData output width f g 0 state.mem q :=
    (hintCopyMem_zero state.mem output (hintMatVecProduct width f g)).symm
  have hQArgs : HintMatVecArgs matrix vec output width rows 0 q := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [q] using hSetup.vec_value
    · simpa [q] using hSetup.mat_value
    · simpa [q] using hSetup.width_value
    · simpa [q] using hSetup.stride_value
    · simpa [q] using hSetup.output_value
    · simpa [q] using hSetup.rows_value
    · simpa [q] using hSetup.one_value
    · simp [q]
  have hQI : I rows q := ⟨0, by omega, hQData, hQArgs, by simp [q]⟩
  have hQPc : q.pc = head := by change state.pc + 1 = base + 1; rw [hPc]
  obtain ⟨_, kLoop, out, hRunLoop, hOutPc, hBound, hOutI⟩ := hintLoopFuel_sem P E head (.lt 2 12 13)
    hintMatVecBody hLoopAt' hWord I (11 * width + 8) hIpc hItest hGo hStop hBody rows q hQI hQPc
  obtain ⟨j, hJ, hData, hArgs, h14⟩ := hOutI
  have hj : j = rows := by omega
  rw [hj] at hData hArgs
  have hBound' : kLoop ≤ (11 * width + 11) * rows + 2 := by
    change kLoop ≤ (1 + (11 * width + 8) + 2) * rows + 2 at hBound
    have hFactor : 1 + (11 * width + 8) + 2 = 11 * width + 11 := by omega
    simpa only [hFactor] using hBound
  refine ⟨hPc, kLoop + 1, out, ?_, ?_, by omega, hData, ?_, ?_, hArgs, h14⟩
  · rw [Function.iterate_add_apply]
    change (step P E)^[kLoop] (step P E state) = out
    rw [hRunInit, hRunLoop]
  · simpa only [head, Cond.code, List.length_cons, List.length_nil, hintMatVecBody_len, Nat.add_assoc] using hOutPc
  · intro r hr
    rw [hData]
    have hRange : output ≤ output + r ∧ output + r < output + rows :=
      ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hr output⟩
    simp only [hintCopyMem, hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, zero_mul, add_zero]
  · intro addr hOutside
    rw [hData]
    exact hintCopyMem_read_frame _ _ _ rows rows addr le_rfl hOutside

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintMatVecStmt_sem


