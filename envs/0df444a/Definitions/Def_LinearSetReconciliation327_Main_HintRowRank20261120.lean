-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintRowRank20261120
-- name    : LinearSetReconciliation327_Main_HintRowRank20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:39:38.120058+00:00
-- url     : https://prove2.me/theorems/167ecacd-7233-40e1-a1c3-fdde3f1e344f
-- title:
--   LinearSetReconciliation327 — HintRowRank (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintRowRank20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowMatrix20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- An actual RAM row update writes precisely this row of the Gaussian state. -/
theorem hintAxpyStmt_residual_row_sem {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (B : HintElimState a h) (j : Fin h) (pivot : Fin a) (row : Fin a)
    (P : Program) (E : RAMEnv) (state : RAMState) (dest src base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : a < 2 ^ E.W)
    (hDest : ∀ t < a, dest + t < 2 ^ E.W) (hSrc : ∀ t < a, src + t < 2 ^ E.W)
    (hF : ∀ t : Fin a, state.mem (dest + t.val) = (B.residual (Pi.single t 1) row).val)
    (hG : ∀ t : Fin a, state.mem (src + t.val) = (B.residual (Pi.single t 1) pivot).val)
    (hSeparate : dest + a ≤ src ∨ src + a ≤ dest)
    (hAt : At P base (hintAxpyStmt.compile base)) (hPc : state.pc = base)
    (hParams : HintAxpyParams dest src a (B.residual (A (Pi.single j 1)) row) state) :
    Sem P E base (base + 13) state (fun k out => k = 11 * a + 4 ∧
      (∀ t : Fin a, out.mem (dest + t.val) = ((hintElimInsert A B j pivot).residual (Pi.single t 1) row).val) ∧
      (∀ addr, (addr < dest ∨ dest + a ≤ addr) → out.mem addr = state.mem addr) ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = state.regs r)) := by
  have hMatrix : ∀ t < a, state.mem (dest + t) = (hintDenseRow B.residual row t).val := by
    intro t ht
    simpa only [hintDenseRow, dif_pos ht] using hF ⟨t, ht⟩
  have hPivot : ∀ t < a, state.mem (src + t) = (hintDenseRow B.residual pivot t).val := by
    intro t ht
    simpa only [hintDenseRow, dif_pos ht] using hG ⟨t, ht⟩
  have hUpdate := hintAxpyStmt_sem P E state dest src a base (B.residual (A (Pi.single j 1)) row)
    (hintDenseRow B.residual row) (hintDenseRow B.residual pivot)
    hWord hCount hDest hSrc hMatrix hPivot hSeparate hAt hPc hParams
  apply Sem.mono hUpdate
  intro k out hOut
  obtain ⟨hK, _, hMem, _, hFrame, hRegs⟩ := hOut
  refine ⟨hK, ?_, hFrame, hRegs⟩
  intro t
  have hRange : dest ≤ dest + t.val ∧ dest + t.val < dest + a :=
    ⟨Nat.le_add_right _ _, Nat.add_lt_add_left t.isLt dest⟩
  rw [hMem, hintElimInsert_residual_coefficient]
  simp only [hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, hintDenseRow, dif_pos t.isLt]

/-- An actual RAM row update writes precisely this row of the Gaussian state. -/
theorem hintAxpyStmt_lift_row_sem {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (B : HintElimState a h) (j : Fin h) (pivot : Fin a) (row : Fin h)
    (P : Program) (E : RAMEnv) (state : RAMState) (dest src base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : a < 2 ^ E.W)
    (hDest : ∀ t < a, dest + t < 2 ^ E.W) (hSrc : ∀ t < a, src + t < 2 ^ E.W)
    (hF : ∀ t : Fin a, state.mem (dest + t.val) = (B.lift (Pi.single t 1) row).val)
    (hG : ∀ t : Fin a, state.mem (src + t.val) = (B.residual (Pi.single t 1) pivot).val)
    (hSeparate : dest + a ≤ src ∨ src + a ≤ dest)
    (hAt : At P base (hintAxpyStmt.compile base)) (hPc : state.pc = base)
    (hParams : HintAxpyParams dest src a (hintElimKernel A B j row) state) :
    Sem P E base (base + 13) state (fun k out => k = 11 * a + 4 ∧
      (∀ t : Fin a, out.mem (dest + t.val) = ((hintElimInsert A B j pivot).lift (Pi.single t 1) row).val) ∧
      (∀ addr, (addr < dest ∨ dest + a ≤ addr) → out.mem addr = state.mem addr) ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = state.regs r)) := by
  have hMatrix : ∀ t < a, state.mem (dest + t) = (hintDenseRow B.lift row t).val := by
    intro t ht
    simpa only [hintDenseRow, dif_pos ht] using hF ⟨t, ht⟩
  have hPivot : ∀ t < a, state.mem (src + t) = (hintDenseRow B.residual pivot t).val := by
    intro t ht
    simpa only [hintDenseRow, dif_pos ht] using hG ⟨t, ht⟩
  have hUpdate := hintAxpyStmt_sem P E state dest src a base (hintElimKernel A B j row)
    (hintDenseRow B.lift row) (hintDenseRow B.residual pivot)
    hWord hCount hDest hSrc hMatrix hPivot hSeparate hAt hPc hParams
  apply Sem.mono hUpdate
  intro k out hOut
  obtain ⟨hK, _, hMem, _, hFrame, hRegs⟩ := hOut
  refine ⟨hK, ?_, hFrame, hRegs⟩
  intro t
  have hRange : dest ≤ dest + t.val ∧ dest + t.val < dest + a :=
    ⟨Nat.le_add_right _ _, Nat.add_lt_add_left t.isLt dest⟩
  rw [hMem, hintElimInsert_lift_coefficient]
  simp only [hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, hintDenseRow, dif_pos t.isLt]

end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintMatrix_other_row (matrix width i j t : ℕ) (ht : t < width) (hNe : i ≠ j) :
    matrix + i * width + t < matrix + j * width ∨
      matrix + j * width + width ≤ matrix + i * width + t := by
  rcases lt_or_gt_of_ne hNe with hij | hji
  · have hMul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hij)
    rw [Nat.succ_mul] at hMul
    exact Or.inl (by omega)
  · have hMul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hji)
    rw [Nat.succ_mul] at hMul
    exact Or.inr (by omega)

structure HintRankOneData (matrix width rows : ℕ) (scale : ℕ → ZMod 2)
    (f : ℕ → ℕ → ZMod 2) (g : ℕ → ZMod 2) (k : ℕ) (original : ℕ → ℕ) (p : RAMState) : Prop where
  cells : ∀ r < rows, ∀ t < width, p.mem (matrix + r * width + t) =
    if r < k then (f r t + scale r * g t).val else (f r t).val
  frame : CRMemFrame matrix (matrix + rows * width) original p.mem

/-- Updating one actual matrix row advances the whole-matrix invariant. The
    other matrix rows and every address outside the matrix retain their data. -/
theorem hintRankOne_row_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (matrix src width rows j base : ℕ) (scale : ℕ → ZMod 2)
    (f : ℕ → ℕ → ZMod 2) (g : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hData : HintRankOneData matrix width rows scale f g j original state) (hj : j < rows)
    (hWord : 1 < 2 ^ E.W) (hWidth : width < 2 ^ E.W)
    (hMatrixSpan : matrix + rows * width < 2 ^ E.W) (hSrcSpan : src + width < 2 ^ E.W)
    (hCache : ∀ t < width, original (src + t) = (g t).val)
    (hSeparate : matrix + rows * width ≤ src ∨ src + width ≤ matrix)
    (hAt : At P base (hintAxpyStmt.compile base)) (hPc : state.pc = base)
    (hParams : HintAxpyParams (matrix + j * width) src width (scale j) state) :
    Sem P E base (base + 13) state (fun k out => k = 11 * width + 4 ∧
      HintRankOneData matrix width rows scale f g (j + 1) original out ∧
      HintAxpyParams (matrix + j * width) src width (scale j) out ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = state.regs r)) := by
  have hRowEnd : matrix + j * width + width ≤ matrix + rows * width := by
    have hMul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hj)
    simpa only [Nat.succ_mul, Nat.add_assoc] using Nat.add_le_add_left hMul matrix
  have hDest : ∀ t < width, matrix + j * width + t < 2 ^ E.W := by
    intro t ht
    omega
  have hSrc : ∀ t < width, src + t < 2 ^ E.W := by
    intro t ht
    omega
  have hF : ∀ t < width, state.mem (matrix + j * width + t) = (f j t).val := by
    intro t ht
    simpa only [lt_self_iff_false, if_false] using hData.cells j hj t ht
  have hG : ∀ t < width, state.mem (src + t) = (g t).val := by
    intro t ht
    have hOutside : src + t < matrix ∨ matrix + rows * width ≤ src + t := by
      rcases hSeparate with hAbove | hBelow
      · exact Or.inr (hAbove.trans (Nat.le_add_right _ _))
      · exact Or.inl ((Nat.add_lt_add_left ht src).trans_le hBelow)
    exact (hData.frame (src + t) hOutside).trans (hCache t ht)
  have hSeparateRow : matrix + j * width + width ≤ src ∨ src + width ≤ matrix + j * width := by
    rcases hSeparate with hAbove | hBelow
    · exact Or.inl (hRowEnd.trans hAbove)
    · exact Or.inr (hBelow.trans (Nat.le_add_right _ _))
  have hUpdate := hintAxpyStmt_sem P E state (matrix + j * width) src width base (scale j) (f j) g
    hWord hWidth hDest hSrc hF hG hSeparateRow hAt hPc hParams
  apply Sem.mono hUpdate
  intro k out hOut
  obtain ⟨hK, _, hMem, hArgs, hFrame, hRegs⟩ := hOut
  refine ⟨hK, ⟨?_, ?_⟩, hArgs, hRegs⟩
  · intro r hr t ht
    by_cases hEq : r = j
    · subst r
      have hRange : matrix + j * width ≤ matrix + j * width + t ∧
          matrix + j * width + t < matrix + j * width + width :=
        ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ht _⟩
      rw [hMem]
      simp only [hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, Nat.lt_succ_self, if_true]
    · have hOutside := hintMatrix_other_row matrix width r j t ht hEq
      rw [hFrame _ hOutside]
      have hIff : (r < j) ↔ (r < j + 1) := by omega
      simpa only [hIff] using hData.cells r hr t ht
  · intro addr hOutside
    have hOutsideRow : addr < matrix + j * width ∨ matrix + j * width + width ≤ addr := by
      rcases hOutside with hBefore | hAfter
      · exact Or.inl (hBefore.trans_le (Nat.le_add_right _ _))
      · exact Or.inr (hRowEnd.trans hAfter)
    exact (hFrame addr hOutsideRow).trans (hData.frame addr hOutside)

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

structure HintRankOneArgs (matrix src scales width rows j : ℕ) (p : RAMState) : Prop where
  dest_value : p.regs 4 = matrix + j * width
  src_value : p.regs 5 = src
  width_value : p.regs 6 = width
  scales_value : p.regs 7 = scales
  rows_value : p.regs 13 = rows
  one_value : p.regs 15 = 1
  counter : p.regs 12 = j

def hintRankLoad : List Instr := [.add 3 7 12, .load 8 3]
def hintRankPost : List Instr := [.add 4 4 6, .add 12 12 15]
def hintRankOneBody : Stmt := .seq (.code hintRankLoad) (.seq hintAxpyStmt (.code hintRankPost))
theorem hintRankOneBody_len : hintRankOneBody.len = 17 := rfl

def hintRankLoadResult (p : RAMState) (scales j : ℕ) (value : ZMod 2) : RAMState :=
  {p with pc := p.pc + 2, regs := Function.update (Function.update p.regs 3 (scales + j)) 8 value.val}

def hintRankPostResult (p : RAMState) (matrix width j : ℕ) : RAMState :=
  {p with pc := p.pc + 2, regs := Function.update (Function.update p.regs 4 (matrix + (j + 1) * width)) 12 (j + 1)}

theorem hintRankLoad_spec (E : RAMEnv) (p : RAMState) (scales j : ℕ) (value : ZMod 2)
    (h7 : p.regs 7 = scales) (h12 : p.regs 12 = j) (hSpan : scales + j < 2 ^ E.W)
    (hWord : 1 < 2 ^ E.W) (hValue : p.mem (scales + j) = value.val) :
    runBlock hintRankLoad E p = hintRankLoadResult p scales j value := by
  have hValueBound := (ZMod.val_lt value).trans_le hWord
  apply crState_ext
  · simp [hintRankLoad, hintRankLoadResult, runBlock, execInstr, Nat.add_assoc]
  · funext r
    simp [hintRankLoad, hintRankLoadResult, runBlock, execInstr, h7, h12, Nat.mod_eq_of_lt hSpan,
      hValue, Nat.mod_eq_of_lt hValueBound]
  · rfl

theorem hintRankPost_spec (E : RAMEnv) (p : RAMState) (matrix width j : ℕ)
    (h4 : p.regs 4 = matrix + j * width) (h6 : p.regs 6 = width)
    (h12 : p.regs 12 = j) (h15 : p.regs 15 = 1)
    (hNext : matrix + (j + 1) * width < 2 ^ E.W) (hCount : j + 1 < 2 ^ E.W) :
    runBlock hintRankPost E p = hintRankPostResult p matrix width j := by
  have hAdd : matrix + j * width + width = matrix + (j + 1) * width := by
    ring
  apply crState_ext
  · simp [hintRankPost, hintRankPostResult, runBlock, execInstr, Nat.add_assoc]
  · funext r
    simp [hintRankPost, hintRankPostResult, runBlock, execInstr, h4, h6, h12, h15, hAdd,
      Nat.mod_eq_of_lt hNext, Nat.mod_eq_of_lt hCount]
  · rfl

theorem hintRankOneData_mem {matrix width rows k : ℕ} {scale : ℕ → ZMod 2}
    {f : ℕ → ℕ → ZMod 2} {g : ℕ → ZMod 2} {original : ℕ → ℕ} {p q : RAMState}
    (hData : HintRankOneData matrix width rows scale f g k original p) (hMem : q.mem = p.mem) :
    HintRankOneData matrix width rows scale f g k original q := by
  constructor
  · intro r hr t ht
    rw [hMem]
    exact hData.cells r hr t ht
  · intro addr hOutside
    rw [hMem]
    exact hData.frame addr hOutside

theorem hintRankOneBody_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (matrix src scales width rows j base : ℕ) (scale : ℕ → ZMod 2)
    (f : ℕ → ℕ → ZMod 2) (g : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hData : HintRankOneData matrix width rows scale f g j original state)
    (hArgs : HintRankOneArgs matrix src scales width rows j state) (hj : j < rows)
    (hWord : 1 < 2 ^ E.W) (hWidth : width < 2 ^ E.W) (hRows : rows < 2 ^ E.W)
    (hMatrixSpan : matrix + rows * width < 2 ^ E.W) (hSrcSpan : src + width < 2 ^ E.W)
    (hScaleSpan : scales + rows < 2 ^ E.W)
    (hCache : ∀ t < width, original (src + t) = (g t).val)
    (hScale : ∀ r < rows, original (scales + r) = (scale r).val)
    (hSeparate : matrix + rows * width ≤ src ∨ src + width ≤ matrix)
    (hScaleSeparate : matrix + rows * width ≤ scales ∨ scales + rows ≤ matrix)
    (hAt : At P base (hintRankOneBody.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 17) state (fun k out => k = 11 * width + 8 ∧
      HintRankOneData matrix width rows scale f g (j + 1) original out ∧
      HintRankOneArgs matrix src scales width rows (j + 1) out ∧ out.regs 14 = state.regs 14) := by
  obtain ⟨hLoadAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hRowAt, hPostAt⟩ := At.seqStmt hRestAt
  have hRowAt' : At P (base + 2) (hintAxpyStmt.compile (base + 2)) := hRowAt
  have hPostAt' : At P (base + 15) hintRankPost := by
    simpa only [Stmt.len, Stmt.compile, hintAxpyStmt_len, hintRankLoad, List.length_cons, List.length_nil, Nat.add_assoc] using hPostAt
  have hScaleOutside : scales + j < matrix ∨ matrix + rows * width ≤ scales + j := by
    rcases hScaleSeparate with hAbove | hBelow
    · exact Or.inr (hAbove.trans (Nat.le_add_right _ _))
    · exact Or.inl ((Nat.add_lt_add_left hj scales).trans_le hBelow)
  have hValue := (hData.frame (scales + j) hScaleOutside).trans (hScale j hj)
  have hLoadSpec := hintRankLoad_spec E state scales j (scale j) hArgs.scales_value hArgs.counter
    (by omega) hWord hValue
  let q := hintRankLoadResult state scales j (scale j)
  have hRunLoad : (step P E)^[2] state = q := by
    have hLoadAtState : At P state.pc hintRankLoad := by rw [hPc]; exact hLoadAt
    have hExec := iterate_runBlock_of_at P E hintRankLoad state hLoadAtState (by simp [hintRankLoad, NoBranch, Instr.NoBranchI])
    simpa only [show hintRankLoad.length = 2 from rfl, hLoadSpec] using hExec
  have hQData : HintRankOneData matrix width rows scale f g j original q := hintRankOneData_mem hData rfl
  have hQParams : HintAxpyParams (matrix + j * width) src width (scale j) q := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [q, hintRankLoadResult] using hArgs.dest_value
    · simpa [q, hintRankLoadResult] using hArgs.src_value
    · simpa [q, hintRankLoadResult] using hArgs.width_value
    · simp [q, hintRankLoadResult]
    · simpa [q, hintRankLoadResult] using hArgs.one_value
  have hQPc : q.pc = base + 2 := by change state.pc + 2 = _; rw [hPc]
  obtain ⟨_, kRow, mid, hRunRow, hMidPc, hCost, hMidData, hMidArgs, hRegs⟩ :=
    hintRankOne_row_sem P E q matrix src width rows j (base + 2) scale f g original hQData hj
      hWord hWidth hMatrixSpan hSrcSpan hCache hSeparate hRowAt' hQPc hQParams
  have h12 : mid.regs 12 = j := (hRegs 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (by simpa [q, hintRankLoadResult] using hArgs.counter)
  have h7 : mid.regs 7 = scales := (hRegs 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (by simpa [q, hintRankLoadResult] using hArgs.scales_value)
  have h13 : mid.regs 13 = rows := (hRegs 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (by simpa [q, hintRankLoadResult] using hArgs.rows_value)
  have h14 : mid.regs 14 = state.regs 14 := (hRegs 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (by simp [q, hintRankLoadResult])
  have hNext : matrix + (j + 1) * width < 2 ^ E.W := by
    have hMul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hj)
    exact (Nat.add_le_add_left hMul matrix).trans_lt hMatrixSpan
  have hPostSpec := hintRankPost_spec E mid matrix width j hMidArgs.dest_value hMidArgs.count_value h12
    hMidArgs.one_value hNext (by omega)
  let out := hintRankPostResult mid matrix width j
  have hRunPost : (step P E)^[2] mid = out := by
    have hPostAtMid : At P mid.pc hintRankPost := by
      rw [hMidPc]
      simpa only [Nat.add_assoc] using hPostAt'
    have hExec := iterate_runBlock_of_at P E hintRankPost mid hPostAtMid (by simp [hintRankPost, NoBranch, Instr.NoBranchI])
    simpa only [show hintRankPost.length = 2 from rfl, hPostSpec] using hExec
  have hOutArgs : HintRankOneArgs matrix src scales width rows (j + 1) out := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [out, hintRankPostResult]
    · simpa [out, hintRankPostResult] using hMidArgs.src_value
    · simpa [out, hintRankPostResult] using hMidArgs.count_value
    · simpa [out, hintRankPostResult] using h7
    · simpa [out, hintRankPostResult] using h13
    · simpa [out, hintRankPostResult] using hMidArgs.one_value
    · simp [out, hintRankPostResult]
  refine ⟨hPc, (2 + kRow) + 2, out, ?_, ?_, by omega, hintRankOneData_mem hMidData rfl, hOutArgs, ?_⟩
  · rw [Function.iterate_add_apply, hRunLoad, Function.iterate_add_apply, hRunRow, hRunPost]
  · change mid.pc + 2 = base + 17
    rw [hMidPc] <;> omega
  · simpa [out, hintRankPostResult] using h14

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

theorem hintRankOneArgs_pc {matrix src scales width rows j pc : ℕ} {state : RAMState}
    (h : HintRankOneArgs matrix src scales width rows j state) :
    HintRankOneArgs matrix src scales width rows j {state with pc := pc} :=
  ⟨h.dest_value, h.src_value, h.width_value, h.scales_value, h.rows_value, h.one_value, h.counter⟩

theorem hintRankOneArgs_test {matrix src scales width rows j pc : ℕ} {state : RAMState}
    (E : RAMEnv) (h : HintRankOneArgs matrix src scales width rows j state) :
    HintRankOneArgs matrix src scales width rows j
      {runBlock (Cond.lt 2 12 13).code E state with pc := pc} := by
  constructor
  · simpa [Cond.code, runBlock, execInstr] using h.dest_value
  · simpa [Cond.code, runBlock, execInstr] using h.src_value
  · simpa [Cond.code, runBlock, execInstr] using h.width_value
  · simpa [Cond.code, runBlock, execInstr] using h.scales_value
  · simpa [Cond.code, runBlock, execInstr] using h.rows_value
  · simpa [Cond.code, runBlock, execInstr] using h.one_value
  · simpa [Cond.code, runBlock, execInstr] using h.counter

theorem hintRankOneLoop_sem (P : Program) (E : RAMEnv)
    (matrix src scales width rows head : ℕ) (scale : ℕ → ZMod 2)
    (f : ℕ → ℕ → ZMod 2) (g : ℕ → ZMod 2) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hWidth : width < 2 ^ E.W) (hRows : rows < 2 ^ E.W)
    (hMatrixSpan : matrix + rows * width < 2 ^ E.W) (hSrcSpan : src + width < 2 ^ E.W)
    (hScaleSpan : scales + rows < 2 ^ E.W)
    (hCache : ∀ t < width, original (src + t) = (g t).val)
    (hScale : ∀ r < rows, original (scales + r) = (scale r).val)
    (hSeparate : matrix + rows * width ≤ src ∨ src + width ≤ matrix)
    (hScaleSeparate : matrix + rows * width ≤ scales ∨ scales + rows ≤ matrix)
    (hAt : At P head ((Stmt.loop (.lt 2 12 13) hintRankOneBody).compile head)) :
    ∀ (left j : ℕ) (state : RAMState), j + left = rows → state.pc = head →
      HintRankOneData matrix width rows scale f g j original state →
      HintRankOneArgs matrix src scales width rows j state →
      Sem P E head (head + 20) state (fun k out => k ≤ (11 * width + 11) * left + 2 ∧
        HintRankOneData matrix width rows scale f g rows original out ∧
        HintRankOneArgs matrix src scales width rows rows out ∧ out.regs 14 = state.regs 14) := by
  intro left
  induction left with
  | zero =>
      intro j state hJ hPc hData hArgs
      have hj : j = rows := by omega
      rw [hj] at hData hArgs
      have hStop : ¬ (Cond.lt 2 12 13).eval state := by
        simp only [Cond.eval, hArgs.counter, hArgs.rows_value, lt_self_iff_false, not_false_eq_true]
      have hExit := Sem.loopExit P E head (.lt 2 12 13) hintRankOneBody state hAt hWord hPc hStop
      have hExit' : Sem P E head (head + 20) state
          (fun k out => k = 2 ∧ out = {runBlock (Cond.lt 2 12 13).code E state with pc := head + 20}) := by
        simpa only [Cond.code, List.length_cons, List.length_nil, hintRankOneBody_len, Nat.add_assoc] using hExit
      apply Sem.mono hExit'
      intro k out hOut
      obtain ⟨hK, rfl⟩ := hOut
      refine ⟨by omega, hintRankOneData_mem hData rfl, hintRankOneArgs_test E hArgs, ?_⟩
      simp [Cond.code, runBlock, execInstr]
  | succ left ih =>
      intro j state hJ hPc hData hArgs
      have hj : j < rows := by omega
      have hGo : (Cond.lt 2 12 13).eval state := by
        simpa only [Cond.eval, hArgs.counter, hArgs.rows_value] using hj
      let q := {runBlock (Cond.lt 2 12 13).code E state with pc := head + 2}
      have hQData : HintRankOneData matrix width rows scale f g j original q := hintRankOneData_mem hData rfl
      have hQArgs : HintRankOneArgs matrix src scales width rows j q := hintRankOneArgs_test E hArgs
      have hParts := at_loop hAt
      have hBodyAt : At P (head + 2) (hintRankOneBody.compile (head + 2)) := by
        simpa only [Cond.code, List.length_cons, List.length_nil] using hParts.2.2.1
      obtain ⟨_, kBody, mid, hRunBody, hMidPc, hCost, hMidData, hMidArgs, hMid14⟩ :=
        hintRankOneBody_sem P E q matrix src scales width rows j (head + 2) scale f g original
          hQData hQArgs hj hWord hWidth hRows hMatrixSpan hSrcSpan hScaleSpan hCache hScale hSeparate
          hScaleSeparate hBodyAt rfl
      have hJump : P[mid.pc]? = some (.jmp head) := by
        rw [hMidPc]
        simpa only [Cond.code, List.length_cons, List.length_nil, hintRankOneBody_len, Nat.add_assoc] using hParts.2.2.2
      let returned := {mid with pc := head}
      have hRunJump : step P E mid = returned := by
        rw [crStep_fetch P E mid _ hJump]
        rfl
      have hBodyReturn : Sem P E (head + (Cond.lt 2 12 13).code.length + 1) head
          {runBlock (Cond.lt 2 12 13).code E state with pc := head + (Cond.lt 2 12 13).code.length + 1}
          (fun k out => k = kBody + 1 ∧ out = returned) := by
        refine ⟨rfl, kBody + 1, returned, ?_, rfl, rfl, rfl⟩
        rw [show kBody + 1 = 1 + kBody by omega, Function.iterate_add_apply]
        change step P E ((step P E)^[kBody] q) = returned
        rw [hRunBody, hRunJump]
      have hStep := Sem.loopStep P E head (.lt 2 12 13) hintRankOneBody state returned (kBody + 1)
        hAt hWord hPc hGo hBodyReturn
      have hStep' : Sem P E head head state (fun k out => k ≤ 11 * width + 11 ∧ out = returned) := by
        apply Sem.mono hStep
        intro k out hOut
        have hK : k = 2 + (kBody + 1) := hOut.1
        exact ⟨by omega, hOut.2⟩
      have hReturnedData : HintRankOneData matrix width rows scale f g (j + 1) original returned :=
        hintRankOneData_mem hMidData rfl
      have hReturnedArgs : HintRankOneArgs matrix src scales width rows (j + 1) returned :=
        hintRankOneArgs_pc hMidArgs
      have hRest := ih (j + 1) returned (by omega) rfl hReturnedData hReturnedArgs
      have hReturn14 : returned.regs 14 = state.regs 14 := by
        change mid.regs 14 = state.regs 14
        exact hMid14.trans (by simp [q, Cond.code, runBlock, execInstr])
      have hRest' : Sem P E head (head + 20) returned (fun k out =>
          k ≤ (11 * width + 11) * left + 2 ∧
          HintRankOneData matrix width rows scale f g rows original out ∧
          HintRankOneArgs matrix src scales width rows rows out ∧ out.regs 14 = state.regs 14) := by
        apply Sem.mono hRest
        intro k out hOut
        exact ⟨hOut.1, hOut.2.1, hOut.2.2.1, hOut.2.2.2.trans hReturn14⟩
      have hCombined := Sem.seq_bound hStep' (fun next hNextPc hNextEq => by
        rw [hNextEq]
        exact hRest')
      apply Sem.mono hCombined
      intro k out hOut
      refine ⟨?_, hOut.2⟩
      rw [Nat.mul_succ]
      omega

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

structure HintRankOneSetup (matrix src scales width rows : ℕ) (state : RAMState) : Prop where
  dest_value : state.regs 4 = matrix
  src_value : state.regs 5 = src
  width_value : state.regs 6 = width
  scales_value : state.regs 7 = scales
  rows_value : state.regs 13 = rows
  one_value : state.regs 15 = 1

def hintRankOneStmt : Stmt := .seq (.code [.imm 12 0]) (.loop (.lt 2 12 13) hintRankOneBody)
theorem hintRankOneStmt_len : hintRankOneStmt.len = 21 := rfl

/-- A native rank-one update of an entire dense binary matrix. The cached row
    and coefficient vector stay read-only; register14 retains caller context. -/
theorem hintRankOneStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (matrix src scales width rows base : ℕ) (scale : ℕ → ZMod 2)
    (f : ℕ → ℕ → ZMod 2) (g : ℕ → ZMod 2)
    (hWord : 1 < 2 ^ E.W) (hWidth : width < 2 ^ E.W) (hRows : rows < 2 ^ E.W)
    (hMatrixSpan : matrix + rows * width < 2 ^ E.W) (hSrcSpan : src + width < 2 ^ E.W)
    (hScaleSpan : scales + rows < 2 ^ E.W)
    (hMatrix : ∀ r < rows, ∀ t < width, state.mem (matrix + r * width + t) = (f r t).val)
    (hCache : ∀ t < width, state.mem (src + t) = (g t).val)
    (hScale : ∀ r < rows, state.mem (scales + r) = (scale r).val)
    (hSeparate : matrix + rows * width ≤ src ∨ src + width ≤ matrix)
    (hScaleSeparate : matrix + rows * width ≤ scales ∨ scales + rows ≤ matrix)
    (hAt : At P base (hintRankOneStmt.compile base)) (hPc : state.pc = base)
    (hSetup : HintRankOneSetup matrix src scales width rows state) :
    Sem P E base (base + 21) state (fun k out => k ≤ (11 * width + 11) * rows + 3 ∧
      (∀ r < rows, ∀ t < width, out.mem (matrix + r * width + t) = (f r t + scale r * g t).val) ∧
      CRMemFrame matrix (matrix + rows * width) state.mem out.mem ∧
      HintRankOneArgs matrix src scales width rows rows out ∧ out.regs 14 = state.regs 14) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  have hLoopAt' : At P (base + 1) ((Stmt.loop (.lt 2 12 13) hintRankOneBody).compile (base + 1)) := hLoopAt
  let q := {state with pc := state.pc + 1, regs := Function.update state.regs 12 0}
  have hFetch : P[state.pc]? = some (.imm 12 0) := by
    have hh := hInitAt 0 (by simp [Stmt.compile])
    simpa only [Stmt.compile, List.getElem?_cons_zero, Nat.add_zero, hPc] using hh
  have hRunInit : step P E state = q := by
    rw [crStep_fetch P E state _ hFetch]
    simp only [q, execInstr, Nat.zero_mod]
  have hQData : HintRankOneData matrix width rows scale f g 0 state.mem q := by
    constructor
    · intro r hr t ht
      simpa only [q, Nat.not_lt_zero, if_false] using hMatrix r hr t ht
    · exact crMemFrame_refl _ _ _
  have hQArgs : HintRankOneArgs matrix src scales width rows 0 q := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [q] using hSetup.dest_value
    · simpa [q] using hSetup.src_value
    · simpa [q] using hSetup.width_value
    · simpa [q] using hSetup.scales_value
    · simpa [q] using hSetup.rows_value
    · simpa [q] using hSetup.one_value
    · simp [q]
  have hQPc : q.pc = base + 1 := by change state.pc + 1 = _; rw [hPc]
  obtain ⟨_, kLoop, out, hRunLoop, hOutPc, hBound, hData, hArgs, h14⟩ :=
    hintRankOneLoop_sem P E matrix src scales width rows (base + 1) scale f g state.mem
      hWord hWidth hRows hMatrixSpan hSrcSpan hScaleSpan hCache hScale hSeparate hScaleSeparate
      hLoopAt' rows 0 q (by omega) hQPc hQData hQArgs
  refine ⟨hPc, kLoop + 1, out, ?_, ?_, by omega, ?_, hData.frame, hArgs, ?_⟩
  · rw [Function.iterate_add_apply]
    change (step P E)^[kLoop] (step P E state) = out
    rw [hRunInit, hRunLoop]
  · simpa only [Nat.add_assoc] using hOutPc
  · intro r hr t ht
    simpa only [if_pos hr] using hData.cells r hr t ht
  · exact h14.trans (by simp [q])

end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.hintRankOneStmt_sem


