-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintGaussInit20261120
-- name    : LinearSetReconciliation327_Main_HintGaussInit20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:39:46.876253+00:00
-- url     : https://prove2.me/theorems/f2c3a563-1886-4704-8d12-fe710ff2b05b
-- title:
--   LinearSetReconciliation327 — HintGaussInit (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintGaussInit20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowFill20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintRowMatrix20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintInitRegs (lift rows hints context : ℕ) (state : RAMState) : Prop where
  hints_value : state.regs 11 = hints
  lift_value : state.regs 12 = lift
  rows_value : state.regs 13 = rows
  context_value : state.regs 14 = context

def hintInitSetup0 : List Instr := [.imm 7 1, .imm 8 0, .mul 6 13 13, .imm 15 1]
def hintInitSetup1 : List Instr := [.imm 3 0, .add 6 13 3, .add 7 13 15, .imm 8 1]
def hintInitSetup2 : List Instr := [.imm 3 0, .add 4 12 3, .mul 6 13 11, .imm 7 1, .imm 8 0]

theorem hintInitSetup0_spec (E : RAMEnv) (state : RAMState) (residual lift rows hints context : ℕ)
    (hRegs : HintInitRegs lift rows hints context state) (hDest : state.regs 4 = residual)
    (hWord : 1 < 2 ^ E.W) (hSquare : rows * rows < 2 ^ E.W) :
    let out := runBlock hintInitSetup0 E state
    HintFillParams residual 1 (rows * rows) 0 out ∧ HintInitRegs lift rows hints context out ∧ out.mem = state.mem := by
  obtain ⟨h11, h12, h13, h14⟩ := hRegs
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [hintInitSetup0, runBlock, execInstr, hDest, h11, h12, h13, h14,
      Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hSquare]

theorem hintInitSetup1_spec (E : RAMEnv) (state : RAMState) (residual lift rows hints context : ℕ)
    (hRegs : HintInitRegs lift rows hints context state) (hDest : state.regs 4 = residual)
    (hOne : state.regs 15 = 1) (hWord : 1 < 2 ^ E.W) (hRows : rows + 1 < 2 ^ E.W) :
    let out := runBlock hintInitSetup1 E state
    HintFillParams residual (rows + 1) rows 1 out ∧ HintInitRegs lift rows hints context out ∧ out.mem = state.mem := by
  have hCount : rows < 2 ^ E.W := by omega
  obtain ⟨h11, h12, h13, h14⟩ := hRegs
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [hintInitSetup1, runBlock, execInstr, hDest, hOne, h11, h12, h13, h14,
      Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hCount, Nat.mod_eq_of_lt hRows,
      show (1 : ZMod 2).val = 1 from rfl]

theorem hintInitSetup2_spec (E : RAMEnv) (state : RAMState) (lift rows hints context : ℕ)
    (hRegs : HintInitRegs lift rows hints context state) (hOne : state.regs 15 = 1)
    (hWord : 1 < 2 ^ E.W) (hLift : lift < 2 ^ E.W) (hProduct : hints * rows < 2 ^ E.W) :
    let out := runBlock hintInitSetup2 E state
    HintFillParams lift 1 (hints * rows) 0 out ∧ HintInitRegs lift rows hints context out ∧ out.mem = state.mem := by
  obtain ⟨h11, h12, h13, h14⟩ := hRegs
  have hProduct' : rows * hints < 2 ^ E.W := by simpa only [Nat.mul_comm] using hProduct
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [hintInitSetup2, runBlock, execInstr, hOne, h11, h12, h13, h14,
      Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hLift, Nat.mod_eq_of_lt hProduct', Nat.mul_comm]

theorem HintInitRegs.of_frame {lift rows hints context : ℕ} {state out : RAMState}
    (h : HintInitRegs lift rows hints context state)
    (hFrame : ∀ r, r ≠ 0 → r ≠ 2 → r ≠ 3 → out.regs r = state.regs r) :
    HintInitRegs lift rows hints context out := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hFrame 11 (by decide) (by decide) (by decide)).trans h.hints_value
  · exact (hFrame 12 (by decide) (by decide) (by decide)).trans h.lift_value
  · exact (hFrame 13 (by decide) (by decide) (by decide)).trans h.rows_value
  · exact (hFrame 14 (by decide) (by decide) (by decide)).trans h.context_value

def hintElimInitStmt : Stmt := .seq (.code hintInitSetup0)
  (.seq hintFillStmt (.seq (.code hintInitSetup1) (.seq hintFillStmt (.seq (.code hintInitSetup2) hintFillStmt))))
theorem hintElimInitStmt_len : hintElimInitStmt.len = 37 := rfl

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintElimInitMem (original : ℕ → ℕ) (residual lift rows hints : ℕ) : ℕ → ℕ :=
  hintFillMem (hintFillMem (hintFillMem original residual 1 (rows * rows) 0)
    residual (rows + 1) rows 1) lift 1 (hints * rows) 0

theorem hintIterate_then {α : Type*} (f : α → α) {s t u : α} {a b : ℕ}
    (ha : f^[a] s = t) (hb : f^[b] t = u) : f^[b + a] s = u := by
  rw [Function.iterate_add_apply, ha, hb]

theorem hintElimInitStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (residual lift rows hints context base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hRows : rows + 1 < 2 ^ E.W)
    (hSquare : rows * rows < 2 ^ E.W) (hProduct : hints * rows < 2 ^ E.W)
    (hResidualSpan : residual + rows * rows < 2 ^ E.W)
    (hLiftSpan : lift + hints * rows < 2 ^ E.W)
    (hAt : At P base (hintElimInitStmt.compile base)) (hPc : state.pc = base)
    (hRegs : HintInitRegs lift rows hints context state) (hDest : state.regs 4 = residual) :
    Sem P E base (base + 37) state (fun k out => k = 7 * (rows * rows + rows + hints * rows) + 22 ∧
      out.mem = hintElimInitMem state.mem residual lift rows hints ∧
      HintInitRegs lift rows hints context out ∧ out.regs 15 = 1) := by
  obtain ⟨hA0, hRest0⟩ := At.seqStmt hAt
  obtain ⟨hF0, hRest1⟩ := At.seqStmt hRest0
  obtain ⟨hA1, hRest2⟩ := At.seqStmt hRest1
  obtain ⟨hF1, hRest3⟩ := At.seqStmt hRest2
  obtain ⟨hA2, hF2⟩ := At.seqStmt hRest3
  change At P base hintInitSetup0 at hA0
  change At P (base + 4) (hintFillStmt.compile (base + 4)) at hF0
  change At P (base + 12) hintInitSetup1 at hA1
  change At P (base + 16) (hintFillStmt.compile (base + 16)) at hF1
  change At P (base + 24) hintInitSetup2 at hA2
  change At P (base + 29) (hintFillStmt.compile (base + 29)) at hF2
  have hNo0 : NoBranch hintInitSetup0 := by simp [hintInitSetup0, NoBranch, Instr.NoBranchI]
  have hNo1 : NoBranch hintInitSetup1 := by simp [hintInitSetup1, NoBranch, Instr.NoBranchI]
  have hNo2 : NoBranch hintInitSetup2 := by simp [hintInitSetup2, NoBranch, Instr.NoBranchI]
  let s0 := runBlock hintInitSetup0 E state
  have hRun0 : (step P E)^[4] state = s0 := by
    exact iterate_runBlock_of_at P E hintInitSetup0 state (by rwa [hPc]) hNo0
  have hPc0 : s0.pc = base + 4 := by
    rw [runBlock_pc _ E state hNo0, hPc]; rfl
  obtain ⟨hParams0, hRegs0, hMem0⟩ := hintInitSetup0_spec E state residual lift rows hints context
    hRegs hDest hWord hSquare
  obtain ⟨_, k0, t0, hFillRun0, hFillPc0, hCost0, _, hFillMem0, hFillParams0, _, hFrame0⟩ :=
    hintFillStmt_sem P E s0 residual 1 (rows * rows) (base + 4) 0 hWord hSquare
      (by intro j hj; simp only [Nat.mul_one]; omega) hF0 hPc0 hParams0
  have hTRegs0 : HintInitRegs lift rows hints context t0 := hRegs0.of_frame hFrame0
  have hT0Pc : t0.pc = base + 12 := by simpa only [Nat.add_assoc] using hFillPc0
  let s1 := runBlock hintInitSetup1 E t0
  have hRun1 : (step P E)^[4] t0 = s1 :=
    iterate_runBlock_of_at P E hintInitSetup1 t0 (by rwa [hT0Pc]) hNo1
  have hPc1 : s1.pc = base + 16 := by
    rw [runBlock_pc _ E t0 hNo1, hT0Pc]; rfl
  obtain ⟨hParams1, hRegs1, hMem1⟩ := hintInitSetup1_spec E t0 residual lift rows hints context
    hTRegs0 hFillParams0.dest_value hFillParams0.one_value hWord hRows
  have hDiag : ∀ j < rows, residual + j * (rows + 1) < 2 ^ E.W := by
    intro j hj
    have hLess : j * (rows + 1) < rows * rows := by
      have hMul := Nat.mul_le_mul_right rows (Nat.succ_le_of_lt hj)
      rw [Nat.succ_mul] at hMul
      rw [Nat.mul_add, Nat.mul_one]
      omega
    omega
  obtain ⟨_, k1, t1, hFillRun1, hFillPc1, hCost1, _, hFillMem1, hFillParams1, _, hFrame1⟩ :=
    hintFillStmt_sem P E s1 residual (rows + 1) rows (base + 16) 1 hWord (by omega) hDiag hF1 hPc1 hParams1
  have hTRegs1 : HintInitRegs lift rows hints context t1 := hRegs1.of_frame hFrame1
  have hT1Pc : t1.pc = base + 24 := by simpa only [Nat.add_assoc] using hFillPc1
  let s2 := runBlock hintInitSetup2 E t1
  have hRun2 : (step P E)^[5] t1 = s2 :=
    iterate_runBlock_of_at P E hintInitSetup2 t1 (by rwa [hT1Pc]) hNo2
  have hPc2 : s2.pc = base + 29 := by
    rw [runBlock_pc _ E t1 hNo2, hT1Pc]; rfl
  obtain ⟨hParams2, hRegs2, hMem2⟩ := hintInitSetup2_spec E t1 lift rows hints context
    hTRegs1 hFillParams1.one_value hWord (by omega) hProduct
  obtain ⟨_, k2, out, hFillRun2, hFillPc2, hCost2, _, hFillMem2, hFillParams2, _, hFrame2⟩ :=
    hintFillStmt_sem P E s2 lift 1 (hints * rows) (base + 29) 0 hWord hProduct
      (by intro j hj; simp only [Nat.mul_one]; omega) hF2 hPc2 hParams2
  have hWhole := hintIterate_then (step P E)
    (hintIterate_then (step P E)
      (hintIterate_then (step P E)
        (hintIterate_then (step P E) (hintIterate_then (step P E) hRun0 hFillRun0) hRun1) hFillRun1) hRun2) hFillRun2
  refine ⟨hPc, k2 + (5 + (k1 + (4 + (k0 + 4)))), out, hWhole, ?_, ?_, ?_, hRegs2.of_frame hFrame2, hFillParams2.one_value⟩
  · simpa only [Nat.add_assoc] using hFillPc2
  · omega
  · change out.mem = _
    rw [hFillMem2, hMem2, hFillMem1, hMem1, hFillMem0, hMem0]
    rfl

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

structure HintElimStored {a h : ℕ} (B : HintElimState a h) (residual lift : ℕ) (memory : ℕ → ℕ) : Prop where
  residual_cells : ∀ s t : Fin a, memory (residual + s.val * a + t.val) = (B.residual (Pi.single t 1) s).val
  lift_cells : ∀ s : Fin h, ∀ t : Fin a, memory (lift + s.val * a + t.val) = (B.lift (Pi.single t 1) s).val

theorem hintDiagonal_offset_lt (rows i : ℕ) (hi : i < rows) : i * (rows + 1) < rows * rows := by
  have hMul := Nat.mul_le_mul_right rows (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hMul
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem hintElimInitMem_frame (original : ℕ → ℕ) (residual lift rows hints addr : ℕ)
    (hResidual : addr < residual ∨ residual + rows * rows ≤ addr)
    (hLift : addr < lift ∨ lift + hints * rows ≤ addr) :
    hintElimInitMem original residual lift rows hints addr = original addr := by
  have hR : addr ∉ hintFillPositions residual 1 (rows * rows) := by
    rw [hintFillPositions_contiguous]
    rcases hResidual with hBefore | hAfter <;> omega
  have hL : addr ∉ hintFillPositions lift 1 (hints * rows) := by
    rw [hintFillPositions_contiguous]
    rcases hLift with hBefore | hAfter <;> omega
  have hD : addr ∉ hintFillPositions residual (rows + 1) rows := by
    intro hPos
    obtain ⟨i, hi, hEq⟩ := Finset.mem_image.mp hPos
    have hi' : i < rows := Finset.mem_range.mp hi
    have hBound := hintDiagonal_offset_lt rows i hi'
    rcases hResidual with hBefore | hAfter <;> omega
  simp only [hintElimInitMem, hintFillMem, if_neg hL, if_neg hD, if_neg hR]

theorem hintElimInitMem_stored (original : ℕ → ℕ) (residual lift rows hints : ℕ)
    (hSeparate : residual + rows * rows ≤ lift ∨ lift + hints * rows ≤ residual) :
    HintElimStored (hintElimInit rows hints) residual lift (hintElimInitMem original residual lift rows hints) := by
  constructor
  · intro s t
    have hOffset : s.val * rows + t.val < rows * rows := by
      have hMul := Nat.mul_le_mul_right rows (Nat.succ_le_of_lt s.isLt)
      rw [Nat.succ_mul] at hMul
      omega
    have hOutside : residual + s.val * rows + t.val < lift ∨ lift + hints * rows ≤ residual + s.val * rows + t.val := by
      rcases hSeparate with hBefore | hAfter
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hNoL : residual + s.val * rows + t.val ∉ hintFillPositions lift 1 (hints * rows) := by
      rw [hintFillPositions_contiguous]
      rcases hOutside with hBefore | hAfter <;> omega
    change hintFillMem _ lift 1 (hints * rows) 0 _ = _
    rw [hintFillMem, if_neg hNoL, hintFill_identity_cells original residual rows s.val t.val s.isLt t.isLt]
    by_cases hEq : s = t
    · subst t
      simp [hintElimInit, Pi.single_apply, show (1 : ZMod 2).val = 1 from rfl]
    · have hVal : s.val ≠ t.val := fun heq => hEq (Fin.ext heq)
      simp [hintElimInit, Pi.single_apply, hEq, Ne.symm hEq, hVal]
  · intro s t
    have hOffset : s.val * rows + t.val < hints * rows := by
      have hMul := Nat.mul_le_mul_right rows (Nat.succ_le_of_lt s.isLt)
      rw [Nat.succ_mul] at hMul
      omega
    have hIn : lift + s.val * rows + t.val ∈ hintFillPositions lift 1 (hints * rows) := by
      rw [hintFillPositions_contiguous]
      omega
    simp only [hintElimInitMem, hintFillMem, if_pos hIn]
    simp [hintElimInit]

theorem hintElimInitStmt_stored_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (residual lift rows hints context base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hRows : rows + 1 < 2 ^ E.W)
    (hSquare : rows * rows < 2 ^ E.W) (hProduct : hints * rows < 2 ^ E.W)
    (hResidualSpan : residual + rows * rows < 2 ^ E.W)
    (hLiftSpan : lift + hints * rows < 2 ^ E.W)
    (hSeparate : residual + rows * rows ≤ lift ∨ lift + hints * rows ≤ residual)
    (hAt : At P base (hintElimInitStmt.compile base)) (hPc : state.pc = base)
    (hRegs : HintInitRegs lift rows hints context state) (hDest : state.regs 4 = residual) :
    Sem P E base (base + 37) state (fun k out => k = 7 * (rows * rows + rows + hints * rows) + 22 ∧
      HintElimStored (hintElimInit rows hints) residual lift out.mem ∧
      (∀ addr, (addr < residual ∨ residual + rows * rows ≤ addr) →
        (addr < lift ∨ lift + hints * rows ≤ addr) → out.mem addr = state.mem addr) ∧
      HintInitRegs lift rows hints context out ∧ out.regs 15 = 1) := by
  have hNative := hintElimInitStmt_sem P E state residual lift rows hints context base hWord hRows hSquare hProduct
    hResidualSpan hLiftSpan hAt hPc hRegs hDest
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, hMem, hKeep, hOne⟩ := hOut
  refine ⟨hCost, ?_, ?_, hKeep, hOne⟩
  · rw [hMem]
    exact hintElimInitMem_stored state.mem residual lift rows hints hSeparate
  · intro addr hR hL
    rw [hMem]
    exact hintElimInitMem_frame state.mem residual lift rows hints addr hR hL

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintElimInitStmt_stored_sem


