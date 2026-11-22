-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_07
-- name    : LinearSetReconciliation327_Main_Bundle51_07
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T13:53:40.986776+00:00
-- url     : https://prove2.me/theorems/4e01cc13-77c2-4d0c-bed8-8ffed4af88d7
-- title:
--   LinearSetReconciliation327 — Bundle51_07
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_07` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintCRCode20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintLoopBudget20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateExport20261120
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_06

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_07
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintGather20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowCoordinates20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintGatherRowImage20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowGather20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowSizing20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowPrepare20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPreparedWorkers20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPreparedStable20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintActionSwitch20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDispatchIO20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDispatchBody20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDispatch20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintLocatedSwitch20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintLocatedBody20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintLocatedDispatch20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlaceCR20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintGather20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintGatherList (accept : ℕ → Bool) (q : ℕ) : List ℕ := (List.range q).filter accept

theorem hintGatherList_length_le (accept : ℕ → Bool) (q : ℕ) :
    (hintGatherList accept q).length ≤ q := by
  simpa [hintGatherList] using List.length_filter_le accept (List.range q)

theorem hintGatherList_succ (accept : ℕ → Bool) (q : ℕ) :
    hintGatherList accept (q + 1) = hintGatherList accept q ++ (if accept q then [q] else []) := by
  cases hb : accept q <;> simp [hintGatherList, List.range_succ, hb]

structure HintGatherSource (E : RAMEnv) (dest source rows row node count : ℕ)
    (coord : ℕ → ℕ) (accept : ℕ → Bool) (original : ℕ → ℕ) : Prop where
  word : 1 < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  dest_end : dest + count ≤ source
  destination_fit : dest + count ≤ 2 ^ E.W
  position_fit : ∀ q < count, row + q * rows < 2 ^ E.W
  source_fit : ∀ q < count, source + coord q < 2 ^ E.W
  inverse : ∀ q < count, E.permInv node (row + q * rows) = coord q
  hint_bit : ∀ q < count, original (source + coord q) = if accept q then 1 else 0

structure HintGatherInv (dest source rows row node count q : ℕ) (accept : ℕ → Bool)
    (original : ℕ → ℕ) (s : RAMState) : Prop where
  args : HintGatherArgs dest source rows row node count s
  index : s.regs 0 = q
  used : s.regs 1 = (hintGatherList accept q).length
  stored : ∀ (i : ℕ) (hi : i < (hintGatherList accept q).length),
    s.mem (dest + i) = (hintGatherList accept q)[i]
  frame : CRMemFrame dest (dest + count) original s.mem

theorem hintGatherInv_step (E : RAMEnv) (s : RAMState)
    (dest source rows row node count q : ℕ) (coord : ℕ → ℕ) (accept : ℕ → Bool) (original : ℕ → ℕ)
    (hSource : HintGatherSource E dest source rows row node count coord accept original)
    (hq : q < count) (hInv : HintGatherInv dest source rows row node count q accept original s) :
    let out := runBlock hintGatherBody E s
    HintGatherInv dest source rows row node count (q + 1) accept original out ∧ out.regs 14 = s.regs 14 := by
  let L := hintGatherList accept q
  let flag : ℕ := if accept q then 1 else 0
  have hLen : L.length ≤ q := hintGatherList_length_le accept q
  have hCount := hSource.count_fit
  have hDest := hSource.destination_fit
  have hEnd := hSource.dest_end
  have hWord := hSource.word
  have hFlag : flag ≤ 1 := by dsimp [flag]; split <;> omega
  have hRead : s.mem (source + coord q) = flag :=
    (hInv.frame _ (Or.inr (by omega))).trans (hSource.hint_bit q hq)
  have hBlock := hintGatherBody_spec E s dest source rows row node count q L.length (coord q) flag
    hInv.args hInv.index hInv.used (hSource.position_fit q hq) (hSource.source_fit q hq)
    (by omega) (hSource.inverse q hq) hRead (by omega) (by omega) (by omega)
  generalize hExec : runBlock hintGatherBody E s = out at hBlock
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


theorem HintGatherInv.pc {dest source rows row node count q : ℕ}
    {accept : ℕ → Bool} {original : ℕ → ℕ} {s : RAMState}
    (h : HintGatherInv dest source rows row node count q accept original s) (pc : ℕ) :
    HintGatherInv dest source rows row node count q accept original {s with pc := pc} :=
  ⟨⟨h.args.dest_value, h.args.source_value, h.args.rows_value, h.args.row_value,
    h.args.node_value, h.args.count_value, h.args.one_value⟩, h.index, h.used, h.stored, h.frame⟩

theorem HintGatherInv.test {dest source rows row node count q : ℕ}
    {accept : ℕ → Bool} {original : ℕ → ℕ} {s : RAMState}
    (h : HintGatherInv dest source rows row node count q accept original s) (E : RAMEnv) :
    HintGatherInv dest source rows row node count q accept original (runBlock (Cond.lt 2 0 6).code E s) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using h.args.dest_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.source_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.rows_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.row_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.node_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.count_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.one_value
  · simpa [Cond.code, runBlock, execInstr] using h.index
  · simpa [Cond.code, runBlock, execInstr] using h.used
  · simpa [Cond.code, runBlock, execInstr] using h.stored
  · simpa [Cond.code, runBlock, execInstr] using h.frame

def hintGatherLoop : Stmt := .loop (.lt 2 0 6) (.code hintGatherBody)

theorem hintGatherLoop_len : hintGatherLoop.len = 12 := rfl

theorem hintGatherLoop_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source rows row node count base : ℕ) (coord : ℕ → ℕ) (accept : ℕ → Bool) (original : ℕ → ℕ)
    (hSource : HintGatherSource E dest source rows row node count coord accept original)
    (hInv : HintGatherInv dest source rows row node count 0 accept original state)
    (hAt : At P base (hintGatherLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 12) state (fun k out => k ≤ 12 * count + 2 ∧
      HintGatherInv dest source rows row node count count accept original out ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ q, q + left = count ∧
    HintGatherInv dest source rows row node count q accept original st ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) hintGatherBody := (at_loop hAt).2.2.1
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
    rw [hData.index, hData.args.count_value]; omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 0 6).eval st := by
    intro st hI
    obtain ⟨q, hQ, hData, _⟩ := hI
    change ¬ st.regs 0 < st.regs 6
    rw [hData.index, hData.args.count_value]; omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintGatherBody).len) st
        (fun k out => k ≤ 9 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨q, hQ, hData, hCtx⟩ := hI
    have hStep := hintGatherInv_step E st dest source rows row node count q coord accept original hSource
      (by omega) hData
    generalize hMid : runBlock hintGatherBody E st = mid at hStep
    have hNative := Sem.block P E (base + 2) hintGatherBody st hBodyAt
      (by simp [hintGatherBody, hintGatherHead, hintGatherTail, NoBranch, Instr.NoBranchI]) hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hOut⟩ := hOut
    rw [hMid] at hOut
    subst out
    exact ⟨hCost.le, q + 1, by omega, hStep.1, hStep.2.trans hCtx⟩
  have hInitial : I count state := ⟨0, by omega, hInv, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintGatherBody) hAt hSource.word I 9
    hIpc hItest hGo hStop hBody count state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, q, hQ, hFinal, hCtx⟩ := hOut
  have hEq : q = count := by omega
  rw [hEq] at hFinal
  exact ⟨hCost, hFinal, hCtx⟩

def hintGatherInit : List Instr := [.imm 0 0, .imm 1 0]
def hintGatherStmt : Stmt := .seq (.code hintGatherInit) hintGatherLoop

theorem hintGatherStmt_len : hintGatherStmt.len = 14 := rfl

/-- Gather the accepted row-local coordinates in ascending order. The physical
array is scratch space with capacity equal to the length of the whole row. -/
theorem hintGatherStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source rows row node count base : ℕ) (coord : ℕ → ℕ) (accept : ℕ → Bool)
    (hSource : HintGatherSource E dest source rows row node count coord accept state.mem)
    (hArgs : HintGatherArgs dest source rows row node count state)
    (hAt : At P base (hintGatherStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 14) state (fun k out => k ≤ 12 * count + 4 ∧
      HintGatherInv dest source rows row node count count accept state.mem out ∧ out.regs 14 = state.regs 14) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintGatherInit at hInitAt
  change At P (base + 2) (hintGatherLoop.compile (base + 2)) at hLoopAt
  have hInit : let out := runBlock hintGatherInit E state
      out.pc = state.pc + 2 ∧ out.regs 14 = state.regs 14 ∧
      HintGatherInv dest source rows row node count 0 accept state.mem out := by
    refine ⟨?_, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
    · simp [hintGatherInit, runBlock, execInstr]
    · simp [hintGatherInit, runBlock, execInstr]
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.dest_value
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.source_value
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.rows_value
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.row_value
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.node_value
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.count_value
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.one_value
    · simp [hintGatherInit, runBlock, execInstr]
    · simp [hintGatherInit, runBlock, execInstr, hintGatherList]
    · intro i hi
      simp [hintGatherList] at hi
    · intro addr hAway
      rfl
  generalize hI : runBlock hintGatherInit E state = mid at hInit
  obtain ⟨hPcI, hCtxI, hInvI⟩ := hInit
  have hRunI : (step P E)^[2] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGatherInit state (by rwa [hPc])
      (by simp [hintGatherInit, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  obtain ⟨_, k, out, hRun, hPcOut, hCost, hInvOut, hCtx⟩ :=
    hintGatherLoop_sem P E mid dest source rows row node count (base + 2) coord accept state.mem
      hSource hInvI hLoopAt (by omega)
  exact ⟨hPc, k + 2, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega,
    hInvOut, hCtx.trans hCtxI⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGatherStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintGather20261120

section -- Def_LinearSetReconciliation327_Main_HintRowCoordinates20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

namespace HintRowCoordinates

def count (N m row : ℕ) : ℕ :=
  if row < N then (N - 1 - row) / m + 1 else 0

theorem lt_count_iff (N m row q : ℕ) (hm : 0 < m) :
    q < count N m row ↔ row + q * m < N := by
  unfold count
  split
  next hRow =>
    have hDiv : q ≤ (N - 1 - row) / m ↔ q * m ≤ N - 1 - row := Nat.le_div_iff_mul_le hm
    omega
  next hRow =>
    omega

theorem count_eq_rowLen (N m row : ℕ) (hm : 0 < m) (hRow : row < m) :
    rowLen N m row = count N m row := by
  classical
  have hInj : Function.Injective (fun q : ℕ => row + q * m) := by
    intro x y heq
    exact Nat.eq_of_mul_eq_mul_right hm (Nat.add_left_cancel heq)
  have hSet : (Finset.range N).filter (fun p => p % m = row) =
      (Finset.range (count N m row)).image (fun q => row + q * m) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpN, hmod⟩ := Finset.mem_filter.mp hp
      have hDecomp : row + (p / m) * m = p := by
        rw [← hmod, Nat.mul_comm]
        exact Nat.mod_add_div p m
      refine Finset.mem_image.mpr ⟨p / m, Finset.mem_range.mpr ?_, hDecomp⟩
      rw [lt_count_iff N m row _ hm, hDecomp]
      exact Finset.mem_range.mp hpN
    · intro hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr ((lt_count_iff N m row q hm).mp (Finset.mem_range.mp hq)),
          by simp [Nat.add_mod, Nat.mod_eq_of_lt hRow]⟩
  unfold rowLen
  rw [hSet, Finset.card_image_of_injective _ hInj, Finset.card_range]

theorem index_lt (N m row q : ℕ) (hm : 0 < m) (hRow : row < m) (hq : q < rowLen N m row) :
    row + q * m < N := by
  rw [count_eq_rowLen N m row hm hRow] at hq
  exact (lt_count_iff N m row q hm).mp hq

theorem mem_rowImage_iff (N m row q : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (hm : 0 < m) (hRow : row < m) (hq : q < rowLen N m row) :
    q ∈ rowImage N m π row J ↔
      (π.symm ⟨row + q * m, index_lt N m row q hm hRow hq⟩).val ∈ J := by
  classical
  let p : Fin N := ⟨row + q * m, index_lt N m row q hm hRow hq⟩
  change q ∈ rowImage N m π row J ↔ (π.symm p).val ∈ J
  unfold rowImage
  constructor
  · intro h
    obtain ⟨i, hi, hDiv⟩ := Finset.mem_image.mp h
    obtain ⟨_, hiJ, hMod⟩ := Finset.mem_filter.mp hi
    have heq : π i = p := by
      apply Fin.ext
      change (π i).val = row + q * m
      rw [← hMod, ← hDiv, Nat.mul_comm ((π i).val / m) m, Nat.mod_add_div]
    have hSame : i = π.symm p := by rw [← heq, Equiv.symm_apply_apply]
    exact hSame ▸ hiJ
  · intro h
    refine Finset.mem_image.mpr ⟨π.symm p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, ?_⟩, ?_⟩
    · rw [Equiv.apply_symm_apply]
      change (row + q * m) % m = row
      simp [Nat.add_mod, Nat.mod_eq_of_lt hRow]
    · rw [Equiv.apply_symm_apply]
      change (row + q * m) / m = q
      rw [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hRow, Nat.zero_add]

theorem mem_rowImage_lt (N m row q : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (hm : 0 < m) (hRow : row < m) (hq : q ∈ rowImage N m π row J) :
    q < rowLen N m row := by
  obtain ⟨i, hi, hDiv⟩ := Finset.mem_image.mp hq
  have hMod := (Finset.mem_filter.mp hi).2.2
  have hDecomp : row + q * m = (π i).val := by
    rw [← hMod, ← hDiv, Nat.mul_comm, Nat.mod_add_div]
  rw [count_eq_rowLen N m row hm hRow, lt_count_iff N m row q hm, hDecomp]
  exact (π i).isLt

end HintRowCoordinates
end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintRowCoordinates.mem_rowImage_iff
end -- Def_LinearSetReconciliation327_Main_HintRowCoordinates20261120

section -- Def_LinearSetReconciliation327_Main_HintGatherRowImage20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

open Classical in
noncomputable def hintRowMembers (N m row : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ) : List ℕ :=
  hintGatherList (fun q => decide (q ∈ rowImage N m π row J)) (rowLen N m row)

theorem hintRowMembers_mem (N m row : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (hm : 0 < m) (hRow : row < m) (q : ℕ) :
    q ∈ hintRowMembers N m row π J ↔ q ∈ rowImage N m π row J := by
  classical
  simp only [hintRowMembers, hintGatherList, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨And.right, fun hq => ⟨HintRowCoordinates.mem_rowImage_lt N m row q π J hm hRow hq, hq⟩⟩

theorem hintRowMembers_nodup (N m row : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ) :
    (hintRowMembers N m row π J).Nodup := by
  unfold hintRowMembers hintGatherList
  exact List.Nodup.filter _ List.nodup_range

theorem hintRowMembers_coords (N m row K : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (hm : 0 < m) (hRow : row < m) (hK : rowLen N m row ≤ K) :
    let L := hintRowMembers N m row π J
    ∃ coords : Fin L.length → Fin K,
      Function.Injective coords ∧
      (∀ i : Fin L.length, (coords i).val = L[i.val] ∧ (coords i).val < rowLen N m row) ∧
      Finset.univ.image (fun i => (coords i).val) = rowImage N m π row J := by
  classical
  let L := hintRowMembers N m row π J
  have hIndex (i : Fin L.length) : L[i.val] < rowLen N m row := by
    have hMem := List.getElem_mem (l := L) i.isLt
    exact HintRowCoordinates.mem_rowImage_lt N m row L[i.val] π J hm hRow
      ((hintRowMembers_mem N m row π J hm hRow _).mp hMem)
  let coords : Fin L.length → Fin K := fun i => ⟨L[i.val], (hIndex i).trans_le hK⟩
  refine ⟨coords, ?_, fun i => ⟨rfl, hIndex i⟩, ?_⟩
  · intro i i' hEq
    apply Fin.ext
    exact (hintRowMembers_nodup N m row π J).getElem_inj_iff.mp (congrArg Fin.val hEq)
  · ext q
    constructor
    · intro h
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact (hintRowMembers_mem N m row π J hm hRow _).mp (List.getElem_mem (l := L) i.isLt)
    · intro h
      have hMem : q ∈ L := (hintRowMembers_mem N m row π J hm hRow q).mpr h
      obtain ⟨i, hi, hq⟩ := List.mem_iff_getElem.mp hMem
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hq⟩

/-- Apply the actual gathering code to a bitmap in the node's original coordinates. -/
theorem hintGatherRowImage_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (N m row node dest source base : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (hm : 0 < m) (hRow : row < m) (hWord : 1 < 2 ^ E.W)
    (hCount : rowLen N m row < 2 ^ E.W) (hEnd : dest + rowLen N m row ≤ source)
    (hSourceSpan : source + N ≤ 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (source + c.val) = hintTruth (c.val ∈ J))
    (hArgs : HintGatherArgs dest source m row node (rowLen N m row) state)
    (hAt : At P base (hintGatherStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 14) state (fun k out => k ≤ 12 * rowLen N m row + 4 ∧
      out.regs 1 = (hintRowMembers N m row π J).length ∧
      (∀ (i : ℕ) (hi : i < (hintRowMembers N m row π J).length),
        out.mem (dest + i) = (hintRowMembers N m row π J)[i]) ∧
      CRMemFrame dest (dest + rowLen N m row) state.mem out.mem ∧ out.regs 14 = state.regs 14) := by
  classical
  let count := rowLen N m row
  let coord : ℕ → ℕ := fun q =>
    if hq : q < count then (π.symm ⟨row + q * m, HintRowCoordinates.index_lt N m row q hm hRow hq⟩).val
    else 0
  let accept : ℕ → Bool := fun q => decide (q ∈ rowImage N m π row J)
  have hSrc : HintGatherSource E dest source m row node count coord accept state.mem := by
    refine ⟨hWord, hCount, hEnd, by dsimp [count]; omega, ?_, ?_, ?_, ?_⟩
    · intro q hq
      have h := HintRowCoordinates.index_lt N m row q hm hRow hq
      omega
    · intro q hq
      simp only [coord, dif_pos hq]
      have h := (π.symm ⟨row + q * m, HintRowCoordinates.index_lt N m row q hm hRow hq⟩).isLt
      omega
    · intro q hq
      simp only [coord, dif_pos hq]
      exact hPerm ⟨row + q * m, HintRowCoordinates.index_lt N m row q hm hRow hq⟩
    · intro q hq
      simp only [coord, dif_pos hq]
      rw [hBits, ← hintTruth_congr (HintRowCoordinates.mem_rowImage_iff N m row q π J hm hRow hq)]
      simp [accept, hintTruth]
  have hNative := hintGatherStmt_sem P E state dest source m row node count base coord accept hSrc hArgs hAt hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, hInv, hCtx⟩ := hOut
  exact ⟨hCost, hInv.used, hInv.stored, hInv.frame, hCtx⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGatherRowImage_sem
end -- Def_LinearSetReconciliation327_Main_HintGatherRowImage20261120

section -- Def_LinearSetReconciliation327_Main_HintRowGather20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintGatherFetch : List Instr :=
  hintParentLoad 4 25 ++ hintParentLoad 5 11 ++ hintParentLoad 7 10 ++
    hintParentLoad 10 27 ++ hintParentLoad 12 26 ++ hintParentLoad 6 2 ++ [.imm 15 1]

def hintGatherSetup : List Instr := hintScanParent ++ hintGatherFetch

theorem hintGatherSetup_length : hintGatherSetup.length = 21 := rfl

structure HintGatherMetadata (parent dest source rows row node count : ℕ) (memory : ℕ → ℕ) : Prop where
  dest_value : memory (parent + 25) = dest
  source_value : memory (parent + 11) = source
  rows_value : memory (parent + 10) = rows
  row_value : memory (parent + 27) = row
  node_value : memory (parent + 26) = node
  count_value : memory (parent + 2) = count

theorem hintGatherSetup_spec (E : RAMEnv) (s : RAMState)
    (parent dest source rows row node count : ℕ)
    (hSpan : parent + 29 < 2 ^ E.W) (hContext : s.regs 14 = parent + 16)
    (hMeta : HintGatherMetadata parent dest source rows row node count s.mem)
    (hDest : dest < 2 ^ E.W) (hSrc : source < 2 ^ E.W) (hRows : rows < 2 ^ E.W)
    (hRow : row < 2 ^ E.W) (hNode : node < 2 ^ E.W) (hCount : count < 2 ^ E.W) :
    let out := runBlock hintGatherSetup E s
    out.pc = s.pc + 21 ∧ out.mem = s.mem ∧ HintGatherArgs dest source rows row node count out ∧
      out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have hParent := hintScanParent_spec E s parent (by omega) hContext
  generalize hP : runBlock hintScanParent E s = mid at hParent
  obtain ⟨hPcP, hMemP, h11, h14⟩ := hParent
  have hFetch : let out := runBlock hintGatherFetch E mid
      out.pc = mid.pc + 19 ∧ out.mem = mid.mem ∧ HintGatherArgs dest source rows row node count out ∧
        out.regs 14 = parent + 16 := by
    have hRead25 : mid.mem (parent + 25) = dest := by
      rw [hMemP]
      exact hMeta.dest_value
    have hOff25 : 25 < 2 ^ E.W := by omega
    have hAddr25 : parent + 25 < 2 ^ E.W := by omega
    have hRead11 : mid.mem (parent + 11) = source := by
      rw [hMemP]
      exact hMeta.source_value
    have hOff11 : 11 < 2 ^ E.W := by omega
    have hAddr11 : parent + 11 < 2 ^ E.W := by omega
    have hRead10 : mid.mem (parent + 10) = rows := by
      rw [hMemP]
      exact hMeta.rows_value
    have hOff10 : 10 < 2 ^ E.W := by omega
    have hAddr10 : parent + 10 < 2 ^ E.W := by omega
    have hRead27 : mid.mem (parent + 27) = row := by
      rw [hMemP]
      exact hMeta.row_value
    have hOff27 : 27 < 2 ^ E.W := by omega
    have hAddr27 : parent + 27 < 2 ^ E.W := by omega
    have hRead26 : mid.mem (parent + 26) = node := by
      rw [hMemP]
      exact hMeta.node_value
    have hOff26 : 26 < 2 ^ E.W := by omega
    have hAddr26 : parent + 26 < 2 ^ E.W := by omega
    have hRead2 : mid.mem (parent + 2) = count := by
      rw [hMemP]
      exact hMeta.count_value
    have hOff2 : 2 < 2 ^ E.W := by omega
    have hAddr2 : parent + 2 < 2 ^ E.W := by omega
    refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp [hintGatherFetch, hintParentLoad, runBlock, execInstr, h11, h14,
        hRead25, hRead11, hRead10, hRead27, hRead26, hRead2,
        Nat.mod_eq_of_lt hOff25, Nat.mod_eq_of_lt hAddr25, Nat.mod_eq_of_lt hOff11,
        Nat.mod_eq_of_lt hAddr11, Nat.mod_eq_of_lt hOff10, Nat.mod_eq_of_lt hAddr10,
        Nat.mod_eq_of_lt hOff27, Nat.mod_eq_of_lt hAddr27, Nat.mod_eq_of_lt hOff26,
        Nat.mod_eq_of_lt hAddr26, Nat.mod_eq_of_lt hOff2, Nat.mod_eq_of_lt hAddr2,
        Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hSrc, Nat.mod_eq_of_lt hRows,
        Nat.mod_eq_of_lt hRow, Nat.mod_eq_of_lt hNode, Nat.mod_eq_of_lt hCount,
        Nat.mod_eq_of_lt hWord]
  generalize hF : runBlock hintGatherFetch E mid = out at hFetch
  obtain ⟨hPcF, hMemF, hArgsF, hCtxF⟩ := hFetch
  have hRun : runBlock hintGatherSetup E s = out := by
    rw [hintGatherSetup, runBlock_append, hP, hF]
  rw [hRun]
  exact ⟨by omega, hMemF.trans hMemP, hArgsF, hCtxF⟩


def hintRowGatherStmt : Stmt := .seq (.code hintGatherSetup) hintGatherStmt

theorem hintRowGatherStmt_len : hintRowGatherStmt.len = 35 := rfl

theorem hintRowGatherStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (N m row node parent dest source base : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (hm : 0 < m) (hRow : row < m)
    (hSpan : parent + 29 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hMeta : HintGatherMetadata parent dest source m row node (rowLen N m row) state.mem)
    (hDest : dest < 2 ^ E.W) (hSrc : source < 2 ^ E.W) (hRows : m < 2 ^ E.W) (hNode : node < 2 ^ E.W)
    (hCount : rowLen N m row < 2 ^ E.W) (hEnd : dest + rowLen N m row ≤ source)
    (hSourceSpan : source + N ≤ 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (source + c.val) = hintTruth (c.val ∈ J))
    (hAt : At P base (hintRowGatherStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 35) state (fun k out => k ≤ 12 * rowLen N m row + 25 ∧
      out.regs 1 = (hintRowMembers N m row π J).length ∧
      (∀ (i : ℕ) (hi : i < (hintRowMembers N m row π J).length),
        out.mem (dest + i) = (hintRowMembers N m row π J)[i]) ∧
      CRMemFrame dest (dest + rowLen N m row) state.mem out.mem ∧ out.regs 14 = parent + 16) := by
  obtain ⟨hSetupAt, hGatherAt⟩ := At.seqStmt hAt
  change At P base hintGatherSetup at hSetupAt
  change At P (base + 21) (hintGatherStmt.compile (base + 21)) at hGatherAt
  have hSetup := hintGatherSetup_spec E state parent dest source m row node (rowLen N m row)
    hSpan hContext hMeta hDest hSrc hRows (hRow.trans hRows) hNode hCount
  generalize hS : runBlock hintGatherSetup E state = mid at hSetup
  obtain ⟨hPcS, hMemS, hArgsS, hCtxS⟩ := hSetup
  have hRunS : (step P E)^[21] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGatherSetup state (by rwa [hPc])
      (by simp [hintGatherSetup, hintGatherFetch, hintScanParent, hintParentLoad, NoBranch, Instr.NoBranchI])
    simpa only [hintGatherSetup_length, hS] using hh
  obtain ⟨_, kG, out, hRunG, hPcG, hCost, hLength, hList, hFrame, hCtx⟩ :=
    hintGatherRowImage_sem P E mid N m row node dest source (base + 21) π J hm hRow (by omega)
      hCount hEnd hSourceSpan hPerm (by intro c; rw [hMemS]; exact hBits c) hArgsS hGatherAt (by omega)
  refine ⟨hPc, kG + 21, out, hintIterate_then (step P E) hRunS hRunG, by omega,
    by omega, hLength, hList, ?_, hCtx.trans hCtxS⟩
  rw [← hMemS]
  exact hFrame

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowGatherStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintRowGather20261120

section -- Def_LinearSetReconciliation327_Main_HintRowSizing20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRowSizingMin : List Instr :=
  [.sub 8 4 1, .imm 15 1, .lt 9 8 5, .bxor 10 9 15, .mul 8 8 9, .mul 10 5 10, .add 8 8 10]
def hintRowSizingTable : List Instr := [.add 5 5 15, .mul 7 5 1, .add 7 6 7]

theorem hintRowSizingMin_spec (E : RAMEnv) (state : RAMState) (Nj BY h : ℕ)
    (hWord : 1 < 2 ^ E.W) (hLe : h ≤ Nj) (hNj : Nj < 2 ^ E.W) (hBY : BY < 2 ^ E.W)
    (h4 : state.regs 4 = Nj) (h5 : state.regs 5 = BY) (h1 : state.regs 1 = h) :
    let out := runBlock hintRowSizingMin E state
    out.pc = state.pc + 7 ∧ out.mem = state.mem ∧ out.regs 8 = min BY (Nj - h) ∧
      out.regs 15 = 1 ∧ (∀ r : Fin 16, r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 15 → out.regs r = state.regs r) := by
  have hShift : Nj + 2 ^ E.W - h = (Nj - h) + 2 ^ E.W := by omega
  have hDiff : Nj - h < 2 ^ E.W := by omega
  have hSub : (Nj + 2 ^ E.W - h) % 2 ^ E.W = Nj - h := by
    rw [hShift, Nat.add_mod_right, Nat.mod_eq_of_lt hDiff]
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp [hintRowSizingMin, runBlock, execInstr]
  · by_cases hh : Nj - h < BY
    · simp [hintRowSizingMin, runBlock, execInstr, h4, h5, h1, hSub, hh,
        min_eq_right hh.le, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hDiff]
    · simp [hintRowSizingMin, runBlock, execInstr, h4, h5, h1, hSub, hh,
        min_eq_left (Nat.le_of_not_gt hh), Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hBY]
  · simp [hintRowSizingMin, runBlock, execInstr, Nat.mod_eq_of_lt hWord]
  · intro r h8 h9 h10 h15
    simp [hintRowSizingMin, runBlock, execInstr, h8, h9, h10, h15]

theorem hintRowSizingTable_spec (E : RAMEnv) (state : RAMState) (table BY h : ℕ)
    (hStride : BY + 1 < 2 ^ E.W) (hTable : table + (BY + 1) * h < 2 ^ E.W)
    (h1 : state.regs 1 = h) (h5 : state.regs 5 = BY) (h6 : state.regs 6 = table)
    (h15 : state.regs 15 = 1) :
    let out := runBlock hintRowSizingTable E state
    out.pc = state.pc + 3 ∧ out.mem = state.mem ∧ out.regs 7 = table + (BY + 1) * h ∧
      (∀ r : Fin 16, r ≠ 5 → r ≠ 7 → out.regs r = state.regs r) := by
  have hMul : (BY + 1) * h < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [hintRowSizingTable, runBlock, execInstr]
  · simp [hintRowSizingTable, runBlock, execInstr, h1, h5, h6, h15,
      Nat.mod_eq_of_lt hStride, Nat.mod_eq_of_lt hMul, Nat.mod_eq_of_lt hTable]
  · intro r h5' h7
    simp [hintRowSizingTable, runBlock, execInstr, h5', h7]


def hintRowSizingFetch : List Instr :=
  hintParentLoad 4 2 ++ hintParentLoad 5 12 ++ hintParentLoad 6 13
def hintRowSizingWrite : List Instr :=
  [.imm 3 4, .add 3 11 3, .store 3 8, .imm 3 5, .add 3 11 3, .store 3 7,
    .imm 3 1, .add 3 14 3, .store 3 1]
def hintRowSizingCode : List Instr :=
  hintScanParent ++ hintRowSizingFetch ++ hintRowSizingMin ++ hintRowSizingTable ++ hintRowSizingWrite

theorem hintRowSizingCode_length : hintRowSizingCode.length = 30 := rfl

def hintRowSizedMem (mem : ℕ → ℕ) (parent Nj BY table h : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update mem (parent + 4) (min BY (Nj - h)))
    (parent + 5) (table + (BY + 1) * h)) (parent + 17) h

theorem hintRowSizingWrite_spec (E : RAMEnv) (state : RAMState) (parent h limit lookup : ℕ)
    (hSpan : parent + 29 < 2 ^ E.W)
    (h11 : state.regs 11 = parent) (h14 : state.regs 14 = parent + 16)
    (h1 : state.regs 1 = h) (h8 : state.regs 8 = limit) (h7 : state.regs 7 = lookup) :
    let out := runBlock hintRowSizingWrite E state
    out.pc = state.pc + 9 ∧
      out.mem = Function.update (Function.update (Function.update state.mem (parent + 4) limit)
        (parent + 5) lookup) (parent + 17) h ∧
      out.regs 14 = parent + 16 := by
  have h1Fit : 1 < 2 ^ E.W := by omega
  have h4Fit : 4 < 2 ^ E.W := by omega
  have h5Fit : 5 < 2 ^ E.W := by omega
  have hAddr4 : parent + 4 < 2 ^ E.W := by omega
  have hAddr5 : parent + 5 < 2 ^ E.W := by omega
  have hAddr17 : parent + 16 + 1 < 2 ^ E.W := by omega
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [hintRowSizingWrite, runBlock, execInstr, h11, h14, h1, h8, h7,
      Nat.mod_eq_of_lt h1Fit, Nat.mod_eq_of_lt h4Fit, Nat.mod_eq_of_lt h5Fit,
      Nat.mod_eq_of_lt hAddr4, Nat.mod_eq_of_lt hAddr5, Nat.mod_eq_of_lt hAddr17]

theorem hintRowSizingCode_spec (E : RAMEnv) (state : RAMState) (parent Nj BY table h : ℕ)
    (hSpan : parent + 29 < 2 ^ E.W) (hCtx : state.regs 14 = parent + 16)
    (hCount : h ≤ Nj) (hNj : Nj < 2 ^ E.W) (hStride : BY + 1 < 2 ^ E.W)
    (hTable : table + (BY + 1) * h < 2 ^ E.W) (hLen : state.regs 1 = h)
    (hReadNj : state.mem (parent + 2) = Nj) (hReadBY : state.mem (parent + 12) = BY)
    (hReadTable : state.mem (parent + 13) = table) :
    let out := runBlock hintRowSizingCode E state
    out.pc = state.pc + 30 ∧ out.mem = hintRowSizedMem state.mem parent Nj BY table h ∧
      out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have hBY : BY < 2 ^ E.W := by omega
  have hTableFit : table < 2 ^ E.W := by omega
  have hParent := hintScanParent_spec E state parent (by omega) hCtx
  have hLenP : (runBlock hintScanParent E state).regs 1 = h := by
    simp [hintScanParent, runBlock, execInstr, hLen]
  generalize hP : runBlock hintScanParent E state = sP at hParent hLenP
  obtain ⟨hPcP, hMemP, h11P, h14P⟩ := hParent
  have hFetch : let out := runBlock hintRowSizingFetch E sP
      out.pc = sP.pc + 9 ∧ out.mem = sP.mem ∧
        out.regs 4 = Nj ∧ out.regs 5 = BY ∧ out.regs 6 = table ∧ out.regs 1 = h ∧
        out.regs 11 = parent ∧ out.regs 14 = parent + 16 := by
    have h2 : 2 < 2 ^ E.W := by omega
    have h12 : 12 < 2 ^ E.W := by omega
    have h13 : 13 < 2 ^ E.W := by omega
    have hA2 : parent + 2 < 2 ^ E.W := by omega
    have hA12 : parent + 12 < 2 ^ E.W := by omega
    have hA13 : parent + 13 < 2 ^ E.W := by omega
    refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hintRowSizingFetch, hintParentLoad, runBlock, execInstr, h11P, h14P, hLenP, hMemP,
        hReadNj, hReadBY, hReadTable, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h12, Nat.mod_eq_of_lt h13,
        Nat.mod_eq_of_lt hA2, Nat.mod_eq_of_lt hA12, Nat.mod_eq_of_lt hA13,
        Nat.mod_eq_of_lt hNj, Nat.mod_eq_of_lt hBY, Nat.mod_eq_of_lt hTableFit]
  generalize hF : runBlock hintRowSizingFetch E sP = sF at hFetch
  obtain ⟨hPcF, hMemF, h4F, h5F, h6F, h1F, h11F, h14F⟩ := hFetch
  have hMin := hintRowSizingMin_spec E sF Nj BY h hWord hCount hNj hBY h4F h5F h1F
  generalize hM : runBlock hintRowSizingMin E sF = sM at hMin
  obtain ⟨hPcM, hMemM, h8M, h15M, hRegsM⟩ := hMin
  have hSameM (r : Fin 16) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10) (h15 : r ≠ 15)
      (value : ℕ) (hEq : sF.regs r = value) : sM.regs r = value := (hRegsM r h8 h9 h10 h15).trans hEq
  have hLoc := hintRowSizingTable_spec E sM table BY h hStride hTable
    (hSameM 1 (by decide) (by decide) (by decide) (by decide) _ h1F)
    (hSameM 5 (by decide) (by decide) (by decide) (by decide) _ h5F)
    (hSameM 6 (by decide) (by decide) (by decide) (by decide) _ h6F) h15M
  generalize hT : runBlock hintRowSizingTable E sM = sT at hLoc
  obtain ⟨hPcT, hMemT, h7T, hRegsT⟩ := hLoc
  have h1T := (hRegsT 1 (by decide) (by decide)).trans
    (hSameM 1 (by decide) (by decide) (by decide) (by decide) _ h1F)
  have h11T := (hRegsT 11 (by decide) (by decide)).trans
    (hSameM 11 (by decide) (by decide) (by decide) (by decide) _ h11F)
  have h14T := (hRegsT 14 (by decide) (by decide)).trans
    (hSameM 14 (by decide) (by decide) (by decide) (by decide) _ h14F)
  have h8T := (hRegsT 8 (by decide) (by decide)).trans h8M
  have hWrite := hintRowSizingWrite_spec E sT parent h (min BY (Nj - h)) (table + (BY + 1) * h)
    hSpan h11T h14T h1T h8T h7T
  generalize hW : runBlock hintRowSizingWrite E sT = out at hWrite
  obtain ⟨hPcW, hMemW, hCtxW⟩ := hWrite
  have hRun : runBlock hintRowSizingCode E state = out := by
    rw [hintRowSizingCode, runBlock_append, runBlock_append, runBlock_append, runBlock_append, hP, hF, hM, hT, hW]
  rw [hRun]
  exact ⟨by omega, by rw [hMemW, hMemT, hMemM, hMemF, hMemP, hintRowSizedMem], hCtxW⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowSizingCode_spec
end -- Def_LinearSetReconciliation327_Main_HintRowSizing20261120

section -- Def_LinearSetReconciliation327_Main_HintRowPrepare20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintRowSizedMem_frame (mem : ℕ → ℕ) (parent Nj BY table h addr : ℕ)
    (h4 : addr ≠ parent + 4) (h5 : addr ≠ parent + 5) (h17 : addr ≠ parent + 17) :
    hintRowSizedMem mem parent Nj BY table h addr = mem addr := by
  simp only [hintRowSizedMem, Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h17]

structure HintRowPrepareMetadata (G : HintGaussArea)
    (parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (memory : ℕ → ℕ) : Prop where
  gather : HintGatherMetadata parent G.hintList hintSource m G.row G.node Nj memory
  outside_pointer : memory parent = outsideBase
  bitmap_pointer : memory (parent + 1) = bitmapBase
  outside_count : memory outsideBase = oldCount
  transcript_pointer : memory (parent + 9) = transcriptSource
  hint_limit : memory (parent + 6) = BX
  outside_limit : memory (parent + 12) = BY
  threshold_table : memory (parent + 13) = table
  header : ∃ index, ∀ i < 14, i ≠ 1 → memory (G.context + i) = hintGaussHeaderValue G index i

structure HintRowPrepared (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (parent Nj outsideBase bitmapBase BX BY table oldCount : ℕ) (state : RAMState) : Prop where
  input : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem
  header : ∃ index, HintGaussHeader G index state.mem
  context : state.regs 14 = G.context
  max_count : state.mem (parent + 4) = min BY (Nj - G.hints)
  wait_table : state.mem (parent + 5) = table + (BY + 1) * G.hints
  hint_limit : state.mem (parent + 6) = BX

def hintRowPrepareStmt : Stmt := .seq hintRowGatherStmt
  (.seq (.code hintRowSizingCode) hintTranscriptStmt)

theorem hintRowPrepareStmt_len : hintRowPrepareStmt.len = 95 := rfl

/-- Prepare the actual inputs for the row workers from the real node hint bitmap
and column-major transcript. The initial hint count and row scratch may be arbitrary. -/
theorem hintRowPrepareStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hParent : parent + 16 = G.context) (hContext : state.regs 14 = G.context)
    (hFits : HintGaussHeaderFits E G 0)
    (hMeta : HintRowPrepareMetadata G parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount state.mem)
    (hm : 0 < m) (hRow : G.row < m) (hNj : Nj = rowLen N m G.row)
    (hHintLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hHintLen.symm ▸ i.isLt))
    (hRowsFit : m < 2 ^ E.W) (hNjFit : Nj < 2 ^ E.W)
    (hBYFit : BY + 1 < 2 ^ E.W) (hTableFit : table + (BY + 1) * G.hints < 2 ^ E.W)
    (hOutside : outsideBase < G.hintList)
    (hGatherEnd : G.hintList + Nj ≤ parent)
    (hDestEnd : G.hintList + G.hints + 2 * G.rows ≤ parent)
    (hHintSeparate : parent ≤ hintSource) (hHintFit : hintSource < 2 ^ E.W)
    (hHintSpan : hintSource + N ≤ 2 ^ E.W)
    (hTranscriptSeparate : G.hintList + G.hints + 2 * G.rows ≤ transcriptSource)
    (hTranscriptOutsideGather : G.hintList + Nj ≤ transcriptSource)
    (hTranscriptAfterHeader : parent + 18 ≤ transcriptSource)
    (hTranscriptFit : transcriptSource < 2 ^ E.W)
    (hTranscriptSpan : ∀ t : Fin G.rows, transcriptSource + t.val * m < 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (hintSource + c.val) = hintTruth (c.val ∈ J))
    (hTranscript : ∀ t : Fin G.rows, state.mem (transcriptSource + t.val * m) = (v t).val)
    (hAt : At P base (hintRowPrepareStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 95) state (fun k out => k ≤ 12 * Nj + 9 * G.rows + 78 ∧
      HintRowPrepared G coords v parent Nj outsideBase bitmapBase BX BY table oldCount out ∧
      CRMemFrame G.hintList (parent + 18) state.mem out.mem) := by
  have hSpan := hFits.span
  have hHL : G.hints ≤ Nj := by
    rw [← hHintLen, hNj]
    exact hintGatherList_length_le _ _
  have hMetaGather : HintGatherMetadata parent G.hintList hintSource m G.row G.node
      (rowLen N m G.row) state.mem := hNj ▸ hMeta.gather
  obtain ⟨hGatherAt, hRestAt⟩ := At.seqStmt hAt
  change At P base (hintRowGatherStmt.compile base) at hGatherAt
  change At P (base + 35) ((Stmt.seq (.code hintRowSizingCode) hintTranscriptStmt).compile (base + 35)) at hRestAt
  obtain ⟨hSizeAt, hTranscriptAt⟩ := At.seqStmt hRestAt
  change At P (base + 35) hintRowSizingCode at hSizeAt
  change At P (base + 65) (hintTranscriptStmt.compile (base + 65)) at hTranscriptAt
  obtain ⟨_, kG, sG, hRunG, hPcG, hCostG, hLenG, hListG, hFrameG, hCtxG⟩ :=
    hintRowGatherStmt_sem P E state N m G.row G.node parent G.hintList hintSource base π J hm hRow
      (by omega) (hContext.trans hParent.symm) hMetaGather (hFits.values 9 (by decide)) hHintFit hRowsFit
      (hFits.values 10 (by decide)) (by omega) (by omega) hHintSpan hPerm hBits hGatherAt hPc
  have hAfterG (addr : ℕ) (ha : parent ≤ addr) : sG.mem addr = state.mem addr :=
    hFrameG addr (Or.inr (by omega))
  have hSize := hintRowSizingCode_spec E sG parent Nj BY table G.hints (by omega) hCtxG hHL hNjFit hBYFit hTableFit
    (hLenG.trans hHintLen)
    ((hAfterG _ (by omega)).trans hMeta.gather.count_value)
    ((hAfterG _ (by omega)).trans hMeta.outside_limit)
    ((hAfterG _ (by omega)).trans hMeta.threshold_table)
  generalize hS : runBlock hintRowSizingCode E sG = sS at hSize
  obtain ⟨hPcS, hMemS, hCtxS⟩ := hSize
  have hRunS : (step P E)^[30] sG = sS := by
    have hh := iterate_runBlock_of_at P E hintRowSizingCode sG (by rwa [hPcG])
      (by simp [hintRowSizingCode, hintScanParent, hintRowSizingFetch, hintParentLoad,
        hintRowSizingMin, hintRowSizingTable, hintRowSizingWrite, NoBranch, Instr.NoBranchI])
    simpa only [hintRowSizingCode_length, hS] using hh
  have hUnchangedS (addr : ℕ) (h4 : addr ≠ parent + 4) (h5 : addr ≠ parent + 5) (h17 : addr ≠ parent + 17) :
      sS.mem addr = sG.mem addr := by
    rw [hMemS]
    exact hintRowSizedMem_frame _ _ _ _ _ _ _ h4 h5 h17
  have hHeaderS : ∃ index, HintGaussHeader G index sS.mem := by
    obtain ⟨index, hHead⟩ := hMeta.header
    refine ⟨index, ?_⟩
    intro i hi
    by_cases hEq : i = 1
    · subst i
      rw [show G.context + 1 = parent + 17 by omega, hMemS]
      simp [hintRowSizedMem, hintGaussHeaderValue]
    · rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
      exact hHead i hi hEq
  obtain ⟨_, kT, out, hRunT, hPcT, hCostT, hObs, hHeaderOut, hCtxOut, hFrameT⟩ :=
    hintTranscriptStmt_sem G v parent transcriptSource m P E sS (base + 65)
      hParent (hCtxS.trans hParent) hHeaderS hFits hTranscriptFit hRowsFit
      (by rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]; exact hMeta.transcript_pointer)
      (by rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]; exact hMeta.gather.rows_value)
      hDestEnd hTranscriptSeparate hTranscriptSpan
      (by
        intro t
        rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
        exact hTranscript t) hTranscriptAt (by omega)
  have hAfterT (addr : ℕ) (ha : parent ≤ addr) : out.mem addr = sS.mem addr :=
    hFrameT addr (Or.inr (by omega))
  refine ⟨hPc, kT + (30 + kG), out, hintIterate_then (step P E) (hintIterate_then (step P E) hRunG hRunS) hRunT,
    by omega, by omega, ⟨⟨?_, ?_, ?_, ?_, ?_, hObs⟩, hHeaderOut, hCtxOut, ?_, ?_, ?_⟩, ?_⟩
  · rw [hAfterT _ le_rfl, hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ le_rfl]
    exact hMeta.outside_pointer
  · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
    exact hMeta.bitmap_pointer
  · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
    exact hMeta.gather.count_value
  · rw [hFrameT _ (Or.inl (by omega)), hUnchangedS _ (by omega) (by omega) (by omega),
      hFrameG _ (Or.inl hOutside)]
    exact hMeta.outside_count
  · intro i
    have hi := i.isLt
    rw [hFrameT _ (Or.inl (by omega)), hUnchangedS _ (by omega) (by omega) (by omega)]
    exact (hListG i.val (hHintLen.symm ▸ hi)).trans (hCoords i).symm
  · rw [hAfterT _ (by omega), hMemS]
    simp [hintRowSizedMem, Function.update_of_ne (by omega : parent + 4 ≠ parent + 17),
      Function.update_of_ne (by omega : parent + 4 ≠ parent + 5)]
  · rw [hAfterT _ (by omega), hMemS]
    simp [hintRowSizedMem, Function.update_of_ne (by omega : parent + 5 ≠ parent + 17)]
  · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
    exact hMeta.hint_limit
  · intro addr hAway
    rcases hAway with hBefore | hAfter
    · rw [hFrameT _ (Or.inl (by omega)), hUnchangedS _ (by omega) (by omega) (by omega), hFrameG _ (Or.inl hBefore)]
    · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowPrepareStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintRowPrepare20261120

section -- Def_LinearSetReconciliation327_Main_HintPreparedWorkers20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

theorem hintRowPrepared_image (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (N m : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (hm : 0 < m) (hRow : G.row < m)
    (hLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hLen.symm ▸ i.isLt)) :
    Finset.univ.image (fun t => (coords t).val) = rowImage N m π G.row J := by
  classical
  ext q
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    rw [hCoords i]
    exact (hintRowMembers_mem N m G.row π J hm hRow _).mp (List.getElem_mem _)
  · intro h
    have hMem := (hintRowMembers_mem N m G.row π J hm hRow q).mpr h
    obtain ⟨i, hi, hq⟩ := List.mem_iff_getElem.mp hMem
    have hBound : i < G.hints := hLen ▸ hi
    exact Finset.mem_image.mpr ⟨⟨i, hBound⟩, Finset.mem_univ _, (hCoords ⟨i, hBound⟩).trans hq⟩

theorem hintPrepared_frames {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj maxR parent outsideBase bitmapBase : ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase) :
    bitmapBase ≤ G.hintList ∧ parent + 18 ≤ G.pivotRow + G.rows ∧
      (∀ addr, addr < bitmapBase ∨ G.pivotRow + G.rows ≤ addr →
        (addr < bitmapBase ∨ bitmapBase + Nj ≤ addr) ∧
        (addr < outsideBase ∨ outsideBase + 1 + maxR ≤ addr) ∧
        addr ≠ parent + 3 ∧ addr ≠ parent + 7 ∧ addr ≠ parent + 8 ∧
        (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) ∧
        (addr < G.context ∨ G.pivotRow + G.rows ≤ addr)) := by
  have hBitmap := hPublic.bitmap_span
  have hOutside := hPublic.outside_span
  have hSource := hPublic.source
  have hParent := hPublic.parent_eq
  have hReserve := hPublic.reserve
  have h0 := hPublic.geometry.residual_before
  have h1 := hPublic.geometry.lift_before
  have h2 := hPublic.geometry.column_before
  have h3 := hPublic.geometry.residualVec_before
  have h4 := hPublic.geometry.kernelVec_before
  refine ⟨by omega, by omega, ?_⟩
  intro addr ha
  rcases ha with ha | ha
  · refine ⟨Or.inl ha, Or.inl (by omega), by omega, by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩
  · refine ⟨Or.inr (by omega), Or.inr (by omega), by omega, by omega, by omega, Or.inr (by omega), Or.inr ha⟩

def hintPreparedPredictStmt : Stmt := .seq hintRowPrepareStmt hintRowPredictStmt
def hintPreparedFinalStmt : Stmt := .seq hintRowPrepareStmt hintRowFinalStmt
theorem hintPreparedPredictStmt_len : hintPreparedPredictStmt.len = 1584 := rfl
theorem hintPreparedFinalStmt_len : hintPreparedFinalStmt.len = 1653 := rfl

theorem hintPreparedPredictStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (c : ℕ)
    (N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hContext : state.regs 14 = G.context)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj (min BY (Nj - G.hints)) parent outsideBase bitmapBase)
    (j : Fin m) (hRowValue : G.row = j.val) (hBX : BX < 2 ^ E.W)
    (hMeta : HintRowPrepareMetadata G parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount state.mem)
    (hm : 0 < m) (hRow : G.row < m) (hNj : Nj = rowLen N m G.row)
    (hHintLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hHintLen.symm ▸ i.isLt))
    (hRowsFit : m < 2 ^ E.W) (hNjFit : Nj < 2 ^ E.W)
    (hBYFit : BY + 1 < 2 ^ E.W) (hTableFit : table + (BY + 1) * G.hints < 2 ^ E.W)
    (hGatherEnd : G.hintList + Nj ≤ parent)
    (hHintSeparate : parent ≤ hintSource) (hHintFit : hintSource < 2 ^ E.W)
    (hHintSpan : hintSource + N ≤ 2 ^ E.W)
    (hTranscriptSeparate : G.hintList + G.hints + 2 * G.rows ≤ transcriptSource)
    (hTranscriptOutsideGather : G.hintList + Nj ≤ transcriptSource)
    (hTranscriptAfterHeader : parent + 18 ≤ transcriptSource)
    (hTranscriptFit : transcriptSource < 2 ^ E.W)
    (hTranscriptSpan : ∀ t : Fin G.rows, transcriptSource + t.val * m < 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (hintSource + c.val) = hintTruth (c.val ∈ J))
    (hTranscript : ∀ t : Fin G.rows, state.mem (transcriptSource + t.val * m) = (v t).val)
    (hWaitTable : table + (BY + 1) * G.hints + min BY (Nj - G.hints) < 2 ^ E.W)
    (hLookup : ∀ r ≤ min BY (Nj - G.hints),
      E.det (table + (BY + 1) * G.hints + r) = min G.steps (sigma G.hints Nj r + c))
    (hCoeff : ∀ hNext : G.rows < G.steps, ∀ q : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + q.val) = (beta ⟨G.rows, hNext⟩ q).val)
    (hAt : At P base (hintPreparedPredictStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1584) state (fun k out =>
      k ≤ (hintRowOuterBudget G Nj (min BY (Nj - G.hints)) + 2) *
        (min BY (Nj - G.hints) + 1) + 12 * Nj + 9 * G.rows + 107 ∧
      hintRowOutput out = workerPredict N m G.steps G.buckets BX BY c j beta
        (rowImage N m π j.val J) (List.ofFn v) ∧
      out.regs 14 = G.context ∧ CRMemFrame bitmapBase (G.pivotRow + G.rows) state.mem out.mem) := by
  let maxR := min BY (Nj - G.hints)
  let tableAddr := table + (BY + 1) * G.hints
  have hh := hPublic.outside_span
  obtain ⟨hBitmapStart, hHeaderEnd, hZones⟩ := hintPrepared_frames hPublic
  have hImage := hintRowPrepared_image G coords N m π J hm hRow hHintLen hCoords
  have hNj' : rowLen N m j.val = Nj := by rw [← hRowValue, hNj]
  obtain ⟨hAtPrep, hAtWork⟩ := At.seqStmt hAt
  change At P base (hintRowPrepareStmt.compile base) at hAtPrep
  change At P (base + 95) (hintRowPredictStmt.compile (base + 95)) at hAtWork
  obtain ⟨_, kP, mid, hRunP, hPcP, hCostP, hp, hFrameP⟩ :=
    hintRowPrepareStmt_sem G coords v N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount π J
      P E state base hPublic.parent_eq hContext hPublic.fits hMeta hm hRow hNj hHintLen hCoords hRowsFit hNjFit
      hBYFit hTableFit (by omega) hGatherEnd hPublic.source hHintSeparate hHintFit hHintSpan
      hTranscriptSeparate hTranscriptOutsideGather hTranscriptAfterHeader hTranscriptFit hTranscriptSpan hPerm hBits hTranscript
      hAtPrep hPc
  obtain ⟨_, kW, out, hRunW, hPcW, hCostW, hOut, _, _, hCtxOut, hFrameW⟩ :=
    hintRowPredictStmt_sem G coords beta hPrefix N m Nj parent outsideBase bitmapBase maxR tableAddr BX BY c oldCount j v
      P E mid (base + 95) hPublic hp.input hp.header hp.context hNj' rfl hBX hp.hint_limit
      hp.max_count hp.wait_table hWaitTable hLookup hCoeff hAtWork hPcP
  have hOutput : hintRowOutput out = workerPredict N m G.steps G.buckets BX BY c j beta
      (rowImage N m π j.val J) (List.ofFn v) := by
    have hAlign : Finset.univ.image (fun t => (coords t).val) = rowImage N m π j.val J := hImage.trans (by rw [← hRowValue])
    simpa only [hAlign] using hOut
  refine ⟨hPc, kW + kP, out, hintIterate_then (step P E) hRunP hRunW, by omega,
    by dsimp only [maxR] at hCostW; omega, hOutput, hCtxOut, ?_⟩
  intro addr hAway
  obtain ⟨hB, hO, h3, _, _, hR, hG⟩ := hZones addr hAway
  rw [hFrameW addr hB hO h3 hR hG]
  apply hFrameP
  rcases hAway with hBefore | hAfter
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem hintPreparedFinalStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hContext : state.regs 14 = G.context)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj (min BY (Nj - G.hints)) parent outsideBase bitmapBase)
    (j : Fin m) (hRowValue : G.row = j.val) (hBX : BX < 2 ^ E.W)
    (hMeta : HintRowPrepareMetadata G parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount state.mem)
    (hm : 0 < m) (hRow : G.row < m) (hNj : Nj = rowLen N m G.row)
    (hHintLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hHintLen.symm ▸ i.isLt))
    (hRowsFit : m < 2 ^ E.W) (hNjFit : Nj < 2 ^ E.W)
    (hBYFit : BY + 1 < 2 ^ E.W) (hTableFit : table + (BY + 1) * G.hints < 2 ^ E.W)
    (hGatherEnd : G.hintList + Nj ≤ parent)
    (hHintSeparate : parent ≤ hintSource) (hHintFit : hintSource < 2 ^ E.W)
    (hHintSpan : hintSource + N ≤ 2 ^ E.W)
    (hTranscriptSeparate : G.hintList + G.hints + 2 * G.rows ≤ transcriptSource)
    (hTranscriptOutsideGather : G.hintList + Nj ≤ transcriptSource)
    (hTranscriptAfterHeader : parent + 18 ≤ transcriptSource)
    (hTranscriptFit : transcriptSource < 2 ^ E.W)
    (hTranscriptSpan : ∀ t : Fin G.rows, transcriptSource + t.val * m < 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (hintSource + c.val) = hintTruth (c.val ∈ J))
    (hTranscript : ∀ t : Fin G.rows, state.mem (transcriptSource + t.val * m) = (v t).val)
    (hAt : At P base (hintPreparedFinalStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1653) state (fun k out =>
      k ≤ (hintFinalBudget G Nj (min BY (Nj - G.hints)) + 2) *
        (min BY (Nj - G.hints) + 1) + hintFinalBudget G Nj (min BY (Nj - G.hints)) +
        26 * Nj + 9 * G.rows + 18 * G.hints + 8 * min BY (Nj - G.hints) + 186 ∧
      (∀ q < Nj, out.mem (bitmapBase + q) = hintTruth (q ∈
        workerFinal N m G.steps G.buckets BX BY j beta (rowImage N m π j.val J) (List.ofFn v))) ∧
      out.regs 14 = G.context ∧ CRMemFrame bitmapBase (G.pivotRow + G.rows) state.mem out.mem) := by
  let maxR := min BY (Nj - G.hints)
  have hh := hPublic.outside_span
  obtain ⟨hBitmapStart, hHeaderEnd, hZones⟩ := hintPrepared_frames hPublic
  have hImage := hintRowPrepared_image G coords N m π J hm hRow hHintLen hCoords
  have hNj' : rowLen N m j.val = Nj := by rw [← hRowValue, hNj]
  obtain ⟨hAtPrep, hAtWork⟩ := At.seqStmt hAt
  change At P base (hintRowPrepareStmt.compile base) at hAtPrep
  change At P (base + 95) (hintRowFinalStmt.compile (base + 95)) at hAtWork
  obtain ⟨_, kP, mid, hRunP, hPcP, hCostP, hp, hFrameP⟩ :=
    hintRowPrepareStmt_sem G coords v N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount π J
      P E state base hPublic.parent_eq hContext hPublic.fits hMeta hm hRow hNj hHintLen hCoords hRowsFit hNjFit
      hBYFit hTableFit (by omega) hGatherEnd hPublic.source hHintSeparate hHintFit hHintSpan
      hTranscriptSeparate hTranscriptOutsideGather hTranscriptAfterHeader hTranscriptFit hTranscriptSpan hPerm hBits hTranscript
      hAtPrep hPc
  obtain ⟨_, kW, out, hRunW, hPcW, hCostW, hOut, _, _, hCtxOut, hFrameW⟩ :=
    hintRowFinalStmt_sem G coords beta hPrefix N m Nj parent outsideBase bitmapBase maxR BX BY oldCount j v
      P E mid (base + 95) hPublic hp.input hp.header hp.context hNj' rfl hBX hp.hint_limit
      hp.max_count hAtWork hPcP
  refine ⟨hPc, kW + kP, out, hintIterate_then (step P E) hRunP hRunW, by omega,
    by dsimp only [maxR] at hCostW; omega, ?_, hCtxOut, ?_⟩
  · intro q hq
    have hAlign : Finset.univ.image (fun t => (coords t).val) = rowImage N m π j.val J := hImage.trans (by rw [← hRowValue])
    simpa only [hAlign] using hOut q hq
  · intro addr hAway
    obtain ⟨hB, hO, h3, h7, h8, hR, hG⟩ := hZones addr hAway
    have hEq := hFrameW addr hB hO h3 h7 h8 hR hG
    rw [hEq]
    apply hFrameP
    rcases hAway with hBefore | hAfter
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPreparedPredictStmt_sem
#print axioms LinearSetReconciliation327.Main.hintPreparedFinalStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintPreparedWorkers20261120

section -- Def_LinearSetReconciliation327_Main_HintPreparedStable20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

theorem hintRowPrepareStmt_stable_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hParent : parent + 16 = G.context) (hContext : state.regs 14 = G.context)
    (hFits : HintGaussHeaderFits E G 0)
    (hMeta : HintRowPrepareMetadata G parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount state.mem)
    (hm : 0 < m) (hRow : G.row < m) (hNj : Nj = rowLen N m G.row)
    (hHintLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hHintLen.symm ▸ i.isLt))
    (hRowsFit : m < 2 ^ E.W) (hNjFit : Nj < 2 ^ E.W)
    (hBYFit : BY + 1 < 2 ^ E.W) (hTableFit : table + (BY + 1) * G.hints < 2 ^ E.W)
    (hOutside : outsideBase < G.hintList)
    (hGatherEnd : G.hintList + Nj ≤ parent)
    (hDestEnd : G.hintList + G.hints + 2 * G.rows ≤ parent)
    (hHintSeparate : parent ≤ hintSource) (hHintFit : hintSource < 2 ^ E.W)
    (hHintSpan : hintSource + N ≤ 2 ^ E.W)
    (hTranscriptSeparate : G.hintList + G.hints + 2 * G.rows ≤ transcriptSource)
    (hTranscriptOutsideGather : G.hintList + Nj ≤ transcriptSource)
    (hTranscriptAfterHeader : parent + 18 ≤ transcriptSource)
    (hTranscriptFit : transcriptSource < 2 ^ E.W)
    (hTranscriptSpan : ∀ t : Fin G.rows, transcriptSource + t.val * m < 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (hintSource + c.val) = hintTruth (c.val ∈ J))
    (hTranscript : ∀ t : Fin G.rows, state.mem (transcriptSource + t.val * m) = (v t).val)
    (hAt : At P base (hintRowPrepareStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 95) state (fun k out => k ≤ 12 * Nj + 9 * G.rows + 78 ∧
      HintRowPrepared G coords v parent Nj outsideBase bitmapBase BX BY table oldCount out ∧
      CRMemFrame G.hintList (parent + 18) state.mem out.mem ∧
      (∀ i < 16, i ≠ 4 → i ≠ 5 → out.mem (parent + i) = state.mem (parent + i))) := by
  have hSpan := hFits.span
  have hHL : G.hints ≤ Nj := by
    rw [← hHintLen, hNj]
    exact hintGatherList_length_le _ _
  have hMetaGather : HintGatherMetadata parent G.hintList hintSource m G.row G.node
      (rowLen N m G.row) state.mem := hNj ▸ hMeta.gather
  obtain ⟨hGatherAt, hRestAt⟩ := At.seqStmt hAt
  change At P base (hintRowGatherStmt.compile base) at hGatherAt
  change At P (base + 35) ((Stmt.seq (.code hintRowSizingCode) hintTranscriptStmt).compile (base + 35)) at hRestAt
  obtain ⟨hSizeAt, hTranscriptAt⟩ := At.seqStmt hRestAt
  change At P (base + 35) hintRowSizingCode at hSizeAt
  change At P (base + 65) (hintTranscriptStmt.compile (base + 65)) at hTranscriptAt
  obtain ⟨_, kG, sG, hRunG, hPcG, hCostG, hLenG, hListG, hFrameG, hCtxG⟩ :=
    hintRowGatherStmt_sem P E state N m G.row G.node parent G.hintList hintSource base π J hm hRow
      (by omega) (hContext.trans hParent.symm) hMetaGather (hFits.values 9 (by decide)) hHintFit hRowsFit
      (hFits.values 10 (by decide)) (by omega) (by omega) hHintSpan hPerm hBits hGatherAt hPc
  have hAfterG (addr : ℕ) (ha : parent ≤ addr) : sG.mem addr = state.mem addr :=
    hFrameG addr (Or.inr (by omega))
  have hSize := hintRowSizingCode_spec E sG parent Nj BY table G.hints (by omega) hCtxG hHL hNjFit hBYFit hTableFit
    (hLenG.trans hHintLen)
    ((hAfterG _ (by omega)).trans hMeta.gather.count_value)
    ((hAfterG _ (by omega)).trans hMeta.outside_limit)
    ((hAfterG _ (by omega)).trans hMeta.threshold_table)
  generalize hS : runBlock hintRowSizingCode E sG = sS at hSize
  obtain ⟨hPcS, hMemS, hCtxS⟩ := hSize
  have hRunS : (step P E)^[30] sG = sS := by
    have hh := iterate_runBlock_of_at P E hintRowSizingCode sG (by rwa [hPcG])
      (by simp [hintRowSizingCode, hintScanParent, hintRowSizingFetch, hintParentLoad,
        hintRowSizingMin, hintRowSizingTable, hintRowSizingWrite, NoBranch, Instr.NoBranchI])
    simpa only [hintRowSizingCode_length, hS] using hh
  have hUnchangedS (addr : ℕ) (h4 : addr ≠ parent + 4) (h5 : addr ≠ parent + 5) (h17 : addr ≠ parent + 17) :
      sS.mem addr = sG.mem addr := by
    rw [hMemS]
    exact hintRowSizedMem_frame _ _ _ _ _ _ _ h4 h5 h17
  have hHeaderS : ∃ index, HintGaussHeader G index sS.mem := by
    obtain ⟨index, hHead⟩ := hMeta.header
    refine ⟨index, ?_⟩
    intro i hi
    by_cases hEq : i = 1
    · subst i
      rw [show G.context + 1 = parent + 17 by omega, hMemS]
      simp [hintRowSizedMem, hintGaussHeaderValue]
    · rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
      exact hHead i hi hEq
  obtain ⟨_, kT, out, hRunT, hPcT, hCostT, hObs, hHeaderOut, hCtxOut, hFrameT⟩ :=
    hintTranscriptStmt_sem G v parent transcriptSource m P E sS (base + 65)
      hParent (hCtxS.trans hParent) hHeaderS hFits hTranscriptFit hRowsFit
      (by rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]; exact hMeta.transcript_pointer)
      (by rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]; exact hMeta.gather.rows_value)
      hDestEnd hTranscriptSeparate hTranscriptSpan
      (by
        intro t
        rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
        exact hTranscript t) hTranscriptAt (by omega)
  have hAfterT (addr : ℕ) (ha : parent ≤ addr) : out.mem addr = sS.mem addr :=
    hFrameT addr (Or.inr (by omega))
  refine ⟨hPc, kT + (30 + kG), out, hintIterate_then (step P E) (hintIterate_then (step P E) hRunG hRunS) hRunT,
    by omega, by omega, ⟨⟨?_, ?_, ?_, ?_, ?_, hObs⟩, hHeaderOut, hCtxOut, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hAfterT _ le_rfl, hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ le_rfl]
    exact hMeta.outside_pointer
  · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
    exact hMeta.bitmap_pointer
  · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
    exact hMeta.gather.count_value
  · rw [hFrameT _ (Or.inl (by omega)), hUnchangedS _ (by omega) (by omega) (by omega),
      hFrameG _ (Or.inl hOutside)]
    exact hMeta.outside_count
  · intro i
    have hi := i.isLt
    rw [hFrameT _ (Or.inl (by omega)), hUnchangedS _ (by omega) (by omega) (by omega)]
    exact (hListG i.val (hHintLen.symm ▸ hi)).trans (hCoords i).symm
  · rw [hAfterT _ (by omega), hMemS]
    simp [hintRowSizedMem, Function.update_of_ne (by omega : parent + 4 ≠ parent + 17),
      Function.update_of_ne (by omega : parent + 4 ≠ parent + 5)]
  · rw [hAfterT _ (by omega), hMemS]
    simp [hintRowSizedMem, Function.update_of_ne (by omega : parent + 5 ≠ parent + 17)]
  · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
    exact hMeta.hint_limit
  · intro addr hAway
    rcases hAway with hBefore | hAfter
    · rw [hFrameT _ (Or.inl (by omega)), hUnchangedS _ (by omega) (by omega) (by omega), hFrameG _ (Or.inl hBefore)]
    · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]

  · intro i hi h4 h5
    rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]

theorem hintPreparedPredictStmt_stable_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (c : ℕ)
    (N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hContext : state.regs 14 = G.context)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj (min BY (Nj - G.hints)) parent outsideBase bitmapBase)
    (j : Fin m) (hRowValue : G.row = j.val) (hBX : BX < 2 ^ E.W)
    (hMeta : HintRowPrepareMetadata G parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount state.mem)
    (hm : 0 < m) (hRow : G.row < m) (hNj : Nj = rowLen N m G.row)
    (hHintLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hHintLen.symm ▸ i.isLt))
    (hRowsFit : m < 2 ^ E.W) (hNjFit : Nj < 2 ^ E.W)
    (hBYFit : BY + 1 < 2 ^ E.W) (hTableFit : table + (BY + 1) * G.hints < 2 ^ E.W)
    (hGatherEnd : G.hintList + Nj ≤ parent)
    (hHintSeparate : parent ≤ hintSource) (hHintFit : hintSource < 2 ^ E.W)
    (hHintSpan : hintSource + N ≤ 2 ^ E.W)
    (hTranscriptSeparate : G.hintList + G.hints + 2 * G.rows ≤ transcriptSource)
    (hTranscriptOutsideGather : G.hintList + Nj ≤ transcriptSource)
    (hTranscriptAfterHeader : parent + 18 ≤ transcriptSource)
    (hTranscriptFit : transcriptSource < 2 ^ E.W)
    (hTranscriptSpan : ∀ t : Fin G.rows, transcriptSource + t.val * m < 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (hintSource + c.val) = hintTruth (c.val ∈ J))
    (hTranscript : ∀ t : Fin G.rows, state.mem (transcriptSource + t.val * m) = (v t).val)
    (hWaitTable : table + (BY + 1) * G.hints + min BY (Nj - G.hints) < 2 ^ E.W)
    (hLookup : ∀ r ≤ min BY (Nj - G.hints),
      E.det (table + (BY + 1) * G.hints + r) = min G.steps (sigma G.hints Nj r + c))
    (hCoeff : ∀ hNext : G.rows < G.steps, ∀ q : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + q.val) = (beta ⟨G.rows, hNext⟩ q).val)
    (hAt : At P base (hintPreparedPredictStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1584) state (fun k out =>
      k ≤ (hintRowOuterBudget G Nj (min BY (Nj - G.hints)) + 2) *
        (min BY (Nj - G.hints) + 1) + 12 * Nj + 9 * G.rows + 107 ∧
      hintRowOutput out = workerPredict N m G.steps G.buckets BX BY c j beta
        (rowImage N m π j.val J) (List.ofFn v) ∧
      out.regs 14 = G.context ∧
      CRMemFrame bitmapBase (G.pivotRow + G.rows) state.mem out.mem ∧
      (∃ count, HintRowInput G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
      (∃ index, HintGaussHeader G index out.mem) ∧
      (∀ i, 9 ≤ i → i < 16 → out.mem (parent + i) = state.mem (parent + i))) := by
  let maxR := min BY (Nj - G.hints)
  let tableAddr := table + (BY + 1) * G.hints
  have hh := hPublic.outside_span
  obtain ⟨hBitmapStart, hHeaderEnd, hZones⟩ := hintPrepared_frames hPublic
  have hImage := hintRowPrepared_image G coords N m π J hm hRow hHintLen hCoords
  have hNj' : rowLen N m j.val = Nj := by rw [← hRowValue, hNj]
  obtain ⟨hAtPrep, hAtWork⟩ := At.seqStmt hAt
  change At P base (hintRowPrepareStmt.compile base) at hAtPrep
  change At P (base + 95) (hintRowPredictStmt.compile (base + 95)) at hAtWork
  obtain ⟨_, kP, mid, hRunP, hPcP, hCostP, hp, hFrameP, hStableP⟩ :=
    hintRowPrepareStmt_stable_sem G coords v N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount π J
      P E state base hPublic.parent_eq hContext hPublic.fits hMeta hm hRow hNj hHintLen hCoords hRowsFit hNjFit
      hBYFit hTableFit (by omega) hGatherEnd hPublic.source hHintSeparate hHintFit hHintSpan
      hTranscriptSeparate hTranscriptOutsideGather hTranscriptAfterHeader hTranscriptFit hTranscriptSpan hPerm hBits hTranscript
      hAtPrep hPc
  obtain ⟨_, kW, out, hRunW, hPcW, hCostW, hOut, hInputOut, hHeaderOut, hCtxOut, hFrameW⟩ :=
    hintRowPredictStmt_sem G coords beta hPrefix N m Nj parent outsideBase bitmapBase maxR tableAddr BX BY c oldCount j v
      P E mid (base + 95) hPublic hp.input hp.header hp.context hNj' rfl hBX hp.hint_limit
      hp.max_count hp.wait_table hWaitTable hLookup hCoeff hAtWork hPcP
  have hOutput : hintRowOutput out = workerPredict N m G.steps G.buckets BX BY c j beta
      (rowImage N m π j.val J) (List.ofFn v) := by
    have hAlign : Finset.univ.image (fun t => (coords t).val) = rowImage N m π j.val J := hImage.trans (by rw [← hRowValue])
    simpa only [hAlign] using hOut
  refine ⟨hPc, kW + kP, out, hintIterate_then (step P E) hRunP hRunW, by omega,
    by dsimp only [maxR] at hCostW; omega, hOutput, hCtxOut, ?_, hInputOut, hHeaderOut, ?_⟩
  · intro addr hAway
    obtain ⟨hB, hO, h3, _, _, hR, hG⟩ := hZones addr hAway
    rw [hFrameW addr hB hO h3 hR hG]
    apply hFrameP
    rcases hAway with hBefore | hAfter
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · intro i hi hi'
    rw [hFrameW.parent hPublic i (by omega) hi', hStableP i hi' (by omega) (by omega)]

theorem hintPreparedFinalStmt_stable_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hContext : state.regs 14 = G.context)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj (min BY (Nj - G.hints)) parent outsideBase bitmapBase)
    (j : Fin m) (hRowValue : G.row = j.val) (hBX : BX < 2 ^ E.W)
    (hMeta : HintRowPrepareMetadata G parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount state.mem)
    (hm : 0 < m) (hRow : G.row < m) (hNj : Nj = rowLen N m G.row)
    (hHintLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hHintLen.symm ▸ i.isLt))
    (hRowsFit : m < 2 ^ E.W) (hNjFit : Nj < 2 ^ E.W)
    (hBYFit : BY + 1 < 2 ^ E.W) (hTableFit : table + (BY + 1) * G.hints < 2 ^ E.W)
    (hGatherEnd : G.hintList + Nj ≤ parent)
    (hHintSeparate : parent ≤ hintSource) (hHintFit : hintSource < 2 ^ E.W)
    (hHintSpan : hintSource + N ≤ 2 ^ E.W)
    (hTranscriptSeparate : G.hintList + G.hints + 2 * G.rows ≤ transcriptSource)
    (hTranscriptOutsideGather : G.hintList + Nj ≤ transcriptSource)
    (hTranscriptAfterHeader : parent + 18 ≤ transcriptSource)
    (hTranscriptFit : transcriptSource < 2 ^ E.W)
    (hTranscriptSpan : ∀ t : Fin G.rows, transcriptSource + t.val * m < 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (hintSource + c.val) = hintTruth (c.val ∈ J))
    (hTranscript : ∀ t : Fin G.rows, state.mem (transcriptSource + t.val * m) = (v t).val)
    (hAt : At P base (hintPreparedFinalStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1653) state (fun k out =>
      k ≤ (hintFinalBudget G Nj (min BY (Nj - G.hints)) + 2) *
        (min BY (Nj - G.hints) + 1) + hintFinalBudget G Nj (min BY (Nj - G.hints)) +
        26 * Nj + 9 * G.rows + 18 * G.hints + 8 * min BY (Nj - G.hints) + 186 ∧
      (∀ q < Nj, out.mem (bitmapBase + q) = hintTruth (q ∈
        workerFinal N m G.steps G.buckets BX BY j beta (rowImage N m π j.val J) (List.ofFn v))) ∧
      out.regs 14 = G.context ∧
      CRMemFrame bitmapBase (G.pivotRow + G.rows) state.mem out.mem ∧
      (∃ count, HintRowInput G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
      (∃ index, HintGaussHeader G index out.mem) ∧
      (∀ i, 9 ≤ i → i < 16 → out.mem (parent + i) = state.mem (parent + i))) := by
  let maxR := min BY (Nj - G.hints)
  have hh := hPublic.outside_span
  obtain ⟨hBitmapStart, hHeaderEnd, hZones⟩ := hintPrepared_frames hPublic
  have hImage := hintRowPrepared_image G coords N m π J hm hRow hHintLen hCoords
  have hNj' : rowLen N m j.val = Nj := by rw [← hRowValue, hNj]
  obtain ⟨hAtPrep, hAtWork⟩ := At.seqStmt hAt
  change At P base (hintRowPrepareStmt.compile base) at hAtPrep
  change At P (base + 95) (hintRowFinalStmt.compile (base + 95)) at hAtWork
  obtain ⟨_, kP, mid, hRunP, hPcP, hCostP, hp, hFrameP, hStableP⟩ :=
    hintRowPrepareStmt_stable_sem G coords v N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount π J
      P E state base hPublic.parent_eq hContext hPublic.fits hMeta hm hRow hNj hHintLen hCoords hRowsFit hNjFit
      hBYFit hTableFit (by omega) hGatherEnd hPublic.source hHintSeparate hHintFit hHintSpan
      hTranscriptSeparate hTranscriptOutsideGather hTranscriptAfterHeader hTranscriptFit hTranscriptSpan hPerm hBits hTranscript
      hAtPrep hPc
  obtain ⟨_, kW, out, hRunW, hPcW, hCostW, hOut, hInputOut, hHeaderOut, hCtxOut, hFrameW⟩ :=
    hintRowFinalStmt_sem G coords beta hPrefix N m Nj parent outsideBase bitmapBase maxR BX BY oldCount j v
      P E mid (base + 95) hPublic hp.input hp.header hp.context hNj' rfl hBX hp.hint_limit
      hp.max_count hAtWork hPcP
  refine ⟨hPc, kW + kP, out, hintIterate_then (step P E) hRunP hRunW, by omega,
    by dsimp only [maxR] at hCostW; omega, ?_, hCtxOut, ?_, hInputOut, hHeaderOut, ?_⟩
  · intro q hq
    have hAlign : Finset.univ.image (fun t => (coords t).val) = rowImage N m π j.val J := hImage.trans (by rw [← hRowValue])
    simpa only [hAlign] using hOut q hq
  · intro addr hAway
    obtain ⟨hB, hO, h3, h7, h8, hR, hG⟩ := hZones addr hAway
    have hEq := hFrameW addr hB hO h3 h7 h8 hR hG
    rw [hEq]
    apply hFrameP
    rcases hAway with hBefore | hAfter
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · intro i hi hi'
    rw [hFrameW.parent hPublic i (by omega) hi' (by omega) (by omega), hStableP i hi' (by omega) (by omega)]


end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPreparedPredictStmt_stable_sem
#print axioms LinearSetReconciliation327.Main.hintPreparedFinalStmt_stable_sem
end -- Def_LinearSetReconciliation327_Main_HintPreparedStable20261120

section -- Def_LinearSetReconciliation327_Main_HintActionSwitch20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDispatchDec : List Instr := [.sub 1 1 15]

def hintActionSwitch : List Stmt → Stmt
  | [] => .code []
  | action :: rest =>
      .ite (.neqz 1) (.seq (.code hintDispatchDec) (hintActionSwitch rest)) action

structure HintDispatchSame (s t : RAMState) : Prop where
  memory : t.mem = s.mem
  regs : ∀ r : Fin 16, r ≠ 1 → t.regs r = s.regs r

theorem HintDispatchSame.trans {s t u : RAMState} (h : HintDispatchSame s t) (h' : HintDispatchSame t u) :
    HintDispatchSame s u :=
  ⟨h'.memory.trans h.memory, fun r hr => (h'.regs r hr).trans (h.regs r hr)⟩

theorem hintDispatchDec_spec (E : RAMEnv) (s : RAMState) (tag : ℕ)
    (hTag : s.regs 1 = tag + 1) (hTagFit : tag < 2 ^ E.W) (hOne : s.regs 15 = 1) :
    let out := runBlock hintDispatchDec E s
    out.pc = s.pc + 1 ∧ out.regs 1 = tag ∧ HintDispatchSame s out := by
  have hSub : (tag + 1) + 2 ^ E.W - 1 = tag + 2 ^ E.W := by omega
  refine ⟨?_, ?_, ⟨rfl, ?_⟩⟩
  · simp [hintDispatchDec, runBlock, execInstr]
  · simp [hintDispatchDec, runBlock, execInstr, hTag, hOne, hSub, Nat.mod_eq_of_lt hTagFit]
  · intro r hr
    simp [hintDispatchDec, runBlock, execInstr, hr]

/-- A fixed switch on the event tag in register 1. Each selected action sees
register 1 equal to zero and the original memory and all other registers. -/
theorem hintActionSwitch_sem (actions : List Stmt) (action : Stmt) (tag : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base budget : ℕ) (Q : RAMState → Prop)
    (hWord : 1 < 2 ^ E.W) (hTag : state.regs 1 = tag) (hTagFit : tag < 2 ^ E.W)
    (hOne : state.regs 15 = 1) (hSelect : actions[tag]? = some action)
    (hAt : At P base ((hintActionSwitch actions).compile base)) (hPc : state.pc = base)
    (hAction : ∀ entry (s : RAMState), HintDispatchSame state s → s.regs 1 = 0 → s.pc = entry →
      At P entry (action.compile entry) →
      Sem P E entry (entry + action.len) s (fun k out => k ≤ budget ∧ Q out))
    (hQpc : ∀ out pc, Q out → Q {out with pc := pc}) :
    Sem P E base (base + (hintActionSwitch actions).len) state (fun k out => k ≤ budget + 3 * tag + 2 ∧ Q out) := by
  induction actions generalizing tag base state with
  | nil => simp at hSelect
  | cons first rest ih =>
    let tail := Stmt.seq (.code hintDispatchDec) (hintActionSwitch rest)
    change At P base ((Stmt.ite (.neqz 1) tail first).compile base) at hAt
    change Sem P E base (base + (Stmt.ite (.neqz 1) tail first).len) state _
    have hEnd : base + (Stmt.ite (.neqz 1) tail first).len =
        base + (Cond.neqz 1).code.length + tail.len + first.len + 3 := by
      simp only [Stmt.len]
      omega
    rw [hEnd]
    apply Sem.ite P E base (.neqz 1) tail first state _ hAt hWord hPc
    · intro hGo
      have hPositive : tag ≠ 0 := by intro hZero; apply hGo; change state.regs 1 = 0; omega
      obtain ⟨t, ht⟩ : ∃ t, tag = t + 1 := ⟨tag - 1, by omega⟩
      have hSelectT : rest[t]? = some action := by
        simpa only [ht, List.getElem?_cons_succ] using hSelect
      let entered : RAMState := {state with pc := base + 1}
      have hTailAt : At P (base + 1) (tail.compile (base + 1)) := (at_ite hAt).2.2.1
      change Sem P E (base + 1) (base + 1 + tail.len) entered _
      obtain ⟨hDecAt, hRestAt⟩ := At.seqStmt hTailAt
      change At P (base + 1) hintDispatchDec at hDecAt
      change At P (base + 1 + 1) ((hintActionSwitch rest).compile (base + 1 + 1)) at hRestAt
      have hDec := hintDispatchDec_spec E entered t (by exact hTag.trans ht) (by omega) hOne
      generalize hD : runBlock hintDispatchDec E entered = mid at hDec
      obtain ⟨hPcD, hTagD, hSameD⟩ := hDec
      have hSame : HintDispatchSame state mid := ⟨hSameD.memory, hSameD.regs⟩
      have hRunD : (step P E)^[1] entered = mid := by
        have h := iterate_runBlock_of_at P E hintDispatchDec entered hDecAt
          (by simp [hintDispatchDec, NoBranch, Instr.NoBranchI])
        rw [hD] at h
        exact h
      have hSuffix := ih t mid (base + 1 + 1) hTagD (by omega)
        ((hSame.regs 15 (by decide)).trans hOne) hSelectT hRestAt hPcD
        (fun entry st hSame' => hAction entry st (hSame.trans hSame'))
      obtain ⟨_, k, out, hRun, hPcOut, hCost, hPost⟩ := hSuffix
      refine ⟨rfl, k + 1, out, hintIterate_then (step P E) hRunD hRun, ?_, ?_, hQpc _ _ hPost⟩
      · change out.pc = base + 1 + (1 + (hintActionSwitch rest).len)
        omega
      · change 1 + (k + 1) + 1 ≤ budget + 3 * tag + 2
        omega
    · intro hStop
      have hZero : tag = 0 := by
        by_contra hNe
        exact hStop (by change state.regs 1 ≠ 0; rwa [hTag])
      have hFirst : first = action := by simpa [hZero] using hSelect
      subst first
      let start := base + tail.len + 2
      let entered : RAMState := {state with pc := start}
      have hRight : At P start (action.compile start) := by
        have h := (at_ite hAt).2.2.2.2.1
        simpa only [Cond.code, List.length_nil, Nat.add_zero, Nat.add_assoc,
          show 1 + (tail.len + 1) = tail.len + 2 by omega, start] using h
      simp only [Cond.code, List.length_nil, Nat.add_zero, Nat.zero_add]
      rw [show base + 1 + tail.len + 1 + action.len = start + action.len by dsimp [start]; omega]
      change Sem P E start (start + action.len) entered _
      have hNative := hAction _ entered ⟨rfl, fun _ _ => rfl⟩ (hTag.trans hZero) rfl hRight
      apply Sem.mono hNative
      intro k out hOut
      exact ⟨by change 1 + k + 1 ≤ budget + 3 * tag + 2; omega, hQpc _ _ hOut.2⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintActionSwitch_sem
end -- Def_LinearSetReconciliation327_Main_HintActionSwitch20261120

section -- Def_LinearSetReconciliation327_Main_HintDispatchIO20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintDispatchTable (E : RAMEnv) (table : ℕ) (events : List (ℕ × ℕ)) : Prop where
  span : table + 2 * events.length ≤ 2 ^ E.W
  tag : ∀ j : Fin events.length, E.det (table + 2 * j.val) = events[j.val].1
  descriptor : ∀ j : Fin events.length, E.det (table + 2 * j.val + 1) = events[j.val].2
  fits : ∀ j : Fin events.length, events[j.val].1 < 2 ^ E.W ∧ events[j.val].2 < 2 ^ E.W

structure HintDispatchData (control table count index : ℕ) (s : RAMState) : Prop where
  context : s.regs 14 = control
  table_pointer : s.mem control = table
  size : s.mem (control + 1) = count
  cursor : s.mem (control + 2) = index

def hintDispatchFetch : List Instr :=
  [.imm 5 2, .add 3 14 5, .load 0 3, .load 4 14, .mul 7 0 5, .add 7 4 7,
    .qDet 1 7, .imm 15 1, .add 7 7 15, .qDet 6 7]
def hintDispatchInit : List Instr :=
  [.imm 3 2, .add 3 14 3, .imm 0 0, .store 3 0, .imm 15 1, .add 4 14 15, .load 6 4, .lt 13 0 6]
def hintDispatchAdvance : List Instr :=
  [.imm 3 2, .add 3 14 3, .load 0 3, .imm 15 1, .add 0 0 15, .store 3 0,
    .add 4 14 15, .load 6 4, .lt 13 0 6]

theorem hintDispatchFetch_spec (E : RAMEnv) (s : RAMState)
    (control table : ℕ) (events : List (ℕ × ℕ)) (j : Fin events.length)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W)
    (hData : HintDispatchData control table events.length j.val s) (hTable : HintDispatchTable E table events) :
    let out := runBlock hintDispatchFetch E s
    out.pc = s.pc + 10 ∧ out.regs 1 = events[j.val].1 ∧ out.regs 6 = events[j.val].2 ∧ out.regs 15 = 1 ∧
      out.mem = s.mem ∧ HintDispatchData control table events.length j.val out := by
  have hSpan := hTable.span
  have hJ := j.isLt
  have hTag := hTable.tag j
  have hDesc := hTable.descriptor j
  have hTagFit := (hTable.fits j).1
  have hDescFit := (hTable.fits j).2
  have hOne : 1 < 2 ^ E.W := by omega
  have hTbl : table < 2 ^ E.W := by omega
  have hIndex : j.val < 2 ^ E.W := by omega
  have hMul : j.val * 2 < 2 ^ E.W := by omega
  have hAddr : table + j.val * 2 < 2 ^ E.W := by omega
  have hAddr2 : table + j.val * 2 + 1 < 2 ^ E.W := by omega
  rw [Nat.mul_comm 2 j.val] at hTag hDesc
  refine ⟨?_, ?_, ?_, ?_, rfl, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintDispatchFetch, runBlock, execInstr, hData.context, hData.table_pointer, hData.cursor,
      hTag, hDesc, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hTbl,
      Nat.mod_eq_of_lt hControl, Nat.mod_eq_of_lt hIndex, Nat.mod_eq_of_lt hMul,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hAddr2, Nat.mod_eq_of_lt hTagFit,
      Nat.mod_eq_of_lt hDescFit, hData.size]

theorem hintDispatchInit_spec (E : RAMEnv) (s : RAMState) (control table count old : ℕ)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hData : HintDispatchData control table count old s) :
    let out := runBlock hintDispatchInit E s
    out.pc = s.pc + 8 ∧ out.mem = Function.update s.mem (control + 2) 0 ∧
      out.regs 13 = hintTruth (0 < count) ∧ HintDispatchData control table count 0 out := by
  classical
  have hOne : 1 < 2 ^ E.W := by omega
  have hA1 : control + 1 < 2 ^ E.W := by omega
  have hNe0 : control ≠ control + 2 := by omega
  have hNe1 : control + 1 ≠ control + 2 := by omega
  by_cases hc : 0 < count <;>
    refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
      simp [hintDispatchInit, runBlock, execInstr, hData.context, hData.table_pointer, hData.size,
        hintTruth, hc, Function.update_of_ne hNe0, Function.update_of_ne hNe1,
        Nat.mod_eq_of_lt hControl, Nat.mod_eq_of_lt hA1, Nat.mod_eq_of_lt hCount,
        Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne]

theorem hintDispatchAdvance_spec (E : RAMEnv) (s : RAMState) (control table count j : ℕ)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : count < 2 ^ E.W) (hj : j < count)
    (hData : HintDispatchData control table count j s) :
    let out := runBlock hintDispatchAdvance E s
    out.pc = s.pc + 9 ∧ out.mem = Function.update s.mem (control + 2) (j + 1) ∧
      out.regs 13 = hintTruth (j + 1 < count) ∧ HintDispatchData control table count (j + 1) out := by
  classical
  have hOne : 1 < 2 ^ E.W := by omega
  have hA1 : control + 1 < 2 ^ E.W := by omega
  have hNe0 : control ≠ control + 2 := by omega
  have hNe1 : control + 1 ≠ control + 2 := by omega
  have hJ : j < 2 ^ E.W := by omega
  have hNext : j + 1 < 2 ^ E.W := by omega
  by_cases hc : j + 1 < count <;>
    refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
      simp [hintDispatchAdvance, runBlock, execInstr, hData.context, hData.table_pointer, hData.size,
        hData.cursor, hintTruth, hc, Function.update_of_ne hNe0, Function.update_of_ne hNe1,
        Nat.mod_eq_of_lt hControl, Nat.mod_eq_of_lt hA1, Nat.mod_eq_of_lt hCount,
        Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hJ, Nat.mod_eq_of_lt hNext]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDispatchFetch_spec
#print axioms LinearSetReconciliation327.Main.hintDispatchAdvance_spec
end -- Def_LinearSetReconciliation327_Main_HintDispatchIO20261120

section -- Def_LinearSetReconciliation327_Main_HintDispatchBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDispatchBody (actions : List Stmt) : Stmt :=
  .seq (.code hintDispatchFetch) (.seq (hintActionSwitch actions) (.code hintDispatchAdvance))

theorem hintDispatchBody_len (actions : List Stmt) :
    (hintDispatchBody actions).len = 10 + ((hintActionSwitch actions).len + 9) := rfl

/-- The work claim for a table of actions. The descriptor is supplied in
register 6. Actions return to the control area and retain the schedule cursor. -/
def HintDispatchActions (P : Program) (E : RAMEnv) (control table : ℕ)
    (actions : List Stmt) (events : List (ℕ × ℕ)) (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) : Prop :=
  ∀ (j : Fin events.length) (action : Stmt) (base : ℕ) (s : RAMState),
    actions[events[j.val].1]? = some action → At P base (action.compile base) → s.pc = base →
    s.regs 6 = events[j.val].2 → s.regs 1 = 0 → HintDispatchData control table events.length j.val s →
    I j.val s.mem →
    Sem P E base (base + action.len) s (fun k out => k ≤ budget j.val ∧
      I (j.val + 1) out.mem ∧ HintDispatchData control table events.length j.val out)

theorem HintDispatchData.pc {control table count index : ℕ} {s : RAMState}
    (h : HintDispatchData control table count index s) (pc : ℕ) :
    HintDispatchData control table count index {s with pc := pc} :=
  ⟨h.context, h.table_pointer, h.size, h.cursor⟩

theorem HintDispatchData.switch {control table count index : ℕ} {s t : RAMState}
    (h : HintDispatchData control table count index s) (hSame : HintDispatchSame s t) :
    HintDispatchData control table count index t :=
  ⟨(hSame.regs 14 (by decide)).trans h.context,
    (congrFun hSame.memory control).trans h.table_pointer,
    (congrFun hSame.memory (control + 1)).trans h.size,
    (congrFun hSame.memory (control + 2)).trans h.cursor⟩

theorem hintDispatchBody_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (j : Fin events.length)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events) (hTag : events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length j.val state) (hInv : I j.val state.mem)
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintDispatchActions P E control table actions events budget I)
    (hAt : At P base ((hintDispatchBody actions).compile base)) (hPc : state.pc = base) :
    Sem P E base (base + (hintDispatchBody actions).len) state (fun k out =>
      k ≤ budget j.val + 3 * actions.length + 21 ∧ I (j.val + 1) out.mem ∧
      HintDispatchData control table events.length (j.val + 1) out ∧ out.regs 13 = hintTruth (j.val + 1 < events.length)) := by
  let switch := hintActionSwitch actions
  obtain ⟨hFetchAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintDispatchFetch at hFetchAt
  change At P (base + 10) ((Stmt.seq switch (.code hintDispatchAdvance)).compile (base + 10)) at hRestAt
  obtain ⟨hSwitchAt, hAdvanceAt⟩ := At.seqStmt hRestAt
  change At P (base + 10) (switch.compile (base + 10)) at hSwitchAt
  change At P (base + 10 + switch.len) hintDispatchAdvance at hAdvanceAt
  have hFetch := hintDispatchFetch_spec E state control table events j hWord hControl hData hTable
  generalize hF : runBlock hintDispatchFetch E state = sF at hFetch
  obtain ⟨hPcF, hTagF, hDescF, hOneF, hMemF, hDataF⟩ := hFetch
  have hRunF : (step P E)^[10] state = sF := by
    have hh := iterate_runBlock_of_at P E hintDispatchFetch state (by rwa [hPc])
      (by simp [hintDispatchFetch, NoBranch, Instr.NoBranchI])
    rw [hF] at hh
    exact hh
  let action := actions[events[j.val].1]
  have hSelect : actions[events[j.val].1]? = some action := List.getElem?_eq_getElem hTag
  have hSwitch := hintActionSwitch_sem actions action events[j.val].1 P E sF (base + 10) (budget j.val)
    (fun out => I (j.val + 1) out.mem ∧ HintDispatchData control table events.length j.val out)
    (by omega) hTagF (hTable.fits j).1 hOneF hSelect hSwitchAt (by omega)
    (by
      intro entry s hSame hZero hPcS hAtS
      exact hActions j action entry s hSelect hAtS hPcS ((hSame.regs 6 (by decide)).trans hDescF)
        hZero (hDataF.switch hSame) (by rw [hSame.memory, hMemF]; exact hInv))
    (by intro out pc hPost; exact ⟨hPost.1, hPost.2.pc pc⟩)
  obtain ⟨_, kS, mid, hRunS, hPcS, hCostS, hInvS, hDataS⟩ := hSwitch
  have hAdvance := hintDispatchAdvance_spec E mid control table events.length j.val hWord hControl hCount j.isLt hDataS
  generalize hA : runBlock hintDispatchAdvance E mid = out at hAdvance
  obtain ⟨hPcA, hMemA, hGoA, hDataA⟩ := hAdvance
  have hRunA : (step P E)^[9] mid = out := by
    have hh := iterate_runBlock_of_at P E hintDispatchAdvance mid (by rwa [hPcS])
      (by simp [hintDispatchAdvance, NoBranch, Instr.NoBranchI])
    rw [hA] at hh
    exact hh
  refine ⟨hPc, 9 + (kS + 10), out, hintIterate_then (step P E) (hintIterate_then (step P E) hRunF hRunS) hRunA,
    ?_, by omega, ?_, hDataA, hGoA⟩
  · rw [hPcA, hPcS, hintDispatchBody_len]
    change base + 10 + switch.len + 9 = base + (10 + (switch.len + 9))
    omega
  · rw [hMemA]
    exact hCursor _ _ _ hInvS

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDispatchBody_sem
end -- Def_LinearSetReconciliation327_Main_HintDispatchBody20261120

section -- Def_LinearSetReconciliation327_Main_HintDispatch20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDispatchLoop (actions : List Stmt) : Stmt := .loop (.neqz 13) (hintDispatchBody actions)
def hintDispatchStmt (actions : List Stmt) : Stmt := .seq (.code hintDispatchInit) (hintDispatchLoop actions)

def hintDispatchBudget (actions : List Stmt) (count : ℕ) (budget : ℕ → ℕ) : ℕ :=
  ∑ left ∈ Finset.range count, (budget (count - (left + 1)) + 3 * actions.length + 23)

theorem hintDispatchLoop_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events) (hTags : ∀ j : Fin events.length, events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length 0 state) (hInv : I 0 state.mem)
    (hGoInitial : state.regs 13 = hintTruth (0 < events.length))
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintDispatchActions P E control table actions events budget I)
    (hAt : At P base ((hintDispatchLoop actions).compile base)) (hPc : state.pc = base) :
    Sem P E base (base + (hintDispatchLoop actions).len) state (fun k out =>
      k ≤ hintDispatchBudget actions events.length budget + 1 ∧ I events.length out.mem ∧
      HintDispatchData control table events.length events.length out) := by
  let count := events.length
  let J : ℕ → RAMState → Prop := fun left st =>
    ∃ j, j + left = count ∧ HintDispatchData control table count j st ∧ I j st.mem ∧
      st.regs 13 = hintTruth (j < count)
  let B : ℕ → ℕ := fun left => budget (count - (left + 1)) + 3 * actions.length + 21
  have hBodyAt : At P (base + 1) ((hintDispatchBody actions).compile (base + 1)) := (at_loop hAt).2.2.1
  have hJpc : ∀ left st pc, J left st → J left {st with pc := pc} := by
    intro left st pc h
    obtain ⟨j, hLeft, hDataJ, hInvJ, hGo⟩ := h
    exact ⟨j, hLeft, hDataJ.pc pc, hInvJ, hGo⟩
  have hTest : ∀ left st, J left st → J left (runBlock (Cond.neqz 13).code E st) := fun _ _ h => h
  have hGo : ∀ left st, J (left + 1) st → (Cond.neqz 13).eval st := by
    intro left st h
    obtain ⟨j, hLeft, _, _, hFlag⟩ := h
    have hj : j < count := by omega
    change st.regs 13 ≠ 0
    rw [hFlag]
    simp [hintTruth, hj]
  have hStop : ∀ st, J 0 st → ¬ (Cond.neqz 13).eval st := by
    intro st h
    obtain ⟨j, hLeft, _, _, hFlag⟩ := h
    have hj : ¬ j < count := by omega
    change ¬ st.regs 13 ≠ 0
    rw [hFlag]
    simp [hintTruth, hj]
  have hBody : ∀ left st, J (left + 1) st → st.pc = base + (Cond.neqz 13).code.length + 1 →
      Sem P E (base + (Cond.neqz 13).code.length + 1)
        (base + (Cond.neqz 13).code.length + 1 + (hintDispatchBody actions).len) st
        (fun k out => k ≤ B left ∧ J left out) := by
    intro left st h hStart
    obtain ⟨j, hLeft, hDataJ, hInvJ, _⟩ := h
    have hJlt : j < events.length := by
      change j < count
      omega
    let pos : Fin events.length := ⟨j, hJlt⟩
    have hNative := hintDispatchBody_sem P E st control table (base + 1) actions events budget I pos
      hWord hControl hCount hTable (hTags pos) hDataJ hInvJ hCursor hActions hBodyAt hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hInvOut, hDataOut, hFlag⟩ := hOut
    have hPos : count - (left + 1) = j := by omega
    refine ⟨?_, j + 1, by omega, hDataOut, hInvOut, hFlag⟩
    dsimp only [B]
    rw [hPos]
    exact hCost
  have hInitial : J count state := ⟨0, Nat.zero_add _, hData, hInv, hGoInitial⟩
  have hNative := hintLoopBudget_sem P E base (.neqz 13) (hintDispatchBody actions) hAt (by omega)
    J B hJpc hTest hGo hStop hBody count state hInitial hPc
  have hEnd : base + (hintDispatchLoop actions).len = base + (Cond.neqz 13).code.length +
      (hintDispatchBody actions).len + 2 := by simp [hintDispatchLoop, Stmt.len, Nat.add_assoc]
  rw [hEnd]
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hLeft, hDataOut, hInvOut, _⟩ := hOut
  have hEq : j = events.length := by simpa [count] using hLeft
  subst j
  refine ⟨?_, hInvOut, hDataOut⟩
  simp only [Cond.code, List.length_nil, Nat.zero_add, B] at hCost
  unfold hintDispatchBudget
  simpa only [count, Nat.add_assoc] using hCost

theorem hintDispatchStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base old : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events) (hTags : ∀ j : Fin events.length, events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length old state) (hInv : I 0 state.mem)
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintDispatchActions P E control table actions events budget I)
    (hAt : At P base ((hintDispatchStmt actions).compile base)) (hPc : state.pc = base) :
    Sem P E base (base + (hintDispatchStmt actions).len) state (fun k out =>
      k ≤ hintDispatchBudget actions events.length budget + 9 ∧ I events.length out.mem ∧
      HintDispatchData control table events.length events.length out) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintDispatchInit at hInitAt
  change At P (base + 8) ((hintDispatchLoop actions).compile (base + 8)) at hLoopAt
  have hInit := hintDispatchInit_spec E state control table events.length old hWord hControl hCount hData
  generalize hI : runBlock hintDispatchInit E state = mid at hInit
  obtain ⟨hPcI, hMemI, hGoI, hDataI⟩ := hInit
  have hRunI : (step P E)^[8] state = mid := by
    have hh := iterate_runBlock_of_at P E hintDispatchInit state (by rwa [hPc])
      (by simp [hintDispatchInit, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  have hInvI : I 0 mid.mem := by rw [hMemI]; exact hCursor _ _ _ hInv
  obtain ⟨_, k, out, hRun, hEnd, hCost, hInvOut, hDataOut⟩ :=
    hintDispatchLoop_sem P E mid control table (base + 8) actions events budget I hWord hControl hCount
      hTable hTags hDataI hInvI hGoI hCursor hActions hLoopAt (by omega)
  refine ⟨hPc, k + 8, out, hintIterate_then (step P E) hRunI hRun, ?_, by omega, hInvOut, hDataOut⟩
  change out.pc = base + (8 + (hintDispatchLoop actions).len)
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDispatchStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintDispatch20261120

section -- Def_LinearSetReconciliation327_Main_HintLocatedSwitch20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- The absolute entry address of a selected action in a compiled switch. -/
def hintActionEntry : List Stmt → ℕ → ℕ → ℕ
  | [], base, _ => base
  | _ :: rest, base, 0 => base + (hintActionSwitch rest).len + 3
  | _ :: rest, base, n + 1 => hintActionEntry rest (base + 2) n

/-- A fixed switch on the event tag in register 1. Each selected action sees
register 1 equal to zero and the original memory and all other registers. -/
theorem hintLocatedSwitch_sem (actions : List Stmt) (action : Stmt) (tag : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base budget : ℕ) (Q : RAMState → Prop)
    (hWord : 1 < 2 ^ E.W) (hTag : state.regs 1 = tag) (hTagFit : tag < 2 ^ E.W)
    (hOne : state.regs 15 = 1) (hSelect : actions[tag]? = some action)
    (hAt : At P base ((hintActionSwitch actions).compile base)) (hPc : state.pc = base)
    (hAction : ∀ entry (s : RAMState), entry = hintActionEntry actions base tag → HintDispatchSame state s → s.regs 1 = 0 → s.pc = entry →
      At P entry (action.compile entry) →
      Sem P E entry (entry + action.len) s (fun k out => k ≤ budget ∧ Q out))
    (hQpc : ∀ out pc, Q out → Q {out with pc := pc}) :
    Sem P E base (base + (hintActionSwitch actions).len) state (fun k out => k ≤ budget + 3 * tag + 2 ∧ Q out) := by
  induction actions generalizing tag base state with
  | nil => simp at hSelect
  | cons first rest ih =>
    let tail := Stmt.seq (.code hintDispatchDec) (hintActionSwitch rest)
    change At P base ((Stmt.ite (.neqz 1) tail first).compile base) at hAt
    change Sem P E base (base + (Stmt.ite (.neqz 1) tail first).len) state _
    have hEnd : base + (Stmt.ite (.neqz 1) tail first).len =
        base + (Cond.neqz 1).code.length + tail.len + first.len + 3 := by
      simp only [Stmt.len]
      omega
    rw [hEnd]
    apply Sem.ite P E base (.neqz 1) tail first state _ hAt hWord hPc
    · intro hGo
      have hPositive : tag ≠ 0 := by intro hZero; apply hGo; omega
      obtain ⟨t, ht⟩ : ∃ t, tag = t + 1 := ⟨tag - 1, by omega⟩
      have hSelectT : rest[t]? = some action := by
        simpa only [ht, List.getElem?_cons_succ] using hSelect
      let entered : RAMState := {state with pc := base + 1}
      have hTailAt : At P (base + 1) (tail.compile (base + 1)) := (at_ite hAt).2.2.1
      change Sem P E (base + 1) (base + 1 + tail.len) entered _
      obtain ⟨hDecAt, hRestAt⟩ := At.seqStmt hTailAt
      change At P (base + 1) hintDispatchDec at hDecAt
      change At P (base + 1 + 1) ((hintActionSwitch rest).compile (base + 1 + 1)) at hRestAt
      have hDec := hintDispatchDec_spec E entered t (by exact hTag.trans ht) (by omega) hOne
      generalize hD : runBlock hintDispatchDec E entered = mid at hDec
      obtain ⟨hPcD, hTagD, hSameD⟩ := hDec
      have hSame : HintDispatchSame state mid := ⟨hSameD.memory, hSameD.regs⟩
      have hRunD : (step P E)^[1] entered = mid := by
        have h := iterate_runBlock_of_at P E hintDispatchDec entered hDecAt
          (by simp [hintDispatchDec, NoBranch, Instr.NoBranchI])
        rw [hD] at h
        exact h
      have hSuffix := ih t mid (base + 1 + 1) hTagD (by omega)
        ((hSame.regs 15 (by decide)).trans hOne) hSelectT hRestAt hPcD
        (fun entry st he hSame' => hAction entry st (by simpa only [ht, hintActionEntry] using he) (hSame.trans hSame'))
      obtain ⟨_, k, out, hRun, hPcOut, hCost, hPost⟩ := hSuffix
      refine ⟨rfl, k + 1, out, hintIterate_then (step P E) hRunD hRun, ?_, ?_, hQpc _ _ hPost⟩
      · change out.pc = base + 1 + (1 + (hintActionSwitch rest).len)
        omega
      · change 1 + (k + 1) + 1 ≤ budget + 3 * tag + 2
        omega
    · intro hStop
      have hZero : tag = 0 := by
        by_contra hNe
        exact hStop (by change state.regs 1 ≠ 0; rwa [hTag])
      have hFirst : first = action := by simpa [hZero] using hSelect
      subst first
      let start := base + tail.len + 2
      let entered : RAMState := {state with pc := start}
      have hRight : At P start (action.compile start) := by
        have h := (at_ite hAt).2.2.2.2.1
        simpa only [Cond.code, List.length_nil, Nat.add_zero, Nat.add_assoc,
          show 1 + (tail.len + 1) = tail.len + 2 by omega, start] using h
      simp only [Cond.code, List.length_nil, Nat.add_zero, Nat.zero_add]
      rw [show base + 1 + tail.len + 1 + action.len = start + action.len by dsimp [start]; omega]
      change Sem P E start (start + action.len) entered _
      have hEntry : start = hintActionEntry (action :: rest) base tag := by
        rw [hZero]
        change base + (1 + (hintActionSwitch rest).len) + 2 = base + (hintActionSwitch rest).len + 3
        omega
      have hNative := hAction _ entered hEntry ⟨rfl, fun _ _ => rfl⟩ (hTag.trans hZero) rfl hRight
      apply Sem.mono hNative
      intro k out hOut
      exact ⟨by omega, hQpc _ _ hOut.2⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintLocatedSwitch_sem
end -- Def_LinearSetReconciliation327_Main_HintLocatedSwitch20261120

section -- Def_LinearSetReconciliation327_Main_HintLocatedBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- The work claim for a table of actions. The descriptor is supplied in
register 6. Actions return to the control area and retain the schedule cursor. -/
def HintLocatedActions (P : Program) (E : RAMEnv) (control table switchBase : ℕ)
    (actions : List Stmt) (events : List (ℕ × ℕ)) (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) : Prop :=
  ∀ (j : Fin events.length) (action : Stmt) (base : ℕ) (s : RAMState),
    actions[events[j.val].1]? = some action →
    base = hintActionEntry actions switchBase events[j.val].1 → At P base (action.compile base) → s.pc = base →
    s.regs 6 = events[j.val].2 → s.regs 1 = 0 → HintDispatchData control table events.length j.val s →
    UpWordState E s → I j.val s.mem →
    Sem P E base (base + action.len) s (fun k out => k ≤ budget j.val ∧
      I (j.val + 1) out.mem ∧ HintDispatchData control table events.length j.val out)

theorem hintLocatedBody_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (j : Fin events.length)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events) (hTag : events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length j.val state) (hInv : I j.val state.mem)
    (hWordState : UpWordState E state)
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintLocatedActions P E control table (base + 10) actions events budget I)
    (hAt : At P base ((hintDispatchBody actions).compile base)) (hPc : state.pc = base) :
    Sem P E base (base + (hintDispatchBody actions).len) state (fun k out =>
      k ≤ budget j.val + 3 * actions.length + 21 ∧ I (j.val + 1) out.mem ∧
      HintDispatchData control table events.length (j.val + 1) out ∧ out.regs 13 = hintTruth (j.val + 1 < events.length) ∧ UpWordState E out) := by
  let switch := hintActionSwitch actions
  obtain ⟨hFetchAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintDispatchFetch at hFetchAt
  change At P (base + 10) ((Stmt.seq switch (.code hintDispatchAdvance)).compile (base + 10)) at hRestAt
  obtain ⟨hSwitchAt, hAdvanceAt⟩ := At.seqStmt hRestAt
  change At P (base + 10) (switch.compile (base + 10)) at hSwitchAt
  change At P (base + 10 + switch.len) hintDispatchAdvance at hAdvanceAt
  have hFetch := hintDispatchFetch_spec E state control table events j hWord hControl hData hTable
  generalize hF : runBlock hintDispatchFetch E state = sF at hFetch
  obtain ⟨hPcF, hTagF, hDescF, hOneF, hMemF, hDataF⟩ := hFetch
  have hRunF : (step P E)^[10] state = sF := by
    have hh := iterate_runBlock_of_at P E hintDispatchFetch state (by rwa [hPc])
      (by simp [hintDispatchFetch, NoBranch, Instr.NoBranchI])
    rw [hF] at hh
    exact hh
  have hWordF : UpWordState E sF := hRunF ▸ upIterate_word_bound P E state 10 hWordState
  let action := actions[events[j.val].1]
  have hSelect : actions[events[j.val].1]? = some action := List.getElem?_eq_getElem hTag
  have hSwitch := hintLocatedSwitch_sem actions action events[j.val].1 P E sF (base + 10) (budget j.val)
    (fun out => I (j.val + 1) out.mem ∧ HintDispatchData control table events.length j.val out)
    (by omega) hTagF (hTable.fits j).1 hOneF hSelect hSwitchAt (by omega)
    (by
      intro entry s hEntry hSame hZero hPcS hAtS
      have hWordS : UpWordState E s := by
        refine ⟨?_, by rw [hSame.memory]; exact hWordF.2⟩
        intro r
        by_cases hr : r = 1
        · subst r
          rw [hZero]
          exact Nat.two_pow_pos E.W
        · rw [hSame.regs r hr]
          exact hWordF.1 r
      exact hActions j action entry s hSelect hEntry hAtS hPcS ((hSame.regs 6 (by decide)).trans hDescF)
        hZero (hDataF.switch hSame) hWordS (by rw [hSame.memory, hMemF]; exact hInv))
    (by intro out pc hPost; exact ⟨hPost.1, hPost.2.pc pc⟩)
  obtain ⟨_, kS, mid, hRunS, hPcS, hCostS, hInvS, hDataS⟩ := hSwitch
  have hAdvance := hintDispatchAdvance_spec E mid control table events.length j.val hWord hControl hCount j.isLt hDataS
  generalize hA : runBlock hintDispatchAdvance E mid = out at hAdvance
  obtain ⟨hPcA, hMemA, hGoA, hDataA⟩ := hAdvance
  have hRunA : (step P E)^[9] mid = out := by
    have hh := iterate_runBlock_of_at P E hintDispatchAdvance mid (by rwa [hPcS])
      (by simp [hintDispatchAdvance, NoBranch, Instr.NoBranchI])
    rw [hA] at hh
    exact hh
  have hRun : (step P E)^[9 + (kS + 10)] state = out :=
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunF hRunS) hRunA
  refine ⟨hPc, 9 + (kS + 10), out, hRun,
    ?_, by omega, ?_, hDataA, hGoA, hRun ▸ upIterate_word_bound P E state _ hWordState⟩
  · rw [hPcA, hPcS, hintDispatchBody_len]
    change base + 10 + switch.len + 9 = base + (10 + (switch.len + 9))
    omega
  · rw [hMemA]
    exact hCursor _ _ _ hInvS

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintLocatedBody_sem
end -- Def_LinearSetReconciliation327_Main_HintLocatedBody20261120

section -- Def_LinearSetReconciliation327_Main_HintLocatedDispatch20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintLocatedLoop_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events) (hTags : ∀ j : Fin events.length, events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length 0 state) (hInv : I 0 state.mem)
    (hGoInitial : state.regs 13 = hintTruth (0 < events.length))
    (hWordState : UpWordState E state)
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintLocatedActions P E control table (base + 11) actions events budget I)
    (hAt : At P base ((hintDispatchLoop actions).compile base)) (hPc : state.pc = base) :
    Sem P E base (base + (hintDispatchLoop actions).len) state (fun k out =>
      k ≤ hintDispatchBudget actions events.length budget + 1 ∧ I events.length out.mem ∧
      HintDispatchData control table events.length events.length out) := by
  let count := events.length
  let J : ℕ → RAMState → Prop := fun left st =>
    ∃ j, j + left = count ∧ HintDispatchData control table count j st ∧ I j st.mem ∧
      st.regs 13 = hintTruth (j < count) ∧ UpWordState E st
  let B : ℕ → ℕ := fun left => budget (count - (left + 1)) + 3 * actions.length + 21
  have hBodyAt : At P (base + 1) ((hintDispatchBody actions).compile (base + 1)) := (at_loop hAt).2.2.1
  have hJpc : ∀ left st pc, J left st → J left {st with pc := pc} := by
    intro left st pc h
    obtain ⟨j, hLeft, hDataJ, hInvJ, hGo, hWordJ⟩ := h
    exact ⟨j, hLeft, hDataJ.pc pc, hInvJ, hGo, hWordJ⟩
  have hTest : ∀ left st, J left st → J left (runBlock (Cond.neqz 13).code E st) := fun _ _ h => h
  have hGo : ∀ left st, J (left + 1) st → (Cond.neqz 13).eval st := by
    intro left st h
    obtain ⟨j, hLeft, _, _, hFlag, _⟩ := h
    have hj : j < count := by omega
    change st.regs 13 ≠ 0
    rw [hFlag]
    simp [hintTruth, hj]
  have hStop : ∀ st, J 0 st → ¬ (Cond.neqz 13).eval st := by
    intro st h
    obtain ⟨j, hLeft, _, _, hFlag, _⟩ := h
    have hj : ¬ j < count := by omega
    change ¬ st.regs 13 ≠ 0
    rw [hFlag]
    simp [hintTruth, hj]
  have hBody : ∀ left st, J (left + 1) st → st.pc = base + (Cond.neqz 13).code.length + 1 →
      Sem P E (base + (Cond.neqz 13).code.length + 1)
        (base + (Cond.neqz 13).code.length + 1 + (hintDispatchBody actions).len) st
        (fun k out => k ≤ B left ∧ J left out) := by
    intro left st h hStart
    obtain ⟨j, hLeft, hDataJ, hInvJ, _, hWordJ⟩ := h
    have hJlt : j < events.length := by
      change j < count
      omega
    let pos : Fin events.length := ⟨j, hJlt⟩
    have hNative := hintLocatedBody_sem P E st control table (base + 1) actions events budget I pos
      hWord hControl hCount hTable (hTags pos) hDataJ hInvJ hWordJ hCursor hActions hBodyAt hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hInvOut, hDataOut, hFlag, hWordOut⟩ := hOut
    have hPos : count - (left + 1) = j := by omega
    refine ⟨?_, j + 1, by omega, hDataOut, hInvOut, hFlag, hWordOut⟩
    dsimp only [B]
    rw [hPos]
    exact hCost
  have hInitial : J count state := ⟨0, Nat.zero_add _, hData, hInv, hGoInitial, hWordState⟩
  have hNative := hintLoopBudget_sem P E base (.neqz 13) (hintDispatchBody actions) hAt (by omega)
    J B hJpc hTest hGo hStop hBody count state hInitial hPc
  have hEnd : base + (hintDispatchLoop actions).len = base + (Cond.neqz 13).code.length +
      (hintDispatchBody actions).len + 2 := by simp [hintDispatchLoop, Stmt.len, Nat.add_assoc]
  rw [hEnd]
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hLeft, hDataOut, hInvOut, _, _⟩ := hOut
  have hEq : j = events.length := by simpa [count] using hLeft
  subst j
  refine ⟨?_, hInvOut, hDataOut⟩
  simp only [Cond.code, List.length_nil, Nat.zero_add, B] at hCost
  unfold hintDispatchBudget
  simpa only [count, Nat.add_assoc] using hCost

theorem hintLocatedDispatch_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base old : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events) (hTags : ∀ j : Fin events.length, events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length old state) (hInv : I 0 state.mem)
    (hWordState : UpWordState E state)
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintLocatedActions P E control table (base + 19) actions events budget I)
    (hAt : At P base ((hintDispatchStmt actions).compile base)) (hPc : state.pc = base) :
    Sem P E base (base + (hintDispatchStmt actions).len) state (fun k out =>
      k ≤ hintDispatchBudget actions events.length budget + 9 ∧ I events.length out.mem ∧
      HintDispatchData control table events.length events.length out) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintDispatchInit at hInitAt
  change At P (base + 8) ((hintDispatchLoop actions).compile (base + 8)) at hLoopAt
  have hInit := hintDispatchInit_spec E state control table events.length old hWord hControl hCount hData
  generalize hI : runBlock hintDispatchInit E state = mid at hInit
  obtain ⟨hPcI, hMemI, hGoI, hDataI⟩ := hInit
  have hRunI : (step P E)^[8] state = mid := by
    have hh := iterate_runBlock_of_at P E hintDispatchInit state (by rwa [hPc])
      (by simp [hintDispatchInit, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  have hWordI : UpWordState E mid := hRunI ▸ upIterate_word_bound P E state 8 hWordState
  have hInvI : I 0 mid.mem := by rw [hMemI]; exact hCursor _ _ _ hInv
  obtain ⟨_, k, out, hRun, hEnd, hCost, hInvOut, hDataOut⟩ :=
    hintLocatedLoop_sem P E mid control table (base + 8) actions events budget I hWord hControl hCount
      hTable hTags hDataI hInvI hGoI hWordI hCursor hActions hLoopAt (by omega)
  refine ⟨hPc, k + 8, out, hintIterate_then (step P E) hRunI hRun, ?_, by omega, hInvOut, hDataOut⟩
  change out.pc = base + (8 + (hintDispatchLoop actions).len)
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintLocatedDispatch_sem
end -- Def_LinearSetReconciliation327_Main_HintLocatedDispatch20261120

section -- Def_LinearSetReconciliation327_Main_HintPlaceCR20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintCRAction (S : CRSourceBundle) (entry : ℕ) (finish : Stmt) : Stmt :=
  .seq (.code (crSourceInputCode S entry)) finish

def hintActionsWithCR (S : CRSourceBundle) (switchBase : ℕ)
    (actions : List Stmt) (finish : Stmt) : List Stmt :=
  actions ++ [hintCRAction S (switchBase + 2 * actions.length + 3) finish]

theorem hintLastActionEntry (actions : List Stmt) (last : Stmt) (switchBase : ℕ) :
    hintActionEntry (actions ++ [last]) switchBase actions.length = switchBase + 2 * actions.length + 3 := by
  induction actions generalizing switchBase with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.cons_append, List.length_cons, hintActionEntry]
    rw [ih]
    omega

theorem hintLastAction_select (actions : List Stmt) (last : Stmt) :
    (actions ++ [last])[actions.length]? = some last := by
  induction actions with
  | nil => rfl
  | cons first rest ih => exact ih

theorem hintCRAction_parts (S : CRSourceBundle) (P : Program)
    (switchBase : ℕ) (actions : List Stmt) (finish act : Stmt) (entry : ℕ)
    (hSelect : (hintActionsWithCR S switchBase actions finish)[actions.length]? = some act)
    (hEntry : entry = hintActionEntry (hintActionsWithCR S switchBase actions finish) switchBase actions.length)
    (hAt : At P entry (act.compile entry)) :
    act.len = (crSourceInputCode S entry).length + finish.len ∧
    At P entry (crSourceInputCode S entry) ∧
    At P (entry + (crSourceInputCode S entry).length)
      (finish.compile (entry + (crSourceInputCode S entry).length)) := by
  have hAddress : entry = switchBase + 2 * actions.length + 3 := hEntry.trans (hintLastActionEntry _ _ _)
  have hAct : act = hintCRAction S entry finish := by
    rw [hintActionsWithCR, hintLastAction_select, ← hAddress] at hSelect
    exact (Option.some.inj hSelect).symm
  subst act
  exact ⟨rfl, At.seqStmt hAt⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCRAction_parts
end -- Def_LinearSetReconciliation327_Main_HintPlaceCR20261120


