-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_05
-- name    : LinearSetReconciliation327_Main_B65_05
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-25T16:19:21.046281+00:00
-- url     : https://prove2.me/theorems/686a7b96-aaca-5502-aa30-fdce910032c1
-- title:
--   Theorem 6.5 supporting machine proof B65_05
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_05RowOuter

set_option autoImplicit false

section S_HintRowFirst20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintFirstIndex (pred : ℕ → Prop) (maxR : ℕ) : ℕ := by
  classical
  let S := (Finset.range (maxR + 1)).filter pred
  exact if h : S.Nonempty then S.min' h else maxR + 1

theorem hintFirstIndex_spec (pred : ℕ → Prop) (maxR : ℕ) :
    let target := hintFirstIndex pred maxR
    target ≤ maxR + 1 ∧ (∀ r < target, ¬ pred r) ∧ (target ≤ maxR → pred target) := by
  classical
  let S := (Finset.range (maxR + 1)).filter pred
  have hEq : hintFirstIndex pred maxR = if h : S.Nonempty then S.min' h else maxR + 1 := rfl
  dsimp only
  rw [hEq]
  split_ifs with hS
  · have hMem : S.min' hS ∈ S := Finset.min'_mem S hS
    have hBound : S.min' hS < maxR + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hMem).1
    refine ⟨by omega, ?_, fun _ => (Finset.mem_filter.mp hMem).2⟩
    intro r hr hp
    have hRMem : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
    have hLe := Finset.min'_le S r hRMem
    omega
  · refine ⟨le_rfl, ?_, ?_⟩
    · intro r hr hp
      exact hS ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hp⟩⟩
    · intro hBad; omega


theorem hintFirstIndex_exists (pred : ℕ → Prop) (maxR : ℕ) :
    hintFirstIndex pred maxR ≤ maxR ↔ ∃ r ≤ maxR, pred r := by
  have hSpec := hintFirstIndex_spec pred maxR
  constructor
  · intro hLe
    exact ⟨_, hLe, hSpec.2.2 hLe⟩
  · rintro ⟨r, hr, hp⟩
    by_contra hBad
    exact hSpec.2.1 r (by omega) hp

open Classical in
theorem hintFind_range (pred : ℕ → Prop) : ∀ (n target : ℕ),
    (∀ r < target, ¬ pred r) → (target < n → pred target) →
    (List.range n).find? (fun r => decide (pred r)) = if target < n then some target else none := by
  classical
  intro n
  induction n with
  | zero => intro target _ _; simp
  | succ n ih =>
    intro target hBefore hAt
    by_cases hLt : target < n
    · have hIH := ih target hBefore (fun ht => hAt (by omega))
      rw [List.range_succ, List.find?_append, hIH, if_pos hLt, if_pos (by omega : target < n + 1)]
      rfl
    · have hNone : (List.range n).find? (fun r => decide (pred r)) = none := by
        apply List.find?_eq_none.mpr
        intro r hr
        have hNo := hBefore r (by have := List.mem_range.mp hr; omega)
        simpa using hNo
      rw [List.range_succ, List.find?_append, hNone]
      by_cases hEq : target = n
      · subst target
        have hp : pred n := hAt (by omega)
        simp [hp]
      · have hNot : ¬ target < n + 1 := by omega
        have hNo : ¬ pred n := hBefore n (by omega)
        simp [hNot, hNo]

open Classical in
theorem hintFirstIndex_find (pred : ℕ → Prop) (maxR : ℕ) :
    (List.range (maxR + 1)).find? (fun r => decide (pred r)) =
      if hintFirstIndex pred maxR ≤ maxR then some (hintFirstIndex pred maxR) else none := by
  classical
  have hSpec := hintFirstIndex_spec pred maxR
  simpa only [Nat.lt_succ_iff] using hintFind_range pred (maxR + 1) (hintFirstIndex pred maxR)
    hSpec.2.1 (fun ht => hSpec.2.2 (by omega))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFirstIndex_find
end S_HintRowFirst20261120
section S_HintRowSearch20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRowSearchStmt : Stmt := .seq (.code hintRowOuterInitCode) hintRowOuterLoop
theorem hintRowSearchStmt_len : hintRowSearchStmt.len = 1466 := rfl

/-- Native first-eligible-singleton search. The actual count and loop flags are
    initialized by the program; the first-success index is only a proof device. -/
theorem hintRowSearchStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hNext : G.rows < G.steps)
    (Nj parent outsideBase bitmapBase maxR table c oldCount : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hNext.le Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hLimit : state.mem (parent + 4) = maxR) (hTableMem : state.mem (parent + 5) = table)
    (hTable : table + maxR < 2 ^ E.W)
    (hLookup : ∀ r ≤ maxR, E.det (table + r) = min G.steps (HintParams.sigma G.hints Nj r + c))
    (hCoeff : ∀ q : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + q.val) = (beta ⟨G.rows, hNext⟩ q).val)
    (hAt : At P base (hintRowSearchStmt.compile base)) (hPc : state.pc = base) :
    let target := hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR
    Sem P E base (base + 1466) state (fun k out =>
      k ≤ (hintRowOuterBudget G Nj maxR + 2) * min (target + 1) (maxR + 1) + 8 ∧
      HintRowOuterDone G coords beta hNext Nj parent outsideBase bitmapBase maxR table target v state.mem out) := by
  let target := hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR
  have hFirst := hintFirstIndex_spec (hintRowQualified G coords beta Nj c v) maxR
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hSpan := hPublic.fits.span
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintRowOuterInitCode at hInitAt
  change At P (base + 7) (hintRowOuterLoop.compile (base + 7)) at hLoopAt
  have hInit := hintRowOuterInitCode_spec E state parent outsideBase (by omega)
    (hContext.trans hParent.symm) (by omega) hInput.outside_pointer
  generalize hI : runBlock hintRowOuterInitCode E state = sI at hInit
  obtain ⟨hPcI, hMemI, hGoI, _, hCtxI⟩ := hInit
  have hRunI : (step P E)^[7] state = sI := by
    have hh := iterate_runBlock_of_at P E hintRowOuterInitCode state (by rwa [hPc])
      (by simp [hintRowOuterInitCode, hintScanParent, hintRowOuterInitTail, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  have hInputI : HintRowInput G coords Nj 0 parent outsideBase bitmapBase v sI.mem := by
    rw [hMemI]
    exact HintRowInput.set_count hPublic hInput 0
  have hHeaderI : ∃ index, HintGaussHeader G index sI.mem := by
    obtain ⟨index, hHeader⟩ := hHeader
    refine ⟨index, ?_⟩
    intro i hi
    rw [hMemI, Function.update_of_ne (by omega : G.context + i ≠ outsideBase)]
    exact hHeader i hi
  have hFrameI : HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR state.mem sI.mem := by
    rw [hMemI]
    exact HintRowControllerFrame.set_count G parent outsideBase bitmapBase Nj maxR state.mem 0
  have hControlI : HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table 0 v state.mem sI :=
    ⟨hInputI, hHeaderI, hCtxI.trans hParent,
      (hFrameI.parent hPublic 4 (by decide) (by decide)).trans hLimit,
      (hFrameI.parent hPublic 5 (by decide) (by decide)).trans hTableMem, hFrameI⟩
  obtain ⟨_, kL, out, hRunL, hPcL, hCostL, hDone⟩ :=
    hintRowOuterLoop_sem G coords beta hNext Nj parent outsideBase bitmapBase maxR table c target v state.mem
      P E sI (base + 7) hPublic hFirst.1 hFirst.2.1 hFirst.2.2 hControlI hGoI hTable hLookup hCoeff hLoopAt (by omega)
  exact ⟨hPc, kL + 7, out, hintIterate_then (step P E) hRunI hRunL, by omega, by dsimp only [target] at hCostL; omega, hDone⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowSearchStmt_sem
end S_HintRowSearch20261120
section S_HintRowPredictAlign20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

def hintRowOutput (state : RAMState) : Option (ZMod 2) :=
  if state.regs 1 = 1 then some (state.regs 8 : ZMod 2) else none

theorem hintCoords_card {h K : ℕ} (coords : Fin h → Fin K) (hInj : Function.Injective coords) :
    (Finset.univ.image (fun j => (coords j).val)).card = h := by
  rw [Finset.card_image_of_injective _ (fun _ _ heq => hInj (Fin.ext heq)), Finset.card_univ, Fintype.card_fin]

theorem hintRowSearch_workerPredict (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hNext : G.rows < G.steps) (N m Nj parent outsideBase bitmapBase maxR table BX BY c : ℕ)
    (j : Fin m) (v : HintVec G.rows) (original : ℕ → ℕ) (state : RAMState)
    (hNj : rowLen N m j.val = Nj) (hBX : G.hints ≤ BX) (hMax : maxR = min BY (Nj - G.hints))
    (hDone : HintRowOuterDone G coords beta hNext Nj parent outsideBase bitmapBase maxR table
      (hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR) v original state) :
    hintRowOutput state = workerPredict N m G.steps G.buckets BX BY c j beta
      (Finset.univ.image (fun t => (coords t).val)) (List.ofFn v) := by
  classical
  have hCard := hintCoords_card coords hInj
  have hFind := hintFirstIndex_find (hintRowQualified G coords beta Nj c v) maxR
  unfold workerPredict
  dsimp only
  rw [hCard, if_neg (by omega : ¬ BX < G.hints), hNj, ← hMax]
  simp only [List.length_ofFn]
  simp only [dif_pos hNext]
  have hPredEq : (fun r => decide (sigma G.hints Nj r + c ≤ G.rows ∧
      (family Nj beta (Finset.univ.image (fun t => (coords t).val)) r (List.ofFn v)).card = 1)) =
      (fun r => decide (hintRowQualified G coords beta Nj c v r)) := by
    funext r
    by_cases hp : sigma G.hints Nj r + c ≤ G.rows ∧
        (family Nj beta (Finset.univ.image (fun t => (coords t).val)) r (List.ofFn v)).card = 1 <;>
      simp only [hintRowQualified, hp, decide_true, decide_false]
  rw [hPredEq]
  rw [hFind]
  rcases hDone.answer with ⟨hWithin, hOne, C, hMember, hUnique, hBit⟩ | ⟨hEnd, hZero⟩
  · have hFam : family Nj beta (Finset.univ.image (fun t => (coords t).val))
        (hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR) (List.ofFn v) = {C} := by
      ext D
      simp only [Finset.mem_singleton]
      exact ⟨fun hD => hUnique D hD, fun heq => heq ▸ hMember⟩
    simp only [if_pos hWithin]
    change hintRowOutput state = Option.map (fun C => rowBit beta C ⟨G.rows, hNext⟩)
      (family Nj beta (Finset.univ.image (fun t => (coords t).val))
        (hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR) (List.ofFn v)).toList.head?
    rw [hFam]
    simp [hintRowOutput, hOne, hBit]
  · have hOutside : ¬ hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR ≤ maxR := by omega
    rw [if_neg hOutside]
    simp [hintRowOutput, hZero]

theorem hintWorkerPredict_abstain {N m ell K BX BY c : ℕ} (j : Fin m)
    (beta : Fin ell → Fin K → ZMod 2) (J : Finset ℕ) (v : List (ZMod 2))
    (hBad : BX < J.card ∨ ¬ v.length < ell) : workerPredict N m ell K BX BY c j beta J v = none := by
  classical
  unfold workerPredict
  dsimp only
  by_cases hBX : BX < J.card
  · rw [if_pos hBX]
  · rw [if_neg hBX]
    have hLength : ¬ v.length < ell := hBad.resolve_left hBX
    split <;> simp [hLength]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowSearch_workerPredict
end S_HintRowPredictAlign20261120
section S_HintRowPredict20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

def hintRowPredictStmt : Stmt := .seq (.code hintRowGuardCode)
  (.ite (.neqz 1) hintRowSearchStmt (.code hintReplayStop))
theorem hintRowPredictStmt_len : hintRowPredictStmt.len = 1489 := rfl

/-- Full native row prediction, with both abstention guards, the waiting test,
    exhaustive family recovery, first eligible singleton, and actual next bit. -/
theorem hintRowPredictStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (N m Nj parent outsideBase bitmapBase maxR table BX BY c oldCount : ℕ) (j : Fin m) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hNj : rowLen N m j.val = Nj) (hMax : maxR = min BY (Nj - G.hints))
    (hBX : BX < 2 ^ E.W) (hReadBX : state.mem (parent + 6) = BX)
    (hLimit : state.mem (parent + 4) = maxR) (hTableMem : state.mem (parent + 5) = table)
    (hTable : table + maxR < 2 ^ E.W)
    (hLookup : ∀ r ≤ maxR, E.det (table + r) = min G.steps (sigma G.hints Nj r + c))
    (hCoeff : ∀ hNext : G.rows < G.steps, ∀ q : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + q.val) = (beta ⟨G.rows, hNext⟩ q).val)
    (hAt : At P base (hintRowPredictStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1489) state (fun k out =>
      k ≤ (hintRowOuterBudget G Nj maxR + 2) * (maxR + 1) + 29 ∧
      hintRowOutput out = workerPredict N m G.steps G.buckets BX BY c j beta
        (Finset.univ.image (fun t => (coords t).val)) (List.ofFn v) ∧
      (∃ count, HintRowInput G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR state.mem out.mem) := by
  classical
  have hJCard := hintCoords_card coords hPublic.injective
  obtain ⟨hGuardAt, hBranchAt⟩ := At.seqStmt hAt
  change At P base hintRowGuardCode at hGuardAt
  change At P (base + 19) ((Stmt.ite (.neqz 1) hintRowSearchStmt (.code hintReplayStop)).compile (base + 19)) at hBranchAt
  obtain ⟨index, hHead⟩ := hHeader
  have hGuard := hintRowGuardCode_spec E G state parent BX index hPublic.parent_eq hContext hHead hPublic.fits hBX hReadBX
  generalize hG : runBlock hintRowGuardCode E state = sG at hGuard
  obtain ⟨hPcG, hMemG, hFlagG, hCtxG⟩ := hGuard
  have hRunG : (step P E)^[19] state = sG := by
    have hh := iterate_runBlock_of_at P E hintRowGuardCode state (by rwa [hPc])
      (by simp [hintRowGuardCode, hintScanParent, hintRowGuardFetch, hintParentLoad, hintRowGuardTail, NoBranch, Instr.NoBranchI])
    simpa only [hintRowGuardCode_length, hG] using hh
  have hInputG : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v sG.mem := by rw [hMemG]; exact hInput
  have hHeaderG : ∃ index, HintGaussHeader G index sG.mem := by rw [hMemG]; exact ⟨index, hHead⟩
  let Q : ℕ → RAMState → Prop := fun k out =>
    k ≤ (hintRowOuterBudget G Nj maxR + 2) * (maxR + 1) + 10 ∧
    hintRowOutput out = workerPredict N m G.steps G.buckets BX BY c j beta
      (Finset.univ.image (fun t => (coords t).val)) (List.ofFn v) ∧
    (∃ count, HintRowInput G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
    (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
    HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR sG.mem out.mem
  have hBranch : Sem P E (base + 19) (base + 1489) sG Q := by
    apply Sem.ite P E (base + 19) (.neqz 1) hintRowSearchStmt (.code hintReplayStop) sG Q
      hBranchAt hPublic.geometry.word_bound (by omega)
    · intro hGo
      change Sem P E (base + 20) (base + 1486) {sG with pc := base + 20}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1489})
      have hValid : G.hints ≤ BX ∧ G.rows < G.steps := by
        by_contra hBad
        have hZero : sG.regs 1 = 0 := by simpa [hintTruth, hBad] using hFlagG
        exact hGo hZero
      have hNative := hintRowSearchStmt_sem G coords beta hValid.2 Nj parent outsideBase bitmapBase maxR table c oldCount v
        P E {sG with pc := base + 20} (base + 20) hPublic hInputG hHeaderG hCtxG
        (by rw [hMemG]; exact hLimit) (by rw [hMemG]; exact hTableMem) hTable hLookup (hCoeff hValid.2)
        (at_ite hBranchAt).2.2.1 rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hDone⟩ := hOut
      have hRoundBound := Nat.mul_le_mul_left (hintRowOuterBudget G Nj maxR + 2)
        (min_le_right (hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR + 1) (maxR + 1))
      have hCorrect := hintRowSearch_workerPredict G coords hPublic.injective beta hValid.2 N m Nj parent outsideBase bitmapBase
        maxR table BX BY c j v sG.mem out hNj hValid.1 hMax hDone
      exact ⟨by omega, hCorrect, ⟨_, hDone.control.input⟩, hDone.control.header,
        hDone.control.context_value, hDone.control.frame⟩
    · intro hStop
      change Sem P E (base + 1487) (base + 1488) {sG with pc := base + 1487}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1489})
      have hBad : ¬ (G.hints ≤ BX ∧ G.rows < G.steps) := by
        intro hGood
        have hOne : sG.regs 1 = 1 := by simpa [hintTruth, hGood] using hFlagG
        apply hStop
        change sG.regs 1 ≠ 0
        rw [hOne]; decide
      have hAbstain := hintWorkerPredict_abstain (N := N) (BX := BX) (BY := BY) (c := c) j beta (Finset.univ.image (fun t => (coords t).val)) (List.ofFn v)
        (by rw [hJCard, List.length_ofFn]; omega : BX < (Finset.univ.image (fun t => (coords t).val)).card ∨
          ¬ (List.ofFn v).length < G.steps)
      have hNative := Sem.block P E (base + 1487) hintReplayStop {sG with pc := base + 1487}
        (at_ite hBranchAt).2.2.2.2.1 (by simp [hintReplayStop, NoBranch, Instr.NoBranchI]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, rfl⟩ := hOut
      dsimp only [Q]
      refine ⟨by change k = 1 at hCost; omega, ?_, ⟨oldCount, hInputG⟩, hHeaderG, ?_, ?_⟩
      · rw [hAbstain]
        simp [hintRowOutput, hintReplayStop, runBlock, execInstr]
      · simpa [hintReplayStop, runBlock, execInstr] using hCtxG
      · exact HintRowControllerFrame.refl G parent outsideBase bitmapBase Nj maxR sG.mem
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hCorrectB, hInputB, hHeaderB, hCtxB, hFrameB⟩ := hBranch
  refine ⟨hPc, kB + 19, out, hintIterate_then (step P E) hRunG hRunB, hPcB, by omega,
    hCorrectB, hInputB, hHeaderB, hCtxB, ?_⟩
  rw [← hMemG]; exact hFrameB

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowPredictStmt_sem
end S_HintRowPredict20261120
section S_HintFinalClassExists20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

/-- Once the shared hint matrix is injective, every nonempty original family
    contains a successful enumerated outside class, for every outside count. -/
theorem hintFamilySuccesses_nonempty (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (Nj r : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (hMatrix : Function.Injective (hintGaussMap G coords beta hPrefix)) :
    (hintFamilySuccesses G coords beta Nj r v hPos).Nonempty ↔
      (family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)).Nonempty := by
  classical
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨C, hClass, _⟩ := (Finset.mem_filter.mp hn).2.2
    exact ⟨C, hClass.1⟩
  · rintro ⟨C, hC⟩
    let J := Finset.univ.image (fun j => (coords j).val)
    let A := C \ J
    have hClass : hintFamilyClass G coords beta Nj r A v C := ⟨hC, rfl⟩
    have hUnique : ∃! D : Finset ℕ, hintFamilyClass G coords beta Nj r A v D :=
      ⟨C, hClass, fun D hD => hintFamilyClass_subsingleton G coords hInj beta hPrefix Nj r A v hMatrix D C hD hClass⟩
    have hDomain := hintFamilyClass_domain G coords beta hPrefix Nj r A v hUnique
    let t : HintOutsideTuple Nj J r := (hintOutsideTupleCodec Nj J r).symm ⟨A, hDomain⟩
    have hSet : hintTupleSet t.val = A := by
      have hh := congrArg (fun B : HintOutsideSet Nj J r => B.val)
        ((hintOutsideTupleCodec Nj J r).apply_symm_apply ⟨A, hDomain⟩)
      exact hh
    let e := hintOdometerEnumeration Nj r hPos
    let n := e.symm t.val
    have hEnum : e n = t.val := e.apply_symm_apply _
    refine ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change (StrictMono (fun i => (e n i).val) ∧ ∀ i, (e n i).val ∉ J) ∧
      ∃! D : Finset ℕ, hintFamilyClass G coords beta Nj r (hintTupleSet (e n)) v D
    rw [hEnum]
    exact ⟨t.property, by rw [hSet]; exact hUnique⟩

theorem hintFamilySuccesses_empty (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj r : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (hEmpty : family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v) = ∅) :
    hintFamilySuccesses G coords beta Nj r v hPos = ∅ := by
  classical
  apply Finset.ext
  intro n
  constructor
  · intro hn
    obtain ⟨C, hClass, _⟩ := (Finset.mem_filter.mp hn).2.2
    have hMem := hClass.1
    rw [hEmpty] at hMem
    exact False.elim (Finset.notMem_empty C hMem)
  · intro hn
    exact False.elim (Finset.notMem_empty n hn)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFamilySuccesses_nonempty
end S_HintFinalClassExists20261120
section S_HintFinalRaw20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

theorem hintNatSum_one {ι : Type*} (S : Finset ι) (f : ι → ℕ) :
    (∑ r ∈ S, f r) = 1 ↔ ∃ r ∈ S, f r = 1 ∧ ∀ q ∈ S, q ≠ r → f q = 0 := by
  classical
  constructor
  · intro hSum
    have hEx : ∃ r ∈ S, f r ≠ 0 := by
      by_contra hNo
      have hAll : ∀ r ∈ S, f r = 0 := by
        intro r hr
        by_contra hNe
        exact hNo ⟨r, hr, hNe⟩
      have hZero : (∑ r ∈ S, f r) = 0 := Finset.sum_eq_zero hAll
      omega
    obtain ⟨r, hr, hNe⟩ := hEx
    have hLe : f r ≤ ∑ q ∈ S, f q := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hr
    have hOne : f r = 1 := by omega
    have hErase := Finset.sum_erase_add S f hr
    have hEraseZero : (∑ q ∈ S.erase r, f q) = 0 := by omega
    refine ⟨r, hr, hOne, ?_⟩
    intro q hq hqr
    have hqLe : f q ≤ ∑ x ∈ S.erase r, f x :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hqr, hq⟩)
    omega
  · rintro ⟨r, hr, hOne, hOthers⟩
    calc
      (∑ q ∈ S, f q) = f r := Finset.sum_eq_single r (fun q hq hqr => hOthers q hq hqr)
        (fun hNot => False.elim (hNot hr))
      _ = 1 := hOne

noncomputable def hintFinalUnion (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj maxR : ℕ) (v : HintVec G.rows) : Finset (Finset ℕ) := by
  classical
  exact (Finset.range (maxR + 1)).biUnion (fun r => family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v))

noncomputable def hintFinalRawCount (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj maxR : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) : ℕ :=
  ∑ r ∈ Finset.range (maxR + 1), (hintFamilySuccesses G coords beta Nj r v hPos).card

theorem hintFamily_count_eq (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r s : ℕ) (v : HintVec G.rows) (C : Finset ℕ)
    (hR : C ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v))
    (hS : C ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) s (List.ofFn v)) : r = s := by
  have hRCard := ((hintFamily_mem hPrefix Nj beta _ C r v).mp hR).2.1
  have hSCard := ((hintFamily_mem hPrefix Nj beta _ C s v).mp hS).2.1
  exact hRCard.symm.trans hSCard

/-- The raw number of successful outside classes, summed over all outside
    counts, detects the singleton union used by the original final worker. -/
theorem hintFinalRawCount_one (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (Nj maxR : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (hHintValid : ∀ j, (coords j).val < Nj) :
    hintFinalRawCount G coords beta Nj maxR v hPos = 1 ↔ (hintFinalUnion G coords beta Nj maxR v).card = 1 := by
  classical
  let Fam := fun r => family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)
  let S := fun r => hintFamilySuccesses G coords beta Nj r v hPos
  let U := hintFinalUnion G coords beta Nj maxR v
  constructor
  · intro hCount
    obtain ⟨r, hr, hOne, hOthers⟩ := (hintNatSum_one (Finset.range (maxR + 1)) (fun r => (S r).card)).mp hCount
    have hFamOne : (Fam r).card = 1 :=
      (hintFamilySuccesses_card_one G coords hInj beta hPrefix Nj r v hPos hHintValid).mp hOne
    obtain ⟨C, hFamEq⟩ := Finset.card_eq_one.mp hFamOne
    have hC : C ∈ Fam r := by rw [hFamEq]; simp
    have hCU : C ∈ U := Finset.mem_biUnion.mpr ⟨r, hr, hC⟩
    obtain ⟨n, hSEq⟩ := Finset.card_eq_one.mp hOne
    have hn : n ∈ S r := by rw [hSEq]; simp
    have hUniqueClass := (Finset.mem_filter.mp hn).2.2
    have hMatrix := hintFamilyClass_unique_injective G coords hInj beta hPrefix Nj r
      (hintTupleSet (hintOdometerEnumeration Nj r hPos n)) v hHintValid hUniqueClass
    have hUnique : ∀ D ∈ U, D = C := by
      intro D hDU
      obtain ⟨s, hs, hD⟩ := Finset.mem_biUnion.mp hDU
      by_cases hEq : s = r
      · subst s
        change D ∈ Fam r at hD
        simpa only [hFamEq, Finset.mem_singleton] using hD
      · have hZero : (S s).card = 0 := hOthers s hs hEq
        have hNonempty : (S s).Nonempty :=
          (hintFamilySuccesses_nonempty G coords hInj beta hPrefix Nj s v hPos hMatrix).mpr ⟨D, hD⟩
        have hPositive := Finset.card_pos.mpr hNonempty
        omega
    apply Finset.card_eq_one.mpr
    refine ⟨C, ?_⟩
    apply Finset.ext
    intro D
    simp only [Finset.mem_singleton]
    exact ⟨fun hD => hUnique D hD, fun hEq => hEq ▸ hCU⟩
  · intro hUnion
    change U.card = 1 at hUnion
    obtain ⟨C, hUEq⟩ := Finset.card_eq_one.mp hUnion
    have hCU : C ∈ U := by rw [hUEq]; simp
    obtain ⟨r, hr, hC⟩ := Finset.mem_biUnion.mp hCU
    have hFamEq : Fam r = {C} := by
      apply Finset.ext
      intro D
      simp only [Finset.mem_singleton]
      constructor
      · intro hD
        have hDU : D ∈ U := Finset.mem_biUnion.mpr ⟨r, hr, hD⟩
        simpa only [hUEq, Finset.mem_singleton] using hDU
      · intro hEq; exact hEq ▸ hC
    have hFamOne : (Fam r).card = 1 := by rw [hFamEq]; simp
    have hSOne : (S r).card = 1 :=
      (hintFamilySuccesses_card_one G coords hInj beta hPrefix Nj r v hPos hHintValid).mpr hFamOne
    apply (hintNatSum_one (Finset.range (maxR + 1)) (fun r => (S r).card)).mpr
    refine ⟨r, hr, hSOne, ?_⟩
    intro s hs hNe
    have hFamEmpty : Fam s = ∅ := by
      apply Finset.ext
      intro D
      constructor
      · intro hD
        have hDU : D ∈ U := Finset.mem_biUnion.mpr ⟨s, hs, hD⟩
        have hDC : D = C := by simpa only [hUEq, Finset.mem_singleton] using hDU
        subst D
        have hEq := hintFamily_count_eq G coords beta hPrefix Nj r s v C hC hD
        exact False.elim (hNe hEq.symm)
      · intro hFalse; exact False.elim (Finset.notMem_empty D hFalse)
    have hSEmpty : S s = ∅ := hintFamilySuccesses_empty G coords beta Nj s v hPos hFamEmpty
    rw [hSEmpty]
    rfl

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalRawCount_one
end S_HintFinalRaw20261120
section S_HintFinalCap20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintCap2_add_capped (a b : ℕ) : min 2 (min 2 a + min 2 b) = min 2 (a + b) := by omega

noncomputable def hintFinalRawPrefix (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj j : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) : ℕ :=
  ∑ r ∈ Finset.range j, (hintFamilySuccesses G coords beta Nj r v hPos).card

theorem hintFinalRawPrefix_zero (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) :
    hintFinalRawPrefix G coords beta Nj 0 v hPos = 0 := by simp [hintFinalRawPrefix]

theorem hintFinalRawPrefix_succ (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj j : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) :
    hintFinalRawPrefix G coords beta Nj (j + 1) v hPos =
      hintFinalRawPrefix G coords beta Nj j v hPos + (hintFamilySuccesses G coords beta Nj j v hPos).card := by
  exact Finset.sum_range_succ _ _

theorem hintFinalRawPrefix_full (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj maxR : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) :
    hintFinalRawPrefix G coords beta Nj (maxR + 1) v hPos = hintFinalRawCount G coords beta Nj maxR v hPos := rfl

def hintCapAddCode : List Instr :=
  [.add 0 0 8, .imm 9 2, .lt 1 9 0, .mul 8 1 9, .imm 15 1,
    .bxor 1 1 15, .mul 0 0 1, .add 0 0 8, .store 4 0]

theorem hintCapAddCode_spec (E : RAMEnv) (state : RAMState) (dest globalCap localCap : ℕ)
    (hWord : 4 < 2 ^ E.W) (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (h4 : state.regs 4 = dest) (h0 : state.regs 0 = globalCap) (h8 : state.regs 8 = localCap) :
    let out := runBlock hintCapAddCode E state
    out.pc = state.pc + 9 ∧ out.mem = Function.update state.mem dest (min 2 (globalCap + localCap)) ∧
      out.regs 0 = min 2 (globalCap + localCap) ∧ out.regs 14 = state.regs 14 := by
  have hSum : globalCap + localCap < 2 ^ E.W := by omega
  have hOne : 1 < 2 ^ E.W := by omega
  have hTwo : 2 < 2 ^ E.W := by omega
  by_cases hLe : globalCap + localCap ≤ 2
  · have hNot : ¬ 2 < globalCap + localCap := by omega
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [hintCapAddCode, runBlock, execInstr, h4, h0, h8, hNot, min_eq_right hLe,
        Nat.mod_eq_of_lt hSum, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hTwo]
  · have hGt : 2 < globalCap + localCap := by omega
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [hintCapAddCode, runBlock, execInstr, h4, h0, h8, hGt, min_eq_left (by omega : 2 ≤ globalCap + localCap),
        Nat.mod_eq_of_lt hSum, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hTwo]

def hintFinalCapFetch : List Instr :=
  [.imm 4 7, .add 4 11 4, .load 0 4, .imm 3 3, .add 3 11 3, .load 8 3]
def hintFinalCapCode : List Instr := hintScanParent ++ hintFinalCapFetch ++ hintCapAddCode

theorem hintFinalCapFetch_spec (E : RAMEnv) (state : RAMState) (parent globalCap localCap : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hParent : state.regs 11 = parent)
    (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (hReadGlobal : state.mem (parent + 7) = globalCap) (hReadLocal : state.mem (parent + 3) = localCap) :
    let out := runBlock hintFinalCapFetch E state
    out.pc = state.pc + 6 ∧ out.mem = state.mem ∧ out.regs 4 = parent + 7 ∧ out.regs 0 = globalCap ∧
      out.regs 8 = localCap ∧ out.regs 14 = state.regs 14 := by
  have h7 : 7 < 2 ^ E.W := by omega
  have h3 : 3 < 2 ^ E.W := by omega
  have hP7 : parent + 7 < 2 ^ E.W := by omega
  have hP3 : parent + 3 < 2 ^ E.W := by omega
  have hGW : globalCap < 2 ^ E.W := by omega
  have hLW : localCap < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp [hintFinalCapFetch, runBlock, execInstr, hParent, hReadGlobal, hReadLocal,
      Nat.mod_eq_of_lt h7, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt hP7, Nat.mod_eq_of_lt hP3,
      Nat.mod_eq_of_lt hGW, Nat.mod_eq_of_lt hLW]

theorem hintFinalCapCode_spec (E : RAMEnv) (state : RAMState) (parent globalCap localCap : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (hReadGlobal : state.mem (parent + 7) = globalCap) (hReadLocal : state.mem (parent + 3) = localCap) :
    let out := runBlock hintFinalCapCode E state
    out.pc = state.pc + 17 ∧ out.mem = Function.update state.mem (parent + 7) (min 2 (globalCap + localCap)) ∧
      out.regs 0 = min 2 (globalCap + localCap) ∧ out.regs 14 = parent + 16 := by
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hFetch := hintFinalCapFetch_spec E sP parent globalCap localCap hEnd hParentP hGlobal hLocal
    (by rw [hMemP]; exact hReadGlobal) (by rw [hMemP]; exact hReadLocal)
  generalize hF : runBlock hintFinalCapFetch E sP = sF at hFetch
  obtain ⟨hPcF, hMemF, h4, h0, h8, hContextF⟩ := hFetch
  have hAdd := hintCapAddCode_spec E sF (parent + 7) globalCap localCap (by omega) hGlobal hLocal h4 h0 h8
  generalize hA : runBlock hintCapAddCode E sF = out at hAdd
  obtain ⟨hPcA, hMemA, hValueA, hContextA⟩ := hAdd
  have hRun : runBlock hintFinalCapCode E state = out := by rw [hintFinalCapCode, runBlock_append, runBlock_append, hP, hF, hA]
  rw [hRun]
  exact ⟨by omega, by rw [hMemA, hMemF, hMemP], hValueA, hContextA.trans (hContextF.trans hContextP)⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalCapCode_spec
end S_HintFinalCap20261120
section S_HintFinalChoose20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalChooseTail : List Instr := [.imm 15 1, .lt 1 0 15, .bxor 9 8 15, .lt 9 9 15, .mul 1 1 9]
def hintFinalChooseCode : List Instr := hintScanParent ++ hintFinalCapFetch ++ hintFinalChooseTail

theorem hintFinalChooseTail_spec (E : RAMEnv) (state : RAMState) (globalCap localCap : ℕ)
    (hWord : 4 < 2 ^ E.W) (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (h0 : state.regs 0 = globalCap) (h8 : state.regs 8 = localCap) :
    let out := runBlock hintFinalChooseTail E state
    out.pc = state.pc + 5 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (globalCap = 0 ∧ localCap = 1) ∧
      out.regs 14 = state.regs 14 := by
  classical
  have hOne : 1 < 2 ^ E.W := by omega
  have hThree : 3 < 2 ^ E.W := by omega
  interval_cases globalCap <;> interval_cases localCap <;>
    refine ⟨?_, rfl, ?_, ?_⟩ <;>
    simp [hintFinalChooseTail, runBlock, execInstr, h0, h8, hintTruth, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hThree]

theorem hintFinalChooseCode_spec (E : RAMEnv) (state : RAMState) (parent globalCap localCap : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (hReadGlobal : state.mem (parent + 7) = globalCap) (hReadLocal : state.mem (parent + 3) = localCap) :
    let out := runBlock hintFinalChooseCode E state
    out.pc = state.pc + 13 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (globalCap = 0 ∧ localCap = 1) ∧
      out.regs 14 = parent + 16 := by
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hFetch := hintFinalCapFetch_spec E sP parent globalCap localCap hEnd hParentP hGlobal hLocal
    (by rw [hMemP]; exact hReadGlobal) (by rw [hMemP]; exact hReadLocal)
  generalize hF : runBlock hintFinalCapFetch E sP = sF at hFetch
  obtain ⟨hPcF, hMemF, _, h0, h8, hContextF⟩ := hFetch
  have hChoose := hintFinalChooseTail_spec E sF globalCap localCap (by omega) hGlobal hLocal h0 h8
  generalize hC : runBlock hintFinalChooseTail E sF = out at hChoose
  obtain ⟨hPcC, hMemC, hFlagC, hContextC⟩ := hChoose
  have hRun : runBlock hintFinalChooseCode E state = out := by rw [hintFinalChooseCode, runBlock_append, runBlock_append, hP, hF, hC]
  rw [hRun]
  exact ⟨by omega, hMemC.trans (hMemF.trans hMemP), hFlagC, hContextC.trans (hContextF.trans hContextP)⟩

def hintFinalSaveTail : List Instr := [.load 4 11, .load 0 4, .imm 3 8, .add 3 11 3, .store 3 0]
def hintFinalSaveCode : List Instr := hintScanParent ++ hintFinalSaveTail

theorem hintFinalSaveCode_spec (E : RAMEnv) (state : RAMState) (parent outsideBase r : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hArray : outsideBase < 2 ^ E.W) (hR : r < 2 ^ E.W)
    (hPointer : state.mem parent = outsideBase) (hCount : state.mem outsideBase = r) :
    let out := runBlock hintFinalSaveCode E state
    out.pc = state.pc + 7 ∧ out.mem = Function.update state.mem (parent + 8) r ∧ out.regs 14 = parent + 16 := by
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hPointerP : sP.mem parent = outsideBase := by rw [hMemP]; exact hPointer
  have hCountP : sP.mem outsideBase = r := by rw [hMemP]; exact hCount
  have h8 : 8 < 2 ^ E.W := by omega
  have hAddr : parent + 8 < 2 ^ E.W := by omega
  have hTail : let out := runBlock hintFinalSaveTail E sP
      out.pc = sP.pc + 5 ∧ out.mem = Function.update sP.mem (parent + 8) r ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [hintFinalSaveTail, runBlock, execInstr, hParentP, hContextP, hPointerP, hCountP,
        Nat.mod_eq_of_lt hArray, Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt h8, Nat.mod_eq_of_lt hAddr]
  generalize hT : runBlock hintFinalSaveTail E sP = out at hTail
  obtain ⟨hPcT, hMemT, hContextT⟩ := hTail
  have hRun : runBlock hintFinalSaveCode E state = out := by rw [hintFinalSaveCode, runBlock_append, hP, hT]
  rw [hRun]
  exact ⟨by omega, by rw [hMemT, hMemP], hContextT⟩

def hintFinalChooseStmt : Stmt := .seq (.code hintFinalChooseCode)
  (.ite (.neqz 1) (.code hintFinalSaveCode) (.code []))
theorem hintFinalChooseStmt_len : hintFinalChooseStmt.len = 23 := rfl


theorem hintFinalChooseStmt_sem (parent outsideBase r globalCap localCap : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hArray : outsideBase < 2 ^ E.W) (hR : r < 2 ^ E.W) (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (hPointer : state.mem parent = outsideBase) (hCount : state.mem outsideBase = r)
    (hReadGlobal : state.mem (parent + 7) = globalCap) (hReadLocal : state.mem (parent + 3) = localCap)
    (hAt : At P base (hintFinalChooseStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 23) state (fun k out => k ≤ 22 ∧
      out.mem = (if globalCap = 0 ∧ localCap = 1 then Function.update state.mem (parent + 8) r else state.mem) ∧
      out.regs 14 = parent + 16) := by
  classical
  have hWord : 1 < 2 ^ E.W := by omega
  obtain ⟨hChooseAt, hBranchAt⟩ := At.seqStmt hAt
  change At P base hintFinalChooseCode at hChooseAt
  change At P (base + 13) ((Stmt.ite (.neqz 1) (.code hintFinalSaveCode) (.code [])).compile (base + 13)) at hBranchAt
  have hChoose := hintFinalChooseCode_spec E state parent globalCap localCap hEnd hContext hGlobal hLocal hReadGlobal hReadLocal
  generalize hC : runBlock hintFinalChooseCode E state = sC at hChoose
  obtain ⟨hPcC, hMemC, hFlagC, hContextC⟩ := hChoose
  have hRunC : (step P E)^[13] state = sC := by
    have hh := iterate_runBlock_of_at P E hintFinalChooseCode state (by rwa [hPc])
      (by simp [hintFinalChooseCode, hintScanParent, hintFinalCapFetch, hintFinalChooseTail, NoBranch, Instr.NoBranchI])
    rw [hC] at hh
    exact hh
  let Q : ℕ → RAMState → Prop := fun k out => k ≤ 9 ∧
    out.mem = (if globalCap = 0 ∧ localCap = 1 then Function.update state.mem (parent + 8) r else state.mem) ∧
    out.regs 14 = parent + 16
  have hBranch : Sem P E (base + 13) (base + 23) sC Q := by
    apply Sem.ite P E (base + 13) (.neqz 1) (.code hintFinalSaveCode) (.code []) sC Q hBranchAt hWord (by omega)
    · intro hGo
      change Sem P E (base + 14) (base + 21) {sC with pc := base + 14}
        (fun k out => Q (1 + k + 1) {out with pc := base + 23})
      have hGood : globalCap = 0 ∧ localCap = 1 := by
        by_contra hBad
        have hZero : sC.regs 1 = 0 := by simpa [hintTruth, hBad] using hFlagC
        exact hGo hZero
      have hSave := hintFinalSaveCode_spec E {sC with pc := base + 14} parent outsideBase r hEnd hContextC hArray hR
        (by rw [hMemC]; exact hPointer) (by rw [hMemC]; exact hCount)
      generalize hS : runBlock hintFinalSaveCode E {sC with pc := base + 14} = sS at hSave
      obtain ⟨_, hMemS, hCtxS⟩ := hSave
      have hNative := Sem.block P E (base + 14) hintFinalSaveCode {sC with pc := base + 14}
        (at_ite hBranchAt).2.2.1 (by simp [hintFinalSaveCode, hintScanParent, hintFinalSaveTail, NoBranch, Instr.NoBranchI]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hOut⟩ := hOut
      rw [hS] at hOut
      subst out
      refine ⟨by change k = 7 at hCost; omega, ?_, hCtxS⟩
      change sS.mem = _
      rw [if_pos hGood, hMemS, hMemC]
    · intro hStop
      change Sem P E (base + 22) (base + 22) {sC with pc := base + 22}
        (fun k out => Q (1 + k + 1) {out with pc := base + 23})
      have hBad : ¬ (globalCap = 0 ∧ localCap = 1) := by
        intro hGood
        have hOne : sC.regs 1 = 1 := by simpa [hintTruth, hGood] using hFlagC
        apply hStop
        change sC.regs 1 ≠ 0
        rw [hOne]; decide
      have hNative := Sem.block P E (base + 22) [] {sC with pc := base + 22}
        (at_ite hBranchAt).2.2.2.2.1 (by simp [NoBranch]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, rfl⟩ := hOut
      refine ⟨by change k = 0 at hCost; omega, ?_, hContextC⟩
      change sC.mem = _
      rw [if_neg hBad]
      exact hMemC
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hMemB, hCtxB⟩ := hBranch
  exact ⟨hPc, kB + 13, out, hintIterate_then (step P E) hRunC hRunB, hPcB, by omega, hMemB, hCtxB⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalChooseStmt_sem
end S_HintFinalChoose20261120
section S_HintFinalAccumulate20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalAccumulateStmt : Stmt := .seq hintFinalChooseStmt (.code hintFinalCapCode)
theorem hintFinalAccumulateStmt_len : hintFinalAccumulateStmt.len = 40 := rfl

/-- Save the first singleton class's outside count, then add the real local
    count to the global capped count. Only parent slots 7 and 8 can change. -/
theorem hintFinalAccumulateStmt_sem (parent outsideBase r globalCap localCap : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hArray : outsideBase < 2 ^ E.W) (hR : r < 2 ^ E.W) (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (hPointer : state.mem parent = outsideBase) (hCount : state.mem outsideBase = r)
    (hReadGlobal : state.mem (parent + 7) = globalCap) (hReadLocal : state.mem (parent + 3) = localCap)
    (hAt : At P base (hintFinalAccumulateStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 40) state (fun k out => k ≤ 39 ∧
      out.mem = Function.update
        (if globalCap = 0 ∧ localCap = 1 then Function.update state.mem (parent + 8) r else state.mem)
        (parent + 7) (min 2 (globalCap + localCap)) ∧
      out.regs 0 = min 2 (globalCap + localCap) ∧ out.regs 14 = parent + 16) := by
  classical
  obtain ⟨hChooseAt, hCapAt⟩ := At.seqStmt hAt
  change At P base (hintFinalChooseStmt.compile base) at hChooseAt
  change At P (base + 23) hintFinalCapCode at hCapAt
  obtain ⟨_, kC, sC, hRunC, hPcC, hCostC, hMemC, hCtxC⟩ :=
    hintFinalChooseStmt_sem parent outsideBase r globalCap localCap P E state base hEnd hContext
      hArray hR hGlobal hLocal hPointer hCount hReadGlobal hReadLocal hChooseAt hPc
  have hUntouched : ∀ addr, addr ≠ parent + 8 → sC.mem addr = state.mem addr := by
    intro addr hNe
    rw [hMemC]
    split_ifs <;> simp [Function.update_of_ne hNe]
  have hCap := hintFinalCapCode_spec E sC parent globalCap localCap hEnd hCtxC hGlobal hLocal
    ((hUntouched _ (by omega)).trans hReadGlobal) ((hUntouched _ (by omega)).trans hReadLocal)
  generalize hA : runBlock hintFinalCapCode E sC = out at hCap
  obtain ⟨hPcA, hMemA, hValueA, hCtxA⟩ := hCap
  have hRunA : (step P E)^[17] sC = out := by
    have hh := iterate_runBlock_of_at P E hintFinalCapCode sC (by rwa [hPcC])
      (by simp [hintFinalCapCode, hintScanParent, hintFinalCapFetch, hintCapAddCode, NoBranch, Instr.NoBranchI])
    rw [hA] at hh
    exact hh
  refine ⟨hPc, 17 + kC, out, hintIterate_then (step P E) hRunC hRunA, by omega, by omega, ?_, hValueA, hCtxA⟩
  rw [hMemA, hMemC]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalAccumulateStmt_sem
end S_HintFinalAccumulate20261120
section S_HintFinalSaved20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintSavedUnique (f : ℕ → ℕ) (j saved : ℕ) : Prop :=
  (∑ r ∈ Finset.range j, f r) = 1 → saved < j ∧ f saved = 1 ∧ ∀ r < j, r ≠ saved → f r = 0

theorem HintSavedUnique.zero (f : ℕ → ℕ) (saved : ℕ) : HintSavedUnique f 0 saved := by
  intro hSum
  simp at hSum

theorem HintSavedUnique.step (f : ℕ → ℕ) (j saved : ℕ) (hOld : HintSavedUnique f j saved) :
    HintSavedUnique f (j + 1)
      (if min 2 (∑ r ∈ Finset.range j, f r) = 0 ∧ min 2 (f j) = 1 then j else saved) := by
  classical
  intro hNew
  have hStep := Finset.sum_range_succ f j
  have hSum : (∑ r ∈ Finset.range j, f r) + f j = 1 := by rw [← hStep]; exact hNew
  by_cases hZero : (∑ r ∈ Finset.range j, f r) = 0
  · have hOne : f j = 1 := by omega
    have hCond : min 2 (∑ r ∈ Finset.range j, f r) = 0 ∧ min 2 (f j) = 1 := by omega
    rw [if_pos hCond]
    refine ⟨by omega, hOne, ?_⟩
    intro r hr hNe
    have hr' : r ∈ Finset.range j := Finset.mem_range.mpr (by omega)
    have hLe : f r ≤ ∑ s ∈ Finset.range j, f s := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hr'
    omega
  · have hOne : (∑ r ∈ Finset.range j, f r) = 1 := by omega
    have hJZero : f j = 0 := by omega
    have hCond : ¬ (min 2 (∑ r ∈ Finset.range j, f r) = 0 ∧ min 2 (f j) = 1) := by omega
    rw [if_neg hCond]
    obtain ⟨hSaved, hSavedOne, hOthers⟩ := hOld hOne
    refine ⟨by omega, hSavedOne, ?_⟩
    intro r hr hNe
    by_cases hEq : r = j
    · simpa only [hEq] using hJZero
    · exact hOthers r (by omega) hNe

theorem hintCappedPrefix_step (f : ℕ → ℕ) (j : ℕ) :
    min 2 (min 2 (∑ r ∈ Finset.range j, f r) + min 2 (f j)) =
      min 2 (∑ r ∈ Finset.range (j + 1), f r) := by
  rw [Finset.sum_range_succ, hintCap2_add_capped]

theorem hintFinal_cap_one (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (Nj maxR : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (hHintValid : ∀ j, (coords j).val < Nj) :
    min 2 (hintFinalRawPrefix G coords beta Nj (maxR + 1) v hPos) = 1 ↔
      (hintFinalUnion G coords beta Nj maxR v).card = 1 := by
  rw [hintFinalRawPrefix_full]
  exact (hintCap2_one _).trans (hintFinalRawCount_one G coords hInj beta hPrefix Nj maxR v hPos hHintValid)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintSavedUnique.step
#print axioms LinearSetReconciliation327.Main.hintFinal_cap_one
end S_HintFinalSaved20261120
section S_HintFinalFrame20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintFinalFrame (G : HintGaussArea) (parent outsideBase bitmapBase Nj maxR : ℕ)
    (original memory : ℕ → ℕ) : Prop :=
  ∀ addr, (addr < bitmapBase ∨ bitmapBase + Nj ≤ addr) →
    (addr < outsideBase ∨ outsideBase + 1 + maxR ≤ addr) →
    addr ≠ parent + 3 → addr ≠ parent + 7 → addr ≠ parent + 8 →
    (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
    (addr < G.context ∨ G.pivotRow + G.rows ≤ addr) → memory addr = original addr

theorem HintFinalFrame.refl (G : HintGaussArea) (parent outsideBase bitmapBase Nj maxR : ℕ) (memory : ℕ → ℕ) :
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR memory memory := by intro _ _ _ _ _ _ _ _; rfl

theorem HintFinalFrame.trans {G : HintGaussArea} {parent outsideBase bitmapBase Nj maxR : ℕ}
    {first middle last : ℕ → ℕ}
    (h1 : HintFinalFrame G parent outsideBase bitmapBase Nj maxR first middle)
    (h2 : HintFinalFrame G parent outsideBase bitmapBase Nj maxR middle last) :
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR first last := by
  intro addr hB hO h3 h7 h8 hR hG
  exact (h2 addr hB hO h3 h7 h8 hR hG).trans (h1 addr hB hO h3 h7 h8 hR hG)

theorem HintFinalFrame.of_controller {G : HintGaussArea} {parent outsideBase bitmapBase Nj maxR : ℕ}
    {original memory : ℕ → ℕ} (h : HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR original memory) :
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR original memory := by
  intro addr hB hO h3 _ _ hR hG
  exact h addr hB hO h3 hR hG

theorem HintFinalFrame.of_scan {G : HintGaussArea} {parent outsideBase bitmapBase Nj maxR r : ℕ}
    {original memory : ℕ → ℕ} (hr : r ≤ maxR) (h : HintScanFrame G parent outsideBase r original memory) :
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR original memory := by
  apply HintFinalFrame.of_controller
  apply HintRowControllerFrame.of_row hr
  intro addr _ hO h3 hR hG
  exact h addr hO h3 hR hG

theorem HintFinalFrame.set_meta (G : HintGaussArea) (parent outsideBase bitmapBase Nj maxR : ℕ)
    (memory : ℕ → ℕ) (i value : ℕ) (hi : i = 7 ∨ i = 8) :
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR memory (Function.update memory (parent + i) value) := by
  intro addr _ _ _ h7 h8 _ _
  apply Function.update_of_ne
  rcases hi with rfl | rfl
  · exact h7
  · exact h8

theorem HintFinalFrame.parent {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj maxR parent outsideBase bitmapBase : ℕ} {original memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hFrame : HintFinalFrame G parent outsideBase bitmapBase Nj maxR original memory)
    (i : ℕ) (hi : 4 ≤ i) (hi' : i < 16) (h7 : i ≠ 7) (h8 : i ≠ 8) :
    memory (parent + i) = original (parent + i) := by
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hBitmap := hPublic.bitmap_span
  have hParent := hPublic.parent_eq
  exact hFrame _ (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inl (by omega))

theorem HintScanReadOnly.set_count {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj maxR oldCount parent outsideBase bitmapBase : ℕ} {v : HintVec G.rows} {memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hData : HintScanReadOnly G coords Nj oldCount parent outsideBase bitmapBase v memory) (count : ℕ) :
    HintScanReadOnly G coords Nj count parent outsideBase bitmapBase v (Function.update memory outsideBase count) := by
  have hInput := HintRowInput.set_count hPublic
    (HintRowInput.mk hData.outside_pointer hData.bitmap_pointer hData.radix hData.outside_count hData.hints hData.observation) count
  refine ⟨hInput.outside_pointer, hInput.bitmap_pointer, hInput.radix, hInput.outside_count, hInput.hints, hInput.observation, ?_⟩
  intro q hq
  rw [Function.update_of_ne (by have := hPublic.bitmap_span; omega : bitmapBase + q ≠ outsideBase)]
  exact hData.bitmap q hq

theorem HintScanReadOnly.set_meta {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj maxR count parent outsideBase bitmapBase : ℕ} {v : HintVec G.rows} {memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hData : HintScanReadOnly G coords Nj count parent outsideBase bitmapBase v memory)
    (i value : ℕ) (hi : 3 ≤ i) :
    HintScanReadOnly G coords Nj count parent outsideBase bitmapBase v (Function.update memory (parent + i) value) := by
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hBitmap := hPublic.bitmap_span
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by omega : parent ≠ parent + i)]; exact hData.outside_pointer
  · rw [Function.update_of_ne (by omega : parent + 1 ≠ parent + i)]; exact hData.bitmap_pointer
  · rw [Function.update_of_ne (by omega : parent + 2 ≠ parent + i)]; exact hData.radix
  · rw [Function.update_of_ne (by omega : outsideBase ≠ parent + i)]; exact hData.outside_count
  · intro j
    rw [Function.update_of_ne (by have := j.isLt; omega : G.hintList + j.val ≠ parent + i)]
    exact hData.hints j
  · intro t
    rw [Function.update_of_ne (by have := t.isLt; omega : G.hintList + G.hints + G.rows + t.val ≠ parent + i)]
    exact hData.observation t
  · intro q hq
    rw [Function.update_of_ne (by omega : bitmapBase + q ≠ parent + i)]
    exact hData.bitmap q hq

theorem hintGaussHeader_set_meta {G : HintGaussArea} {index parent : ℕ} {memory : ℕ → ℕ}
    (hParent : parent + 16 = G.context) (hHeader : HintGaussHeader G index memory)
    (i value : ℕ) (hi : i < 16) : HintGaussHeader G index (Function.update memory (parent + i) value) := by
  intro t ht
  rw [Function.update_of_ne (by omega : G.context + t ≠ parent + i)]
  exact hHeader t ht

structure HintFinalState (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj parent outsideBase bitmapBase maxR j : ℕ)
    (v : HintVec G.rows) (hPos : 0 < Nj) (original : ℕ → ℕ) (state : RAMState) : Prop where
  readonly : HintScanReadOnly G coords Nj j parent outsideBase bitmapBase v state.mem
  header : ∃ index, HintGaussHeader G index state.mem
  context_value : state.regs 14 = G.context
  limit : state.mem (parent + 4) = maxR
  total : state.mem (parent + 7) = min 2 (hintFinalRawPrefix G coords beta Nj j v hPos)
  saved : HintSavedUnique (fun r => (hintFamilySuccesses G coords beta Nj r v hPos).card) j (state.mem (parent + 8))
  frame : HintFinalFrame G parent outsideBase bitmapBase Nj maxR original state.mem

theorem HintFinalState.pc {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {Nj parent outsideBase bitmapBase maxR j : ℕ}
    {v : HintVec G.rows} {hPos : 0 < Nj} {original : ℕ → ℕ} {state : RAMState}
    (h : HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR j v hPos original state) (pc : ℕ) :
    HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR j v hPos original {state with pc := pc} :=
  ⟨h.readonly, h.header, h.context_value, h.limit, h.total, h.saved, h.frame⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintScanReadOnly.set_meta
end S_HintFinalFrame20261120
section S_HintFinalAccInvariant20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintFinalTallied (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj parent outsideBase bitmapBase maxR count progress : ℕ)
    (v : HintVec G.rows) (hPos : 0 < Nj) (original : ℕ → ℕ) (state : RAMState) : Prop where
  readonly : HintScanReadOnly G coords Nj count parent outsideBase bitmapBase v state.mem
  header : ∃ index, HintGaussHeader G index state.mem
  context_value : state.regs 14 = G.context
  limit : state.mem (parent + 4) = maxR
  total : state.mem (parent + 7) = min 2 (hintFinalRawPrefix G coords beta Nj progress v hPos)
  saved : HintSavedUnique (fun r => (hintFamilySuccesses G coords beta Nj r v hPos).card) progress (state.mem (parent + 8))
  frame : HintFinalFrame G parent outsideBase bitmapBase Nj maxR original state.mem

theorem HintFinalState.after_accumulate {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj parent outsideBase bitmapBase maxR j : ℕ} {v : HintVec G.rows} {hPos : 0 < Nj}
    {original : ℕ → ℕ} {state out : RAMState}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hState : HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR j v hPos original state)
    (hMemory : out.mem = Function.update
      (if min 2 (hintFinalRawPrefix G coords beta Nj j v hPos) = 0 ∧
          min 2 (hintFamilySuccesses G coords beta Nj j v hPos).card = 1
        then Function.update state.mem (parent + 8) j else state.mem)
      (parent + 7) (min 2 (min 2 (hintFinalRawPrefix G coords beta Nj j v hPos) +
        min 2 (hintFamilySuccesses G coords beta Nj j v hPos).card)))
    (hContext : out.regs 14 = G.context) :
    HintFinalTallied G coords beta Nj parent outsideBase bitmapBase maxR j (j + 1) v hPos original out := by
  classical
  let oldSum := hintFinalRawPrefix G coords beta Nj j v hPos
  let localCount := (hintFamilySuccesses G coords beta Nj j v hPos).card
  let choose := min 2 oldSum = 0 ∧ min 2 localCount = 1
  let M := if choose then Function.update state.mem (parent + 8) j else state.mem
  let value := min 2 (min 2 oldSum + min 2 localCount)
  have hMemory' : out.mem = Function.update M (parent + 7) value := hMemory
  have hDataM : HintScanReadOnly G coords Nj j parent outsideBase bitmapBase v M := by
    dsimp only [M]
    split_ifs
    · exact HintScanReadOnly.set_meta hPublic hState.readonly 8 j (by decide)
    · exact hState.readonly
  have hHeaderM : ∃ index, HintGaussHeader G index M := by
    obtain ⟨index, hHeader⟩ := hState.header
    dsimp only [M]
    split_ifs
    · exact ⟨index, hintGaussHeader_set_meta hPublic.parent_eq hHeader 8 j (by decide)⟩
    · exact ⟨index, hHeader⟩
  have hFrameM : HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem M := by
    dsimp only [M]
    split_ifs
    · exact HintFinalFrame.set_meta G parent outsideBase bitmapBase Nj maxR state.mem 8 j (Or.inr rfl)
    · exact HintFinalFrame.refl G parent outsideBase bitmapBase Nj maxR state.mem
  have hLocalFrame : HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem out.mem := by
    rw [hMemory']
    exact hFrameM.trans (HintFinalFrame.set_meta G parent outsideBase bitmapBase Nj maxR M 7 value (Or.inl rfl))
  refine ⟨?_, ?_, hContext, (hLocalFrame.parent hPublic 4 (by decide) (by decide) (by decide) (by decide)).trans hState.limit,
    ?_, ?_, hState.frame.trans hLocalFrame⟩
  · rw [hMemory']
    exact HintScanReadOnly.set_meta hPublic hDataM 7 value (by decide)
  · obtain ⟨index, hHeader⟩ := hHeaderM
    rw [hMemory']
    exact ⟨index, hintGaussHeader_set_meta hPublic.parent_eq hHeader 7 value (by decide)⟩
  · have hValueAt : out.mem (parent + 7) = value := by simp [hMemory']
    rw [hValueAt]
    change min 2 (min 2 (hintFinalRawPrefix G coords beta Nj j v hPos) +
        min 2 (hintFamilySuccesses G coords beta Nj j v hPos).card) =
      min 2 (hintFinalRawPrefix G coords beta Nj (j + 1) v hPos)
    rw [hintFinalRawPrefix_succ, hintCap2_add_capped]
  · have hSavedValue : out.mem (parent + 8) = if choose then j else state.mem (parent + 8) := by
      rw [hMemory', Function.update_of_ne (by omega : parent + 8 ≠ parent + 7)]
      dsimp only [M]
      split_ifs <;> simp
    rw [hSavedValue]
    exact hState.saved.step

theorem HintFinalTallied.after_count {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj parent outsideBase bitmapBase maxR j : ℕ} {v : HintVec G.rows} {hPos : 0 < Nj}
    {original : ℕ → ℕ} {state out : RAMState}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hState : HintFinalTallied G coords beta Nj parent outsideBase bitmapBase maxR j (j + 1) v hPos original state)
    (hMemory : out.mem = Function.update state.mem outsideBase (j + 1)) (hContext : out.regs 14 = G.context) :
    HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR (j + 1) v hPos original out := by
  have hFrame : HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR state.mem out.mem := by
    rw [hMemory]
    exact HintRowControllerFrame.set_count G parent outsideBase bitmapBase Nj maxR state.mem (j + 1)
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hParent := hPublic.parent_eq
  refine ⟨?_, ?_, hContext, (hFrame.parent hPublic 4 (by decide) (by decide)).trans hState.limit,
    (hFrame.parent hPublic 7 (by decide) (by decide)).trans hState.total, ?_,
    hState.frame.trans (HintFinalFrame.of_controller hFrame)⟩
  · rw [hMemory]
    exact HintScanReadOnly.set_count hPublic hState.readonly (j + 1)
  · obtain ⟨index, hHeader⟩ := hState.header
    refine ⟨index, ?_⟩
    intro i hi
    rw [hMemory, Function.update_of_ne (by omega : G.context + i ≠ outsideBase)]
    exact hHeader i hi
  · rw [hFrame.parent hPublic 8 (by decide) (by decide)]
    exact hState.saved

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintFinalState.after_accumulate
end S_HintFinalAccInvariant20261120
section S_HintFinalBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalBody : Stmt := .seq hintScanFirstPassStmt (.seq hintFinalAccumulateStmt (.code hintRowAdvanceCode))
theorem hintFinalBody_len : hintFinalBody.len = 713 := rfl

def hintFinalBodyTime (G : HintGaussArea) (Nj r : ℕ) : ℕ :=
  7 * r + 73 + (hintScanBodyTime G r + 2) * Nj ^ r

theorem hintFinalBody_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj parent outsideBase bitmapBase maxR j : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) (original : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase) (hj : j ≤ maxR)
    (hState : HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR j v hPos original state)
    (hAt : At P base (hintFinalBody.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 713) state (fun k out => k ≤ hintFinalBodyTime G Nj j ∧
      HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR (j + 1) v hPos original out ∧
      out.regs 13 = hintTruth (j + 1 ≤ maxR)) := by
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hSpan := hPublic.fits.span
  obtain ⟨hFirstAt, hTailAt⟩ := At.seqStmt hAt
  change At P base (hintScanFirstPassStmt.compile base) at hFirstAt
  change At P (base + 661) ((Stmt.seq hintFinalAccumulateStmt (.code hintRowAdvanceCode)).compile (base + 661)) at hTailAt
  obtain ⟨hAccAt, hAdvanceAt⟩ := At.seqStmt hTailAt
  change At P (base + 661) (hintFinalAccumulateStmt.compile (base + 661)) at hAccAt
  change At P (base + 701) hintRowAdvanceCode at hAdvanceAt
  obtain ⟨_, kF, sF, hRunF, hPcF, hCostF, hCountF, _, hDataF, hHeaderF, hCtxF, hScanFrameF⟩ :=
    hintScanFirstPassStmt_sem G coords beta hPrefix Nj j parent outsideBase bitmapBase v P E state base
      (hPublic.at_count j hj) hState.readonly hState.header hState.context_value hFirstAt hPc
  have hMutationF : HintRowMutationFrame G parent outsideBase bitmapBase Nj j state.mem sF.mem := by
    intro addr _ hO h3 hR hG
    exact hScanFrameF addr hO h3 hR hG
  have hMetaF : ∀ i, 4 ≤ i → i < 16 → sF.mem (parent + i) = state.mem (parent + i) := by
    intro i hi hi'
    exact hMutationF.parent (hPublic.at_count j hj) i hi hi'
  have hStateF : HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR j v hPos original sF := by
    refine ⟨hDataF, hHeaderF, hCtxF, (hMetaF 4 (by decide) (by decide)).trans hState.limit,
      (hMetaF 7 (by decide) (by decide)).trans hState.total, ?_,
      hState.frame.trans (HintFinalFrame.of_scan hj hScanFrameF)⟩
    rw [hMetaF 8 (by decide) (by decide)]
    exact hState.saved
  obtain ⟨_, kA, sA, hRunA, hPcA, hCostA, hMemA, _, hCtxA⟩ :=
    hintFinalAccumulateStmt_sem parent outsideBase j
      (min 2 (hintFinalRawPrefix G coords beta Nj j v hPos))
      (min 2 (hintFamilySuccesses G coords beta Nj j v hPos).card)
      P E sF (base + 661) (by omega) (hCtxF.trans hParent.symm) (by omega) (by omega)
      (min_le_left _ _) (min_le_left _ _) hDataF.outside_pointer hDataF.outside_count hStateF.total hCountF hAccAt hPcF
  have hTallied : HintFinalTallied G coords beta Nj parent outsideBase bitmapBase maxR j (j + 1) v hPos original sA :=
    HintFinalState.after_accumulate hPublic hStateF hMemA (hCtxA.trans hParent)
  have hAdvance := hintRowAdvanceCode_spec E sA parent outsideBase j maxR (by omega) hCtxA
    (by omega) (by omega) (by omega) hTallied.readonly.outside_pointer hTallied.readonly.outside_count hTallied.limit
  generalize hD : runBlock hintRowAdvanceCode E sA = out at hAdvance
  obtain ⟨hPcD, hMemD, hGoD, _, _, hCtxD⟩ := hAdvance
  have hStateD := HintFinalTallied.after_count hPublic hTallied hMemD (hCtxD.trans hParent)
  have hRunD : (step P E)^[12] sA = out := by
    have hh := iterate_runBlock_of_at P E hintRowAdvanceCode sA (by rwa [hPcA])
      (by simp [hintRowAdvanceCode, hintScanParent, hintRowAdvanceFetch, hintParentLoad, hintRowAdvanceTail, NoBranch, Instr.NoBranchI])
    simpa only [hintRowAdvanceCode_length, hD] using hh
  refine ⟨hPc, 12 + (kA + kF), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunF hRunA) hRunD,
    by omega, ?_, hStateD, hGoD⟩
  dsimp only [hintFinalBodyTime]
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalBody_sem
end S_HintFinalBody20261120
section S_HintFinalLoop20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalLoop : Stmt := .loop (.neqz 13) hintFinalBody
theorem hintFinalLoop_len : hintFinalLoop.len = 715 := rfl

def hintFinalBudget (G : HintGaussArea) (Nj maxR : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (maxR + 1), hintFinalBodyTime G Nj r

theorem hintFinalLoop_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj parent outsideBase bitmapBase maxR : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) (original : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hState : HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR 0 v hPos original state)
    (hGoInitial : state.regs 13 = 1)
    (hAt : At P base (hintFinalLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 715) state (fun k out => k ≤ (hintFinalBudget G Nj maxR + 2) * (maxR + 1) + 1 ∧
      HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR (maxR + 1) v hPos original out ∧
      out.regs 13 = 0) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = maxR + 1 ∧
    HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR j v hPos original st ∧
      st.regs 13 = hintTruth (j ≤ maxR)
  have hBodyAt : At P (base + 1) (hintFinalBody.compile (base + 1)) := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, hState, hGo⟩ := hI
    exact ⟨j, hJ, hState.pc pc, hGo⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.neqz 13).code E st) := by
    intro left st hI
    exact hI
  have hGo : ∀ left st, I (left + 1) st → (Cond.neqz 13).eval st := by
    intro left st hI
    obtain ⟨j, hJ, _, hGo⟩ := hI
    have hj : j ≤ maxR := by omega
    have hOne : st.regs 13 = 1 := by simpa [hintTruth, hj] using hGo
    change st.regs 13 ≠ 0
    rw [hOne]; decide
  have hStop : ∀ st, I 0 st → ¬ (Cond.neqz 13).eval st := by
    intro st hI
    obtain ⟨j, hJ, _, hGo⟩ := hI
    have hj : j = maxR + 1 := by omega
    have hZero : st.regs 13 = 0 := by simpa [hintTruth, hj] using hGo
    change ¬ st.regs 13 ≠ 0
    rw [hZero]; simp
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.neqz 13).code.length + 1 →
      Sem P E (base + (Cond.neqz 13).code.length + 1)
        (base + (Cond.neqz 13).code.length + 1 + hintFinalBody.len) st
        (fun k out => k ≤ hintFinalBudget G Nj maxR ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, hState, _⟩ := hI
    have hj : j ≤ maxR := by omega
    have hNative := hintFinalBody_sem G coords beta hPrefix Nj parent outsideBase bitmapBase maxR j v hPos original
      P E st (base + 1) hPublic hj hState hBodyAt hStart
    have hBudget : hintFinalBodyTime G Nj j ≤ hintFinalBudget G Nj maxR :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hFinal, hGo⟩ := hOut
    exact ⟨hCost.trans hBudget, j + 1, by omega, hFinal, hGo⟩
  have hInitial : I (maxR + 1) state :=
    ⟨0, by omega, hState, by simpa [hintTruth] using hGoInitial⟩
  have hNative := hintLoopFuel_sem P E base (.neqz 13) hintFinalBody hAt hPublic.geometry.word_bound I
    (hintFinalBudget G Nj maxR) hIpc hItest hGo hStop hBody (maxR + 1) state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hJ, hFinal, hGo⟩ := hOut
  simp only [Cond.code, List.length_nil, Nat.zero_add] at hCost
  have hj : j = maxR + 1 := by omega
  rw [hj] at hFinal hGo
  exact ⟨hCost, hFinal, by simpa [hintTruth] using hGo⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalLoop_sem
end S_HintFinalLoop20261120
section S_HintFinalInit20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalResetTail : List Instr := [.imm 3 7, .add 3 11 3, .imm 0 0, .store 3 0, .imm 13 1]
def hintFinalResetCode : List Instr := hintScanParent ++ hintFinalResetTail

theorem hintFinalResetCode_spec (E : RAMEnv) (state : RAMState) (parent : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16) :
    let out := runBlock hintFinalResetCode E state
    out.pc = state.pc + 7 ∧ out.mem = Function.update state.mem (parent + 7) 0 ∧
      out.regs 13 = 1 ∧ out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have h7 : 7 < 2 ^ E.W := by omega
  have hAddr : parent + 7 < 2 ^ E.W := by omega
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hTail : let out := runBlock hintFinalResetTail E sP
      out.pc = sP.pc + 5 ∧ out.mem = Function.update sP.mem (parent + 7) 0 ∧
        out.regs 13 = 1 ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [hintFinalResetTail, runBlock, execInstr, hParentP, hContextP,
        Nat.mod_eq_of_lt h7, Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hWord]
  generalize hT : runBlock hintFinalResetTail E sP = out at hTail
  obtain ⟨hPcT, hMemT, hGo, hCtx⟩ := hTail
  have hRun : runBlock hintFinalResetCode E state = out := by rw [hintFinalResetCode, runBlock_append, hP, hT]
  rw [hRun]
  exact ⟨by omega, by rw [hMemT, hMemP], hGo, hCtx⟩

def hintFinalInitStmt : Stmt := .seq (.code hintRowOuterInitCode) (.seq hintRowBitmapStmt (.code hintFinalResetCode))
theorem hintFinalInitStmt_len : hintFinalInitStmt.len = 48 := rfl

theorem hintFinalInitStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj parent outsideBase bitmapBase maxR oldCount : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hLimit : state.mem (parent + 4) = maxR)
    (hAt : At P base (hintFinalInitStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 48) state (fun k out => k ≤ 7 * Nj + 8 * G.hints + 37 ∧
      HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR 0 v hPos state.mem out ∧ out.regs 13 = 1) := by
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hSpan := hPublic.fits.span
  obtain ⟨hInitAt, hTailAt⟩ := At.seqStmt hAt
  change At P base hintRowOuterInitCode at hInitAt
  change At P (base + 7) ((Stmt.seq hintRowBitmapStmt (.code hintFinalResetCode)).compile (base + 7)) at hTailAt
  obtain ⟨hBitmapAt, hResetAt⟩ := At.seqStmt hTailAt
  change At P (base + 7) (hintRowBitmapStmt.compile (base + 7)) at hBitmapAt
  change At P (base + 41) hintFinalResetCode at hResetAt
  have hInit := hintRowOuterInitCode_spec E state parent outsideBase (by omega) (hContext.trans hParent.symm)
    (by omega) hInput.outside_pointer
  generalize hI : runBlock hintRowOuterInitCode E state = sI at hInit
  obtain ⟨hPcI, hMemI, _, _, hCtxI⟩ := hInit
  have hRunI : (step P E)^[7] state = sI := by
    have hh := iterate_runBlock_of_at P E hintRowOuterInitCode state (by rwa [hPc])
      (by simp [hintRowOuterInitCode, hintScanParent, hintRowOuterInitTail, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  have hInputI : HintRowInput G coords Nj 0 parent outsideBase bitmapBase v sI.mem := by
    rw [hMemI]; exact HintRowInput.set_count hPublic hInput 0
  have hHeaderI : ∃ index, HintGaussHeader G index sI.mem := by
    obtain ⟨index, hHeader⟩ := hHeader
    refine ⟨index, ?_⟩
    intro i hi
    rw [hMemI, Function.update_of_ne (by omega : G.context + i ≠ outsideBase)]
    exact hHeader i hi
  have hFrameI : HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem sI.mem := by
    rw [hMemI]
    exact HintFinalFrame.of_controller (HintRowControllerFrame.set_count G parent outsideBase bitmapBase Nj maxR state.mem 0)
  obtain ⟨_, kB, sB, hRunB, hPcB, hCostB, hDataB, hHeaderB, hCtxB, hBitmapFrame⟩ :=
    hintRowBitmapStmt_sem G coords beta hPrefix Nj 0 parent outsideBase bitmapBase v P E sI (base + 7)
      (hPublic.at_count 0 (by omega)) hInputI hHeaderI (hCtxI.trans hParent) hBitmapAt (by omega)
  have hFrameB : HintFinalFrame G parent outsideBase bitmapBase Nj maxR sI.mem sB.mem := by
    intro addr hB _ _ _ _ _ _
    exact hBitmapFrame addr hB
  have hReset := hintFinalResetCode_spec E sB parent (by omega) (hCtxB.trans hParent.symm)
  generalize hR : runBlock hintFinalResetCode E sB = out at hReset
  obtain ⟨hPcR, hMemR, hGoR, hCtxR⟩ := hReset
  have hRunR : (step P E)^[7] sB = out := by
    have hh := iterate_runBlock_of_at P E hintFinalResetCode sB (by rwa [hPcB])
      (by simp [hintFinalResetCode, hintScanParent, hintFinalResetTail, NoBranch, Instr.NoBranchI])
    rw [hR] at hh
    exact hh
  have hFrameR : HintFinalFrame G parent outsideBase bitmapBase Nj maxR sB.mem out.mem := by
    rw [hMemR]
    exact HintFinalFrame.set_meta G parent outsideBase bitmapBase Nj maxR sB.mem 7 0 (Or.inl rfl)
  have hAllFrame := hFrameI.trans (hFrameB.trans hFrameR)
  have hFinal : HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR 0 v hPos state.mem out := by
    refine ⟨?_, ?_, hCtxR.trans hParent,
      (hAllFrame.parent hPublic 4 (by decide) (by decide) (by decide) (by decide)).trans hLimit,
      ?_, HintSavedUnique.zero _ _, hAllFrame⟩
    · rw [hMemR]
      exact HintScanReadOnly.set_meta hPublic hDataB 7 0 (by decide)
    · obtain ⟨index, hHeader⟩ := hHeaderB
      rw [hMemR]
      exact ⟨index, hintGaussHeader_set_meta hParent hHeader 7 0 (by decide)⟩
    · simp [hMemR, hintFinalRawPrefix_zero]
  exact ⟨hPc, 7 + (kB + 7), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunI hRunB) hRunR,
    by omega, by omega, hFinal, hGoR⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalInitStmt_sem
end S_HintFinalInit20261120
section S_HintFinalScan20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalScanStmt : Stmt := .seq hintFinalInitStmt hintFinalLoop
theorem hintFinalScanStmt_len : hintFinalScanStmt.len = 763 := rfl

/-- Native all-count final scan from actual row inputs. It constructs the hint
    bitmap, initializes all needed counters, and records a real replay count. -/
theorem hintFinalScanStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj parent outsideBase bitmapBase maxR oldCount : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hLimit : state.mem (parent + 4) = maxR)
    (hAt : At P base (hintFinalScanStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 763) state (fun k out =>
      k ≤ (hintFinalBudget G Nj maxR + 2) * (maxR + 1) + 7 * Nj + 8 * G.hints + 38 ∧
      HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR (maxR + 1) v hPos state.mem out ∧
      out.regs 13 = 0 ∧
      (out.mem (parent + 7) = 1 ↔ (hintFinalUnion G coords beta Nj maxR v).card = 1) ∧
      (out.mem (parent + 7) = 1 → ∃ r ≤ maxR, out.mem (parent + 8) = r ∧
        (hintFamilySuccesses G coords beta Nj r v hPos).card = 1 ∧
        ∀ s ≤ maxR, s ≠ r → (hintFamilySuccesses G coords beta Nj s v hPos).card = 0)) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base (hintFinalInitStmt.compile base) at hInitAt
  change At P (base + 48) (hintFinalLoop.compile (base + 48)) at hLoopAt
  obtain ⟨_, kI, sI, hRunI, hPcI, hCostI, hStateI, hGoI⟩ :=
    hintFinalInitStmt_sem G coords beta hPrefix Nj parent outsideBase bitmapBase maxR oldCount v hPos P E state base
      hPublic hInput hHeader hContext hLimit hInitAt hPc
  obtain ⟨_, kL, out, hRunL, hPcL, hCostL, hFinal, hGo⟩ :=
    hintFinalLoop_sem G coords beta hPrefix Nj parent outsideBase bitmapBase maxR v hPos state.mem P E sI (base + 48)
      hPublic hStateI hGoI hLoopAt hPcI
  refine ⟨hPc, kL + kI, out, hintIterate_then (step P E) hRunI hRunL,
    by omega, by omega, hFinal, hGo, ?_, ?_⟩
  · rw [hFinal.total]
    exact hintFinal_cap_one G coords hPublic.injective beta hPrefix Nj maxR v hPos hPublic.hint_valid
  · intro hOne
    have hCapOne : min 2 (hintFinalRawPrefix G coords beta Nj (maxR + 1) v hPos) = 1 := hFinal.total.symm.trans hOne
    have hRawOne := (hintCap2_one _).mp hCapOne
    obtain ⟨hBound, hSavedOne, hOthers⟩ := hFinal.saved hRawOne
    exact ⟨out.mem (parent + 8), by omega, rfl, hSavedOne, fun s hs hNe => hOthers s (by omega) hNe⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalScanStmt_sem
end S_HintFinalScan20261120
section S_HintFinalReplayPrep20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalRestoreTail : List Instr := [.load 4 11, .imm 3 8, .add 3 11 3, .load 0 3, .store 4 0]
def hintFinalRestoreCode : List Instr := hintScanParent ++ hintFinalRestoreTail

theorem hintFinalRestoreCode_spec (E : RAMEnv) (state : RAMState) (parent outsideBase r : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hArray : outsideBase < 2 ^ E.W) (hR : r < 2 ^ E.W)
    (hPointer : state.mem parent = outsideBase) (hSaved : state.mem (parent + 8) = r) :
    let out := runBlock hintFinalRestoreCode E state
    out.pc = state.pc + 7 ∧ out.mem = Function.update state.mem outsideBase r ∧ out.regs 14 = parent + 16 := by
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hPointerP : sP.mem parent = outsideBase := by rw [hMemP]; exact hPointer
  have hSavedP : sP.mem (parent + 8) = r := by rw [hMemP]; exact hSaved
  have h8 : 8 < 2 ^ E.W := by omega
  have hAddr : parent + 8 < 2 ^ E.W := by omega
  have hTail : let out := runBlock hintFinalRestoreTail E sP
      out.pc = sP.pc + 5 ∧ out.mem = Function.update sP.mem outsideBase r ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [hintFinalRestoreTail, runBlock, execInstr, hParentP, hContextP, hPointerP, hSavedP,
        Nat.mod_eq_of_lt hArray, Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt h8, Nat.mod_eq_of_lt hAddr]
  generalize hT : runBlock hintFinalRestoreTail E sP = out at hTail
  obtain ⟨hPcT, hMemT, hContextT⟩ := hTail
  have hRun : runBlock hintFinalRestoreCode E state = out := by rw [hintFinalRestoreCode, runBlock_append, hP, hT]
  rw [hRun]
  exact ⟨by omega, by rw [hMemT, hMemP], hContextT⟩

def hintFinalCheckPrep : List Instr := hintScanParent ++ [.imm 4 7, .add 4 11 4]
def hintFinalCheckCode : List Instr := hintFinalCheckPrep ++ hintFamilyCheckTail

theorem hintFinalOneTail_spec (E : RAMEnv) (state : RAMState) (pointer count : ℕ)
    (hWord : 3 < 2 ^ E.W) (hCount : count ≤ 2)
    (h4 : state.regs 4 = pointer) (hRead : state.mem pointer = count) :
    let out := runBlock hintFamilyCheckTail E state
    out.pc = state.pc + 4 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (count = 1) ∧ out.regs 14 = state.regs 14 := by
  classical
  have hOne : 1 < 2 ^ E.W := by omega
  have hTwo : 2 < 2 ^ E.W := by omega
  interval_cases count <;> refine ⟨?_, rfl, ?_, ?_⟩ <;>
    simp [hintFamilyCheckTail, runBlock, execInstr, h4, hRead, hintTruth,
      Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hTwo]

theorem hintFinalCheckCode_spec (E : RAMEnv) (state : RAMState) (parent count : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hCount : count ≤ 2) (hRead : state.mem (parent + 7) = count) :
    let out := runBlock hintFinalCheckCode E state
    out.pc = state.pc + 8 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (count = 1) ∧ out.regs 14 = parent + 16 := by
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have h7 : 7 < 2 ^ E.W := by omega
  have hAddr : parent + 7 < 2 ^ E.W := by omega
  have hPrep : let out := runBlock [.imm 4 7, .add 4 11 4] E sP
      out.pc = sP.pc + 2 ∧ out.mem = sP.mem ∧ out.regs 4 = parent + 7 ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, rfl, ?_, ?_⟩ <;> simp [runBlock, execInstr, hParentP, hContextP, Nat.mod_eq_of_lt h7, Nat.mod_eq_of_lt hAddr]
  generalize hQ : runBlock [.imm 4 7, .add 4 11 4] E sP = sQ at hPrep
  obtain ⟨hPcQ, hMemQ, h4, hContextQ⟩ := hPrep
  have hTail := hintFinalOneTail_spec E sQ (parent + 7) count (by omega) hCount h4 (by rw [hMemQ, hMemP]; exact hRead)
  generalize hT : runBlock hintFamilyCheckTail E sQ = out at hTail
  obtain ⟨hPcT, hMemT, hFlagT, hContextT⟩ := hTail
  have hRun : runBlock hintFinalCheckCode E state = out := by
    rw [hintFinalCheckCode, hintFinalCheckPrep, runBlock_append, runBlock_append, hP, hQ, hT]
  rw [hRun]
  exact ⟨by omega, hMemT.trans (hMemQ.trans hMemP), hFlagT, hContextT.trans hContextQ⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalRestoreCode_spec
#print axioms LinearSetReconciliation327.Main.hintFinalCheckCode_spec
end S_HintFinalReplayPrep20261120
section S_HintFinalReplay20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalReplayStmt : Stmt := .seq (.code hintFinalRestoreCode) hintReplayStmt
theorem hintFinalReplayStmt_len : hintFinalReplayStmt.len = 660 := rfl

theorem hintFinalReplayStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase maxR oldCount : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase) (hr : r ≤ maxR)
    (target : Fin (Nj ^ r)) (hS : hintFamilySuccesses G coords beta Nj r v hPublic.positive = {target})
    (hData : HintScanReadOnly G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hSaved : state.mem (parent + 8) = r)
    (hAt : At P base (hintFinalReplayStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 660) state (fun k out => k ≤ 7 * r + 30 + (hintScanBodyTime G r + 2) * Nj ^ r ∧
      out.regs 1 = 1 ∧
      HintScanSolution G coords beta Nj r (hintTupleSet (hintOdometerEnumeration Nj r hPublic.positive target)) v out.mem ∧
      (∀ i < r, out.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj target.val i) ∧
      HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem out.mem) := by
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hSpan := hPublic.fits.span
  obtain ⟨hRestoreAt, hReplayAt⟩ := At.seqStmt hAt
  change At P base hintFinalRestoreCode at hRestoreAt
  change At P (base + 7) (hintReplayStmt.compile (base + 7)) at hReplayAt
  have hRestore := hintFinalRestoreCode_spec E state parent outsideBase r (by omega)
    (hContext.trans hParent.symm) (by omega) (by omega) hData.outside_pointer hSaved
  generalize hR : runBlock hintFinalRestoreCode E state = sR at hRestore
  obtain ⟨hPcR, hMemR, hCtxR⟩ := hRestore
  have hRunR : (step P E)^[7] state = sR := by
    have hh := iterate_runBlock_of_at P E hintFinalRestoreCode state (by rwa [hPc])
      (by simp [hintFinalRestoreCode, hintScanParent, hintFinalRestoreTail, NoBranch, Instr.NoBranchI])
    rw [hR] at hh
    exact hh
  have hDataR : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v sR.mem := by
    rw [hMemR]; exact HintScanReadOnly.set_count hPublic hData r
  have hHeaderR : ∃ index, HintGaussHeader G index sR.mem := by
    obtain ⟨index, hHeader⟩ := hHeader
    refine ⟨index, ?_⟩
    intro i hi
    rw [hMemR, Function.update_of_ne (by omega : G.context + i ≠ outsideBase)]
    exact hHeader i hi
  have hFrameR : HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem sR.mem := by
    rw [hMemR]
    exact HintFinalFrame.of_controller (HintRowControllerFrame.set_count G parent outsideBase bitmapBase Nj maxR state.mem r)
  obtain ⟨_, kP, out, hRunP, hPcP, hCostP, hOne, hSolution, hArray, hCommon⟩ :=
    hintReplayStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v P E sR (base + 7)
      (hPublic.at_count r hr) target hS hDataR hHeaderR (hCtxR.trans hParent) hReplayAt (by omega)
  exact ⟨hPc, kP + 7, out, hintIterate_then (step P E) hRunR hRunP, by omega, by omega,
    hOne, hSolution, hArray, hCommon.readonly, hCommon.header, hCommon.context_value,
    hFrameR.trans (HintFinalFrame.of_scan hr hCommon.frame)⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalReplayStmt_sem
end S_HintFinalReplay20261120


