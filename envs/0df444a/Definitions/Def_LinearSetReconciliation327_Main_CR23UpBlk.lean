-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CR23UpBlk
-- name    : LinearSetReconciliation327_Main_CR23UpBlk
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-21T14:13:10.31237+00:00
-- url     : https://prove2.me/theorems/110c587a-7a95-4547-895b-b818b9b37bcf
-- title:
--   The fifth obstruction to Theorem 6.5's CR contract: `UpBlkSem`'s `forall Bw`, and the repaired per-block shape
-- statement:
--   The per-block contract `UpBlkSem` quantifies universally over the width $Bw$ of the window on which the environment's table must agree with the block's table.  At $Bw=0$ that premise is vacuous, so the contract asserts that the block toggles its payload in *every* environment of the correct word width.  For Proposition 2.3's toggle block this is false, and the failure is machine-checked here at the block's own instance (`cr23_upBlkSem_bw0_false`): in the all-zero table the prologue computes its countdown register as $r_6=\mathrm{det}\ r_1=0$, the countdown loop is skipped, no store is executed, and the payload is left exactly as it was, whereas the contract demands it XORed by a non-zero column of the CR matrix.  Consequently the hypothesis $h_{cr}:\texttt{UpBlkSem}\ S_{cr}\ E\ T_{cr}\ H_{cr}$ of the conjunct-6 assembly can never be discharged for 2.3's CR block: the $\forall Bw$ has to be repaired first.  The bundle also defines the repair — `UpBlkSemB`, the same contract with $Bw$ a parameter fixed by the caller, and `CrSemAt`, the exact contract the composite's CR block then has to meet: $Bw$ pinned to at least the CR table width, the table pinned to 2.3's `cr23DecDetAt`, the $\det$ base and payload base read from $r_{14}$ and $r_{15}$, a two-sided memory frame against the caller's own memory, and no register clauses.
-- source:
--   Theorem 6.5 (conjunct 6) and Proposition 2.3 of arXiv:2611.11409 (Liu--Xu--Yang--Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*); the contract `UpBlkSem` and the assembly `conj6_assembly`, and Proposition 2.3's program, table and sketch (`cr23*`).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_BlkContracts
import Definitions.Def_LinearSetReconciliation327_Main_CR23
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
/-!
# `CR23UpBlk`: the fifth obstruction to Theorem 6.5's `hCr`, machine-checked

`Definitions.Def_…_Conj6Asm` proves Theorem 6.5's conjunct 6 (`conj6_assembly`) conditional on two
hypotheses: `hUp` (Theorem 5.1's per-block contract) and `hCr : UpBlkSem Scr E Tcr Hcr` --- 2.3's
`CR` block.  Four obstructions to discharging `hCr` from 2.3's published export were already known
and machine-checked (`cr23_progUpPre_third`, `cr23_iTbl_r3`, `cr23_payStart_regs15`,
`cr23_payStart_regs1`).

This bundle adds a **fifth, independent, and fatal** one, which no export can circumvent:

* **`UpBlkSem` quantifies over `Bw`.**  At `Bw = 0` the table-agreement premise
  `∀ a < Bw, E.det (δ + a) = dt a` is *vacuous*, so the contract asserts that the block toggles the
  payload in **every** environment of width `E.W` --- in particular in the all-zero table.
  In that table 2.3's prologue computes its countdown register as `r6 = det r1 = 0`, the countdown
  loop is skipped, no store is ever executed, and the payload is left untouched.  The contract
  demands it toggled, so it fails: `cr23_upBlkSem_bw0_false`.

The refutation is at 2.3's *own* instance (`progUpStmt`, `cr23Sketch N t C`, any `T`, any width,
`1 ≤ t ≤ N`), so it is not an artefact of a toy block.  Since `UpBlkSem` is a hypothesis of
`conj6_assembly`, the assembly can never be applied with 2.3's `CR` block as `Scr`, whatever
statement 2.3's export is given: the `∀ Bw` has to be repaired first.

## The repair

`UpBlkSemB` below is `UpBlkSem` with `Bw` a **parameter** (`Bw` pinned by the caller to the block's
own table width) instead of a universally quantified variable, and `CrSemAt` is the shape the
composite's `CR` block then has to meet: `Bw` pinned, the table *pinned* to 2.3's
`cr23DecDetAt N t C β` (the window premise with an arbitrary `dt` cannot determine what the program
reads), the `det` base `δ` and payload base `β` taken from `r14`/`r15`, a two-sided frame against
the caller's own memory, and **no** register-preservation conjuncts (2.3's block legitimately writes
`r3`/`r4`, and the `CR` block is the last block of the composite, so the dispatcher needs nothing
preserved).

The remaining gap for 2.3's block is then only the `det`-relocation: 2.3's program indexes `det`
absolutely, so a block that reads its table from `det` base `r14` must relocate itself
(`r0 += r14`, `r1 := r14`, `r5 += r14`) before the published prologue; the run of the relocated
block is the `δ`-generalisation of `§R.4` of `Solutions/Sol_proposition_2_3.lean`.
-/

set_option autoImplicit false

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

noncomputable section

/-! ## 1. The all-zero table -/

/-- The table that answers `0` on every cell, at width `W`. -/
def zeroDet (W : ℕ) : RAMEnv := detEnv W (fun _ => 0)

@[simp] theorem zeroDet_det (W a : ℕ) : (zeroDet W).det a = 0 := rfl

@[simp] theorem zeroDet_W (W : ℕ) : (zeroDet W).W = W := rfl

/-! ## 2. `progUp` address by address -/

theorem progUp_unfold :
    progUp = progUpPre ++ [iJz r6 20] ++ progUpBody ++ [iJmp 10] ++ [iHalt] := rfl

theorem progUpPre_length : progUpPre.length = 10 := rfl

theorem progUpBody_length : progUpBody.length = 8 := rfl

theorem progUp_len : progUpStmt.len = 20 := rfl

theorem at_compile : At progUp 0 (progUpStmt.compile 0) := by
  intro r hr
  rw [show progUp = progUpStmt.compile 0 ++ [iHalt] from rfl]
  simpa using List.getElem?_append_left (l₁ := progUpStmt.compile 0) (l₂ := [iHalt])
    (by simpa using hr)

/-- The head piece of a right-nested concatenation sits at address `0`. -/
theorem At.headApp (l rest : Program) : At (l ++ rest) 0 l := by
  intro r hr
  simpa using List.getElem?_append_left (l₁ := l) (l₂ := rest) (by simpa using hr)

/-- Moving an `At` fact one piece to the left along a right-nested concatenation. -/
theorem At.tailApp {A B : Program} {a : ℕ} {l : List Instr} (h : At B a l) :
    At (A ++ B) (A.length + a) l := by
  intro r hr
  rw [show A.length + a + r = A.length + (a + r) from by omega]
  rw [List.getElem?_append_right (l₁ := A) (l₂ := B) (by omega)]
  rw [show A.length + (a + r) - A.length = a + r from by omega]
  exact h r hr

theorem at_pre : At progUp 0 progUpPre := by
  rw [progUp_unfold]
  exact At.headApp progUpPre _

theorem at_jz : At progUp 10 [iJz r6 20] := by
  have h : At (progUpPre ++ ([iJz r6 20] ++ (progUpBody ++ ([iJmp 10] ++ [iHalt])))) (10 + 0)
      [iJz r6 20] :=
    At.tailApp (A := progUpPre) (At.headApp [iJz r6 20] (progUpBody ++ ([iJmp 10] ++ [iHalt])))
  rw [progUp_unfold]
  simpa using h

theorem at_halt : At progUp 20 [iHalt] := by
  have h : At ((progUpPre ++ [iJz r6 20] ++ progUpBody ++ [iJmp 10]) ++ [iHalt]) (20 + 0)
      [iHalt] :=
    At.tailApp (A := progUpPre ++ [iJz r6 20] ++ progUpBody ++ [iJmp 10]) (At.headApp [iHalt] [])
  rw [progUp_unfold]
  simpa using h

theorem progUp_jz : progUp[10]? = some (iJz r6 20) := by
  have h := at_jz 0 (by simp)
  simpa using h

theorem progUp_halt : progUp[20]? = some iHalt := by
  have h := at_halt 0 (by simp)
  simpa using h

/-! ## 3. The prologue never branches and never stores -/

theorem noBranch_pre : NoBranch progUpPre := by
  simp [progUpPre, NoBranch, Instr.NoBranchI]

theorem pre_noBranchI {i : Instr} (hi : i ∈ progUpPre) : i.NoBranchI := by
  simp only [progUpPre, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem pre_mem {E : RAMEnv} {i : Instr} (hi : i ∈ progUpPre) (t : RAMState) :
    (execInstr i E t).mem = t.mem := by
  simp only [progUpPre, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem runBlock_mem_of (l : List Instr) (E : RAMEnv) (s : RAMState)
    (h : ∀ i ∈ l, ∀ t : RAMState, (execInstr i E t).mem = t.mem) :
    (runBlock l E s).mem = s.mem := by
  induction l generalizing s with
  | nil => rfl
  | cons i tl ih =>
      rw [runBlock_cons, ih (execInstr i E s) (fun j hj => h j (List.mem_cons_of_mem _ hj))]
      exact h i List.mem_cons_self s

theorem pre_step_pc {E : RAMEnv} {s : RAMState} {j : ℕ} (hj : j < 10) (hpc : s.pc = j) :
    (step progUp E s).pc = j + 1 := by
  have hjlen : j < progUpPre.length := by simpa [progUpPre_length] using hj
  have h1 : progUp[j]? = progUpPre[j]? := by simpa using at_pre j hjlen
  have h2 : progUpPre[j]? = some (progUpPre[j]) := List.getElem?_eq_getElem hjlen
  have hAt : progUp[s.pc]? = some (progUpPre[j]) := by rw [hpc, h1, h2]
  rw [step_eq_execInstr progUp E s _ hAt,
    execInstr_pc _ _ _ (pre_noBranchI (List.getElem_mem hjlen)), hpc]

theorem pre_step_mem {E : RAMEnv} {s : RAMState} {j : ℕ} (hj : j < 10) (hpc : s.pc = j) :
    (step progUp E s).mem = s.mem := by
  have hjlen : j < progUpPre.length := by simpa [progUpPre_length] using hj
  have h1 : progUp[j]? = progUpPre[j]? := by simpa using at_pre j hjlen
  have h2 : progUpPre[j]? = some (progUpPre[j]) := List.getElem?_eq_getElem hjlen
  have hAt : progUp[s.pc]? = some (progUpPre[j]) := by rw [hpc, h1, h2]
  rw [step_eq_execInstr progUp E s _ hAt]
  exact pre_mem (List.getElem_mem hjlen) s

/-! ## 4. The run of `progUp` in the all-zero table is memory-preserving -/

theorem pre_run {W : ℕ} {s : RAMState} (hpc : s.pc = 0) :
    (step progUp (zeroDet W))^[10] s = runBlock progUpPre (zeroDet W) s := by
  have hAt : At progUp s.pc progUpPre := by rw [hpc]; exact at_pre
  have h := iterate_runBlock_of_at progUp (zeroDet W) progUpPre s hAt noBranch_pre
  simp only [progUpPre_length] at h
  exact h

/-- **In the all-zero table the countdown register is `0`**, so the loop body is never entered. -/
theorem pre_r6 {W : ℕ} (s : RAMState) :
    (runBlock progUpPre (zeroDet W) s).regs r6 = 0 := by
  have h0 : (0 ||| 0 : ℕ) = 0 := by decide
  simp [progUpPre, runBlock_cons, runBlock_nil, execInstr, zeroDet, detEnv, h0]

theorem pre_mem_run {W : ℕ} (s : RAMState) :
    (runBlock progUpPre (zeroDet W) s).mem = s.mem :=
  runBlock_mem_of progUpPre (zeroDet W) s (fun i hi => pre_mem hi)

theorem pre_pc_run {W : ℕ} {s : RAMState} (hpc : s.pc = 0) :
    (runBlock progUpPre (zeroDet W) s).pc = 10 := by
  rw [runBlock_pc _ _ _ noBranch_pre, hpc, progUpPre_length]

theorem orbit_h11 {W : ℕ} {s : RAMState} (hpc : s.pc = 0) :
    (step progUp (zeroDet W))^[11] s
      = { runBlock progUpPre (zeroDet W) s with pc := 20 } := by
  rw [show (11 : ℕ) = 1 + 10 from rfl, Function.iterate_add_apply, pre_run hpc,
    Function.iterate_one]
  have hpc10 : (runBlock progUpPre (zeroDet W) s).pc = 10 := pre_pc_run hpc
  have hAt : progUp[(runBlock progUpPre (zeroDet W) s).pc]? = some (iJz r6 20) := by
    rw [hpc10]; exact progUp_jz
  rw [step_eq_execInstr progUp (zeroDet W) _ _ hAt, execInstr_jz, if_pos (pre_r6 s)]

theorem orbit_fix {W : ℕ} (s : RAMState) :
    step progUp (zeroDet W) { runBlock progUpPre (zeroDet W) s with pc := 20 }
      = { runBlock progUpPre (zeroDet W) s with pc := 20 } := by
  have hAt : progUp[({ runBlock progUpPre (zeroDet W) s with pc := 20 } : RAMState).pc]?
      = some iHalt := by
    show progUp[20]? = some iHalt
    exact progUp_halt
  rw [step_eq_execInstr progUp (zeroDet W) _ _ hAt]
  rfl

theorem orbit_fix_iter {W : ℕ} (s : RAMState) (j : ℕ) :
    (step progUp (zeroDet W))^[j] { runBlock progUpPre (zeroDet W) s with pc := 20 }
      = { runBlock progUpPre (zeroDet W) s with pc := 20 } := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, orbit_fix]

theorem orbit_low {W : ℕ} {s : RAMState} (hpc : s.pc = 0) :
    ∀ k ≤ 10, ((step progUp (zeroDet W))^[k] s).pc = k ∧
      ((step progUp (zeroDet W))^[k] s).mem = s.mem := by
  intro k
  induction k with
  | zero => intro _; exact ⟨hpc, rfl⟩
  | succ k ih =>
      intro hk
      have hk10 : k < 10 := by omega
      obtain ⟨hpck, hmemk⟩ := ih (by omega)
      have hstep := pre_step_pc (E := zeroDet W) (s := (step progUp (zeroDet W))^[k] s) hk10 hpck
      have hstepm := pre_step_mem (E := zeroDet W) (s := (step progUp (zeroDet W))^[k] s) hk10 hpck
      rw [Function.iterate_succ_apply']
      exact ⟨hstep, hstepm.trans hmemk⟩

/-- **Every state of the run in the all-zero table has the caller's memory.** -/
theorem orbit_mem {W : ℕ} {s : RAMState} (hpc : s.pc = 0) (k : ℕ) :
    ((step progUp (zeroDet W))^[k] s).mem = s.mem := by
  rcases Nat.lt_or_ge k 11 with h | h
  · exact (orbit_low hpc k (by omega)).2
  · have hsplit : k = (k - 11) + 11 := by omega
    rw [hsplit, Function.iterate_add_apply, orbit_h11 hpc, orbit_fix_iter]
    simpa using pre_mem_run (W := W) s

/-! ## 5. The toggle demanded by the contract is non-zero at some payload word -/

theorem packMem_pos {W M : ℕ} {z : Fin M → ZMod 2} {p : Fin M} (hp : z p = 1) :
    0 < packMem W z (p.val / W) := by
  unfold packMem
  have hterm : (if p.val / W = p.val / W ∧ z p = 1 then 2 ^ (p.val % W) else 0)
      = 2 ^ (p.val % W) := by rw [if_pos ⟨rfl, hp⟩]
  have hnn : ∀ x ∈ (univ : Finset (Fin M)),
      0 ≤ (if x.val / W = p.val / W ∧ z x = 1 then 2 ^ (x.val % W) else 0) := by
    intro x _; split <;> simp
  have hle : 2 ^ (p.val % W)
      ≤ ∑ x, (if x.val / W = p.val / W ∧ z x = 1 then 2 ^ (x.val % W) else 0) := by
    have h := Finset.single_le_sum (f := fun x : Fin M =>
      (if x.val / W = p.val / W ∧ z x = 1 then 2 ^ (x.val % W) else 0)) hnn (Finset.mem_univ p)
    rwa [hterm] at h
  exact lt_of_lt_of_le (Nat.two_pow_pos _) hle

theorem packMem_zero {W M : ℕ} (a : ℕ) :
    packMem W (0 : Fin M → ZMod 2) a = 0 := by
  simp [packMem]

theorem payMem_zero {W M β : ℕ} (a : ℕ) :
    payMem W β (0 : Fin M → ZMod 2) a = 0 := by
  simp [payMem, packMem]

theorem div_lt_wordsOf {W M : ℕ} (hW : 0 < W) {p : ℕ} (hp : p < M) (hM : 0 < M) :
    p / W < wordsOf W M := by
  unfold wordsOf
  have h1 : M + W - 1 = (M - 1) + W := by omega
  rw [h1, Nat.add_div_right _ hW]
  have h2 : p ≤ M - 1 := by omega
  exact Nat.lt_succ_of_le (Nat.div_le_div_right h2)

theorem cr23Lb_pos' {N : ℕ} (hN : 1 ≤ N) : 0 < cr23Lb N := by
  unfold cr23Lb
  exact Nat.clog_pos (by norm_num) (by omega)

theorem cr23D_pos' {N : ℕ} (hN : 1 ≤ N) : 0 < cr23D N := by
  have h2 : 0 < cr23Lb N := cr23Lb_pos' hN
  unfold cr23D
  positivity

theorem cr23M_pos' {t : ℕ} (ht : 1 ≤ t) : 0 < cr23M t := by
  unfold cr23M
  positivity

theorem cr23R_pos' {N t : ℕ} (hN : 1 ≤ N) (ht : 1 ≤ t) : 0 < cr23R N t := by
  unfold cr23R
  have h1 : 0 < cr23D N := cr23D_pos' hN
  have h2 : 0 < cr23M t := cr23M_pos' ht
  have h3 : 0 < cr23Lb N + 1 := by omega
  positivity

/-- The count-parity row of the check `(0, C v 0)` is `1` in column `v`: the column is non-zero. -/
theorem cr23Sketch_single_apply {N t : ℕ} (hN : 1 ≤ N) (ht : 1 ≤ t)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) :
    cr23Sketch N t C (Pi.single v 1)
        (cr23RowEquiv N t ⟨((⟨0, cr23D_pos' hN⟩ : Fin (cr23D N)), C v ⟨0, cr23D_pos' hN⟩),
          ⟨cr23Lb N, Nat.lt_succ_self _⟩⟩) = 1 := by
  rw [cr23Sketch, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  simp [cr23Matrix, cr23Entry]

theorem cr23Sketch_single_ne_zero {N t : ℕ} (hN : 1 ≤ N) (ht : 1 ≤ t)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (v : Fin N) :
    cr23Sketch N t C (Pi.single v 1) ≠ 0 := by
  intro hzero
  have h1 := cr23Sketch_single_apply hN ht C v
  have h2 := congrFun hzero (cr23RowEquiv N t
    ⟨((⟨0, cr23D_pos' hN⟩ : Fin (cr23D N)), C v ⟨0, cr23D_pos' hN⟩),
      ⟨cr23Lb N, Nat.lt_succ_self _⟩⟩)
  rw [h1] at h2
  exact one_ne_zero h2

/-! ## 6. The fifth obstruction -/

/-- **`UpBlkSem` is uninhabited at 2.3's own instance.**  `UpBlkSem` quantifies over `Bw`, so at
`Bw = 0` its table-agreement premise is vacuous and the contract promises a toggle in *every*
environment of the right width.  In the all-zero table the prologue's countdown register is
`r6 = det r1 = 0`, the loop is skipped, no store is executed, and the payload is left untouched ---
while the contract demands it toggled.  Hence no published 2.3 export can discharge
`conj6_assembly`'s `hCr`. -/
theorem cr23_upBlkSem_bw0_false (W N t : ℕ) (hW : 0 < W) (hN : 1 ≤ N) (ht : 1 ≤ t)
    (htN : t ≤ N) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (T : ℝ) :
    ¬ UpBlkSem progUpStmt (zeroDet W) T (cr23Sketch N t C) := by
  intro h
  have hpaypre : ∀ q < wordsOf (zeroDet W).W (cr23R N t),
      (initState (payMem W 0 (0 : Fin (cr23R N t) → ZMod 2)) 0 0 0).mem (0 + q)
        = packMem (zeroDet W).W (0 : Fin (cr23R N t) → ZMod 2) q := by
    intro q hq
    rw [zeroDet_W, Nat.zero_add]
    show payMem W 0 (0 : Fin (cr23R N t) → ZMod 2) q
      = packMem W (0 : Fin (cr23R N t) → ZMod 2) q
    rw [payMem, if_pos ⟨Nat.zero_le _, by simpa using hq⟩, Nat.sub_zero]
  obtain ⟨k, out, -, hstep, hpc, hpay, -⟩ :=
    h progUp 0 0 0 0 (fun _ => 0) (0 : Fin (cr23R N t) → ZMod 2) ⟨0, hN⟩
      (initState (payMem W 0 (0 : Fin (cr23R N t) → ZMod 2)) 0 0 0)
      at_compile rfl (by simp) (fun a ha => absurd ha (by omega)) rfl rfl rfl hpaypre
  have hmem : out.mem = (initState (payMem W 0 (0 : Fin (cr23R N t) → ZMod 2)) 0 0 0).mem := by
    rw [← hstep]
    exact orbit_mem rfl k
  let v : Fin N := ⟨0, hN⟩
  let p : Fin (cr23R N t) := cr23RowEquiv N t
    ⟨((⟨0, cr23D_pos' hN⟩ : Fin (cr23D N)), C v ⟨0, cr23D_pos' hN⟩),
      ⟨cr23Lb N, Nat.lt_succ_self _⟩⟩
  have hp1 : cr23Sketch N t C (Pi.single v 1) p = 1 := cr23Sketch_single_apply hN ht C v
  have hRpos : 0 < cr23R N t := cr23R_pos' hN ht
  have hq : p.val / W < wordsOf (zeroDet W).W (cr23R N t) := by
    simpa [zeroDet_W] using div_lt_wordsOf hW p.isLt hRpos
  have hq' : p.val / W < wordsOf W (cr23R N t) := by simpa [zeroDet_W] using hq
  have hcontra := hpay (p.val / W) hq
  simp only [zeroDet_W] at hcontra
  rw [Nat.zero_add, hmem] at hcontra
  have hzero : (initState (payMem W 0 (0 : Fin (cr23R N t) → ZMod 2)) 0 0 0).mem
      (p.val / W) = 0 := by
    show payMem W 0 (0 : Fin (cr23R N t) → ZMod 2) (p.val / W) = 0
    rw [payMem, if_pos ⟨Nat.zero_le _, by simpa using hq'⟩, Nat.sub_zero, packMem_zero]
  rw [hzero] at hcontra
  rw [show (0 : Fin (cr23R N t) → ZMod 2) + cr23Sketch N t C (Pi.single v 1)
      = cr23Sketch N t C (Pi.single v 1) from by funext x; simp] at hcontra
  have hpos : 0 < packMem W (cr23Sketch N t C (Pi.single v 1)) (p.val / W) := packMem_pos hp1
  exact (Nat.ne_of_gt hpos) hcontra.symm

/-! ## 7. The repaired shape -/

/-- `UpBlkSem` with `Bw` a **parameter** instead of a universally quantified variable: the window
premise is only available for the width the caller pins, which is what makes the contract true for a
block that reads its table (see `cr23_upBlkSem_bw0_false` for why the `∀ Bw` form is not). -/
def UpBlkSemB (Sup : Stmt) (E : RAMEnv) (T : ℝ) (Bw : ℕ) {N Ms : ℕ}
    (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)) : Prop :=
  ∀ (G : Program) (base δ β : ℕ) (dt : ℕ → ℕ) (y : Fin Ms → ZMod 2) (i : Fin N)
    (s : RAMState),
    At G base (Sup.compile base) → s.pc = base →
    δ + Bw ≤ 2 ^ E.W →
    (∀ a < Bw, E.det (δ + a) = dt a) →
    s.regs 14 = δ → s.regs 15 = β → s.regs 0 = i.val →
    (∀ q < wordsOf E.W Ms, s.mem (β + q) = packMem E.W y q) →
    ∃ (k : ℕ) (out : RAMState), (k : ℝ) ≤ T ∧ (step G E)^[k] s = out ∧
      out.pc = base + Sup.len ∧
      (∀ q < wordsOf E.W Ms, out.mem (β + q) = packMem E.W (y + Hs (Pi.single i 1)) q) ∧
      (∀ a, a < β ∨ β + wordsOf E.W Ms ≤ a → out.mem a = s.mem a) ∧
      out.regs 0 = s.regs 0 ∧ out.regs 1 = s.regs 1 ∧ out.regs 2 = s.regs 2 ∧
      out.regs 3 = s.regs 3 ∧ out.regs 4 = s.regs 4

/-- Every `UpBlkSem` gives the pinned form at every `Bw`. -/
theorem upBlkSem_to_upBlkSemB {Sup : Stmt} {E : RAMEnv} {T : ℝ} {N Ms : ℕ}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (h : UpBlkSem Sup E T Hs) (Bw : ℕ) : UpBlkSemB Sup E T Bw Hs :=
  fun G base δ β dt y i s hAt hpc hfit hdet => h G base δ β Bw dt y i s hAt hpc hfit hdet

/-- The width of 2.3's `det` table: every cell `progUp` reads is below `cr23Graph0 N`. -/
def cr23TblW (N : ℕ) : ℕ := cr23Graph0 N

/-- **The exact shape Theorem 6.5's conjunct 6 must consume for its `CR` block**: `Bw` pinned to
(at least) 2.3's table width, the table pinned to 2.3's `cr23DecDetAt`, `δ`/`β` taken from
`r14`/`r15`, a two-sided frame against the caller's memory, and no register-preservation conjuncts
(the `CR` block is last, and 2.3's block writes `r3`/`r4`). -/
def CrSemAt (Sup : Stmt) (E : RAMEnv) (T : ℝ) (Bw N t : ℕ)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) : Prop :=
  ∀ (G : Program) (base δ β : ℕ) (y : Fin (cr23R N t) → ZMod 2) (i : Fin N) (s : RAMState),
    At G base (Sup.compile base) → s.pc = base →
    δ + Bw ≤ 2 ^ E.W →
    (∀ a < Bw, E.det (δ + a) = cr23DecDetAt N t C β a) →
    s.regs 14 = δ → s.regs 15 = β → s.regs 0 = i.val →
    (∀ q < wordsOf E.W (cr23R N t), s.mem (β + q) = packMem E.W y q) →
    ∃ (k : ℕ) (out : RAMState), (k : ℝ) ≤ T ∧ (step G E)^[k] s = out ∧
      out.pc = base + Sup.len ∧
      (∀ q < wordsOf E.W (cr23R N t),
        out.mem (β + q) = packMem E.W (y + cr23Sketch N t C (Pi.single i 1)) q) ∧
      (∀ a, a < β ∨ β + wordsOf E.W (cr23R N t) ≤ a → out.mem a = s.mem a)

end

end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.cr23_upBlkSem_bw0_false


