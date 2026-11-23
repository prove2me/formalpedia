-- Prove2me | Definitions.Def_DetANN_Supplement_GreedyExact
-- name    : DetANN_Supplement_GreedyExact
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:52:04.755058+00:00
-- url     : https://prove2.me/theorems/f5799ad2-3289-48c8-8440-812f2e60dd18
-- title:
--   Exact control-flow and sign-layout API for the greedy loop of `pre`
-- statement:
--   This module exposes the exact instruction-level interface of the greedy sign loop in the construction program $\mathrm{pre}(q,o)$ of Theorem 3.2. It includes the transitions at offsets $188$–$205$, the updates of the two sign trials, the sign-memory layout under `setSignAt`, and the invariant `GreedyCtx` consisting of all pointers, constants, Sylvester columns, difference table, and factorial table read by `EVAL`.
--
--   At iteration $kk<L2^k$, the program writes $+1$ at sign $kk$, evaluates the conditional potential, writes $-1$, evaluates again, and keeps the smaller value (with ties resolved in favor of $+1$). After all $L2^k$ signs it writes $L$ to integer cell $0$ and halts. The module records these facts for an arbitrary program in which `pre` is embedded.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission, §6.3, pp.15–16 and the construction program for Theorem 3.2 (definition DetANN_Supplement_PreProg). Exact reusable support extracted from the accepted proof of DetANN.Supplement.theorem_3_2.

import Mathlib
import Definitions.Def_DetANN_HPIMBSP
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMBalProg
import Definitions.Def_DetANN_Supplement_EvProg
import Definitions.Def_DetANN_Supplement_PreProg
import Definitions.Def_DetANN_SignChoice
import Definitions.Def_DetANN_Supplement_Greedy
import Definitions.Def_DetANN_Supplement_PreDedup
import Definitions.Def_DetANN_Sylvester

open PNormReg PNormRegLib DetANN SmaleNinth

namespace DetANN.Supplement.Thm32

lemma greedy_RAMStep_eq {R : RAMProgram} {s : RAMConfig} {i : RAMInstr} (h : R[s.pc]? = some i) :
    RAMStep R s = coreExec i s := by
  simp only [RAMStep, h]
  cases i <;> rfl

lemma greedy_core_get {P : Program} {pc : ℕ} {i : RAMInstr} (h : P[pc]? = some (.core i)) :
    (coreProgram P)[pc]? = some i := by
  simp [coreProgram, List.getElem?_map, h]

lemma greedy_step_eq_exec (P : Program) (ω : ℕ → Bool) (s : State) (ins : Instr)
    (hh : s.halted = false) (h : P[s.core.pc]? = some ins) : step P ω s = exec ω ins s := by
  cases ins with
  | core i => simp [step, exec, hh, h, greedy_RAMStep_eq (greedy_core_get h)]
  | _ => simp [step, exec, hh, h]

lemma greedy_run_succ (P : Program) (s : State) (ω : ℕ → Bool) (n : ℕ) :
    run P s ω (n + 1) = run P (step P ω s) ω n := by
  simp [run, Function.iterate_succ_apply]

lemma greedy_run_zero (P : Program) (s : State) (ω : ℕ → Bool) : run P s ω 0 = s := rfl

lemma greedy_run_add (P : Program) (s : State) (ω : ℕ → Bool) (a b : ℕ) :
    run P s ω (a + b) = run P (run P s ω a) ω b := by
  simp only [run]; rw [add_comm, Function.iterate_add_apply]

lemma greedy_run_exec {P : Program} {s : State} {ω : ℕ → Bool} {n : ℕ} {ins : Instr}
    (hh : s.halted = false) (h : P[s.core.pc]? = some ins) :
    run P s ω (n + 1) = run P (exec ω ins s) ω n := by
  rw [greedy_run_succ, greedy_step_eq_exec P ω s ins hh h]

lemma greedy_run_exec_at {Q B : Program} {off i : ℕ} {ins : Instr} (hE : Embeds Q B off) {s : State}
    {ω : ℕ → Bool} {n : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + i)
    (hB : B[i]? = some ins) : run Q s ω (n + 1) = run Q (exec ω ins s) ω n :=
  greedy_run_exec hh (by rw [hpc]; exact hE i ins hB)

lemma greedy_cellsWritten_add (P : Program) (s : State) (a b : ℕ) :
    cellsWritten P s (a + b) = cellsWritten P s a ∪ cellsWritten P (run P s detTape a) b := by
  ext c
  simp only [cellsWritten, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, hc⟩
    by_cases hia : i < a
    · exact Or.inl ⟨i, hia, hc⟩
    · refine Or.inr ⟨i - a, by omega, ?_⟩
      rw [← greedy_run_add, Nat.add_sub_cancel' (by omega)]; exact hc
  · rintro (⟨i, hi, hc⟩ | ⟨i, hi, hc⟩)
    · exact ⟨i, by omega, hc⟩
    · exact ⟨a + i, by omega, by rw [greedy_run_add]; exact hc⟩

lemma greedy_cellsWritten_zero (P : Program) (s : State) : cellsWritten P s 0 = ∅ := by
  simp [cellsWritten]

def greedy_wcell (ins : Instr) (s : State) : Option (Bool × ℤ) :=
  match ins with
  | .core (.store q _) => some (true, s.core.ptrs q)
  | .integerStore a _ => some (false, s.core.ptrs a)
  | _ => none

lemma greedy_cw_exec_at {Q B : Program} {off i : ℕ} {ins : Instr} (hE : Embeds Q B off) {s : State}
    {n : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + i) (hB : B[i]? = some ins) :
    cellsWritten Q s (n + 1) = (greedy_wcell ins s).toFinset ∪ cellsWritten Q (exec detTape ins s) n := by
  have hQ : Q[s.core.pc]? = some ins := by rw [hpc]; exact hE i ins hB
  rw [show n + 1 = 1 + n by omega, greedy_cellsWritten_add]
  congr 1
  · simp only [cellsWritten, Finset.range_one, Finset.singleton_biUnion, greedy_run_zero, writtenCell, hh,
      Bool.false_eq_true, if_false, hQ]
    cases ins with
    | core i => cases i <;> rfl
    | _ => rfl
  · rw [greedy_run_succ, greedy_run_zero, greedy_step_eq_exec Q detTape s ins hh hQ]

lemma greedy_cw_zero (Q : Program) (s : State) : cellsWritten Q s 0 = ∅ := greedy_cellsWritten_zero Q s

lemma greedy_embeds_app_right {Q A B : Program} {o : ℕ} (h : Embeds Q (A ++ B) o) :
    Embeds Q B (o + A.length) := by
  intro i x hx
  have := h (A.length + i) x (by rw [List.getElem?_append_right (by omega)]; simpa using hx)
  rwa [← Nat.add_assoc] at this

lemma greedy_embeds_app_left {Q A B : Program} {o : ℕ} (h : Embeds Q (A ++ B) o) : Embeds Q A o := by
  intro i x hx
  exact h i x (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1]; exact hx)

lemma greedy_run_exec_seg {Q B : Program} {off c n i : ℕ} {ins : Instr} (hE : Embeds Q B (off + c))
    {s : State} {ω : ℕ → Bool} {k : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + n)
    (hn : i + c = n) (hB : B[i]? = some ins) : run Q s ω (k + 1) = run Q (exec ω ins s) ω k :=
  greedy_run_exec_at hE hh (by rw [hpc]; omega) hB

lemma greedy_cw_exec_seg {Q B : Program} {off c n i : ℕ} {ins : Instr} (hE : Embeds Q B (off + c))
    {s : State} {k : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + n) (hn : i + c = n)
    (hB : B[i]? = some ins) :
    cellsWritten Q s (k + 1) = (greedy_wcell ins s).toFinset ∪ cellsWritten Q (exec detTape ins s) k :=
  greedy_cw_exec_at hE hh (by rw [hpc]; omega) hB

lemma greedy_len_preA (q : ℚ) (off : ℕ) : (preA q off).length = 41 := rfl
lemma greedy_len_preB0 (q : ℚ) (off : ℕ) : (preB0 q off).length = 51 := rfl
lemma greedy_len_preB1 (q : ℚ) (off : ℕ) : (preB1 q off).length = 73 := rfl

lemma greedy_emb_preB {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB0 q off ++ preB1 q off ++ preB2 q off ++ preB3 q off ++ preB4 q off ++ preB5 q off ++ preB6 q off) (off + 64) := by
  have h := greedy_embeds_app_right hE
  simpa only [List.length_append, greedy_len_preA, show (fw (off + 41)).length = 23 from rfl,
    Nat.add_assoc, Nat.reduceAdd] using h

lemma greedy_emb_preB2 {Q : Program} {q : ℚ} {off : ℕ} (hE : Embeds Q (pre q off) off) :
    Embeds Q (preB2 q off) (off + 188) := by
  have h := greedy_embeds_app_right (greedy_embeds_app_left (greedy_embeds_app_left (greedy_embeds_app_left (greedy_embeds_app_left (greedy_emb_preB hE)))))
  simpa only [List.length_append, greedy_len_preB0, greedy_len_preB1, Nat.add_assoc, Nat.reduceAdd] using h

lemma greedy_g_init (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 188) (hh : s.halted = false) :
    (run Q s detTape 1).core.pc = off + 189 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs 48 = 0 ∧
      (∀ x, x ≠ 48 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ := by
  have hS := greedy_emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh ⊢
  subst hh
  rw [hpc]
  (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [greedy_run_zero, greedy_cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, rfl, (by simp)⟩

lemma greedy_g_call (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 189) (hh : s.halted = false)
    (hb0 : s.core.ptrs 48 < s.core.ptrs 47) :
    (run Q s detTape 5).core.pc = off + 206 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 49 = s.core.ptrs 15 - s.core.ptrs 48 ∧
      (run Q s detTape 5).core.ptrs 50 = 0 ∧
      (∀ x, x ≠ 49 → x ≠ 50 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs = s.core.regs ∧
      (run Q s detTape 5).core.mem (s.core.ptrs 15 - s.core.ptrs 48) = s.core.regs 7 ∧
      (∀ z, z ≠ s.core.ptrs 15 - s.core.ptrs 48 → (run Q s detTape 5).core.mem z = s.core.mem z) ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      ∀ c ∈ cellsWritten Q s 5, c = (true, s.core.ptrs 15 - s.core.ptrs 48) := by
  have hS := greedy_emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [greedy_run_zero, greedy_cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _ _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma greedy_g_done (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 189) (hh : s.halted = false)
    (hb0 : s.core.ptrs 47 ≤ s.core.ptrs 48) :
    (run Q s detTape 2).core.pc = off + 205 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory (s.core.ptrs 0) = s.core.ptrs 14 ∧
      (∀ z, z ≠ s.core.ptrs 0 → (run Q s detTape 2).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      ∀ c ∈ cellsWritten Q s 2, c = (false, s.core.ptrs 0) := by
  have hS := greedy_emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [greedy_run_zero, greedy_cw_zero]
  exact ⟨rfl, rfl, rfl, rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma greedy_r0 (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 194) (hh : s.halted = false) :
    (run Q s detTape 4).core.pc = off + 206 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs 50 = 1 ∧
      (∀ x, x ≠ 50 → (run Q s detTape 4).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 4).core.regs 12 = (s.core.regs 13 + s.core.regs 6) ∧
      (∀ x, x ≠ 12 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧
      (run Q s detTape 4).core.mem (s.core.ptrs 49) = s.core.regs 8 ∧
      (∀ z, z ≠ s.core.ptrs 49 → (run Q s detTape 4).core.mem z = s.core.mem z) ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      ∀ c ∈ cellsWritten Q s 4, c = (true, s.core.ptrs 49) := by
  have hS := greedy_emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh ⊢
  subst hh
  rw [hpc]
  (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [greedy_run_zero, greedy_cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma greedy_r1_set (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 198) (hh : s.halted = false)
    (hb0 : (s.core.regs 12 - s.core.regs 13) ≤ 0) :
    (run Q s detTape 5).core.pc = off + 189 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 48 = s.core.ptrs 48 + 1 ∧
      (∀ x, x ≠ 48 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs 2 = (s.core.regs 12 - s.core.regs 13) ∧
      (∀ x, x ≠ 2 → (run Q s detTape 5).core.regs x = s.core.regs x) ∧
      (run Q s detTape 5).core.mem (s.core.ptrs 49) = s.core.regs 7 ∧
      (∀ z, z ≠ s.core.ptrs 49 → (run Q s detTape 5).core.mem z = s.core.mem z) ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      ∀ c ∈ cellsWritten Q s 5, c = (true, s.core.ptrs 49) := by
  have hS := greedy_emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [greedy_run_zero, greedy_cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro z _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, (by intro c hc; simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc; subst hc; simp; try omega)⟩

lemma greedy_r1_keep (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 198) (hh : s.halted = false)
    (hb0 : ¬ (s.core.regs 12 - s.core.regs 13) ≤ 0) :
    (run Q s detTape 5).core.pc = off + 189 ∧
      (run Q s detTape 5).halted = false ∧
      (run Q s detTape 5).core.ptrs 48 = s.core.ptrs 48 + 1 ∧
      (∀ x, x ≠ 48 → (run Q s detTape 5).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 5).core.regs 2 = (s.core.regs 12 - s.core.regs 13) ∧
      (∀ x, x ≠ 2 → (run Q s detTape 5).core.regs x = s.core.regs x) ∧
      (run Q s detTape 5).core.mem = s.core.mem ∧
      (run Q s detTape 5).integerMemory = s.integerMemory ∧
      (run Q s detTape 5).work = s.work + 5 ∧
      cellsWritten Q s 5 = ∅ := by
  have hS := greedy_emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hb0 ⊢
  subst hh
  rw [hpc]
  (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg]); (rw [greedy_run_exec_seg hS rfl rfl rfl rfl, greedy_cw_exec_seg hS rfl rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, greedy_wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := first | assumption | omega) only [if_pos, if_neg])
  rw [greedy_run_zero, greedy_cw_zero]
  exact ⟨rfl, rfl, (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), (by (simp (disch := omega) only [Function.update_apply, if_pos, if_neg, if_true, if_false]; try ring_nf; try omega)), (by intro x _; simp (disch := omega) only [Function.update_apply, if_pos, if_neg]), rfl, rfl, rfl, (by simp)⟩

lemma greedy_pre_halt (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (s : State)
    (hpc : s.core.pc = off + 205) (hh : s.halted = false) :
    (run Q s detTape 1).halted = true ∧ (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 := by
  have hS := greedy_emb_preB2 hE
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh ⊢
  subst hh
  rw [hpc, greedy_run_exec_seg hS rfl rfl rfl rfl]
  simp [exec, greedy_run_zero]

lemma greedy_signsAt_set {mem mem' : ℤ → ℝ} {L k : ℕ} {ξ : Fin L → Fin (2 ^ k) → Bool} (kk : ℕ) (b : Bool)
    (hS : SignsAt mem L k ξ) (hw : mem' (-(2 ^ k : ℤ) - 1 - kk) = signOf b)
    (hfr : ∀ z, z ≠ -(2 ^ k : ℤ) - 1 - kk → mem' z = mem z) :
    SignsAt mem' L k (setSignAt kk b ξ) := by
  intro ℓ r
  unfold setSignAt
  by_cases h : (ℓ : ℕ) * 2 ^ k + r = kk
  · rw [if_pos h]
    have e : ((ℓ : ℤ) * 2 ^ k + r) = kk := by exact_mod_cast h
    rw [e]; exact hw
  · rw [if_neg h]
    have hne : -(2 ^ k : ℤ) - 1 - ((ℓ : ℤ) * 2 ^ k + r) ≠ -(2 ^ k : ℤ) - 1 - kk := by
      intro e
      apply h
      have : ((ℓ : ℤ) * 2 ^ k + r) = kk := by linarith
      exact_mod_cast this
    rw [hfr _ hne]; exact hS ℓ r

lemma greedy_signsAt_of {mem mem' : ℤ → ℝ} {L k : ℕ} {ξ : Fin L → Fin (2 ^ k) → Bool}
    (hS : SignsAt mem L k ξ) (hfr : ∀ z, z < 0 → mem' z = mem z) : SignsAt mem' L k ξ := by
  intro ℓ r
  rw [hfr _ (by
    have : (0 : ℤ) ≤ (ℓ : ℤ) * 2 ^ k + r := by positivity
    have : (0 : ℤ) < 2 ^ k := by positivity
    omega)]
  exact hS ℓ r

lemma greedy_setSignAt_twice {L d : ℕ} (kk : ℕ) (b b' : Bool) (ξ : Fin L → Fin d → Bool) :
    setSignAt kk b (setSignAt kk b' ξ) = setSignAt kk b ξ := by
  funext ℓ r; unfold setSignAt; split_ifs <;> rfl

/-- The data read by `EVAL`, held fixed by the greedy loop. -/
def GreedyCtx (k L p₀ : ℕ) (τ : ℝ) (l : List (EuclideanSpace ℝ (Fin (2 ^ k)))) (Hb Db t0 : ℤ)
    (s : State) : Prop :=
  s.core.ptrs 0 = 0 ∧ s.core.ptrs 1 = 1 ∧ s.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ) ∧ s.core.ptrs 14 = L ∧
  s.core.ptrs 15 = -((2 ^ k : ℕ) : ℤ) - 1 ∧ s.core.ptrs 24 = Hb ∧ s.core.ptrs 26 = Db ∧
  s.core.ptrs 27 = Db + ((l.length * 2 ^ k : ℕ) : ℤ) ∧ s.core.ptrs 36 = 2 * (p₀ : ℤ) ∧
  s.core.ptrs 37 = 2 * (p₀ : ℤ) + 1 ∧ s.core.ptrs 39 = 4 * (p₀ : ℤ) + 1 ∧ s.core.ptrs 40 = t0 ∧
  s.core.ptrs 41 = t0 + (4 * (p₀ : ℤ) + 1) ∧ s.core.ptrs 42 = t0 + 2 * (4 * (p₀ : ℤ) + 1) ∧
  s.core.ptrs 43 = t0 + 3 * (4 * (p₀ : ℤ) + 1) ∧
  s.core.ptrs 44 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + (2 * (p₀ : ℤ) + 1) ∧
  s.core.ptrs 45 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + 2 * (2 * (p₀ : ℤ) + 1) ∧
  s.core.ptrs 46 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + 3 * (2 * (p₀ : ℤ) + 1) ∧
  s.core.ptrs 47 = ((L * 2 ^ k : ℕ) : ℤ) ∧
  s.core.regs 5 = τ ∧ s.core.regs 6 = 0 ∧ s.core.regs 7 = 1 ∧ s.core.regs 8 = -1 ∧
  (∀ r j : Fin (2 ^ k), s.core.mem (Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ)) = sylvester k j r) ∧
  TableAt s.core.mem Db l ∧
  (∀ i : ℕ, i < 4 * p₀ + 1 → s.core.mem (t0 + i) = (i.factorial : ℝ))

/-- The pointers occurring in `GreedyCtx`. -/
def GreedyCritP (y : ℕ) : Prop :=
  y = 0 ∨ y = 1 ∨ y = 3 ∨ y = 14 ∨ y = 15 ∨ y = 24 ∨ y = 26 ∨ y = 27 ∨
  y = 36 ∨ y = 37 ∨ y = 39 ∨ y = 40 ∨ y = 41 ∨ y = 42 ∨ y = 43 ∨ y = 44 ∨
  y = 45 ∨ y = 46 ∨ y = 47

end DetANN.Supplement.Thm32


