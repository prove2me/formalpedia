-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelTransducer
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelTransducer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:48.989189+00:00
-- url     : https://prove2.me/theorems/ecc7973e-0cb2-461a-bf5a-9c1bce76d506
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTransducer — Finite-state transducers and their machine semantics
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTransducer` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Machine declarations are moved from their original module without changing programs or resource
--   formulas. Higher computability-calculus theorems remain in the original facade.
--
--   **Contents.** The module is published as a whole: 14 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelTransducer`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/KernelTransducer.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Fintype.Option
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelZeroSpace

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTransducer` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Finite-state transducers and their machine semantics

Machine declarations are moved from their original module without changing programs or resource
formulas. Higher computability-calculus theorems remain in the original facade.
-/

namespace Turing.MultiTapeTM

/-- A finite-state transducer with input and output alphabet `Symbol` and states `Q`. In state `q`
on the symbol `a` it moves to `(step q a).1` and emits `(step q a).2`; at the end of the input it
emits `final q`. -/
public structure Transducer (Symbol Q : Type*) where
  /-- The initial state. -/
  q₀ : Q
  /-- The successor state and the emitted word on reading a symbol. -/
  step : Q → Symbol → Q × List Symbol
  /-- The word emitted at the end of the input. -/
  final : Q → List Symbol
  /-- At most two symbols are emitted per input symbol. -/
  length_step_le : ∀ q a, (step q a).2.length ≤ 2
  /-- At most two symbols are emitted at the end of the input. -/
  length_final_le : ∀ q, (final q).length ≤ 2

namespace Transducer

variable {Symbol Q : Type*} (τ : Transducer Symbol Q)

/-- The word `τ` emits on `w`, started in state `q`. -/
@[expose] public def run : Q → List Symbol → List Symbol
  | q, [] => τ.final q
  | q, a :: w => (τ.step q a).2 ++ run (τ.step q a).1 w

@[simp]
public lemma run_nil (q : Q) : τ.run q [] = τ.final q := rfl

@[simp]
public lemma run_cons (q : Q) (a : Symbol) (w : List Symbol) :
    τ.run q (a :: w) = (τ.step q a).2 ++ τ.run (τ.step q a).1 w := rfl

/-- `τ` as a machine without work tapes. Its states are the states of `τ`, a pending output
symbol, and whether the end of the input has been reached. -/
public def toTM : MultiTapeTM 0 Symbol (Q × Option Symbol × Bool) :=
  ofTr (τ.q₀, none, false) fun st inp _ =>
    match st with
    | (q, some b, fin) =>
      { inputTape := 0, workTapes := Fin.elim0, output := some b, state := some (q, none, fin) }
    | (_, none, true) =>
      { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
    | (q, none, false) =>
      match inp with
      | some a =>
        { inputTape := 1, workTapes := Fin.elim0, output := (τ.step q a).2.head?,
          state := some ((τ.step q a).1, (τ.step q a).2.tail.head?, false) }
      | none =>
        { inputTape := 0, workTapes := Fin.elim0, output := (τ.final q).head?,
          state := some (q, (τ.final q).tail.head?, true) }

variable {input : List Symbol}

/-- The configuration of `τ.toTM` in state `st` with the input head at `pos`, having emitted `o`. -/
def cfg (input : List Symbol) (st : Option (Q × Option Symbol × Bool))
    (pos : Fin (input.length + 2)) (o : List Symbol) :
    Cfg 0 Symbol (Q × Option Symbol × Bool) input :=
  ⟨st, pos, fun _ _ => none, fun _ => 0, o⟩

/-- A pending symbol is emitted. -/
lemma step_pending (q : Q) (b : Symbol) (fin : Bool) (pos : Fin (input.length + 2))
    (o : List Symbol) :
    τ.toTM.step (cfg input (some (q, some b, fin)) pos o) = cfg input (some (q, none, fin)) pos
      (o ++ [b]) := by
  rw [step_of_state rfl]
  refine Cfg.ext_zero_tapes ?_ ?_ ?_ <;> simp [cfg, toTM, Action.apply]

/-- After the end of the input, the machine halts. -/
lemma step_halt (q : Q) (pos : Fin (input.length + 2)) (o : List Symbol) :
    τ.toTM.step (cfg input (some (q, none, true)) pos o) = cfg input none pos o := by
  rw [step_of_state rfl]
  refine Cfg.ext_zero_tapes ?_ ?_ ?_ <;> simp [cfg, toTM, Action.apply]

/-- Flushing a possibly pending symbol takes at most one step. -/
lemma exists_runFrom_flush (q : Q) (p : Option Symbol) (fin : Bool)
    (pos : Fin (input.length + 2)) (o : List Symbol) :
    ∃ u ≤ 1, τ.toTM.runFrom (cfg input (some (q, p, fin)) pos o) u =
      cfg input (some (q, none, fin)) pos (o ++ p.toList) := by
  cases p with
  | none => exact ⟨0, Nat.zero_le _, by simp [runFrom]⟩
  | some b => exact ⟨1, le_rfl, by simp [runFrom, step_pending]⟩

/-- Reading the input symbol at position `i`. -/
lemma step_read (q : Q) {i : ℕ} (hi : i < input.length) (o : List Symbol) :
    τ.toTM.step (cfg input (some (q, none, false)) ⟨i + 1, by omega⟩ o) =
      cfg input (some ((τ.step q input[i]).1, (τ.step q input[i]).2.tail.head?, false))
        ⟨i + 1 + 1, by omega⟩ (o ++ (τ.step q input[i]).2.head?.toList) := by
  have hsym : (cfg input (some (q, none, false)) ⟨i + 1, by omega⟩ o).inputSymbol =
      some input[i] := inputSymbolInner i (by simp only [cfg]; omega) hi
  rw [step_of_state rfl, hsym]
  refine Cfg.ext_zero_tapes (by simp [cfg, toTM, Action.apply]) ?_
    (by simp [cfg, toTM, Action.apply])
  simp only [cfg, toTM, tr_ofTr, Action.apply]
  exact moveInputPos_pos_of_ne_right _ (by simp only; omega)

/-- Reaching the end of the input. -/
lemma step_end (q : Q) (o : List Symbol) :
    τ.toTM.step (cfg input (some (q, none, false)) ⟨input.length + 1, by omega⟩ o) =
      cfg input (some (q, (τ.final q).tail.head?, true)) ⟨input.length + 1, by omega⟩
        (o ++ (τ.final q).head?.toList) := by
  have hsym : (cfg input (some (q, none, false)) ⟨input.length + 1, by omega⟩ o).inputSymbol =
      none := inputSymbol_eq_none_of_boundary (.inr rfl)
  rw [step_of_state rfl, hsym]
  refine Cfg.ext_zero_tapes ?_ ?_ ?_ <;> simp [cfg, toTM, Action.apply]

/-- From input position `i` on, the machine halts within `2 * (input.length - i) + 3` steps,
having emitted what `τ` emits on the rest of the input. -/
lemma exists_runFrom_halt (q : Q) {i : ℕ} (hi : i ≤ input.length) (o : List Symbol) :
    ∃ u ≤ 2 * (input.length - i) + 3, ∃ pos,
      τ.toTM.runFrom (cfg input (some (q, none, false)) ⟨i + 1, by omega⟩ o) u =
        cfg input none pos (o ++ τ.run q (input.drop i)) := by
  obtain ⟨n, hn⟩ : ∃ n, input.length - i = n := ⟨_, rfl⟩
  induction n generalizing i q o with
  | zero =>
    obtain rfl : i = input.length := by omega
    obtain ⟨u, hu, hflush⟩ := τ.exists_runFrom_flush (input := input) q (τ.final q).tail.head?
      true ⟨input.length + 1, by omega⟩ (o ++ (τ.final q).head?.toList)
    refine ⟨1 + u + 1, by omega, ⟨input.length + 1, by omega⟩, ?_⟩
    rw [runFrom_add, runFrom_add, runFrom_one, runFrom_one, step_end, hflush, step_halt]
    rw [List.drop_length, run_nil, List.append_assoc, ← List.take_one, List.head?_tail,
      ← List.take_add_one, List.take_of_length_le (τ.length_final_le q)]
  | succ n ih =>
    have hi' : i < input.length := by omega
    obtain ⟨u₁, hu₁, hflush⟩ := τ.exists_runFrom_flush (input := input) (τ.step q input[i]).1
      (τ.step q input[i]).2.tail.head? false ⟨i + 1 + 1, by omega⟩
      (o ++ (τ.step q input[i]).2.head?.toList)
    obtain ⟨u₂, hu₂, pos, hrest⟩ := ih (τ.step q input[i]).1 (i := i + 1) (by omega)
      (o ++ (τ.step q input[i]).2) (by omega)
    refine ⟨1 + u₁ + u₂, by omega, pos, ?_⟩
    rw [runFrom_add, runFrom_add, runFrom_one, step_read _ _ hi', hflush,
      List.append_assoc, ← List.take_one, List.head?_tail, ← List.take_add_one,
      List.take_of_length_le (τ.length_step_le _ _), hrest,
      List.drop_eq_getElem_cons hi', run_cons, List.append_assoc]

/-- `τ.toTM` emits `τ.run τ.q₀ input` on `input`, in `2 * input.length + 3` steps and zero
space. -/
public theorem computesInTimeAndSpace_toTM (input : List Symbol) :
    τ.toTM.ComputesInTimeAndSpace input (τ.run τ.q₀ input) (2 * input.length + 3) 0 := by
  obtain ⟨u, hu, pos, hrun⟩ := τ.exists_runFrom_halt τ.q₀ (Nat.zero_le input.length) []
  have hinit : τ.toTM.initCfg input = cfg input (some (τ.q₀, none, false)) ⟨0 + 1, by omega⟩ [] :=
    Cfg.ext_zero_tapes rfl (Fin.ext (by simp [MultiTapeNTM.initCfg, Cfg.init, cfg])) rfl
  rw [← hinit, List.drop_zero, List.nil_append] at hrun
  have hhalt : (τ.toTM.runFrom (τ.toTM.initCfg input) u).Halted := by
    rw [hrun]
    rfl
  refine ⟨⟨u, hhalt, by rw [hrun]; rfl⟩, runsInTime_iff_halted.mpr ?_, by simp⟩
  rw [runFrom_eq_of_halt _ _ (by omega : u ≤ 2 * input.length + 3) hhalt]
  exact hhalt

/-- Followed by a rewind of the input head, `τ.toTM` emits `τ.run τ.q₀ input` tidily. -/
public theorem computesTidily (input : List Symbol) :
    (τ.toTM.seq (rewindInput Symbol)).ComputesTidilyInTimeAndSpace input (τ.run τ.q₀ input)
      (4 * input.length + 8) 0 :=
  TransformsTapes.mono (τ.computesInTimeAndSpace_toTM input).computesTidily_seq_rewindInput
    (by omega) le_rfl

end Transducer

end Turing.MultiTapeTM


