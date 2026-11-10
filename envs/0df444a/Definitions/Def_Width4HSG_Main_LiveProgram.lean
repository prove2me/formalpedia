-- Prove2me | Definitions.Def_Width4HSG_Main_LiveProgram
-- name    : Width4HSG_Main_LiveProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:17:23.551121+00:00
-- url     : https://prove2.me/theorems/67e66d51-95d5-46a3-898e-1e7bec7527ab
-- title:
--   Definition 4.1 — three live states, rejection and fixed transitions
-- statement:
--   Three live states and an implicit absorbing rejection state are represented by Option (Fin 3). A transition either reads a fresh coordinate in increasing order or uses a fixed bit without reading input. Inputs contain exactly the free coordinates. Every final live state accepts. Evaluation, suffix density, forward reachability, and the number of colliding transition positions follow the original maps. A collision merges two distinct live states to a live state using an available branch; each position is counted once. Totality forbids rejection on available branches.
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, p. 19, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_FiniteCube

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

structure LiveProgram (n d : ℕ) where
  start : Fin 3
  read : Fin d → Option (Fin n)
  fixed : Fin d → Bool
  step : Fin d → Bool → Fin 3 → Option (Fin 3)
  ordered : ∀ (t u : Fin d) (i j : Fin n),
    read t = some i → read u = some j → t < u → i < j

def LiveProgram.free {n d : ℕ} (P : LiveProgram n d) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ t, P.read t = some i)

def LiveProgram.bit {n d : ℕ} (P : LiveProgram n d) (x : P.free → Bool) (i : Fin n) : Bool := by
  classical
  exact if hi : i ∈ P.free then x ⟨i, hi⟩ else false

def LiveProgram.runFrom {n d : ℕ} (P : LiveProgram n d) (a b : ℕ)
    (q : Option (Fin 3)) (x : P.free → Bool) : Option (Fin 3) :=
  ((List.finRange d).filter (fun t => a ≤ t.val ∧ t.val < b)).foldl
    (fun u t => u.bind (P.step t ((P.read t).elim (P.fixed t) (P.bit x)))) q

def LiveProgram.state {n d : ℕ} (P : LiveProgram n d)
    (x : P.free → Bool) (t : ℕ) : Option (Fin 3) :=
  P.runFrom 0 t (some P.start) x

def LiveProgram.eval {n d : ℕ} (P : LiveProgram n d) (x : P.free → Bool) : Bool :=
  (P.state x d).isSome

def LiveProgram.density {n d : ℕ} (P : LiveProgram n d) : ℝ :=
  average (fun x => indicator (P.eval x))

def LiveProgram.suffix {n d : ℕ} (P : LiveProgram n d) (t : ℕ) (q : Option (Fin 3)) : ℝ :=
  average (fun x => indicator (P.runFrom t d q x).isSome)

def LiveProgram.available {n d : ℕ} (P : LiveProgram n d) (t : Fin d) (b : Bool) : Prop :=
  P.read t ≠ none ∨ b = P.fixed t

def LiveProgram.colliding {n d : ℕ} (P : LiveProgram n d) (t : Fin d) : Prop :=
  ∃ b, P.available t b ∧ ∃ u v z : Fin 3,
    u ≠ v ∧ P.step t b u = some z ∧ P.step t b v = some z

def LiveProgram.collisions {n d : ℕ} (P : LiveProgram n d) (a b : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun t : Fin d => a ≤ t.val ∧ t.val < b ∧ P.colliding t)).card

def LiveProgram.reachable {n d : ℕ} (P : LiveProgram n d) (t : ℕ) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun u => ∃ x, P.state x t = some u)

def LiveProgram.Total {n d : ℕ} (P : LiveProgram n d) : Prop :=
  ∀ t b, P.available t b → ∀ u, (P.step t b u).isSome = true

end Width4HSG.Main


