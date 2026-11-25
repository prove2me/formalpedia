-- Prove2me | Definitions.Def_SinkReset_Basic
-- name    : SinkReset_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:33:34.043981+00:00
-- url     : https://prove2.me/theorems/d935f465-6599-413f-b386-ad5c071aff86
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Ben Keene (benkeene/sink-reset-thresholds; see pinned Apache-2.0 LICENSE and source headers)'s pinned Sharp reset thresholds for bounded-response synchronization games with a sink development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Basic.lean

module
public import Mathlib
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SinkReset
def f (k n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (i + k - 1) / k
abbrev Letter (n : ℕ) := Fin n → Fin n
def act {n : ℕ} (w : List (Letter n)) (q : Fin n) : Fin n := w.foldl (fun q a => a q) q
structure Automaton (n : ℕ) [NeZero n] where
  /-- The alphabet. -/
  letters : Set (Letter n)
  /-- Every letter fixes the sink `0`. -/
  sink_fixed : ∀ a ∈ letters, a 0 = 0
def Automaton.IsWord {n : ℕ} [NeZero n] (A : Automaton n) (w : List (Letter n)) : Prop :=
  ∀ a ∈ w, a ∈ A.letters
def Automaton.IsReset {n : ℕ} [NeZero n] (A : Automaton n) (w : List (Letter n)) : Prop :=
  A.IsWord w ∧ ∀ q, act w q = 0
inductive Automaton.AliceWins {n : ℕ} [NeZero n] (A : Automaton n) (k : ℕ) : Finset (Fin n) → Prop
  | reset (S : Finset (Fin n)) (h : ∀ q ∈ S, q = 0) : A.AliceWins k S
  | step (S : Finset (Fin n)) (a : Letter n) (ha : a ∈ A.letters)
      (h : ∀ u : List (Letter n), A.IsWord u → u.length < k →
        A.AliceWins k (S.image (act (a :: u)))) : A.AliceWins k S
def Automaton.IsAk {n : ℕ} [NeZero n] (A : Automaton n) (k : ℕ) : Prop :=
  A.AliceWins k Finset.univ
end SinkReset


