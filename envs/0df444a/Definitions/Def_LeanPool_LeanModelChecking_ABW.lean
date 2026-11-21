-- Prove2me | Definitions.Def_LeanPool_LeanModelChecking_ABW
-- name    : LeanPool_LeanModelChecking_ABW
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:43:16.300876+00:00
-- url     : https://prove2.me/theorems/f4b2667e-0452-4d4b-89e2-2cd11d68a862
-- title:
--   ABW
-- statement:
--   Definitions and structural lemmas for ABW, from György Kurucz; maintained by LeanPool contributors's pinned Formalizations of theorems related to model checking development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABW.lean

module
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanModelChecking
inductive PositiveBool (Q : Type) where
| atom (q : Q)
| true
| false
| and (ψ₁ ψ₂ : PositiveBool Q)
| or (ψ₁ ψ₂ : PositiveBool Q)
def PositiveBool.Sat {Q} (Y : Set Q) : PositiveBool Q → Prop
| atom q => q ∈ Y
| true => True
| false => False
| and ψ₁ ψ₂ => Sat Y ψ₁ ∧ Sat Y ψ₂
| or ψ₁ ψ₂ => Sat Y ψ₁ ∨ Sat Y ψ₂
structure ABW (S Q : Type) where
  /-- The initial state. -/
  q₀ : Q
  /-- The transition function, mapping a state and a letter to a positive Boolean
  formula over the successor states. -/
  δ : Q → S → PositiveBool Q
  /-- The set of accepting (final) states. -/
  F : Set Q
structure DAG.Base Q where
  /-- The set of vertices, each a state paired with a level. -/
  V : Set (Q × ℕ)
  /-- The set of edges, each from a state/level pair to a successor state. -/
  E : Set ((Q × ℕ) × Q)
structure DAG Q extends DAG.Base Q where
  /-- Every edge starts at a vertex of `V` and ends at a vertex on the next level. -/
  edge_closure : ∀ e ∈ E, e.1 ∈ V ∧ (e.2, e.1.2 + 1) ∈ V
def DAG.path {Q} (G : DAG Q) (p : ℕ → Q) :=
  ∃ n, ∀ i, ((p i, n + i), p (i + 1)) ∈ G.E
structure RunDAG {S Q} (A : ABW S Q) (w : ℕ → S) extends DAG Q where
  /-- The initial state sits at the root (level `0`). -/
  p_root : (A.q₀, 0) ∈ V
  /-- Each vertex has a set of successors satisfying its transition formula. -/
  p_sat :
    ∀ v ∈ V, let (q, i) := v;
    ∃ Y,
    PositiveBool.Sat Y (A.δ q (w i)) ∧
    {(q, i)} ×ˢ Y ⊆ E
def RunDAG.accepting {S Q} {A : ABW S Q} {w : ℕ → S} (G : RunDAG A w) :=
  ∀ p, G.path p → ∀ i, ∃ j ≥ i, p j ∈ A.F
def ABW.language {S Q} (A : ABW S Q) (w : Nat → S) :=
  ∃ (G : RunDAG A w), G.accepting
end LeanModelChecking


