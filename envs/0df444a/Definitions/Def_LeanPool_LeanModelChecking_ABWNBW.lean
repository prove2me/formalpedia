-- Prove2me | Definitions.Def_LeanPool_LeanModelChecking_ABWNBW
-- name    : LeanPool_LeanModelChecking_ABWNBW
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:43:35.786409+00:00
-- url     : https://prove2.me/theorems/a51020d3-3c73-4a1e-91bb-c6427bb2200f
-- title:
--   ABWNBW
-- statement:
--   Definitions and structural lemmas for ABWNBW, from György Kurucz; maintained by LeanPool contributors's pinned Formalizations of theorems related to model checking development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Order.KonigLemma
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanModelChecking
def ABW.toNBW {S Q} (A : ABW S Q) : NBW S := {
  Q := (Set Q) × (Set Q)
  q₀ := {({A.q₀}, ∅)}
  δ := fun (X, W) s (X', W') =>
    (∀ q ∈ X, PositiveBool.Sat X' (A.δ q s)) ∧ (
      (W = ∅ ∧ W' = X' \ A.F) ∨
      (W ≠ ∅ ∧ ∃ W'', (
        W' = W'' \ A.F ∧ W'' ⊆ X' ∧ (∀ q ∈ W, PositiveBool.Sat W'' (A.δ q s))
      ))
    )
  F := { (_, W) | W = ∅ }
}
def level {S Q} {A : ABW S Q} {w : Nat → S} {G : RunDAG A w} (i : Nat) : Set Q :=
  { q | (q, i) ∈ G.V }
structure LevelGraph where
  /-- The type of vertices on each level. -/
  level : Nat → Type
  /-- The edge relation between consecutive levels. -/
  E : (i : Nat) → level i → level (i + 1) → Prop
  /-- Every vertex on level `i + 1` has a predecessor on level `i`. -/
  ex_parent : ∀ i (v : level (i + 1)), ∃ (v' : level i), E i v' v
  /-- Each level is finite. -/
  fin : ∀ i, Finite (level i)
  /-- Each level is nonempty. -/
  nonempty : ∀ i, Nonempty (level i)
namespace LevelGraph
structure Path (G : LevelGraph) where
  /-- The vertex chosen on each level. -/
  f : ∀ i, G.level i
  /-- Consecutive chosen vertices are connected by an edge. -/
  p : ∀ i, G.E i (f i) (f (i + 1))
section
variable {G : LevelGraph}
noncomputable def ancestor {i j} (hij : i ≤ j) (v : G.level j) : G.level i :=
  if eq : i = j then
    eq ▸ v
  else
    ancestor (show i ≤ (j - 1) by omega)
      (G.ex_parent (j - 1) ((show (j - 1) + 1 = j by omega) ▸ v)).choose
end
end LevelGraph
open Classical in
/-- The canonical run of `ABW.toNBW A` extracted from a run DAG `G` of `A`: at each
level it records the set of live states together with the breakpoint obligation
set. -/
def helper.p {S Q} {A : ABW S Q} {w : Nat → S} {G : RunDAG A w} : Nat → (Set Q) × (Set Q)
| 0 => ({A.q₀}, ∅)
| i + 1 =>
  let X' := level (G := G) (i + 1)
  let (_, W) := p (G := G) i
  let W' :=
    if W = ∅ then
      X' \ A.F
    else
      { y' | y' ∉ A.F ∧
        ∃ y, y ∈ W ∧ (y, i) ∈ G.V ∧ (y', i + 1) ∈ G.V ∧ ((y, i), y') ∈ G.E }
  (X', W')
end LeanModelChecking


