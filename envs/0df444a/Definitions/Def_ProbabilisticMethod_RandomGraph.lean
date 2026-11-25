-- Prove2me | Definitions.Def_ProbabilisticMethod_RandomGraph
-- name    : ProbabilisticMethod_RandomGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T20:59:30.408017+00:00
-- url     : https://prove2.me/theorems/7acbf51e-db16-4cf6-aae7-c77f8e385c3c
-- title:
--   Random Graph
-- statement:
--   Definitions and structural lemmas for Random Graph, from Brian Sanders (Egly443/lean-probabilistic-method; see pinned Apache-2.0 LICENSE and source headers)'s pinned The finite probabilistic method for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/RandomGraph.lean

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace Finset
variable {V : Type*} [DecidableEq V]
def pairs (s : Finset V) : Finset (Sym2 V) := {e ∈ s.sym2 | ¬e.IsDiag}
end Finset
namespace SimpleGraph
variable {V : Type*} [DecidableEq V]
def possibleEdges (V : Type*) [Fintype V] [DecidableEq V] : Finset (Sym2 V) :=
  (univ : Finset V).pairs
variable [Fintype V] {p : ℝ}
end SimpleGraph


