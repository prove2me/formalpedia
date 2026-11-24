-- Prove2me | Definitions.Def_BalanceSpecificaton_OneSidedGraph
-- name    : BalanceSpecificaton_OneSidedGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:36:58.281963+00:00
-- url     : https://prove2.me/theorems/65b477ec-974a-4b54-9a00-9154dd907ab9
-- title:
--   One Sided Graph
-- statement:
--   Definitions and structural lemmas for One Sided Graph, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraph.lean

module
public import Definitions.Def_BalanceSpecificaton_OneSidedExample
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification.OneSidedExample
inductive Vertex where
  | q : ℕ → Vertex
  | p : ℕ → Vertex
  deriving DecidableEq
inductive Edge : Vertex → Alphabet → Vertex → Prop where
  | qa (n : ℕ) : Edge (.q n) a (.q (n + 1))
  | qb (n : ℕ) : Edge (.q n) b (.p n)
  | pa : Edge (.p 0) a (.q 0)
  | pc (n : ℕ) : Edge (.p n) c (.p 0)
  | pb (n : ℕ) : Edge (.p (n + 1)) b (.p n)
inductive Walk : Vertex → Word Alphabet → Vertex → Prop where
  | nil (s : Vertex) : Walk s [] s
  | cons {s t z : Vertex} {d : Alphabet} {w : Word Alphabet} :
      Edge s d t → Walk t w z → Walk s (d :: w) z
def edgeLabel : Vertex → Bool → Alphabet
  | .q _, false => a
  | .q _, true => b
  | .p 0, false => a
  | .p 0, true => c
  | .p (_ + 1), false => b
  | .p (_ + 1), true => c
def edgeTarget : Vertex → Bool → Vertex
  | .q n, false => .q (n + 1)
  | .q n, true => .p n
  | .p 0, false => .q 0
  | .p 0, true => .p 0
  | .p (n + 1), false => .p n
  | .p (_ + 1), true => .p 0
def runWord : Vertex → List Bool → Word Alphabet
  | _, [] => []
  | s, d :: ds => edgeLabel s d :: runWord (edgeTarget s d) ds
end BalanceSpecification.OneSidedExample


