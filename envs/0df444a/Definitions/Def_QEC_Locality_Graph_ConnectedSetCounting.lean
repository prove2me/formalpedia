-- Prove2me | Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
-- name    : QEC_Locality_Graph_ConnectedSetCounting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:09:15.001611+00:00
-- url     : https://prove2.me/theorems/90d4d7b1-9dc2-4d93-903f-015204c10fe0
-- title:
--   Connected Set Counting
-- statement:
--   Definitions and structural lemmas for Connected Set Counting, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/ConnectedSetCounting.lean

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
set_option autoImplicit false
noncomputable section
namespace QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
def next (G : SimpleGraph V) (r : V) : Finset V := by
  classical
  exact insert r (Finset.univ.filter (G.Adj r))
def traces (G : SimpleGraph V) (r : V) : Nat → Finset (List V)
  | 0 => {[r]}
  | n+1 => (next G r).biUnion fun w => (traces G w n).image (List.cons r)
def rooted (G : SimpleGraph V) (r : V) (m : Nat) : Finset (Finset V) := by
  classical
  exact Finset.univ.powerset.filter fun A =>
    r ∈ A ∧ A.card = m ∧ (G.induce (A : Set V)).Connected
def anchored (G : SimpleGraph V) (R : Finset V) (m : Nat) : Finset (Finset V) := by
  classical
  exact Finset.univ.powerset.filter fun A =>
    A.card = m ∧ (G.induce (A : Set V)).Connected ∧ (A ∩ R).Nonempty
end QEC.Locality.ConnectedSetCounting


