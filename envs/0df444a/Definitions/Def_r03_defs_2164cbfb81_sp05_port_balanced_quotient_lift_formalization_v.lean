-- Prove2me | Definitions.Def_r03_defs_2164cbfb81_sp05_port_balanced_quotient_lift_formalization_v
-- name    : r03_defs_2164cbfb81_sp05_port_balanced_quotient_lift_formalization_v
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:20:37.729068+00:00
-- url     : https://prove2.me/theorems/935fc56f-2373-41a6-9d4f-55684e34ca80
-- title:
--   R03 P3-factor definition module: r03_defs_2164cbfb81_sp05_port_balanced_quotient_lift_formalization_v
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp05/sp05_port_balanced_quotient_lift_formalization_v1.lean; source SHA-256 1b17dce1207077544dcd17ef33d4aaa37486a28a3ac9d14883405116a1691579; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03PortBalancedLift

open CubicP3Partition

universe u v

variable {P : Type u} {V : Type v} [Fintype P] [Fintype V]

noncomputable section
open scoped Classical

/-- A port-labelled relation on the quotient vertices.  A relation edge records
which endpoint/port of each paired quotient vertex is used. -/
def PortRelation := P → Fin 2 → P → Fin 2 → Prop

/-- A port-balanced P3-factor of a paired quotient.  The two quotient edges at
one quotient centre use distinct ports. -/
structure PortBalancedFactor (R : PortRelation (P := P)) where
  blockCount : Nat
  place : (Fin blockCount × Fin 3) ≃ P
  leaf01Port : Fin blockCount → Fin 2
  center01Port : Fin blockCount → Fin 2
  center12Port : Fin blockCount → Fin 2
  leaf12Port : Fin blockCount → Fin 2
  edge01 : ∀ i, R (place (i, 0)) (leaf01Port i)
      (place (i, 1)) (center01Port i)
  edge12 : ∀ i, R (place (i, 1)) (center12Port i)
      (place (i, 2)) (leaf12Port i)
  center_ports_ne : ∀ i, center01Port i ≠ center12Port i

/-- The original graph data associated with a paired quotient. -/
structure PairedPortLift (G : SimpleGraph V) (R : PortRelation (P := P)) where
  pair : (P × Fin 2) ≃ V
  pair_edge : ∀ p, G.Adj (pair (p, 0)) (pair (p, 1))
  relation_edge : ∀ {p i q j}, R p i q j →
    G.Adj (pair (p, i)) (pair (q, j))

/-- The exact port relation obtained by contracting a supplied pairing of the
original vertices.  A quotient edge is present precisely when its two lifted
ports are adjacent in the original graph. -/
def contractedRelation (G : SimpleGraph V)
    (pair : (P × Fin 2) ≃ V) : PortRelation (P := P) :=
  fun p i q j => p ≠ q ∧ G.Adj (pair (p, i)) (pair (q, j))

/-- Package an actual paired quotient as a `PairedPortLift`; here the relation
edge proof is definitional because the relation is the contracted relation. -/
def contractedPairedPortLift (G : SimpleGraph V)
    (pair : (P × Fin 2) ≃ V)
    (pair_edge : ∀ p, G.Adj (pair (p, 0)) (pair (p, 1))) :
    PairedPortLift G (contractedRelation G pair) :=
  {
    pair := pair
    pair_edge := pair_edge
    relation_edge := by
      intro p i q j h
      exact h.2
  }

def portFlip (p : Fin 2) : Fin 2 :=
  if p = 0 then 1 else 0

def pairingGraph (pair : (P × Fin 2) ≃ V) : SimpleGraph V where
  Adj u v := ∃ p, (u = pair (p, 0) ∧ v = pair (p, 1)) ∨
    (u = pair (p, 1) ∧ v = pair (p, 0))
  symm := ⟨by
    intro u v h
    rcases h with ⟨p, h | h⟩
    · exact ⟨p, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨p, Or.inl ⟨h.2, h.1⟩⟩⟩
  loopless := ⟨by
    intro v h
    rcases h with ⟨p, h | h⟩
    · have hp := pair.injective (h.1.symm.trans h.2)
      exact Fin.zero_ne_one (congrArg Prod.snd hp)
    · have hp := pair.injective (h.1.symm.trans h.2)
      exact Fin.zero_ne_one (congrArg Prod.snd hp).symm⟩

def nonmatchingNeighborFinset (G : SimpleGraph V)
    (pair : (P × Fin 2) ≃ V) (p : P) (b : Fin 2) : Finset V :=
  (G.neighborFinset (pair (p, b))).erase (pair (p, portFlip b))

def contractedPortNeighborFinset (G : SimpleGraph V)
    (pair : (P × Fin 2) ≃ V) (p : P) (b : Fin 2) : Finset (P × Fin 2) :=
  Finset.univ.filter (fun x => contractedRelation G pair p b x.1 x.2)

def contractedHalfEdgeFinset (G : SimpleGraph V)
    (pair : (P × Fin 2) ≃ V) (p : P) :
    Finset (Σ b : Fin 2, P × Fin 2) :=
  (Finset.univ : Finset (Fin 2)).sigma
    (fun b => contractedPortNeighborFinset G pair p b)

def allContractedHalfEdgeFinset (G : SimpleGraph V)
    (pair : (P × Fin 2) ≃ V) :
    Finset (Σ p : P, Σ b : Fin 2, P × Fin 2) :=
  (Finset.univ : Finset P).sigma
    (fun p => contractedHalfEdgeFinset G pair p)

def reverseContractedHalfEdge :
    (Σ p : P, Σ b : Fin 2, P × Fin 2) →
      (Σ p : P, Σ b : Fin 2, P × Fin 2)
  | ⟨p, ⟨b, ⟨q, j⟩⟩⟩ => ⟨q, ⟨j, ⟨p, b⟩⟩⟩

def cycleBlockPlace (k : Nat) : (Fin k × Fin 3) ≃ Fin (3 * k) :=
  (finProdFinEquiv : Fin k × Fin 3 ≃ Fin (k * 3)).trans
    (finCongr (Nat.mul_comm k 3))

structure CycleTripleDecomposition (F : SimpleGraph V) where
  cycleCount : Nat
  cycleBlocks : Fin cycleCount → Nat
  place : (Σ c : Fin cycleCount, Fin (3 * cycleBlocks c)) ≃ V
  edge01 : ∀ (c : Fin cycleCount) (r : Fin (cycleBlocks c)),
    F.Adj
      (place ⟨c, cycleBlockPlace (cycleBlocks c) (r, 0)⟩)
      (place ⟨c, cycleBlockPlace (cycleBlocks c) (r, 1)⟩)
  edge12 : ∀ (c : Fin cycleCount) (r : Fin (cycleBlocks c)),
    F.Adj
      (place ⟨c, cycleBlockPlace (cycleBlocks c) (r, 1)⟩)
      (place ⟨c, cycleBlockPlace (cycleBlocks c) (r, 2)⟩)

def basePlace (G : SimpleGraph V)
    (R : PortRelation (P := P))
    (Q : PortBalancedFactor (P := P) R)
    (L : PairedPortLift (P := P) (V := V) G R)
    (x : (Fin Q.blockCount × Fin 2) × Fin 3) : V :=
  let i := x.1.1
  let t := x.1.2
  let j := x.2
  if t = 0 then
    if j = 0 then
      L.pair (Q.place (i, 0), portFlip (Q.leaf01Port i))
    else if j = 1 then
      L.pair (Q.place (i, 0), Q.leaf01Port i)
    else
      L.pair (Q.place (i, 1), Q.center01Port i)
  else
    if j = 0 then
      L.pair (Q.place (i, 1), Q.center12Port i)
    else if j = 1 then
      L.pair (Q.place (i, 2), Q.leaf12Port i)
    else
      L.pair (Q.place (i, 2), portFlip (Q.leaf12Port i))

end
end R03PortBalancedLift


