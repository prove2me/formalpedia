-- Prove2me | Definitions.Def_r03_defs_adda565e91_r03_sp01_center_slot_factor_bridge_candidate_v1
-- name    : r03_defs_adda565e91_r03_sp01_center_slot_factor_bridge_candidate_v1
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:53:25.714151+00:00
-- url     : https://prove2.me/theorems/d9f14a30-d44c-487c-9f8e-2d386ea11381
-- title:
--   R03 candidate definition: r03 defs adda565e91 r03 sp01 center slot factor bridge candidate v1
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_adda565e91_r03_sp01_center_slot_factor_bridge_candidate_v1.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

set_option maxRecDepth 100000

/-- A center-slot certificate for a proposed center set.  The two slots over
an index i are assigned to two distinct non-center vertices, and both are
adjacent to the center indexed by i.  This is an explicit integral
capacity-two assignment; it is not a claim that Hall's inequalities always
have a solution. -/
def R03SP01CenterSlotCertificate
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ n : Nat,
    ∃ eC : Fin n ≃ (↑C : Set V),
    ∃ eL : (Fin n × Fin 2) ≃ ((↑C : Set V)ᶜ : Set V),
      ∀ i : Fin n, ∀ j : Fin 2,
        G.Adj (eL (i, j) : V) (eC i : V)

def R03SP01CenterSlotCertificateAt
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V)
    (n : Nat) (eC : Fin n ≃ (↑C : Set V)) : Prop :=
  ∃ eL : (Fin n × Fin 2) ≃ ((↑C : Set V)ᶜ : Set V),
    ∀ i : Fin n, ∀ j : Fin 2,
      G.Adj (eL (i, j) : V) (eC i : V)

/-- Hall's condition for assigning complementary vertices to two slots over
an enumerated center set. -/
def R03SP01CenterSlotHallCondition
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V)
    [DecidableEq V] [DecidableRel G.Adj]
    (n : Nat) (eC : Fin n ≃ (↑C : Set V)) : Prop :=
  ∀ A : Finset ((↑C : Set V)ᶜ : Set V),
    A.card ≤ (Finset.univ.filter (fun b : Fin n × Fin 2 =>
      ∃ a ∈ A, G.Adj (a : V) (eC b.1 : V))).card

end CubicP3Partition


