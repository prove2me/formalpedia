-- Prove2me | Definitions.Def_TwoAgentSched_TotalTotal_OrderedPartitionGadget
-- name    : TwoAgentSched_TotalTotal_OrderedPartitionGadget
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T20:55:04.990498+00:00
-- url     : https://prove2.me/theorems/1e402548-3298-4152-878a-14959e02edbf
-- title:
--   Directly ordered even PARTITION gadget weights
-- statement:
--   For each source weight $w_i$ and a bit bound $N$, define two even tagged weights. With $K=4^n$, the pair has values
--
--   $$
--   2\bigl(K\,2^{N+i}+4^i\bigr),\qquad
--   2\bigl(K(2^{N+i}+w_i)+4^i\bigr).
--   $$
--
--   The output lists these two members consecutively for each source index, in index order. When the source weights are positive and below $2^N$, the increasing high offsets make this fixed pair-by-pair order strictly increasing; no sorting step is built into the definition.
--
--   This ordered gadget is an additional construction for the formal encoding reduction, not a construction stated in the cited paper. Its correctness and bit-size properties are separate theorems.
-- source:
--   Supporting construction for Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. The directly ordered even PARTITION gadget is an additional formalization construction.

import Mathlib

set_option autoImplicit false

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- Place both pair members in the high block indexed by their input position. -/
def orderedPairWeight {n : ℕ} (w : Fin n → ℕ) (N : ℕ) (i : Fin n) (b : Bool) : ℕ :=
  2 * (4 ^ n * (2 ^ (N + i.val) + if b then w i else 0) + 4 ^ i.val)

/-- The index of the source pair containing a position in the output list. -/
def orderedIndex {n : ℕ} (t : Fin (2 * n)) : Fin n := ⟨t.val / 2, by omega⟩

/-- Even output positions hold the unweighted member, odd positions the
    weight-carrying member. -/
def orderedIsHeavy {n : ℕ} (t : Fin (2 * n)) : Bool := decide (t.val % 2 = 1)

def orderedEnum {n : ℕ} (w : Fin n → ℕ) (N : ℕ) (t : Fin (2 * n)) : ℕ :=
  orderedPairWeight w N (orderedIndex t) (orderedIsHeavy t)


end TwoAgentSched.TotalTotal.StrictPartition


