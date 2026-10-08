-- Prove2me | Definitions.Def_SeymourSecondNeighborhood
-- name    : SeymourSecondNeighborhood
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:19.731038+00:00
-- url     : https://prove2.me/theorems/ba84c4b6-b74f-405d-9455-3ba1a955cdf2
-- statement:
--   A relation r on a type V is IsOriented when it is loopless (no v satisfies r v v) and asymmetric (r u v implies not r v u), so r behaves like the arc relation of an oriented graph. For a finite type V with decidable equality, firstNeighbors(r,v) is the finite set of vertices w with r v w, the out-neighbors of v. secondNeighbors(r,v) is the finite set of vertices w such that w differs from v, r v w does not hold, and there is some u with r v u and r u w; these are the vertices reachable by a directed path of length two that are not v itself or a first neighbor. A vertex v is a GoodVertex for r when the number of first neighbors is at most the number of second neighbors, that is |firstNeighbors(r,v)| ≤ |secondNeighbors(r,v)|. The block only introduces these definitions, together with an assumption that V is nonempty, and states no theorem or conjecture about the existence of good vertices.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SeymourSecondNeighborhood.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SeymourSecondNeighborhood.lean; bytes 67..762
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Union

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*}

structure IsOriented (r : V → V → Prop) : Prop where
  loopless : ∀ v, ¬ r v v
  asymmetric : ∀ {u v}, r u v → ¬ r v u

variable [Fintype V] [DecidableEq V]

noncomputable section

def firstNeighbors (r : V → V → Prop) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (r v)

def secondNeighbors (r : V → V → Prop) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w =>
    w ≠ v ∧ ¬ r v w ∧ ∃ u, r v u ∧ r u w)

def GoodVertex (r : V → V → Prop) (v : V) : Prop :=
  (firstNeighbors r v).card ≤ (secondNeighbors r v).card

end

variable [Nonempty V]



end SeymourSecondNeighborhood
end OAI


