-- Prove2me | Definitions.Def_CycleCliqueRamsey
-- name    : CycleCliqueRamsey
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:06.656656+00:00
-- url     : https://prove2.me/theorems/30ba19b8-0c20-4b15-bc8d-1fc9e44da953
-- statement:
--   For nonnegative integers m, n, and N, RamseyProperty(m,n,N) is the proposition that every simple graph G on N vertices contains a copy of the cycle graph Cₘ, or its complement contains a complete graph on n vertices; the latter alternative means that G has an independent set of n vertices. A copy is given by an injective map preserving edges, so the cycle need not be induced. Here Cₘ is the usual cycle for m ≥ 3, while C₀ and C₁ have no edges and C₂ is a single edge. The cycle–clique Ramsey number cycleCliqueRamsey(m,n) is defined as the infimum, in the nonnegative integers, of all N satisfying this property: the least such N when this set is nonempty, with value zero under the empty-set infimum convention. These are definitions, with no positivity restrictions on the parameters.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CycleCliqueRamsey.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CycleCliqueRamsey.lean; bytes 16..339
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

 

namespace CycleClique
open scoped SimpleGraph

 

def RamseyProperty (m n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    SimpleGraph.cycleGraph m ⊑ G ∨ (⊤ : SimpleGraph (Fin n)) ⊑ Gᶜ

 

noncomputable def cycleCliqueRamsey (m n : ℕ) : ℕ :=
  sInf {N : ℕ | RamseyProperty m n N}

 



end CycleClique
end OAI


