-- Prove2me | Definitions.Def_CliqueFreeLog
-- name    : CliqueFreeLog
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:04.076053+00:00
-- url     : https://prove2.me/theorems/746f3779-2f30-4c5a-b35a-b84091e3a777
-- statement:
--   For a simple graph G on a finite vertex set V, averageDegree(G) is the real number 2|E(G)|/|V|, where |E(G)| is the number of undirected edges and |V| is the number of vertices. For a nonempty vertex set this is the mean of the vertex degrees, with each edge contributing to both endpoints. No nonemptiness assumption is imposed: for the empty graph the definition gives zero, using real division by zero as defined in Lean.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CliqueFreeLog.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CliqueFreeLog.lean; bytes 16..220
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace CliqueFreeLog

noncomputable def averageDegree {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical
  exact 2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)



end CliqueFreeLog
end OAI


