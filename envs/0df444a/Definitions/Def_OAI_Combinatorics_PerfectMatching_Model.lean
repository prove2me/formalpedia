-- Prove2me | Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
-- name    : OAI_Combinatorics_PerfectMatching_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:43:38.73977+00:00
-- url     : https://prove2.me/theorems/0114824c-1291-40f4-9b00-e398754bd50d
-- title:
--   Edge records with multiplicities for describing multigraphs by lists
-- statement:
--   This module introduces one elementary data type, used to describe a multigraph concretely as a finite list of numbers.
--
--   1. An *edge record* is a triple $(i,j,\mu)\in\mathbb{N}^3$. The numbers $i$ and $j$ (the fields `left` and `right`) are the labels of two vertices, and $\mu$ (the field `multiplicity`) is the number of parallel edges joining them. Equality of records is decidable, so lists of records can be searched and compared algorithmically.
--
--   The record imposes no conditions of its own. Requirements such as $i<j<n$ for a graph on the vertex labels $\{0,1,\dots,n-1\}$, or the absence of repeated vertex pairs, are imposed separately wherever lists of records serve as input. Records give an explicit, encodable description of a multigraph by vertex pairs and multiplicities. This complements the abstract loopless multigraphs used elsewhere in the development, whose edge type distinguishes parallel edges.
--
--   **Formalization Note** The structure is `OAI.BinaryMatching.Record` with fields `left`, `right`, `multiplicity : ℕ` and a derived `DecidableEq` instance. The module also contains an empty variable section for loopless graphs, which declares nothing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingEntropy

namespace OAI

universe u_1 u_2

namespace MatchingEntropy
namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
end LooplessGraph
end MatchingEntropy

namespace BinaryMatching
structure Record where
  left : ℕ
  right : ℕ
  multiplicity : ℕ
  deriving DecidableEq

end BinaryMatching

end OAI


