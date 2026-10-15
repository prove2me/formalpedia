-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
-- name    : OAI_Combinatorics_Sensitivity_TournamentCounts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:28:08.344056+00:00
-- url     : https://prove2.me/theorems/137e76b3-a80e-408c-96b5-f53cf3bdb764
-- title:
--   Internal edges of a vertex set in a tournament
-- statement:
--   Let $T$ be a tournament on $[k] = \{0, \dots, k-1\}$ with edge relation $i \to j$. For a set of vertices $I \subseteq [k]$, the internal edges of $I$ are the ordered pairs of vertices of $I$ that are edges of $T$:
--
--   $$
--   E_T(I) = \{ (i,j) \in I \times I : i \to j \}.
--   $$
--
--   Because a tournament has no loops and joins every pair of distinct vertices in exactly one direction, $E_T(I)$ has exactly $\binom{|I|}{2}$ elements. Internal edges are the coordinates on which an edge labeling is constrained when it is required to be target-constant on $I$, so they are the basic objects in counting bad labelings; counting them through out-degrees also shows that a vertex set in which every vertex has at most one out-neighbour inside the set has at most $3$ vertices.
--
--   **Formalization Note** The definition is `Tournament.internalEdges`, the filter of the product `I ×ˢ I` by the adjacency relation; the count $\binom{|I|}{2}$ is proved separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/TournamentCounts.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/TournamentCounts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SensitivitySeparation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets

namespace OAI

/-! The exact internal edge count and the small gate-candidate bound. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320.Tournament
variable {k : ℕ} (T : Tournament k)

def internalEdges (I : Finset (Fin k)) : Finset (Fin k × Fin k) :=
  (I ×ˢ I).filter fun p => T.Adj p.1 p.2

end Paper320.Tournament

end

end OAI


