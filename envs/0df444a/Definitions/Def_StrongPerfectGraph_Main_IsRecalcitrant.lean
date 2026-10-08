-- Prove2me | Definitions.Def_StrongPerfectGraph_Main_IsRecalcitrant
-- name    : StrongPerfectGraph_Main_IsRecalcitrant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:59:43.627831+00:00
-- url     : https://prove2.me/theorems/e43e6927-4ba4-4354-907a-29e6236431b3
-- title:
--   Recalcitrant graph
-- statement:
--   A graph $G$ is **recalcitrant** if it is Berge, neither $G$ nor $\overline G$ is a line graph, $G$ is not double split, neither $G$ nor $\overline G$ admits a proper 2-join, and $G$ admits neither a proper homogeneous pair nor a balanced skew partition.
--
--   $$\operatorname{Berge}(G)\ \land\ \neg\operatorname{Line}(G)\ \land\ \neg\operatorname{Line}(\overline G)\ \land\ \neg\operatorname{DoubleSplit}(G)\ \land\ \cdots.$$
--
--   “Line graph” here means the line graph of any finite simple graph, not only of a bipartite graph. The full exclusions are the hypotheses of Theorem 13.5.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 154, §13, definition preceding 13.5

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsBasic
import Definitions.Def_StrongPerfectGraph_Main_IsProperTwoJoin
import Definitions.Def_StrongPerfectGraph_Main_IsProperHomogeneousPair
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition

namespace StrongPerfectGraph.Main

/-- A Berge graph with all the non-bipartite basic and decomposition outcomes excluded. -/
def IsRecalcitrant {V : Type*} (G : SimpleGraph V) : Prop :=
  IsBerge G ∧
    ¬ IsLineGraph G ∧ ¬ IsLineGraph Gᶜ ∧ ¬ IsDoubleSplit G ∧
    ¬ IsProperTwoJoin G ∧ ¬ IsProperTwoJoin Gᶜ ∧
    ¬ IsProperHomogeneousPair G ∧ ¬ AdmitsBalancedSkewPartition G

end StrongPerfectGraph.Main


