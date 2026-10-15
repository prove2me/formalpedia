-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
-- name    : OAI_Combinatorics_Sensitivity_RecursiveCandidates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:29:51.463653+00:00
-- url     : https://prove2.me/theorems/0ec94e7f-0743-496b-b084-6b786742b2f6
-- title:
--   Sinks among the gate-candidate rows
-- statement:
--   In the row-clause construction over a tournament $T$ on $[k] = \{0, \dots, k-1\}$ (edges $i \to j$), with labeling $\lambda$, family $F$, clause index $q$ and input $x$, let $\mathcal{G}_q(x)$ be the set of gate candidates: rows with no failed target and exactly one failed gate. The gate sinks are the gate candidates that have no out-neighbour among the gate candidates:
--
--   $$
--   \mathrm{Sink}_q(x) = \{ i \in \mathcal{G}_q(x) : \text{there is no } j \in \mathcal{G}_q(x) \text{ with } i \to j \}.
--   $$
--
--   Since any two distinct vertices of a tournament are joined by an edge, there is at most one gate sink. In the sensitivity analysis of a rejected input this possible sink is treated separately: its flips are counted through the side sensitivity of the family on accepted inputs, while the flips of the other gate candidates are counted through a joint sensitivity.
--
--   **Formalization Note** The definition is `gateSinks`, a filter of `gateCandidates`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/RecursiveCandidates.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/RecursiveCandidates.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures

namespace OAI

/-! Unique failed children and the unique possible sink of the gate-clause list. -/

noncomputable section
open scoped Classical

namespace Paper320

def gateSinks {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  (gateCandidates T label F q x).filter fun i =>
    ∀ j ∈ gateCandidates T label F q x, ¬ T.Adj i j

end Paper320

end

end OAI


