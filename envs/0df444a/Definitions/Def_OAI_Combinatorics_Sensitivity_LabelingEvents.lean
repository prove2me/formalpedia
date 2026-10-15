-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_LabelingEvents
-- name    : OAI_Combinatorics_Sensitivity_LabelingEvents
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:49:04.62532+00:00
-- url     : https://prove2.me/theorems/03856974-7d28-40c8-be67-c3a53257cc69
-- title:
--   Labeling events and bad labelings of a tournament
-- statement:
--   Let $T$ be a tournament on $[k] = \{0, 1, \dots, k-1\}$ with edge relation $i \to j$, and let $n, r \in \mathbb{N}$. A labeling is any map $A : [k] \times [k] \to [r]$, assigning a label to each ordered pair of vertices.
--
--   1. **Labeling event.** For a map $v : [n] \to [k]$ and target labels $m : [n] \to [r]$, the event $\mathcal{E}(v,m)$ is the following set of labelings:
--   $$
--   \mathcal{E}(v,m) = \begin{cases} \{\, A : A(v(i), v(j)) = m(j) \text{ for all } i, j \in [n] \text{ with } v(i) \to v(j) \,\}, & v \text{ injective}, \\ \emptyset, & \text{otherwise.} \end{cases}
--   $$
--   For injective $v$ it consists of the labelings under which every edge inside the $n$-vertex set $v([n])$ carries the target label of its head.
--
--   2. **Bad labelings.** The set of bad labelings is the union of all events,
--   $$
--   \mathrm{Bad}_n = \bigcup_{v : [n] \to [k]} \ \bigcup_{m : [n] \to [r]} \mathcal{E}(v,m),
--   $$
--   that is, the labelings for which some set of $n$ vertices admits target labels respected by every internal edge.
--
--   With $n = 16$, a labeling outside $\mathrm{Bad}_{16}$ has no target-constant set of $16$ vertices, so it is a good labeling. The union bound $|\mathrm{Bad}_n| \le k^n r^n r^{k^2 - \binom{n}{2}}$, proved separately, therefore yields good labelings as soon as this bound is smaller than the total number $r^{k^2}$ of labelings.
--
--   **Formalization Note** The definitions are `Tournament.labelingEvent T v m` and `Tournament.badLabelings T n r`, both `Finset`s of functions `(Fin k × Fin k) → Fin r`; the injectivity test is decided classically. The definitions are stated for general $n$, although the construction only uses $n = 16$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/LabelingEvents.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/LabelingEvents.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or
import Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex
import Definitions.Def_OAI_Combinatorics_Sensitivity_Construction
import Definitions.Def_OAI_Combinatorics_Sensitivity_FixedCoordinates

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Exact counts of target-constant label constraints on sixteen vertices. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320.Tournament
variable {k r n : ℕ} (T : Tournament k)

def labelingEvent (v : Fin n → Fin k) (m : Fin n → Fin r) :
    Finset ((Fin k × Fin k) → Fin r) :=
  if Function.Injective v then
    Finset.univ.filter fun A => ∀ i j, T.Adj (v i) (v j) → A (v i, v j) = m j
  else ∅

def badLabelings (n r : ℕ) : Finset ((Fin k × Fin k) → Fin r) :=
  Finset.univ.biUnion fun v : Fin n → Fin k =>
    Finset.univ.biUnion fun m : Fin n → Fin r => T.labelingEvent v m

end Paper320.Tournament

end

end OAI


