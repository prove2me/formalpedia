-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
-- name    : OAI_Combinatorics_Sensitivity_Tournament
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:22:37.776869+00:00
-- url     : https://prove2.me/theorems/c016508c-2ccd-4f1b-b082-e2c7ec1183d8
-- title:
--   Tournaments, regular tournaments, and good edge labelings
-- statement:
--   Let $[k] = \{0, 1, \dots, k-1\}$.
--
--   1. **Tournament.** A tournament on $k$ vertices is a directed graph on $[k]$, with edge relation written $i \to j$, that has no loops and in which every pair of distinct vertices is joined in exactly one direction: for $i \ne j$, $i \to j$ holds if and only if $j \to i$ fails.
--
--   2. **Regular tournament.** For $M \in \mathbb{N}$, a regular tournament with parameter $M$ is a tournament on $2M^2 + 1$ vertices in which every vertex has out-degree exactly $M^2$.
--
--   3. **Good labeling.** For a tournament $T$ on $[k]$ and $r \in \mathbb{N}$, a good labeling with $r$ labels is a map $\lambda : [k] \times [k] \to [r]$, assigning a label to every ordered pair of vertices, such that for every set $I$ of exactly $16$ vertices and every choice of target labels $m : [k] \to [r]$, some edge inside $I$ carries a label different from the target of its head:
--   $$
--   \forall\, I \subseteq [k] \text{ with } |I| = 16,\ \ \forall\, m : [k] \to [r],\ \ \exists\, i, j \in I:\ i \to j \ \text{ and } \ \lambda(i,j) \ne m(j).
--   $$
--   Since only the values of $m$ on $I$ matter, this says that no $16$-vertex set is target-constant, i.e. there is no $I$ with $|I| = 16$ such that for each $j \in I$ all edges from $I$ into $j$ carry one common label.
--
--   In the recursive construction the tournament decides which rows a row clause tests through its gate conditions, and the labeling decides which column of each such row is tested. The good-labeling property limits how many rows of a rejected input can be repaired by a single bit flip in a target, which keeps the sensitivity on rejected inputs under control; good labelings of regular tournaments with about $\sqrt{M}$ labels exist by a counting argument.
--
--   **Formalization Note** `Tournament k` extends Mathlib's `Digraph (Fin k)` by the fields `loopless` and `edge_compl`; `RegularTournament M` extends `Tournament (2 * M^2 + 1)` by the field `outdegree`. `GoodLabeling T r` is a structure carrying the labeling as data (field `label`) together with the property (field `good`), so existence of a good labeling is nonemptiness of this type. Labels are attached to all ordered pairs, but only their values on edges matter.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Tournament.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Tournament.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SensitivitySeparation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates

namespace OAI

/-! Finite tournaments and the target-constant labeling condition. -/

noncomputable section
open scoped Classical

namespace Paper320

structure Tournament (k : ℕ) extends Digraph (Fin k) where
  loopless : ∀ i, ¬ Adj i i
  edge_compl : ∀ {i j}, i ≠ j → (Adj i j ↔ ¬ Adj j i)

structure RegularTournament (M : ℕ) extends Tournament (2 * M^2 + 1) where
  outdegree : ∀ i, (Finset.univ.filter (Adj i)).card = M^2

structure GoodLabeling {k : ℕ} (T : Tournament k) (r : ℕ) where
  label : Fin k → Fin k → Fin r
  good : ∀ I : Finset (Fin k), I.card = 16 → ∀ m : Fin k → Fin r,
    ∃ i ∈ I, ∃ j ∈ I, T.Adj i j ∧ label i j ≠ m j

namespace Tournament
variable {k : ℕ} (T : Tournament k)

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)

end GoodLabeling
end Paper320

end

end OAI


