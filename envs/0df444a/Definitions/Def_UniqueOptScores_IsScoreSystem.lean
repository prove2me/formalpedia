-- Prove2me | Definitions.Def_UniqueOptScores_IsScoreSystem
-- name    : UniqueOptScores_IsScoreSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:22.083626+00:00
-- url     : https://prove2.me/theorems/4eee5078-9234-417a-b7db-036827202b21
-- title:
--   Score systems with ceiling $r$ and query bound $q$
-- statement:
--   A **score system** on regions $X, Y$ with exterior answers $e$ is a finite nonempty family of candidates $C$, each evaluated by a deterministic query algorithm $T_c$. It has **score ceiling $r$ and query bound $q$** if for every support $S \subseteq X \cup Y$ and every candidate $c$, the evaluation of $T_c$ under $O_S$ makes at most $q$ membership queries and returns a score in $\{0, \dots, r\}$. There is no bound on $|C|$ and no efficiency assumption beyond the query bound.
--
--   **Formalization Note** The bounds are required on every support, as printed on p.8 ("for every support S"), not as a bound on the depth of the tree over all oracles. The candidate set is the type indexing the family; its finiteness and nonemptiness are hypotheses of the theorems.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 6, p.22; Section 2.3.1, p.8 ("makes at most q membership queries, for every support S")

import Mathlib
import Definitions.Def_UniqueOptScores_QTree
import Definitions.Def_UniqueOptScores_supportOracle

namespace UniqueOptScores

/-- **A score system with score ceiling `r` and query bound `q`.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §6, p.22: "A score system has a fixed finite nonempty candidate set C, independent of S.
Each candidate is evaluated by a total deterministic oracle algorithm with scores in {0, . . . , r}
and at most q membership queries"; p.8: "… makes at most q membership queries, for every support S."

`IsScoreSystem X Y e T r q` holds when, for every support `S ⊆ X ∪ Y` and every candidate `c`, the
evaluation `T c` under the oracle of `S` makes at most `q` queries and returns a score at most `r`.

**Formalization Note.** The bounds are per support, as printed (not a bound on the depth of the
tree over all oracles). The candidate type (finite, nonempty) is a binder of each theorem. -/
def IsScoreSystem {ι α : Type*} [DecidableEq α] (X Y : Finset α) (e : α → Bool)
    (T : ι → QTree α ℕ) (r q : ℕ) : Prop :=
  ∀ S ⊆ X ∪ Y, ∀ c : ι, ((T c).queries (supportOracle X Y e S)).length ≤ q ∧
    (T c).eval (supportOracle X Y e S) ≤ r

end UniqueOptScores


