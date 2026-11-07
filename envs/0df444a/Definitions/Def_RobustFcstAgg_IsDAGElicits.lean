-- Prove2me | Definitions.Def_RobustFcstAgg_IsDAGElicits
-- name    : RobustFcstAgg_IsDAGElicits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:51:25.791958+00:00
-- url     : https://prove2.me/theorems/b8b0c5a5-0da1-4632-8b5a-db98432e05ee
-- title:
--   $G$ DAG-elicits $\mathcal Q$ (Definition 3, with Condition 1)
-- statement:
--   A directed acyclic graph $G$ on $\mathcal Q\cup\{Y\}$ **DAG-elicits** the collection $\mathcal Q$ if
--
--   1. each $Q\in\mathcal Q$ is elicitable with respect to the set $N_G(Q)$ of its out-neighbours, which may include $Y$;
--   2. $Y$ is the unique sink;
--   3. each $Q\in\mathcal Q$ satisfies Condition 1 for the variables in $N_G(Q)$.
--
--   **Formalization Note** "$Y$ is the unique sink" is the requirement that every query has a nonempty out-neighbour set; $Y$ has no out-edges by typing. Clause 3 is the standing regularity condition of pp.14, 25.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Definition 3, p.5; Condition 1, p.25

import Mathlib
import Definitions.Def_RobustFcstAgg_vertexVal
import Definitions.Def_RobustFcstAgg_IsElicitable
import Definitions.Def_RobustFcstAgg_SatisfiesCondition1

namespace RobustFcstAgg

/-- **`G` DAG-elicits `𝒬`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Definition 3, p.5: `G` is a directed acyclic graph on `𝒬 ∪ {Y}`, each `Q` is
elicitable with respect to its out-neighbours `N_G(Q)`, and `Y` is the unique sink. Condition 1 (p.14 "Throughout,
we require", p.25) is a standing clause.

**Formalization Note.** A graph is its out-neighbour map. "`Y` is the unique sink" is `(out j).Nonempty` for every
query, `Y` having no out-edges by typing. Scored variables are exactly the out-neighbours' values. -/
def IsDAGElicits {n : ℕ} {ι : Type} (Q : ι → Query n) (out : ι → Finset (Option ι)) : Prop :=
  (∀ j, ¬ Relation.TransGen (fun u v : ι => some v ∈ out u) j j) ∧
  (∀ j, (out j).Nonempty) ∧
  (∀ j, IsElicitable (Q j) (fun D (v : out j) => vertexVal Q D v.1)) ∧
  (∀ j, SatisfiesCondition1 (Q j) (fun D (v : out j) => vertexVal Q D v.1))

end RobustFcstAgg


