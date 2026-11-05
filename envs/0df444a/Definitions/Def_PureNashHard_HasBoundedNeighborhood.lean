-- Prove2me | Definitions.Def_PureNashHard_HasBoundedNeighborhood
-- name    : PureNashHard_HasBoundedNeighborhood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:51.149268+00:00
-- url     : https://prove2.me/theorems/b669a90f-4060-4418-8501-12280065b908
-- title:
--   $k$-bounded neighborhood
-- statement:
--   A game with neighbourhood function $\mathrm{Neigh}$ has **$k$-bounded neighborhood** if
--   $$
--   |\mathrm{Neigh}(p)|\le k\qquad\text{for every player }p .
--   $$
--   Theorem 3.1's hardness holds already for games with 3-bounded neighborhood.
--
--   **Formalization Note** $|\mathrm{Neigh}(p)|$ is the length of the neighbour list; for a well-formed game it has no repetitions, so this is the size of the set.
-- source:
--   Gottlob, Greco, Scarcello, Pure Nash Equilibria: Hard and Easy Games, JAIR 24 (2005), doi:10.1613/jair.1683, §1, p.359 (PDF p.3): Bounded Neighborhood

import Definitions.Def_PureNashHard_Game

set_option autoImplicit false

namespace PureNashHard

/-- **k-bounded neighborhood** (Gottlob, Greco, Scarcello, JAIR 24 (2005), §1, p.359): "A
strategic game with associated neighborhood function Neigh has k-bounded neighborhood if, for
each player p, |Neigh(p)| ≤ k."

**Formalization Note** `|Neigh(p)|` is the length of the list `neigh p`; for a well-formed game
(`Game.WellFormed`) the list has no repetitions, so its length is the cardinality of the set.
The paper's `k > 0` is not built in; the mission uses `k = 3`. -/
def HasBoundedNeighborhood {R : Type} (G : Game R) (k : ℕ) : Prop :=
  ∀ p, (G.neigh p).length ≤ k

end PureNashHard


