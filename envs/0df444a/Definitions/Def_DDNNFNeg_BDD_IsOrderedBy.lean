-- Prove2me | Definitions.Def_DDNNFNeg_BDD_IsOrderedBy
-- name    : DDNNFNeg_BDD_IsOrderedBy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:38.446923+00:00
-- url     : https://prove2.me/theorems/9eb36fc7-128e-4b83-a9e4-4d60277e627c
-- title:
--   Branching program reading variables in a fixed order
-- statement:
--   A branching program **reads its variables in the order** $\pi : X \to \mathbb N$ if, whenever a vertex $u$ reachable from the starting vertex is labelled by $v$ and a vertex reachable from a successor of $u$ is labelled by $v'$, then $\pi(v) < \pi(v')$.
--
--   With $\pi$ injective this says that on every source-to-sink path the variables appear in the same order; it implies read-once. An **OBDD** is a branching program with no $\vee$ vertices that is ordered by an injective $\pi$.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 3.2, p.9

import Mathlib
import Definitions.Def_DDNNFNeg_BDD_Reach

namespace DDNNFNeg

/-- The branching program `B` reads its variables in the order given by `π : X → ℕ`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 3.2, p.9: "on every source-to-sink path variables appear in the same order"):
whenever a vertex `u` reachable from the starting vertex is labelled by `v` and a vertex
reachable from a successor of `u` is labelled by `v'`, then `π v < π v'`.

**Formalization Note** With `π` injective this says that all paths from the start read
variables in one common order; it implies `BDD.IsReadOnce`. An OBDD is a branching program
with `BDD.IsDeterministic` and `IsOrderedBy π` for an injective `π`. -/
def BDD.IsOrderedBy {X : Type*} (B : BDD X) (π : X → ℕ) : Prop :=
  ∀ (u : Fin B.size) (v : X) (lo hi : Fin B.size), B.Reach B.start u →
    B.node u = .test v lo hi →
    ∀ (w : Fin B.size) (v' : X) (lo' hi' : Fin B.size), (B.Reach lo w ∨ B.Reach hi w) →
      B.node w = .test v' lo' hi' → π v < π v'

end DDNNFNeg


