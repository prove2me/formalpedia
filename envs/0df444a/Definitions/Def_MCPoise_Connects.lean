-- Prove2me | Definitions.Def_MCPoise_Connects
-- name    : MCPoise_Connects
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:13.729447+00:00
-- url     : https://prove2.me/theorems/95cf8154-268b-44f3-9650-4ed44baab2c2
-- title:
--   A subgraph connects every demand
-- statement:
--   A graph $H$ on $V$ **connects every demand** when $s_i$ and $t_i$ lie in one connected component of $H$ for every $i \in [k]$.
--
--   **Formalization Note** This is a separate clause from any distance bound, since Lean's graph distance is $0$ between vertices in different components.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Definition 1, p.3

import Mathlib
import Definitions.Def_MCPoise_Inst

namespace MCPoise

/-- **`H` connects every pair of demands.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Definition 1, p.3: "a subgraph H ⊆ G that connects every pair of demands in D".

**Formalization Note.** Mathlib's `SimpleGraph.dist` is `0` on unreachable pairs, so connection is its own
clause and is never read off a distance. -/
def Connects (I : Inst) (H : SimpleGraph (Fin I.n)) : Prop :=
  ∀ i : Fin I.k, H.Reachable (I.s i) (I.t i)

end MCPoise


