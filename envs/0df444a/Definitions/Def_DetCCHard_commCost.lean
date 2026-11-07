-- Prove2me | Definitions.Def_DetCCHard_commCost
-- name    : DetCCHard_commCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:42.968267+00:00
-- url     : https://prove2.me/theorems/06ba066b-af55-421a-b742-b92972ab71f5
-- title:
--   Communication cost $D(F[U,V])$ of a restriction and $D(M)$
-- statement:
--   For a table $M : X \times Y \to \{0,1\}$ and sets $U \subseteq X$, $V \subseteq Y$, the **cost of the restriction** $M[U, V]$ is
--   $$
--   D(M[U,V]) = \min\{\operatorname{depth}(P) : P \text{ a protocol with } P(x, y) = M(x, y) \text{ for all } x \in U,\ y \in V\}.
--   $$
--   The **deterministic communication complexity** of $M$ is $D(M) = D(M[X, Y])$: the least cost of a protocol, with unrestricted speaking order, that computes every entry correctly. Every bit is charged, including fixed bits, and local computation is free.
--
--   The deletion bounds (Definition 5.1) and every lower and upper bound of the mission are statements about these two quantities.
--
--   **Formalization Note** The restriction is encoded as correctness on $U \times V$ of a protocol over all of $X$ and $Y$; this has the same cost as the submatrix on $U \times V$, since protocols extend and restrict. An empty $U$ or $V$ gives cost $0$. For finite $X$ the minimum exists (Alice sends her input, Bob the answer), so the infimum is never the junk value of an empty set; this is checked in the mission's verification file.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Definitions 4.1 and 5.1, pp.13 and 16

import Mathlib
import Definitions.Def_DetCCHard_Protocol

namespace DetCCHard

/-- The **communication cost of a restriction** `D(F[U, V])` (Gaspers–He–Mackenzie,
arXiv:2508.05597, held version sha256 ad552d13…a4a03, Definitions 4.1 and 5.1, pp.13 and 16): the
least depth of a deterministic protocol that computes the table `M` correctly on every input pair
of `U × V`.

**Formalization Note** The restriction `F[U, V]` is encoded as correctness on `U × V` of a protocol
over all of `X` and `Y`. This equals the cost of the submatrix on `U × V`, since a protocol for the
submatrix extends to all inputs and a protocol correct on `U × V` restricts to one for the
submatrix. An empty `U` or `V` gives cost `0` (every protocol is vacuously correct). For finite `X`
the set of admissible depths is nonempty (Alice can send her input and Bob the answer), so the
infimum is a minimum and never the junk value of `sInf ∅`. -/
noncomputable def commCost {X Y : Type} (M : X → Y → Bool) (U : Set X) (V : Set Y) : ℕ :=
  sInf {n : ℕ | ∃ P : Protocol X Y, P.depth ≤ n ∧ ∀ x ∈ U, ∀ y ∈ V, P.eval x y = M x y}

/-- The **deterministic communication complexity** `D(M)` of a total table `M : X × Y → {0, 1}`
(Definition 4.1, p.13): the least cost of a deterministic public-output protocol, with unrestricted
speaking order, that computes every entry correctly. -/
noncomputable def Dcost {X Y : Type} (M : X → Y → Bool) : ℕ :=
  commCost M Set.univ Set.univ

end DetCCHard


