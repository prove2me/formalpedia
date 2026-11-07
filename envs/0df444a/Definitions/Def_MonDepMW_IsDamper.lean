-- Prove2me | Definitions.Def_MonDepMW_IsDamper
-- name    : MonDepMW_IsDamper
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:33.184033+00:00
-- url     : https://prove2.me/theorems/296b5a88-84ea-40e0-a40d-1777b1484feb
-- title:
--   The damper $(S,H)$ of a vertex set $A$
-- statement:
--   A pair $(S,H)$ is a **damper** of $A$ with parameters $q,r$ and bound $B$ if $H$ is an $S$-flip of $G$, $|S|\leqslant|A|/q$, and for every vertex $u$, $\mathrm{Ball}^r_H[u]$ intersects at most $B$ parts of $\mathcal T_1(G,A\cup S)$.
--
--   This is the shared conclusion of Theorems 4.1 and 8.3, stated once for use in both their existence and algorithmic clauses.
--
--   **Formalization Note** Every use carries $q\geqslant1$.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §4, p.15; §8, p.33

import Mathlib
import Definitions.Def_MonDepMW_IsFlip

set_option autoImplicit false

namespace MonDepMW

/-- **The conclusion of the Damping Theorem** for `A`, with bound `bound` (Theorems 4.1, p.15, and 8.3, p.33): `H` is an
`S`-flip of `G`, "|S| ⩽ |A|/q; and for every vertex u ∈ V (G), Ball^r_H[u] intersects at most [bound] parts of
𝒯1(G, A ∪ S)".

**Formalization Note.** Every use carries `1 ≤ q`, so the division is genuine. -/
structure IsDamper {n : ℕ} (G : SimpleGraph (Fin n)) (A S : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (q r bound : ℕ) : Prop where
  flip : IsFlip G (oneType G S) H
  card_le : (S.card : ℝ) ≤ (A.card : ℝ) / (q : ℝ)
  hits : ∀ u, partsHit (oneType G (A ∪ S)) (ball H r u) ≤ bound

end MonDepMW


