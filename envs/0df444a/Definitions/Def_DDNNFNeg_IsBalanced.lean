-- Prove2me | Definitions.Def_DDNNFNeg_IsBalanced
-- name    : DDNNFNeg_IsBalanced
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:03.721194+00:00
-- url     : https://prove2.me/theorems/715c8b8e-6fdb-427c-aa6e-3798bbaa6f3f
-- title:
--   Balanced bipartition: $|A|, |B| \ge |X|/3$
-- statement:
--   A bipartition $(A, B)$ of a finite set of variables $X$ is **balanced** if
--   $$
--   |A| \ge |X|/3 \quad\text{and}\quad |B| \ge |X|/3 .
--   $$
--
--   **Formalization Note** The bipartition is given by $A$, with $B = X \setminus A$; the conditions are written $|X| \le 3|A|$ and $|X| \le 3|B|$.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.2, p.8

import Mathlib

namespace DDNNFNeg

/-- The bipartition `(A, Aᶜ)` of the finite variable set `X` is balanced: `|A|, |Aᶜ| ≥ |X|/3`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.2, p.8).

**Formalization Note** A bipartition `(A, B)` is encoded by its first part `A : Finset X`,
with `B = Aᶜ`. The condition `|A| ≥ |X|/3` is written `|X| ≤ 3|A|`, which is equivalent in
the rationals and avoids natural-number division. -/
def IsBalanced {X : Type*} [Fintype X] [DecidableEq X] (A : Finset X) : Prop :=
  Fintype.card X ≤ 3 * A.card ∧ Fintype.card X ≤ 3 * Aᶜ.card

end DDNNFNeg


