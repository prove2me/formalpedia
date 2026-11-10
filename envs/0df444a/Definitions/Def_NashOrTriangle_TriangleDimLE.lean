-- Prove2me | Definitions.Def_NashOrTriangle_TriangleDimLE
-- name    : NashOrTriangle_TriangleDimLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:34.863239+00:00
-- url     : https://prove2.me/theorems/40674cee-5e75-46b8-8ca3-411a2fe8dae8
-- title:
--   Triangle dimension bound $d_H(u)\le d$
-- statement:
--   For a game $H$ and $u > 0$, $d_H(u)$ is the largest size of a triangle with margin $u$ in $H$ or in the complemented game $1 - H$. This predicate expresses
--   $$
--   d_H(u) \le d ,
--   $$
--   that is: neither $H$ nor $1 - H$ contains a $(d+1, u)$-triangle. The paper bounds $d_H$ by $t$ on games without (margin) triangles of size $t$, and Lemma C.1 bounds the running time of the double-oracle algorithm in terms of $d_H$.
--
--   **Formalization Note** The paper uses $d_H$ only through upper bounds, so the bound is a predicate instead of a maximum (which would need a junk value when no maximum exists). Deleting the last row and column of a margin triangle leaves a margin triangle, so excluding size $d+1$ excludes all sizes above $d$.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_NashOrTriangle_HasMarginTriangle
import Definitions.Def_NashOrTriangle_complement

namespace NashOrTriangle

/-- `d_H(u) ≤ d`: neither `H` nor the complemented game `1 − H` contains a triangle with margin
`u` of size `d + 1`. Here `d_H(u)` is "the largest size of a triangle with margin u in H or in
the complemented game 1 − H".

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C, printed p. 23 (PDF p. 24).

**Formalization Note** The paper only ever uses `d_H` through upper bounds, so the predicate
"`d_H(u) ≤ d`" replaces the maximum (which would need a junk value when unbounded). Margin
triangles are closed under deleting the last row and column, so excluding size `d + 1` excludes
every size `> d`. -/
def TriangleDimLE {A B : Type*} (M : A → B → ℚ) (u : ℝ) (d : ℕ) : Prop :=
  ¬ HasMarginTriangle M (d + 1) u ∧ ¬ HasMarginTriangle (complement M) (d + 1) u

end NashOrTriangle


