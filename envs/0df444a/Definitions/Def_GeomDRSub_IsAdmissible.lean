-- Prove2me | Definitions.Def_GeomDRSub_IsAdmissible
-- name    : GeomDRSub_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:52.63991+00:00
-- url     : https://prove2.me/theorems/80f4a834-ddec-40f7-86f2-3996e48420fe
-- title:
--   Admissible feasible set $K$ with $\zeta\mathbf 1\in K$
-- statement:
--   A set $K\subseteq\mathbb R^d$ is **admissible with diagonal level $\zeta$** if
--   1. $K\subseteq[0,1]^d$;
--   2. $K$ is nonempty, compact and convex;
--   3. $K$ is down-closed;
--   4. the diagonal point $\zeta\mathbf 1$ belongs to $K$ (condition (4)).
--
--   These are the standing assumptions on the feasible set of the paper. Down-closedness and nonemptiness give $\mathbf 0\in K$.
--
--   **Formalization Note** The range $\zeta\in[0,1]$ of the supplied level is a separate hypothesis of each theorem, as in the paper.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 3.1, p.8, Eq. (4)

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_diagPt
import Definitions.Def_GeomDRSub_IsDownClosed

namespace GeomDRSub

/-- **The standing feasible set with diagonal level `ζ`.** Aggarwal–Lu, arXiv:2610.00545,
Section 3.1, p.8: "Let `K ⊆ Q` be nonempty, compact, convex, and down-closed … A supplied number
`ζ ∈ [0, 1]` satisfies `ζ1 ∈ K`. (4)"

`IsAdmissible K ζ` collects these conditions: `K ⊆ [0,1]^d`, `K` nonempty, compact, convex and
down-closed, and the diagonal point `ζ1` lies in `K`.

**Formalization Note.** The range `ζ ∈ [0,1]` of the supplied number is a separate hypothesis of
each theorem, as on the page. -/
def IsAdmissible {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ζ : ℝ) : Prop :=
  K ⊆ cube d ∧ K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧ IsDownClosed K ∧ diagPt d ζ ∈ K

end GeomDRSub


