-- Prove2me | Definitions.Def_WagelmansELS_Efficient_EfficientPeriods
-- name    : WagelmansELS_Efficient_EfficientPeriods
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:57.758296+00:00
-- url     : https://prove2.me/theorems/e16f5cd7-861f-4347-bb3c-c89b2ee84cd3
-- title:
--   Section 2: efficient periods as lower-envelope breakpoints
-- statement:
--   For an iteration $i$, plot the points $(D(t),G(t))$ for $i<t\le n+1$. A period $t$ is **efficient** when its point is a vertex of the lower convex envelope of these points. The finite set of efficient periods is denoted $E_i$:
--
--   $$E_i=\{t:i<t\le n+1,\ (D(t),G(t))\text{ is a lower-envelope breakpoint}\}.$$
--
--   The definition uses an equivalent finite-point test. At a shared abscissa it keeps a point of least height, choosing the smallest period index when heights tie. A point strictly between two abscissae is excluded if it lies on or above the chord joining two plotted points. Thus collinear interior points are excluded, while the endpoints are breakpoints. This makes the representation well-defined even when some demands are zero.
--
--   These periods are the candidate next production periods used in Proposition 1 and the threshold rule.
--
--   **Formalization Note** The smallest-index tie follows the paper's update convention on p. S150, where a zero-demand period replaces its successor as the efficient representative. The chord condition is written without division, and equality excludes a collinear interior point.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), pp. S147–S148, Section 2, lower convex envelope and efficient periods; p. S150, zero-demand replacement convention

import Mathlib
import Definitions.Def_WagelmansELS_Efficient_Instance

namespace WagelmansELS.Efficient
namespace Instance
variable (P : Instance)

/-- A breakpoint of the lower convex envelope of `(D t,G t)`, represented by
its earliest period at equal abscissa and height. Collinear interior points are excluded. -/
def IsEfficient (i t : ℕ) : Prop :=
  t ∈ Finset.Ioc i (P.n + 1) ∧
  (∀ u ∈ Finset.Ioc i (P.n + 1), u ≠ t → P.D u = P.D t →
    P.G t < P.G u ∨ (P.G t = P.G u ∧ t < u)) ∧
  ¬ ∃ u ∈ Finset.Ioc i (P.n + 1), ∃ w ∈ Finset.Ioc i (P.n + 1),
    P.D u < P.D t ∧ P.D t < P.D w ∧
    (P.D w - P.D u) * P.G t ≥
      (P.D w - P.D t) * P.G u + (P.D t - P.D u) * P.G w

/-- The efficient periods for iteration `i`. -/
noncomputable def E (i : ℕ) : Finset ℕ :=
  by
  classical
  exact (Finset.Ioc i (P.n + 1)).filter (P.IsEfficient i)

end Instance
end WagelmansELS.Efficient


