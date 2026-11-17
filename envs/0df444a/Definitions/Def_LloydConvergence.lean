-- Prove2me | Definitions.Def_LloydConvergence
-- name    : LloydConvergence
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-17T04:42:18.125003+00:00
-- url     : https://prove2.me/theorems/a60e4219-90da-4278-861e-c987142efb35
-- title:
--   Lloyd's (k-means) iteration: assignments, centers, strict-move step, orbit, and induced partition
-- statement:
--   Lloyd's iteration for $k$-means clustering (Shalev-Shwartz and Ben-David, Chapter 22).
--
--   An assignment $f$ sends each point of a finite dataset $S \subset \mathbb{R}^n$ to one of $k$ clusters. `fiber S f i` is the set of points assigned to cluster $i$; `centroidS S T` is the mean of the points in $T$; `centers S f i` is the centroid of cluster $i$; `obj S f` is the $k$-means objective $\sum_x \|x - \mu(f(x))\|^2$; and `cost S \mu f` is the same sum against prescribed centers $\mu$. `argminDist \mu x` is a nearest center to $x$ (ties broken by the choice). One Lloyd step, `step S f`, reassigns each point to its nearest center — but only when that center is strictly nearer than its current one (strict-move tie-breaking; on ties the point stays). `orbit S f_0 t` is the $t$-fold iterate of `step` from $f_0$, and `part S f i` is the partition induced by $f$, as sets of points.
--
--   Two conventions are fixed here. First, an empty cluster's centroid is $0$, matching the platform's convention for `UnderstandingML.centroid`. Second, the strict-move rule is a deliberate divergence from the platform's `IsNearestAssignment` (ties arbitrary): under arbitrary tie-breaking a point can move between equidistant centroids with no change in the objective, and the iteration need not terminate. With strict moves, Lloyd's algorithm reaches a fixed point in finitely many steps, which is the content of `LloydConvergence.lloyd_converges`.
--
--   **Formalization Note** The definitions are stated for assignments `f : S \to \mathrm{Fin}\, k` on the subtype of points, with `[NeZero k]` wherever an argmin must exist.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, Section 22.2, pp. 312-313; Lloyd, Least squares quantization in PCM, IEEE Trans. Inform. Theory 28 (1982)

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.MetricSpace.Basic

/-!
# Lloyd's (k-means) iteration — definitions

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory
to Algorithms*, Cambridge University Press 2014, §22.2 (pp. 312–313);
Lloyd, "Least squares quantization in PCM", IEEE Trans. Inform. Theory 28
(1982).

An assignment `f : S → Fin k` sends each point of a finite dataset
`S ⊆ ℝⁿ` to one of `k` clusters. Its centers are the cluster means
(`centers`), and one Lloyd step (`step`) reassigns each point to its nearest
center — but only when that center is STRICTLY nearer than its current one
(strict-move tie-breaking; on ties the point stays). The `orbit` of an
initial assignment under iteration of `step` is what the convergence theorem
`LloydConvergence.lloyd_converges` is about; `part` is the partition induced
by an assignment, as Finsets of points.

Conventions: an empty cluster's centroid is `0` (the platform convention for
`UnderstandingML.centroid`, `(C.card : ℝ)⁻¹ • ∑ x ∈ C, x`, which is also `0`
on the empty set). The strict-move rule is a deliberate divergence from the
platform's `IsNearestAssignment` (ties arbitrary): under arbitrary
tie-breaking a point can move between equidistant centroids with no change in
the objective, and the iteration need not terminate.
-/

namespace LloydConvergence

variable {n k : ℕ}

/-- The fiber of an assignment: the points of `S` assigned to cluster `i`. -/
def fiber (S : Finset (EuclideanSpace ℝ (Fin n))) (f : S → Fin k) (i : Fin k) :
    Finset S :=
  Finset.univ.filter (fun x => f x = i)

/-- The centroid of a fiber, as a `Finset S`: the mean of its points.
For an empty fiber this is `0`, matching the platform convention. -/
noncomputable def centroidS (S : Finset (EuclideanSpace ℝ (Fin n))) (T : Finset S) :
    EuclideanSpace ℝ (Fin n) :=
  (T.card : ℝ)⁻¹ • ∑ x ∈ T, (x : EuclideanSpace ℝ (Fin n))

/-- The centers of an assignment: the centroid of each cluster. -/
noncomputable def centers (S : Finset (EuclideanSpace ℝ (Fin n))) (f : S → Fin k)
    (i : Fin k) : EuclideanSpace ℝ (Fin n) :=
  centroidS S (fiber S f i)

/-- The k-means objective of an assignment: `∑ x, ‖x - μ(f x)‖²`. This is the
platform's `kmeansObjective` of the induced partition. -/
noncomputable def obj (S : Finset (EuclideanSpace ℝ (Fin n))) (f : S → Fin k) : ℝ :=
  ∑ x : S, ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (f x)‖ ^ 2

/-- The cost of an assignment against prescribed centers. -/
noncomputable def cost (S : Finset (EuclideanSpace ℝ (Fin n)))
    (μ : Fin k → EuclideanSpace ℝ (Fin n)) (f : S → Fin k) : ℝ :=
  ∑ x : S, ‖(x : EuclideanSpace ℝ (Fin n)) - μ (f x)‖ ^ 2

/-- An argmin of the distance from `x` to the centers `μ`, chosen once and for
all (ties broken by the choice). Needs `Fin k` nonempty. -/
noncomputable def argminDist [NeZero k] (μ : Fin k → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Fin k :=
  Classical.choose
    (Finset.exists_min_image Finset.univ (fun j => ‖x - μ j‖) Finset.univ_nonempty)

/-- One Lloyd step, with the strict-move tie-breaking rule: a point moves to
its argmin center only when that center is STRICTLY nearer than its current
one; on ties it stays. -/
noncomputable def step (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f : S → Fin k) : S → Fin k :=
  fun x =>
    if ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (argminDist (centers S f) x)‖
        < ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (f x)‖
      then argminDist (centers S f) x
      else f x

/-- The orbit of an initial assignment under iteration of `step`. -/
noncomputable def orbit (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f₀ : S → Fin k) (t : ℕ) : S → Fin k :=
  (step S)^[t] f₀

/-- The partition induced by an assignment, as Finsets of points. -/
noncomputable def part (S : Finset (EuclideanSpace ℝ (Fin n))) (f : S → Fin k)
    (i : Fin k) : Finset (EuclideanSpace ℝ (Fin n)) :=
  (fiber S f i).image (fun x : S => (x : EuclideanSpace ℝ (Fin n)))

end LloydConvergence


