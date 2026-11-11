-- Prove2me | Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
-- name    : BallPolyApprox_VertexBudget_VolumeError
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:53:49.285954+00:00
-- url     : https://prove2.me/theorems/e8c9df63-26db-442d-8c71-6354bc28caf7
-- title:
--   Relative volume error $\Delta_d(P)$ (1) and polytopes with at most $N$ vertices in unrestricted position
-- statement:
--   $\mathbb R^d$ carries the Euclidean norm, $B_d=\{x\in\mathbb R^d:\|x\|_2\le1\}$ is the closed unit ball and $|A|=\mathrm{vol}_d(A)$ is Lebesgue measure. For a convex body $K$ and a polytope $P$ in $\mathbb R^d$ the **relative symmetric-difference error** is
--   $$\Delta_K(P)=\frac{|K\triangle P|}{|K|},\qquad \Delta_d(P)=\Delta_{B_d}(P).$$
--   A polytope in **unrestricted position** with at most $N$ vertices is the convex hull $\operatorname{conv}V$ of a finite set $V\subset\mathbb R^d$ with $|V|\le N$: the points may lie anywhere (not necessarily in $B_d$), the hull need not contain the origin, and lower-dimensional hulls are allowed (they have volume $0$ and error $1$). The polytope is **origin-symmetric** when $V=-V$. The minimum vertex budget is $N_\varepsilon(d)=\min\{N\in\mathbb N:\exists P\in\mathcal P_d(N),\ \Delta_d(P)\le\varepsilon\}$; the theorems state bounds on it through the existence of, or a property of every, such $V$.
--
--   **Formalization Note.** The ambient space is `EuclideanSpace ℝ (Fin d)` (on `Fin d → ℝ` the unit ball would be a cube). $\Delta_K(P)$ is `(volume (K ∆ P)).toReal / (volume K).toReal`; for $K=B_d$ and $P$ compact both volumes are finite.
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), (1), p. 1 (PDF 3); §2, p. 3 (PDF 5)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

noncomputable section

/-!
# Relative volume error and polytopes with at most `N` vertices

Gorodzha, Hoehner, Kur, *Approximating the Euclidean Ball by Polytopes*, arXiv:2610.34651
(sha256 164dc885…), (1), p. 1 (PDF 3), and §2, p. 3 (PDF 5).

`B_d = {x ∈ ℝ^d : ‖x‖₂ ≤ 1}` is the closed Euclidean unit ball and `|A| = vol_d(A)` is Lebesgue
measure. For a convex body `K` and a polytope `P`, `Δ_K(P) = |K △ P| / |K|` and
`Δ_d(P) = Δ_{B_d}(P)`. A polytope in `ℝ^d` with at most `N` vertices, in unrestricted position,
is the convex hull of a finite set `V` of at most `N` points of `ℝ^d`, anywhere in `ℝ^d`;
lower-dimensional hulls are allowed (their volume is `0`, so their error is `1`).
-/

/-- Euclidean space `ℝ^d` with the `ℓ²` norm (not `Fin d → ℝ`, whose norm is the sup norm). -/
abbrev Rd (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The closed Euclidean unit ball `B_d`. -/
def unitBall (d : ℕ) : Set (Rd d) := Metric.closedBall 0 1

/-- The relative symmetric-difference error `Δ_K(P) = |K △ P| / |K|` (1), with Lebesgue measure
`volume` on `ℝ^d`. -/
def relErr {d : ℕ} (K P : Set (Rd d)) : ℝ :=
  (volume (symmDiff K P)).toReal / (volume K).toReal

/-- `Δ_d(P) = Δ_{B_d}(P)` (1). -/
def ballErr {d : ℕ} (P : Set (Rd d)) : ℝ := relErr (unitBall d) P

/-- The polytope `conv V` spanned by a finite point set `V ⊂ ℝ^d`. A polytope has at most `N`
vertices exactly when it is `polytope V` for some `V` with `V.card ≤ N`. -/
def polytope {d : ℕ} (V : Finset (Rd d)) : Set (Rd d) := convexHull ℝ (V : Set (Rd d))

/-- The point set `V` is origin-symmetric (`V = −V`), so `conv V` is an origin-symmetric
polytope. -/
def IsOriginSymmetric {d : ℕ} (V : Finset (Rd d)) : Prop := ∀ v ∈ V, -v ∈ V

end

end BallPolyApprox.VertexBudget


