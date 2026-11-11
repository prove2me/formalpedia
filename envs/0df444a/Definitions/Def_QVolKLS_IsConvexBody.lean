-- Prove2me | Definitions.Def_QVolKLS_IsConvexBody
-- name    : QVolKLS_IsConvexBody
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:36:41.7312+00:00
-- url     : https://prove2.me/theorems/72ce503b-83ac-434f-b6a1-2cfcac52d3b7
-- title:
--   Convex bodies, rational and lattice points, the pencil coordinates $(x_0,x')$
-- statement:
--   A **convex body** in $\mathbb R^d$ is a compact convex set with nonempty interior. Throughout, $\mathbb R^d$ carries the Euclidean norm $\|\cdot\|_2$, and $B(x,r)=\{y:\|y-x\|_2<r\}$ is the open Euclidean ball.
--
--   Three coordinate conventions accompany it.
--
--   1. A rational point $x_0\in\mathbb Q^d$ is read as the point of $\mathbb R^d$ with the same coordinates.
--   2. For a spacing $h>0$ and an integer vector $k\in\mathbb Z^D$, the point $hk$ is a point of the lattice $\Lambda=h\mathbb Z^D$.
--   3. A point of $\mathbb R^{d+1}$ is written $x=(x_0,x')$ with $x_0\in\mathbb R$ its first coordinate and $x'\in\mathbb R^d$ the remaining ones; this is how the pencil construction of §6.1 splits coordinates.
--
--   A real number is **dyadic** if it equals $k/2^p$ for some $k\in\mathbb Z$ and $p\in\mathbb N$.
--
--   These are the geometric conventions shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` (abbreviated `Euc d`); `ratPoint`, `latticePt`, `tailE` and `IsDyadic` implement items 1–3 and the dyadic predicate.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §2, p.21 (convex body, balls); §5.1, p.37 (Λ = hℤ^D); §6.1, p.44 (points (x₀, x′))

import Mathlib

set_option autoImplicit false

namespace QVolKLS

/-!
# Convex bodies, rational and lattice points, the pencil coordinates

R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…), §2, p.21 ("A convex body is a compact convex
set with nonempty interior. The Euclidean ball of radius r about x is B(x, r)."), §5.1, p.37
(the lattice `Λ = hℤ^D`) and §6.1, p.44 (points `(x₀, x′)` of `ℝ^{d+1}`).

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)` (abbreviated `Euc d`), so the norm is
the Euclidean norm `‖·‖₂` and `Metric.ball x r` is the open ball `B(x, r)`. A point of
`ℝ^{d+1} = ℝ × ℝ^d` is written `(x₀, x′)`: coordinate `0` is `x₀`, and `tailE x` is `x′`.
-/

/-- The Euclidean space `ℝ^d` with its Euclidean norm. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Zhang, arXiv:2610.04987, §2, p.21: a **convex body** is a compact convex set with nonempty
interior. -/
def IsConvexBody {d : ℕ} (K : Set (Euc d)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- The point of `ℝ^d` with the given rational coordinates (the rational point `x₀` of
Theorem 6.1, p.44). -/
noncomputable def ratPoint {d : ℕ} (x : Fin d → ℚ) : Euc d :=
  WithLp.toLp 2 (fun j => ((x j : ℚ) : ℝ))

/-- Zhang, §5.1, p.37: the point `h k` of the lattice `Λ = hℤ^D` with integer coordinates `k`. -/
noncomputable def latticePt {D : ℕ} (h : ℝ) (k : Fin D → ℤ) : Euc D :=
  WithLp.toLp 2 (fun i => h * (k i : ℝ))

/-- Zhang, §6.1, p.44: the component `x′ ∈ ℝ^d` of a point `x = (x₀, x′) ∈ ℝ^{d+1}`
(coordinates `1, …, d`). The component `x₀` is the coordinate `x 0`. -/
noncomputable def tailE {d : ℕ} (x : Euc (d + 1)) : Euc d :=
  WithLp.toLp 2 (fun j => x (Fin.succ j))

/-- A real number is **dyadic** when it is `k / 2^p` for an integer `k` and a natural `p`. -/
def IsDyadic (x : ℝ) : Prop :=
  ∃ (k : ℤ) (p : ℕ), x = (k : ℝ) / 2 ^ p

end QVolKLS


