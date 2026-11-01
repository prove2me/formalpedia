-- Prove2me | Definitions.Def_TSDRiem_RiemSetting
-- name    : TSDRiem_RiemSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:32.886619+00:00
-- url     : https://prove2.me/theorems/fa72b53f-2fda-4c28-b3e2-1983a0cb29b8
-- title:
--   Abstract Riemannian setting — metric space, tangent fibres, exponential map, isometric transports (§2)
-- statement:
--   The analysis of tangent subspace descent uses a Riemannian manifold $M$ only through a few facts recalled in §2. This definition packages exactly those facts.
--
--   A **Riemannian setting** on a metric space $(M,d)$ consists of:
--
--   1. for every point $x\in M$, a real inner product space $T_xM$ (the tangent space), with inner product $\langle\cdot,\cdot\rangle_x$ and norm $\|\cdot\|_x$;
--   2. an **exponential map** $\operatorname{Exp}_x : T_xM\to M$ for every $x$;
--   3. for every $x$, every $v\in T_xM$ and $y=\operatorname{Exp}_x(v)$, a linear isometric isomorphism $\Gamma^y_x : T_xM\to T_yM$ (parallel transport along the geodesic $t\mapsto\operatorname{Exp}_x(tv)$), which may depend on $v$;
--
--   subject to two axioms: for all $x\in M$ and $v\in T_xM$,
--
--   $$
--   \text{(A1)}\quad d\big(x,\operatorname{Exp}_x(v)\big)\le\|v\|_x,
--   \qquad\qquad
--   \text{(A2)}\quad \forall\, y\in M\ \ \exists\, v\in T_xM:\ \operatorname{Exp}_x(v)=y,\ \ \|v\|_x=d(x,y).
--   $$
--
--   Every connected, geodesically complete Riemannian manifold, with its Riemannian distance, exponential map and parallel transport, is a Riemannian setting: (A1) is the inequality $\|v\|_x\ge d(x,\operatorname{Exp}_x(v))$ of p.4, (A2) is the existence of a minimizing geodesic between any two points (p.4), and parallel transport is an invertible linear isometry (pp.4–5). Euclidean space with $\operatorname{Exp}_x(v)=x+v$ and $\Gamma=\mathrm{id}$ is the simplest instance.
--
--   **Formalization Note** Mathlib has no exponential map or parallel transport on Riemannian manifolds, so the mission states its results for this abstract structure. The transport is indexed by a proof of $\operatorname{Exp}_x(v)=y$, so vectors are never cast between different tangent spaces. Finite dimensionality of the tangent spaces is assumed separately where it is used.
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, §2, pp.4–5 (Riemannian distance, exponential map, inverse exponential map, parallel transport)

import Mathlib

namespace TSDRiem

/-- The Riemannian setting of §2 (pp.4–5), in abstract form: a metric space `M` (the manifold
with its Riemannian distance `d = dist`), a real inner product space `T x` at every point (the
tangent space `T_xM` with `⟨·,·⟩_x` and `‖·‖_x`), an exponential map `exp x : T x → M`, and, for
every `v : T x` with `exp x v = y`, a linear isometry `transport x y v h : T x ≃ T y` (the parallel
transport `Γ^y_x` along the geodesic `t ↦ Exp_x(tv)`).

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, §2, pp.4–5.

Axioms, both §2 facts stated on p.4:
* (A1) `dist_exp_le`: `d(x, Exp_x(v)) ≤ ‖v‖_x` for every `v ∈ T_xM`;
* (A2) `exists_minimizing`: for all `x, y` there is `v ∈ T_xM` with `Exp_x(v) = y` and
  `‖v‖_x = d(x, y)` ("we can find a geodesic γ between them such that L(γ) = d(x, y)", and
  "for any v ∈ Exp⁻¹_x(y), d(x, y) = ‖v‖_x").

Formalization Note: Mathlib has no exponential map or parallel transport, so this structure
abstracts them. Every connected, geodesically complete Riemannian manifold (the paper's standing
setting) is an instance, with `transport` its parallel transport along `t ↦ Exp_x(tv)`, which is a
linear isometry (p.4). The transport is indexed by the equation `exp x v = y`, so no cast between
fibres is ever needed; it depends on `v`, as the paper notes on p.5. Finite dimensionality of the
fibres is assumed separately where it is used. -/
structure RiemSetting (M : Type*) [MetricSpace M] (T : M → Type*)
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)] where
  /-- The exponential map `Exp_x : T_xM → M`. -/
  exp : (x : M) → T x → M
  /-- Parallel transport `Γ^y_x : T_xM → T_yM` along `t ↦ Exp_x(tv)`, for `y = Exp_x(v)`. -/
  transport : (x y : M) → (v : T x) → exp x v = y → T x ≃ₗᵢ[ℝ] T y
  /-- (A1): `d(x, Exp_x(v)) ≤ ‖v‖_x`. -/
  dist_exp_le : ∀ (x : M) (v : T x), dist x (exp x v) ≤ ‖v‖
  /-- (A2): a minimizing geodesic joins any two points. -/
  exists_minimizing : ∀ x y : M, ∃ v : T x, exp x v = y ∧ ‖v‖ = dist x y

end TSDRiem


