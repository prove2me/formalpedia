-- Prove2me | Definitions.Def_PLIAG_IsLegendre
-- name    : PLIAG_IsLegendre
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:35.761589+00:00
-- url     : https://prove2.me/theorems/b4f345bb-9fab-4952-b8f8-08f6a2a0ecae
-- title:
--   Legendre function (essentially smooth and strictly convex on $\operatorname{int}\operatorname{dom}w$)
-- statement:
--   Let $w:\mathbb R^d\to(-\infty,+\infty]$ be a proper, lower semicontinuous, convex function. It is **essentially smooth** if
--
--   1. $\operatorname{int}\operatorname{dom}w\neq\emptyset$,
--   2. $w$ is differentiable on $\operatorname{int}\operatorname{dom}w$, and
--   3. $\|\nabla w(x_k)\|\to\infty$ for every sequence $\{x_k\}_{k\ge0}\subseteq\operatorname{int}\operatorname{dom}w$ converging to a boundary point of $\operatorname{dom}w$.
--
--   It is a **Legendre function** if it is essentially smooth and strictly convex on $\operatorname{int}\operatorname{dom}w$.
--
--   The Legendre function $w$ is the "distance-generating" function of the method: the constraint set is $\mathcal Q=\overline{\operatorname{dom}w}$ and the proximal term of every subproblem is the Bregman distance $D_w$. Examples are $\tfrac12\|x\|^2$ on $\mathbb R^d$ and Burg's entropy $-\sum_j\log x_j$ on $\mathbb R^d_{++}$.
--
--   **Formalization Note** "Proper lsc convex" is the published `TensorAHPE.IsProperClosedConvex` (never $-\infty$, not identically $+\infty$, lower semicontinuous, convex epigraph). On the open set $\operatorname{int}\operatorname{dom}w$ the function is finite, so differentiability, the gradient and strict convexity are stated for the real function $x\mapsto w(x)$ there (`(w x).toReal`). A boundary point of $\operatorname{dom}w$ is a point of its topological frontier.
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, §2, p.5 (definition of essentially smooth and Legendre functions)

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_TensorAHPE_IsProperClosedConvex

open Filter Topology

namespace PLIAG

/-- **Legendre function** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, §2, p.5). A proper lsc convex
`φ : ℝ^d → (−∞, +∞]` is *essentially smooth* if `int dom φ ≠ ∅`, `φ` is differentiable on
`int dom φ`, and `‖∇φ(x_k)‖ → ∞` for every sequence `{x_k} ⊆ int dom φ` converging to a boundary
point of `dom φ`; it is *of Legendre type* if it is essentially smooth and strictly convex on
`int dom φ`.

**Formalization Note.** Values are `EReal`; "proper lsc convex" is the published
`TensorAHPE.IsProperClosedConvex` (never `−∞`, not identically `+∞`, lower semicontinuous, convex
epigraph). On the open set `int dom w` the function is finite, so differentiability, the gradient
and strict convexity are those of the real function `x ↦ (w x).toReal`, which agrees with `w`
there. "Boundary point of `dom φ`" is a point of `frontier (AubinLipschitz.effDom w)`. -/
def IsLegendre {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal) : Prop :=
  TensorAHPE.IsProperClosedConvex w ∧
  (interior (AubinLipschitz.effDom w)).Nonempty ∧
  DifferentiableOn ℝ (fun x => (w x).toReal) (interior (AubinLipschitz.effDom w)) ∧
  (∀ (u : ℕ → EuclideanSpace ℝ (Fin d)) (xb : EuclideanSpace ℝ (Fin d)),
    xb ∈ frontier (AubinLipschitz.effDom w) → (∀ k, u k ∈ interior (AubinLipschitz.effDom w)) → Tendsto u atTop (𝓝 xb) →
      Tendsto (fun k => ‖gradient (fun y => (w y).toReal) (u k)‖) atTop atTop) ∧
  StrictConvexOn ℝ (interior (AubinLipschitz.effDom w)) (fun x => (w x).toReal)

end PLIAG


