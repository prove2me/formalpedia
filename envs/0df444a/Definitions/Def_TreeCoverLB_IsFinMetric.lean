-- Prove2me | Definitions.Def_TreeCoverLB_IsFinMetric
-- name    : TreeCoverLB_IsFinMetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:21:58.135416+00:00
-- url     : https://prove2.me/theorems/885a7fc9-5b6c-4fcf-9730-95273bc4ab08
-- title:
--   Finite metric $d : X \times X \to \mathbb R$
-- statement:
--   A **finite metric** on a point set $X$ is a function $d : X \times X \to \mathbb R$ with
--   $$
--   d(x,x)=0,\qquad d(x,y)>0\ (x\neq y),\qquad d(x,y)=d(y,x),\qquad d(x,z)\le d(x,y)+d(y,z).
--   $$
--   An $n$-point metric space is the set $\{0,\dots,n-1\}$ with such a function.
--
--   **Formalization Note** The metric is a bare function, not a `MetricSpace` instance, because Mathlib's instance on `Fin n` is the fixed metric $|i-j|$. Every $n$-point metric space is isometric to one of this form.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), §1, p.1 (PDF p.3): an n-point metric space (X, d_X)

import Mathlib

namespace TreeCoverLB

/-- A **finite metric** on a point set `X`: a distance function `d : X → X → ℝ` with
`d x x = 0`, `d x y > 0` for `x ≠ y`, symmetry and the triangle inequality
(Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §1, p.1 (PDF p.3): "an n-point metric space (X, d_X)").

**Formalization Note** The metric is a bare function rather than a `MetricSpace` instance, so that
an `n`-point metric space is `Fin n` with such a function (Mathlib's `MetricSpace (Fin n)` instance
is the fixed metric `|i − j|`). Every `n`-point metric space is isometric to one of this form via a
bijection with `Fin n`. -/
def IsFinMetric {X : Type*} (d : X → X → ℝ) : Prop :=
  (∀ x, d x x = 0) ∧ (∀ x y, x ≠ y → 0 < d x y) ∧ (∀ x y, d x y = d y x) ∧
    (∀ x y z, d x z ≤ d x y + d y z)

end TreeCoverLB


