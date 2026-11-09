-- Prove2me | Definitions.Def_MaskingHardness_IsDist
-- name    : MaskingHardness_IsDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:45.490496+00:00
-- url     : https://prove2.me/theorems/40a2b530-350e-486c-b636-8902d9402ee0
-- title:
--   A distribution $\mathcal D$ on a finite set $\mathcal X\times\mathcal Y$
-- statement:
--   A **distribution** $\mathcal D$ over labeled data points $(x,y)\in\mathcal X\times\mathcal Y$, for finite $\mathcal X,\mathcal Y$, is given by weights $\mathcal D(x,y)\ge 0$ with
--
--   $$
--   \sum_{x\in\mathcal X}\sum_{y\in\mathcal Y}\mathcal D(x,y)=1 .
--   $$
--
--   Expectations are weighted sums, $\mathbb E[f(x,y)]=\sum_{x,y}\mathcal D(x,y)\,f(x,y)$. Pairs of probability zero are allowed.
--
--   **Formalization Note** The distribution is a function `D : X → Y → ℝ` with the two properties above, rather than a `PMF`, so that expectations are plain finite sums.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 1.3, p.5 (PDF p.7); Theorem 1.9, p.6 (PDF p.8); Theorem 3.3, p.21 (PDF p.23)

import Mathlib

namespace MaskingHardness

/-- **A distribution over labeled data points** `(x, y) ∈ X × Y` (Gopalan–Prabhakaran–Tankala,
*Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d,
Definition 1.3 and Theorem 1.9, printed pp.5–6 = PDF pp.7–8): nonnegative weights `D(x, y)`
summing to `1`.

**Formalization Note** Zero-probability pairs are allowed. Expectations are the weighted finite
sums `E[f(x, y)] = ∑ₓ ∑_y D(x, y) f(x, y)`. -/
def IsDist {X Y : Type*} [Fintype X] [Fintype Y] (D : X → Y → ℝ) : Prop :=
  (∀ x y, 0 ≤ D x y) ∧ ∑ x, ∑ y, D x y = 1

end MaskingHardness


