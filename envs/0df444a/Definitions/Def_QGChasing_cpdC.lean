-- Prove2me | Definitions.Def_QGChasing_cpdC
-- name    : QGChasing_cpdC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:58.577007+00:00
-- url     : https://prove2.me/theorems/ea0da157-36e1-4794-a692-cc6120f5be1d
-- title:
--   Competitive ratio $C=\frac{32}{7}(1+\kappa^{1/3})$, Eq. (3)
-- statement:
--   The competitive ratio achieved by Clipped Proximal Descent is
--   $$
--   C=\frac{32}{7}\big(1+\kappa^{1/3}\big),
--   $$
--   which equals $\frac{8(2+4r)}{7r}$ with $r=\frac1{2\kappa^{1/3}}$. It is the constant of Theorem 1.1.
--
--   **Formalization Note** $\kappa^{1/3}$ is the real power `κ ^ (1/3 : ℝ)`. The second form of (3) is a consequence, not part of the definition.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Eq. (3), p.6; Theorem 1.1, p.2

import Mathlib

namespace QGChasing

/-- The competitive ratio `C = (32/7)(1 + κ^{1/3})` of CPD (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), Eq. (3), p.6, and
Theorem 1.1, p.2).

**Formalization Note** `κ^{1/3}` is `Real.rpow κ (1/3)`. The equal form `8(2 + 4r)/(7r)` of (3)
is not built in. -/
noncomputable def cpdC (κ : ℝ) : ℝ := 32 / 7 * (1 + κ ^ (1 / 3 : ℝ))

end QGChasing


