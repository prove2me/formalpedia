-- Prove2me | Definitions.Def_AnytimeAdaVR_fStar
-- name    : AnytimeAdaVR_fStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:41.891197+00:00
-- url     : https://prove2.me/theorems/3e46d137-fc53-4dba-8f8d-abd7ddd620e1
-- title:
--   Optimal value $f^* = \inf_x f(x)$
-- statement:
--   For an objective $f:\mathbb R^d\to\mathbb R$, the **optimal value** is
--   $$
--   f^*=\inf_{x\in\mathbb R^d} f(x).
--   $$
--   It enters through the initial gap $f(x_{\mathrm{init}})-f^*\le\Delta_f$ of Assumption 1.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. The value is the real infimum of the range of $f$; it is the true infimum whenever $f$ is bounded below, which Assumption 1 requires explicitly.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §2, p.3

import Mathlib

namespace AnytimeAdaVR

/-- **The optimal value `f* := inf_{x ∈ ℝ^d} f(x)`.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance
Reduction across Smoothness and Noise Conditions* (preprint, 2026), §2, p.3: "`f∗ := inf_{x∈ℝ^d} f(x)`".

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)` (Euclidean norm). The value is the real
`sInf` of the range; it is the paper's infimum whenever the range is bounded below, which
Assumption 1 (`f∗ > −∞`) requires explicitly (`AnytimeAdaVR.Assumption1`). -/
noncomputable def fStar {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  sInf (Set.range f)

end AnytimeAdaVR


