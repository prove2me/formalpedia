-- Prove2me | Definitions.Def_PrefixVR_Supplement_Assumption4
-- name    : PrefixVR_Supplement_Assumption4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:48:50.67327+00:00
-- url     : https://prove2.me/theorems/c069aa45-9e5d-4955-88a2-868b63866dc9
-- title:
--   Assumption 4: the PL condition $\tfrac12\|\nabla f(x)\|^2\ge\mu(f(x)-f_*)$
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ and $f_*=\inf_x f(x)$. **Assumption 4** (the Polyak–Łojasiewicz condition) holds with constant $\mu$ if $\mu>0$ and, for all $x\in\mathbb R^d$,
--   $$
--   \frac12\,\|\nabla f(x)\|^2\ \ge\ \mu\big(f(x)-f_*\big).\qquad(13)
--   $$
--   Under it gradient-type methods converge linearly in function value without convexity; no minimizer needs to exist.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, $\nabla f$ is Mathlib's `gradient`, and $f_*$ is the real infimum `⨅ y, f y`, which is the true infimum when $f$ is bounded below (Assumption 2); the theorems using this definition assume that separately.
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), §5, Assumption 4, Eq. (13), p.8 (PDF p.8)

import Mathlib

namespace PrefixVR.Supplement

/-- **Assumption 4 (the PL condition).** Jiang, Wang, Yang, Li, Zhang, *Memory-efficient
Finite-sum Optimization without Full Gradient Refreshes* (manuscript, sha256 ed33106a…),
Assumption 4, Eq. (13), p.8: "There exists μ > 0 such that, for all x ∈ ℝᵈ,
½‖∇f(x)‖² ≥ μ(f(x) − f_*)."

`Assumption4 f μ` says `0 < μ` and `½‖∇f(x)‖² ≥ μ (f(x) − f_*)` for every `x`, with
`f_* = ⨅ y, f y` (Assumption 2, p.4).

**Formalization Note.** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)` and `∇f` is Mathlib's `gradient`.
The infimum `f_*` is the real infimum `⨅ y, f y`; it is the true infimum when `f` is bounded
below (Assumption 2), which every theorem using this definition assumes separately. No minimizer
is required to exist. -/
def Assumption4 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (μ : ℝ) : Prop :=
  0 < μ ∧ ∀ x : EuclideanSpace ℝ (Fin d), μ * (f x - ⨅ y, f y) ≤ (1 / 2) * ‖gradient f x‖ ^ 2

end PrefixVR.Supplement


