-- Prove2me | Definitions.Def_ShapleyNV_vDhat
-- name    : ShapleyNV_vDhat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:53:52.190562+00:00
-- url     : https://prove2.me/theorems/5b14b150-0028-4608-ba61-9bc710e6e14e
-- title:
--   In-sample dual problem $v_{\widehat D}$
-- statement:
--   The in-sample dual problem is
--
--   $$
--   v_{\widehat D} := \min_{\hat f \in \widehat{\mathcal F}, \lambda \ge 0} \Big\{ \lambda\rho + \mathbb E_{(\hat X,\hat Z)\sim\widehat{\mathbb P}}\Big[ \sup_{z \in \mathcal Z} \max_{x \in \widehat{\mathcal X}} \big\{ \Psi(\hat f(x), z) - \lambda\|x - \hat X\| - \lambda|z - \hat Z| \big\} \Big] \Big\}. \tag{$\widehat{\mathrm D}$}
--   $$
--
--   **Formalization Note** Defined as an infimum over vectors $y \in \mathbb R_+^K$.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), (D̂), pp.6–7

import Mathlib
import Definitions.Def_ShapleyNV_inDual

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **In-sample dual problem** `v_D̂ := min_{f̂ ∈ ℱ̂, λ≥0} { λρ + E_P̂[ sup_{z∈𝒵} max_{x∈𝒳̂} { Ψ(f̂(x), z) − λ‖x − X̂‖ − λ|z − Ẑ| } ] }`, (D̂).
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), (D̂), p.6 and p.7.

**Formalization Note.** Defined as an infimum over `y : Fin K → ℝ`, `y ≥ 0`, of `inDual`. -/
noncomputable def vDhat {X : Type*} [MetricSpace X] (D : Data X) (h b ρ : ℝ) : ℝ≥0∞ :=
  ⨅ y : Fin D.K → ℝ, ⨅ (_ : ∀ k, 0 ≤ y k), inDual D h b ρ y

end ShapleyNV


