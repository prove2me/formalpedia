-- Prove2me | Definitions.Def_ShapleyNV_vD
-- name    : ShapleyNV_vD
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:54:37.463226+00:00
-- url     : https://prove2.me/theorems/98ab2d96-b29b-4e4b-a30a-43abf40eac9e
-- title:
--   Dual problem $v_D$
-- statement:
--   The dual problem of (P) is
--
--   $$
--   v_D := \inf_{f \in \mathcal F} \min_{\lambda \ge 0} \Big\{ \lambda\rho + \mathbb E_{(\hat X,\hat Z)\sim\widehat{\mathbb P}}\Big[ \sup_{z \in \mathcal Z, x \in \mathcal X} \big\{ \Psi(f(x), z) - \lambda\|x - \hat X\| - \lambda|z - \hat Z| \big\} \Big] \Big\}. \tag{D}
--   $$
--
--   **Formalization Note** The outer infimum is over all measurable $f \ge 0$.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), (D), p.7

import Mathlib
import Definitions.Def_ShapleyNV_fullDual

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Dual problem** `v_D := inf_{f ∈ ℱ} min_{λ≥0} { λρ + E_P̂[ sup_{z∈𝒵, x∈𝒳} { Ψ(f(x), z) − λ‖x − X̂‖ − λ|z − Ẑ| } ] }`, (D).
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), (D), p.7.

**Formalization Note.** The infimum ranges over all measurable `f : X → ℝ` with `f ≥ 0`. -/
noncomputable def vD {X : Type*} [MetricSpace X] [MeasurableSpace X] (D : Data X) (h b ρ : ℝ) : ℝ≥0∞ :=
  ⨅ f : X → ℝ, ⨅ (_ : Measurable f ∧ ∀ x, 0 ≤ f x), fullDual D h b ρ f

end ShapleyNV


