-- Prove2me | Definitions.Def_ShapleyNV_inDual
-- name    : ShapleyNV_inDual
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:52:51.189511+00:00
-- url     : https://prove2.me/theorems/2f391c6e-50cd-4d7e-b0c2-b75898288e3e
-- title:
--   Inner in-sample dual value of an in-sample policy $\hat f$
-- statement:
--   For an in-sample policy $\hat f$, the inner part of the in-sample dual problem $(\widehat{\mathrm D})$ is
--
--   $$
--   \inf_{\lambda \ge 0} \Big( \lambda\rho + \mathbb E_{(\hat X,\hat Z)\sim\widehat{\mathbb P}}\Big[ \sup_{z \in \mathcal Z} \max_{x \in \widehat{\mathcal X}} \big\{ \Psi(\hat f(x), z) - \lambda\|x - \hat X\| - \lambda|z - \hat Z| \big\} \Big] \Big).
--   $$
--
--   **Formalization Note** $\hat f$ is the vector $y_k = \hat f(\hat x_k)$ and $\widehat{\mathcal X}$ is indexed by $[K]$.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), objective of (D̂) minimized over λ ≥ 0 for fixed f̂, pp.6–7

import Mathlib
import Definitions.Def_ShapleyNV_nvCost
import Definitions.Def_ShapleyNV_PhatIn
import Definitions.Def_ShapleyNV_inCost
import Definitions.Def_ShapleyNV_dualVal

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Inner in-sample dual value of an in-sample policy**
`inf_{λ≥0} ( λρ + E_{(X̂,Ẑ)∼P̂}[ sup_{z∈𝒵} max_{x∈𝒳̂} { Ψ(f̂(x), z) − λ‖x − X̂‖ − λ|z − Ẑ| } ] )`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), the objective of (D̂) minimized over `λ ≥ 0` for a fixed `f̂`, p.6 and p.7.

**Formalization Note.** `f̂` is the vector `y k = f̂(x̂_k)`; `𝒳̂` is `Fin K`. -/
noncomputable def inDual {X : Type*} [MetricSpace X] (D : Data X) (h b ρ : ℝ) (y : Fin D.K → ℝ) :
    ℝ≥0∞ :=
  dualVal (inCost D) (PhatIn D) ρ (fun ξ => nvCost h b (y ξ.1) ξ.2)

end ShapleyNV


