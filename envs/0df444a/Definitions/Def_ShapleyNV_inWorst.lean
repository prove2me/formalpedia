-- Prove2me | Definitions.Def_ShapleyNV_inWorst
-- name    : ShapleyNV_inWorst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:53:10.976815+00:00
-- url     : https://prove2.me/theorems/7bf0ac97-bd7d-4731-a198-0aa168a59a23
-- title:
--   Inner in-sample primal value of an in-sample policy $\hat f$
-- statement:
--   For an in-sample policy $\hat f : \widehat{\mathcal X} \to \mathcal Z$, its worst-case expected cost over the Wasserstein ball of radius $\rho$ around $\widehat{\mathbb P}$ **on the in-sample space** $\widehat{\mathcal X} \times \mathcal Z$ is
--
--   $$
--   \sup_{\mathbb P \in \mathcal P_1(\widehat{\mathcal X} \times \mathcal Z)} \Big\{ \mathbb E_{(X,Z)\sim\mathbb P}\big[\Psi(\hat f(X), Z)\big] : \mathcal W(\mathbb P, \widehat{\mathbb P}) \le \rho \Big\}.
--   $$
--
--   **Formalization Note** An in-sample policy is the vector $y_k = \hat f(\hat x_k)$, $k \in [K]$ (Remark 1: $\widehat{\mathcal F} \subset \mathbb R_+^K$).
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Theorem 1 (I), inner supremum of (P̂), p.6

import Mathlib
import Definitions.Def_ShapleyNV_nvCost
import Definitions.Def_ShapleyNV_PhatIn
import Definitions.Def_ShapleyNV_inCost
import Definitions.Def_ShapleyNV_worstCase

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Inner in-sample primal value of an in-sample policy**
`sup_{P ∈ 𝒫₁(𝒳̂×𝒵)} { E_P[Ψ(f̂(X), Z)] : W(P, P̂) ≤ ρ }`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Theorem 1 (I), the inner supremum of (P̂), p.6.

**Formalization Note.** An in-sample policy `f̂ : 𝒳̂ → 𝒵` is the vector `y k = f̂(x̂_k)`
(Remark 1, p.6: `ℱ̂ ⊂ ℝ₊^K`); its nonnegativity is a hypothesis where needed. -/
noncomputable def inWorst {X : Type*} [MetricSpace X] (D : Data X) (h b ρ : ℝ) (y : Fin D.K → ℝ) :
    ℝ≥0∞ :=
  worstCase (inCost D) (PhatIn D) ρ (fun ξ => nvCost h b (y ξ.1) ξ.2)

end ShapleyNV


