-- Prove2me | Definitions.Def_ShapleyNV_vP
-- name    : ShapleyNV_vP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:54:39.159902+00:00
-- url     : https://prove2.me/theorems/3a1d34c2-03c4-474e-8b13-f76ae89fa632
-- title:
--   Optimal value $v_P$ of the Wasserstein robust feature-based newsvendor
-- statement:
--   The Wasserstein robust feature-based newsvendor problem is
--
--   $$
--   v_P := \inf_{f \in \mathcal F}\ \sup_{\mathbb P \in \mathcal P_1(\mathcal X \times \mathcal Z)} \Big\{ \mathbb E_{(X,Z)\sim\mathbb P}\big[\Psi(f(X), Z)\big] : \mathcal W(\mathbb P, \widehat{\mathbb P}) \le \rho \Big\}, \tag{P}
--   $$
--
--   where $\mathcal F$ is the set of all measurable functions $f : \mathcal X \to \mathcal Z$.
--
--   **Formalization Note** The infimum is over all measurable $f$ with $f \ge 0$, not only continuous or Lipschitz policies.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), (P), p.6; ℱ = all measurable functions on 𝒳, p.5

import Mathlib
import Definitions.Def_ShapleyNV_fullWorst

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Optimal value of the Wasserstein robust feature-based newsvendor problem**
`v_P := inf_{f ∈ ℱ} sup_{P ∈ 𝒫₁(𝒳×𝒵)} { E_P[Ψ(f(X), Z)] : W(P, P̂) ≤ ρ }`, (P), p.6.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), (P), p.6; `ℱ` is "the set of all measurable functions on 𝒳" (p.5) with values in `𝒵`.

**Formalization Note.** The infimum ranges over **all** measurable `f : X → ℝ` with `f ≥ 0`
(values in `𝒵 = ℝ₊`), not only continuous or Lipschitz ones. -/
noncomputable def vP {X : Type*} [MetricSpace X] [MeasurableSpace X] (D : Data X) (h b ρ : ℝ) : ℝ≥0∞ :=
  ⨅ f : X → ℝ, ⨅ (_ : Measurable f ∧ ∀ x, 0 ≤ f x), fullWorst D h b ρ f

end ShapleyNV


