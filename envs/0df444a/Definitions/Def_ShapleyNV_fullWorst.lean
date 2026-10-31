-- Prove2me | Definitions.Def_ShapleyNV_fullWorst
-- name    : ShapleyNV_fullWorst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:53:26.889404+00:00
-- url     : https://prove2.me/theorems/a35b852a-2655-437a-923f-488dede06707
-- title:
--   Inner primal value $v_P^f$ of a policy $f$
-- statement:
--   For a policy $f : \mathcal X \to \mathbb R$, its worst-case expected newsvendor cost over the Wasserstein ball of radius $\rho$ around $\widehat{\mathbb P}$ is
--
--   $$
--   v_P^f := \sup_{\mathbb P \in \mathcal P_1(\mathcal X \times \mathcal Z)} \Big\{ \mathbb E_{(X,Z)\sim\mathbb P}\big[\Psi(f(X), Z)\big] : \mathcal W(\mathbb P, \widehat{\mathbb P}) \le \rho \Big\}.
--   $$
--
--   **Formalization Note** That $f$ is measurable with values in $\mathcal Z = \mathbb R_+$ ($f \in \mathcal F$) is a hypothesis of the theorems that need it.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma EC.1, v_P^f, p.ec1 (PDF 22); inner problem of (P), p.6

import Mathlib
import Definitions.Def_ShapleyNV_nvCost
import Definitions.Def_ShapleyNV_Phat
import Definitions.Def_ShapleyNV_fullCost
import Definitions.Def_ShapleyNV_worstCase

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Inner primal value of a policy** `v_P^f := sup_{P ∈ 𝒫₁(𝒳×𝒵)} { E_P[Ψ(f(X), Z)] : W(P, P̂) ≤ ρ }`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma EC.1, p.ec1 (PDF 22); the inner problem of (P), p.6.

**Formalization Note.** A policy is a function `f : X → ℝ`; that it is measurable and takes values
in `𝒵 = ℝ₊` is a hypothesis wherever the paper requires `f ∈ ℱ`. -/
noncomputable def fullWorst {X : Type*} [MetricSpace X] [MeasurableSpace X] (D : Data X) (h b ρ : ℝ)
    (f : X → ℝ) : ℝ≥0∞ :=
  worstCase fullCost (Phat D) ρ (fun ξ => nvCost h b (f ξ.1) ξ.2)

end ShapleyNV


