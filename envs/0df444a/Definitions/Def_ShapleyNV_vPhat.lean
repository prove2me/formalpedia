-- Prove2me | Definitions.Def_ShapleyNV_vPhat
-- name    : ShapleyNV_vPhat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:54:30.616445+00:00
-- url     : https://prove2.me/theorems/62737086-e5da-4620-a055-4a272d97a010
-- title:
--   Optimal value $v_{\widehat P}$ of the in-sample robust problem
-- statement:
--   The in-sample robust problem only assigns orders to the observed features:
--
--   $$
--   v_{\widehat P} := \min_{\hat f : \widehat{\mathcal X} \to \mathcal Z}\ \sup_{\mathbb P \in \mathcal P_1(\widehat{\mathcal X} \times \mathcal Z)} \Big\{ \mathbb E_{(X,Z)\sim\mathbb P}\big[\Psi(\hat f(X), Z)\big] : \mathcal W(\mathbb P, \widehat{\mathbb P}) \le \rho \Big\}. \tag{$\widehat{\mathrm P}$}
--   $$
--
--   **Formalization Note** Defined as the infimum over vectors $y \in \mathbb R_+^K$; that the minimum is attained is part of Theorem 1.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Theorem 1 (I), (P̂), p.6

import Mathlib
import Definitions.Def_ShapleyNV_inWorst

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Optimal value of the in-sample robust problem**
`v_P̂ := min_{f̂ : 𝒳̂ → 𝒵} sup_{P ∈ 𝒫₁(𝒳̂×𝒵)} { E_P[Ψ(f̂(X), Z)] : W(P, P̂) ≤ ρ }`, (P̂), p.6.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Theorem 1 (I), (P̂), p.6.

**Formalization Note.** Defined as an infimum over in-sample policies `y : Fin K → ℝ` with `y ≥ 0`;
that the infimum is attained (the paper's "min") is a clause of `ShapleyNV.theorem_1`. -/
noncomputable def vPhat {X : Type*} [MetricSpace X] (D : Data X) (h b ρ : ℝ) : ℝ≥0∞ :=
  ⨅ y : Fin D.K → ℝ, ⨅ (_ : ∀ k, 0 ≤ y k), inWorst D h b ρ y

end ShapleyNV


