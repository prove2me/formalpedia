-- Prove2me | Definitions.Def_ShapleyNV_fullDual
-- name    : ShapleyNV_fullDual
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:52:58.519171+00:00
-- url     : https://prove2.me/theorems/d2a4815e-8f0b-4736-a6b9-d3e9b6e3e99e
-- title:
--   Inner dual value $v_D^f$ of a policy $f$
-- statement:
--   For a policy $f$, the inner dual problem of Lemma EC.1 is
--
--   $$
--   v_D^f := \inf_{\lambda \ge 0} \Big( \lambda\rho + \mathbb E_{(\hat X,\hat Z)\sim\widehat{\mathbb P}}\Big[ \sup_{(x,z) \in \mathcal X \times \mathcal Z} \big\{ \Psi(f(x), z) - \lambda(\|x - \hat X\| + |z - \hat Z|) \big\} \Big] \Big).
--   $$
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma EC.1, v_D^f, p.ec1 (PDF 22); inner problem of (D), p.7

import Mathlib
import Definitions.Def_ShapleyNV_nvCost
import Definitions.Def_ShapleyNV_Phat
import Definitions.Def_ShapleyNV_fullCost
import Definitions.Def_ShapleyNV_dualVal

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Inner dual value of a policy**
`v_D^f := inf_{λ≥0} ( λρ + E_{(X̂,Ẑ)∼P̂}[ sup_{(x,z)∈𝒳×𝒵} { Ψ(f(x), z) − λ(‖x − X̂‖ + |z − Ẑ|) } ] )`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma EC.1, p.ec1 (PDF 22); the inner minimization of (D), p.7. -/
noncomputable def fullDual {X : Type*} [MetricSpace X] [MeasurableSpace X] (D : Data X) (h b ρ : ℝ)
    (f : X → ℝ) : ℝ≥0∞ :=
  dualVal fullCost (Phat D) ρ (fun ξ => nvCost h b (f ξ.1) ξ.2)

end ShapleyNV


