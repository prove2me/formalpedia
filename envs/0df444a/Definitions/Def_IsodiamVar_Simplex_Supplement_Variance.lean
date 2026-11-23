-- Prove2me | Definitions.Def_IsodiamVar_Simplex_Supplement_Variance
-- name    : IsodiamVar_Simplex_Supplement_Variance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:45:27.986646+00:00
-- url     : https://prove2.me/theorems/e89b2c53-6e72-4fb5-b845-b5c83cd883de
-- title:
--   Equation (1.2) — classical variance about the barycenter
-- statement:
--   Let $\mu$ be a compactly supported Borel probability on Euclidean $\mathbb R^n$, and write $\bar x(\mu)$ for its barycenter. Its classical variance is
--
--   $$\operatorname{Var}(\mu)=\int_{\mathbb R^n}|x-\bar x(\mu)|^2\,d\mu(x).$$
--
--   This measures squared Euclidean spread about the mean. It is the objective of Theorem 1.1. The already published generalized variance remains an infimum over all centers; it is not redefined here or assumed equal to this integral.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 2, (1.2)

import Definitions.Def_IsodiamVar_Simplex_Supplement_Barycenter

open MeasureTheory

namespace IsodiamVar.Simplex.Supplement

/-- Equation (1.2), p. 2: ordinary variance around the barycenter. -/
noncomputable def variance {n : ℕ} (μ : Measure (E n)) : ℝ :=
  ∫ x, ‖x - barycenter μ‖ ^ 2 ∂μ

end IsodiamVar.Simplex.Supplement


