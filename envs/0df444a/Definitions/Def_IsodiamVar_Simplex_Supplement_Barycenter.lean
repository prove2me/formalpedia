-- Prove2me | Definitions.Def_IsodiamVar_Simplex_Supplement_Barycenter
-- name    : IsodiamVar_Simplex_Supplement_Barycenter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:44:14.578876+00:00
-- url     : https://prove2.me/theorems/8d985700-0550-4f66-b237-43c312f7b4bb
-- title:
--   Equation (1.1) — barycenter of a Borel probability
-- statement:
--   For a Borel probability measure $\mu$ on Euclidean $\mathbb R^n$, its barycenter is
--
--   $$\bar x(\mu)=\int_{\mathbb R^n}x\,d\mu(x).$$
--
--   This is the mean constraint used in the variance bounds and zero-mean duality. All theorem uses have compact support, which guarantees existence of the Bochner integral. The total function is defined for all measures, but its default value on nonintegrable inputs is never used by a theorem.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 2, (1.1)

import Definitions.Def_IsodiamVar_Simplex_Defs

open MeasureTheory

namespace IsodiamVar.Simplex.Supplement

/-- Equation (1.1), p. 2. Compact support in all uses guarantees integrability. -/
noncomputable def barycenter {n : ℕ} (μ : Measure (E n)) : E n := ∫ x, x ∂μ

end IsodiamVar.Simplex.Supplement


