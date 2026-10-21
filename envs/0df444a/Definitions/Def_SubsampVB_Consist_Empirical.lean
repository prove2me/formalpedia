-- Prove2me | Definitions.Def_SubsampVB_Consist_Empirical
-- name    : SubsampVB_Consist_Empirical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:47.782137+00:00
-- url     : https://prove2.me/theorems/d2b819c0-3c92-4e78-a445-2137cd209a4f
-- title:
--   Empirical measure of a finite sample
-- statement:
--   For a finite sample $z_1,\ldots,z_k$ in a measurable space, the **empirical measure** is
--
--   $$\widehat F_z=\frac1k\sum_{j=1}^{k}\delta_{z_j}.$$
--
--   This is the distribution that assigns equal weight to each observed value. It is the common building block for the observed input models and the resampled input models in Algorithm 2. The source uses this construction on p. 7 and again on pp. 14–15.
--
--   **Formalization Note** The total definition also assigns a zero measure when $k=0$. Every theorem that uses it as a probability distribution requires positive sample size, at least eventually.
-- source:
--   Lam & Qian, Subsampling to enhance efficiency in input uncertainty quantification, arXiv:1811.04500v2, pp. 7, 14–15, empirical input distributions and Algorithm 2

import Mathlib

namespace SubsampVB.Consist

universe u

/-- The empirical probability measure of a finite sample. -/
noncomputable def empirical {α : Type u} [MeasurableSpace α] {k : ℕ} (z : Fin k → α) :
    MeasureTheory.Measure α :=
  (k : ENNReal)⁻¹ • ∑ j : Fin k, MeasureTheory.Measure.dirac (z j)

end SubsampVB.Consist


