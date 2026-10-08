-- Prove2me | Definitions.Def_GenEmpLik_Coverage_remainder
-- name    : GenEmpLik_Coverage_remainder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:26:29.803108+00:00
-- url     : https://prove2.me/theorems/6f6bbf8a-c4cc-4073-9ee2-fdf8d70658d6
-- title:
--   Linearization remainder for T_opt
-- statement:
--   For a weighted empirical law $p$, the **linearization remainder** is
--
--   $$\kappa(p)=T_{\rm opt}(p)-T_{\rm opt}(P_0)-\sum_i p_iT^{(1)}(z_i;P_0).$$
--
--   Lemma 16 shows that this remainder is uniformly negligible at the $n^{-1/2}$ scale throughout the divergence ball. The population centering is part of the definition.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 37, Lemma 16, definition of κ

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_optimalValue
import Definitions.Def_GenEmpLik_Coverage_empiricalOptimalValue
import Definitions.Def_GenEmpLik_Coverage_influence

namespace GenEmpLik.Coverage

/-- The linearization remainder κ(P), Appendix B.4, (36)–(37), on empirical weights. -/
noncomputable def remainder {d n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (P₀ : MeasureTheory.Measure Ξ) (xs : EuclideanSpace ℝ (Fin d))
    (z : Fin n → Ξ) (p : Fin n → ℝ) : ℝ :=
  empiricalOptimalValue X ℓ z p - optimalValue X ℓ P₀ -
    ∑ i, p i * influence ℓ xs P₀ (z i)

end GenEmpLik.Coverage


