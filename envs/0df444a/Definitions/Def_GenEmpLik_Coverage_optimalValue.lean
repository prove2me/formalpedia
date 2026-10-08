-- Prove2me | Definitions.Def_GenEmpLik_Coverage_optimalValue
-- name    : GenEmpLik_Coverage_optimalValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:03:55.95607+00:00
-- url     : https://prove2.me/theorems/f88a27dc-580c-4fa4-b6f0-4c91b0acf618
-- title:
--   Population optimal-value functional
-- statement:
--   For a probability distribution $P$ on observations, a decision set $\mathcal X$, and a real loss $\ell$, the optimal-value functional is
--
--   $$T_{\rm opt}(P)=\inf_{x\in\mathcal X}\mathbb E_P[\ell(x;\xi)].$$
--
--   It is the population quantity for which Theorem 3 constructs a confidence set. The theorem's compactness, nonemptiness, integrability, and Lipschitz hypotheses make the real infimum a finite attained value.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 8, definition of T_opt

import Mathlib

namespace GenEmpLik.Coverage

/-- The optimal-value functional T_opt(P), p. 8. -/
noncomputable def optimalValue {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (P : MeasureTheory.Measure Ξ) : ℝ :=
  sInf ((fun x => ∫ z, ℓ x z ∂P) '' X)

end GenEmpLik.Coverage


