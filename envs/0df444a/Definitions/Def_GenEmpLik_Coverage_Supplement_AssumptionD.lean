-- Prove2me | Definitions.Def_GenEmpLik_Coverage_Supplement_AssumptionD
-- name    : GenEmpLik_Coverage_Supplement_AssumptionD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:09:56.076195+00:00
-- url     : https://prove2.me/theorems/17a882ae-3550-4ddf-9ce1-3b63e4629907
-- title:
--   Assumption D — proper closed convex sample losses
-- statement:
--   Let $X\subset\mathbb R^d$ and let $\ell:X\times\Xi\to\mathbb R$ be a sample loss with population law $P$. Assumption D says
--   $$X\text{ is convex},\qquad \ell(\cdot;z)+I_X\text{ is proper, closed and convex for }P\text{-almost every }z.$$
--   The extension is $+\infty$ outside $X$; convexity is written for the real loss on $X$. This supplies the sample convexity used in robust consistency without imposing a compact domain.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, pp. 12, Assumption D; 48

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_Supplement_AssumptionC

open MeasureTheory

namespace GenEmpLik.Coverage.Supplement

/-- Assumption D, p. 12: proper closed convex sample losses on X. -/
def AssumptionD {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (P : Measure Ξ) : Prop :=
  Convex ℝ X ∧ ∀ᵐ z ∂P,
    DupacovaWets.Consistency.IsProperFn (extendedLoss X ℓ z) ∧
    LowerSemicontinuous (extendedLoss X ℓ z) ∧ ConvexOn ℝ X (fun x => ℓ x z)

end GenEmpLik.Coverage.Supplement


