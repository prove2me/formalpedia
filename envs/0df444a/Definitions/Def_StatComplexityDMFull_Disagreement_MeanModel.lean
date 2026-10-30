-- Prove2me | Definitions.Def_StatComplexityDMFull_Disagreement_MeanModel
-- name    : StatComplexityDMFull_Disagreement_MeanModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:52:46.996714+00:00
-- url     : https://prove2.me/theorems/f8135d7e-09be-4b03-9e40-3078dcb7e8a8
-- title:
--   Bounded mean rewards, selected optimizers and shifted classes
-- statement:
--   Let $\mathcal M$ index models and let $\Pi$ be the decision space. Mean-reward data consist of a measurable function $f^M:\Pi\to[0,1]$ for each $M\in\mathcal M$, together with one selected maximizing decision $\pi_M$. Thus
--
--   $$f^M(\pi)\le f^M(\pi_M)\quad(M\in\mathcal M,\ \pi\in\Pi).$$
--
--   The actual model-induced class and its pointwise shift are
--
--   $$\mathcal F_{\mathcal M}=\{f^M:M\in\mathcal M\},\qquad
--   \mathcal F-g=\{\pi\mapsto f(\pi)-g(\pi):f\in\mathcal F\}.$$
--
--   These data are sufficient for the square-loss result. Each source reward-observation kernel supplies $f^M(\pi)=\mathbb E_{M(\pi)}r$ and the selected optimizer already presupposed by the source. The abstraction admits any such mean data without imposing additional conditions on the kernels, the decision space, or the tie-breaking rule. Maximizer existence is retained; uniqueness and compactness are not assumed.
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, p. 5, model means, selected argmax and induced class; p. 9, kernels; p. 41, bounded rewards; p. 45, shifted classes

import Mathlib

set_option autoImplicit false

namespace StatComplexityDMFull.Disagreement

/-- Mean-reward data of the source models. No reward-observation kernel is needed by (72).
Every source kernel supplies these measurable bounded means and its selected argmax. -/
structure MeanModel (M A : Type*) [MeasurableSpace A] where
  mean : M → A → ℝ
  optimal : M → A
  range : ∀ m a, 0 ≤ mean m a ∧ mean m a ≤ 1
  measurable : ∀ m, Measurable (mean m)
  maximizing : ∀ m a, mean m a ≤ mean m (optimal m)

/-- The actual induced mean class, not an unrelated ambient function class. -/
def meanClass {M A : Type*} [MeasurableSpace A] (D : MeanModel M A) : Set (A → ℝ) :=
  Set.range D.mean

/-- Pointwise subtraction uses the sign in the source's F - g. -/
def shiftClass {A : Type*} (F : Set (A → ℝ)) (g : A → ℝ) : Set (A → ℝ) :=
  (fun f a => f a - g a) '' F

end StatComplexityDMFull.Disagreement


