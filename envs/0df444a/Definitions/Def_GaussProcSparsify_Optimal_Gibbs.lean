-- Prove2me | Definitions.Def_GaussProcSparsify_Optimal_Gibbs
-- name    : GaussProcSparsify_Optimal_Gibbs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:28.672244+00:00
-- url     : https://prove2.me/theorems/25c49c56-150d-4c9b-a6b2-85823c276590
-- title:
--   Normalized measure with density proportional to exp(−V)
-- statement:
--   For a real potential $V:\mathbb R^n\to\mathbb R$, let
--   $$Z_V=\int_{\mathbb R^n}e^{-V(x)}\,dx,\qquad d\mu_V(x)=\frac{e^{-V(x)}}{Z_V}\,dx.$$
--   This is Mathlib's exponentially tilted Lebesgue measure. It uses the actual integral, rather than a freely supplied normalizing constant. For $C^2$ potentials satisfying $D^2V(x)[u,u]\ge\|u\|_2^2$, the normalizer is positive and finite; those are hypotheses of Lemma 10, rather than fields built into this definition. Outside the integrable regime Mathlib's tilted measure is zero, a default never relied on by that lemma.
--
--   This construction supplies the strongly log-concave probability laws used in the variance inequality. The underlying exponential tilting operation is reused from Mathlib.
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Lemma 10, PDF p. 13 (printed p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Mathlib
import Definitions.Def_GaussProcSparsify_Optimal_Gaussian

open MeasureTheory

namespace GaussProcSparsify.Optimal

/-- The normalized density proportional to exp(-V) in Lemma 10, PDF p. 13.
Mathlib's tilted measure divides by the actual integral of exp(-V) against volume.
C² and the Hessian lower bound in Lemma 10 guarantee a positive finite normalizer;
no such analytic property is built into this definition. -/
noncomputable def gibbsLaw {n : ℕ} (V : Vec n → ℝ) : Measure (Vec n) :=
  (volume : Measure (Vec n)).tilted (fun x => -V x)

end GaussProcSparsify.Optimal


