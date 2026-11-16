-- Prove2me | Definitions.Def_GaussProcSparsify_Optimal_Supplement_Entropy
-- name    : GaussProcSparsify_Optimal_Supplement_Entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:20:41.524014+00:00
-- url     : https://prove2.me/theorems/9e17216a-7e0a-451c-b238-ab715b64b1e2
-- title:
--   Differential entropy of laws and i.i.d. linear images
-- statement:
--   For a probability law $\mu$ with Lebesgue density $f$, having differential entropy $h$ means that $f$ has a measurable nonnegative representative, the signed integral is well-defined, and
--   $$h=-\int f(x)\ln f(x)\,dx.$$
--   The integral is the published extended-real entropy definition: the difference of the nonnegative integrals of the positive and negative parts of $-f\ln f$, with the condition that these parts are not both infinite. The convention is $0\ln0=0$. No finite variance or bounded support is required. A finite real value certifies finite differential entropy; projected entropy may instead equal $+\infty$.
--   For a common coordinate law $\mu$ on $\mathbb R$ and a real $d\times n$ matrix $M$, the i.i.d. linear-image law is
--   $$M_*\mu^{\otimes n}.$$
--   The matrix acts on coordinate functions, and its output is identified with Euclidean $\mathbb R^d$. The map is linear and continuous, so its pushforward is the actual law. This supplies the distributional formulation of Lemma 22 without imposing a model of an underlying probability space.
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), §5.2.1, PDF p. 34 (printed p. 33); entropy arithmetic reused from PsdPermanent_entropy, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Gaussian
import Definitions.Def_PsdPermanent_entropy

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- A law has the stated differential entropy when it has a measurable nonnegative
Lebesgue density with well-defined signed entropy. No moment or support condition.
The signed integral itself is the published PsdPermanent.entropy, PDF p. 34. -/
def HasDifferentialEntropy {E : Type*} [MeasureSpace E] (μ : Measure E) (h : EReal) : Prop :=
  ∃ f : E → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      PsdPermanent.EntropyWellDefined f ∧ PsdPermanent.entropy f = h

/-- The law of Mx for x having independent coordinates with common law μ.
The product measure is on ordinary coordinate functions; the output is Euclidean.
PDF p. 34. -/
noncomputable def iidLinearImage {n d : ℕ} (μ : Measure ℝ)
    (M : Matrix (Fin d) (Fin n) ℝ) : Measure (Vec d) :=
  Measure.map (fun x : Fin n → ℝ => WithLp.toLp 2 (M.mulVec x))
    (Measure.pi (fun _ : Fin n => μ))

end GaussProcSparsify.Optimal.Supplement


