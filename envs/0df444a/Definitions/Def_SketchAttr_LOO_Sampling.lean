-- Prove2me | Definitions.Def_SketchAttr_LOO_Sampling
-- name    : SketchAttr_LOO_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:28:16.206947+00:00
-- url     : https://prove2.me/theorems/bbca6d7e-b5b9-479c-a202-5f6a64a74a61
-- title:
--   Section 3.1 — standard complex Gaussian vectors and tapes
-- statement:
--   A standard complex Gaussian is the law of
--   $$g=(a+ib)/\sqrt2,$$
--   where $a$ and $b$ are independent standard real Gaussians. A standard complex Gaussian vector has independent coordinates of this law. The random tape is an infinite sequence of independent samples with the same scalar law.
--
--   These are the probability laws used in the Gaussian tensor moment lemma and the goal's failure event. The scalar law is a measurable pushforward of the product of two standard real Gaussian laws, vectors are represented in Euclidean coordinates, and the tape uses the infinite product measure. Probability-measure instances for all three laws are proved in this definition module, so the infinite product cannot silently take a zero default value.
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), p. 9, Section 3.1, Complex Gaussians; p. 16, Algorithm 1, line 2; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib
import Definitions.Def_SketchAttr_LOO_Taylor

namespace SketchAttr.LOO
open MeasureTheory ProbabilityTheory

noncomputable def complexGaussian : Measure ℂ :=
  Measure.map (fun ab : ℝ × ℝ => ((ab.1 : ℂ) + Complex.I * (ab.2 : ℂ)) / (Real.sqrt 2 : ℂ))
    ((gaussianReal 0 1).prod (gaussianReal 0 1))

instance complexGaussian_probability : IsProbabilityMeasure complexGaussian := by
  unfold complexGaussian
  apply Measure.isProbabilityMeasure_map
  fun_prop

noncomputable def gaussianVector (n : ℕ) : Measure (Vec n) :=
  Measure.map (WithLp.toLp 2) (Measure.pi fun _ : Fin n => complexGaussian)

instance gaussianVector_probability (n : ℕ) : IsProbabilityMeasure (gaussianVector n) := by
  unfold gaussianVector
  apply Measure.isProbabilityMeasure_map
  fun_prop

/-- Every finite prefix consists of independent standard complex normals. -/
noncomputable def gaussianTape : Measure (ℕ → ℂ) :=
  Measure.infinitePi (fun _ : ℕ => complexGaussian)

instance gaussianTape_probability : IsProbabilityMeasure gaussianTape := by
  unfold gaussianTape
  infer_instance

end SketchAttr.LOO


