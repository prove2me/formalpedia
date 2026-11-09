-- Prove2me | Definitions.Def_ZonotopeContainment_AdaptiveSampling_LocalGaussian
-- name    : ZonotopeContainment_AdaptiveSampling_LocalGaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:17:57.211488+00:00
-- url     : https://prove2.me/theorems/9454f6cd-d214-44d1-b5b7-ba8c03465e27
-- title:
--   Alignment event, conditional mean and good-update inequalities
-- statement:
--   For a current generator family $v$, a nonzero functional $b\in\mathbb R^d$, and parameters $C,\lambda$, take a standard Gaussian vector $z$ and the local sample $x(z)$ of Algorithm 1. Define
--   $$E=\left\{z:\frac{\sqrt{\log d}}{C\lambda}\le\left\langle z,\frac b{\|b\|}\right\rangle\le\frac{\sqrt{\log d}}{C\lambda}+1\right\},\qquad \mu=\frac1{\mathbb P(E)}\int_E\langle b,x(z)\rangle\,d\mathbb P(z).$$
--   Let $S$ and $v^+$ be the algorithm's weighted matrix and updated generators, $b^+=S^{1/2}b$, $H=h_{Z(v)}(b)$ and $H^+=h_{Z(v^+)}(b^+)$. An update is good precisely when
--   $$\|b^+\|^2\le\frac{8C^2\lambda^2}{\sqrt{\log d}}\|b\|\mu,\qquad H-H^+\le\frac{4H}{C\lambda}+4\mu.$$
--   These definitions assert no positivity or probability guarantee; Lemma 2.4 supplies those conclusions. The event is a measurable Gaussian slab. The local sample has bounded norm for fixed generators, so the restricted integral is integrable.
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), §2.2, p. 7, and equation (4), p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm

noncomputable section
open MeasureTheory ProbabilityTheory

open scoped MatrixOrder

namespace ZonotopeContainment.AdaptiveSampling

/-- The event E on p. 7. -/
def alignmentEvent {d : ℕ} (C lam : ℝ) (b : E d) : Set (E d) :=
  {z | Real.sqrt (Real.log d) / (C * lam) ≤ inner ℝ z (‖b‖⁻¹ • b) ∧
    inner ℝ z (‖b‖⁻¹ • b) ≤ Real.sqrt (Real.log d) / (C * lam) + 1}

/-- Conditional mean given E; the lemma proves that E has positive probability. -/
def conditionalMean {d n : ℕ} (C lam : ℝ) (v : Fin n → E d) (b : E d) : ℝ :=
  (stdGaussian (E d) (alignmentEvent C lam b)).toReal⁻¹ *
    ∫ z in alignmentEvent C lam b, inner ℝ b (localPoint C lam v z) ∂stdGaussian (E d)

/-- Exactly the two inequalities (4), without any probability assertion built in. -/
def GoodUpdate {d n : ℕ} (C lam : ℝ) (v : Fin n → E d) (b z : E d) : Prop :=
  let r := weights C lam v z
  let bplus := act (CFC.sqrt (weightedMatrix v r)) b
  let μ := conditionalMean C lam v b
  ‖bplus‖ ^ 2 ≤ (8 * C ^ 2 * lam ^ 2 / Real.sqrt (Real.log d)) * ‖b‖ * μ ∧
    support v b - support (updatedGenerators v r) bplus ≤
      4 * support v b / (C * lam) + 4 * μ

end ZonotopeContainment.AdaptiveSampling


