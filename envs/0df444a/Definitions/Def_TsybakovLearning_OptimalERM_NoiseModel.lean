-- Prove2me | Definitions.Def_TsybakovLearning_OptimalERM_NoiseModel
-- name    : TsybakovLearning_OptimalERM_NoiseModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:08.741407+00:00
-- url     : https://prove2.me/theorems/25269461-1619-4ebc-a6a4-4636a292132d
-- title:
--   Definition 1 — Tsybakov noise and binary Bayes classification
-- statement:
--   Fix a probability law $D$ on an arbitrary measurable space $X\times\{0,1\}$. A regression version $\eta_D:X\to[0,1]$ is measurable and satisfies, for every measurable $A\subseteq X$,
--
--   $$D(A\times\{1\})=\int_A\eta_D(x)\,dD_X(x).$$
--
--   The Bayes prediction is $h_D^*(x)=\mathbf1\{\eta_D(x)\ge1/2\}$, including prediction 1 at equality. For $a\ge1$ and $0<\alpha<1$, the Tsybakov condition means $h_D^*\in H$ and
--
--   $$D_X\{|\eta_D-1/2|\le t\}\le a't^{\alpha/(1-\alpha)}\quad\text{for every real }t>0,\qquad a'=(1-\alpha)(2\alpha)^{\alpha/(1-\alpha)}a^{1/(1-\alpha)}.$$
--
--   This fixes the exact normalization needed for the noise-parameter dependence of the upper bound. The Bernstein disagreement condition mentioned in the footnote is a consequence and is not used as a replacement definition.
--
--   **Formalization Note** Regression stores the version and its defining identity, not an unrelated free function. Binary labels permit a Radon–Nikodym construction on arbitrary measurable X; no standard Borel or disintegration hypothesis is imposed. The probability and parameter-range assumptions are explicit in the theorem binders; Tsybakov itself records membership and the displayed all-threshold inequality.
-- source:
--   Steve Hanneke, Hongao Wang, Mingyue Xu, STOC 2027 submission #1413 (October 2026), Definition 1 and footnote 1, p. 3 (PDF p. 3); Bayes rule, p. 2 (PDF p. 2)

import Definitions.Def_TsybakovLearning_OptimalERM_Regions

open MeasureTheory

namespace TsybakovLearning.OptimalERM

variable {X : Type*} [MeasurableSpace X]

/-- A measurable [0,1]-valued version of P(Y=true | X), specified by its defining identity.
Binary labels require only Radon–Nikodym derivatives, not a disintegration of X. -/
structure Regression (D : Measure (X × Bool)) where
  eta : X → ℝ
  measurable_eta : Measurable eta
  range_eta : ∀ x, eta x ∈ Set.Icc (0 : ℝ) 1
  joint_identity : ∀ A : Set X, MeasurableSet A →
    (D (A ×ˢ {true})).toReal = ∫ x in A, eta x ∂(marginal D)

noncomputable def bayes {D : Measure (X × Bool)} (R : Regression D) : X → Bool :=
  fun x => decide ((1 : ℝ) / 2 ≤ R.eta x)

noncomputable def noiseCoefficient (a α : ℝ) : ℝ :=
  (1 - α) * (2 * α) ^ (α / (1 - α)) * a ^ (1 / (1 - α))

/-- Definition 1, p. 3: all positive real thresholds, with the exact printed a-prime. -/
def Tsybakov (H : Set (X → Bool)) (D : Measure (X × Bool)) (R : Regression D)
    (a α : ℝ) : Prop :=
  bayes R ∈ H ∧ ∀ t : ℝ, 0 < t →
    (marginal D {x | |R.eta x - 1 / 2| ≤ t}).toReal ≤
      noiseCoefficient a α * t ^ (α / (1 - α))

end TsybakovLearning.OptimalERM


