-- Prove2me | Definitions.Def_MohriFoML_OnlineToBatch_genError
-- name    : MohriFoML_OnlineToBatch_genError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:04:57.322504+00:00
-- url     : https://prove2.me/theorems/6fd2c220-19d2-461a-80ff-d2d6c9b384e9
-- title:
--   Generalization error $R(h)$ of a hypothesis
-- statement:
--   Let $D$ be a probability distribution on $X \times Y$, let $L$ be a loss function that takes a prediction $a$ and a label $y$ to a real number $L(a, y)$, and let $h : X \to Y'$ be a hypothesis. The **generalization error** of $h$ is its expected loss
--
--   $$
--   R(h) = \mathbb{E}_{(x,y)\sim D}\big[L(h(x), y)\big] = \int_{X \times Y} L(h(x), y)\, dD(x, y).
--   $$
--
--   This is the quantity the on-line to batch conversion bounds: Lemma 8.14 bounds the average of $R(h_t)$ over the hypotheses of an on-line algorithm, and Theorem 8.15 bounds $R$ of their average.
--
--   **Formalization Note** The expectation is a Bochner integral, which Lean sets to $0$ when the integrand is not integrable. Every theorem of the mission that uses $R(h)$ assumes the loss bounded and $(x, y) \mapsto L(h(x), y)$ measurable for the hypotheses involved, so the integral is the genuine expectation.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 202 (PDF p. 219), §8.4, definition of the generalization error R(h) after (8.25)

import Mathlib

namespace MohriFoML.OnlineToBatch

open MeasureTheory

/-- **Generalization error of a hypothesis.**
Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018,
§8.4 "On-line to batch conversion", p. 202 (PDF p. 219): "The generalization error of a
hypothesis `h ∈ H` is its expected loss `R(h) = E_{(x,y)∼D}[L(h(x), y)]`."

`genError D L h = ∫ L (h x) y d D(x, y)`, for a distribution `D` on `X × Y`, a loss
`L : E → Y → ℝ` (prediction first, label second) and a hypothesis `h : X → E`.

**Formalization Note.** This is a Bochner integral, which Lean sets to `0` when the integrand is
not integrable. Every theorem using `genError` assumes the loss bounded and the map
`(x, y) ↦ L (h x) y` measurable for the hypotheses it is applied to, so that the integral is the
book's expectation. -/
noncomputable def genError {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) (L : E → Y → ℝ) (h : X → E) : ℝ :=
  ∫ z, L (h z.1) z.2 ∂D

end MohriFoML.OnlineToBatch


