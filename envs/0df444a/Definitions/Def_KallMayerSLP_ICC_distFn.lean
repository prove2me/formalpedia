-- Prove2me | Definitions.Def_KallMayerSLP_ICC_distFn
-- name    : KallMayerSLP_ICC_distFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:56.029005+00:00
-- url     : https://prove2.me/theorems/01338f8a-4449-4fb2-861e-758d88f4dec5
-- title:
--   Distribution function $F_\vartheta$ of a real random variable
-- statement:
--   For a real random variable $\vartheta$ on a probability space, the **probability distribution function** is
--   $$
--   F_\vartheta(t)=\mathbb P(\vartheta\le t),\qquad t\in\mathbb R.
--   $$
--   It is the function integrated in the tail formulas of Proposition 4.1, which give the name "integrated" chance constraint.
--
--   **Formalization Note** The value is the real number `μ {ω | ϑ ω ≤ t}`, obtained with `toReal`.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4, p.147 (PDF 157)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.ICC

/-- **Probability distribution function `F_ϑ` of a real random variable.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §4, p.147 (PDF 157), used in
Proposition 4.1: `F_ϑ(t) = ℙ(ϑ ≤ t)`.

**Formalization Note.** The value is the real number `μ {ω | ϑ ω ≤ t}`; for a probability measure
the `toReal` loses nothing. -/
noncomputable def distFn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ϑ : Ω → ℝ) (t : ℝ) : ℝ :=
  (μ {ω | ϑ ω ≤ t}).toReal

end KallMayerSLP.ICC


