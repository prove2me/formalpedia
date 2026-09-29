-- Prove2me | Definitions.Def_OnlineConvexOpt_LearningTheory_GeneralizationError
-- name    : OnlineConvexOpt_LearningTheory_GeneralizationError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:45:22.893266+00:00
-- url     : https://prove2.me/theorems/c7464683-9d9c-412b-85a4-f668ce5e4484
-- title:
--   Generalization error (general and zero-one loss)
-- statement:
--   Two declarations for §9.1's core notion. `GeneralizationError D pred ℓ hparam` is
--   $\mathrm{error}(h) = \mathbb E_{(x,y)\sim D}[\ell(h(x),y)]$ (p. 152), the expected loss of a
--   hypothesis's predictions against a labeled-example distribution $D$; predictions are
--   parametrized (`pred hparam x`), generalizing the book's linear hypotheses $h_w(x)=w^\top x$
--   (p. 155). `GeneralizationErrorZeroOne D h` specializes this to the zero-one loss for a
--   `Bool`-labeled concept: $\mathrm{error}(h) = \Pr_{(x,y)\sim D}[h(x)\ne y]$, used throughout
--   §9.1.2's No Free Lunch theorem.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 152, PDF p. 174

import Mathlib

open MeasureTheory

namespace OnlineConvexOpt.LearningTheory

/-- The generalization error of a hypothesis `h : E → X → ℝ` (Hazan, *Introduction to Online
Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 152, PDF p. 174):
`error(h) = E_{(x,y)∼D}[ℓ(h(x), y)]`, the expected loss of `h`'s predictions against a
distribution `D` on labeled examples. Predictions are parametrized: `pred hparam x` is the
real-valued prediction of the hypothesis identified by `hparam ∈ E` on input `x` (generalizing
the book's `hw(x) = wᵀx`, p. 155). -/
noncomputable def GeneralizationError {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) (pred : E → X → ℝ) (ℓ : ℝ → Y → ℝ) (hparam : E) : ℝ :=
  ∫ p, ℓ (pred hparam p.1) p.2 ∂D

/-- The generalization error under the zero-one loss for a `Bool`-labeled concept
(p. 152, PDF p. 174, and used throughout §9.1.2's No Free Lunch theorem): `error(h) =
Pr_{(x,y)∼D}[h(x) ≠ y]`. -/
noncomputable def GeneralizationErrorZeroOne {X : Type*} [MeasurableSpace X]
    (D : Measure (X × Bool)) (h : X → Bool) : ℝ :=
  (D {p : X × Bool | h p.1 ≠ p.2}).toReal

end OnlineConvexOpt.LearningTheory


