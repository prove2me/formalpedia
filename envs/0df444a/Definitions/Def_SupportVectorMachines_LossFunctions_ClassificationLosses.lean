-- Prove2me | Definitions.Def_SupportVectorMachines_LossFunctions_ClassificationLosses
-- name    : SupportVectorMachines_LossFunctions_ClassificationLosses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:19:31.363991+00:00
-- url     : https://prove2.me/theorems/01c1bcf3-c6c4-4763-afd4-0b8485b19d0a
-- title:
--   The classification loss, the hinge loss, clipping, and the Bayes classifier
-- statement:
--   Throughout this bundle $Y := \{-1,1\}$ (standard binary classification, Steinwart &
--   Christmann, *Support Vector Machines*, Springer 2008, §2.3). Write `sgn` for the book's own
--   sign convention (p. 36, proof of Lemma 2.30): $\operatorname{sgn}(t) = 1$ for $t \ge 0$ and
--   $\operatorname{sgn}(t)=-1$ for $t<0$ — the usual sign function except that $\operatorname{sgn}(0):=1$.
--
--   The **classification loss** (Example 2.4, Eq. (2.2), p. 22) is
--   $$
--   L_{\mathrm{class}}(y,t) := \mathbf 1_{(-\infty,0]}(y \cdot \operatorname{sgn} t), \qquad y \in \{-1,1\},\ t \in \mathbb R,
--   $$
--   penalizing exactly the predictions $t$ whose sign disagrees with the label $y$.
--
--   The **hinge loss** (Example 2.27, p. 36) is
--   $$
--   L_{\mathrm{hinge}}(y,t) := \max\{0,\, 1 - yt\}, \qquad y \in \{-1,1\},\ t \in \mathbb R,
--   $$
--   the piecewise-linear surrogate used by soft-margin SVMs. Both are lifted to full losses on
--   $X \times Y \times \mathbb R$ by ignoring the $x$-coordinate, per the book's own identification
--   convention (Definition 2.7).
--
--   A loss $L$ **can be clipped at $M>0$** (Definition 2.22, Eq. (2.14), p. 34) if clipping every
--   prediction to $[-M,M]$ never increases the loss: $L(x,y,\widehat t) \le L(x,y,t)$ for all
--   $x,y,t$, where $\widehat t$ is $t$ truncated to $[-M,M]$.
--
--   Given $\eta(x) := P(y=1\mid x)$, the **Bayes classification function** (Theorem 2.31, p. 37) is
--   $$
--   f^*_{L_{\mathrm{class}},P}(x) := \operatorname{sgn}(2\eta(x)-1).
--   $$
--
--   **Formalization Note** `clip M t` implements Eq. (2.14) directly by cases on `t < -M` and
--   `t > M`. `CanBeClipped` is stated for a general `Loss X`, reused for both `lemma_2_23` and,
--   at $M=1$, for `hingeLoss` inside `zhang_inequality`'s proof obligation.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 22, 34, 36-37, Definitions 2.7, 2.22, Examples 2.4 and 2.27, Theorem 2.31 (sign convention, p. 36)

import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_RiskBasics

open MeasureTheory

namespace SupportVectorMachines.LossFunctions

/-- The book's sign convention, used throughout Section 2.3 (p. 36, proof of Lemma 2.30:
"let us first recall our convention `sign 0 := 1`"): agrees with the usual sign function except
that it sends `0` to `1` rather than `0`. -/
noncomputable def sgn (t : ℝ) : ℝ := if t < 0 then -1 else 1

/-- The clipped value of `t` at `±M` (Definition 2.22, Eq. (2.14), p. 34):
`clip M t = -M` if `t < -M`, `= t` if `t ∈ [-M,M]`, `= M` if `t > M`. -/
noncomputable def clip (M : ℝ) (t : ℝ) : ℝ :=
  if t < -M then -M else if t > M then M else t

/-- A loss `L` can be clipped at `M > 0` (Definition 2.22, p. 34) if clipping the prediction
never increases the loss: `L(x, y, clip M t) ≤ L(x, y, t)` for all `x, y, t`. -/
def CanBeClipped {X : Type*} (L : Loss X) (M : ℝ) : Prop :=
  ∀ x y t, L x y (clip M t) ≤ L x y t

/-- The classification loss `L_class` for standard binary classification (Example 2.4, Eq.
(2.2), p. 22): `L_class(y,t) := 1_{(-∞,0]}(y · sgn t)`, penalizing a prediction `t` whose sign
disagrees with the label `y`. Lifted to a full loss `X × Y × ℝ → [0,∞)` by ignoring `x`, per the
book's own identification convention (Definition 2.7). -/
noncomputable def classLoss {X : Type*} : Loss X := fun _ y t => if y * sgn t ≤ 0 then 1 else 0

/-- The hinge loss `L_hinge` (Example 2.27, p. 36): `L_hinge(y,t) := max{0, 1 - y·t}`, lifted to
a full loss `X × Y × ℝ → [0,∞)` as above. -/
noncomputable def hingeLoss {X : Type*} : Loss X := fun _ y t => max 0 (1 - y * t)

/-- The Bayes classification function `f*_{L_class,P}` associated to `η(x) := P(y=1|x)`
(Theorem 2.31, p. 37): `f*_{L_class,P}(x) := sign(2η(x) - 1)`. -/
noncomputable def bayesClassifier {X : Type*} (η : X → ℝ) (x : X) : ℝ := sgn (2 * η x - 1)

end SupportVectorMachines.LossFunctions


