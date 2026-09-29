-- Prove2me | Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses
-- name    : SupportVectorMachines_Classification_ClassificationLosses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:09:32.981333+00:00
-- url     : https://prove2.me/theorems/9eb02455-7c5f-4008-9ff8-e121162265c4
-- title:
--   The classification loss, the hinge loss, and the Bayes classifier
-- statement:
--   Throughout $Y := \{-1,1\}$ (standard binary classification, Steinwart & Christmann, *Support
--   Vector Machines*, Springer 2008, §2.3). Write `sgn` for the book's own sign convention
--   (p. 36, proof of Lemma 2.30): $\operatorname{sgn}(t) = 1$ for $t \ge 0$ and
--   $\operatorname{sgn}(t) = -1$ for $t < 0$.
--
--   The **classification loss** (Example 2.4, Eq. (2.2), p. 22) is
--   $$
--   L_{\mathrm{class}}(y,t) := \mathbf 1_{(-\infty,0]}(y \cdot \operatorname{sgn} t), \qquad y \in \{-1,1\},\ t \in \mathbb R.
--   $$
--   The **hinge loss** (Example 2.27, p. 36) is
--   $$
--   L_{\mathrm{hinge}}(y,t) := \max\{0,\, 1 - yt\}, \qquad y \in \{-1,1\},\ t \in \mathbb R.
--   $$
--   Both are lifted to full losses on $X \times Y \times \mathbb R$ by ignoring $x$, per the
--   book's identification convention (Definition 2.7).
--
--   Given $\eta(x) := P(y=1\mid x)$, the **Bayes classification function** is
--   $f^*_{L_{\mathrm{class}},P}(x) := \operatorname{sgn}(2\eta(x)-1)$.
--
--   **Formalization Note** Restated locally from this series' `01-loss-functions` mission (same
--   definitions, same conventions) per Hard Rule 9, since a draft cannot import another draft.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 22, 36-37, Definitions 2.7, Examples 2.4 and 2.27

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- The book's sign convention (p. 36, proof of Lemma 2.30: "let us first recall our convention
`sign 0 := 1`"): agrees with the usual sign function except that it sends `0` to `1`. -/
noncomputable def sgn (t : ℝ) : ℝ := if t < 0 then -1 else 1

/-- The classification loss `L_class` for standard binary classification `Y := {-1,1}` (Example
2.4, Eq. (2.2), p. 22): `L_class(y,t) := 1_{(-∞,0]}(y · sgn t)`, lifted to a full loss
`X × Y × ℝ → [0,∞)` by ignoring `x`. -/
noncomputable def classLoss {X : Type*} : Loss X := fun _ y t => if y * sgn t ≤ 0 then 1 else 0

/-- The hinge loss `L_hinge` (Example 2.27, p. 36): `L_hinge(y,t) := max{0, 1 - y·t}`, lifted to a
full loss `X × Y × ℝ → [0,∞)` as above. -/
noncomputable def hingeLoss {X : Type*} : Loss X := fun _ y t => max 0 (1 - y * t)

/-- The Bayes classification function `f*_{L_class,P}` associated to `η(x) := P(y=1|x)` (used in
Theorem 2.31, p. 37): `f*_{L_class,P}(x) := sign(2η(x) - 1)`. -/
noncomputable def bayesClassifier {X : Type*} (η : X → ℝ) (x : X) : ℝ := sgn (2 * η x - 1)

end SupportVectorMachines.Classification


