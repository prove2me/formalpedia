-- Prove2me | Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses_v2
-- name    : SupportVectorMachines_Classification_ClassificationLosses_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:35:44.398276+00:00
-- url     : https://prove2.me/theorems/9e1c0ede-1a53-4afc-a30d-f210e21ee178
-- title:
--   Sign convention, classification loss, hinge loss and Bayes classifier (Examples 2.4, 2.27; Chapter 8 draft) — as bundled losses
-- statement:
--   The book's sign convention $\operatorname{sign}(0) := 1$ (p. 36); the **classification loss** $L_{\mathrm{class}}(y,t) := \mathbf 1_{(-\infty,0]}(y \operatorname{sign} t)$ (Example 2.4) and the **hinge loss** $L_{\mathrm{hinge}}(y,t) := \max\{0, 1 - yt\}$ (Example 2.27) for $Y = \{-1,1\}$, lifted to losses on $X \times Y \times \mathbb R$ by ignoring $x$; and the **Bayes classification function** $f^*_{L_{\mathrm{class}},P}(x) := \operatorname{sign}(2\eta(x) - 1)$.
--
--   **Formalization Note.** Identical to the retired module except that both losses are instances of the corrected bundled `Loss X`, carrying their (proved) measurability and nonnegativity.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 22, 36-37, Definition 2.7, Examples 2.4 and 2.27

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics_v2

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- The book's sign convention (p. 36, proof of Lemma 2.30: "let us first recall our convention
`sign 0 := 1`"): agrees with the usual sign function except that it sends `0` to `1`. -/
noncomputable def sgn (t : ℝ) : ℝ := if t < 0 then -1 else 1

/-- `sgn` is measurable (a step function of the measurable set `(-∞,0)`). -/
theorem measurable_sgn : Measurable sgn :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

/-- The classification loss `L_class` for standard binary classification `Y := {-1,1}` (Example
2.4, Eq. (2.2), p. 22): `L_class(y,t) := 1_{(-∞,0]}(y · sgn t)`, lifted to a full loss
`X × Y × ℝ → [0,∞)` by ignoring `x`; it is measurable and nonnegative. -/
noncomputable def classLoss {X : Type*} [MeasurableSpace X] : Loss X where
  toFun := fun _ y t => if y * sgn t ≤ 0 then 1 else 0
  measurable := by
    refine Measurable.ite (measurableSet_le ?_ measurable_const) measurable_const measurable_const
    exact measurable_snd.fst.mul (measurable_sgn.comp measurable_snd.snd)
  nonneg := by
    intro x y t
    split_ifs <;> norm_num

/-- The hinge loss `L_hinge` (Example 2.27, p. 36): `L_hinge(y,t) := max{0, 1 - y·t}`, lifted to a
full loss `X × Y × ℝ → [0,∞)` as above; it is measurable and nonnegative. -/
noncomputable def hingeLoss {X : Type*} [MeasurableSpace X] : Loss X where
  toFun := fun _ y t => max 0 (1 - y * t)
  measurable :=
    measurable_const.max (measurable_const.sub (measurable_snd.fst.mul measurable_snd.snd))
  nonneg := fun _ _ _ => le_max_left _ _

/-- The Bayes classification function `f*_{L_class,P}` associated to `η(x) := P(y=1|x)` (used in
Theorem 2.31, p. 37): `f*_{L_class,P}(x) := sign(2η(x) - 1)`. -/
noncomputable def bayesClassifier {X : Type*} (η : X → ℝ) (x : X) : ℝ := sgn (2 * η x - 1)

end SupportVectorMachines.Classification


