-- Prove2me | Definitions.Def_CalibratedMA_Randomized_Supplement_Categories
-- name    : CalibratedMA_Randomized_Supplement_Categories
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:23:50.855168+00:00
-- url     : https://prove2.me/theorems/413c58c2-3f73-4a75-9a58-1ca60d34e533
-- title:
--   Section 5.1 — category projection, covariance and calibration
-- statement:
--   Let $P$ be a context probability law, $S:X\to[0,1]$ a measurable score, and $J:X\to\{1,\ldots,r\}$ a finite measurable category assignment. For a category $j$ of positive mass define
--   $$s_j=\frac{\int_{J=j}S\,dP}{P(J=j)},\quad p_J(x)=s_{J(x)},\quad R_J=S-p_J.$$
--   A zero-mass category receives mean zero. Conditional covariance is the conditional product moment minus the product of the conditional means, also zero at a zero-mass category. For a labeled law $D$ and score $q$ the cell calibration and category-sign maximum are
--   $$\mathrm{Cal}_{C_J}(q)=\sum_j\left|\mathbb E_D[\mathbf1_{\{J(X)=j\}}(Y-q(X))]\right|,$$
--   $$\max_{\sigma\in\{-1,1\}^r}\left|\mathbb E_D[\sigma_{J(X)}(Y-S(X))]\right|.$$
--   Signs are encoded as Booleans, and the maximum as a supremum over the finite nonempty type of sign assignments. These definitions distinguish categories from prediction level sets and assignment cells. Lemma 5.2 supplies the projection identities; no identity is assumed here.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), pp.21–22, Section 5.1 and Lemma 5.2

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Learning

open MeasureTheory

namespace CalibratedMA.Randomized.Supplement

/-- Section 5.1: category means, zero on a category of probability zero. -/
noncomputable def categoryMean {X : Type} [MeasurableSpace X] {r : ℕ}
    (P : Measure X) (S : X → ℝ) (J : X → Fin r) (j : Fin r) : ℝ :=
  (∫ x in {x | J x = j}, S x ∂P) / (P {x | J x = j}).toReal

noncomputable def categoryPredictor {X : Type} [MeasurableSpace X] {r : ℕ}
    (P : Measure X) (S : X → ℝ) (J : X → Fin r) : X → ℝ :=
  fun x => categoryMean P S J (J x)

noncomputable def categoryResidual {X : Type} [MeasurableSpace X] {r : ℕ}
    (P : Measure X) (S : X → ℝ) (J : X → Fin r) : X → ℝ :=
  fun x => S x - categoryPredictor P S J x

/-- Conditional covariance, zero for a zero-mass category (real division by zero). -/
noncomputable def categoryCovariance {X : Type} [MeasurableSpace X] {r : ℕ}
    (P : Measure X) (S g : X → ℝ) (J : X → Fin r) (j : Fin r) : ℝ :=
  categoryMean P (fun x => g x * S x) J j -
    categoryMean P g J j * categoryMean P S J j

noncomputable def cellCalibration {X : Type} [MeasurableSpace X] {r : ℕ}
    (D : Measure (X × ℝ)) (q : X → ℝ) (J : X → Fin r) : ℝ :=
  ∑ j : Fin r, |∫ z, (if J z.1 = j then z.2 - q z.1 else 0) ∂D|

/-- Bool encodes the two category signs; this supremum is over a finite nonempty type. -/
noncomputable def categorySignMaximum {X : Type} [MeasurableSpace X] {r : ℕ}
    (D : Measure (X × ℝ)) (S : X → ℝ) (J : X → Fin r) : ℝ :=
  ⨆ σ : Fin r → Bool, |∫ z, (if σ (J z.1) then (1 : ℝ) else -1) * (z.2 - S z.1) ∂D|

end CalibratedMA.Randomized.Supplement


