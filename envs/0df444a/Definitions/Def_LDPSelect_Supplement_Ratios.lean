-- Prove2me | Definitions.Def_LDPSelect_Supplement_Ratios
-- name    : LDPSelect_Supplement_Ratios
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:02:03.812958+00:00
-- url     : https://prove2.me/theorems/24d29ddb-a06d-4750-b731-1f201e4f3081
-- title:
--   Competitive ratios $\inf_X W(X)/M_{\mathcal F}(X)$ against the prophet
-- statement:
--   For a downward-closed family $\mathcal F$ on $n$ users, a privacy parameter $a$, and the optimal rewards $W^{\mathrm N}_{\mathcal F}$, $W^{\mathrm I}_{\mathcal F}$ and the prophet value $M_{\mathcal F}=\mathbb E\max_{S\in\mathcal F}X(S)$, the **competitive ratios** are
--   $$\inf_X \frac{W^{\mathrm N}_{\mathcal F}(X)}{M_{\mathcal F}(X)},\qquad \inf_X \frac{W^{\mathrm I}_{\mathcal F}(X)}{M_{\mathcal F}(X)},$$
--   where $X$ ranges over product priors with integrable values for which $0<M_{\mathcal F}(X)<\infty$, so that the ratio is defined.
--
--   Theorems 5, 6 and 7 determine these ratios for uniform matroids and general matroids.
--
--   **Formalization Note** The ratio is computed in $[0,\infty]$; on the admissible priors it is a quotient of finite numbers with positive denominator, so no junk value arises.
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), §1.1, pp.2–3 (pdf pp.3–4), Theorems 5–7

import Mathlib
import Definitions.Def_LDPSelect_Values

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect.Supplement

/-!
# Competitive ratios against the prophet

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), §1.1, pp.2–3 (Theorems 5–7).

**Formalization Note.** The paper's `inf_X W(X) / M_F(X)` ranges over product priors for which the
ratio is defined: every `P i` is a probability measure, the values are integrable (the standing
assumption of §2), and the prophet value `M_F = E max_{S ∈ F} X(S)` is positive and finite. The ratio
is taken in `ℝ≥0∞`; on this set of priors it is a genuine quotient of finite numbers with positive
denominator, so no junk value arises.
-/

open LDPSelect

variable {n : ℕ}

/-- The priors over which a competitive ratio is taken: probability measures with finite means and
`0 < M_F < ∞`. -/
def Admissible (F : Family n) (P : Fin n → Measure ℝ≥0) : Prop :=
  (∀ i, IsProbabilityMeasure (P i)) ∧ IsIntegrablePrior P ∧ 0 < prophet F P ∧ prophet F P < ⊤

/-- `inf_X W^N_F(X) / M_F(X)`. -/
noncomputable def ratioN (a : ℝ) (F : Family n) : ℝ≥0∞ :=
  ⨅ (P : Fin n → Measure ℝ≥0) (_ : Admissible F P), WN a F P / prophet F P

/-- `inf_X W^I_F(X) / M_F(X)`. -/
noncomputable def ratioI (a : ℝ) (F : Family n) : ℝ≥0∞ :=
  ⨅ (P : Fin n → Measure ℝ≥0) (_ : Admissible F P), WI a F P / prophet F P

end LDPSelect.Supplement


