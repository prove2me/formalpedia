-- Prove2me | Definitions.Def_WeightedMajority_Continuous_WMCRun
-- name    : WeightedMajority_Continuous_WMCRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:38.585488+00:00
-- url     : https://prove2.me/theorems/3c5fea34-f8bb-4e7a-9d24-e75612e4680f
-- title:
--   The continuous Weighted Majority master and its permitted runs
-- statement:
--   For a finite nonempty pool and a finite sequence of trials, let $w_i^{(j)}$ be expert $i$'s weight before trial $j$, $x_i^{(j)}\in[0,1]$ its prediction, and $\rho^{(j)}\in[0,1]$ the label. The total weight and weighted mean prediction are
--
--   $$s^{(j)}=\sum_i w_i^{(j)},\qquad \gamma^{(j)}=\frac{\sum_i w_i^{(j)}x_i^{(j)}}{s^{(j)}}.$$
--
--   The continuous master predicts $\gamma^{(j)}$ and incurs total absolute loss $m=\sum_j|\gamma^{(j)}-\rho^{(j)}|$. Initial weights are positive and all weights through the final update are nonnegative. A WMC run with $0\le\beta<1$ updates every expert on every trial using a factor $F_i^{(j)}$ satisfying
--
--   $$w_i^{(j+1)}=F_i^{(j)}w_i^{(j)},\qquad \beta^{|x_i^{(j)}-\rho^{(j)}|}\le F_i^{(j)}\le 1-(1-\beta)|x_i^{(j)}-\rho^{(j)}|.$$
--
--   This interface also names the weaker upper-update conditions used by Lemmas 5.2 and 5.3. The factor is free to vary by trial and expert within the paper's interval.
--
--   **Formalization Note** Trial indices start at zero, so the paper's $w^{(1)}$ is `w 0` and $w_{\mathrm{fin}}$ is `totalWeight w t`. The quotient in $\gamma$ is used in theorems only when positive final total weight ensures all earlier totals are positive. The paper's $0^0=1$ convention agrees with real exponentiation here.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108 (1994), pp. 220, 232–233, Notations and Assumptions and §5, eq. (5.1); https://doi.org/10.1006/inco.1994.1009

import Mathlib
import Definitions.Def_WeightedMajority_Basic_IsWMRun

namespace WeightedMajority.Continuous

/-- The pool's weighted mean prediction at trial `j`. -/
noncomputable def meanPrediction {n t : ℕ} (w : ℕ → Fin n → ℝ)
    (x : Fin t → Fin n → ℝ) (j : Fin t) : ℝ :=
  (∑ i : Fin n, w j.val i * x j i) / WeightedMajority.Basic.totalWeight w j.val

/-- Total absolute loss of WMC, whose prediction is the weighted mean. -/
noncomputable def masterLoss {n t : ℕ} (w : ℕ → Fin n → ℝ)
    (x : Fin t → Fin n → ℝ) (rho : Fin t → ℝ) : ℝ :=
  ∑ j : Fin t, |meanPrediction w x j - rho j|

/-- The standing conditions of Section 5 for a pool and a finite trial sequence. -/
def BaseConditions {n t : ℕ} (beta : ℝ) (w : ℕ → Fin n → ℝ)
    (x : Fin t → Fin n → ℝ) (rho : Fin t → ℝ) : Prop :=
  0 < n ∧ 0 ≤ beta ∧ beta < 1 ∧
  (∀ i : Fin n, 0 < w 0 i) ∧
  (∀ k : ℕ, k ≤ t → ∀ i : Fin n, 0 ≤ w k i) ∧
  (∀ j : Fin t, 0 ≤ rho j ∧ rho j ≤ 1) ∧
  (∀ j : Fin t, ∀ i : Fin n, 0 ≤ x j i ∧ x j i ≤ 1)

/-- The upper update inequality assumed by Lemma 5.2. -/
def PotentialConditions {n t : ℕ} (beta : ℝ) (w : ℕ → Fin n → ℝ)
    (x : Fin t → Fin n → ℝ) (rho : Fin t → ℝ) : Prop :=
  BaseConditions beta w x rho ∧
  ∀ j : Fin t, ∀ i : Fin n,
    w (j.val + 1) i ≤ w j.val i *
      (1 - (1 - beta) * |x j i - rho j|)

/-- A WMC run updates on every trial with any factor allowed by (5.1). -/
def IsWMCRun {n t : ℕ} (beta : ℝ) (w : ℕ → Fin n → ℝ)
    (x : Fin t → Fin n → ℝ) (rho : Fin t → ℝ) : Prop :=
  BaseConditions beta w x rho ∧
  ∀ j : Fin t, ∀ i : Fin n, ∃ F : ℝ,
    beta ^ (|x j i - rho j|) ≤ F ∧
    F ≤ 1 - (1 - beta) * |x j i - rho j| ∧
    w (j.val + 1) i = F * w j.val i

end WeightedMajority.Continuous


