-- Prove2me | Definitions.Def_SelfSelReg_SatisfiesAssumption
-- name    : SelfSelReg_SatisfiesAssumption
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:52.492812+00:00
-- url     : https://prove2.me/theorems/f8ca331d-7fb5-4ad2-b765-42fd1caeaa13
-- title:
--   Assumption 1.2: boundedness and uncoveredness of the regressors
-- statement:
--   Let $B\ge1$ and $\Delta\in(0,1]$. Regressors $w_1,\dots,w_k\in\mathbb R^n$ satisfy **boundedness and uncoveredness** with constants $B,\Delta$ if
--   $$\Delta\le\|w_i\|_2\le B\quad(i\in[k]),\qquad |\langle w_i,w_j\rangle|\le\min\{\|w_i\|_2^2,\|w_j\|_2^2\}-\Delta^2\quad(i\ne j).$$
--
--   Boundedness keeps every regressor's norm between $\Delta$ and $B$; uncoveredness says no regressor is nearly "covered" by another in the direction of either. These are the standard geometric assumptions under which the self-selection problem admits finite-sample guarantees, and every quantitative result of the paper is stated under them.
--
--   **Formalization Note** The ranges $B\ge1$ and $\Delta\in(0,1]$ are hypotheses of the theorems that use the predicate, not part of it. The angular separation bound (3) is a consequence and is not included.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Assumption 1.2, (2), p.2 (PDF p.5)

import Mathlib

namespace SelfSelReg

/-- **Assumption 1.2** (Boundedness and Uncoveredness).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Assumption 1.2, p.2 (PDF p.5): "For some absolute constants B ≥ 1 and
∆ ∈ (0, 1], the regressors satisfy ∆ ≤ ‖w_i‖₂ ≤ B, |⟨w_i, w_j⟩| ≤ min{‖w_i‖₂², ‖w_j‖₂²} − ∆² (i ≠ j)." (2)

**Formalization Note.** The ranges `B ≥ 1` and `∆ ∈ (0, 1]` are hypotheses of the theorems that use
this predicate, not part of it. The angular bound (3) is a consequence and is not included. -/
def SatisfiesAssumption {n k : ℕ} (B Δ : ℝ) (w : Fin k → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ i, Δ ≤ ‖w i‖ ∧ ‖w i‖ ≤ B) ∧
    ∀ i j, i ≠ j → |inner ℝ (w i) (w j)| ≤ min (‖w i‖ ^ 2) (‖w j‖ ^ 2) - Δ ^ 2

end SelfSelReg


