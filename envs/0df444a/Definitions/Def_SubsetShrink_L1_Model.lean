-- Prove2me | Definitions.Def_SubsetShrink_L1_Model
-- name    : SubsetShrink_L1_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:25:59.168239+00:00
-- url     : https://prove2.me/theorems/797a90ef-0b7f-46ba-bd9e-d58f7b8a38d9
-- title:
--   §3.1, pp. 12–13 — prediction loss and the ℓ1-regularized best-subset estimator
-- statement:
--   For a fixed design matrix $X\in\mathbb R^{n\times p}$, this definition supplies the squared prediction loss, a finite maximum norm, and the estimator predicate. The shared event model supplies the Euclidean and $\ell_1$ norms, support size, $B_0(s)$, and the noise events $\mathcal F$, $\mathcal G_s$, $\mathcal H$; the shared sparse-eigenvalue model supplies $\gamma_s$.
--
--   An $\ell_1$-regularized best subset estimate is any feasible minimizer of
--
--   $$\|y-X\beta\|_2^2+\lambda\|\beta\|_1,\qquad \|\beta\|_0\le k.$$
--
--   Together with the shared definitions, these objects provide the model for Theorem 3 and its five proof milestones.
--
--   **Formalization Note** Vectors use zero-based `Fin` indices. The squared loss is a finite sum; the estimator predicate covers every minimizer and has no $1/2$ in its objective. The event and sparse-eigenvalue conventions are supplied by the imported shared definitions.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, pp. 12–13, (15)–(16), event definitions

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model
import Definitions.Def_SubsetShrink_L2_Model

namespace SubsetShrink.L1

/-! The deterministic model of (15)–(16) and the events of p. 13. -/

def lInf {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  Finset.univ.fold max 0 (fun i => |v i|)

/-! The maximum over permutations equals the sum of decreasingly sorted absolute
coordinates against the decreasing weights, by rearrangement. `j.val + 1` is the
paper's one-based `j`. -/

/-! For `1 ≤ s ≤ p`, the sparse domain is nonempty and its norm ratios are
nonnegative, so this infimum represents the paper's minimum `γ_s`. -/

def predictionError {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (fstar : Fin n → ℝ) (β : Fin p → ℝ) : ℝ :=
  ∑ i, (fstar i - X.mulVec β i) ^ 2

def IsL1BestSubset {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (k : ℕ) (lam : ℝ) (βhat : Fin p → ℝ) : Prop :=
  SubsetShrink.Events.l0 βhat ≤ k ∧
    ∀ β : Fin p → ℝ, SubsetShrink.Events.l0 β ≤ k →
      (∑ i, (y i - X.mulVec βhat i) ^ 2) + lam * SubsetShrink.Events.l1 βhat ≤
        (∑ i, (y i - X.mulVec β i) ^ 2) + lam * SubsetShrink.Events.l1 β

end SubsetShrink.L1


