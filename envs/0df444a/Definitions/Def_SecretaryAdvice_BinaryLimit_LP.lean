-- Prove2me | Definitions.Def_SecretaryAdvice_BinaryLimit_LP
-- name    : SecretaryAdvice_BinaryLimit_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:55.806382+00:00
-- url     : https://prove2.me/theorems/f2139f87-47f9-4a90-8e74-5599ae17064b
-- title:
--   §6, p. 20 — primal LP and its optimum
-- statement:
--   For $n$ arrivals, let $p$ be the classifier’s recall and $p'$ its specificity. For each time $i\in\{1,\ldots,n\}$ and signal $s\in\{Y,N\}$, let $z_i^s$ be a primal decision variable. Write $\bar z_j=(1-p')z_j^Y+p'z_j^N$. The **binary advice primal LP** is
--
--   $$
--   \operatorname{Opt}(n,p,p')=\sup\left\{\sum_{i=1}^n\frac{pz_i^Y+(1-p)z_i^N}{n}:0\le z_i^s\le1,\quad z_i^s\le1-\sum_{j=1}^{i-1}\frac{\bar z_j}{j}\quad(i,s)\right\}.
--   $$
--
--   This is the finite LP whose optimum is analyzed in Theorem 20. Coordinates of $z$ outside times $1,\ldots,n$ play no role.
--
--   **Formalization Note** The signal $Y$ is `true`, $N$ is `false`, and time indices are the paper’s 1-based indices. The source assumes $p,p'\in[1/2,1]$ in Example 5; that range is imposed by theorem hypotheses. The feasible objective set is nonempty and bounded for these parameters and $n\ge1$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 20, LP Formulation

import Mathlib

namespace SecretaryAdvice.BinaryLimit

/-- The section 6 primal LP. `true` is advice Y and `false` is advice N;
only rounds `1, ..., n` enter the constraints. -/
def PrimalFeasible (n : ℕ) (_p pp : ℝ) (z : ℕ → Bool → ℝ) : Prop :=
  ∀ i ∈ Finset.Icc 1 n, ∀ s : Bool,
    0 ≤ z i s ∧ z i s ≤ 1 ∧
      z i s ≤ 1 - ∑ j ∈ Finset.Ico 1 i,
        (1 / (j : ℝ)) * ((1 - pp) * z j true + pp * z j false)

/-- The objective of the section 6 primal LP. -/
noncomputable def primalObj (n : ℕ) (p _pp : ℝ) (z : ℕ → Bool → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n,
    (1 / (n : ℝ)) * (p * z i true + (1 - p) * z i false)

/-- `Opt(n,p,p')` is the optimal value of the actual primal LP. -/
noncomputable def Opt (n : ℕ) (p pp : ℝ) : ℝ :=
  sSup (primalObj n p pp '' {z : ℕ → Bool → ℝ | PrimalFeasible n p pp z})

end SecretaryAdvice.BinaryLimit


