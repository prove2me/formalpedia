-- Prove2me | Definitions.Def_EmpiricalDRO_Discrete_Setting
-- name    : EmpiricalDRO_Discrete_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:05:36.468341+00:00
-- url     : https://prove2.me/theorems/f27c4b09-06e3-47e6-8401-457db400283e
-- title:
--   Empirical histogram and finite-support Burg ball
-- statement:
--   For a sample of size $n$ classified among $k$ support points, let $n_i$ count observations at point $i$ and let $\hat p_i=n_i/n$. The Burg generator and the lower empirical DRO value are imported from the shared setting.
--
--   The **finite-support Burg ball** of radius $\eta$ contains probability vectors $p$ absolutely continuous with respect to the histogram $\hat p$, with $p_i>0$ whenever $\hat p_i>0$, such that
--
--   $$
--   -\sum_{i=1}^k \hat p_i\log\frac{p_i}{\hat p_i}\le\eta.
--   $$
--
--   These objects let the sample-weight and support-weight optimizations in Proposition 1 use the same loss values.
--
--   **Formalization Note** The absolute-continuity condition $\hat p_i=0\Rightarrow p_i=0$ comes from (13)–(14); display (28) omits it. The positivity condition excludes Lean's value $\log 0=0$ when the paper's divergence is infinite. Indices are zero-based in Lean. The lower value uses a real infimum only when the ball is nonempty and bounded, as it is for $n>0$ and nonnegative radius.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 6, (13)–(15); p. 8, (19); p. 11, (26), (28)

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_EmpiricalDRO_Coverage_Setting

namespace EmpiricalDRO.Discrete

/-- The number of sample observations equal to support point `i` (p. 6). -/
def count {n k : ℕ} (c : Fin n → Fin k) (i : Fin k) : ℕ :=
  (Finset.univ.filter fun j => c j = i).card

/-- The empirical histogram, with mass `nᵢ/n` on support point `i` (p. 6). -/
noncomputable def phat {n k : ℕ} (c : Fin n → Fin k) (i : Fin k) : ℝ :=
  (count c i : ℝ) / n

/-- The finite-support Burg ball of (28), interpreted in the absolutely continuous class
`P_{p̂}` specified in (13)–(14). A positive baseline coordinate must also have positive
candidate mass, so the logarithm has its intended extended-real meaning. -/
def burgBall {k : ℕ} (phat : Fin k → ℝ) (η : ℝ) : Set (Fin k → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧
    ∑ i, p i = 1 ∧
    (∀ i, phat i = 0 → p i = 0) ∧
    (∀ i, 0 < phat i → 0 < p i) ∧
    -∑ i, phat i * Real.log (p i / phat i) ≤ η}

end EmpiricalDRO.Discrete


