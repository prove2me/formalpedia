-- Prove2me | Definitions.Def_AssortOpt_HMF_Supplement_BudgetRandom
-- name    : AssortOpt_HMF_Supplement_BudgetRandom
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:15:05.992686+00:00
-- url     : https://prove2.me/theorems/37321220-b077-42b6-b945-33b3fbd161ed
-- title:
--   Definition 17 and Theorems 3, 5 — budget mechanisms and independent-assortment revenue
-- statement:
--   For nonnegative real weights $w_j$ and $B\in[0,1]$, the budget-additive function and its allocation mechanism are
--   $$f(S)=\min\!\left\{\sum_{j\in S}w_j,B\right\},\qquad x_{\ell_k}(\ell)=f(\ell_{1:k})-f(\ell_{1:k-1}).$$
--   For an inclusion vector $q$, independent assortment sampling gives subset $S$ probability $\prod_{j\in S}q_j\prod_{j\notin S}(1-q_j)$. Its expected revenue is the finite sum of this probability times the published assortment revenue. The existing general Bernoulli-subset expectation supplies this law; the buyer distribution is independent of the sampling.
--
--   Theorem 3 uses $q_j=1-e^{-w_j}$, without clipping weights. For Theorem 5, $L$ is the maximum positive-support list length and $q_j=\varphi(f_j)$, where $\varphi(a)=2a/L$ for $a\le1/2$ and $1/L$ otherwise. When $L=0$, the source formula is undefined: the explicit total convention uses $q_j=0$ and approximation coefficient zero. All positive-support lists are then empty and both revenues are zero. No real supremum or unbounded maximum is used.
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 23, Definition 17; pp. 24–25, Theorems 3 and 5; p. 56, proof of Theorem 5

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_Reports
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset

namespace AssortOpt.HMF.Supplement
open Finset

/-- Definition 17, p. 23: weights are nonnegative and `B ∈ [0,1]` when this function is used. -/
def budgetFn {n : ℕ} (w : Fin n → ℝ) (B : ℝ) (S : Finset (Fin n)) : ℝ :=
  min (∑ j ∈ S, w j) B

/-- Definition 17: no clipping of the weights before forming the prefix sums. -/
def budgetMech {n : ℕ} (w : Fin n → ℝ) (B : ℝ) : List (Fin n) → Fin n → ℝ :=
  incrementMech (budgetFn w B)

/-- Actual independent-subset expectation, using the published product law on all subsets.
Buyer randomness is already integrated in `revAssort`, independently of assortment randomness. -/
noncomputable def revIndependent {n : ℕ} (D : ListDist n) (r q : Fin n → ℝ) : ℝ :=
  SpectralSparsify.Sampling.expect Finset.univ q (revAssort D r)

/-- Theorem 3's exact independent inclusion probabilities, even when weights exceed 1 or B. -/
noncomputable def expInclusion {n : ℕ} (w : Fin n → ℝ) (j : Fin n) : ℝ :=
  1 - Real.exp (-w j)

/-- Maximum length among positive-mass types, not among probability-zero reports. -/
def maxLength {n : ℕ} (D : ListDist n) : ℕ :=
  D.supp.sup List.length

/-- Theorem 5's piecewise rule. The separate `L = 0` branch extends the source's undefined
expression by offering nothing; it is used only when all positive-mass lists are empty. -/
noncomputable def cappedInclusion (L : ℕ) (a : ℝ) : ℝ :=
  if L = 0 then 0 else if a ≤ 1 / 2 then 2 * a / L else 1 / L

/-- The zero-length case has zero revenue on both sides, with coefficient explicitly 0. -/
noncomputable def lengthFactor (L : ℕ) : ℝ :=
  if L = 0 then 0 else 2 / (Real.exp 1 * L)

end AssortOpt.HMF.Supplement


