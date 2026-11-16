-- Prove2me | Definitions.Def_AgreementTop736_Exact_Supplement_Hamming
-- name    : AgreementTop736_Exact_Supplement_Hamming
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:42:11.12762+00:00
-- url     : https://prove2.me/theorems/296fd32c-e8f1-4440-8e18-37ddbfd57ec8
-- title:
--   Parent-independent inclusion, its minimum, and Hamming error probabilities
-- statement:
--   Let $X$ be a finite set, $\Sigma$ a finite alphabet, and $S=(\mu,D,q_k,q_h)$ the published sampling scheme: $\mu$ is a probability law on $q_k$-element top sets $K$, and $D(\cdot\mid K)$ samples $q_h$-element subsets of $K$. The published functions $F_K$ and $g$ have Hamming error $d_K=\#\{x\in K:F_K(x)\ne g(x)\}$.
--
--   Parent-independent inclusion means that $a_x>0$ for every element of positive top marginal mass and that $\Pr_{H\mid K}[x\in H]=a_x$ for every supported $K\ni x$. Define
--   $$\xi=\min_{x:\Pr_K[x\in K]>0}a_x,\qquad
--   \mathbb E_K d_K=\sum_K\mu(K)d_K,\qquad
--   \mathbb E_K\frac{d_K}{q_k}=\sum_K\mu(K)\frac{d_K}{q_k}.$$
--   For any real $\delta$, the approximate disagreement probability is
--   $$\sum_K\mu(K)\mathbf1[d_K\ge\delta q_k].$$
--   Theorem 9 uses this event for every $\delta>0$. The family $a_x$ need not be constant across elements.
--
--   These definitions add the quantities needed for the average Hamming theorem while reusing the published sampling, Hamming count and majority definitions.
--
--   **Formalization Note** The finite minimum is computed from the image of the positive element support. Its empty-support default is zero, but valid sampling with $0<q_h<q_k$ makes that support nonempty. The top size is then positive, so normalized error never divides by zero in the theorem.
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), p.12, Theorem 9; Section 2, p.7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized

/-! Kaufman–Pham, STOC 2027 submission #736, §2 p.7 and Theorem 9 p.12.
Only the additional objects for heterogeneous inclusion and Hamming error are defined here.
The sampling scheme, majority and conditioned Poincaré gap are the published objects. -/

namespace AgreementTop736.Exact.Supplement

open Finset
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Theorem 9: positive inclusion on the element support, independent of its parent.
No equality between different elements' inclusion probabilities is required. -/
def ParentIndependentInclusion (S : Scheme V) (a : V → ℝ) : Prop :=
  (∀ x, 0 < S.pointMass x → 0 < a x) ∧
  (∀ K, 0 < S.μ K → ∀ x ∈ K, S.incl K x = a x)

/-- The actual minimum ξ of the a_x on positive-marginal elements.
The empty-support value is 0; Scheme.IsValid rules that case out. -/
def inclusionMinimum (S : Scheme V) (a : V → ℝ) : ℝ :=
  let values := (univ.filter (fun x => 0 < S.pointMass x)).image a
  if h : values.Nonempty then values.min' h else 0

/-- Absolute expected Hamming error on a top face, using the published error count. -/
def averageError (S : Scheme V) (F : Finset V → V → α) (g : V → α) : ℝ :=
  ∑ K, S.μ K * (errCount F g K : ℝ)

/-- Expected relative Hamming error. N is positive whenever Scheme.IsValid holds. -/
def normalizedAverageError (S : Scheme V) (F : Finset V → V → α) (g : V → α) : ℝ :=
  ∑ K, S.μ K * ((errCount F g K : ℝ) / (S.N : ℝ))

/-- The event of §2: d(F_K,g|_K) ≥ δ q_k, including equality at the threshold. -/
def approximateDisagreementProb (S : Scheme V) (F : Finset V → V → α)
    (g : V → α) (δ : ℝ) : ℝ :=
  ∑ K, S.μ K * (if δ * (S.N : ℝ) ≤ (errCount F g K : ℝ) then 1 else 0)

end
end AgreementTop736.Exact.Supplement


