-- Prove2me | Definitions.Def_SubsetSumPartialMatch_SubsetSum_DegreePairs
-- name    : SubsetSumPartialMatch_SubsetSum_DegreePairs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:28.447024+00:00
-- url     : https://prove2.me/theorems/6a2b66db-67c7-48a8-8d3c-7f40e86cb612
-- title:
--   Degree-pair lists and the rebalancing recursion
-- statement:
--   A **degree-pair list** is a finite nonempty list $W$ of pairs $(a,b)$ of reals with $a,b\ge1$, repeated pairs counting separately. Its **volume** is $\rho_W(t)=\sum_{(a,b)\in W}a^tb^{1-t}$. The one-element lists $[(A,1)]$ and $[(1,B)]$ with $A,B\ge1$ are **trivial**.
--
--   For lists $W_1,\dots,W_m$ the functions $F_d$ are given by
--   $$F_0(\lambda)=1+\lambda,\qquad F_d(\lambda)=\min_{1\le i\le m}\ \sum_{(a,b)\in W_i}a\,F_{d-1}\!\left(\lambda\frac ba\right)\quad(d\ge1).$$
--
--   **Formalization Note** The minimum over the finite index set is an infimum over `Fin m`, which equals the minimum when $m\ge1$; Lemma 3.4 assumes trivial lists exist, so $m\ge1$ there. The recursion is defined for all real arguments and used only at $\lambda>0$, where every argument stays positive.
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 20, §3.3.2, degree-pair lists and Lemma 3.4

import Mathlib

namespace SubsetSumPartialMatch.SubsetSum

/-- A degree-pair list: a finite nonempty list of real pairs `(a, b)` with `a, b ≥ 1`. Repeated
pairs count separately. -/
def IsDegreePairList (W : List (ℝ × ℝ)) : Prop :=
  W ≠ [] ∧ ∀ p ∈ W, 1 ≤ p.1 ∧ 1 ≤ p.2

/-- The volume `ρ_W(t) = ∑_{(a,b) ∈ W} a^t b^{1-t}`. -/
noncomputable def listVolume (W : List (ℝ × ℝ)) (t : ℝ) : ℝ :=
  (W.map fun p => p.1 ^ t * p.2 ^ (1 - t)).sum

/-- The trivial list `[(A, 1)]` with `A ≥ 1`. -/
def IsTrivialLeft (W : List (ℝ × ℝ)) : Prop := ∃ A : ℝ, 1 ≤ A ∧ W = [(A, 1)]

/-- The trivial list `[(1, B)]` with `B ≥ 1`. -/
def IsTrivialRight (W : List (ℝ × ℝ)) : Prop := ∃ B : ℝ, 1 ≤ B ∧ W = [(1, B)]

/-- The recursion `F_0(λ) = 1 + λ`,
`F_d(λ) = min_i ∑_{(a,b) ∈ W_i} a F_{d-1}(λ b / a)`. The minimum is over the finite index set
`Fin m`, which is nonempty wherever this is used. -/
noncomputable def recF {m : ℕ} (W : Fin m → List (ℝ × ℝ)) : ℕ → ℝ → ℝ
  | 0, lam => 1 + lam
  | d + 1, lam => ⨅ i, ((W i).map fun p => p.1 * recF W d (lam * p.2 / p.1)).sum

end SubsetSumPartialMatch.SubsetSum


