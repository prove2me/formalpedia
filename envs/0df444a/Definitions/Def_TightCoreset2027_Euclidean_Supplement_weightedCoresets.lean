-- Prove2me | Definitions.Def_TightCoreset2027_Euclidean_Supplement_weightedCoresets
-- name    : TightCoreset2027_Euclidean_Supplement_weightedCoresets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:08:43.040424+00:00
-- url     : https://prove2.me/theorems/bfb3e9ef-fffc-4454-93cc-6a07a08eaaa3
-- title:
--   Weighted-input strong coresets for exact-k and at-most-k queries
-- statement:
--   Let X be a finite subset of a metric space E, let u be its input weights, and let S⊆X have output weights w. For a nonempty finite ambient query C, reuse the published nearest-center distance and weighted clustering cost
--
--   $$d(p,C)=\min_{c\in C}d(p,c),\qquad Q_z(X,u,C)=\sum_{p\in X}u(p)d(p,C)^z.$$
--
--   An exact-k weighted-input strong ε-coreset satisfies
--
--   $$|Q_z(S,w,C)-Q_z(X,u,C)|\le\varepsilon Q_z(X,u,C)\qquad (|C|=k).$$
--
--   The separate at-most-k predicate imposes the same inequality for every finite ambient query with 1≤|C|≤k. Both predicates require S⊆X. Centers may lie anywhere in E. Input positivity and the valid parameter ranges are imposed by the using theorems; output weights are arbitrary nonnegative real numbers, represented by NNReal. Weights are functions on E whose values outside the respective finite set are ignored. Empty inputs and candidates are permitted. A zero true cost requires exact preservation. These predicates add no mass constraint or sampling law.
--
--   This extends the published unweighted-input model without changing its costs or its exact-k convention, and keeps the stronger query class of Lemma 4.1 separate.
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), Definition 1.1 and §4 weighted-input preamble / Lemma 4.1, printed p. 1, 28 / PDF p. 3, 30; canonical source.pdf SHA256 9c247b18d4e2080420cb421dad0fe6c53b99885cef599b8f8e3cd8d639e13d5f.

import Definitions.Def_TightCoreset2027_Euclidean_coresetModel
set_option autoImplicit false

namespace TightCoreset2027.Euclidean.Supplement

/-- Definition 1.1 with positive input weights supplied by theorems: exact-k ambient queries. -/
def IsWeightedStrongCoreset {E : Type*} [MetricSpace E]
    (z ε : ℝ) (k : ℕ) (X : Finset E) (u : E → NNReal)
    (S : Finset E) (w : E → NNReal) : Prop :=
  S ⊆ X ∧ ∀ C : Finset E, C.card = k →
    |weightedCost z S w C - weightedCost z X u C| ≤ ε * weightedCost z X u C

/-- Lemma 4.1 preserves every nonempty ambient query with at most k distinct centers. -/
def IsWeightedAtMostCoreset {E : Type*} [MetricSpace E]
    (z ε : ℝ) (k : ℕ) (X : Finset E) (u : E → NNReal)
    (S : Finset E) (w : E → NNReal) : Prop :=
  S ⊆ X ∧ ∀ C : Finset E, 1 ≤ C.card → C.card ≤ k →
    |weightedCost z S w C - weightedCost z X u C| ≤ ε * weightedCost z X u C

end TightCoreset2027.Euclidean.Supplement


