-- Prove2me | Definitions.Def_FasterDistributedMatching_ApproximateMatching_Pairwise
-- name    : FasterDistributedMatching_ApproximateMatching_Pairwise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:11:57.018557+00:00
-- url     : https://prove2.me/theorems/958e8860-4ead-455f-8f2b-ea7439413cd3
-- title:
--   Finite labels, local pairwise objectives and exact expectations
-- statement:
--   Each vertex of a variable graph has a finite set of label names and a normalized real probability mass function supported on that set. Every positive label probability is at least $\lambda\in(0,1/2]$. Nonnegative utility and cost tables depend on one vertex label or two adjacent vertex labels. Multiple terms may be aggregated into ordered incident tables. Their totals are $U(s)$ and $C(s)$.
--
--   $$\mathbb E[f]=\sum_s\left(\prod_v p_v(s_v)\right)f(s)$$
--
--   is a finite sum over the product of the actual label sets. Initial processor data contain the local label set, its probabilities, its unary tables, both ordered tables incident to each neighbor, and its supplied color. Table entries outside finite label domains are masked to zero. The empty variable graph has the unique empty assignment and objective zero.
--
--   This interface supplies the exact utility-cost formulation of local derandomization without an integrability or default-integral issue.
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Lemma 2.2 and preceding paragraph, printed p.7, PDF p.9; §3.2, printed pp.11–12, PDF pp.13–14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_StageData

namespace FasterDistributedMatching.ApproximateMatching

/-! Finite pairwise objectives, §2 Lemma 2.2. Labels are arbitrary finite sets of natural
names. A sum of any number of unary/pair terms can be aggregated in these tables. -/
structure PairwiseInstance (N : ℕ) where
  graph : SimpleGraph (Fin N)
  labels : Fin N → Finset ℕ
  probability : Fin N → ℕ → ℝ
  unaryUtility : Fin N → ℕ → ℝ
  unaryCost : Fin N → ℕ → ℝ
  pairUtility : Fin N → Fin N → ℕ → ℕ → ℝ
  pairCost : Fin N → Fin N → ℕ → ℕ → ℝ

/- Ordered adjacent-pair tables may be asymmetric. Summing them once each represents
an arbitrary list of pair terms without a vertex order becoming processor input. -/
open Classical in
noncomputable def utility {N : ℕ} (D : PairwiseInstance N) (s : Fin N → ℕ) : ℝ :=
  ∑ v, D.unaryUtility v (s v) +
    ∑ v, ∑ w ∈ D.graph.neighborFinset v, D.pairUtility v w (s v) (s w)

open Classical in
noncomputable def cost {N : ℕ} (D : PairwiseInstance N) (s : Fin N → ℕ) : ℝ :=
  ∑ v, D.unaryCost v (s v) +
    ∑ v, ∑ w ∈ D.graph.neighborFinset v, D.pairCost v w (s v) (s w)

noncomputable def finiteExpectation {N : ℕ} (D : PairwiseInstance N)
    (f : (Fin N → ℕ) → ℝ) : ℝ :=
  ∑ s : (v : Fin N) → ↥(D.labels v),
    (∏ v, D.probability v (s v)) * f (fun v => s v)

def ValidObjective {N : ℕ} (D : PairwiseInstance N) (lambda : ℝ) : Prop :=
  0 < lambda ∧ lambda ≤ 1 / 2 ∧
  (∀ v, (∑ a ∈ D.labels v, D.probability v a) = 1) ∧
  (∀ v a, 0 ≤ D.probability v a ∧ (a ∉ D.labels v → D.probability v a = 0) ∧
    (0 < D.probability v a → lambda ≤ D.probability v a)) ∧
  (∀ v a, 0 ≤ D.unaryUtility v a ∧ 0 ≤ D.unaryCost v a) ∧
  (∀ v w a b, 0 ≤ D.pairUtility v w a b ∧ 0 ≤ D.pairCost v w a b)

structure ObjectiveInput where
  neighbors : Finset ℕ
  labels : Finset ℕ
  probability : ℕ → ℝ
  unaryUtility : ℕ → ℝ
  unaryCost : ℕ → ℝ
  /- Both ordered incident tables are locally known. -/
  tables : ℕ → (ℕ → ℕ → ℝ) × (ℕ → ℕ → ℝ) × (ℕ → ℕ → ℝ) × (ℕ → ℕ → ℝ)
  color : ℕ

open Classical in
noncomputable def objectiveInput {N : ℕ} (D : PairwiseInstance N) (ids : Fin N → ℕ)
    (col : Fin N → ℕ) (v : Fin N) : ObjectiveInput where
  neighbors := neighborIDs D.graph ids v
  labels := D.labels v
  probability := D.probability v
  unaryUtility := fun a => if a ∈ D.labels v then D.unaryUtility v a else 0
  unaryCost := fun a => if a ∈ D.labels v then D.unaryCost v a else 0
  tables := fun j =>
    (fun a b => ∑ w ∈ D.graph.neighborFinset v, if ids w = j ∧ a ∈ D.labels v ∧ b ∈ D.labels w then D.pairUtility v w a b else 0,
     fun a b => ∑ w ∈ D.graph.neighborFinset v, if ids w = j ∧ a ∈ D.labels v ∧ b ∈ D.labels w then D.pairCost v w a b else 0,
     fun a b => ∑ w ∈ D.graph.neighborFinset v, if ids w = j ∧ a ∈ D.labels v ∧ b ∈ D.labels w then D.pairUtility w v b a else 0,
     fun a b => ∑ w ∈ D.graph.neighborFinset v, if ids w = j ∧ a ∈ D.labels v ∧ b ∈ D.labels w then D.pairCost w v b a else 0)
  color := col v

end FasterDistributedMatching.ApproximateMatching


