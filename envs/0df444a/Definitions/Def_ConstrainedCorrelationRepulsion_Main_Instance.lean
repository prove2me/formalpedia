-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Instance
-- name    : ConstrainedCorrelationRepulsion_Main_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:24:09.326359+00:00
-- url     : https://prove2.me/theorems/d0358926-1e01-40ab-9354-e96da0e08e97
-- title:
--   Finite signed instances, constrained optima, and the two full LPs
-- statement:
--   A complete signed graph on $V=\{0,\ldots,n-1\}$ has a positive or negative label on every unordered pair of distinct vertices. Two additional pair sets $M,H$ require endpoints to be together or apart. A partition is represented by vertex labels, and is feasible exactly when it satisfies both requirements. The disagreement cost counts positive pairs split and negative pairs joined, once each; $\mathrm{OPT}(I)$ minimizes that cost over feasible partitions.
--
--   Arbitrary real separation/joining costs $w^+,w^-$ are used for true twins; probability weights instead have the form $(p,1-p)$ with $p\in[0,1]$. The metric LP is the bounded symmetric pseudometric relaxation with zero diagonal, triangles, $x_M=0$ and $x_H=1$. The full cluster LP puts nonnegative weight on nonempty feasible cluster sets, covers each vertex once, and defines $x_{uv}=1-\sum_{C\ni u,v}\lambda_C$. These two LPs are separate from the bounded sub-cluster LP.
--
--   The empty vertex set and its empty partition are included. Weighted optima are real infima of finite nonempty feasible cost sets whenever used; their off-domain default is not a theorem hypothesis or conclusion.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), §§1, 2.1, 3.1, printed pp.1, 4, 13–14 (PDF pp.2, 5, 14–15)

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace ConstrainedCorrelationRepulsion.Main

open scoped BigOperators
open Classical

/-- §1, printed p.1: a complete signed graph, with arbitrary must- and cannot-links.
The simple graph `positive` encodes the positive pairs; its off-diagonal complement is negative.
No compatibility between the three graphs is imposed. -/
structure Instance (n : ℕ) where
  positive : SimpleGraph (Fin n)
  mustLink : SimpleGraph (Fin n)
  cannotLink : SimpleGraph (Fin n)

/-- A finite partition is encoded by labels. Every partition has such a labelling, including
the unique empty partition when n=0. Two vertices are together exactly when their labels agree. -/
abbrev Partition (n : ℕ) := Fin n → Fin n

def Feasible {n : ℕ} (I : Instance n) (P : Partition n) : Prop :=
  (∀ u v, I.mustLink.Adj u v → P u = P v) ∧
  (∀ u v, I.cannotLink.Adj u v → P u ≠ P v)

def FeasibleInput {n : ℕ} (I : Instance n) : Prop := ∃ P, Feasible I P

noncomputable def cost {n : ℕ} (I : Instance n) (P : Partition n) : ℕ :=
  CorrClustBBC.Cautious.mistakes I.positive (fun u v => P u = P v)

/-- Constrained optimum. On infeasible inputs the natural infimum is 0; every result about
this quantity either assumes feasibility or has an independent feasible construction. -/
noncomputable def OPT {n : ℕ} (I : Instance n) : ℕ :=
  sInf {k : ℕ | ∃ P, Feasible I P ∧ cost I P = k}

def Optimal {n : ℕ} (I : Instance n) (P : Partition n) : Prop :=
  Feasible I P ∧ ∀ Q, Feasible I Q → cost I P ≤ cost I Q

noncomputable def pairSum {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, if u < v then f u v else 0

/-- Arbitrary real separation and co-clustering costs, used only for Theorem 2.1.
An unordered-pair index makes symmetry structural; diagonal values are never charged. -/
structure PairCosts (n : ℕ) where
  separate : Sym2 (Fin n) → ℝ
  together : Sym2 (Fin n) → ℝ

noncomputable def weightedCost {n : ℕ} (w : PairCosts n) (P : Partition n) : ℝ :=
  pairSum (fun u v => if P u = P v then w.together s(u,v) else w.separate s(u,v))

noncomputable def weightedOPT {n : ℕ} (I : Instance n) (w : PairCosts n) : ℝ :=
  sInf {z : ℝ | ∃ P, Feasible I P ∧ weightedCost w P = z}

def WeightedOptimal {n : ℕ} (I : Instance n) (w : PairCosts n) (P : Partition n) : Prop :=
  Feasible I P ∧ ∀ Q, Feasible I Q → weightedCost w P ≤ weightedCost w Q

/-- Probability weights are complementary costs, and are distinct from arbitrary pair costs. -/
structure ProbabilityWeights (n : ℕ) where
  positive : Sym2 (Fin n) → ℝ
  lower : ∀ e, 0 ≤ positive e
  upper : ∀ e, positive e ≤ 1

def probabilityCosts {n : ℕ} (p : ProbabilityWeights n) : PairCosts n :=
  ⟨p.positive, fun e => 1 - p.positive e⟩

def MetricFeasible {n : ℕ} (I : Instance n) (x : Fin n → Fin n → ℝ) : Prop :=
  (∀ u, x u u = 0) ∧ (∀ u v, x u v = x v u) ∧
  (∀ u v, 0 ≤ x u v ∧ x u v ≤ 1) ∧
  (∀ u v t, x u v ≤ x u t + x t v) ∧
  (∀ u v, I.mustLink.Adj u v → x u v = 0) ∧
  (∀ u v, I.cannotLink.Adj u v → x u v = 1)

noncomputable def lpObjective {n : ℕ} (w : PairCosts n) (x : Fin n → Fin n → ℝ) : ℝ :=
  pairSum (fun u v => w.separate s(u,v) * x u v + w.together s(u,v) * (1 - x u v))

noncomputable def signedCosts {n : ℕ} (I : Instance n) : PairCosts n :=
  ⟨fun e => if e ∈ I.positive.edgeSet then 1 else 0,
   fun e => if e ∈ I.positive.edgeSet then 0 else 1⟩

def MetricOptimal {n : ℕ} (I : Instance n) (w : PairCosts n)
    (x : Fin n → Fin n → ℝ) : Prop :=
  MetricFeasible I x ∧ ∀ z, MetricFeasible I z → lpObjective w x ≤ lpObjective w z

def FeasibleCluster {n : ℕ} (I : Instance n) (C : Finset (Fin n)) : Prop :=
  C.Nonempty ∧ (∀ u v, I.mustLink.Adj u v → (u ∈ C ↔ v ∈ C)) ∧
  (∀ u ∈ C, ∀ v ∈ C, ¬ I.cannotLink.Adj u v)

/-- Full cluster LP (§3.1), with zero entries on ineligible sets. This is not the bounded LP. -/
def ClusterFeasible {n : ℕ} (I : Instance n) (lam : Finset (Fin n) → ℝ)
    (x : Fin n → Fin n → ℝ) : Prop :=
  (∀ C, 0 ≤ lam C) ∧ (∀ C, ¬ FeasibleCluster I C → lam C = 0) ∧
  (∀ v, (∑ C : Finset (Fin n), if v ∈ C then lam C else 0) = 1) ∧
  (∀ u v, u ≠ v → x u v = 1 -
    ∑ C : Finset (Fin n), if u ∈ C ∧ v ∈ C then lam C else 0) ∧
  (∀ u, x u u = 0)

def ClusterOptimal {n : ℕ} (I : Instance n) (w : PairCosts n)
    (lam : Finset (Fin n) → ℝ) (x : Fin n → Fin n → ℝ) : Prop :=
  ClusterFeasible I lam x ∧ ∀ mu z, ClusterFeasible I mu z →
    lpObjective w x ≤ lpObjective w z

end ConstrainedCorrelationRepulsion.Main


