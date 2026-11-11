-- Prove2me | Definitions.Def_SpacePropTest_ChainTree
-- name    : SpacePropTest_ChainTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:54.280198+00:00
-- url     : https://prove2.me/theorems/67ec3350-d731-4863-b627-afba1c098a11
-- title:
--   Closed communicating classes and arborescences of a chain; the weights $\|W(C)\|$, $\|W_s(C)\|$ (Definitions 60–61)
-- statement:
--   View a finite chain $C$ with start state $s^\star$ as the directed graph with an edge $s\to s'$ iff $C(s,s')>0$.
--
--   1. A **closed communicating class** (Definition 60) is a maximal set $V$ of states such that any two states of $V$ communicate (each is reachable from the other) and no edge leaves $V$. Let $d$ be the number of such classes.
--   2. An **arborescence** (Definition 61) is a spanning directed forest of this graph with exactly $d$ components whose edges point toward the roots: every non-root has outdegree one, every root outdegree zero.
--   3. For an arborescence $F$, $W(C,F)=\prod_{(u,v)\in F}C(u,v)$; $\|W(C)\|=\sum_F W(C,F)$ over all arborescences, and $\|W_s(C)\|=\sum_{F\in\mathcal F_s(C)}W(C,F)$ over those in which $s^\star$ lies in the tree rooted at $s$ ($0$ if there are none).
--
--   These are the objects of the Markov chain tree theorem (Theorem 62).
--
--   **Formalization Note** An arborescence is given by its parent map $u\mapsto$ (`none` for a root, `some v` for the edge $u\to v$): edges are positive transitions, following parents from any state reaches a root (no cycles), and the number of roots is $d$. The root of $s^\star$'s tree is reached after $|\sigma|$ parent steps.
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), App. A.1, Definitions 60–61, p.52 (PDF 54); weights, p.53 (PDF 55)

import Mathlib

set_option autoImplicit false

namespace SpacePropTest

noncomputable section

open Classical

/-- **Closed communicating classes and arborescences of a finite chain** (C. Canonne, X. Chen,
W. Pires, T. Pitassi, R. A. Servedio, *The Space Complexity of Property Testing*, manuscript of
November 2, 2026, sha256 65850aa6…; App. A.1, Definitions 60–61, p.52 (PDF 54), and the weights
`W(C,F)`, `‖W(C)‖`, `‖W_s(C)‖`, p.53 (PDF 55)).

The chain `C` is viewed as the directed graph on `σ` with an edge `s → s'` iff `C(s, s') > 0`.
`Reach C u v`: `v` is reachable from `u` by a (possibly empty) sequence of positive transitions. -/
def Reach {σ : Type*} (C : Matrix σ σ ℝ) (u v : σ) : Prop :=
  Relation.ReflTransGen (fun a b => 0 < C a b) u v

/-- `u` and `v` communicate: each is reachable from the other. -/
def Communicate {σ : Type*} (C : Matrix σ σ ℝ) (u v : σ) : Prop :=
  Reach C u v ∧ Reach C v u

/-- `V` is closed and communicating: all pairs in `V` communicate and no positive transition
leaves `V`. -/
def ClosedComm {σ : Type*} (C : Matrix σ σ ℝ) (V : Finset σ) : Prop :=
  (∀ u ∈ V, ∀ v ∈ V, Communicate C u v) ∧ (∀ u ∈ V, ∀ v, 0 < C u v → v ∈ V)

/-- A closed communicating class (Definition 60): a maximal (non-empty) set `V` that is closed
and communicating. -/
def IsClosedClass {σ : Type*} (C : Matrix σ σ ℝ) (V : Finset σ) : Prop :=
  V.Nonempty ∧ ClosedComm C V ∧ ∀ W : Finset σ, V ⊆ W → ClosedComm C W → W = V

/-- `d`, the number of closed communicating classes of `C`. -/
def numClosedClasses {σ : Type*} [Fintype σ] (C : Matrix σ σ ℝ) : ℕ :=
  (Finset.univ.filter (fun V : Finset σ => IsClosedClass C V)).card

/-- One step toward the root along a parent map (`par u = none` marks a root, which stays put). -/
def follow {σ : Type*} (par : σ → Option σ) (u : σ) : σ := (par u).getD u

/-- The root of the tree containing `u`: follow parents `|σ|` times. -/
def rootOf {σ : Type*} [Fintype σ] (par : σ → Option σ) (u : σ) : σ :=
  (follow par)^[Fintype.card σ] u

/-- An arborescence of `C` (Definition 61), given by its parent map `par`: the edge set is
`{(u, v) : par u = some v}`; every edge is a positive transition of `C`; following parents from
any vertex reaches a root (no cycles), so the edges form a spanning directed forest directed toward
the roots, in which every non-root vertex has outdegree one and every root outdegree zero; and the
number of roots (= components) equals the number `d` of closed communicating classes. -/
def IsArborescence {σ : Type*} [Fintype σ] (C : Matrix σ σ ℝ) (par : σ → Option σ) : Prop :=
  (∀ u v, par u = some v → 0 < C u v) ∧
  (∀ u, ∃ k : ℕ, par ((follow par)^[k] u) = none) ∧
  (Finset.univ.filter (fun u => par u = none)).card = numClosedClasses C

/-- `F(C)`, the set of all arborescences of `C`. -/
def arbs {σ : Type*} [Fintype σ] [DecidableEq σ] (C : Matrix σ σ ℝ) : Finset (σ → Option σ) :=
  Finset.univ.filter (fun par => IsArborescence C par)

/-- `W(C, F) = ∏_{(u,v) ∈ F} C(u, v)`. -/
def treeWeight {σ : Type*} [Fintype σ] (C : Matrix σ σ ℝ) (par : σ → Option σ) : ℝ :=
  ∏ u, (par u).elim 1 (fun v => C u v)

/-- `‖W(C)‖ = ∑_{F ∈ F(C)} W(C, F)`. -/
def Wnorm {σ : Type*} [Fintype σ] [DecidableEq σ] (C : Matrix σ σ ℝ) : ℝ :=
  ∑ par ∈ arbs C, treeWeight C par

/-- `‖W_s(C)‖ = ∑_{F ∈ F_s(C)} W(C, F)`, where `F_s(C)` are the arborescences in which the start
state `s₀` lies in the tree rooted at `s` (the empty sum `0` when `F_s(C) = ∅`). -/
def WnormAt {σ : Type*} [Fintype σ] [DecidableEq σ] (C : Matrix σ σ ℝ) (s₀ s : σ) : ℝ :=
  ∑ par ∈ (arbs C).filter (fun par => rootOf par s₀ = s), treeWeight C par

end

end SpacePropTest


