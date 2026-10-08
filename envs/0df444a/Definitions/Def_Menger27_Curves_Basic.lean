-- Prove2me | Definitions.Def_Menger27_Curves_Basic
-- name    : Menger27_Curves_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:08:46.66298+00:00
-- url     : https://prove2.me/theorems/9f1734b1-b639-4592-a935-867f79263372
-- title:
--   pp. 96–98 — regular points, order, arcs, and topological n-legs
-- statement:
--   Let $X$ be a topological space and $p\in X$. A point is **regular** if every open neighbourhood of it contains an open neighbourhood with finite boundary. It has **order at most $n$** if each such neighbourhood contains one whose boundary has at most $n$ points. It has **order $n$** if it has order at most $n$ and not order at most any smaller integer. For a compact connected metric space, **regular curve** means that every point is regular.
--
--   An **arc** in $X$ is a continuous injective map $\gamma:[0,1]\to X$. A **topological $n$-leg** at $p$ consists of arcs $\gamma_i$, indexed by $i=1,\dots,n$, with $\gamma_i(0)=p$ and
--   $$\gamma_i([0,1])\cap\gamma_j([0,1])=\{p\}\qquad(i\ne j).$$
--
--   These definitions record the local order and the nondegenerate arcs used throughout Part I. **Formalization Note** A neighbourhood is open; boundary counts use extended cardinality, so an infinite boundary never counts as zero. Parameter zero fixes the orientation of an arc ending at $p$.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), pp. 96–98, definitions of regular point, point order, regular curve, and the Theorem

import Mathlib

namespace Menger27.Curves

/-- Menger's regular point: arbitrarily small open neighbourhoods have finite boundary. -/
def IsRegularPoint {X : Type*} [TopologicalSpace X] (p : X) : Prop :=
  ∀ W : Set X, IsOpen W → p ∈ W →
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ⊆ W ∧ (frontier V).Finite

/-- Boundary cardinalities at most `n` occur in arbitrarily small neighbourhoods. -/
def OrderAtMost {X : Type*} [TopologicalSpace X] (p : X) (n : ℕ) : Prop :=
  ∀ W : Set X, IsOpen W → p ∈ W →
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ⊆ W ∧ (frontier V).encard ≤ n

/-- Exact order includes minimality, including the case `n = 0`. -/
def HasOrder {X : Type*} [TopologicalSpace X] (p : X) (n : ℕ) : Prop :=
  OrderAtMost p n ∧ ∀ m : ℕ, m < n → ¬ OrderAtMost p m

/-- A compact connected metric curve all of whose points are regular. -/
def IsRegularCurve (X : Type*) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] : Prop :=
  ∀ p : X, IsRegularPoint p

/-- A parameterized topological arc, with its endpoints at parameters zero and one. -/
def IsArc {X : Type*} [TopologicalSpace X]
    (γ : unitInterval → X) : Prop :=
  Continuous γ ∧ Function.Injective γ

/-- `n` arcs end at `p` and any two meet exactly at `p`. -/
def HasNBein {X : Type*} [TopologicalSpace X] (p : X) (n : ℕ) : Prop :=
  ∃ γ : Fin n → unitInterval → X,
    (∀ i, IsArc (γ i) ∧ γ i 0 = p) ∧
      ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) = {p}

end Menger27.Curves


