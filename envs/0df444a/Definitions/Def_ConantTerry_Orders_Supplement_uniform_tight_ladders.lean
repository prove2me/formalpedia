-- Prove2me | Definitions.Def_ConantTerry_Orders_Supplement_uniform_tight_ladders
-- name    : ConantTerry_Orders_Supplement_uniform_tight_ladders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:23:33.197713+00:00
-- url     : https://prove2.me/theorems/7ed80419-87f9-4a2e-ac74-f561f8a046ac
-- title:
--   Uniform and tight ladders
-- statement:
--   Let $X,Y$ be arbitrary sets, $f:X\times Y\to[0,1]$, and $k\ge1$. A uniform $(k,\delta)$-ladder consists of labels $x_1,\ldots,x_k\in X$, $y_1,\ldots,y_k\in Y$ and one $r\in[0,1]$ such that
--   $$
--   f(x_i,y_j)\ge r+\delta\quad(i\le j),\qquad f(x_i,y_j)\le r\quad(i>j).
--   $$
--   It is $\epsilon$-tight if there are intervals $I,J\subseteq[0,1]$, each of length at most $\epsilon$, with
--   $$
--   f(x_i,y_j)\in I\quad(i\le j),\qquad f(x_i,y_j)\in J\quad(i>j).
--   $$
--   Admission means existence of these labels and the common threshold. This extends the published ladder predicate with uniformity and tightness and is shared by Lemma 4.2 and Theorem 1.14.
--
--   **Formalization Note** Indices use `Fin k`, with the diagonal high. An interval is an order-convex subset of the unit interval; length at most $\epsilon$ means $|u-v|\le\epsilon$ for every two of its elements. Since the ambient interval is bounded, this is the usual length bound for every endpoint convention, including empty and singleton intervals. No distinctness of labels is imposed. The predicates are defined for all natural lengths and real scales; consumer theorems state the source's positive domains.
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p. 3, Definition 1.4(2)–(3)

import Mathlib
import Definitions.Def_ConantTerry_Orders_ladder

namespace ConantTerry.Orders.Supplement

/-- An interval in the unit interval with length at most ε. Order convexity
allows every endpoint convention and the empty interval. The pairwise width
condition is equivalent to the usual interval length bound, including singletons. -/
def IsSmallInterval (ε : ℝ) (I : Set (Set.Icc (0 : ℝ) 1)) : Prop :=
  I.OrdConnected ∧ ∀ u ∈ I, ∀ v ∈ I, |(u : ℝ) - (v : ℝ)| ≤ ε

/-- Definition 1.4(2), p.3: the published ladder with a constant threshold. -/
def IsUniformLadder {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (k : ℕ) (δ : ℝ)
    (x : Fin k → X) (y : Fin k → Y) (r : Set.Icc (0 : ℝ) 1) : Prop :=
  IsLadder f k δ x y (fun _ => r)

/-- Definition 1.4(3), p.3: both triangular regions are in small intervals;
the diagonal belongs to the high region. -/
def IsTightLadder {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (k : ℕ) (δ ε : ℝ)
    (x : Fin k → X) (y : Fin k → Y) (r : Set.Icc (0 : ℝ) 1) : Prop :=
  IsUniformLadder f k δ x y r ∧
    ∃ I J : Set (Set.Icc (0 : ℝ) 1),
      IsSmallInterval ε I ∧ IsSmallInterval ε J ∧
        ∀ i j : Fin k, (i ≤ j → f (x i, y j) ∈ I) ∧
          (j < i → f (x i, y j) ∈ J)

/-- Admission is existence of actual labels and a common threshold. -/
def AdmitsUniformLadder {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (k : ℕ) (δ : ℝ) : Prop :=
  ∃ (x : Fin k → X) (y : Fin k → Y) (r : Set.Icc (0 : ℝ) 1),
    IsUniformLadder f k δ x y r

/-- A tight ladder is already uniform, not a separate non-uniform predicate. -/
def AdmitsTightLadder {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (k : ℕ) (δ ε : ℝ) : Prop :=
  ∃ (x : Fin k → X) (y : Fin k → Y) (r : Set.Icc (0 : ℝ) 1),
    IsTightLadder f k δ ε x y r

end ConantTerry.Orders.Supplement


