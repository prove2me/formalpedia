-- Prove2me | Definitions.Def_WeightedRainbowCycle_Weighted_Reachability
-- name    : WeightedRainbowCycle_Weighted_Reachability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:23.140375+00:00
-- url     : https://prove2.me/theorems/ca3f3e2b-4542-4f62-91a3-afd28655ddc0
-- title:
--   Full-list rainbow walks, genuine cycles and random reachability
-- statement:
--   Let $G$ be a weighted list graph. A length-$r$ walk is a sequence of vertices $v_0,\ldots,v_r$ and incident edge identities $e_0,\ldots,e_{r-1}$ with $e_i$ joining $v_i$ to $v_{i+1}$. It is rainbow when the entire sets $L(e_i)$ are pairwise disjoint. A rainbow cycle is such a walk with $r\ge2$, $v_r=v_0$, distinct edges, and distinct $v_0,\ldots,v_{r-1}$. Thus two distinct parallel edges can form a cycle, while traversing one edge twice cannot; in a simple graph the minimum cycle length is three.
--
--   For $x\in V(G)$ and $A\subseteq C$, define
--
--   $$U_x(A)=\{y:\text{a rainbow walk from }x\text{ to }y\text{ uses only edges }e\text{ with }L(e)\subseteq A\}.$$
--
--   The empty walk is permitted, so $x\in U_x(A)$. On the finite active color set, a Boolean vector $z$ specifies the sampled subset $A(z)$. The two finite observables are
--
--   $$g_x(z)=\log|U_x(A(z))|,\qquad h_x(z)=\frac{|\partial_G U_x(A(z))|_w}{|U_x(A(z))|}.$$
--
--   These operational definitions are used in Lemma 4.2 and in the goal's cycle conclusion. Selecting one representative color per list would define a different, weaker property.
--
--   **Formalization Note** Sequence indices start at zero. Reachability is a finite set defined by existence of actual walks; it is not supplied as free data. Sampling only active colors preserves every reachable set and boundary observable for arbitrary ambient color sets. Expectations use the published finite Bernoulli polynomial, without a clipping operation or integration convention.
-- source:
--   Andrew D. Lin, STOC 2027 submission #545 (October 2026), §2 proof, p. 5; Theorem 1.1 and proof setup, p. 8; Lemma 4.2 and its proof, pp. 8, 10–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/545.pdf

import Definitions.Def_WeightedRainbowCycle_Weighted_Model
import Definitions.Def_DiffNeighbors_Bias_Model

set_option autoImplicit false
noncomputable section

namespace WeightedRainbowCycle.Weighted

variable {V E C : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq C]

/-- An actual consecutive edge walk whose entire edge lists are pairwise disjoint.
The zero-edge walk is permitted. -/
def RainbowWalk (G : Model V E C) (n : ℕ) (v : Fin (n + 1) → V) (e : Fin n → E) : Prop :=
  (∀ i, G.graph.IsLink (e i) (v i.castSucc) (v i.succ)) ∧
    ∀ i j, i ≠ j → Disjoint (G.colors (e i)) (G.colors (e j))

/-- A nonempty simple closed walk, with distinct edges and distinct vertices before closing.
Two distinct parallel edges may form a cycle, but using one edge twice never does. -/
def HasRainbowCycle (G : Model V E C) : Prop :=
  ∃ (n : ℕ) (v : Fin (n + 1) → V) (e : Fin n → E),
    2 ≤ n ∧ RainbowWalk G n v e ∧ v 0 = v (Fin.last n) ∧
    Function.Injective (fun i : Fin n => v i.castSucc) ∧ Function.Injective e

/-- U_x(A), including x via the empty walk; all colors of every used edge lie in A. -/
def Model.reachable (G : Model V E C) (x : V) (A : Set C) : Finset V := by
  classical
  exact Finset.univ.filter (fun y =>
    ∃ (n : ℕ) (v : Fin (n + 1) → V) (e : Fin n → E),
      RainbowWalk G n v e ∧ v 0 = x ∧ v (Fin.last n) = y ∧
        ∀ i, ∀ c ∈ G.colors (e i), c ∈ A)

/-- Turn a Boolean vector on the finite active color support into a subset of the ambient C. -/
def Model.sampledColors (G : Model V E C) (z : {c // c ∈ G.activeColors} → Bool) : Set C :=
  {c | ∃ a : {c // c ∈ G.activeColors}, a.val = c ∧ z a = true}

/-- Finite observable log |U_x(A)|. -/
def Model.logReach (G : Model V E C) (x : V) (z : {c // c ∈ G.activeColors} → Bool) : ℝ :=
  Real.log (G.reachable x (G.sampledColors z)).card

/-- Finite observable boundary mass / reachable cardinality, before taking its expectation. -/
def Model.boundaryRatio (G : Model V E C) (x : V) (z : {c // c ∈ G.activeColors} → Bool) : ℝ :=
  G.boundaryMass (G.reachable x (G.sampledColors z)) /
    (G.reachable x (G.sampledColors z)).card

end WeightedRainbowCycle.Weighted


