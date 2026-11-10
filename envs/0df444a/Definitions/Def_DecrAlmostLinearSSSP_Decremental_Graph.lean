-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_Decremental_Graph
-- name    : DecrAlmostLinearSSSP_Decremental_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:49:04.765508+00:00
-- url     : https://prove2.me/theorems/a040cb20-3433-4859-b08a-eb00d91e5f62
-- title:
--   Directed labelled graphs, deletion histories and extended distances
-- statement:
--   A finite directed graph has vertices $\{0,\ldots,n-1\}$ and distinct edge identifiers $\{0,\ldots,k-1\}$. Each identifier has a tail and a head, so parallel edges remain distinct. A walk is a list of active edge identifiers with successive endpoints matching; the empty walk joins a vertex to itself. With nonnegative extended edge weights $w_e$, its weight is the sum along the list, and
--
--   $$d_G(s,v)=\inf\left\{\sum_{e\in P}w_e:P\text{ is an active walk from }s\text{ to }v\right\}\in[0,\infty].$$
--
--   The empty infimum is $\infty$. An original input also supplies a source $s$, positive integer weights in $[1,W]$, a size bound $m\ge\max(n,k)$ and real accuracy $0<\epsilon\le1$. A legal deletion history has no repeated identifier; its complement is the current active set. Arbitrary disconnected initial graphs and edges entering the source are admitted.
--
--   This separates the general directed graph from the paper's normalized optimization graph. **Formalization Note** The complete lattice $\mathbb R_{\ge0}\cup\{\infty\}$ represents unreachable distances directly; no empty real infimum is used.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), pp. 3–4, Theorem 1.1 and Preliminaries; pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- Directed labelled edges; `tail` is the source endpoint. No reachability or simplicity
assumption is built into the general graph. Weights and active sets are separate. -/
structure Digraph (n k : ℕ) where
  tail : Fin k → Fin n
  head : Fin k → Fin n

/-- Walks retain edge identities, including parallel edges and the empty walk. -/
inductive Walk {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k)) :
    Fin n → Fin n → List (Fin k) → Prop
  | nil (v : Fin n) : Walk g active v v []
  | cons {u v : Fin n} {es : List (Fin k)} (e : Fin k)
      (he : e ∈ active) (h : Walk g active (g.head e) v es) :
      Walk g active (g.tail e) v (e :: es)

noncomputable def distance {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ≥0∞) (s v : Fin n) : ℝ≥0∞ :=
  ⨅ (es : List (Fin k)) (_ : Walk g active s v es), (es.map w).sum

def Reachable {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (s v : Fin n) : Prop := ∃ es, Walk g active s v es

/-- Original positive-integer-weight input. Every original edge has its own identifier. -/
structure Input where
  n : ℕ
  k : ℕ
  graph : Digraph n k
  source : Fin n
  weight : Fin k → ℕ
  W : ℕ
  accuracy : ℝ
  size : ℕ

def Input.Valid (i : Input) : Prop :=
  i.n ≤ i.size ∧ i.k ≤ i.size ∧ 1 ≤ i.W ∧ 0 < i.accuracy ∧ i.accuracy ≤ 1 ∧
  ∀ e, 1 ≤ i.weight e ∧ i.weight e ≤ i.W

def live {k : ℕ} (deleted : List (Fin k)) : Finset (Fin k) :=
  Finset.univ \ deleted.toFinset

def Legal {k : ℕ} (deleted : List (Fin k)) : Prop := deleted.Nodup

noncomputable def Input.dist (i : Input) (deleted : List (Fin i.k)) (v : Fin i.n) : ℝ≥0∞ :=
  distance i.graph (live deleted) (fun e => (i.weight e : ℝ≥0∞)) i.source v

end DecrAlmostLinearSSSP.Decremental


