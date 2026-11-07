-- Prove2me | Definitions.Def_MCPoise_IsPathIn
-- name    : MCPoise_IsPathIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:48.309538+00:00
-- url     : https://prove2.me/theorems/14e0ee03-a908-431a-9ff8-d447d80350cb
-- title:
--   Simple paths as vertex lists; path sets, loads and edge stars
-- statement:
--   A **simple path** of a graph $G$ from $a$ to $b$ is a list of distinct vertices, starting at $a$ and ending at $b$, with consecutive vertices adjacent in $G$. The one-vertex list $[a]$ is the length-zero path from $a$ to $a$. The **length** of a path is the number of its edges.
--
--   The module also fixes:
--
--   1. the set of $a$-$b$ simple paths of length at most $d$, the set $P^j_t$ of the linear programs;
--   2. the **load** $\sum_{p \in P : e \in p} f_p$ of a path flow $f$ on an edge $e$;
--   3. the set $\delta(v)$ of edges of $G$ incident to $v$.
--
--   **Formalization Note** The path sets are finite on a finite vertex set, so the sums over them are finite sums.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §2, p.9; Junction-LP, p.10; p.21

import Mathlib

namespace MCPoise

/-- The edges of a vertex list, consecutive vertices in order. The list `[a]` has none. -/
def pEdges {V : Type*} (p : List V) : List (Sym2 V) :=
  List.zipWith (fun a b => s(a, b)) p p.tail

/-- **A simple path of `G` from `a` to `b`, as a vertex list.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §2, p.9: "the set of all r_j-t paths in G"; p.21: "including the length-zero path when t = r_j".

**Formalization Note.** The one-vertex list `[a]` is the length-zero path from `a` to `a`, so a terminal
that coincides with its root has a path. The length of `p` is `(pEdges p).length`. -/
def IsPathIn {V : Type*} (G : SimpleGraph V) (a b : V) (p : List V) : Prop :=
  p.Nodup ∧ p.IsChain G.Adj ∧ p.head? = some a ∧ p.getLast? = some b

/-- The set of `a`–`b` simple paths of `G` with at most `d` edges: `P^j_t` of p.9 and p.15.
On a finite vertex type this set is finite (`Solutions/verification/MCPoise_sanity.lean`), so the `finsum`s
over it below are honest sums. -/
def pathSet {V : Type*} (G : SimpleGraph V) (a b : V) (d : ℕ) : Set (List V) :=
  {p | IsPathIn G a b p ∧ (pEdges p).length ≤ d}

/-- `∑_{p∈P : e∈p} f_p`, the load of the path flow `f` on the edge `e`, as in Junction-LP (p.10). -/
noncomputable def pathLoad {V : Type*} (P : Set (List V)) (f : List V → ℝ) (e : Sym2 V) : ℝ :=
  ∑ᶠ p ∈ {p ∈ P | e ∈ pEdges p}, f p

/-- `δ(v)`: the edges of `G` incident to `v`. -/
noncomputable def delta {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V) :
    Finset (Sym2 V) :=
  open scoped Classical in Finset.univ.filter fun e => e ∈ G.edgeSet ∧ v ∈ e

end MCPoise


