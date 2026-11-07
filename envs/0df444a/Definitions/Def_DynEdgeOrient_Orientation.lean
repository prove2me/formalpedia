-- Prove2me | Definitions.Def_DynEdgeOrient_Orientation
-- name    : DynEdgeOrient_Orientation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:58.292658+00:00
-- url     : https://prove2.me/theorems/ceb7e1e5-655b-4345-9fa7-16eca16fe661
-- title:
--   Orientations, out-degrees $d^+(v)$, directed counts $\vec E(S,T)$ and edge flips
-- statement:
--   An **orientation** assigns each edge $e$ with endpoints $(u,v)$ a direction, $u\to v$ or $v\to u$; the first endpoint of the arrow is the **tail**, the second the **head**. For a state $F$ and an orientation $\sigma$:
--
--   1. the **out-degree** $d^+(v)$ is the number of edges of $F$ with tail $v$, parallel edges counted with multiplicity; a **$k$-orientation** is one with $d^+(v)\le k$ for every $v$;
--   2. the out-degree of $v$ **inside $G[S]$** counts only the edges of $E(S)$;
--   3. $|\vec E(S,T)|$ is the number of edges of $F$ with tail in $S$ and head in $T$.
--
--   For two consecutive states $F,F'$ with orientations $\sigma,\sigma'$, the number of **edge flips** is
--
--   $$
--   \#\{e\in F\cap F' : \sigma(e)\neq\sigma'(e)\},
--   $$
--
--   the edges present at both times whose direction changes. A newly inserted edge may be oriented freely, and a deleted edge no longer counts. The same count restricted to $E(S)$ at both times gives the flips inside $G[S]$.
--
--   These are the quantities in which Theorem 1.2 is stated: a sequence of $k$-orientations of the dynamic graph and its total number of flips.
--
--   **Formalization Note** An orientation is a Boolean function on all labels; `true` orients an edge from its first to its second endpoint. Only its values on the current state matter. A label that is deleted and inserted again is a new insertion with a free direction.
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), §1, p.1 (k-orientations) and §1.5, p.4 (d⁺(v), E⃗(S,T))

import Mathlib
import Definitions.Def_DynEdgeOrient_Multigraph

namespace DynEdgeOrient

/-!
# Orientations, out-degrees and flips

S. Hiken, N. Wein, *Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n
Barrier*, STOC 2027 submission (manuscript sha256 626b4eee…), §1, p.1 (k-orientations) and §1.5,
p.4 (`d⁺(v)`, `E⃗(S, T)`).

**Formalization Note.**
* An orientation is `σ : E → Bool`: `σ e = true` orients `e` from `(ends e).1` to `(ends e).2`,
  `false` the other way. Only the values of `σ` on the edges of the current state matter.
* `outDeg ends F σ v` is `d⁺(v)` in the state `F` oriented by `σ`, parallel edges counted with
  multiplicity. A `k`-orientation of `F` is a `σ` with `outDeg ends F σ v ≤ k` for every `v`.
* `outDegIn ends F S σ v` is the out-degree of `v` inside `G[S]` (only edges of `E(S)` count).
* `dirCount ends F σ S T` is `|E⃗(S, T)|`: edges of `F` with tail in `S` and head in `T`.
* `flips F F' σ σ'` counts the edges present in both consecutive states `F`, `F'` whose direction
  differs. An edge inserted at this step is not in `F` and its direction is free; a deleted edge
  is not in `F'`. A label deleted and later re-inserted is a new insertion.
* `flipsIn ends F F' S σ σ'` is the same count for the induced subgraphs `F[S]`, `F'[S]`.
-/

variable {V E : Type*} [DecidableEq V]

/-- The tail of `e` under the orientation `σ`. -/
def tail (ends : E → V × V) (σ : E → Bool) (e : E) : V :=
  if σ e then (ends e).1 else (ends e).2

/-- The head of `e` under the orientation `σ`. -/
def head (ends : E → V × V) (σ : E → Bool) (e : E) : V :=
  if σ e then (ends e).2 else (ends e).1

/-- `d⁺(v)`: the number of edges of `F` whose tail under `σ` is `v` (Hiken–Wein, §1.5, p.4). -/
def outDeg (ends : E → V × V) (F : Finset E) (σ : E → Bool) (v : V) : ℕ :=
  (F.filter (fun e => tail ends σ e = v)).card

/-- The out-degree of `v` in the induced subgraph `G[S]` of the state `F`. -/
def outDegIn (ends : E → V × V) (F : Finset E) (S : Finset V) (σ : E → Bool) (v : V) : ℕ :=
  outDeg ends (edgesIn ends F S) σ v

/-- `|E⃗(S, T)|`: the edges of `F` with tail in `S` and head in `T` under `σ` (Hiken–Wein, §1.5,
p.4). -/
def dirCount (ends : E → V × V) (F : Finset E) (σ : E → Bool) (S T : Finset V) : ℕ :=
  (F.filter (fun e => tail ends σ e ∈ S ∧ head ends σ e ∈ T)).card

variable [DecidableEq E]

/-- The number of edge flips between the orientation `σ` of `F` and the orientation `σ'` of the
next state `F'`: edges present in both states whose direction changes. -/
def flips (F F' : Finset E) (σ σ' : E → Bool) : ℕ :=
  ((F ∩ F').filter (fun e => σ e ≠ σ' e)).card

/-- Flips counted inside the induced subgraphs `F[S]` and `F'[S]`. -/
def flipsIn (ends : E → V × V) (F F' : Finset E) (S : Finset V) (σ σ' : E → Bool) : ℕ :=
  flips (edgesIn ends F S) (edgesIn ends F' S) σ σ'

end DynEdgeOrient


