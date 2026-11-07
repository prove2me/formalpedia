-- Prove2me | Definitions.Def_MISInducedMinor_edgeList
-- name    : MISInducedMinor_edgeList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:24.018598+00:00
-- url     : https://prove2.me/theorems/fad6c6ee-8081-475c-8c35-3df4b5bdc582
-- title:
--   The edges of $F$ in a fixed order
-- statement:
--   Let $F$ be a graph on the vertices $\{0,\dots,n-1\}$ (the paper's $v_1,\dots,v_n$). Its **edge list** is the list of pairs $(a,b)$ with $a<b$ and $ab\in E(F)$, in lexicographic order; it contains every edge exactly once, so its length is $m=|E(F)|$.
--
--   Edge number $t$ of this list is the edge $e$ whose two reserved rows $e_0,e_1$ of the construction are the rows $2t$ and $2t+1$.
--
--   **Formalization Note** The paper orders the vertices of $F$ and assigns the rows arbitrarily; this fixes the vertex order of $\{0,\dots,n-1\}$ and the lexicographic row order.
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), §3, p.6

import Mathlib

set_option autoImplicit false

namespace MISInducedMinor

/-- The edges of a graph `F` on `Fin n` in a **canonical order**: the pairs `(a, b)` with `a < b`
and `F.Adj a b`, listed lexicographically. Edge number `t` of this list is the edge `e` whose
reserved rows `e₀, e₁` (arXiv:2609.11285 (sha256 e378b906…), §3, p.6: "We reserve two rows
R′_{e,0}, R′_{e,1} for every e ∈ E(F)") are the rows `2t` and `2t + 1`.

**Formalization Note.** The paper orders the vertices `v₁, …, vₙ` and the rows arbitrarily; here
the vertex order is the order of `Fin n` and the row order is this list's. Every edge appears
exactly once, with its smaller endpoint first, so `m = (edgeList F).length`. -/
def edgeList {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a =>
    (List.finRange n).filterMap fun b => if a < b ∧ F.Adj a b then some (a, b) else none

end MISInducedMinor


