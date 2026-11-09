-- Prove2me | Definitions.Def_HypRecov_crisp
-- name    : HypRecov_crisp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:34.245484+00:00
-- url     : https://prove2.me/theorems/fbc4a091-5c1c-4d2c-9c6c-dfb41256e68f
-- title:
--   Cuts $\delta_H(S)$, $\mathrm{cut}_H(S)$ and the $k$-crisp edges $\mathcal B_k(H)$
-- statement:
--   Let $H=(V,E)$ be a simple hypergraph on the vertex set $V=\{0,\dots,n-1\}$, given as a finite set of vertex sets. For $S\subseteq V$ the **boundary** of $S$ is the set of edges meeting both $S$ and its complement,
--   $$\delta_H(S)=\{e\in E:\ e\cap S\neq\emptyset,\ e\setminus S\neq\emptyset\},\qquad \mathrm{cut}_H(S)=|\delta_H(S)|.$$
--   For $k\ge 0$ the family of **$k$-crisp edges** is
--   $$\mathcal B_k(H)=\bigcup_{S\subseteq V:\ \mathrm{cut}_H(S)<k}\delta_H(S),$$
--   the edges crossing some cut of value below $k$ (eq. (1) of the paper). These are the edges that can become bridges after at most $k-2$ other edge failures, and the family the mission's sketch must recover.
--
--   **Formalization Note** Vertices are `Fin n` and a hypergraph is a `Finset` of vertex sets, so it has no repeated edge. The union ranges over all $2^n$ sets $S$, including $\emptyset$ and $V$, whose boundaries are empty.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), §1.1, p.1 (PDF p.2), eq. (1)

import Mathlib

namespace HypRecov

/-- **The boundary `δ_H(S)` of a vertex set.** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous
Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), §1.1, p.1 (PDF p.2):
"For S ⊆ V, write δ_H(S) = {e ∈ E : e ∩ S ≠ ∅, e ∖ S ≠ ∅}".

**Formalization Note.** The vertex set is `Fin n` and a hypergraph is a `Finset` of vertex sets, so
it is simple (no repeated edge). -/
def bdry {n : ℕ} (E : Finset (Finset (Fin n))) (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  E.filter (fun e => (e ∩ S).Nonempty ∧ (e \ S).Nonempty)

/-- The cut value `cut_H(S) = |δ_H(S)|`, ibid., §1.1, p.1. -/
def cut {n : ℕ} (E : Finset (Finset (Fin n))) (S : Finset (Fin n)) : ℕ :=
  (bdry E S).card

/-- **The `k`-crisp edges `ℬ_k(H)`.** Ibid., §1.1, p.1, eq. (1):
"ℬ_k(H) = ⋃_{S : cut_H(S) < k} δ_H(S)". These are the edges crossing some cut of value below `k`.

**Formalization Note.** The union ranges over all `2^n` vertex sets `S`, including `∅` and `V`,
whose boundaries are empty. -/
def crisp {n : ℕ} (E : Finset (Finset (Fin n))) (k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ.filter (fun S => cut E S < k)).biUnion (bdry E)

end HypRecov


