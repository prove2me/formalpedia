-- Prove2me | Definitions.Def_FreeReplExchange_Exchange
-- name    : FreeReplExchange_Exchange
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:16:49.492848+00:00
-- url     : https://prove2.me/theorems/4cfafa73-59e5-4ae4-aa3b-75afd1658a23
-- title:
--   Exchange proposals, receiving slots $R(p)$, well-formedness (5) and $x[S]$ (6)
-- statement:
--   An **exchange proposal** $p=((i,r),(j,s))$ recommends that agent $i$ give a copy of good $r$ to agent $j$ in return for a copy of good $s$; both keep what they give. Its **receiving slots** are $R(p)=\{(i,s),(j,r)\}$. Given a participating set $P\subseteq A$ and the initial allocation $x^{(0)}$, $p$ is **well formed** if
--   $$i,j\in P,\qquad i<j,\qquad x^{(0)}_{i,r}=x^{(0)}_{j,s}=1,$$
--   where $<$ is the fixed ordering of the agents. Executing a set $S$ of proposals at an allocation $x$ gives
--   $$x[S]_{k,q}=\max\bigl\{x_{k,q},\ \mathbf 1\{\exists p\in S:(k,q)\in R(p)\}\bigr\},$$
--   so $x[\varnothing]=x$ and receiving a good twice changes nothing. A set $S$ has **pairwise disjoint receiving slots** if $R(p)\cap R(q)=\varnothing$ for all distinct $p,q\in S$.
--
--   These are the units a protocol proposes, and the disjointness condition is the matching condition of the exchange graph.
--
--   **Formalization Note** The type `Exchange A m` holds every quadruple $(i,r,j,s)$; well-formedness is a separate predicate.
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), §2.2, pp.13–14 (PDF pp.15–16), eqs. (5), (6)

import Mathlib

namespace FreeReplExchange

/-- An exchange proposal `p = ((i, r), (j, s))` of Yang–Kandasamy, *Pairwise Exchanges of Freely
Replicable Goods with Negative Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…),
§2.2, p.13 (PDF p.15): agent `i` gives a copy of good `r` to agent `j` in return for a copy of
good `s`.

**Formalization Note.** The type contains every quadruple; well-formedness (5), including the
normal form `i < j`, is the separate predicate `WellFormed`. -/
structure Exchange (A : Type*) (m : ℕ) where
  /-- the first agent `i` -/
  i : A
  /-- the good `r` given by `i` -/
  r : Fin m
  /-- the second agent `j` -/
  j : A
  /-- the good `s` given by `j` -/
  s : Fin m
  deriving DecidableEq, Fintype

/-- The two receiving slots `R(p) = {(i, s), (j, r)}` of `p = ((i, r), (j, s))`, p.14. -/
def recv {A : Type*} [DecidableEq A] {m : ℕ} (p : Exchange A m) : Finset (A × Fin m) :=
  {(p.i, p.s), (p.j, p.r)}

/-- Well-formedness, p.14: `p` satisfies (5) (`i, j ∈ P`, `x^(0)_{i,r} = x^(0)_{j,s} = 1`) and
`i < j` in the fixed ordering of the agents. -/
def WellFormed {A : Type*} [LinearOrder A] {m : ℕ} (x0 : A → Fin m → Bool) (P : Finset A)
    (p : Exchange A m) : Prop :=
  p.i ∈ P ∧ p.j ∈ P ∧ p.i < p.j ∧ x0 p.i p.r = true ∧ x0 p.j p.s = true

open Classical in
/-- The allocation `x[S]` (6), p.14, after executing a set `S` of proposals at `x`:
`x[S]_{k,q} = max{x_{k,q}, 1{∃ p ∈ S : (k, q) ∈ R(p)}}`. In particular `x[∅] = x`. -/
noncomputable def exec {A : Type*} [DecidableEq A] {m : ℕ} (x : A → Fin m → Bool)
    (S : Finset (Exchange A m)) : A → Fin m → Bool :=
  fun k q => x k q || decide (∃ p ∈ S, (k, q) ∈ recv p)

/-- Pairwise disjoint receiving slots: `R(p) ∩ R(q) = ∅` for all distinct `p, q ∈ S` (the
condition of (10), p.16, and of Proposition 1 (ii)). Read on exchanges that are edges of an
exchange graph, this says that `S` is a matching: its edges have pairwise disjoint endpoints. -/
def RecvDisjoint {A : Type*} [DecidableEq A] {m : ℕ} (S : Finset (Exchange A m)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (recv p) (recv q)

end FreeReplExchange


