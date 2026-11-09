-- Prove2me | Definitions.Def_CSPSubsample_Instance
-- name    : CSPSubsample_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:13:48.67773+00:00
-- url     : https://prove2.me/theorems/c4f26d73-0531-429a-a088-e60076f840a0
-- title:
--   $k$-CSP instance on $n$ variables with alphabet $[q]$ and predicates $P_w:[q]^k\to[0,1]$
-- statement:
--   A **$k$-constraint satisfaction problem ($k$-CSP) instance** on $n$ variables with alphabet size $q$ is a collection of constraints $P_w$, one for every $k$-tuple $w=(i_1,\dots,i_k)$ of **distinct** variable indices in $[n]=\{1,\dots,n\}$. Write $W$ for the set of these tuples. Each constraint is a bounded predicate
--   $$
--   P_w:[q]^k\to[0,1].
--   $$
--   An **assignment** is a function $\phi\in[q]^n$, and $\phi|_w=(\phi_{i_1},\dots,\phi_{i_k})$ is its restriction to the variables of $w$.
--
--   This is the object of the whole mission: the value, the optimum, the restricted optimum $\mathrm{OPT}(U)$ and the balanced CSP of the structure lemma are all built from it.
--
--   **Formalization Note** Variables are `Fin n`, the alphabet is `Fin q` (paper index $i$ is Lean index $i-1$), and $W$ is the type `Fin k ↪ Fin n` of injective maps. The bounds $0\le P_w(a)\le 1$ are fields of the structure.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Definition 2.1, p.5 (PDF p.7)

import Mathlib

set_option autoImplicit false

namespace CSPSubsample

/-- A **k-CSP instance** on `n` variables with alphabet size `q` (Bernasconi, Castiglioni, Celli,
Farina, Malavolta, *A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity*,
arXiv:2608.00203 (PDF sha256 fd9ae011…), Definition 2.1, p.5 = PDF p.7): one bounded predicate
`P_w : [q]^k → [0,1]` for every k-tuple `w` of distinct variable indices.

**Formalization Note** Variables are `Fin n`, the alphabet is `Fin q` (paper index `i` is Lean
index `i − 1`). The set `W` of k-tuples of distinct variables is `Fin k ↪ Fin n`; `P w a` is
`P_w(a_1, …, a_k)` with `a : Fin k → Fin q`. The fields `nonneg`, `le_one` are "bounded predicate
… [0,1]". -/
structure Instance (n k q : ℕ) where
  /-- The predicate `P_w` of the constraint on the tuple `w`. -/
  P : (Fin k ↪ Fin n) → (Fin k → Fin q) → ℝ
  /-- `0 ≤ P_w(a)`. -/
  nonneg : ∀ w a, 0 ≤ P w a
  /-- `P_w(a) ≤ 1`. -/
  le_one : ∀ w a, P w a ≤ 1

end CSPSubsample


