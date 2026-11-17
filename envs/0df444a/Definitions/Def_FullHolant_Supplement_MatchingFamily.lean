-- Prove2me | Definitions.Def_FullHolant_Supplement_MatchingFamily
-- name    : FullHolant_Supplement_MatchingFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:58:34.498676+00:00
-- url     : https://prove2.me/theorems/d32f86b9-5fdc-469a-beb6-d05d738f7b5c
-- title:
--   Perfect matchings and the splicing $\kappa_r(P_e)$
-- statement:
--   Let $V$ be a finite set.
--
--   1. A **perfect matching** of $W\subseteq V$ is a set of two-element subsets of $W$ such that every element of $W$ lies in exactly one of them.
--   2. For a perfect matching $P$ of $V\setminus e$ and a pair $r=\{u,v\}$ disjoint from $e$, the **splicing** $\kappa_r(P)$ is defined as follows. If $r\in P$, delete that edge. Otherwise let $u',v'$ be the mates of $u,v$, remove $uu'$ and $vv'$, add $u'v'$, and retain the untouched edges.
--
--   At arity eight, $\kappa_r(P_e)$ is a two-edge matching on $V\setminus(e\cup r)$; the compatibility $\kappa_r(P_e)=\kappa_e(P_r)$ is the constraint satisfied by the matching families of the height-four analysis.
--
--   **Formalization Note** Pairs are unordered pairs `Sym2 V`. The retained edges are those of $P$ meeting neither $u$ nor $v$; the added edge is $\{a,b\}$ with $\{u,a\},\{v,b\}\in P$ and $a\neq v$, a condition that fails exactly when $uv\in P$.
-- source:
--   Liu–Meng–Wang, A Full Complexity Dichotomy for Complex-Valued Boolean Holant Problems, arXiv:2610.00081 (held version, sha256 d67958c6…), §F.2.2, p.F-6 (PDF p.24); App. F.A.2.3, p.F-77 (PDF p.95)

import Mathlib

set_option autoImplicit false

namespace FullHolant.Supplement

/-- The vertices of an unordered pair `e`, as a finset. -/
def pairSet {V : Type*} [Fintype V] [DecidableEq V] (e : Sym2 V) : Finset V :=
  open Classical in Finset.univ.filter fun v => v ∈ e

/-- `M` is a **perfect matching of `W`**: a set of non-loop unordered pairs inside `W` such that
every vertex of `W` lies in exactly one of them. Liu–Meng–Wang, *A Full Complexity Dichotomy for
Complex-Valued Boolean Holant Problems*, arXiv:2610.00081 (held version, sha256 d67958c6…), §F.2.2,
p.F-6 (PDF p.24): "A perfect matching of a finite set V is a partition into pairs." -/
def IsPerfectMatchingOn {V : Type*} (M : Finset (Sym2 V)) (W : Set V) : Prop :=
  (∀ z ∈ M, ¬ z.IsDiag ∧ ∀ v ∈ z, v ∈ W) ∧ ∀ v ∈ W, ∃! z, z ∈ M ∧ v ∈ z

/-- **The splicing `κ_r(P)`** of a matching `P` of `V ∖ e` at a pair `r = {u, v}` disjoint from
`e`: if `r ∈ P`, delete that edge; otherwise, with `u′, v′` the mates of `u, v`, remove `uu′` and
`vv′`, add `u′v′`, and retain the untouched edges. Liu–Meng–Wang, arXiv:2610.00081, App. F.A.2.3,
p.F-77 (PDF p.95).

**Formalization Note.** The edges of `P` meeting neither `u` nor `v` are kept; the added edge is
`{a, b}` with `{u, a}, {v, b} ∈ P` and `a ≠ v`, which is empty exactly when `uv ∈ P`. -/
noncomputable def kappa {V : Type*} [Fintype V] (P : Finset (Sym2 V)) (r : Sym2 V) :
    Finset (Sym2 V) :=
  open Classical in
  P.filter (fun z => ∀ w ∈ r, w ∉ z) ∪
    Finset.univ.filter (fun z => ∃ u v a b : V, r = s(u, v) ∧ z = s(a, b) ∧ s(u, a) ∈ P ∧
      s(v, b) ∈ P ∧ a ≠ v)

end FullHolant.Supplement


