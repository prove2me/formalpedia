-- Prove2me | Definitions.Def_AlgebraicFPT_HittingSet_HittingSets
-- name    : AlgebraicFPT_HittingSet_HittingSets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:56:07.227289+00:00
-- url     : https://prove2.me/theorems/59f8c600-dfdc-4c0e-8385-5e7a0891ebbe
-- title:
--   Finite hypergraphs and inclusion-minimal hitting sets
-- statement:
--   Let $V=\{0,\ldots,n-1\}$, where $n\ge0$, and let $E$ be a finite family of subsets of $V$. A subset $C\subseteq V$ is a hitting set if
--   $$\forall e\in E,\quad C\cap e\ne\varnothing.$$
--   It is inclusion-minimal if it is a hitting set and every hitting subset $D\subseteq C$ equals $C$. Write $\mathcal H_{\le k}(E)$ and $\mathcal H_{=k}(E)$ for all such minimal hitting sets of size at most $k$ and exactly $k$, respectively.
--
--   These predicates record feasibility and inclusion-minimality separately from the geometric encoding. Hypergraphs use Mathlib finite families of finite sets directly; no rank, feasibility, or counting property is built into them. The empty vertex set, empty family, and empty hyperedge are permitted.
-- source:
--   Liming Cai, Sixiang Zhang, STOC 2027 submission #1035 (October 2026), pp.3–4, §2.1 and §3

import Mathlib

set_option autoImplicit false

namespace AlgebraicFPT.HittingSet

/-- A hypergraph is represented directly by a finite family of finite vertex sets.
This predicate is the hitting condition of Section 3, p.4. No feasibility is assumed. -/
def IsHitting {n : ℕ} (E : Finset (Finset (Fin n))) (C : Finset (Fin n)) : Prop :=
  ∀ e ∈ E, (C ∩ e).Nonempty

/-- Inclusion-minimal, rather than minimum-cardinality, hitting sets (§2.1, p.3). -/
def IsMinimalHitting {n : ℕ} (E : Finset (Finset (Fin n))) (C : Finset (Fin n)) : Prop :=
  IsHitting E C ∧ ∀ D ⊆ C, IsHitting E D → D = C

/-- The entire collection of minimal hitting sets with size at most k. -/
def smallHittingSets {n : ℕ} (E : Finset (Finset (Fin n))) (k : ℕ) :
    Set (Finset (Fin n)) :=
  {C | IsMinimalHitting E C ∧ C.card ≤ k}

/-- The entire collection of minimal hitting sets with size exactly k. -/
def exactHittingSets {n : ℕ} (E : Finset (Finset (Fin n))) (k : ℕ) :
    Set (Finset (Fin n)) :=
  {C | IsMinimalHitting E C ∧ C.card = k}

end AlgebraicFPT.HittingSet


