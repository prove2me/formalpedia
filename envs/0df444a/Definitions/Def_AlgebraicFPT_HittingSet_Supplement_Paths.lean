-- Prove2me | Definitions.Def_AlgebraicFPT_HittingSet_Supplement_Paths
-- name    : AlgebraicFPT_HittingSet_Supplement_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:41:04.457449+00:00
-- url     : https://prove2.me/theorems/d0f72d7f-a928-4668-a736-17bcf42d2065
-- title:
--   Ordered vertex paths, avoidance queries, and the exact representative bound
-- statement:
--   Let $G$ be a finite simple undirected graph on $n$ vertices. An ordered simple $h$-vertex path from $s$ to $v$ is a list of exactly $h$ distinct vertices, with first vertex $s$, last vertex $v$, and adjacent consecutive vertices. Write $V(P)$ for its vertex set and $\mathcal P_{h,s,v}$ for the entire finite family of these ordered lists. Different orders with the same support remain distinct witnesses.
--
--   For a finite family $A$ of ordered lists and a vertex set $Q$, an avoidance query succeeds when some $P\in A$ satisfies $V(P)\cap Q=\varnothing$. A subfamily $R\subseteq A$ is $q$-representative when this query has the same answer in $R$ and $A$ for every $|Q|\le q$. Define the exact bound
--
--   $$B(p,q)=\sum_{j=0}^{q}p^j.$$
--
--   These objects describe the path-prefix information preserved by both companion theorems. The graph itself uses the existing Mathlib simple-graph type; no paper-specific replacement graph is introduced.
--
--   **Formalization Note** Vertices are relabelled by $\operatorname{Fin}(n)$, with $n=0$ allowed. Lists count vertices rather than edges; the one-vertex path is $(s)$. The finite family is enumerated using every map $\operatorname{Fin}(h)\to\operatorname{Fin}(n)$ and filtered by the path conditions. The sum includes $j=0$, so $B(p,0)=1$ and $B(1,q)=q+1$. No path existence, connectedness, or distinct-endpoint condition is assumed.
-- source:
--   Liming Cai, Sixiang Zhang, STOC 2027 submission #1035 (October 2026), pp.10–12, Section 5; p.20, Appendix D

import Mathlib

set_option autoImplicit false

namespace AlgebraicFPT.HittingSet.Supplement

/-! Section 5, pp.10–12: graphs are Mathlib simple undirected graphs on `Fin n`.
An h-vertex path is an ordered list of length h, not a walk of edge-length h.
No connectedness, distinct-endpoint, or k ≤ n assumption is imposed. -/

/-- The vertices used by an ordered witness. -/
def support {n : ℕ} (P : List (Fin n)) : Finset (Fin n) := P.toFinset

/-- The full path predicate, including both endpoints and every adjacency. -/
def IsPath {n : ℕ} (G : SimpleGraph (Fin n)) (h : ℕ) (s v : Fin n)
    (P : List (Fin n)) : Prop :=
  P.length = h ∧ P.Nodup ∧ P.head? = some s ∧ P.getLast? = some v ∧ P.IsChain G.Adj

/-- Every ordered h-vertex simple path from s to v, with all orders retained. -/
def pathFamily {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ℕ) (s v : Fin n) : Finset (List (Fin n)) :=
  ((Finset.univ : Finset (Fin h → Fin n)).image List.ofFn).filter
    (fun P => P.Nodup ∧ P.head? = some s ∧ P.getLast? = some v ∧ P.IsChain G.Adj)

/-- A query is successful precisely when some ordered witness avoids all its vertices. -/
def AvoidsQuery {n : ℕ} (A : Finset (List (Fin n))) (Q : Finset (Fin n)) : Prop :=
  ∃ P ∈ A, Disjoint (support P) Q

/-- Appendix D, p.20: inclusion together with all queries of size at most q. -/
def IsRepresentative {n : ℕ} (q : ℕ) (A R : Finset (List (Fin n))) : Prop :=
  R ⊆ A ∧ ∀ Q : Finset (Fin n), Q.card ≤ q → (AvoidsQuery R Q ↔ AvoidsQuery A Q)

/-- The inclusive sum in Theorems 5.1 and 5.2, including its j = 0 term. -/
def representativeBound (p q : ℕ) : ℕ := ∑ j ∈ Finset.range (q + 1), p ^ j

end AlgebraicFPT.HittingSet.Supplement


