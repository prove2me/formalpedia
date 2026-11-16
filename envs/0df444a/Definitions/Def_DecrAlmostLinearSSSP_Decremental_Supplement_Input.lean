-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_Input
-- name    : DecrAlmostLinearSSSP_Decremental_Supplement_Input
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:13:57.247015+00:00
-- url     : https://prove2.me/theorems/e82472c7-51eb-47c1-8380-77512b3fb21b
-- title:
--   Incremental directed graph inputs and legal insertion prefixes
-- statement:
--   Let $V=\{0,\ldots,n-1\}$ be a finite nonempty vertex set, let $s\in V$ be the source, and give each original directed edge its own identifier in $\{0,\ldots,k-1\}$. Its tail, head and real weight $w(e)$ are fixed. The initial graph is a duplicate-free list $E_0$; a legal insertion list $e_1,\ldots,e_t$ has no repeated identifier and is disjoint from $E_0$. At that prefix the active graph and its distance are
--
--   $$
--   E_t=E_0\cup\{e_1,\ldots,e_t\},\qquad d_t(v)=\inf_{P:s\leadsto v,\ P\subseteq E_t}\sum_{e\in P}w(e).
--   $$
--
--   Validity means $n,k\le m$, $W\ge1$, $0<\epsilon\le1$, and $1\le w(e)\le W$ for every identifier. A separate integrality predicate requires integer edge weights only when used; the numerical upper bound $W$ remains real. Source membership supplies nonemptiness. Parallel edges, loops, edges entering the source, arbitrary initial reachability and empty insertion lists remain admissible.
--
--   These incremental wrappers reuse the published general directed graph, walk, extended distance and reachability definitions. They do not use any deletion-specific legality or live-edge convention. Extended nonnegative distances give infinity exactly when no walk exists for valid finite weights. The full future graph is specification data; the execution protocol exposes only initially active edges and then the current inserted edge.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), pp.1, 3–4, 18, 31, incremental graph convention and Lemmas 4.1, 5.1

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Graph

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.Supplement

/-- Specification of an incremental instance. The graph includes potential future identifiers,
but the initialization tape below exposes only `initial`. Parallel edges and loops are allowed.
Real weights are needed by the black-box Lemma 5.1. -/
structure Instance where
  n : ℕ
  k : ℕ
  graph : Digraph n k
  source : Fin n
  weight : Fin k → ℝ
  initial : List (Fin k)
  size : ℕ
  W : ℝ
  accuracy : ℝ

def Instance.Valid (i : Instance) : Prop :=
  i.n ≤ i.size ∧ i.k ≤ i.size ∧ i.initial.Nodup ∧ 1 ≤ i.W ∧
  0 < i.accuracy ∧ i.accuracy ≤ 1 ∧ ∀ e, 1 ≤ i.weight e ∧ i.weight e ≤ i.W

/-- Integrality concerns edge lengths only; the numerical upper bound W may be real. -/
def Instance.Integral (i : Instance) : Prop :=
  ∀ e, ∃ w : ℕ, i.weight e = (w : ℝ)

def Instance.Legal (i : Instance) (es : List (Fin i.k)) : Prop :=
  (i.initial ++ es).Nodup

def Instance.active (i : Instance) (es : List (Fin i.k)) : Finset (Fin i.k) :=
  (i.initial ++ es).toFinset

noncomputable def Instance.dist (i : Instance) (es : List (Fin i.k)) (v : Fin i.n) : ℝ≥0∞ :=
  distance i.graph (i.active es) (fun e => ENNReal.ofReal (i.weight e)) i.source v

def Instance.reachable (i : Instance) (es : List (Fin i.k)) (v : Fin i.n) : Prop :=
  Reachable i.graph (i.active es) i.source v

end DecrAlmostLinearSSSP.Decremental.Supplement


