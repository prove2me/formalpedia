-- Prove2me | Definitions.Def_RoslingAssembly_SeriesEquiv_Supplement_Aggregation
-- name    : RoslingAssembly_SeriesEquiv_Supplement_Aggregation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:17:50.506895+00:00
-- url     : https://prove2.me/theorems/7460b820-42b1-4e66-9b25-383393dee714
-- title:
--   Finite aggregation states, simultaneous elimination and relabeling
-- statement:
--   An aggregation state records the current active original labels $C$, their successor map $s$, lead times $l$, holding coefficients $h$, and the ultimate representative of every original item. Initially $C=\{1,\ldots,N\}$ and all representatives are identities. An eligible pair $(i,n)$ satisfies $h_i\le0$, $h_k>0$ for $k\in P(i)$, and $n\in P(i)$ has minimum lead time. One simultaneous step removes $i$ and sets
--   $$
--    h'_n=h_n\alpha^{-l_i}+h_i,\quad l'_n=l_n+l_i,\quad s'(n)=s(i),
--   $$
--   $$
--    h'_k=h_k\alpha^{l_n},\quad l'_k=l_k-l_n,\quad s'(k)=n
--    \quad(k\in P(i)\setminus\{n\}).
--   $$
--   All other active data are unchanged. Every representative currently targeting $i$ is redirected to $n$. Thus the new predecessor set of $n$ is $(P(i)\setminus\{n\})\cup P(n)$. Every right-hand side uses pre-step data. The eliminated set is the complement of $C$ among the original items. Reachability means finitely many such steps; a terminal state has no eligible pair.
--
--   The reduced model uses a bijective relabeling from $1,\ldots,|C|$ to $C$ and the corresponding inverse successor labels. Its penalty coefficient $p+H_1$ remains unchanged. No Assumption, termination or optimality conclusion is part of the step definition.
--
--   **Formalization Note** Lead subtraction is nonnegative by the shortest-lead choice. A coordinate relabeling is necessary for arbitrary ties: if siblings 2 and 3 have equal leads and item 1 is eliminated into 3, item 2 acquires successor 3. The theorem supplies valid source indexing of the reduced tree; in the zero-step case it preserves the original indexing.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4):565–579, 1989, DOI 10.1287/opre.37.4.565, pp. 572–573, Theorem 3, aggregation procedure

import Definitions.Def_RoslingAssembly_SeriesEquiv_Supplement_Criterion

namespace RoslingAssembly.SeriesEquiv.Supplement

/-- Current data on original labels. A representative is updated transitively
whenever its current target is eliminated. No optimality or termination is
built into a state or into the step relation. -/
structure AggregationState where
  active : Finset ℕ
  succ : ℕ → ℕ
  lead : ℕ → ℕ
  h : ℕ → ℝ
  representative : ℕ → ℕ

namespace AggregationState

def predecessors (A : AggregationState) (i : ℕ) : Finset ℕ :=
  A.active.filter (fun k => A.succ k = i)

def Eligible (A : AggregationState) (i n : ℕ) : Prop :=
  i ∈ A.active ∧ A.h i ≤ 0 ∧
    (∀ k ∈ A.predecessors i, 0 < A.h k) ∧
    n ∈ A.predecessors i ∧ ∀ k ∈ A.predecessors i, A.lead n ≤ A.lead k

/-- Simultaneous assignments, always using the PRE-STEP l_i and l_n. -/
noncomputable def eliminate (A : AggregationState) (α : ℝ) (i n : ℕ) : AggregationState where
  active := A.active.erase i
  succ := fun k => if k = n then A.succ i
    else if k ∈ A.predecessors i then n else A.succ k
  lead := fun k => if k = n then A.lead n + A.lead i
    else if k ∈ A.predecessors i then A.lead k - A.lead n else A.lead k
  h := fun k => if k = n then A.h n * (α ^ A.lead i)⁻¹ + A.h i
    else if k ∈ A.predecessors i then A.h k * α ^ A.lead n else A.h k
  representative := fun j => if A.representative j = i then n else A.representative j

/-- The stopping rule only, with no Assumption packaged into it. -/
def Terminal (A : AggregationState) : Prop := ¬ ∃ i n, A.Eligible i n

/-- A coordinate change is a bijection, not an assumption that the reduced
system already satisfies GA or optimality. Tied total lead times may need
reordering after reattachment; no particular shortest-lead tie is excluded. -/
def Relabeling (A : AggregationState) (e : ℕ → ℕ) : Prop :=
  Set.BijOn e (↑(Finset.Icc 1 A.active.card) : Set ℕ) (↑A.active : Set ℕ)

/-- Inverse of a relabeling on active labels; its unused default is zero. -/
noncomputable def rank (A : AggregationState) (e : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc 1 A.active.card, if e r = j then r else 0

def orderedLabels (A : AggregationState) (e : ℕ → ℕ) : List ℕ :=
  (List.range A.active.card).map (fun r => e (r + 1))

/-- Reduced Model on 1,...,|C|. Its ValidTree (including sorted total
lead times) is asserted by Theorem 3, not built into the procedure. -/
noncomputable def reduced (A : AggregationState) (S : Model) (e : ℕ → ℕ) : Model where
  N := A.active.card
  succ := fun r => if A.succ (e r) = 0 then 0 else A.rank e (A.succ (e r))
  lead := fun r => A.lead (e r)
  h := fun r => A.h (e r)
  p := S.p
  H1 := S.H1
  α := S.α
  ν := S.ν

end AggregationState

/-- Start with the published original data and identity representatives. -/
def initialAggregation (S : Model) : AggregationState where
  active := Finset.Icc 1 S.N
  succ := S.succ
  lead := S.lead
  h := S.h
  representative := id

def AggregationStep (S : Model) (A B : AggregationState) : Prop :=
  ∃ i n, A.Eligible i n ∧ B = A.eliminate S.α i n

def Reachable (S : Model) (A : AggregationState) : Prop :=
  Relation.ReflTransGen (AggregationStep S) (initialAggregation S) A

end RoslingAssembly.SeriesEquiv.Supplement


