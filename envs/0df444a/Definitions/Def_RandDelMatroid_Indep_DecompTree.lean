-- Prove2me | Definitions.Def_RandDelMatroid_Indep_DecompTree
-- name    : RandDelMatroid_Indep_DecompTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T18:29:11.00377+00:00
-- url     : https://prove2.me/theorems/93fdced0-7ec3-4086-b770-65a0b82a1563
-- title:
--   Unordered decomposition trees, clean trees, completions and expansions (Definitions 11, 12, §4.1)
-- statement:
--   Let $M$ be a regular matroid. An **unordered decomposition tree** of $M$ (Definition 11) is a finite tree $T$ with a nonempty regular matroid $M_u=(E_u,\mathcal I_u)$ at every node $u$ such that
--
--   1. for every edge $e=\{u,v\}$ the **boundary set** $S_e=E_u\cap E_v$ has size $0$, $1$ or $3$ and $M_u\triangle M_v$ is a 1-, 2- or 3-sum respectively; the ground sets of nonadjacent nodes are disjoint;
--   2. at every node the boundary sets of its incident edges are pairwise disjoint;
--   3. for every nonempty connected subtree $Q$ the sums along its edges produce a matroid $M_Q$ on $E_Q=\triangle_{v\in Q}E_v$;
--   4. $M_T$ is (identified with) $M$; in particular $E=\triangle_{u}E_u$.
--
--   Following p. 13, $M_Q$ is characterised by its cycles: they are exactly the sets $\triangle_{v\in Q}C_v$ with $C_v$ a cycle of $M_v$ and $C_u\cap S_e=C_v\cap S_e$ on every edge $e=\{u,v\}$ of $Q$.
--
--   The tree is **clean** (Definition 12) if every node matroid is graphic, cographic or isomorphic to $R_{10}$, and every cographic, non-graphic node $v$ has a graph $G_v$ with $M_v=M^*(G_v)$ in which, for every tree edge $e$ at $v$ with $|S_e|=3$, some vertex of degree three is incident to all edges of $S_e$.
--
--   **Completions and expansions (§4.1).** For a node $u$, removing $u$ splits $T$ into the components attached to $u$. If $Q$ is attached to $u$ with boundary set $S$, a **completion** of $s\in S$ in $Q$ is a set $P\subseteq E_Q\setminus S$ such that $P\cup\{s\}$ is a circuit of $M_Q$. For selected boundary sets $S_1,\dots,S_k$ with chosen completions $P_{Q_i,s}$, the **expansion** of $D$ is
--
--   $$D^+=\Big(D\setminus \bigcup_{i=1}^k S_i\Big)\cup\bigcup_{i\in[k]}\bigcup_{s\in D\cap S_i}P_{Q_i,s}.$$
--
--   **Formalization Note** Nodes form a `Fintype ι`; $T$ is a `SimpleGraph ι` with `T.IsTree`; node matroids `Mn : ι → Matroid β` share the element type of `M`, and property 4 is the equation `M = M_T` (the paper identifies $M_T$ with $M$). $\triangle_{v\in Q}X_v$ is `bigSymmDiff`: the elements lying in an odd number of the sets. `subtreeMatroid T Mn Q` is the unique matroid with the cycle characterisation when it exists (property 3 guarantees it for connected $Q$; the fallback `emptyOn` is never reached there). In the clean condition the graph $G_v$ is existentially chosen (one graph for all boundaries at $v$). The component of $T-u$ through the neighbour $v$ is `attachedComp T u v`, the nodes $w$ with $d(u,w)=d(v,w)+1$. `expansion D B P` takes $B=\bigcup_i S_i$ and the completion `P s` indexed by the boundary element $s$ (boundary sets at a node are disjoint, so $s$ determines $i$). This file duplicates, in this paper's conventions, objects that the platform definitions `RegMatroidXC_Main_Sums` model differently (3-sum-only trees, TU-based regularity).
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), pp. 12–13, Definition 11; pp. 15–16, Definition 12; p. 18, §4.1

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Regular
import Definitions.Def_RandDelMatroid_Indep_Sums
import Definitions.Def_RandDelMatroid_Indep_Graphic
import Definitions.Def_RandDelMatroid_Indep_R10

set_option autoImplicit false

namespace RandDelMatroid.Indep

variable {β ι : Type}

/-- The symmetric difference `△_{i ∈ Q} X_i` of a finite family of sets: the elements lying in an
odd number of the sets `X_i`, `i ∈ Q`. -/
def bigSymmDiff (Q : Finset ι) (X : ι → Set β) : Set β :=
  {x | Odd {i | i ∈ Q ∧ x ∈ X i}.ncard}

/-- The boundary set `S_e = E_u ∩ E_v` of a tree edge `e = {u, v}` (Definition 11.1). -/
def edgeBoundary (Mn : ι → Matroid β) (u v : ι) : Set β :=
  (Mn u).E ∩ (Mn v).E

/-- The ground set `E_Q = △_{v ∈ Q} E_v` of a set `Q` of tree nodes (Definition 11.3). -/
def groundOf (Mn : ι → Matroid β) (Q : Finset ι) : Set β :=
  bigSymmDiff Q (fun v => (Mn v).E)

/-- `Q` is a nonempty connected subtree of `T` (it induces a connected subgraph). -/
def IsConnectedSubtree (T : SimpleGraph ι) (Q : Finset ι) : Prop :=
  (T.induce (Q : Set ι)).Connected

/-- p. 13: `N` is the matroid `M_Q` obtained by performing the sums along the edges of the subtree
`Q` (in any order): its ground set is `E_Q`, and its cycles are exactly the sets `△_{v ∈ Q} C_v`
where each `C_v` is a cycle of `M_v` and `C_u ∩ S_e = C_v ∩ S_e` for every edge `e = {u, v}` of `Q`.
(A matroid is determined by its cycles, so at most one `N` qualifies.) -/
def IsSubtreeMatroid (T : SimpleGraph ι) (Mn : ι → Matroid β) (Q : Finset ι) (N : Matroid β) :
    Prop :=
  N.E = groundOf Mn Q ∧
    ∀ C : Set β, IsCycle N C ↔
      ∃ X : ι → Set β, (∀ v ∈ Q, IsCycle (Mn v) (X v)) ∧
        (∀ u ∈ Q, ∀ v ∈ Q, T.Adj u v → X u ∩ edgeBoundary Mn u v = X v ∩ edgeBoundary Mn u v) ∧
        C = bigSymmDiff Q X

open Classical in
/-- The matroid `M_Q` of a subtree `Q` (Definition 11.3). In an unordered decomposition tree it
exists for every nonempty connected subtree (property 3); the fallback `emptyOn β` is never used
there. -/
noncomputable def subtreeMatroid (T : SimpleGraph ι) (Mn : ι → Matroid β) (Q : Finset ι) :
    Matroid β :=
  if h : ∃ N, IsSubtreeMatroid T Mn Q N then h.choose else Matroid.emptyOn β

/-- Definition 11 (p. 12). `(T, (M_u)_u)` is an unordered decomposition tree of the regular
matroid `M`. The node matroids live on the same element type as `M`, and `M` is identified with
the assembled matroid `M_T` (property 4: `M = M_T`, so `E = △_u E_u`). -/
def IsUnorderedDecompTree [Fintype ι] (M : Matroid β) (T : SimpleGraph ι) (Mn : ι → Matroid β) :
    Prop :=
  IsRegular M ∧ T.IsTree ∧
    -- each node carries a nonempty (finite) regular matroid
    (∀ u, IsRegular (Mn u) ∧ (Mn u).E.Nonempty ∧ (Mn u).E.Finite) ∧
    -- 1. each tree edge is a 1-, 2- or 3-sum (|S_e| = 0, 1, 3 respectively) ...
    (∀ u v, T.Adj u v → IsSumPair (Mn u) (Mn v)) ∧
    -- ... and the ground sets of nonadjacent nodes are disjoint
    (∀ u v, u ≠ v → ¬ T.Adj u v → Disjoint (Mn u).E (Mn v).E) ∧
    -- 2. the boundary sets of the edges at a node are pairwise disjoint
    (∀ u v w, T.Adj u v → T.Adj u w → v ≠ w →
      Disjoint (edgeBoundary Mn u v) (edgeBoundary Mn u w)) ∧
    -- 3. every nonempty connected subtree has its matroid `M_Q` on `E_Q`
    (∀ Q : Finset ι, IsConnectedSubtree T Q → ∃ N, IsSubtreeMatroid T Mn Q N) ∧
    -- 4. `M_T = M`
    IsSubtreeMatroid T Mn Finset.univ M

/-- Definition 12 (pp. 15–16). An unordered decomposition tree is *clean* if every node matroid is
graphic, cographic or isomorphic to `R10`, and every cographic, non-graphic node `v` has a graph
`G_v` with `M_v = M*(G_v)` in which, for every tree edge `e` at `v` with `|S_e| = 3`, some vertex
`w` of degree three is incident to all edges of `S_e`. -/
def IsCleanDecompTree [Fintype ι] (M : Matroid β) (T : SimpleGraph ι) (Mn : ι → Matroid β) :
    Prop :=
  IsUnorderedDecompTree M T Mn ∧
    (∀ u, IsGraphic (Mn u) ∨ IsCographic (Mn u) ∨ IsR10 (Mn u)) ∧
    (∀ v, IsCographic (Mn v) → ¬ IsGraphic (Mn v) →
      ∃ (V : Type) (_ : Fintype V) (ends : β → Sym2 V), IsGraphicMatroidOf (Mn v)✶ V ends ∧
        ∀ u, T.Adj v u → (edgeBoundary Mn v u).ncard = 3 →
          ∃ x : V, degree ends (Mn v).E x = 3 ∧ ∀ e ∈ edgeBoundary Mn v u, x ∈ ends e)

open Classical in
/-- §4.1 (p. 18): for a tree edge `{u, v}`, the component of `T - u` containing `v` (a component
attached to `u`): the nodes `w` whose path from `u` passes through `v`. -/
noncomputable def attachedComp (T : SimpleGraph ι) [Fintype ι] (u v : ι) : Finset ι :=
  Finset.univ.filter (fun w => T.dist u w = T.dist v w + 1)

/-- §4.1 (p. 18): `P` is a *completion* of `s ∈ S` in the subtree `Q` with boundary set `S`:
`P ⊆ E_Q \ S` and `P ∪ {s}` is a circuit of `M_Q`. -/
def IsCompletion (T : SimpleGraph ι) (Mn : ι → Matroid β) (Q : Finset ι) (S : Set β) (s : β)
    (P : Set β) : Prop :=
  P ⊆ groundOf Mn Q \ S ∧ (subtreeMatroid T Mn Q).IsCircuit (insert s P)

/-- A minimum-cardinality completion of `s` in `Q`. -/
def IsMinCompletion (T : SimpleGraph ι) (Mn : ι → Matroid β) (Q : Finset ι) (S : Set β) (s : β)
    (P : Set β) : Prop :=
  IsCompletion T Mn Q S s P ∧ ∀ P', IsCompletion T Mn Q S s P' → P.ncard ≤ P'.ncard

/-- §4.1 (p. 18): the *expansion* `D⁺ = (D \ ⋃ᵢ Sᵢ) ∪ ⋃ᵢ ⋃_{s ∈ D ∩ Sᵢ} P_{Qᵢ,s}` of `D`, where
`B = ⋃ᵢ Sᵢ` is the union of the selected boundary sets and `P s` the chosen completion of `s`. -/
def expansion (D B : Set β) (P : β → Set β) : Set β :=
  (D \ B) ∪ ⋃ s ∈ D ∩ B, P s

end RandDelMatroid.Indep


