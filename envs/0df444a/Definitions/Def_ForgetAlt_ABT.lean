-- Prove2me | Definitions.Def_ForgetAlt_ABT
-- name    : ForgetAlt_ABT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:21:58.006531+00:00
-- url     : https://prove2.me/theorems/d9476318-911a-400c-94b5-1e1ac7ee8113
-- title:
--   Candidate parents, the alternating base DAG, alternating base trees, incoming edges and MIEs
-- statement:
--   For a vertex $u$ of the extended system, the **candidate parents** $P(u)$ are the vertices $u'$ such that some shortest orthodox alternating path from $f$ to $u$ ends with the edge $\{u',u\}$. The **alternating base DAG** (ABD) $H$ has the vertices reachable from $f$ and the arcs $(u,u')$ with $u'\in P(u)$; $E^+_H(u)$ is the set of edges $\{u,u'\}$, $u'\in P(u)$. An edge of the graph not in $H$ is **critical**.
--
--   An **alternating base tree** (ABT) $T$ chooses for every reachable $v\neq f$ one parent $p_T(v)\in P(v)$. $T(v)$ is the set of reachable vertices whose ancestor chain reaches $v$, and $r_T(v)$ is the free vertex $u$ with $v\in T(u)$. An **incoming edge** of $T(t)$ is a non-tree edge $\{y,z\}$ with $y\notin T(t)$, $z\in T(t)$; $\tilde E_T(t)$ is the set of them; a **minimum incoming edge** (MIE) is one of minimum level, and the MIEs $e^*_T(t)$ are fixed arbitrarily. For a path $P$, $\mathrm{level}_T(P)$ and $\mathrm{vlevel}_T(P)$ are the maximum level and volume of its non-tree edges (the least value if there are none).
--
--   **Formalization Note** An ABT is a total parent function with a validity predicate; its values at $f$ and at unreachable vertices are ignored (the ancestor chain stops at $f$). "Fix the MIEs arbitrarily" is a function `mie` with the property `MIEChoice`, and every theorem quantifies over all such functions.
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Section 3.2, Definitions 3.2 and 3.4, printed pp.17–18 (PDF pp.18–19); Section 3.3, printed pp.18–19 (PDF pp.19–20)

import Mathlib
import Definitions.Def_ForgetAlt_ExtSystem

namespace ForgetAlt

open BergeMatching.Core

/-!
# The alternating base DAG, alternating base trees, incoming edges and MIEs

Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…), Section 3.2 (Definitions 3.2 and 3.4), printed pp.17–18
(PDF pp.18–19), and Section 3.3, printed pp.18–19 (PDF pp.19–20).

**Formalization Notes.**
* An ABT is a total parent function `par : ExtV V → ExtV V` with the validity predicate
  `IsABT`: every reachable vertex other than `f` has its parent among its candidate parents.
  Its values on `f` and on unreachable vertices are unconstrained and ignored: the ancestor
  chain (`parT`) stops at `f`, and `InSubtree` only contains reachable vertices, so `V(T)` is the
  reachable set as in Definition 3.4.
* A tree edge is `{v, par v}` for a reachable `v ≠ f`. "`T` respects a path" is: every vertex
  of the path except the last has the next vertex as its parent.
* "Fix an MIE `e*_T(t)` arbitrarily" (p.19) is a function `mie` with the property `MIEChoice`;
  theorems quantify over **every** such function.
* `levelT` / `vlevelT` of a walk: the maximum level / volume over its non-tree edges, and the
  least value (`(0, 0)` / `0`) when it has none, as on p.19.
-/

variable {V : Type}

/-- The candidate parents `P_I(u)` (p.17): the vertices `u'` such that some shortest orthodox
alternating path from `f` to `u` ends with the edge `{u', u}`. -/
def candParents (G : SimpleGraph V) (M : G.Subgraph) (u : ExtV V) : Set (ExtV V) :=
  {u' | ∃ (q : (extGraph G M).Walk .f u') (h : (extGraph G M).Adj u' u),
    IsAltPath (extMatching G M) (q.concat h) ∧ parityOf (q.concat h).length = alpha G M u ∧
      ((q.concat h).length : ℕ∞) = distA G M u}

/-- The arc `(u, u')` of the alternating base DAG `H_I` (Definition 3.2): `u` is reachable and
`u' ∈ P_I(u)`. -/
def abdArc (G : SimpleGraph V) (M : G.Subgraph) (u u' : ExtV V) : Prop :=
  Reach G M u ∧ u' ∈ candParents G M u

/-- `E⁺_H(u)` (p.18): the undirected edges `{u, u'}` with `u' ∈ P_I(u)`. -/
def EplusH (G : SimpleGraph V) (M : G.Subgraph) (u : ExtV V) : Set (Sym2 (ExtV V)) :=
  {e | ∃ u', abdArc G M u u' ∧ e = s(u, u')}

/-- An edge of the extended system lies in `E(H_I)` (one of its orientations is an ABD arc). -/
def InABD (G : SimpleGraph V) (M : G.Subgraph) (e : Sym2 (ExtV V)) : Prop :=
  ∃ u u', abdArc G M u u' ∧ e = s(u, u')

/-- A critical edge (p.18): an edge of the graph not contained in `E(H_I)`. -/
def IsCritical (G : SimpleGraph V) (M : G.Subgraph) (e : Sym2 (ExtV V)) : Prop :=
  e ∈ (extGraph G M).edgeSet ∧ ¬ InABD G M e

/-- An alternating base tree (Definition 3.4), as a parent function: every reachable vertex
other than `f` has exactly one outgoing edge, to one of its candidate parents. -/
def IsABT (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V) : Prop :=
  ∀ v, v ≠ .f → Reach G M v → par v ∈ candParents G M v

/-- The parent map with `f` as a fixed point (the root has no parent). -/
def parT (par : ExtV V → ExtV V) : ExtV V → ExtV V
  | .f => .f
  | v => par v

/-- `w ∈ V(T(v))`: `w` is a vertex of `T` (reachable) and `v` is an ancestor of `w` (possibly
`w` itself). -/
def InSubtree (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V) (v w : ExtV V) :
    Prop :=
  Reach G M w ∧ ∃ k : ℕ, (parT par)^[k] w = v

/-- `r_T(v)` (p.18): the free vertex `u` with `v ∈ V(T(u))`. It is unique when it exists (the
subtrees `T(u)`, `u ∈ U`, partition the reachable original vertices); junk otherwise. -/
noncomputable def rootFree (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V)
    (v : ExtV V) : ExtV V :=
  open Classical in
  if h : ∃ u : V, IsNeutral M u ∧ InSubtree G M par (.orig u) v then .orig h.choose else v

/-- A tree edge of the ABT `par`: `{v, p_T(v)}` for a reachable `v ≠ f`. -/
def IsTreeEdge (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V)
    (e : Sym2 (ExtV V)) : Prop :=
  ∃ v, v ≠ .f ∧ Reach G M v ∧ e = s(v, par v)

/-- `T` respects a path given as a vertex list directed towards the root: each vertex but the
last has the next one as its parent (Definition 3.4, "T contains X as a subgraph"). -/
def RespectsPath (par : ExtV V → ExtV V) (l : List (ExtV V)) : Prop :=
  l.IsChain (fun a b => par a = b)

/-- An incoming edge of `T(t)` (p.18): an edge `{y, z} ∉ E(T)` with `y ∉ V(T(t))` and
`z ∈ V(T(t))`. -/
def IsIncoming (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V) (t : ExtV V)
    (e : Sym2 (ExtV V)) : Prop :=
  e ∈ (extGraph G M).edgeSet ∧ ¬ IsTreeEdge G M par e ∧
    ∃ y z, e = s(y, z) ∧ ¬ InSubtree G M par t y ∧ InSubtree G M par t z

/-- A minimum incoming edge (MIE) of `T(t)` (p.19): a minimum-level edge of `Ẽ_T(t)`. -/
def IsMIE (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V) (t : ExtV V)
    (e : Sym2 (ExtV V)) : Prop :=
  IsIncoming G M par t e ∧ ∀ e', IsIncoming G M par t e' → level G M e ≤ level G M e'

/-- The MIEs `e*_T(t)` fixed arbitrarily (p.19): for every `t` with `Ẽ_T(t) ≠ ∅`, `mie t` is an
MIE of `T(t)`. -/
def MIEChoice (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V)
    (mie : ExtV V → Sym2 (ExtV V)) : Prop :=
  ∀ t, (∃ e, IsIncoming G M par t e) → IsMIE G M par t (mie t)

/-- `level_T(P)` (p.19): the maximum level of the non-tree edges of `P`, and `(0, 0)` (the least
level) if there are none. -/
noncomputable def levelT (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V)
    {a b : ExtV V} (p : (extGraph G M).Walk a b) : WithTop (ℕ ×ₗ ℕ) :=
  open Classical in
  p.edges.foldr (fun e acc => if IsTreeEdge G M par e then acc else max (level G M e) acc)
    ((toLex ((0 : ℕ), (0 : ℕ)) : ℕ ×ₗ ℕ) : WithTop (ℕ ×ₗ ℕ))

/-- `vlevel_T(P)` (p.19): the maximum volume of the non-tree edges of `P`, `0` if none. -/
noncomputable def vlevelT (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V)
    {a b : ExtV V} (p : (extGraph G M).Walk a b) : ℕ∞ :=
  open Classical in
  p.edges.foldr (fun e acc => if IsTreeEdge G M par e then acc else max (vlevelE G M e) acc) 0

end ForgetAlt


