-- Prove2me | Definitions.Def_ForgetAlt_DoublePathABD
-- name    : ForgetAlt_DoublePathABD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:57.463256+00:00
-- url     : https://prove2.me/theorems/4a07cf86-200b-421a-b42d-ca9d4f57c43a
-- title:
--   $H_0$, crossable edges $E^*$, the bridges $E_c$, double paths of the ABD and $\mathrm{Aug}(D)$
-- statement:
--   $H_0$ is the ABD with $f$ and every $a_u$ removed; its sinks are the free vertices, and $\mathrm{cl}=\mathrm{cl}_{H_0}$. An ABT $T$ **separates** $e=\{y,z\}$ if $r_T(y)\neq r_T(z)$. An edge is **crossable** if its volume is $2\ell+5$ and some ABT separates it; $E^*$ is the set of crossable critical edges, and $E_c$ the set of all critical edges of volume $2\ell+5$.
--
--   A **double path** of $(H,B)$ for a bridge set $B$ is a 4-tuple $(P,Q,y,z)$ with $\{y,z\}\in B$ and $P,Q$ vertex-disjoint directed paths of $H_0$ from $y$ and $z$ to free vertices. An ABT **respects** $(P,Q,y,z)$ if every vertex of $P$ and $Q$ other than the last has the next vertex as its parent. For a set $D$ of double paths and an ABT respecting all of them,
--
--   $$\mathrm{Aug}(D)=\big(\textsc{PathConstruction}(T,r_T(y),r_T(z),\mathrm{odd},\{y,z\})\big)_{(P,Q,y,z)\in D}.$$
--
--   **Formalization Note** The arcs of $H_0$ are a relation on the original vertex type; unreachable vertices carry no arc. The bridge set is a parameter of the double-path predicate so that $E_c$ and $E^*$ can be compared.
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Definitions 3.10 and 3.11, printed p.23 (PDF p.24); Section 3.5, printed pp.24 (PDF p.25)

import Mathlib
import Definitions.Def_ForgetAlt_PathConstruction
import Definitions.Def_ForgetAlt_Postdom

namespace ForgetAlt

open BergeMatching.Core

/-!
# `H₀`, crossable edges `E*`, the bridge set `E_c`, double paths of the ABD and `Aug(D)`

Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…), Definitions 3.10 and 3.11 and the paragraphs after them,
printed pp.23–24 (PDF pp.24–25); `H₀` and `cl` from Section 3.5, printed p.24 (PDF p.25).

**Formalization Notes.**
* `H₀` is the ABD with `f` and every `a_u` removed. Its arc relation `h0Adj` lives on `V`;
  a vertex of `V` unreachable from `f` carries no arc and plays no role (no arc of `H₀` enters
  or leaves it), so `cl (h0Adj G M)` on reachable vertices is `cl_{H₀}`. Statements about
  `V(H₀)` assume reachability explicitly.
* `U` is the set of free vertices (`IsNeutral M`), the sinks of `H₀`.
* `ℓ` is `ell M`; items that use it assume that an augmenting path exists.
* A double path is the 4-tuple `(P, Q, y, z)` of Definition 3.11, with `P`, `Q` vertex lists
  of directed paths of `H₀` from `y`, `z` to vertices of `U`. A bridge predicate
  (`InEstar` or `InEc`) is a parameter, so that the Section 3.4 claim compares the two.
* `Aug(D)` is the list of outputs of `PathConstruction(T, r_T(y), r_T(z), odd, {y, z})`, one per
  member of `D`, each a list of original vertices.
-/

variable {V : Type}

/-- The arc relation of `H₀` (Section 3.5): the ABD arcs between original vertices. -/
def h0Adj (G : SimpleGraph V) (M : G.Subgraph) (a b : V) : Prop :=
  abdArc G M (.orig a) (.orig b)

/-- `T` separates `e = {y, z}` (Definition 3.10): `r_T(y) ≠ r_T(z)`, both defined. -/
def Separates (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V)
    (e : Sym2 (ExtV V)) : Prop :=
  ∃ y z, e = s(y, z) ∧ ∃ u u' : V, u ≠ u' ∧ IsNeutral M u ∧ IsNeutral M u' ∧
    InSubtree G M par (.orig u) y ∧ InSubtree G M par (.orig u') z

/-- A crossable edge (Definition 3.10): volume `2ℓ + 5` and separated by some ABT. -/
def IsCrossable (G : SimpleGraph V) (M : G.Subgraph) (e : Sym2 (ExtV V)) : Prop :=
  vlevelE G M e = ((2 * ell M + 5 : ℕ) : ℕ∞) ∧
    ∃ par, IsABT G M par ∧ Separates G M par e

/-- `E*` (Definition 3.10): the crossable critical edges, as a predicate on original pairs. -/
def InEstar (G : SimpleGraph V) (M : G.Subgraph) (y z : V) : Prop :=
  IsCritical G M s(.orig y, .orig z) ∧ IsCrossable G M s(.orig y, .orig z)

/-- `E_c` (Section 3.4, p.23): the critical edges of volume `2ℓ + 5`. -/
def InEc (G : SimpleGraph V) (M : G.Subgraph) (y z : V) : Prop :=
  IsCritical G M s(.orig y, .orig z) ∧
    vlevelE G M s(.orig y, .orig z) = ((2 * ell M + 5 : ℕ) : ℕ∞)

/-- A directed path of `H₀` from `x` to a vertex of `U` (a free vertex). -/
def IsH0PathToU (G : SimpleGraph V) (M : G.Subgraph) (x : V) (l : List V) : Prop :=
  IsDPath (h0Adj G M) l ∧ l.head? = some x ∧ ∃ u, l.getLast? = some u ∧ IsNeutral M u

/-- A double path `(P, Q, y, z)` of `(H, B)` for a bridge predicate `B` (Definition 3.11):
`{y, z}` a bridge, `P`, `Q` vertex-disjoint paths of `H₀` from `y` and `z` ending in `U`
(their end vertices are then distinct). -/
def IsDoublePathABD (G : SimpleGraph V) (M : G.Subgraph) (B : V → V → Prop)
    (d : List V × List V × V × V) : Prop :=
  B d.2.2.1 d.2.2.2 ∧ IsH0PathToU G M d.2.2.1 d.1 ∧ IsH0PathToU G M d.2.2.2 d.2.1 ∧
    List.Disjoint d.1 d.2.1

/-- The vertices of a double path. -/
def dpVerts (d : List V × List V × V × V) : List V := d.1 ++ d.2.1

/-- A set of pairwise vertex-disjoint double paths of `(H, B)`. -/
def IsDisjointDPFamilyABD (G : SimpleGraph V) (M : G.Subgraph) (B : V → V → Prop)
    (D : List (List V × List V × V × V)) : Prop :=
  (∀ d ∈ D, IsDoublePathABD G M B d) ∧ D.Pairwise (fun d d' => List.Disjoint (dpVerts d) (dpVerts d'))

/-- A *maximal* set of vertex-disjoint double paths of `(H, B)`: no double path is
vertex-disjoint from all members. -/
def IsMaximalDPFamilyABD (G : SimpleGraph V) (M : G.Subgraph) (B : V → V → Prop)
    (D : List (List V × List V × V × V)) : Prop :=
  IsDisjointDPFamilyABD G M B D ∧
    ∀ d, IsDoublePathABD G M B d → ∃ d' ∈ D, ¬ List.Disjoint (dpVerts d) (dpVerts d')

/-- `T` respects the double path `(P, Q, y, z)` (p.23): it respects both `P` and `Q`. -/
def RespectsDP (par : ExtV V → ExtV V) (d : List V × List V × V × V) : Prop :=
  RespectsPath par (d.1.map .orig) ∧ RespectsPath par (d.2.1.map .orig)

/-- The augmenting path obtained from `(P, Q, y, z)` with `T` (p.23):
`PathConstruction(T, r_T(y), r_T(z), odd, {y, z})` returns `l`, read as original vertices. -/
def IsAugOfDP (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V)
    (mie : ExtV V → Sym2 (ExtV V)) (d : List V × List V × V × V) (l : List V) : Prop :=
  PCReturns G M par mie (rootFree G M par (.orig d.2.2.1)) (rootFree G M par (.orig d.2.2.2))
    .odd s(.orig d.2.2.1, .orig d.2.2.2) (l.map .orig)

/-- `A = Aug(D)` (Section 3.5, p.24): the `i`-th member of `A` is the augmenting path obtained
from the `i`-th member of `D` with `T`. -/
def IsAugOf (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V)
    (mie : ExtV V → Sym2 (ExtV V)) (D : List (List V × List V × V × V)) (A : List (List V)) :
    Prop :=
  List.Forall₂ (IsAugOfDP G M par mie) D A

end ForgetAlt


