-- Prove2me | Definitions.Def_BasicPackArb_Main_Supplement_Polyhedron
-- name    : BasicPackArb_Main_Supplement_Polyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:56:17.599975+00:00
-- url     : https://prove2.me/theorems/d4c4843d-7568-4067-979f-4a1c2bb9adb2
-- title:
--   The packing polyhedron (5)–(7), actual-arc coordinates and packing vectors
-- statement:
--   For a finite digraph $D=(V,A)$, root set $S$, placement $\pi$ and matroid $M$ on $S$, let $k=r_M(S)$ and $S_X=\pi^{-1}(X)$. A vector $x$ has one real coordinate for each actual arc $a\in A$, and $x(F)=\sum_{a\in F\cap A}x(a)$. The polyhedron is
--
--   $$P_{M,D}=\{x:0\le x(a)\le1\ (a\in A),\ x(\varrho_D(X))+r_M(S_X)\ge k\ (\varnothing\ne X\subseteq V),\ x(A)=k|V|-|S|\}.$$
--
--   For a family of arborescences, its packing vector is the indicator of its arc union. An integral polyhedron here means equality with the convex hull of its integer points; the box constraints make this equivalent to integer extreme points. Empty polyhedra are allowed. Loops are coordinates in $A$, although no loop enters any cut or occurs in an arborescence. All subtractions in the displayed system use real arithmetic.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 6, (5)–(7)

import Definitions.Def_BasicPackArb_Main_Supplement_TreePacking

set_option autoImplicit false
open scoped BigOperators

namespace BasicPackArb.Main.Supplement

/-- The coordinate carrier is exactly A, even if the ambient arc type is infinite. -/
abbrev ArcVector {V Arc : Type} (D : Digraph V Arc) := {a // a ∈ D.arcs} → ℝ

noncomputable def arcSum {V Arc : Type} (D : Digraph V Arc)
    (x : ArcVector D) (F : Finset Arc) : ℝ := by
  classical
  exact ∑ a : {a // a ∈ D.arcs}, if a.val ∈ F then x a else 0

/-- Equations (5)--(7), without truncation of k|V| - |S|. -/
noncomputable def packingPolyhedron {V Arc S : Type} [Fintype V] [Fintype S]
    [DecidableEq V] (D : Digraph V Arc) (π : S → V) (M : Matroid S) : Set (ArcVector D) :=
  {x | (∀ a, 0 ≤ x a ∧ x a ≤ 1) ∧
    (∀ X : Finset V, X.Nonempty →
      (rank M Set.univ : ℝ) ≤ arcSum D x (D.enteringArcs X) +
        (rank M (π ⁻¹' (X : Set V)) : ℝ)) ∧
    arcSum D x D.arcs = (rank M Set.univ : ℝ) * Fintype.card V - Fintype.card S}

noncomputable def packingVector {V Arc S : Type} [Fintype S] (D : Digraph V Arc)
    (T : S → Arborescence D) : ArcVector D := by
  classical
  exact fun a => if ∃ s, a.val ∈ (T s).arcs then 1 else 0

/-- On this bounded polyhedron, integrality is equivalently the convex hull of its integer points. -/
def IntegralPolyhedron {I : Type} (P : Set (I → ℝ)) : Prop :=
  P = convexHull ℝ {x | x ∈ P ∧ ∀ i, ∃ z : ℤ, x i = z}

end BasicPackArb.Main.Supplement


