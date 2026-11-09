-- Prove2me | Definitions.Def_WatsonPseudodeterminism_MASeparation_Rectangles
-- name    : WatsonPseudodeterminism_MASeparation_Rectangles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:23:49.066976+00:00
-- url     : https://prove2.me/theorems/60b294d9-f782-4d54-b366-518b5e556ad9
-- title:
--   Finite combinatorial rectangles and pointwise containment
-- statement:
--   A finite combinatorial rectangle on input spaces $X,Y$ is represented by a pair of finite sides $A\subseteq X$, $B\subseteq Y$. Its points are
--
--   $$R=A\times B.$$
--
--   A subrectangle is a rectangle whose Cartesian product is contained in that of its parent. Two rectangles are disjoint when their sets of input pairs are disjoint. This definition does not require both sides of a subrectangle to be nonempty: empty products represent the empty rectangle. In packing families, disjointness is imposed on input pairs, so overlap on one individual side remains permitted. The interface is independent of the inner-product gadget and can be reused for other communication problems.
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §2.2, p. 7 (rectangles and pairwise disjoint subrectangles); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Mathlib

namespace WatsonPseudodeterminism.MASeparation

/-- A combinatorial rectangle is given by its two finite sides. -/
abbrev Rectangle (X Y : Type) := Finset X × Finset Y

/-- The underlying finite Cartesian product. -/
noncomputable def rectPoints {X Y : Type} (R : Rectangle X Y) : Finset (X × Y) := by
  classical
  exact R.1 ×ˢ R.2

/-- Subrectangle means inclusion of the actual Cartesian products, including empty products. -/
def Subrectangle {X Y : Type} (Q R : Rectangle X Y) : Prop :=
  rectPoints Q ⊆ rectPoints R

/-- Disjointness concerns points, rather than either individual side. -/
def DisjointRectangles {X Y : Type} (Q R : Rectangle X Y) : Prop :=
  Disjoint (rectPoints Q) (rectPoints R)

end WatsonPseudodeterminism.MASeparation


