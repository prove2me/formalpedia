-- Prove2me | Definitions.Def_UnitSquarePack_NPHard_PackingLanguage
-- name    : UnitSquarePack_NPHard_PackingLanguage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:19:49.134336+00:00
-- url     : https://prove2.me/theorems/26ad0c4f-838d-4ef6-ac32-c0a8077f353d
-- title:
--   The language 2×2-Square-Packing restricted to orthogonally convex grid polygons
-- statement:
--   An instance of 2 × 2-Square-Packing is a polygon $P$, given in the standard representation as the coordinates of its vertices in binary, and an integer $k$. Here an instance is a vertex list $v_0, \dots, v_{N-1} \in \mathbb Z^2$ and $k \in \mathbb N$, written as the binary word
--   $$\mathrm{code}(v, k) = \mathrm{encNat}(N)\; \mathrm{encInt}(v_{0,x})\,\mathrm{encInt}(v_{0,y}) \cdots \mathrm{encInt}(v_{N-1,x})\,\mathrm{encInt}(v_{N-1,y})\; \mathrm{encNat}(k)$$
--   with the published self-delimiting binary numerals `encNat` and `encInt` (sign bit and magnitude).
--
--   The language **2 × 2-Square-Packing on orthogonally convex grid polygons** is the set of words $\mathrm{code}(v, k)$ such that $v$ is a grid polygon, its closed region $P$ is orthogonally convex, and $P$ has room for $k$ axis-aligned $2\times 2$ squares (real positions, pairwise disjoint interiors, each square contained in $P$). Words that are not codes, codes of chains that are not grid polygons, and codes of polygons that are not orthogonally convex are not in the language.
--
--   **Formalization Note.** A negative $k$ is a trivial yes-instance and is not encoded; $k \in \mathbb N$.
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 3, §1 (input representation; problem statement p. 1)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_UnitSquarePack_NPHard_GridPolygon
import Definitions.Def_UnitSquarePack_NPHard_Squares

set_option autoImplicit false

namespace UnitSquarePack.NPHard

open OptimalQueuingComplexity.Restless

/-- The binary code of an instance `(P, k)` of 2 × 2-Square-Packing: the number `N` of vertices,
then the `N` vertices `v_0, …, v_{N-1}` of `P` (each as two integers in sign-and-magnitude
binary), then `k` in binary. -/
def packingCode (vs : List (ℤ × ℤ)) (k : ℕ) : List Bool :=
  encNat vs.length ++ vs.flatMap (fun v => encInt v.1 ++ encInt v.2) ++ encNat k

/-- The language 2 × 2-Square-Packing restricted to orthogonally convex grid polygons: the codes
of the pairs `(vs, k)` such that `vs` is a grid polygon whose closed region `P` is orthogonally
convex and `P` has room for `k` axis-aligned `2 × 2` squares. Words that are not such a code,
codes of chains that are not grid polygons, and codes of polygons that are not orthogonally
convex are not in the language. -/
def orthoConvexSquarePacking : CookPvsNP.Lang Bool :=
  {w | ∃ (vs : List (ℤ × ℤ)) (k : ℕ), w = packingCode vs k ∧ IsGridPolygon vs ∧
      IsOrthogonallyConvex (region vs) ∧ HasRoomFor (region vs) k}

end UnitSquarePack.NPHard


