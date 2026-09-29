-- Prove2me | Definitions.Def_SpaceGroupsLinPartHom
-- name    : SpaceGroupsLinPartHom
-- status  : Definition
-- author  : @Gabewhigham
-- created : 2026-09-06T07:59:34.876496+00:00
-- url     : https://prove2.me/theorems/9bca2c13-103a-4641-aaa4-cadfb8459254
-- title:
--   The linear part homomorphism of a group of Euclidean isometries
-- statement:
--   For a subgroup $G$ of the Euclidean motion group $E_d$ of $\mathbb{R}^d$, every element $g\in G$ decomposes as $g(x)=\mathrm{lin}(g)(x)+g(0)$ with $\mathrm{lin}(g)$ a linear isometry. Since $\mathrm{lin}(gh)=\mathrm{lin}(g)\mathrm{lin}(h)$, the assignment
--
--   $$\mathrm{lin}:G\longrightarrow O(d),\qquad g\longmapsto \mathrm{lin}(g)$$
--
--   is a group homomorphism. Its image is the point group of $G$ and its kernel is the subgroup of translations contained in $G$; this homomorphism is the exact sequence through which a space group is presented as an extension of its point group by its translation lattice.
-- source:
--   Standard; L. S. Charlap, Bieberbach Groups and Flat Manifolds, Springer 1986, Chapter I, Section 1.

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupsPointGroupDefs

/-!
# The linear part homomorphism of a group of Euclidean isometries

For a subgroup `G` of the Euclidean motion group `E_d`, the map sending an element of `G` to
its linear part is a group homomorphism `G →* O(d)`. Its range is the point group of `G` and
its kernel is the subgroup of translations belonging to `G`.
-/

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

variable {d : ℕ}

/-- The linear part homomorphism of a group of Euclidean isometries. -/
noncomputable def linPartHom (G : Subgroup (EuclideanIsom d)) : G →* (E d ≃ₗᵢ[ℝ] E d) where
  toFun g := linPart g.1
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma linPartHom_apply (G : Subgroup (EuclideanIsom d)) (g : G) :
    linPartHom G g = linPart g.1 := rfl

end SpaceGroupsProblem
end Geometry
end LeanEval


