-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateSupport
-- name    : OAI_Geometry_DoublingHilbert_CoordinateSupport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:01:05.405613+00:00
-- url     : https://prove2.me/theorems/65103b16-838c-4779-8968-66c5088191b0
-- title:
--   Coordinate support of the points of the strip set in $\ell^2$
-- statement:
--   Work in real $\ell^2=\ell^2(\mathbb{N};\mathbb{R})$ with standard unit vectors $e_0,e_1,e_2,\dots$. Recall the strip construction: level $j\in\mathbb{N}$ has scale $r_j=1000^{-(j+1)}$, the coordinate index of level $j$ and color $i$ is $c(j,i)=2+\pi(j,i)$, where $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ is a fixed pairing bijection, and a base point $p=(p_1,p_2)\in\mathbb{R}^2$ together with a finitely supported tuple $w:\mathbb{N}\to\mathbb{N}$ gives the point
--   $$
--   z(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\neq0} r_j\,e_{c(j,\,w_j-1)}\in\ell^2 .
--   $$
--
--   This module records where such points live in coordinates.
--
--   1. **Injectivity of the coordinate index.** For all $j,i,m,h\in\mathbb{N}$ one has $c(j,i)=c(m,h)$ if and only if $j=m$ and $i=h$.
--   2. **Base coordinates.** For every base point $p$ and every tuple $w$, the coordinates of $z(p,w)$ with index $0$ and $1$ are $z(p,w)_0=p_1$ and $z(p,w)_1=p_2$; the displacements never touch these two coordinates.
--   3. **Coordinate support of a tuple.** For a finitely supported tuple $w$ the finite set
--   $$
--   \Sigma(w)=\{0,1\}\cup\{\,c(j,\,w_j-1):\ j\in\mathbb{N},\ w_j\neq0\,\}\subseteq\mathbb{N}
--   $$
--   consists of the two base coordinates and, for each level $j$ where $w$ is nonzero, the coordinate of the displacement chosen at that level. It depends only on $w$, not on the base point $p$, and it contains every coordinate in which $z(p,w)$ can be nonzero.
--
--   These facts show that each point of the strip set, and hence each finite set of such points, is supported on finitely many coordinates of $\ell^2$. That finiteness is what allows a finite piece of the strip set to be transported linearly into an arbitrary infinite-dimensional normed space using only finitely many vectors.
--
--   **Formalization Note** The defined object is `pointSupport w : Finset ℕ`; items 1 and 2 are the simp lemmas `coordinate_eq_iff`, `point_apply_zero` and `point_apply_one` about `coordinate` and `point` from the construction module. Elements of `RealL2` are evaluated coordinatewise as functions on the natural numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/CoordinateSupport.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/CoordinateSupport.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CompactBanach mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling

namespace OAI

open Set Metric
noncomputable section
namespace CompactBanach
open DoublingHilbert

@[simp] theorem coordinate_eq_iff (j i m h : ℕ) :
    coordinate j i = coordinate m h ↔ j = m ∧ i = h := by
  constructor
  · intro hh
    exact Prod.mk.inj (coordinate_injective hh)
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem point_apply_zero (p : Base) (w : Tuple) : point p w 0 = p.1 := by
  simp only [point, lp.coeFn_add, Pi.add_apply, baseVector, tupleVector, lp.coeFn_sum,
    Finset.sum_apply, levelVector, lp.single_apply]
  simp

@[simp] theorem point_apply_one (p : Base) (w : Tuple) : point p w 1 = p.2 := by
  simp only [point, lp.coeFn_add, Pi.add_apply, baseVector, tupleVector, lp.coeFn_sum,
    Finset.sum_apply, levelVector, lp.single_apply]
  simp

                                                                        
noncomputable def pointSupport (w : Tuple) : Finset ℕ :=
  insert 0 (insert 1 (w.support.image fun j => coordinate j (w j - 1)))

end CompactBanach
end

end OAI


