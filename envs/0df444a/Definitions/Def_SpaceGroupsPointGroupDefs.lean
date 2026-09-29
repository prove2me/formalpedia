-- Prove2me | Definitions.Def_SpaceGroupsPointGroupDefs
-- name    : SpaceGroupsPointGroupDefs
-- status  : Definition
-- author  : @Gabewhigham
-- created : 2026-09-06T07:23:33.90954+00:00
-- url     : https://prove2.me/theorems/2778e414-5b26-4f5f-8b7b-0cad9d2f8b4b
-- title:
--   Point group and translation lattice of a Euclidean group
-- statement:
--   Basic constructions attached to a subgroup $G$ of the Euclidean motion group $E_d$ of $\mathbb{R}^d$.
--
--   For an isometry $g$ of $\mathbb{R}^d$, its **linear part** $\mathrm{lin}(g)$ is the linear isometry with $g(x) = \mathrm{lin}(g)(x) + g(0)$. For a subgroup $G \le E_d$ we introduce:
--
--   1. the set of **translation vectors** of $G$, $T(G) = \{v : \text{some } g \in G \text{ is the translation } x \mapsto x+v\}$, which is an additive subgroup of $\mathbb{R}^d$ and hence a $\mathbb{Z}hBcsubmodule (the **translation lattice** of $G$);
--   2. the **point group** of $G$, the set $P(G) = \{\mathrm{lin}(g) : g \in G\}$ of linear parts, which is a subgroup of the orthogonal group of $\mathbb{R}^d$.
--
--   These are the standard invariants entering the structure theory of crystallographic groups: a space group sits in an extension of its point group by its translation lattice.
-- source:
--   Standard definitions; see e.g. L. S. Charlap, Bieberbach Groups and Flat Manifolds, Springer 1986, Chapter I, Sections 1-2.

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions

/-!
# Point group and translation lattice of a Euclidean group

Basic definitions attached to a subgroup `G` of the Euclidean motion group `E_d`
(in the sense of the mission "230 space groups"):

* the linear part `linPart g` of a Euclidean isometry `g`;
* the set `transVectors G` of translation vectors realised inside `G`, packaged as the
  additive subgroup `transAddSubgroup G` and the `ℤ`-submodule `transSubmoduleZ G`
  (the *translation lattice* of `G`);
* the point group `pointGroup G`, the group of linear parts of elements of `G`.
-/

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

variable {d : ℕ}

/-- The linear part of a Euclidean isometry. -/
noncomputable def linPart (g : EuclideanIsom d) : E d ≃ₗᵢ[ℝ] E d := g.linearIsometryEquiv

lemma linPart_apply_add (g : EuclideanIsom d) (x y : E d) :
    linPart g y = g (x + y) - g x := by
  have := AffineIsometryEquiv.map_vsub g (x + y) x
  simpa [linPart, vsub_eq_sub] using this

@[simp] lemma linPart_mul (g h : EuclideanIsom d) : linPart (g * h) = linPart g * linPart h := rfl

@[simp] lemma linPart_one : linPart (1 : EuclideanIsom d) = 1 := rfl

@[simp] lemma linPart_inv (g : EuclideanIsom d) : linPart g⁻¹ = (linPart g)⁻¹ := rfl

/-- The set of translation vectors realised by elements of `G`. -/
def transVectors (G : Subgroup (EuclideanIsom d)) : Set (E d) :=
  {v | ∃ g ∈ G, IsTranslationBy g v}

/-- The **point group** of `G`: the set of linear parts of elements of `G`. -/
def pointGroupSet (G : Subgroup (EuclideanIsom d)) : Set (E d ≃ₗᵢ[ℝ] E d) :=
  {A | ∃ g ∈ G, linPart g = A}

/-- The translation vectors of `G`, as an additive subgroup of `ℝᵈ`. -/
def transAddSubgroup (G : Subgroup (EuclideanIsom d)) : AddSubgroup (E d) where
  carrier := transVectors G
  add_mem' := by
    rintro v w ⟨g, hg, hgv⟩ ⟨h, hh, hhw⟩
    refine ⟨g * h, G.mul_mem hg hh, fun x => ?_⟩
    show g (h x) = x + (v + w)
    rw [hhw x, hgv (x + w)]
    abel
  zero_mem' := ⟨1, G.one_mem, fun x => by simp⟩
  neg_mem' := by
    rintro v ⟨g, hg, hgv⟩
    refine ⟨g⁻¹, G.inv_mem hg, fun x => ?_⟩
    have h1 : g (g⁻¹ x) = x := by
      have : (g * g⁻¹) x = x := by simp
      simpa using this
    have h2 : g (g⁻¹ x) = g⁻¹ x + v := hgv _
    have h3 : g⁻¹ x + v = x := h2.symm.trans h1
    rw [eq_sub_of_add_eq h3]
    abel

@[simp] lemma mem_transAddSubgroup {G : Subgroup (EuclideanIsom d)} {v : E d} :
    v ∈ transAddSubgroup G ↔ v ∈ transVectors G := Iff.rfl

/-- The **translation lattice** of `G`, as a `ℤ`-submodule of `ℝᵈ`. -/
def transSubmoduleZ (G : Subgroup (EuclideanIsom d)) : Submodule ℤ (E d) :=
  AddSubgroup.toIntSubmodule (transAddSubgroup G)

@[simp] lemma mem_transSubmoduleZ {G : Subgroup (EuclideanIsom d)} {v : E d} :
    v ∈ transSubmoduleZ G ↔ v ∈ transVectors G := Iff.rfl

/-- The point group of `G`, as a subgroup of the group of linear isometries of `ℝᵈ`. -/
def pointGroup (G : Subgroup (EuclideanIsom d)) : Subgroup (E d ≃ₗᵢ[ℝ] E d) where
  carrier := pointGroupSet G
  mul_mem' := by
    rintro A B ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
    exact ⟨g * h, G.mul_mem hg hh, rfl⟩
  one_mem' := ⟨1, G.one_mem, rfl⟩
  inv_mem' := by
    rintro A ⟨g, hg, rfl⟩
    exact ⟨g⁻¹, G.inv_mem hg, rfl⟩

@[simp] lemma mem_pointGroup {G : Subgroup (EuclideanIsom d)} {A : E d ≃ₗᵢ[ℝ] E d} :
    A ∈ pointGroup G ↔ ∃ g ∈ G, linPart g = A := Iff.rfl

end SpaceGroupsProblem
end Geometry
end LeanEval


