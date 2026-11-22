-- Prove2me | Definitions.Def_TopStack_Inertia
-- name    : TopStack_Inertia
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T17:00:37.021362+00:00
-- url     : https://prove2.me/theorems/8d7982a3-3723-4352-be53-15cd74739735
-- title:
--   The inertia category $\mathcal I_{\mathcal X}$ of a category $p:\mathcal X\to\mathcal S$ over a base, with $\iota:\mathcal I_{\mathcal X}\to\mathcal X$ and $q:\mathcal I_{\mathcal X}\to\mathcal S$
-- statement:
--   **The inertia category of a category over a base.** Let $\mathcal S$ be a category and $p:\mathcal X\to\mathcal S$ a functor (for instance a stack in groupoids over a site). The *inertia category* $\mathcal I_{\mathcal X}$ of $\mathcal X$ is the category whose
--
--   1. objects are the pairs $(x,f)$ with $x$ an object of $\mathcal X$ and $f:x\to x$ an automorphism of $x$ with $p(f)=\mathrm{id}_{p(x)}$;
--   2. morphisms $(x,f)\to(y,g)$ are the morphisms $\phi:x\to y$ of $\mathcal X$ making the square commute:
--   $$\phi\circ f=g\circ\phi,$$
--   with composition and identities those of $\mathcal X$.
--
--   It comes with the canonical functor $\iota:\mathcal I_{\mathcal X}\to\mathcal X$, $(x,f)\mapsto x$, $\phi\mapsto\phi$ (Remark E.6.3.3), and the structure functor $q=p\circ\iota:\mathcal I_{\mathcal X}\to\mathcal S$, $(x,f)\mapsto p(x)$.
--
--   Inertia keeps track of the automorphisms of the objects of a stack that lie over identities of the base; for a quotient stack $[X/\mathcal G]$ of a topological groupoid it interpolates the isotropy (inertia) groups $I_x$ of the points of $X$ (Lemma E.6.3.11, Remark E.6.3.12), and "trivial inertia" ($\iota$ an equivalence) is the condition under which the paper studies representability of quotient stacks (Lemma E.6.3.7, Proposition E.6.3.8).
--
--   **Formalization Note.** `TopStack.Inertia p` is a structure with fields `obj`, `aut : obj ≅ obj` and `map_aut_hom : p.map aut.hom = 𝟙 (p.obj obj)`; its morphisms are the subtype `{φ : a.obj ⟶ b.obj // a.aut.hom ≫ φ = φ ≫ b.aut.hom}` (Mathlib composes left to right, so `f ≫ φ = φ ≫ g` is $\phi\circ f=g\circ\phi$). `TopStack.Inertia.forget p` is $\iota$ and `TopStack.Inertia.proj p := forget p ⋙ p` is $q$. The definition makes sense for any functor $p$; the paper takes $p$ a stack over $\mathbf{CGWH}_{\alpha,\tau}$ and follows the Stacks Project, Tag 034I(2).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 924, Definition E.6.3.1, and p. 925, Remark E.6.3.3; classical reference: the paper follows the Stacks Project, Tags 034I(2) and 04Z2

import Mathlib

/-!
# The inertia category of a category over a base

For a functor `p : 𝒳 ⥤ 𝒮` (a category `𝒳` over a base category `𝒮`, e.g. a category fibered in
groupoids over a site), the *inertia category* `I_𝒳` has as objects the pairs `(x, f)` of an object
`x` of `𝒳` and an automorphism `f : x ≅ x` lying over the identity of `p(x)`, and as morphisms
`(x, f) ⟶ (y, g)` the morphisms `φ : x ⟶ y` of `𝒳` with `f ≫ φ = φ ≫ g`.

* `TopStack.Inertia p` : the inertia category `I_𝒳` of `p`.
* `TopStack.Inertia.forget p` : the canonical functor `ι : I_𝒳 ⥤ 𝒳`, `(x, f) ↦ x`.
* `TopStack.Inertia.proj p` : the structure functor `q : I_𝒳 ⥤ 𝒮`, `(x, f) ↦ p(x)`, i.e. `ι ⋙ p`.

Source: A. M. Masullo, *The Music of the Primes*, Definition E.6.3.1 and Remark E.6.3.3
(following the Stacks Project, Tags 034I and 04Z2).
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace TopStack

/-- An object of the *inertia category* `I_𝒳` of a functor `p : 𝒳 ⥤ 𝒮`: a pair `(x, f)` of an
object `x` of `𝒳` and an automorphism `f : x ≅ x` with `p(f) = 𝟙_{p(x)}`. -/
structure Inertia {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
    (p : 𝒳 ⥤ 𝒮) where
  /-- The underlying object `x` of `𝒳`. -/
  obj : 𝒳
  /-- The automorphism `f : x ≅ x`. -/
  aut : obj ≅ obj
  /-- The automorphism lies over the identity: `p(f) = 𝟙_{p(x)}`. -/
  map_aut_hom : p.map aut.hom = 𝟙 (p.obj obj)

namespace Inertia

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒮}

/-- The morphisms `(x, f) ⟶ (y, g)` of the inertia category are the morphisms `φ : x ⟶ y` of `𝒳`
with `f ≫ φ = φ ≫ g`; composition and identities are those of `𝒳`. -/
instance category : Category (Inertia p) where
  Hom a b := {φ : a.obj ⟶ b.obj // a.aut.hom ≫ φ = φ ≫ b.aut.hom}
  id a := ⟨𝟙 a.obj, by rw [Category.comp_id, Category.id_comp]⟩
  comp φ ψ := ⟨φ.1 ≫ ψ.1, by
    rw [← Category.assoc, φ.2, Category.assoc, ψ.2, Category.assoc]⟩
  id_comp φ := Subtype.ext (Category.id_comp φ.1)
  comp_id φ := Subtype.ext (Category.comp_id φ.1)
  assoc φ ψ χ := Subtype.ext (Category.assoc φ.1 ψ.1 χ.1)

variable (p) in
/-- The canonical functor `ι : I_𝒳 ⥤ 𝒳`, `(x, f) ↦ x`, `φ ↦ φ`. -/
def forget : Inertia p ⥤ 𝒳 where
  obj a := a.obj
  map φ := φ.1
  map_id _ := rfl
  map_comp _ _ := rfl

variable (p) in
/-- The structure functor `q : I_𝒳 ⥤ 𝒮`, `(x, f) ↦ p(x)`, i.e. the composite `ι ⋙ p`. -/
abbrev proj : Inertia p ⥤ 𝒮 := forget p ⋙ p

@[simp] lemma forget_obj (a : Inertia p) : (forget p).obj a = a.obj := rfl

@[simp] lemma forget_map {a b : Inertia p} (φ : a ⟶ b) : (forget p).map φ = φ.1 := rfl

end Inertia

end TopStack


