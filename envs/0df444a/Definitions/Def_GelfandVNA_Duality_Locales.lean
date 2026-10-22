-- Prove2me | Definitions.Def_GelfandVNA_Duality_Locales
-- name    : GelfandVNA_Duality_Locales
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:19.865087+00:00
-- url     : https://prove2.me/theorems/6c83260f-f4fa-4fd9-9e0e-c78e625e9d5a
-- title:
--   Defs 2.15, 2.55, 2.61, pp. 10–18 — open frame maps, hyperstonean locales, the categories HStoneanLoc and MLoc
-- statement:
--   This module sets up the two localic categories of Theorem 1.1 of Pavlov, *Gelfand-type duality for commutative von Neumann algebras*.
--
--   A **frame** is a complete lattice in which finite meets distribute over arbitrary joins; a **locale** is a frame read in the opposite direction, so a map of locales $f\colon L\to L'$ is a frame map $f^*\colon L'\to L$ (Definitions 2.2–2.3). The objects of a locale are called opens, and $\neg a = (a\to 0)$ is the pseudocomplement.
--
--   1. **Open maps** (Definition 2.15). A frame map $f^*\colon L'\to L$ is *open* if it preserves arbitrary infima and the Heyting implication:
--   $$f^*\Big(\bigwedge S\Big)=\bigwedge f^*(S),\qquad f^*(m\to n)=(f^*m\to f^*n).$$
--   Identities and composites of open frame maps are open.
--   2. **Hyperstonean locales** (Definition 2.61). A locale $L$ is hyperstonean if it is Stonean (Definition 2.45: coherent, regular, and $\neg x\vee\neg\neg x=1$ for all $x$) and has sufficiently many normal valuations: for every open $a\neq 0$ there is a finite positive normal valuation $\nu\colon L\to[0,\infty)$ (a continuous valuation with $\nu(\neg\neg b)=\nu(b)$, Definition 2.57) with $\nu(a)\neq 0$.
--   3. **HStoneanLoc** is the category whose objects are hyperstonean locales and whose morphisms $L\to L'$ are the open frame maps $L'\to L$: the full subcategory of the category StoneanLoc of Stonean locales and open maps on the hyperstonean ones. It comes with its forgetful functor to the category of locales.
--   4. **MLoc** (Definitions 2.52, 2.55). A complete Boolean algebra $A$ is *localizable* if $1$ is the supremum of all $a\in A$ such that the principal algebra $aA$ admits a finite faithful continuous valuation $aA\to[0,\infty)$. The category MLoc of **measurable locales** is the full subcategory of the category of locales on the localizable Boolean algebras: a morphism $A\to B$ is any frame map $B\to A$ (for complete Boolean algebras these are exactly the complete Boolean homomorphisms, Lemma 2.44).
--
--   These two categories are the middle of the chain of equivalences $\mathsf{HStonean}\simeq\mathsf{HStoneanLoc}\simeq\mathsf{MLoc}\simeq\mathsf{CVNA}^{\mathrm{op}}$, $\mathsf{CSLEMS}\simeq\mathsf{MLoc}$.
--
--   **Formalization Note** Locales are represented by their frames (`Order.Frame`); `MLoc` is Mathlib's `InducedCategory` over `Locale`, so its morphisms are literally the locale morphisms. Valuations, Stonean locales and localizability (`HasFiniteValuationCover`) are taken from the published module `QAlgorithms_Papers_Independent_Support21_P20`, which formalizes the same paper. All objects live in `Type u` and no nontriviality is imposed (the one-element frame is allowed).
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, pp. 8–18, Definitions 2.2, 2.3, 2.15, 2.45, 2.52, 2.55, 2.57, 2.61

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace GelfandVNA.Duality

open CategoryTheory QAlgorithms.Papers.Independent.Support21.P20
open scoped NNReal

universe u

/-- Definition 2.15, p. 10: an open map of frames `f* : L' → L` is a frame map that preserves
arbitrary infima and the Heyting implication. A map of locales `L → L'` is given by its frame map
`f* : L' → L`. -/
def IsOpenFrameHom {L L' : Type u} [Order.Frame L] [Order.Frame L'] (f : FrameHom L' L) : Prop :=
  (∀ s : Set L', f (sInf s) = sInf (f '' s)) ∧ ∀ a b : L', f (a ⇨ b) = f a ⇨ f b

lemma isOpenFrameHom_id (L : Type u) [Order.Frame L] : IsOpenFrameHom (FrameHom.id L) :=
  ⟨fun s => by simp, fun _ _ => rfl⟩

lemma IsOpenFrameHom.comp {L L' L'' : Type u} [Order.Frame L] [Order.Frame L'] [Order.Frame L'']
    {f : FrameHom L' L} {g : FrameHom L'' L'} (hf : IsOpenFrameHom f) (hg : IsOpenFrameHom g) :
    IsOpenFrameHom (f.comp g) := by
  refine ⟨fun s => ?_, fun a b => ?_⟩
  · simp only [FrameHom.comp_apply]
    rw [hg.1, hf.1, Set.image_image]
    rfl
  · simp only [FrameHom.comp_apply]
    rw [hg.2, hf.2]

/-- Definition 2.61, p. 18: a hyperstonean locale is a Stonean locale (Definition 2.45) that admits
sufficiently many normal valuations: every nonzero open `a` has a (finite, positive) normal valuation
`ν : L → [0, ∞)` with `ν a ≠ 0`. -/
def IsHyperstoneanLocale (L : Type u) [Order.Frame L] : Prop :=
  IsStoneanLocale L ∧ ∀ a : L, a ≠ ⊥ → ∃ ν : L → ℝ≥0, IsPositiveNormalValuation ν ∧ ν a ≠ 0

/-- An object of `HStoneanLoc`: a hyperstonean locale, given by its frame of opens. -/
structure HStoneanLoc : Type (u + 1) where
  /-- The frame of opens. -/
  carrier : Type u
  [frame : Order.Frame carrier]
  hyperstonean : IsHyperstoneanLocale carrier

attribute [instance] HStoneanLoc.frame

/-- Definitions 2.45 and 2.61, pp. 15, 18: `HStoneanLoc` is the full subcategory of `StoneanLoc`
on hyperstonean locales, and morphisms of `StoneanLoc` are the open maps of locales. A morphism
`L → L'` is an open frame map `L' → L`. -/
instance : Category.{u} HStoneanLoc.{u} where
  Hom L L' := {f : FrameHom L'.carrier L.carrier // IsOpenFrameHom f}
  id L := ⟨FrameHom.id L.carrier, isOpenFrameHom_id L.carrier⟩
  comp f g := ⟨f.1.comp g.1, f.2.comp g.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The forgetful functor `HStoneanLoc ⥤ Loc` (Definition 2.3: `Loc = Frm^op`). -/
def HStoneanLoc.toLocale : HStoneanLoc.{u} ⥤ Locale.{u} where
  obj L := Locale.of L.carrier
  map f := (Frm.ofHom f.1).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An object of `MLoc` (Definitions 2.52, 2.55, p. 17): a localizable Boolean algebra, i.e. a
complete Boolean algebra in which `1` is the supremum of the elements `a` such that `aA` admits a
finite faithful continuous valuation (`HasFiniteValuationCover`). -/
structure MLocObj : Type (u + 1) where
  /-- The underlying complete Boolean algebra (the frame of opens of the locale). -/
  carrier : Type u
  [cba : CompleteBooleanAlgebra carrier]
  localizable : HasFiniteValuationCover carrier

attribute [instance] MLocObj.cba

/-- The locale with frame of opens `A.carrier`. -/
def MLocObj.toLocale (A : MLocObj.{u}) : Locale.{u} := Locale.of A.carrier

/-- Definition 2.55, p. 17: `MLoc` is the full subcategory of the category of locales on the
localizable Boolean algebras. -/
def MLoc : Type (u + 1) := InducedCategory Locale.{u} MLocObj.toLocale

instance : Category.{u} MLoc.{u} := inferInstanceAs (Category (InducedCategory _ MLocObj.toLocale))

/-- The underlying complete Boolean algebra of an object of `MLoc`. -/
abbrev MLoc.carrier (A : MLoc.{u}) : Type u := MLocObj.carrier A

instance (A : MLoc.{u}) : CompleteBooleanAlgebra A.carrier := MLocObj.cba A

/-- The frame map `B → A` underlying a morphism `A ⟶ B` of `MLoc`. -/
def MLoc.frameHom {A B : MLoc.{u}} (f : A ⟶ B) : FrameHom B.carrier A.carrier :=
  (InducedCategory.Hom.hom f).unop.hom

end GelfandVNA.Duality


