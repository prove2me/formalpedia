-- Prove2me | Definitions.Def_HofmannStreicher1994_Groupoids
-- name    : HofmannStreicher1994_Groupoids
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-29T06:17:16.247991+00:00
-- url     : https://prove2.me/theorems/83e5dcaf-98b4-482d-8cb9-307b881f3698
-- title:
--   Identity groupoids and the discrete universe of small groupoids
-- statement:
--   For a groupoid $G$ and objects $x,y$, the identity groupoid is discrete on the arrows $G(x,y)$. Given a functor $F:G\to H$ and arrows $b:F(x)\to x'$ and $c:F(y)\to y'$, identity transport sends $p:x\to y$ to $c\circ F(p)\circ b^{-1}$.
--
--   Semantic UIP means that every pair of arrows with common endpoints is joined by an arrow in this discrete identity groupoid. Its diagonal version requires every endomorphism to be joined to the identity. These are pointwise semantic predicates; they do not themselves supply an interpretation of the object syntax or a soundness theorem.
--
--   For each universe level, $U$ is the discrete groupoid on all small groupoids and $\mathrm{El}$ decodes a code to its groupoid. Two total-space presentations are provided: the Grothendieck construction of $\mathrm{El}$ and the categorical disjoint union of the small groupoids. A concrete object in the latter comes from the one-object groupoid of permutations of a two-element set, together with its identity and transposition loops.
-- source:
--   Hofmann and Streicher, A Groupoid Model Refutes Uniqueness of Identity Proofs, author manuscript dated 21 March 1994, https://www.dcs.ed.ac.uk/home/mxh/SH.dvi.gz; LICS 1994, https://doi.org/10.1109/LICS.1994.316071. Sections 2.2, 2.3 and 3, manuscript pp. 5–7.

module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Groupoid.Discrete
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Sigma.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Algebra.Group.End

/-!
# The source geometry of the Hofmann–Streicher groupoid countermodel

This file records the literal semantic objects in Sections 2.2, 2.3 and 3 of
Hofmann and Streicher, *A Groupoid Model Refutes Uniqueness of Identity Proofs*,
author manuscript dated 21 March 1994, pp. 5–7 (LICS 1994, pp. 208–212).

The universe is **discrete on all small groupoids**, as in the 1994 manuscript.
The later universe whose morphisms are groupoid isomorphisms is not used here.
`UniverseTotal` is the explicit disjoint-union presentation of the Grothendieck
construction over this discrete universe. No claim about syntactic derivability
or soundness of an object type theory is part of these definitions.
-/

@[expose] public section

namespace HofmannStreicher1994

open CategoryTheory

universe u v w z

/-- The identity groupoid has original arrows as objects and only equality arrows.
Source: Section 2.2, manuscript p. 5. -/
def identityGroupoid (G : Type u) [Groupoid.{v} G] (x y : G) : Grpd.{v, v} :=
  Grpd.of (Discrete (x ⟶ y))

/-- The source's conjugation map for identity proofs, including the action of the
groupoid-valued family on a base arrow in the functor `F`.
With Mathlib's diagrammatic composition order, it is `b⁻¹ ≫ F(p) ≫ c`.
Source: Section 2.2, manuscript p. 5. -/
def identityTransport {G : Type u} [Groupoid.{v} G]
    {H : Type w} [Groupoid.{z} H] (F : G ⥤ H)
    {x y : G} {x' y' : H} (b : F.obj x ⟶ x') (c : F.obj y ⟶ y') :
    Discrete (x ⟶ y) ⥤ Discrete (x' ⟶ y') :=
  Discrete.functor fun p ↦ Discrete.mk (Groupoid.inv b ≫ F.map p ≫ c)

/-- Semantic UIP says any two objects of any identity groupoid are connected
by an identity proof at the next level. The latter is a hom in a discrete
groupoid, rather than Lean's own identity type as a proof-relevant object.
Source: Section 1, manuscript p. 2, and Section 3, p. 7. -/
def SemanticUIP (G : Type u) [Groupoid.{v} G] : Prop :=
  ∀ (x y : G) (p q : x ⟶ y),
    Nonempty ((Discrete.mk p : Discrete (x ⟶ y)) ⟶ Discrete.mk q)

/-- The diagonal version of semantic UIP: each endomorphism proof is identified
with reflexivity. This is the conclusion that an interpretation of K would
provide. It does not by definition assert existence of a K eliminator.
Source: Theorem 1, manuscript p. 2; Section 3.1, pp. 7–9. -/
def SemanticBasedUIP (G : Type u) [Groupoid.{v} G] : Prop :=
  ∀ (x : G) (p : x ⟶ x),
    Nonempty ((Discrete.mk p : Discrete (x ⟶ x)) ⟶ Discrete.mk (𝟙 x))

/-- The first universe in the 1994 groupoid model. Objects are all groupoids
small in universe `u`; its arrows are equality arrows only.
Source: Section 2.3, manuscript p. 7. -/
abbrev Universe := Discrete Grpd.{u, u}

/-- The generic family decodes a universe object to the small groupoid it names.
Source: Section 2.3, manuscript p. 7. -/
def universeEl : Universe.{u} ⥤ Grpd.{u, u} :=
  Discrete.functor id

/-- Mathlib's general Grothendieck presentation of `Σ X : U. El(X)`. -/
abbrev UniverseGrothendieck := Grothendieck (universeEl.{u} ⋙ Grpd.forgetToCat)

/-- Explicit disjoint-union presentation of `Σ X : U. El(X)`. Its objects are
pairs consisting of a small groupoid and an object of that groupoid. Since U is
discrete, arrows are precisely arrows within one chosen groupoid.
Source: Section 3, manuscript p. 7. -/
abbrev UniverseTotal := Σ G : Grpd.{u, u}, G

instance universeTotalGroupoid : Groupoid (UniverseTotal.{u}) where
  toCategory := inferInstanceAs (Category (UniverseTotal.{u}))
  inv {X Y} f := by
    cases f with
    | mk g => exact CategoryTheory.Sigma.SigmaHom.mk (Groupoid.inv g)
  inv_comp := by
    intro X Y f
    cases f with
    | mk g => exact congrArg CategoryTheory.Sigma.SigmaHom.mk (Groupoid.inv_comp g)
  comp_inv := by
    intro X Y f
    cases f with
    | mk g => exact congrArg CategoryTheory.Sigma.SigmaHom.mk (Groupoid.comp_inv g)

/-- A concrete small groupoid with one object and two automorphisms: the
permutation group of Bool, viewed as a one-object groupoid. -/
def twoAutomorphismGroupoid : Grpd.{0, 0} :=
  Grpd.of (SingleObj (Equiv.Perm Bool))

/-- The object of `Σ X : U. El(X)` carrying the two distinct identity proofs. -/
def counterexampleObject : UniverseTotal.{0} :=
  ⟨twoAutomorphismGroupoid, SingleObj.star (Equiv.Perm Bool)⟩

/-- Reflexivity at the chosen counterexample object. -/
def counterexampleRefl : counterexampleObject ⟶ counterexampleObject :=
  𝟙 counterexampleObject

/-- The transposition automorphism, regarded as a second proof of reflexive
identity at the chosen object of the total universe family. -/
def counterexampleLoop : counterexampleObject ⟶ counterexampleObject :=
  CategoryTheory.Sigma.SigmaHom.mk (Equiv.swap false true)

end HofmannStreicher1994


