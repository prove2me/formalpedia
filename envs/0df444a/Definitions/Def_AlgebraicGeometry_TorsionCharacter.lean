-- Prove2me | Definitions.Def_AlgebraicGeometry_TorsionCharacter
-- name    : AlgebraicGeometry_TorsionCharacter
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/6930bb95-a024-56ce-9572-0109c21f4fe5
-- title:
--   Characters of relative n-torsion as a functor-of-points structure
-- statement:
--   The setting is a commutative ring $S$, a scheme morphism $f\colon A \to \operatorname{Spec} S$ carrying a relative group law `L : RelativeGroupLaw S f`, a natural number $n$, and a morphism $\iota\colon \operatorname{Spec} R \to \operatorname{Spec} S$ with $R$ a commutative ring, thought of as an affine base change of $S$. Recall that a `RelativeGroupLaw` equips, for every scheme $T$ and every morphism $t\colon T \to \operatorname{Spec} S$, the set `SchemeHomOver t f` of morphisms $T \to A$ over $\operatorname{Spec} S$ with a group structure, natural in $(T,t)$; `L.IsTorsionPoint t n x` is the condition `L.nsmul t n x = L.one t`, where `nsmul` is the $n$-fold iterate of `L.mul` starting from the unit section, so it says that $x$ is killed by $n$ in that group.
--
--   The structure `TorsionCharacter L n ι` packages a character of the $n$-torsion over $R$ in functor-of-points form. Its field `val` assigns, to each commutative ring $T$, each morphism $\kappa\colon \operatorname{Spec} T \to \operatorname{Spec} R$, each point $x$ of $A$ over $\kappa$ followed by $\iota$, and each proof that $x$ is $n$-torsion for `L`, a unit $\chi(x) \in T^{\times}$. The field `val_mul` asserts multiplicativity: whenever $x$, $y$ and their product `L.mul` are $n$-torsion, the value at the product is the product of the values. The field `val_natural` expresses naturality in the test ring relationally rather than by transport of structure: given ring homomorphisms $\varphi\colon T \to T'$ and morphisms $\kappa$, $\kappa'$ with $\operatorname{Spec}\varphi$ followed by $\kappa$ equal to $\kappa'$, and $n$-torsion points $x$ over $\kappa$ and $x'$ over $\kappa'$ whose underlying scheme morphisms satisfy $x' = \operatorname{Spec}\varphi$ followed by $x$, the value at $x'$ is the image of the value at $x$ under the induced map $T^{\times} \to T'^{\times}$. The accompanying extensionality lemma `ext` states that two such characters with equal `val` fields coincide. Values are taken in the full unit group, not in $n$-th roots of unity, and no finiteness, flatness or representability hypothesis on the $n$-torsion is imposed.
--
--   **Relation to Mathlib.** Mathlib has group objects in a monoidal category and Hopf-algebraic notions, but no functor-of-points relative group law over an affine base of this shape and no corresponding notion of character of the $n$-torsion; both `RelativeGroupLaw` and `TorsionCharacter` are the project's own, phrased in terms of the subtype `SchemeHomOver` of morphisms over a fixed base morphism.
--
--   **Where it is used.** This module supplies the vocabulary in which the $R$-points of the Cartier dual of the $n$-torsion of a relative group law are spoken about: once the $n$-torsion is represented by a finite free Hopf algebra, such characters correspond to homomorphisms into $\mathbb{G}_m$. It feeds the treatment of torsion on Jacobians and abelian schemes with good reduction used in the analysis of the Galois representations attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TorsionCharacter.lean

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace GoodReductionJacobian.RelativeGroupLaw

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

structure TorsionCharacter (L : RelativeGroupLaw S f) (n : ℕ) {R : Type u} [CommRing R]
    (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) where

  val : ∀ (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver (κ ≫ ι) f), L.IsTorsionPoint (κ ≫ ι) n x → Tˣ

  val_mul : ∀ (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) n x) (hy : L.IsTorsionPoint (κ ≫ ι) n y)
    (hxy : L.IsTorsionPoint (κ ≫ ι) n (L.mul (κ ≫ ι) x y)),
    val T κ (L.mul (κ ≫ ι) x y) hxy = val T κ x hx * val T κ y hy

  val_natural : ∀ (T T' : Type u) [CommRing T] [CommRing T']
    (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R)) (κ' : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R))
    (φ : T →+* T'), Spec.map (CommRingCat.ofHom φ) ≫ κ = κ' →
    ∀ (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) n x)
      (x' : SchemeHomOver (κ' ≫ ι) f) (hx' : L.IsTorsionPoint (κ' ≫ ι) n x'),
      x'.1 = Spec.map (CommRingCat.ofHom φ) ≫ x.1 →
      val T' κ' x' hx' = Units.map (φ : T →* T') (val T κ x hx)

namespace TorsionCharacter

variable {L : RelativeGroupLaw S f} {n : ℕ} {R R' : Type u} [CommRing R] [CommRing R']
  {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)} {ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)}

@[ext] theorem ext {χ χ' : TorsionCharacter L n ι} (h : χ.val = χ'.val) : χ = χ' := by
  cases χ; cases χ'; cases h; rfl

end TorsionCharacter

end GoodReductionJacobian.RelativeGroupLaw

end


