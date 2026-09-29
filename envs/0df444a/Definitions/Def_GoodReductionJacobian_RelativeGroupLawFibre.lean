-- Prove2me | Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
-- name    : GoodReductionJacobian_RelativeGroupLawFibre
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/be5f96c3-1343-50dc-87f6-0ebf52578d17
-- title:
--   Fibres of a relative group law over residue fields
-- statement:
--   Fix a commutative ring $R$, a scheme $A$ and a morphism $f \colon A \to \operatorname{Spec} R$, and a point $s$ of $\operatorname{Spec} R$. The module first fixes notation for the fibre of $f$ at $s$: `baseResidueField` is the residue field $\kappa(s)$ of $\operatorname{Spec} R$ at $s$ (Mathlib's `residueField`), `basePointInclusion` is the canonical morphism $\iota_s \colon \operatorname{Spec}\kappa(s) \to \operatorname{Spec} R$ (`fromSpecResidueField`), `fibreScheme` is the fibre product $A_s = A \times_{\operatorname{Spec} R} \operatorname{Spec}\kappa(s)$ and `fibreStr` is its second projection $A_s \to \operatorname{Spec}\kappa(s)$. Two lemmas record that these agree, definitionally, with Mathlib's `fiber` and `fiberToSpecResidueField` of $f$ at $s$.
--
--   For a test scheme $T$ with a structure morphism $t' \colon T \to \operatorname{Spec}\kappa(s)$, the $T$-points of $A_s$ over $t'$ — elements of `SchemeHomOver t' (fibreStr f s)`, that is, morphisms $T \to A_s$ whose composite with the projection is $t'$ — correspond to $T$-points of $A$ over $t'$ followed by $\iota_s$. The maps `fibrePointToBase` (compose with the first projection) and `fibrePointOfBase` (the morphism induced by the universal property of the fibre product) are mutually inverse, giving the bijection `fibrePointEquiv`; `fibrePointToBase_schemeHomOverComp` states that `fibrePointToBase` commutes with precomposition by a morphism $\psi \colon T' \to T$ over the base.
--
--   The main construction `RelativeGroupLaw.fibre` transports a relative group law $G$ on $f$, in the project's sense — a choice, for every test morphism $t$ to $\operatorname{Spec} R$, of a group structure (multiplication, unit, inverse, with associativity, unit laws and left inverse as fields) on the set of $T$-points of $A$ over $t$, with multiplication natural in the test object — across this bijection, producing a relative group law on $\mathrm{fibreStr}\, f\, s$ over $\kappa(s)$. Three unfolding lemmas give its multiplication, unit and inverse as the conjugates of those of $G$ by `fibrePointToBase` and `fibrePointOfBase`.
--
--   **Relation to Mathlib.** `fibreScheme` and `fibreStr` are definitionally Mathlib's `fiber` and `fiberToSpecResidueField` of a scheme morphism at a point, repackaged as the pullback along `fromSpecResidueField`; the lemmas `fibreScheme_eq_fiber` and `fibreStr_eq_fiberToSpecResidueField` record the identification. The notion `RelativeGroupLaw` transported here is the project's own functor-of-points formulation of a relative group structure, not Mathlib's group-object API.
--
--   **Where it is used.** The construction lets statements about group laws over a field — for instance properties of multiplication by $n$ on an abelian variety — be applied fibrewise to a group scheme over a general base, as needed when studying the reduction of Jacobians and Néron models in the Frey-curve part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_RelativeGroupLawFibre.lean

import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev baseResidueField (s : (Spec (CommRingCat.of R) : Scheme.{u})) : Type u :=
  (Spec (CommRingCat.of R)).residueField s

abbrev basePointInclusion (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    Spec (CommRingCat.of (baseResidueField s)) ⟶ Spec (CommRingCat.of R) :=
  (Spec (CommRingCat.of R)).fromSpecResidueField s

abbrev fibreScheme (f : A ⟶ Spec (CommRingCat.of R)) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    Scheme.{u} :=
  pullback f (basePointInclusion s)

abbrev fibreStr (f : A ⟶ Spec (CommRingCat.of R)) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    fibreScheme f s ⟶ Spec (CommRingCat.of (baseResidueField s)) :=
  pullback.snd f (basePointInclusion s)

variable (s : (Spec (CommRingCat.of R) : Scheme.{u}))

theorem fibreScheme_eq_fiber : fibreScheme f s = f.fiber s := rfl

theorem fibreStr_eq_fiberToSpecResidueField :
    fibreStr f s = f.fiberToSpecResidueField s := rfl

def fibrePointToBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (x : SchemeHomOver t' (fibreStr f s)) : SchemeHomOver (t' ≫ basePointInclusion s) f :=
  ⟨x.1 ≫ pullback.fst f (basePointInclusion s), by
    rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩

def fibrePointOfBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (y : SchemeHomOver (t' ≫ basePointInclusion s) f) : SchemeHomOver t' (fibreStr f s) :=
  ⟨pullback.lift y.1 t' y.2, pullback.lift_snd _ _ _⟩

@[simp]
theorem fibrePointToBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (x : SchemeHomOver t' (fibreStr f s)) :
    (fibrePointToBase s x).1 = x.1 ≫ pullback.fst f (basePointInclusion s) :=
  rfl

@[simp]
theorem fibrePointOfBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (y : SchemeHomOver (t' ≫ basePointInclusion s) f) :
    (fibrePointOfBase s y).1 = pullback.lift y.1 t' y.2 :=
  rfl

@[simp]
theorem fibrePointToBase_ofBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (y : SchemeHomOver (t' ≫ basePointInclusion s) f) :
    fibrePointToBase s (fibrePointOfBase s y) = y :=
  Subtype.ext (pullback.lift_fst _ _ _)

@[simp]
theorem fibrePointOfBase_toBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (x : SchemeHomOver t' (fibreStr f s)) :
    fibrePointOfBase s (fibrePointToBase s x) = x := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [fibrePointOfBase_coe, pullback.lift_fst, fibrePointToBase_coe]
  · rw [fibrePointOfBase_coe, pullback.lift_snd]
    exact x.2.symm

def fibrePointEquiv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) :
    SchemeHomOver t' (fibreStr f s) ≃ SchemeHomOver (t' ≫ basePointInclusion s) f where
  toFun := fibrePointToBase s
  invFun := fibrePointOfBase s
  left_inv := fibrePointOfBase_toBase s
  right_inv := fibrePointToBase_ofBase s

theorem fibrePointToBase_schemeHomOverComp {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of (baseResidueField s)))
    (t' : T' ⟶ Spec (CommRingCat.of (baseResidueField s))) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t (fibreStr f s)) :
    fibrePointToBase s (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (fibrePointToBase s x) :=
  Subtype.ext (Category.assoc _ _ _)

def fibre (G : RelativeGroupLaw R f) : RelativeGroupLaw (baseResidueField s) (fibreStr f s) where
  mul t' x y := fibrePointOfBase s (G.mul _ (fibrePointToBase s x) (fibrePointToBase s y))
  one t' := fibrePointOfBase s (G.one _)
  inv t' x := fibrePointOfBase s (G.inv _ (fibrePointToBase s x))
  mul_assoc t' x y z := by
    simp only [fibrePointToBase_ofBase, G.mul_assoc]
  one_mul t' x := by
    simp only [fibrePointToBase_ofBase, G.one_mul, fibrePointOfBase_toBase]
  mul_one t' x := by
    simp only [fibrePointToBase_ofBase, G.mul_one, fibrePointOfBase_toBase]
  inv_mul_cancel t' x := by
    simp only [fibrePointToBase_ofBase, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [schemeHomOverComp_coe, fibrePointOfBase_coe, fibrePointOfBase_coe, Category.assoc, pullback.lift_fst,
        pullback.lift_fst]
      have h := congrArg Subtype.val
        (G.mul_natural (t ≫ basePointInclusion s) (t' ≫ basePointInclusion s) ψ
          (by rw [← Category.assoc, hψ]) (fibrePointToBase s x) (fibrePointToBase s y))
      rw [schemeHomOverComp_coe] at h
      rw [h, ← fibrePointToBase_schemeHomOverComp, ← fibrePointToBase_schemeHomOverComp]
    · rw [schemeHomOverComp_coe, fibrePointOfBase_coe, fibrePointOfBase_coe, Category.assoc, pullback.lift_snd,
        pullback.lift_snd]
      exact hψ

@[simp]
theorem fibre_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) (x y : SchemeHomOver t' (fibreStr f s)) :
    (G.fibre s).mul t' x y = fibrePointOfBase s (G.mul _ (fibrePointToBase s x) (fibrePointToBase s y)) :=
  rfl

@[simp]
theorem fibre_one (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) :
    (G.fibre s).one t' = fibrePointOfBase s (G.one _) :=
  rfl

@[simp]
theorem fibre_inv (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) (x : SchemeHomOver t' (fibreStr f s)) :
    (G.fibre s).inv t' x = fibrePointOfBase s (G.inv _ (fibrePointToBase s x)) :=
  rfl

end RelativeGroupLaw
end GoodReductionJacobian

end


