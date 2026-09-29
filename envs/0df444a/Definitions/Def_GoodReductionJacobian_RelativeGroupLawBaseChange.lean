-- Prove2me | Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
-- name    : GoodReductionJacobian_RelativeGroupLawBaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/65807b91-7c61-5993-af9b-e83d9985eda0
-- title:
--   Base change of a relative group law; generic fibre
-- statement:
--   Fix a commutative ring $R$, a scheme $A$ and a structure morphism $f\colon A\to\operatorname{Spec}R$, and let $G$ be a `RelativeGroupLaw R f`: the project's functor-of-points group law, i.e. operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on the sets $\mathrm{SchemeHomOver}\,t\,f=\{\varphi\colon T\to A\mid \varphi\circ f=t\}$ for every $t\colon T\to\operatorname{Spec}R$, satisfying associativity, unit and left-inverse laws together with naturality of $\mathrm{mul}$ in the test object $T$. For a morphism $\iota\colon\operatorname{Spec}R'\to\operatorname{Spec}R$ the abbreviations `baseChangeScheme` and `baseChangeStr` name the pullback $A\times_{\operatorname{Spec}R}\operatorname{Spec}R'$ and its second projection to $\operatorname{Spec}R'$. The pair `baseChangePointToBase` and `baseChangePointOfBase` are the mutually inverse maps $\mathrm{SchemeHomOver}\,t'\,(\text{base change})\;\leftrightarrow\;\mathrm{SchemeHomOver}\,(t'\circ\iota)\,f$, given by composing with the first projection and by the universal property of the pullback; `baseChangePointEquiv` packages them as an equivalence, with unfolding lemmas for the underlying morphisms and compatibility with reindexing along $\psi\colon T'\to T$ and with [`NeronSpecialFibreInfra.fibreRestrictAlong`](../def/AlgebraicGeometry_NeronSpecialFibreRestriction.html#L41).
--
--   `baseChange` then transports $G$ through this bijection: the product, unit and inverse of $R'$-points are defined by sending points down to $A$, applying $G$ over $t'\circ\iota$, and lifting back; the group axioms and the naturality of multiplication are verified by the round-trip identities, with naturality checked componentwise against both projections. Further lemmas record the defining equations of `baseChange`, that `baseChangePointToBase` is a homomorphism for product, unit and inverse, and that commutativity of $G$ (in the project's pointwise sense `IsCommutative`) is inherited. Finally `fibre_eq_baseChange` states that the residue-field fibre law $G.\mathrm{fibre}\,s$ is, definitionally, the base change along $(\operatorname{Spec}R).\mathrm{fromSpecResidueField}\,s$, and the `genericFibre` abbreviations specialise the construction to $\operatorname{Spec}K\to\operatorname{Spec}R$ for an $R$-algebra field $K$, the inclusion used in the Néron-model vocabulary.
--
--   **Relation to Mathlib.** The pullback of schemes and `pullback.lift` are Mathlib's; the relative group law itself is the project's own functor-of-points structure on `SchemeHomOver` rather than a Mathlib monoid object in an over-category, and its base change is constructed here by hand.
--
--   **Where it is used.** This provides the single mechanism by which the group law on a smooth $R$-scheme (a Néron model or a Jacobian with good reduction) is transported to its generic fibre over $K$, to its special fibres over residue fields, and to completions or unramified extensions, so that reduction of torsion points can be compared across fibres in the study of the Galois representations attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_RelativeGroupLawBaseChange.lean

import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_NeronSpecialFibreRestriction
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

section BaseChange

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev baseChangeScheme (f : A ⟶ Spec (CommRingCat.of R)) : Scheme.{u} :=
  pullback f ι

abbrev baseChangeStr (f : A ⟶ Spec (CommRingCat.of R)) :
    baseChangeScheme ι f ⟶ Spec (CommRingCat.of R') :=
  pullback.snd f ι

def baseChangePointToBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) : SchemeHomOver (t' ≫ ι) f :=
  ⟨x.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩

def baseChangePointOfBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) : SchemeHomOver t' (baseChangeStr ι f) :=
  ⟨pullback.lift y.1 t' y.2, pullback.lift_snd _ _ _⟩

@[simp]
theorem baseChangePointToBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) :
    (baseChangePointToBase ι x).1 = x.1 ≫ pullback.fst f ι :=
  rfl

@[simp]
theorem baseChangePointOfBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) :
    (baseChangePointOfBase ι y).1 = pullback.lift y.1 t' y.2 :=
  rfl

@[simp]
theorem baseChangePointToBase_ofBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) :
    baseChangePointToBase ι (baseChangePointOfBase ι y) = y :=
  Subtype.ext (pullback.lift_fst _ _ _)

@[simp]
theorem baseChangePointOfBase_toBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointOfBase ι (baseChangePointToBase ι x) = x := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [baseChangePointOfBase_coe, pullback.lift_fst, baseChangePointToBase_coe]
  · rw [baseChangePointOfBase_coe, pullback.lift_snd]
    exact x.2.symm

def baseChangePointEquiv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    SchemeHomOver t' (baseChangeStr ι f) ≃ SchemeHomOver (t' ≫ ι) f where
  toFun := baseChangePointToBase ι
  invFun := baseChangePointOfBase ι
  left_inv := baseChangePointOfBase_toBase ι
  right_inv := baseChangePointToBase_ofBase ι

theorem baseChangePointToBase_schemeHomOverComp {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R')) (t' : T' ⟶ Spec (CommRingCat.of R')) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t (baseChangeStr ι f)) :
    baseChangePointToBase ι (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (baseChangePointToBase ι x) :=
  Subtype.ext (Category.assoc _ _ _)

theorem baseChangePointToBase_comp_fibreRestrictAlong {B : Scheme.{u}}
    {g : B ⟶ Spec (CommRingCat.of R)} (φ : SchemeHomOver g f)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')} (x : SchemeHomOver t' (baseChangeStr ι g)) :
    baseChangePointToBase ι (NeronModelInfra.schemeHomOverComp x (fibreRestrictAlong ι f g φ)) =
      NeronModelInfra.schemeHomOverComp (baseChangePointToBase ι x) φ := by
  apply Subtype.ext
  simp only [baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
    fibreRestrictAlong_coe_comp_fst]

def baseChange (G : RelativeGroupLaw R f) : RelativeGroupLaw R' (baseChangeStr ι f) where
  mul t' x y := baseChangePointOfBase ι (G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y))
  one t' := baseChangePointOfBase ι (G.one _)
  inv t' x := baseChangePointOfBase ι (G.inv _ (baseChangePointToBase ι x))
  mul_assoc t' x y z := by
    simp only [baseChangePointToBase_ofBase, G.mul_assoc]
  one_mul t' x := by
    simp only [baseChangePointToBase_ofBase, G.one_mul, baseChangePointOfBase_toBase]
  mul_one t' x := by
    simp only [baseChangePointToBase_ofBase, G.mul_one, baseChangePointOfBase_toBase]
  inv_mul_cancel t' x := by
    simp only [baseChangePointToBase_ofBase, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [schemeHomOverComp_coe, baseChangePointOfBase_coe, baseChangePointOfBase_coe, Category.assoc,
        pullback.lift_fst, pullback.lift_fst]
      have h := congrArg Subtype.val
        (G.mul_natural (t ≫ ι) (t' ≫ ι) ψ (by rw [← Category.assoc, hψ]) (baseChangePointToBase ι x)
          (baseChangePointToBase ι y))
      rw [schemeHomOverComp_coe] at h
      rw [h, ← baseChangePointToBase_schemeHomOverComp, ← baseChangePointToBase_schemeHomOverComp]
    · rw [schemeHomOverComp_coe, baseChangePointOfBase_coe, baseChangePointOfBase_coe, Category.assoc,
        pullback.lift_snd, pullback.lift_snd]
      exact hψ

@[simp]
theorem baseChange_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' (baseChangeStr ι f)) :
    (G.baseChange ι).mul t' x y =
      baseChangePointOfBase ι (G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y)) :=
  rfl

@[simp]
theorem baseChange_one (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (G.baseChange ι).one t' = baseChangePointOfBase ι (G.one _) :=
  rfl

@[simp]
theorem baseChange_inv (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t' (baseChangeStr ι f)) :
    (G.baseChange ι).inv t' x = baseChangePointOfBase ι (G.inv _ (baseChangePointToBase ι x)) :=
  rfl

theorem baseChangePointToBase_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((G.baseChange ι).mul t' x y) =
      G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y) := by
  rw [baseChange_mul, baseChangePointToBase_ofBase]

theorem baseChangePointToBase_one (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) :
    baseChangePointToBase ι ((G.baseChange ι).one t') = G.one _ := by
  rw [baseChange_one, baseChangePointToBase_ofBase]

theorem baseChangePointToBase_inv (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((G.baseChange ι).inv t' x) = G.inv _ (baseChangePointToBase ι x) := by
  rw [baseChange_inv, baseChangePointToBase_ofBase]

theorem IsCommutative.baseChange {G : RelativeGroupLaw R f} (hG : G.IsCommutative) :
    (G.baseChange ι).IsCommutative := fun t' x y => by
  rw [baseChange_mul, baseChange_mul, hG.mul_comm]

theorem fibre_eq_baseChange (G : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    G.fibre s = G.baseChange (basePointInclusion s) :=
  rfl

end BaseChange

section GenericFibre

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev genericFibreScheme (f : A ⟶ Spec (CommRingCat.of R)) : Scheme.{u} :=
  baseChangeScheme (specGenericFibreInclusion R K) f

abbrev genericFibreStr (f : A ⟶ Spec (CommRingCat.of R)) : genericFibreScheme K f ⟶ Spec (CommRingCat.of K) :=
  baseChangeStr (specGenericFibreInclusion R K) f

abbrev genericFibre (G : RelativeGroupLaw R f) : RelativeGroupLaw K (genericFibreStr K f) :=
  G.baseChange (specGenericFibreInclusion R K)

theorem baseChangePointToBase_comp_genericFibreRestrict {B : Scheme.{u}}
    {g : B ⟶ Spec (CommRingCat.of R)} (φ : SchemeHomOver g f)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)} (x : SchemeHomOver t' (genericFibreStr K g)) :
    baseChangePointToBase (specGenericFibreInclusion R K)
        (NeronModelInfra.schemeHomOverComp x (genericFibreRestrict R K f g φ)) =
      NeronModelInfra.schemeHomOverComp (baseChangePointToBase (specGenericFibreInclusion R K) x) φ :=
  baseChangePointToBase_comp_fibreRestrictAlong (specGenericFibreInclusion R K) φ x

end GenericFibre

end RelativeGroupLaw
end GoodReductionJacobian

end


