-- Prove2me | Definitions.Def_AlgebraicGeometry_RigKerDualNumberBaseTransport
-- name    : AlgebraicGeometry_RigKerDualNumberBaseTransport
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/d45955c5-c62a-5d2c-be94-902b07be2c89
-- title:
--   Base transport of the dual-number rigidified Picard kernel
-- statement:
--   Throughout, $c\colon C\to\operatorname{Spec}R$ is a scheme over an affine base equipped with $\varepsilon$, a morphism over $\operatorname{Spec}R$ from $\operatorname{Spec}R$ to $C$ (a section of $c$), $R\to R'$ is a ring map, and $B$ is an $R'$-algebra regarded also as an $R$-algebra through the tower. A rigidified line bundle on a base $t\colon T\to\operatorname{Spec}R$ is, in the sense used here, a module $L$ on $C\times_{\operatorname{Spec}R}T$ together with the local triviality property `Scheme.Modules.IsInvertible` and a nonempty set of isomorphisms between the pullback of $L$ along the section induced by $\varepsilon$ and the unit module on $T$; `pullbackAlong` transports such data along a morphism $\psi$ with $\psi\circ$-compatibility over $\operatorname{Spec}R$, via the induced map of fibre products. The first group of declarations records the pasting calculus for this operation: composition of Spec of a tower of algebra maps; the morphism `idOver` over an equality of structure morphisms, whose underlying map is the identity; triviality of the induced map on fibre products when the underlying map is the identity; isomorphisms comparing a double `pullbackAlong` with the pullback along the composite, a `pullbackAlong` whose underlying map is the identity with the original bundle, a round trip along `idOver h` and `idOver h.symm`, two morphisms with equal underlying maps, the image of the unit bundle with the unit bundle, and functoriality on isomorphisms. For the base-change comparison $\kappa$ of the two fibre products, the companions `ofR_pullbackAlong_iso`, `ofR_unit_iso`, `ofR_mapIso` and `toR_mapIso` are supplied alongside the previously available `toR` versions. Two tower lemmas note that the reduction $B[\epsilon]\to B$ has the same underlying ring map over $R$ and over $R'$, and that Spec of $R'\to B[\epsilon]$ followed by Spec of $R\to R'$ is Spec of $R\to B[\epsilon]$.
--
--   The main construction is `baseTransport`, a bijection between `RigKerDualNumber c ε B` and `RigKerDualNumber (baseChange R c R') (sectionBaseChange R' ε) B`. Members of the carrier are rigidified line bundles on the base $\operatorname{Spec}B[\epsilon]\to\operatorname{Spec}R$ whose pullback along the dual-number reduction admits an isomorphism to the unit bundle, and the kernel itself is the quotient by the relation of having isomorphic underlying modules. The forward map sends such a bundle to its image under $\kappa$ after pullback along `idOver` for the tower equality, `baseTransportCarrierIso` exhibiting the required trivialisation of its reduction; the inverse uses $\kappa^{-1}$ and the opposite tower equality, with `baseTransportCarrierInvIso`. Two further statements record that `baseTransport` carries `RigKerDualNumber.mul`, the operation induced by tensor product, to `RigKerDualNumber.mul`, and the unit class to the unit class; multiplicativity and unitality are thus asserted for the bare operations, no group structure on these quotients being introduced here.
--
--   **Relation to Mathlib.** Mathlib supplies the dual numbers, `TrivSqZeroExt.fstHom`, and pullback of sheaves of modules along a morphism of schemes, all used here; the rigidified line bundles, the kernel `RigKerDualNumber` of the reduction map on rigidified Picard classes, and their behaviour under base change of the base ring are the project's own notions.
--
--   **Where it is used.** The rigidified relative Picard machinery of this part of the development underlies the construction and study of Jacobians and their Néron models; the dual-number kernel plays the role of the tangent space of the relative Picard functor, and the bijection constructed here identifies it for a base ring with that for a base change, for instance when an integral model is compared with its generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RigKerDualNumberBaseTransport.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra

noncomputable section

namespace AlgebraicGeometry.RelPicard.BaseTransport

variable {R : Type u} [CommRing R]

theorem specMap_comp_specMap (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T] :
    specMap S T ≫ specMap R S = specMap R T := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R S T]

def idOver {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) : SchemeHomOver t₂ t₁ :=
  ⟨𝟙 T, (Category.id_comp t₁).trans h⟩

@[simp] theorem idOver_coe {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) :
    (idOver h).1 = 𝟙 T := rfl

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem baseChangeSnd_eq_id {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (φ : SchemeHomOver t t)
    (hφ : φ.1 = 𝟙 T) : baseChangeSnd c φ = 𝟙 (pullback c t) := by
  obtain ⟨f, hf⟩ := φ
  cases hφ
  exact baseChangeSnd_id c t

namespace RigidifiedLineBundle

variable {c ε}

def pullbackAlong_pullbackAlong_iso {T T' T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (φ : SchemeHomOver t' t) (ψ : SchemeHomOver t'' t') :
    ((M.pullbackAlong φ).pullbackAlong ψ).L ≅ (M.pullbackAlong (postComp φ ψ)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) (baseChangeSnd c φ)).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c φ ψ)).app M.L

def pullbackAlong_iso_of_coe_eq_id {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (φ : SchemeHomOver t t) (hφ : φ.1 = 𝟙 T) :
    (M.pullbackAlong φ).L ≅ M.L :=
  (Scheme.Modules.pullbackCongr (baseChangeSnd_eq_id c φ hφ)).app M.L ≪≫
    (Scheme.Modules.pullbackId _).app M.L

def pullbackAlong_idOver_idOver_iso {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (M : RigidifiedLineBundle c ε t₁) :
    (((M.pullbackAlong (idOver h)).pullbackAlong (idOver h.symm))).L ≅ M.L :=
  pullbackAlong_pullbackAlong_iso M _ _ ≪≫
    pullbackAlong_iso_of_coe_eq_id M _ (Category.id_comp _)

def unit_pullbackAlong_iso {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    ((RigidifiedLineBundle.unit (c := c) (ε := ε) t).pullbackAlong ψ).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) t').L :=
  Scheme.Modules.pullbackUnitIso (baseChangeSnd c ψ)

def pullbackAlong_mapIso {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {M M' : RigidifiedLineBundle c ε t}
    (ψ : SchemeHomOver t' t) (e : M.L ≅ M'.L) : (M.pullbackAlong ψ).L ≅ (M'.pullbackAlong ψ).L :=
  (Scheme.Modules.pullback (baseChangeSnd c ψ)).mapIso e

end RigidifiedLineBundle

namespace BaseChange

variable (R' : Type u) [CommRing R'] [Algebra R R']

def ofR_pullbackAlong_iso {T T'' : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    {t'' : T'' ⟶ Spec (CommRingCat.of R')} (ψ : SchemeHomOver t'' t')
    (M : RigidifiedLineBundle c ε (t' ≫ specMap R R')) :
    ((BaseChange.ofR c ε R' M).pullbackAlong ψ).L ≅
      (BaseChange.ofR c ε R' (M.pullbackAlong (BaseChange.overR R' ψ))).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd (baseChange R c R') ψ) (BaseChange.κ c R' t').hom).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (BaseChange.baseChangeSnd_κ_hom c R' ψ)).app M.L ≪≫
    ((Scheme.Modules.pullbackComp (BaseChange.κ c R' t'').hom (baseChangeSnd c (BaseChange.overR R' ψ))).app
      M.L).symm

def ofR_unit_iso {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (BaseChange.ofR c ε R' (RigidifiedLineBundle.unit (t' ≫ specMap R R'))).L ≅
      (RigidifiedLineBundle.unit (c := baseChange R c R') (ε := sectionBaseChange R' ε) t').L :=
  Scheme.Modules.pullbackUnitIso (BaseChange.κ c R' t').hom

def ofR_mapIso {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    {M M' : RigidifiedLineBundle c ε (t' ≫ specMap R R')} (e : M.L ≅ M'.L) :
    (BaseChange.ofR c ε R' M).L ≅ (BaseChange.ofR c ε R' M').L :=
  (Scheme.Modules.pullback (BaseChange.κ c R' t').hom).mapIso e

def toR_mapIso {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    {M M' : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t'} (e : M.L ≅ M'.L) :
    (BaseChange.toR c ε R' M).L ≅ (BaseChange.toR c ε R' M').L :=
  (Scheme.Modules.pullback (BaseChange.κ c R' t').inv).mapIso e

end BaseChange

section DualNumberTower

variable (R' : Type u) [CommRing R'] [Algebra R R'] (B : Type u) [CommRing B] [Algebra R' B] [Algebra R B]
  [IsScalarTower R R' B]

example : IsScalarTower R R' (DualNumber B) := inferInstance

omit [Algebra R R'] [IsScalarTower R R' B] in

theorem fstHom_toRingHom_eq :
    (TrivSqZeroExt.fstHom R B B).toRingHom = (TrivSqZeroExt.fstHom R' B B).toRingHom := rfl

theorem specMap_dualNumber_comp : specMap R' (DualNumber B) ≫ specMap R R' = specMap R (DualNumber B) :=
  specMap_comp_specMap R R' (DualNumber B)

end DualNumberTower

end AlgebraicGeometry.RelPicard.BaseTransport

namespace AlgebraicGeometry.RelPicard.RigKerDualNumber

open AlgebraicGeometry.RelPicard.BaseTransport MonoidalCategory

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
  {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
  (B : Type u) [CommRing B] [Algebra R' B] [Algebra R B] [IsScalarTower R R' B]

theorem tower_dualNumber :
    Scheme.TwoAffineOpenCover.specMap R (DualNumber B) = specMap R' (DualNumber B) ≫ specMap R R' :=
  (specMap_comp_specMap R R' (DualNumber B)).symm

theorem tower_base : Scheme.TwoAffineOpenCover.specMap R B = specMap R' B ≫ specMap R R' :=
  (specMap_comp_specMap R R' B).symm

variable {c ε} in

def _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle.pullbackAlong_congr_hom
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (φ ψ : SchemeHomOver t' t) (h : φ.1 = ψ.1) :
    (M.pullbackAlong φ).L ≅ (M.pullbackAlong ψ).L :=
  (Scheme.Modules.pullbackCongr (congrArg (baseChangeSnd c) (Subtype.ext h))).app M.L

def baseTransportCarrierIso (M : RigKerDualNumber.Carrier c ε B) :
    ((BaseChange.ofR c ε R' (M.1.pullbackAlong (idOver (tower_dualNumber R' B)))).pullbackAlong
        (dualNumberReductionOver R' B)).L ≅
      (RigidifiedLineBundle.unit (c := baseChange R c R') (ε := sectionBaseChange R' ε)
        (Scheme.TwoAffineOpenCover.specMap R' B)).L :=
  BaseChange.ofR_pullbackAlong_iso c ε R' (dualNumberReductionOver R' B) _ ≪≫
    BaseChange.ofR_mapIso c ε R'
      (RigidifiedLineBundle.pullbackAlong_pullbackAlong_iso M.1 _ _ ≪≫
        RigidifiedLineBundle.pullbackAlong_congr_hom M.1 _
          (postComp (dualNumberReductionOver R B) (idOver (tower_base R' B))) (by simp [postComp, idOver, BaseChange.overR]; rfl) ≪≫
        (RigidifiedLineBundle.pullbackAlong_pullbackAlong_iso M.1 _ _).symm ≪≫
        RigidifiedLineBundle.pullbackAlong_mapIso (idOver (tower_base R' B)) M.2.some ≪≫
        RigidifiedLineBundle.unit_pullbackAlong_iso (idOver (tower_base R' B))) ≪≫
    BaseChange.ofR_unit_iso c ε R' (specMap R' B)

def baseTransportCarrier (M : RigKerDualNumber.Carrier c ε B) :
    RigKerDualNumber.Carrier (baseChange R c R') (sectionBaseChange R' ε) B :=
  ⟨BaseChange.ofR c ε R' (M.1.pullbackAlong (idOver (tower_dualNumber R' B))),
    ⟨baseTransportCarrierIso R' c ε B M⟩⟩

def baseTransportCarrierInvIso
    (M' : RigKerDualNumber.Carrier (baseChange R c R') (sectionBaseChange R' ε) B) :
    (((BaseChange.toR c ε R' M'.1).pullbackAlong (idOver (tower_dualNumber R' B).symm)).pullbackAlong
        (dualNumberReductionOver R B)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R B)).L :=
  RigidifiedLineBundle.pullbackAlong_pullbackAlong_iso _ _ _ ≪≫
    RigidifiedLineBundle.pullbackAlong_congr_hom _ _
      (postComp (BaseChange.overR R' (dualNumberReductionOver R' B)) (idOver (tower_base R' B).symm))
      (by simp [postComp, idOver, BaseChange.overR]; rfl) ≪≫
    (RigidifiedLineBundle.pullbackAlong_pullbackAlong_iso _ _ _).symm ≪≫
    RigidifiedLineBundle.pullbackAlong_mapIso (idOver (tower_base R' B).symm)
      (BaseChange.toR_pullbackAlong_iso c ε R' (dualNumberReductionOver R' B) M'.1 ≪≫
        BaseChange.toR_mapIso c ε R' M'.2.some ≪≫
        BaseChange.toR_unit_iso c ε R' _) ≪≫
    RigidifiedLineBundle.unit_pullbackAlong_iso (idOver (tower_base R' B).symm)

def baseTransportCarrierInv
    (M' : RigKerDualNumber.Carrier (baseChange R c R') (sectionBaseChange R' ε) B) :
    RigKerDualNumber.Carrier c ε B :=
  ⟨(BaseChange.toR c ε R' M'.1).pullbackAlong (idOver (tower_dualNumber R' B).symm),
    ⟨baseTransportCarrierInvIso R' c ε B M'⟩⟩

def baseTransport :
    RigKerDualNumber c ε B ≃ RigKerDualNumber (baseChange R c R') (sectionBaseChange R' ε) B where
  toFun := Quotient.map (baseTransportCarrier R' c ε B)
    (fun M N (h : Nonempty (M.1.L ≅ N.1.L)) =>
      (⟨BaseChange.ofR_mapIso c ε R' (RigidifiedLineBundle.pullbackAlong_mapIso _ h.some)⟩ :
        Nonempty ((baseTransportCarrier R' c ε B M).1.L ≅ (baseTransportCarrier R' c ε B N).1.L)))
  invFun := Quotient.map (baseTransportCarrierInv R' c ε B)
    (fun M N (h : Nonempty (M.1.L ≅ N.1.L)) =>
      (⟨RigidifiedLineBundle.pullbackAlong_mapIso _ (BaseChange.toR_mapIso c ε R' h.some)⟩ :
        Nonempty ((baseTransportCarrierInv R' c ε B M).1.L ≅ (baseTransportCarrierInv R' c ε B N).1.L)))
  left_inv := fun x => by
    induction x using Quotient.ind with
    | _ M =>
      exact Quotient.sound
        (⟨RigidifiedLineBundle.pullbackAlong_mapIso _ (BaseChange.toR_ofR_iso c ε R' _) ≪≫
          RigidifiedLineBundle.pullbackAlong_idOver_idOver_iso (tower_dualNumber R' B) M.1⟩ :
          Nonempty (_ ≅ M.1.L))
  right_inv := fun x => by
    induction x using Quotient.ind with
    | _ M' =>
      exact Quotient.sound
        (⟨BaseChange.ofR_mapIso c ε R'
            (RigidifiedLineBundle.pullbackAlong_idOver_idOver_iso (tower_dualNumber R' B).symm _) ≪≫
          BaseChange.ofR_toR_iso c ε R' M'.1⟩ : Nonempty (_ ≅ M'.1.L))

@[simp] theorem baseTransport_mk (M : RigKerDualNumber.Carrier c ε B) :
    baseTransport R' c ε B (Quotient.mk _ M) = Quotient.mk _ (baseTransportCarrier R' c ε B M) := rfl

@[simp] theorem baseTransport_symm_mk
    (M' : RigKerDualNumber.Carrier (baseChange R c R') (sectionBaseChange R' ε) B) :
    (baseTransport R' c ε B).symm (Quotient.mk _ M') = Quotient.mk _ (baseTransportCarrierInv R' c ε B M') :=
  rfl

theorem baseTransport_mul (x y : RigKerDualNumber c ε B) :
    baseTransport R' c ε B (RigKerDualNumber.mul c ε B x y) =
      RigKerDualNumber.mul (baseChange R c R') (sectionBaseChange R' ε) B
        (baseTransport R' c ε B x) (baseTransport R' c ε B y) := by
  induction x using Quotient.ind with
  | _ M =>
    induction y using Quotient.ind with
    | _ N =>
      refine Quotient.sound (?_ : Nonempty (_ ≅ _))
      exact ⟨(Scheme.Modules.pullback _).mapIso (Scheme.Modules.pullbackTensorObjIso _ M.1.L N.1.L) ≪≫
        Scheme.Modules.pullbackTensorObjIso _ _ _⟩

theorem baseTransport_one :
    baseTransport R' c ε B (RigKerDualNumber.one c ε B) =
      RigKerDualNumber.one (baseChange R c R') (sectionBaseChange R' ε) B := by
  refine Quotient.sound (?_ : Nonempty (_ ≅ _))
  exact ⟨BaseChange.ofR_mapIso c ε R' (RigidifiedLineBundle.unit_pullbackAlong_iso _) ≪≫
    BaseChange.ofR_unit_iso c ε R' _⟩

end AlgebraicGeometry.RelPicard.RigKerDualNumber


