-- Prove2me | Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
-- name    : AlgebraicGeometry_ThetaGroupLaw
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/8ac43043-03bb-5c89-89f3-9b85824803de
-- title:
--   Theta points: group law, homotheties, translation automorphisms
-- statement:
--   Three layers are set up here. First, for a scheme $X$ and $M : X.Modules$, automorphisms of the object $(X,M)$ of the co-Grothendieck construction of the pullback pseudofunctor `Scheme.Modules.fibration` are produced from geometric data: `autOfIso M e φ` takes an automorphism $e : X \cong X$ together with a trivialisation $\varphi : e^{*}M \cong M$ and returns the automorphism whose base component is $e$ and whose fibre component is $\varphi^{-1}$. The composition laws for such data are made explicit: `transIso` builds, from $e_{12} = e_1 \circ e_2$ (in diagrammatic order) and trivialisations $\varphi_1, \varphi_2$, the composite $e_{12}^{*}M \cong e_1^{*}e_2^{*}M \xrightarrow{e_1^{*}\varphi_2} e_1^{*}M \xrightarrow{\varphi_1} M$, using the pullback congruence and composition comparison isomorphisms; `reflIso` and `symmIso` do the same for an $e$ equal to the identity and for an inverse pair $e' \circ e = \mathrm{id}$. The accompanying theorems say that `autOfIso` turns these into composition, identity and inverse of automorphisms, and that `autOfIso M e` is injective in $\varphi$. Second, for $N : Y.Modules$ and a global section $r \in \Gamma(Y,\top)$, `homothety N r` is the endomorphism acting on each $\Gamma(N,U)$ by multiplication by the restriction $r|_U$ (`topRes`), with multiplicativity $r r' \mapsto$ the composite of the two homotheties and `homothetyIso` the resulting automorphism for a unit $u \in \Gamma(Y,\top)^{\times}$. Third, for a relative group law $L$ on $f : A \to \operatorname{Spec} S$, a module $\mathcal L$ on $A$ and $t : \operatorname{Spec} R \to \operatorname{Spec} S$: the translation morphisms of $A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ are shown to be compatible with the structure morphism, to be trivial at the unit point and multiplicative in the point, whence `translateIso`, an automorphism of the base change; `PtGrp L t` is the type of points $\operatorname{SchemeHomOver} t\, f$ with the group structure given by $L$. The set `ThetaPt f L 𝓛 t` of pairs (a point $x$, an isomorphism between the $x$-translate pullback of $\mathrm{pr}_1^{*}\mathcal L$ and $\mathrm{pr}_1^{*}\mathcal L$) is given multiplication, unit and inverse by `transIso`, `reflIso`, `symmIso`, together with division and natural and integer powers; `ofUnit` and `ofScalar` are the theta points over the unit point whose trivialisation is a homothety by a global unit, respectively by the image of $c \in R^{\times}$ under the ring map `baseScalarHom`. The map `toGrp`, sending a theta point to the pair consisting of its associated automorphism of the module pair (in the multiplicative opposite, to account for the order of composition in `Aut`) and its underlying point, is injective and multiplicative, and the group structure on `ThetaPt` is transported along it; `toGrpHom` is the resulting monoid homomorphism, `ptHom` its second component, `thetaGroupR` its image subgroup and `equivThetaGroupR` the induced isomorphism of `ThetaPt` with that subgroup.
--
--   **Relation to Mathlib.** Mathlib provides the ambient machinery used (pseudofunctors on bicategories and the co-Grothendieck construction, `Aut`, presheaves of modules, and fibre products of schemes); the pullback pseudofunctor `Scheme.Modules.fibration`, the relative group law `RelativeGroupLaw` and the theta points `ThetaPt` are the project's own notions, Mathlib having no theta group.
--
--   **Where it is used.** These constructions belong to the project's infrastructure for polarised abelian schemes: they realise, over a variable affine base, the group of pairs consisting of a point and a trivialisation of the translate of a module, together with its scalar subgroup and its projection to the group of points. They underlie the Riemann-form and level-pairing definitions used for the torsion of abelian schemes occurring in the study of the associated Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ThetaGroupLaw.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupAction
import Definitions.Def_AlgebraicGeometry_ThetaGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules.fibration

theorem mapComp_inv_app {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (M : Z.Modules) :
    (fibration.mapComp b.op.toLoc a.op.toLoc).inv.toNatTrans.app M = (pullbackComp a b).hom.app M := by
  simp [fibration, Pseudofunctor.comp_mapComp]
  exact Category.id_comp _

theorem mapId_inv_app (X : Scheme.{0}) (N : X.Modules) :
    (fibration.mapId ⟨Opposite.op X⟩).inv.toNatTrans.app N = (pullbackId X).inv.app N := by
  simp [fibration, Pseudofunctor.comp_mapId]
  exact Category.id_comp _

theorem pullbackCongr_hom_app_eq_eqToHom {X Y : Scheme.{0}} {a b : X ⟶ Y} (h : a = b) (M : Y.Modules) :
    (pullbackCongr h).hom.app M = eqToHom (by rw [h]) := by
  subst h; simp [pullbackCongr]

theorem pullbackCongr_inv_app_eq_eqToHom {X Y : Scheme.{0}} {a b : X ⟶ Y} (h : a = b) (M : Y.Modules) :
    (pullbackCongr h).inv.app M = eqToHom (by rw [h]) := by
  subst h; simp [pullbackCongr]

variable {X : Scheme.{0}} (M : X.Modules)

def autOfIso (e : X ≅ X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M) : Aut (RiemannForm.modulePair (A := X) M) :=
  Pseudofunctor.CoGrothendieck.isoMk (X := RiemannForm.modulePair M) (Y := RiemannForm.modulePair M) e φ.symm

@[simp] theorem autOfIso_hom_base (e : X ≅ X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    (autOfIso M e φ).hom.base = e.hom := rfl
@[simp] theorem autOfIso_hom_fiber (e : X ≅ X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    (autOfIso M e φ).hom.fiber = φ.inv := rfl

def transIso (e₁ e₂ e₁₂ : X ≅ X) (h : e₁₂.hom = e₁.hom ≫ e₂.hom)
    (φ₁ : (Scheme.Modules.pullback e₁.hom).obj M ≅ M) (φ₂ : (Scheme.Modules.pullback e₂.hom).obj M ≅ M) :
    (Scheme.Modules.pullback e₁₂.hom).obj M ≅ M :=
  (pullbackCongr h).app M ≪≫ ((pullbackComp e₁.hom e₂.hom).app M).symm ≪≫
    (Scheme.Modules.pullback e₁.hom).mapIso φ₂ ≪≫ φ₁

theorem autOfIso_trans (e₁ e₂ e₁₂ : X ≅ X) (h : e₁₂.hom = e₁.hom ≫ e₂.hom)
    (φ₁ : (Scheme.Modules.pullback e₁.hom).obj M ≅ M) (φ₂ : (Scheme.Modules.pullback e₂.hom).obj M ≅ M) :
    autOfIso M e₁₂ (transIso M e₁ e₂ e₁₂ h φ₁ φ₂) = autOfIso M e₁ φ₁ ≪≫ autOfIso M e₂ φ₂ := by
  apply Iso.ext
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ h ?_
  simp only [Iso.trans_hom, Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber, autOfIso_hom_fiber,
    autOfIso_hom_base, RiemannForm.modulePair_fiber, fibration_map_toFunctor, mapComp_inv_app]
  simp only [transIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom, Category.assoc,
    pullbackCongr_inv_app_eq_eqToHom]
  rfl

def reflIso (e : X ≅ X) (h : e.hom = 𝟙 X) : (Scheme.Modules.pullback e.hom).obj M ≅ M :=
  (pullbackCongr h).app M ≪≫ (pullbackId X).app M

theorem autOfIso_refl (e : X ≅ X) (h : e.hom = 𝟙 X) : autOfIso M e (reflIso M e h) = Iso.refl _ := by
  apply Iso.ext
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ h ?_
  simp only [Iso.refl_hom, Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber, autOfIso_hom_fiber,
    RiemannForm.modulePair_fiber, RiemannForm.modulePair_base, mapId_inv_app]
  simp only [reflIso, Iso.trans_inv, Iso.app_inv, pullbackCongr_inv_app_eq_eqToHom]
  rfl

def symmIso (e e' : X ≅ X) (h : e'.hom ≫ e.hom = 𝟙 X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    (Scheme.Modules.pullback e'.hom).obj M ≅ M :=
  ((Scheme.Modules.pullback e'.hom).mapIso φ).symm ≪≫ (pullbackComp e'.hom e.hom).app M ≪≫
    (pullbackCongr h).app M ≪≫ (pullbackId X).app M

theorem transIso_symmIso (e e' : X ≅ X) (h : e'.hom ≫ e.hom = 𝟙 X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    transIso M e' e (Iso.refl X) h.symm (symmIso M e e' h φ) φ = reflIso M (Iso.refl X) rfl := by
  ext : 1
  simp [transIso, symmIso, reflIso, pullbackCongr_hom_app_eq_eqToHom]

theorem autOfIso_symm_trans (e e' : X ≅ X) (h : e'.hom ≫ e.hom = 𝟙 X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    autOfIso M e' (symmIso M e e' h φ) ≪≫ autOfIso M e φ = Iso.refl _ := by
  rw [← autOfIso_trans M e' e (Iso.refl X) h.symm (symmIso M e e' h φ) φ, transIso_symmIso, autOfIso_refl]

theorem autOfIso_injective (e : X ≅ X) (φ φ' : (Scheme.Modules.pullback e.hom).obj M ≅ M)
    (h : autOfIso M e φ = autOfIso M e φ') : φ = φ' := by
  have h1 := Pseudofunctor.CoGrothendieck.Hom.congr (congrArg Iso.hom h)
  simp only [autOfIso_hom_fiber, autOfIso_hom_base, eqToHom_refl, Category.comp_id] at h1
  have h2 : φ.symm = φ'.symm := Iso.ext h1
  simpa using congrArg Iso.symm h2

end AlgebraicGeometry.Scheme.Modules.fibration

namespace AlgebraicGeometry.Scheme.Modules

section Homothety

variable {Y : Scheme.{0}} (N : Y.Modules)

def topRes (r : Γ(Y, ⊤)) (U : Y.Opens) : Γ(Y, U) := Y.presheaf.map (homOfLE (le_top (a := U))).op r

theorem map_topRes (r : Γ(Y, ⊤)) {U V : Y.Opens} (i : V ⟶ U) :
    Y.presheaf.map i.op (topRes r U) = topRes r V := by
  change (Y.presheaf.map _ ≫ Y.presheaf.map i.op) r = _
  rw [← Functor.map_comp]
  rfl

theorem topRes_top (r : Γ(Y, ⊤)) : topRes r ⊤ = r := by
  change Y.presheaf.map _ r = r
  have : (homOfLE (le_top (a := (⊤ : Y.Opens)))).op = 𝟙 _ := rfl
  rw [this, Y.presheaf.map_id]; rfl

theorem topRes_one (U : Y.Opens) : topRes (1 : Γ(Y, ⊤)) U = 1 := map_one _
theorem topRes_mul (r r' : Γ(Y, ⊤)) (U : Y.Opens) : topRes (r * r') U = topRes r U * topRes r' U := map_mul _ _ _

def homothety (r : Γ(Y, ⊤)) : N ⟶ N :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (DistribSMul.toAddMonoidHom Γ(N, U.unop) (topRes r U.unop))
      naturality := fun {U V} i => by
        obtain ⟨i⟩ := i
        ext s
        change topRes r (unop V) • (show Γ(N, unop V) from N.presheaf.map i.op s) =
          N.presheaf.map i.op (topRes r (unop U) • (show Γ(N, unop U) from s))
        rw [Scheme.Modules.map_smul, map_topRes] }
    (fun U a m => by
      change topRes r U.unop • ((show Γ(Y, U.unop) from a) • m) = (show Γ(Y, U.unop) from a) • (topRes r U.unop • m)
      exact smul_comm _ _ _)⟩

@[simp] theorem homothety_app (r : Γ(Y, ⊤)) (U : Y.Opens) (s : Γ(N, U)) :
    (homothety N r).app U s = topRes r U • s := rfl

theorem homothety_one : homothety N 1 = 𝟙 N := by
  ext U s
  rw [homothety_app, topRes_one, one_smul, Scheme.Modules.Hom.id_app]; rfl

theorem homothety_mul (r r' : Γ(Y, ⊤)) : homothety N (r * r') = homothety N r' ≫ homothety N r := by
  ext U s
  rw [homothety_app, topRes_mul, mul_smul, Scheme.Modules.Hom.comp_app]; rfl

def homothetyIso (u : Γ(Y, ⊤)ˣ) : N ≅ N where
  hom := homothety N (u : Γ(Y, ⊤))
  inv := homothety N (u⁻¹ : Γ(Y, ⊤)ˣ)
  hom_inv_id := by rw [← homothety_mul, Units.inv_mul, homothety_one]
  inv_hom_id := by rw [← homothety_mul, Units.mul_inv, homothety_one]

end Homothety

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Polarisation

set_option linter.unusedVariables false in

def PtGrp {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : Type := SchemeHomOver t f

instance PtGrp.instGroup {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : Group (PtGrp L t) := L.pointGroup t

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
variable {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))

def prPt : SchemeHomOver (pullback.snd f t ≫ t) f := ⟨pullback.fst f t, pullback.condition⟩

def constPtR (x : SchemeHomOver t f) : SchemeHomOver (pullback.snd f t ≫ t) f :=
  schemeHomOverComp (pullback.snd f t) rfl x

theorem constPtR_coe (x : SchemeHomOver t f) : (constPtR f t x).1 = pullback.snd f t ≫ x.1 := rfl

theorem translate_fst (x : SchemeHomOver t f) :
    translate f L t x ≫ pullback.fst f t = (L.mul _ (prPt f t) (constPtR f t x)).1 :=
  pullback.lift_fst _ _ _

theorem translate_over (x : SchemeHomOver t f) :
    translate f L t x ≫ (pullback.snd f t ≫ t) = pullback.snd f t ≫ t := by
  rw [← Category.assoc, translate_snd]

theorem constPtR_one : constPtR f t (L.one t) = L.one _ :=
  L.one_natural t _ (pullback.snd f t) rfl

theorem constPtR_mul (x y : SchemeHomOver t f) :
    constPtR f t (L.mul t x y) = L.mul _ (constPtR f t x) (constPtR f t y) :=
  L.mul_natural t _ (pullback.snd f t) rfl x y

theorem translate_one : translate f L t (L.one t) = 𝟙 (pullback f t) := by
  apply pullback.hom_ext
  · rw [translate_fst, constPtR_one, L.mul_one, Category.id_comp]; rfl
  · rw [translate_snd, Category.id_comp]

theorem translate_mul (x y : SchemeHomOver t f) :
    translate f L t (L.mul t x y) = translate f L t x ≫ translate f L t y := by
  apply pullback.hom_ext
  · rw [translate_fst, Category.assoc, translate_fst, constPtR_mul]
    have hx := translate_over f L t x
    have e1 : translate f L t x ≫ (L.mul _ (prPt f t) (constPtR f t y)).1 =
        (schemeHomOverComp (translate f L t x) hx (L.mul _ (prPt f t) (constPtR f t y))).1 := rfl
    have e2 : schemeHomOverComp (translate f L t x) hx (prPt f t) = L.mul _ (prPt f t) (constPtR f t x) :=
      Subtype.ext (translate_fst f L t x)
    have e3 : schemeHomOverComp (translate f L t x) hx (constPtR f t y) = constPtR f t y :=
      Subtype.ext (show translate f L t x ≫ (pullback.snd f t ≫ y.1) = pullback.snd f t ≫ y.1 by
        rw [← Category.assoc, translate_snd])
    rw [e1, L.mul_natural, e2, e3, L.mul_assoc]
  · rw [translate_snd, Category.assoc, translate_snd, translate_snd]

theorem translate_inv_mul (x : SchemeHomOver t f) :
    translate f L t (L.inv t x) ≫ translate f L t x = 𝟙 (pullback f t) := by
  rw [← translate_mul, L.inv_mul_cancel, translate_one]

theorem translate_mul_inv (x : SchemeHomOver t f) :
    translate f L t x ≫ translate f L t (L.inv t x) = 𝟙 (pullback f t) := by
  rw [← translate_mul, L.mul_inv_cancel, translate_one]

def translateIso (x : SchemeHomOver t f) : pullback f t ≅ pullback f t where
  hom := translate f L t x
  inv := translate f L t (L.inv t x)
  hom_inv_id := translate_mul_inv f L t x
  inv_hom_id := translate_inv_mul f L t x

@[simp] theorem translateIso_hom (x : SchemeHomOver t f) : (translateIso f L t x).hom = translate f L t x := rfl
@[simp] theorem translateIso_inv (x : SchemeHomOver t f) : (translateIso f L t x).inv = translate f L t (L.inv t x) := rfl

def baseScalarHom : R →+* Γ(pullback f t, ⊤) :=
  (pullback.snd f t).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

@[simp] theorem baseScalarHom_apply (r : R) : baseScalarHom f t r = baseScalar f t r := rfl

namespace ThetaPt

variable {f} {L} {𝓛 : A.Modules} {t}

def mul (θ θ' : ThetaPt f L 𝓛 t) : ThetaPt f L 𝓛 t where
  pt := L.mul t θ.pt θ'.pt
  iso := Scheme.Modules.fibration.transIso _ (translateIso f L t θ.pt) (translateIso f L t θ'.pt) (translateIso f L t (L.mul t θ.pt θ'.pt))
    (translate_mul f L t θ.pt θ'.pt) θ.iso θ'.iso

def one : ThetaPt f L 𝓛 t where
  pt := L.one t
  iso := Scheme.Modules.fibration.reflIso _ (translateIso f L t (L.one t)) (translate_one f L t)

def inv (θ : ThetaPt f L 𝓛 t) : ThetaPt f L 𝓛 t where
  pt := L.inv t θ.pt
  iso := Scheme.Modules.fibration.symmIso _ (translateIso f L t θ.pt) (translateIso f L t (L.inv t θ.pt)) (translate_inv_mul f L t θ.pt) θ.iso

instance : Mul (ThetaPt f L 𝓛 t) := ⟨mul⟩
instance : One (ThetaPt f L 𝓛 t) := ⟨one⟩
instance : Inv (ThetaPt f L 𝓛 t) := ⟨inv⟩
instance : Div (ThetaPt f L 𝓛 t) := ⟨fun θ θ' => θ * θ'⁻¹⟩
instance : Pow (ThetaPt f L 𝓛 t) ℕ := ⟨fun θ n => npowRec n θ⟩
instance : Pow (ThetaPt f L 𝓛 t) ℤ := ⟨fun θ n => zpowRec npowRec n θ⟩

@[simp] theorem mul_pt (θ θ' : ThetaPt f L 𝓛 t) : (θ * θ').pt = L.mul t θ.pt θ'.pt := rfl
@[simp] theorem one_pt : (1 : ThetaPt f L 𝓛 t).pt = L.one t := rfl
@[simp] theorem inv_pt (θ : ThetaPt f L 𝓛 t) : (θ⁻¹).pt = L.inv t θ.pt := rfl
theorem div_def (θ θ' : ThetaPt f L 𝓛 t) : θ / θ' = θ * θ'⁻¹ := rfl
theorem npow_zero (θ : ThetaPt f L 𝓛 t) : θ ^ (0 : ℕ) = 1 := rfl
theorem npow_succ (θ : ThetaPt f L 𝓛 t) (n : ℕ) : θ ^ (n + 1) = θ ^ n * θ := rfl
theorem zpow_ofNat (θ : ThetaPt f L 𝓛 t) (n : ℕ) : θ ^ (n : ℤ) = θ ^ n := rfl
theorem zpow_negSucc (θ : ThetaPt f L 𝓛 t) (n : ℕ) : θ ^ (Int.negSucc n) = (θ ^ (n + 1))⁻¹ := rfl

theorem mul_iso (θ θ' : ThetaPt f L 𝓛 t) : (θ * θ').iso =
    (Scheme.Modules.pullbackCongr (translate_mul f L t θ.pt θ'.pt)).app _ ≪≫
    ((Scheme.Modules.pullbackComp (translate f L t θ.pt) (translate f L t θ'.pt)).app _).symm ≪≫
    (Scheme.Modules.pullback (translate f L t θ.pt)).mapIso θ'.iso ≪≫ θ.iso := rfl

theorem one_iso : (1 : ThetaPt f L 𝓛 t).iso =
    (Scheme.Modules.pullbackCongr (translate_one f L t)).app _ ≪≫ (Scheme.Modules.pullbackId _).app _ := rfl

def ofUnit (u : Γ(pullback f t, ⊤)ˣ) : ThetaPt f L 𝓛 t where
  pt := L.one t
  iso := Scheme.Modules.fibration.reflIso _ (translateIso f L t (L.one t)) (translate_one f L t) ≪≫ Scheme.Modules.homothetyIso _ u

def ofScalar (c : Rˣ) : ThetaPt f L 𝓛 t := ofUnit (Units.map (baseScalarHom f t).toMonoidHom c)

@[simp] theorem ofUnit_pt (u : Γ(pullback f t, ⊤)ˣ) : (ofUnit u : ThetaPt f L 𝓛 t).pt = L.one t := rfl
@[simp] theorem ofScalar_pt (c : Rˣ) : (ofScalar c : ThetaPt f L 𝓛 t).pt = L.one t := rfl
theorem ofUnit_iso (u : Γ(pullback f t, ⊤)ˣ) : (ofUnit u : ThetaPt f L 𝓛 t).iso =
    ((Scheme.Modules.pullbackCongr (translate_one f L t)).app _ ≪≫ (Scheme.Modules.pullbackId _).app _) ≪≫
      Scheme.Modules.homothetyIso _ u := rfl
theorem ofScalar_eq (c : Rˣ) : (ofScalar c : ThetaPt f L 𝓛 t) = ofUnit (Units.map (baseScalarHom f t).toMonoidHom c) := rfl

def toAut (θ : ThetaPt f L 𝓛 t) :
    Aut (RiemannForm.modulePair (A := pullback f t) ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)) :=
  Scheme.Modules.fibration.autOfIso _ (translateIso f L t θ.pt) θ.iso

theorem toAut_mul (θ θ' : ThetaPt f L 𝓛 t) : toAut (θ * θ') = toAut θ ≪≫ toAut θ' :=
  Scheme.Modules.fibration.autOfIso_trans _ (translateIso f L t θ.pt) (translateIso f L t θ'.pt)
    (translateIso f L t (L.mul t θ.pt θ'.pt)) (translate_mul f L t θ.pt θ'.pt) θ.iso θ'.iso

theorem toAut_one : toAut (1 : ThetaPt f L 𝓛 t) = Iso.refl _ :=
  Scheme.Modules.fibration.autOfIso_refl _ _ _

theorem toAut_inv_trans (θ : ThetaPt f L 𝓛 t) : toAut θ⁻¹ ≪≫ toAut θ = Iso.refl _ :=
  Scheme.Modules.fibration.autOfIso_symm_trans _ (translateIso f L t θ.pt) (translateIso f L t (L.inv t θ.pt))
    (translate_inv_mul f L t θ.pt) θ.iso

def toGrp (θ : ThetaPt f L 𝓛 t) :
    (Aut (RiemannForm.modulePair (A := pullback f t) ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)))ᵐᵒᵖ ×
      PtGrp L t :=
  (MulOpposite.op (toAut θ), θ.pt)

theorem eq_of_toGrp_eq (θ θ' : ThetaPt f L 𝓛 t) (h : toGrp θ = toGrp θ') : θ = θ' := by
  obtain ⟨x, ψ⟩ := θ
  obtain ⟨x', ψ'⟩ := θ'
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  change x = x' at h2
  subst h2
  have h3 : ψ = ψ' :=
    Scheme.Modules.fibration.autOfIso_injective _ (translateIso f L t x) ψ ψ' (MulOpposite.op_injective h1)
  subst h3
  rfl

theorem toGrp_injective : Function.Injective (toGrp (f := f) (L := L) (𝓛 := 𝓛) (t := t)) :=
  fun θ θ' h => eq_of_toGrp_eq θ θ' h

theorem toGrp_mul (θ θ' : ThetaPt f L 𝓛 t) : toGrp (θ * θ') = toGrp θ * toGrp θ' := by
  refine Prod.ext ?_ rfl
  show MulOpposite.op (toAut (θ * θ')) = MulOpposite.op (toAut θ) * MulOpposite.op (toAut θ')
  rw [← MulOpposite.op_mul, toAut_mul, Aut.Aut_mul_def]

theorem toGrp_one : toGrp (1 : ThetaPt f L 𝓛 t) = 1 := by
  refine Prod.ext ?_ rfl
  show MulOpposite.op (toAut 1) = 1
  rw [toAut_one]; rfl

theorem toGrp_inv (θ : ThetaPt f L 𝓛 t) : toGrp θ⁻¹ = (toGrp θ)⁻¹ := by
  refine Prod.ext ?_ rfl
  show MulOpposite.op (toAut θ⁻¹) = (MulOpposite.op (toAut θ))⁻¹
  rw [← MulOpposite.op_inv]
  congr 1
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [Aut.Aut_mul_def]
  exact toAut_inv_trans θ

theorem toGrp_div (θ θ' : ThetaPt f L 𝓛 t) : toGrp (θ / θ') = toGrp θ / toGrp θ' := by
  rw [div_def, toGrp_mul, toGrp_inv, div_eq_mul_inv]

theorem toGrp_npow (θ : ThetaPt f L 𝓛 t) (n : ℕ) : toGrp (θ ^ n) = toGrp θ ^ n := by
  induction n with
  | zero => rw [npow_zero, toGrp_one, pow_zero]
  | succ n ih => rw [npow_succ, toGrp_mul, ih, pow_succ]

theorem toGrp_zpow (θ : ThetaPt f L 𝓛 t) (n : ℤ) : toGrp (θ ^ n) = toGrp θ ^ n := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_ofNat, toGrp_npow, zpow_natCast]
  | negSucc n => rw [zpow_negSucc, toGrp_inv, toGrp_npow, _root_.zpow_negSucc]

instance instGroup : Group (ThetaPt f L 𝓛 t) :=
  Function.Injective.group toGrp toGrp_injective toGrp_one toGrp_mul toGrp_inv toGrp_div toGrp_npow toGrp_zpow

def toGrpHom : ThetaPt f L 𝓛 t →* (Aut (RiemannForm.modulePair (A := pullback f t)
      ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)))ᵐᵒᵖ × PtGrp L t where
  toFun := toGrp
  map_one' := toGrp_one
  map_mul' := toGrp_mul

def ptHom : ThetaPt f L 𝓛 t →* PtGrp L t := (MonoidHom.snd _ _).comp toGrpHom

@[simp] theorem ptHom_apply (θ : ThetaPt f L 𝓛 t) : ptHom θ = θ.pt := rfl

def thetaGroupR : Subgroup ((Aut (RiemannForm.modulePair (A := pullback f t)
      ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)))ᵐᵒᵖ × PtGrp L t) :=
  (toGrpHom (f := f) (L := L) (𝓛 := 𝓛) (t := t)).range

def equivThetaGroupR : ThetaPt f L 𝓛 t ≃* thetaGroupR (f := f) (L := L) (𝓛 := 𝓛) (t := t) :=
  MonoidHom.ofInjective toGrp_injective

end ThetaPt

end AlgebraicGeometry.Polarisation

end


