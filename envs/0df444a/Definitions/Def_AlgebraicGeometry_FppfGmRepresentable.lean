-- Prove2me | Definitions.Def_AlgebraicGeometry_FppfGmRepresentable
-- name    : AlgebraicGeometry_FppfGmRepresentable
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/2ce8a9f5-9d9a-539b-a101-817bbc6b0d86
-- title:
--   Representable fppf sheaves: group schemes, Gm​, μn​
-- statement:
--   Working with Mathlib's fppf and fpqc topologies on `Scheme.{u}`, which are subcanonical, the module records first that any representable presheaf of types is a sheaf for either topology (`isSheaf_fppf_of_isRepresentable`, `isSheaf_fpqc_of_isRepresentable`, and the `yoneda` and `RepresentableBy` corollaries), and then transports this along the forgetful functors: a presheaf of monoids, groups, commutative groups or additive commutative groups whose composite with the forgetful functor to types is representable is an fppf sheaf. For a scheme $G$ carrying a group-object structure, `fppfGrpSheaf` packages $T \mapsto \mathrm{Hom}(T,G)$ as a sheaf of groups; under the additional assumption that the multiplication is commutative, `yonedaCommGrpObj` is the same functor of points valued in commutative groups, `yonedaAddCommGrpObj` its image under the equivalence between commutative and additive commutative groups, and `fppfCommGrpSheaf`, `fppfAbelianSheaf` the corresponding sheaves; `fppfGrpSheafSectionsMulEquiv`, `fppfAbelianSheafSectionsAddEquiv` and the global-sections variant at the tensor unit identify the sections over $T$ with $\mathrm{Hom}(T,G)$, respectively with `Additive (T ⟶ G)`. The section `GroupSchemeOverBase` repeats this over a base $S$ for the induced topology `fppfTopologyOver S` on `Over S`, ending with `fppfOverAbelianSheaf` and its sections equivalence.
--
--   For multiplicative groups, `unitsPresheaf O` is the presheaf of units of a presheaf of commutative rings $O$, and `presieve_isSheaf_units` shows the units presheaf is a sheaf whenever the underlying type-valued presheaf of $O$ is. Applied to global sections this gives `Gm = unitsPresheaf Scheme.Γ`, a sheaf because $\Gamma$ composed with the forgetful functor is represented by $\mathrm{Spec}\,\mathbb{Z}[x]$ (`affineLineOverZ`, `gammaRepresentableBy`); `GmSheaf`, `GmAbelianSheaf` and `GmSectionsMulEquiv` : $\mathrm{Gm}(X) \simeq \Gamma(X,\mathcal{O}_X)^\times$ follow. The roots of unity `mu n` is $X \mapsto \mathrm{Hom}_{\mathrm{CommGrp}}(\mathbb{Z}/n, \mathbb{G}_m(X))$, with $\mathbb{Z}/n$ written multiplicatively, and satisfies the presieve sheaf condition. `constantZModSheaf` is the presheaf of continuous $\mathbb{Z}/n$-valued maps, discrete topology, an fppf sheaf because it is an fpqc sheaf. Closing lemmas: the trivial group scheme has subsingleton sections, a flat, surjective, locally finitely presented morphism generates an fppf covering sieve, and $\mathbb{G}_m(\mathrm{Spec}\,\mathbb{Z}) \simeq \mathbb{Z}^\times$ is nontrivial.
--
--   **Relation to Mathlib.** The topologies, their subcanonicity, `GrpObj`/`IsCommMonObj`, `CommMonCat.units` and the commutative/additive group equivalence are Mathlib's; `unitsPresheaf`, `Gm`, `mu`, `constantZMod` and the sheaf packagings are the project's own assembly of them.
--
--   **Where it is used.** These sheaves supply the terms of the Kummer sequence $0 \to \mu_p \to \mathbb{G}_m \xrightarrow{p} \mathbb{G}_m \to 0$ in the fppf topology, used in the descent and torsion arguments on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_FppfGmRepresentable.lean

import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace FppfRepresentableGroupSchemeSheaf

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe w v₁ u₁ u

section TypeValued

theorem isSheaf_fppf_of_isRepresentable (P : Scheme.{u}ᵒᵖ ⥤ Type u) [P.IsRepresentable] :
    Presheaf.IsSheaf Scheme.fppfTopology P := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

theorem isSheaf_fpqc_of_isRepresentable (P : Scheme.{u}ᵒᵖ ⥤ Type u) [P.IsRepresentable] :
    Presheaf.IsSheaf Scheme.fpqcTopology P := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

theorem isSheaf_fppf_yoneda (G : Scheme.{u}) :
    Presheaf.IsSheaf Scheme.fppfTopology (yoneda.obj G) :=
  isSheaf_fppf_of_isRepresentable _

theorem isSheaf_fppf_of_representableBy (P : Scheme.{u}ᵒᵖ ⥤ Type u) {G : Scheme.{u}}
    (h : P.RepresentableBy G) :
    Presheaf.IsSheaf Scheme.fppfTopology P :=
  have : P.IsRepresentable := h.isRepresentable
  isSheaf_fppf_of_isRepresentable P

theorem presieve_isSheaf_fppf_of_isRepresentable (P : Scheme.{u}ᵒᵖ ⥤ Type u)
    [P.IsRepresentable] : Presieve.IsSheaf Scheme.fppfTopology P :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

end TypeValued

section StructuredValues

theorem isSheaf_fppf_monCat_of_forget_isRepresentable (F : Scheme.{u}ᵒᵖ ⥤ MonCat.{u})
    [(F ⋙ forget MonCat).IsRepresentable] :
    Presheaf.IsSheaf Scheme.fppfTopology F :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget MonCat)
    (isSheaf_fppf_of_isRepresentable (F ⋙ forget MonCat))

theorem isSheaf_fppf_grpCat_of_forget_isRepresentable (F : Scheme.{u}ᵒᵖ ⥤ GrpCat.{u})
    [(F ⋙ forget GrpCat).IsRepresentable] :
    Presheaf.IsSheaf Scheme.fppfTopology F :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget GrpCat)
    (isSheaf_fppf_of_isRepresentable (F ⋙ forget GrpCat))

theorem isSheaf_fppf_commGrpCat_of_forget_isRepresentable (F : Scheme.{u}ᵒᵖ ⥤ CommGrpCat.{u})
    [(F ⋙ forget CommGrpCat).IsRepresentable] :
    Presheaf.IsSheaf Scheme.fppfTopology F :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget CommGrpCat)
    (isSheaf_fppf_of_isRepresentable (F ⋙ forget CommGrpCat))

theorem isSheaf_fppf_ab_of_forget_isRepresentable (F : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u})
    [(F ⋙ forget AddCommGrpCat).IsRepresentable] :
    Presheaf.IsSheaf Scheme.fppfTopology F :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat)
    (isSheaf_fppf_of_isRepresentable (F ⋙ forget AddCommGrpCat))

end StructuredValues

section GroupSchemeOverZ

variable (G : Scheme.{u}) [GrpObj G]

theorem isSheaf_fppf_yonedaGrpObj :
    Presheaf.IsSheaf Scheme.fppfTopology (yonedaGrpObj G) :=
  have : (yonedaGrpObj G ⋙ forget GrpCat).IsRepresentable :=
    (yonedaGrpObjRepresentableBy G).isRepresentable
  isSheaf_fppf_grpCat_of_forget_isRepresentable _

def fppfGrpSheaf : Sheaf Scheme.fppfTopology GrpCat.{u} :=
  ⟨yonedaGrpObj G, isSheaf_fppf_yonedaGrpObj G⟩

variable [IsCommMonObj G]

def yonedaCommGrpObj : Scheme.{u}ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (unop T ⟶ G)
  map φ := CommGrpCat.ofHom ((yonedaGrpObj G).map φ).hom
  map_id _ := CommGrpCat.hom_ext (MonoidHom.ext fun g => Category.id_comp g)
  map_comp φ ψ := CommGrpCat.hom_ext (MonoidHom.ext fun g => Category.assoc ψ.unop φ.unop g)

def yonedaCommGrpObjRepresentableBy :
    (yonedaCommGrpObj G ⋙ forget CommGrpCat).RepresentableBy G where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

theorem isSheaf_fppf_yonedaCommGrpObj :
    Presheaf.IsSheaf Scheme.fppfTopology (yonedaCommGrpObj G) :=
  have : (yonedaCommGrpObj G ⋙ forget CommGrpCat).IsRepresentable :=
    (yonedaCommGrpObjRepresentableBy G).isRepresentable
  isSheaf_fppf_commGrpCat_of_forget_isRepresentable _

def fppfCommGrpSheaf : Sheaf Scheme.fppfTopology CommGrpCat.{u} :=
  ⟨yonedaCommGrpObj G, isSheaf_fppf_yonedaCommGrpObj G⟩

def yonedaAddCommGrpObj : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yonedaCommGrpObj G ⋙ commGroupAddCommGroupEquivalence.functor

theorem isSheaf_fppf_yonedaAddCommGrpObj :
    Presheaf.IsSheaf Scheme.fppfTopology (yonedaAddCommGrpObj G) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ commGroupAddCommGroupEquivalence.functor
    (isSheaf_fppf_yonedaCommGrpObj G)

def fppfAbelianSheaf : Sheaf Scheme.fppfTopology AddCommGrpCat.{u} :=
  ⟨yonedaAddCommGrpObj G, isSheaf_fppf_yonedaAddCommGrpObj G⟩

end GroupSchemeOverZ

section SectionsIdentification

variable (G : Scheme.{u}) [GrpObj G]

def fppfGrpSheafSectionsMulEquiv (T : Scheme.{u}) :
    ((fppfGrpSheaf G).obj.obj (op T)) ≃* (T ⟶ G) :=
  MulEquiv.refl _

variable [IsCommMonObj G]

def fppfCommGrpSheafSectionsMulEquiv (T : Scheme.{u}) :
    ((fppfCommGrpSheaf G).obj.obj (op T)) ≃* (T ⟶ G) :=
  MulEquiv.refl _

def fppfAbelianSheafSectionsAddEquiv (T : Scheme.{u}) :
    ((fppfAbelianSheaf G).obj.obj (op T)) ≃+ Additive (T ⟶ G) :=
  AddEquiv.refl _

def fppfAbelianSheafGlobalSectionsAddEquiv :
    ((fppfAbelianSheaf G).obj.obj (op (𝟙_ Scheme.{u}))) ≃+ Additive (𝟙_ Scheme.{u} ⟶ G) :=
  fppfAbelianSheafSectionsAddEquiv G (𝟙_ Scheme.{u})

end SectionsIdentification

section GroupSchemeOverBase

variable (S : Scheme.{u})

abbrev fppfTopologyOver : GrothendieckTopology (Over S) :=
  Scheme.fppfTopology.over S

example : (fppfTopologyOver S).Subcanonical := inferInstance

variable (G : Over S) [GrpObj G]

theorem isSheaf_fppfOver_yonedaGrpObj :
    Presheaf.IsSheaf (fppfTopologyOver S) (yonedaGrpObj G) :=
  have : (yonedaGrpObj G ⋙ forget GrpCat).IsRepresentable :=
    (yonedaGrpObjRepresentableBy G).isRepresentable
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget GrpCat) (by
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

def fppfOverGrpSheaf : Sheaf (fppfTopologyOver S) GrpCat.{u} :=
  ⟨yonedaGrpObj G, isSheaf_fppfOver_yonedaGrpObj S G⟩

variable [IsCommMonObj G]

def yonedaCommGrpObjOver : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (unop T ⟶ G)
  map φ := CommGrpCat.ofHom ((yonedaGrpObj G).map φ).hom
  map_id _ := CommGrpCat.hom_ext (MonoidHom.ext fun g => Category.id_comp g)
  map_comp φ ψ := CommGrpCat.hom_ext (MonoidHom.ext fun g => Category.assoc ψ.unop φ.unop g)

def yonedaCommGrpObjOverRepresentableBy :
    (yonedaCommGrpObjOver S G ⋙ forget CommGrpCat).RepresentableBy G where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

theorem isSheaf_fppfOver_yonedaCommGrpObjOver :
    Presheaf.IsSheaf (fppfTopologyOver S) (yonedaCommGrpObjOver S G) :=
  have : (yonedaCommGrpObjOver S G ⋙ forget CommGrpCat).IsRepresentable :=
    (yonedaCommGrpObjOverRepresentableBy S G).isRepresentable
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget CommGrpCat) (by
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

def yonedaAddCommGrpObjOver : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yonedaCommGrpObjOver S G ⋙ commGroupAddCommGroupEquivalence.functor

theorem isSheaf_fppfOver_yonedaAddCommGrpObjOver :
    Presheaf.IsSheaf (fppfTopologyOver S) (yonedaAddCommGrpObjOver S G) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ commGroupAddCommGroupEquivalence.functor
    (isSheaf_fppfOver_yonedaCommGrpObjOver S G)

def fppfOverAbelianSheaf : Sheaf (fppfTopologyOver S) AddCommGrpCat.{u} :=
  ⟨yonedaAddCommGrpObjOver S G, isSheaf_fppfOver_yonedaAddCommGrpObjOver S G⟩

def fppfOverAbelianSheafSectionsAddEquiv (T : Over S) :
    ((fppfOverAbelianSheaf S G).obj.obj (op T)) ≃+ Additive (T ⟶ G) :=
  AddEquiv.refl _

end GroupSchemeOverBase

section UnitsDescent

variable {C : Type u₁} [Category.{v₁} C]

def unitsPresheaf (O : Cᵒᵖ ⥤ CommRingCat.{w}) : Cᵒᵖ ⥤ CommGrpCat.{w} :=
  O ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units

theorem presieve_isSheaf_units {J : GrothendieckTopology C} {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (hO : Presieve.IsSheaf J (O ⋙ forget CommRingCat)) :
    Presieve.IsSheaf J (unitsPresheaf O ⋙ forget CommGrpCat) := by
  intro X S hS x hx

  let xu : ∀ ⦃Y : C⦄ (f : Y ⟶ X), S.arrows f → ((O.obj (op Y)) : Type w)ˣ := fun _ f hf => x f hf

  let v : Presieve.FamilyOfElements (O ⋙ forget CommRingCat) S.arrows :=
    fun Y f hf => ((xu f hf : ((O.obj (op Y)) : Type w)ˣ) : (O.obj (op Y)))
  let w' : Presieve.FamilyOfElements (O ⋙ forget CommRingCat) S.arrows :=
    fun Y f hf => (((xu f hf)⁻¹ : ((O.obj (op Y)) : Type w)ˣ) : (O.obj (op Y)))

  have hv : v.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    exact congrArg Units.val (hx g₁ g₂ h₁ h₂ hcomm)
  have hw : w'.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    exact congrArg (fun u : ((O.obj (op Z)) : Type w)ˣ => ((u⁻¹ : _ˣ) : (O.obj (op Z))))
      (hx g₁ g₂ h₁ h₂ hcomm)

  obtain ⟨a, ha, ha_uniq⟩ := hO S hS v hv
  obtain ⟨b, hb, -⟩ := hO S hS w' hw

  have hab : a * b = 1 := by
    apply (hO S hS).isSeparatedFor.ext
    intro Y f hf
    have h1 : (O.map f.op).hom (a * b) =
        (O.map f.op).hom a * (O.map f.op).hom b := map_mul _ a b
    have h2 : (O.map f.op).hom (1 : (O.obj (op X))) = 1 := map_one _
    have ha' : (O.map f.op).hom a = v f hf := ha f hf
    have hb' : (O.map f.op).hom b = w' f hf := hb f hf
    show (O.map f.op).hom (a * b) = (O.map f.op).hom (1 : (O.obj (op X)))
    rw [h1, h2, ha', hb']
    exact Units.mul_inv _
  have hba : b * a = 1 := by rw [mul_comm]; exact hab

  refine ⟨(⟨a, b, hab, hba⟩ : ((O.obj (op X)) : Type w)ˣ), ?_, ?_⟩
  ·
    intro Y f hf
    show Units.map (O.map f.op).hom.toMonoidHom (⟨a, b, hab, hba⟩ : ((O.obj (op X)) : Type w)ˣ)
      = xu f hf
    apply Units.ext
    show (O.map f.op).hom a = ((xu f hf : ((O.obj (op Y)) : Type w)ˣ) : (O.obj (op Y)))
    exact ha f hf
  ·
    intro u hu

    let u' : ((O.obj (op X)) : Type w)ˣ := u
    have hval : (u' : (O.obj (op X))) = a := by
      apply ha_uniq
      intro Y f hf
      exact congrArg Units.val (hu f hf)
    show u' = (⟨a, b, hab, hba⟩ : ((O.obj (op X)) : Type w)ˣ)
    exact Units.ext hval

end UnitsDescent

section Instances

abbrev affineLineOverZ : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))

def gammaRepresentableBy :
    (Scheme.Γ.{u} ⋙ forget CommRingCat).RepresentableBy affineLineOverZ.{u} where
  homEquiv {X} := (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1} (X := X)).trans
    (Equiv.funUnique PUnit.{u + 1} _)
  homEquiv_comp f g := by
    show AffineSpace.toSpecMvPolyIntEquiv _ (f ≫ g) PUnit.unit = _
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp]
    rfl

theorem presieve_isSheaf_fppf_gammaForget :
    Presieve.IsSheaf Scheme.fppfTopology.{u} (Scheme.Γ ⋙ forget CommRingCat) :=
  have : (Scheme.Γ.{u} ⋙ forget CommRingCat).IsRepresentable :=
    gammaRepresentableBy.{u}.isRepresentable
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

def Gm : Scheme.{u}ᵒᵖ ⥤ CommGrpCat.{u} :=
  unitsPresheaf Scheme.Γ

theorem isSheaf_fppf_Gm : Presheaf.IsSheaf Scheme.fppfTopology.{u} Gm.{u} := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget CommGrpCat)
  rw [isSheaf_iff_isSheaf_of_type]
  exact presieve_isSheaf_units presieve_isSheaf_fppf_gammaForget

def GmSheaf : Sheaf Scheme.fppfTopology.{u} CommGrpCat.{u} :=
  ⟨Gm, isSheaf_fppf_Gm⟩

def GmSectionsMulEquiv (X : Scheme.{u}) :
    ((Gm.{u}).obj (op X) : Type u) ≃* ((Γ(X, ⊤) : Type u))ˣ :=
  MulEquiv.refl _

def GmAbelianSheaf : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u} :=
  ⟨Gm ⋙ commGroupAddCommGroupEquivalence.functor,
    Presheaf.isSheaf_comp_of_isSheaf _ _ commGroupAddCommGroupEquivalence.functor
      isSheaf_fppf_Gm⟩

def mu (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type u :=
  Gm ⋙ coyoneda.obj (op (CommGrpCat.of (ULift.{u} (Multiplicative (ZMod n)))))

theorem presieve_isSheaf_fppf_mu (n : ℕ) :
    Presieve.IsSheaf Scheme.fppfTopology.{u} (mu.{u} n) :=
  isSheaf_fppf_Gm (CommGrpCat.of (ULift.{u} (Multiplicative (ZMod n))))

theorem mu_obj (n : ℕ) (X : Scheme.{u}) :
    (mu.{u} n).obj (op X) =
      (CommGrpCat.of (ULift.{u} (Multiplicative (ZMod n))) ⟶ Gm.{u}.obj (op X)) :=
  rfl

section ConstantZMod

variable (n : ℕ)

local instance : TopologicalSpace (ZMod n) := ⊥

local instance : DiscreteTopology (ZMod n) := ⟨rfl⟩

local instance : IsTopologicalAddGroup (ZMod n) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

def constantZMod : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  continuousMapPresheafAb (ZMod n)

theorem isSheaf_fppf_constantZMod :
    Presheaf.IsSheaf Scheme.fppfTopology.{u} (constantZMod.{u} n) :=
  Presheaf.IsSheaf.of_le Scheme.fppfTopology_le_fpqcTopology
    (isSheaf_fpqcTopology_continuousMapPresheafAb (ZMod n))

def constantZModSheaf : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u} :=
  ⟨constantZMod n, isSheaf_fppf_constantZMod n⟩

end ConstantZMod

end Instances

section Gates

instance : IsCommMonObj (𝟙_ Scheme.{u}) where
  mul_comm := isTerminalTensorUnit.hom_ext _ _

def gateTrivialGroupSchemeAbelianSheaf : Sheaf Scheme.fppfTopology AddCommGrpCat.{u} :=
  fppfAbelianSheaf (𝟙_ Scheme.{u})

instance gateTrivialSheafSectionsSubsingleton (T : Scheme.{u}) :
    Subsingleton ((gateTrivialGroupSchemeAbelianSheaf.{u}).obj.obj (op T)) :=
  ⟨fun a b => by
    have h : ∀ x y : Additive (T ⟶ 𝟙_ Scheme.{u}), x = y := fun x y =>
      congrArg Additive.ofMul (isTerminalTensorUnit.hom_ext x.toMul y.toMul)
    exact (fppfAbelianSheafSectionsAddEquiv (𝟙_ Scheme.{u}) T).injective (h _ _)⟩

theorem gate_singleton_generates_fppf_cover {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [Surjective f] [LocallyOfFinitePresentation f] :
    Sieve.generate (Presieve.singleton f) ∈ Scheme.fppfTopology Y :=
  Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage f)

def gateGmSectionsSpecZ :
    ((Gm.{0}).obj (op (Spec (CommRingCat.of ℤ))) : Type 0) ≃* ℤˣ :=
  (GmSectionsMulEquiv (Spec (CommRingCat.of ℤ))).trans
    (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.toMulEquiv)

theorem gate_Gm_sections_nontrivial :
    Nontrivial ((Gm.{0}).obj (op (Spec (CommRingCat.of ℤ))) : Type 0) :=
  haveI : Nontrivial ℤˣ := ⟨1, -1, by decide⟩
  gateGmSectionsSpecZ.toEquiv.nontrivial

end Gates

end FppfRepresentableGroupSchemeSheaf


