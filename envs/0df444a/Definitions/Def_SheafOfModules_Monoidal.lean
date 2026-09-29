-- Prove2me | Definitions.Def_SheafOfModules_Monoidal
-- name    : SheafOfModules_Monoidal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/bb2c5a3e-57ef-55ec-9593-4a0e9facc28b
-- title:
--   Monoidal structure on sheaves of modules over a site
-- statement:
--   Throughout, $(\mathcal{C},J)$ is a site with $\mathcal{C}$ a small category in the universe of the rings, $\mathcal{O} : \mathcal{C}^{\mathrm{op}} \to \mathrm{CommRing}$ a presheaf of commutative rings together with a proof `h𝒪` that the underlying presheaf of rings is a $J$-sheaf, and $J$ satisfies the usual hypotheses making sheafification of abelian-group-valued presheaves available and locally bijective. `ringSheaf` packages $\mathcal{O}$ and `h𝒪` as a sheaf of rings, `PMod` abbreviates the category of presheaves of modules over the underlying presheaf of rings, `sheafifyFunctor` and `toPMod` are the sheafification functor $\mathrm{PMod}(\mathcal{O}) \to \mathrm{Mod}(\mathcal{O})$ (along the identity of $\mathcal{O}$) and its right adjoint given by forgetting the sheaf condition and restricting scalars along the identity, and `sheafifyAdj` is their adjunction; the right adjoint is recorded as full and faithful, and sheafification is a localisation at `presheafW`, the class of morphisms of presheaves of modules whose underlying morphism of presheaves of abelian groups lies in $J.W$, i.e. is inverted by abelian sheafification. The theorem `presheafW_isMonoidal` states that this class is compatible with the tensor product of presheaves of modules. The isomorphisms `sheafifyCounitIso` and `sheafifyUnitIso` exhibit the counit of the adjunction as invertible and identify the sheafification of the monoidal unit of $\mathrm{PMod}(\mathcal{O})$ with the unit sheaf of modules. Using these, the monoidal, symmetric monoidal and monoidal-functor structures on $\mathrm{Mod}(\mathcal{O})$ and on `sheafifyFunctor` are obtained by transport from the monoidal localisation of $\mathrm{PMod}(\mathcal{O})$ at `presheafW`; `tensorUnit_eq` identifies the unit object with `unit`, `monoidalClosed` deduces closedness by reflection from the presheaf level, and `tensorIsoSheafify` gives a natural isomorphism from the sheafification of $L^{\mathrm{val}} \otimes M^{\mathrm{val}}$ to $L \otimes M$. The second half specialises all of this to a scheme $X$: monoidal, symmetric and closed structures on `X.PresheafOfModules` and on `X.Modules`, the abbreviations `tensor` and `dual` $L^{\vee} = \mathcal{H}om(L, \mathcal{O}_X)$ (the internal hom evaluated at the unit), the identification of the unit with $\mathcal{O}_X$, the sheafification functor $X.\mathrm{PresheafOfModules} \to X.\mathrm{Modules}$ with its monoidal structure, and the corresponding comparison isomorphism.
--
--   **Relation to Mathlib.** Mathlib provides the monoidal structure on `PresheafOfModules`, the sheafification adjunction and the machinery of monoidal localisations, but no monoidal structure on `SheafOfModules` or on `Scheme.Modules`; those are the contribution of this module. The internal hom of presheaves of modules, whose sections over $X$ are the families assigning to each $f : X \to Y$ an $\mathcal{O}(Y)$-linear map $F(Y) \to N(Y)$ compatibly with restriction, and the resulting `MonoidalClosed` instance on `PresheafOfModules`, come from the project's own `PresheafOfModules_InternalHom`.
--
--   **Where it is used.** Tensor products and duals of invertible $\mathcal{O}_X$-modules, hence the group structure on isomorphism classes of line bundles, rest on this monoidal closed structure; it is used in the project's treatment of Picard groups and of the rigidified relative Picard functor of a curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_SheafOfModules_Monoidal.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Limits

noncomputable section

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

abbrev ringSheaf : Sheaf J RingCat.{u} := ⟨𝒪 ⋙ forget₂ CommRingCat RingCat, h𝒪⟩

abbrev PMod := PresheafOfModules.{u} (𝒪 ⋙ forget₂ CommRingCat RingCat)

abbrev presheafW (J : GrothendieckTopology C) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) :
    MorphismProperty (PMod 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))

abbrev sheafifyFunctor : PMod 𝒪 ⥤ SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) :=
  PresheafOfModules.sheafification (R := ringSheaf 𝒪 h𝒪) (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))

abbrev toPMod : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) ⥤ PMod 𝒪 :=
  SheafOfModules.forget (ringSheaf 𝒪 h𝒪) ⋙
    PresheafOfModules.restrictScalars (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))

abbrev sheafifyAdj : sheafifyFunctor 𝒪 h𝒪 ⊣ toPMod 𝒪 h𝒪 :=
  PresheafOfModules.sheafificationAdjunction (R := ringSheaf 𝒪 h𝒪)
    (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))

instance : (toPMod 𝒪 h𝒪).Faithful := (sheafifyAdj 𝒪 h𝒪).fullyFaithfulROfIsIsoCounit.faithful
instance : (toPMod 𝒪 h𝒪).Full := (sheafifyAdj 𝒪 h𝒪).fullyFaithfulROfIsIsoCounit.full

instance : (sheafifyFunctor 𝒪 h𝒪).IsLocalization (presheafW J 𝒪) := inferInstance

include h𝒪 in

theorem presheafW_isMonoidal : (presheafW J 𝒪).IsMonoidal :=
  PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf 𝒪 (ringSheaf 𝒪 h𝒪) (𝟙 _)

def sheafifyCounitIso (M : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :
    (sheafifyFunctor 𝒪 h𝒪).obj ((toPMod 𝒪 h𝒪).obj M) ≅ M :=
  (asIso (sheafifyAdj 𝒪 h𝒪).counit).app M

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

set_option backward.isDefEq.respectTransparency false in

def sheafifyUnitIso : (sheafifyFunctor 𝒪 h𝒪).obj (𝟙_ (PMod 𝒪)) ≅
    (unit (ringSheaf 𝒪 h𝒪) : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  sheafifyCounitIso 𝒪 h𝒪 (unit (ringSheaf 𝒪 h𝒪))

instance monoidalCategory : MonoidalCategory (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)))

instance symmetricCategory : SymmetricCategory (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)))

instance sheafifyFunctor_monoidal : (sheafifyFunctor 𝒪 h𝒪).Monoidal :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)).Monoidal

@[simp] theorem tensorUnit_eq : 𝟙_ (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) = unit _ := rfl

instance monoidalClosed : MonoidalClosed (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  Monoidal.Reflective.monoidalClosed (sheafifyAdj 𝒪 h𝒪)

def tensorIsoSheafify (L M : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :
    (sheafifyFunctor 𝒪 h𝒪).obj (L.val ⊗ M.val) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (sheafifyFunctor 𝒪 h𝒪) L.val M.val).symm ≪≫
    (sheafifyCounitIso 𝒪 h𝒪 L ⊗ᵢ sheafifyCounitIso 𝒪 h𝒪 M)

end SheafOfModules

namespace AlgebraicGeometry

variable (X : Scheme.{u})

instance Scheme.PresheafOfModules.monoidalCategory : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
instance Scheme.PresheafOfModules.symmetricCategory : SymmetricCategory X.PresheafOfModules :=
  inferInstanceAs (SymmetricCategory (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
instance Scheme.PresheafOfModules.monoidalClosed : MonoidalClosed X.PresheafOfModules :=
  inferInstanceAs (MonoidalClosed (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

instance Scheme.Modules.monoidalCategory : MonoidalCategory X.Modules :=
  inferInstanceAs (MonoidalCategory
    (SheafOfModules.{u} (SheafOfModules.ringSheaf X.sheaf.obj X.ringCatSheaf.property)))
instance Scheme.Modules.symmetricCategory : SymmetricCategory X.Modules :=
  inferInstanceAs (SymmetricCategory
    (SheafOfModules.{u} (SheafOfModules.ringSheaf X.sheaf.obj X.ringCatSheaf.property)))
instance Scheme.Modules.monoidalClosed : MonoidalClosed X.Modules :=
  inferInstanceAs (MonoidalClosed
    (SheafOfModules.{u} (SheafOfModules.ringSheaf X.sheaf.obj X.ringCatSheaf.property)))

variable {X}

abbrev Scheme.Modules.tensor (L M : X.Modules) : X.Modules := L ⊗ M

abbrev Scheme.Modules.dual (L : X.Modules) : X.Modules := (ihom L).obj (𝟙_ X.Modules)

@[simp] theorem Scheme.Modules.tensorUnit_eq :
    𝟙_ X.Modules = SheafOfModules.unit X.ringCatSheaf := rfl

variable (X) in

abbrev Scheme.Modules.sheafify : X.PresheafOfModules ⥤ X.Modules :=
  SheafOfModules.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property

instance : (Scheme.Modules.sheafify X).Monoidal :=
  inferInstanceAs (SheafOfModules.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property).Monoidal

def Scheme.Modules.tensorIsoSheafify (L M : X.Modules) :
    (Scheme.Modules.sheafify X).obj (L.val ⊗ M.val) ≅ L ⊗ M :=
  SheafOfModules.tensorIsoSheafify X.sheaf.obj X.ringCatSheaf.property L M

end AlgebraicGeometry

end


