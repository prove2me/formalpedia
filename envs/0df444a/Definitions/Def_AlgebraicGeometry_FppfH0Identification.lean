-- Prove2me | Definitions.Def_AlgebraicGeometry_FppfH0Identification
-- name    : AlgebraicGeometry_FppfH0Identification
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/0e83f2ba-6bb6-5a56-8444-e787eaeb74ad
-- title:
--   Degree-zero fppf cohomology as sections; étale–fppf sheaf comparison
-- statement:
--   For a scheme $S$ and an abelian sheaf $F$ on the small fppf site $S.\mathrm{Fppf}$ (objects: flat, locally finitely presented $S$-schemes), the degree-zero cohomology $H^0(F)=\mathrm{Ext}^0(\underline{\mathbb{Z}},F)$ is identified with the group of sections over the terminal object $\mathrm{id}_S$. `fppfH0SectionsIsoApp` packages the additive equivalence `fppfCohomologyZeroAddEquiv` — the composite of $\mathrm{Ext}^0(\underline{\mathbb Z},F)\cong\mathrm{Hom}(\underline{\mathbb Z},F)$, the constant-sheaf adjunction at the terminal object, and $\mathrm{Hom}_{\mathrm{Ab}}(\mathrm{ULift}\,\mathbb Z,A)\cong A$ — as an isomorphism of abelian groups, and `fppfCohomologyZeroNatIso` assembles these into a natural isomorphism $H^0(-)\cong$ evaluation at `fppfTerminal S` of functors on sheaves; `fppfCohomologySpecIntZeroNatIso` is the case $S=\operatorname{Spec}\mathbb Z$. Since evaluation at a terminal object is right adjoint to the constant-sheaf functor, $H^0$ preserves limits of any size, hence finite limits. Auxiliary naturality lemmas record how $\mathrm{Ext}^0$'s identification with $\mathrm{Hom}$ and an additive hom-equivalence of an adjunction behave under pre- and post-composition; the `gate_` lemmas are consistency checks (naturality on identities and into the zero sheaf, round-trip through the natural isomorphism, transport of non-triviality).
--
--   A second part treats change of topology: for $J\le K$ on a site, `sheafInclusionOfLe` is the functor $\mathrm{Sheaf}(K,A)\to\mathrm{Sheaf}(J,A)$ given by the same underlying presheaf, shown full, faithful, additive and equal to the pushforward along the identity functor viewed as continuous; `sheafHZeroSectionsAddEquiv` is the generic $H^0\cong$ sections-at-a-terminal-object equivalence, and `sheafInclusionHZeroAddEquiv` compares $H^0$ of a $K$-sheaf with $H^0$ of its $J$-restriction through these sections. Specialising to $\mathrm{\acute et}\le\mathrm{fppf}$ on schemes gives `fppfSheafToEtaleSheaf`, the étale site's own six-term sequence and cohomology functor `etaleCohomologyFunctor`, and `fppfToEtaleHZeroAddEquiv` (degree zero only; no comparison in higher degrees is asserted). Finally, for sheaves of abelian groups on any site, the degree-zero part of the long exact sequence is rewritten as left exactness of $\mathrm{Hom}(\underline{\mathbb Z},-)$: injectivity and exactness of postcomposition with a short exact sequence, and injectivity of $H^0(\varphi)$ for monomorphic $\varphi$.
--
--   **Relation to Mathlib.** Built on Mathlib's sheaf cohomology (`Sheaf.H`, `Sheaf.functorH`), `Ext.addEquiv₀` and `constantSheafAdj`. The restriction functor `sheafInclusionOfLe` for a refinement $J \le K$ of Grothendieck topologies is defined here directly and then identified with Mathlib's `sheafPushforwardContinuous` along the identity functor; the $H^0$-as-sections natural isomorphism is the project's own.
--
--   **Where it is used.** The identification of $H^0$ on the small fppf site with sections over the base, and its naturality, supply the degree-zero term when the long exact cohomology sequence is applied to short exact sequences of fppf sheaves (notably Kummer sequences) in the study of torsion on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_FppfH0Identification.lean

import Mathlib.CategoryTheory.Sites.Continuous
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe v' u' wE vE uE v₁ v₂ u₁ u₂ u w' w v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Abelian.Ext

variable {C : Type uE} [Category.{vE} C] [Abelian C] [HasExt.{wE} C]

theorem addEquiv₀_comp_mk₀ {X Y Z : C} (α : Ext X Y 0) (ψ : Y ⟶ Z)
    (h : (0 : ℕ) + 0 = 0) :
    addEquiv₀ (α.comp (mk₀ ψ) h) = addEquiv₀ α ≫ ψ := by
  apply (mk₀_bijective X Z).injective
  rw [mk₀_addEquiv₀_apply, ← mk₀_comp_mk₀, mk₀_addEquiv₀_apply]

theorem addEquiv₀_mk₀_comp {X Y Z : C} (ψ : X ⟶ Y) (α : Ext Y Z 0)
    (h : (0 : ℕ) + 0 = 0) :
    addEquiv₀ ((mk₀ ψ).comp α h) = ψ ≫ addEquiv₀ α := by
  apply (mk₀_bijective X Z).injective
  rw [mk₀_addEquiv₀_apply, ← mk₀_comp_mk₀, mk₀_addEquiv₀_apply]

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive]

theorem homAddEquiv_naturality_right (X : C) {Y Y' : D} (f : L.obj X ⟶ Y) (g : Y ⟶ Y') :
    adj.homAddEquiv X Y' (f ≫ g) = adj.homAddEquiv X Y f ≫ R.map g := by
  simpa only [Adjunction.homAddEquiv_apply] using adj.homEquiv_naturality_right f g

theorem homAddEquiv_naturality_left {X' X : C} (Y : D) (f : X' ⟶ X) (g : L.obj X ⟶ Y) :
    adj.homAddEquiv X' Y (L.map f ≫ g) = f ≫ adj.homAddEquiv X Y g := by
  simpa only [Adjunction.homAddEquiv_apply] using adj.homEquiv_naturality_left f g

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme

theorem homULiftIntAddEquiv_naturality {A B : Ab.{w}}
    (f : AddCommGrpCat.of (ULift.{w} ℤ) ⟶ A) (ψ : A ⟶ B) :
    homULiftIntAddEquiv B (f ≫ ψ) = ψ (homULiftIntAddEquiv A f) := rfl

variable (S : Scheme.{u})

theorem sheafSections_fppfTerminal_obj (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) :
    ((sheafSections (smallFppfTopology S) Ab.{u + 1}).obj (op (fppfTerminal S))).obj F =
      F.obj.obj (op (fppfTerminal S)) := rfl

theorem sheafSections_fppfTerminal_map_apply {F G : Sheaf (smallFppfTopology S) Ab.{u + 1}}
    (φ : F ⟶ G) (x : F.obj.obj (op (fppfTerminal S))) :
    ((sheafSections (smallFppfTopology S) Ab.{u + 1}).obj (op (fppfTerminal S))).map φ x =
      φ.hom.app (op (fppfTerminal S)) x := rfl

open Abelian in

theorem fppfCohomologyFunctor_map_apply (n : ℕ)
    {F G : Sheaf (smallFppfTopology S) Ab.{u + 1}} (φ : F ⟶ G) (α : F.H n) :
    (fppfCohomologyFunctor S n).map φ α = Ext.comp α (Ext.mk₀ φ) (add_zero n) := rfl

open Abelian in

theorem fppfCohomologyFunctor_map_eq_fppfCohomologyMap (n : ℕ)
    {F G : Sheaf (smallFppfTopology S) Ab.{u + 1}} (φ : F ⟶ G)
    (α : fppfCohomology S F n) :
    (fppfCohomologyFunctor S n).map φ α = fppfCohomologyMap S φ n α := rfl

open Abelian in

theorem sheafHZeroAddEquiv_apply (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) (x : F.H 0) :
    sheafHZeroAddEquiv S F x =
      homULiftIntAddEquiv.{u + 1} (F.obj.obj (op (fppfTerminal S)))
        ((constantSheafAdj (smallFppfTopology S) Ab.{u + 1}
          (fppfTerminalIsTerminal S)).homAddEquiv
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)) F (Ext.addEquiv₀ x)) := rfl

open Abelian in

theorem sheafHZeroAddEquiv_naturality {F G : Sheaf (smallFppfTopology S) Ab.{u + 1}}
    (φ : F ⟶ G) (α : F.H 0) :
    sheafHZeroAddEquiv S G (Ext.comp α (Ext.mk₀ φ) (add_zero 0)) =
      φ.hom.app (op (fppfTerminal S)) (sheafHZeroAddEquiv S F α) := by
  rw [sheafHZeroAddEquiv_apply, sheafHZeroAddEquiv_apply]
  rw [Ext.addEquiv₀_comp_mk₀]
  rw [Adjunction.homAddEquiv_naturality_right]
  exact homULiftIntAddEquiv_naturality _ _

open Abelian in

theorem fppfCohomologyZeroAddEquiv_naturality
    {F G : Sheaf (smallFppfTopology S) Ab.{u + 1}} (φ : F ⟶ G)
    (α : fppfCohomology S F 0) :
    fppfCohomologyZeroAddEquiv S G (fppfCohomologyMap S φ 0 α) =
      φ.hom.app (op (fppfTerminal S)) (fppfCohomologyZeroAddEquiv S F α) :=
  sheafHZeroAddEquiv_naturality S φ α

open Abelian in

theorem fppfCohomologyZeroAddEquiv_symm_naturality
    {F G : Sheaf (smallFppfTopology S) Ab.{u + 1}} (φ : F ⟶ G)
    (x : F.obj.obj (op (fppfTerminal S))) :
    (fppfCohomologyZeroAddEquiv S G).symm (φ.hom.app (op (fppfTerminal S)) x) =
      fppfCohomologyMap S φ 0 ((fppfCohomologyZeroAddEquiv S F).symm x) := by
  apply (fppfCohomologyZeroAddEquiv S G).injective
  rw [AddEquiv.apply_symm_apply, fppfCohomologyZeroAddEquiv_naturality,
    AddEquiv.apply_symm_apply]

noncomputable def fppfH0SectionsIsoApp (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) :
    (fppfCohomologyFunctor S 0).obj F ≅ F.obj.obj (op (fppfTerminal S)) :=
  AddEquiv.toAddCommGrpIso
    (X := (fppfCohomologyFunctor S 0).obj F)
    (Y := F.obj.obj (op (fppfTerminal S)))
    (fppfCohomologyZeroAddEquiv S F)

theorem fppfH0SectionsIsoApp_naturality {F G : Sheaf (smallFppfTopology S) Ab.{u + 1}}
    (φ : F ⟶ G) :
    (fppfCohomologyFunctor S 0).map φ ≫ (fppfH0SectionsIsoApp S G).hom =
      (fppfH0SectionsIsoApp S F).hom ≫
        ((sheafSections (smallFppfTopology S) Ab.{u + 1}).obj (op (fppfTerminal S))).map φ := by
  ext α
  show fppfCohomologyZeroAddEquiv S G ((fppfCohomologyFunctor S 0).map φ α) =
    φ.hom.app (op (fppfTerminal S)) (fppfCohomologyZeroAddEquiv S F α)
  rw [fppfCohomologyFunctor_map_apply]
  exact sheafHZeroAddEquiv_naturality S φ α

noncomputable def fppfCohomologyZeroNatIso :
    fppfCohomologyFunctor S 0 ≅
      (sheafSections (smallFppfTopology S) Ab.{u + 1}).obj (op (fppfTerminal S)) :=
  NatIso.ofComponents (fun F => fppfH0SectionsIsoApp S F)
    (fun φ => fppfH0SectionsIsoApp_naturality S φ)

noncomputable example : (Sheaf (smallFppfTopology S) Ab.{u + 1} ⥤ Ab.{u + 1}) :=
  fppfCohomologyFunctor S 0
noncomputable example : (Sheaf (smallFppfTopology S) Ab.{u + 1} ⥤ Ab.{u + 1}) :=
  (sheafSections (smallFppfTopology S) Ab.{u + 1}).obj (op (fppfTerminal S))

@[simp]
theorem fppfCohomologyZeroNatIso_hom_app_apply (F : Sheaf (smallFppfTopology S) Ab.{u + 1})
    (α : fppfCohomology S F 0) :
    (fppfCohomologyZeroNatIso S).hom.app F α = fppfCohomologyZeroAddEquiv S F α := rfl

@[simp]
theorem fppfCohomologyZeroNatIso_inv_app_apply (F : Sheaf (smallFppfTopology S) Ab.{u + 1})
    (x : F.obj.obj (op (fppfTerminal S))) :
    (fppfCohomologyZeroNatIso S).inv.app F x =
      (fppfCohomologyZeroAddEquiv S F).symm x := rfl

theorem fppfCohomologyZeroNatIso_naturality {F G : Sheaf (smallFppfTopology S) Ab.{u + 1}}
    (φ : F ⟶ G) :
    (fppfCohomologyFunctor S 0).map φ ≫ (fppfCohomologyZeroNatIso S).hom.app G =
      (fppfCohomologyZeroNatIso S).hom.app F ≫
        ((sheafSections (smallFppfTopology S) Ab.{u + 1}).obj (op (fppfTerminal S))).map φ :=
  (fppfCohomologyZeroNatIso S).hom.naturality φ

theorem sectionsAtFppfTerminal_preservesLimits :
    PreservesLimitsOfSize.{v', u'}
      ((sheafSections (smallFppfTopology S) Ab.{u + 1}).obj (op (fppfTerminal S))) :=
  (constantSheafAdj (smallFppfTopology S) Ab.{u + 1}
    (fppfTerminalIsTerminal S)).rightAdjoint_preservesLimits

theorem fppfCohomologyFunctor_zero_preservesLimits :
    PreservesLimitsOfSize.{v', u'} (fppfCohomologyFunctor S 0) :=
  haveI := sectionsAtFppfTerminal_preservesLimits.{v', u'} S
  preservesLimits_of_natIso (fppfCohomologyZeroNatIso S).symm

theorem fppfCohomologyFunctor_zero_preservesFiniteLimits :
    PreservesFiniteLimits (fppfCohomologyFunctor S 0) :=
  haveI := fppfCohomologyFunctor_zero_preservesLimits.{0, 0} S
  PreservesLimitsOfSize.preservesFiniteLimits _

instance (n : ℕ) : (fppfCohomologyFunctor S n).Additive :=
  inferInstanceAs (Sheaf.functorH (smallFppfTopology S) n).Additive

theorem gate_naturality_fires_on_id (F : Sheaf (smallFppfTopology S) Ab.{u + 1})
    (α : fppfCohomology S F 0) :
    fppfCohomologyZeroAddEquiv S F (fppfCohomologyMap S (𝟙 F) 0 α) =
      fppfCohomologyZeroAddEquiv S F α := by
  rw [fppfCohomologyZeroAddEquiv_naturality S (𝟙 F) α]
  rfl

example (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) (α : fppfCohomology S F 0) :
    fppfCohomologyZeroAddEquiv S F (fppfCohomologyMap S (𝟙 F) 0 α) =
      fppfCohomologyZeroAddEquiv S F α :=
  congrArg (fppfCohomologyZeroAddEquiv S F) (fppfCohomologyMap_id S 0 α)

open ZeroObject in

theorem gate_naturality_fires_into_zero_sheaf (F : Sheaf (smallFppfTopology S) Ab.{u + 1})
    (φ : F ⟶ (0 : Sheaf (smallFppfTopology S) Ab.{u + 1}))
    (α : fppfCohomology S F 0) :
    φ.hom.app (op (fppfTerminal S)) (fppfCohomologyZeroAddEquiv S F α) =
      fppfCohomologyZeroAddEquiv S (0 : Sheaf (smallFppfTopology S) Ab.{u + 1})
        (fppfCohomologyMap S φ 0 α) :=
  (fppfCohomologyZeroAddEquiv_naturality S φ α).symm

theorem gate_natIso_component_roundtrip (F : Sheaf (smallFppfTopology S) Ab.{u + 1})
    (α : fppfCohomology S F 0) :
    (fppfCohomologyZeroNatIso S).inv.app F ((fppfCohomologyZeroNatIso S).hom.app F α) = α :=
  (fppfCohomologyZeroAddEquiv S F).symm_apply_apply α

theorem gate_natIso_nontriviality_transport (F : Sheaf (smallFppfTopology S) Ab.{u + 1})
    (h : Nontrivial (F.obj.obj (op (fppfTerminal S)))) :
    Nontrivial ((fppfCohomologyFunctor S 0).obj F) :=
  (fppfCohomologyZeroAddEquiv S F).toEquiv.nontrivial

section SpecInt

noncomputable def fppfCohomologySpecIntZeroNatIso :
    fppfCohomologyFunctor specInt 0 ≅
      (sheafSections (smallFppfTopology specInt) Ab.{1}).obj (op (fppfTerminal specInt)) :=
  fppfCohomologyZeroNatIso specInt

theorem gate_specInt_natIso_component_eq_addEquiv
    (F : Sheaf (smallFppfTopology specInt) Ab.{1}) (α : fppfCohomology specInt F 0) :
    fppfCohomologySpecIntZeroNatIso.hom.app F α =
      fppfCohomologySpecIntZeroAddEquiv F α := rfl

theorem gate_specInt_H0_preservesFiniteLimits :
    PreservesFiniteLimits (fppfCohomologyFunctor specInt 0) :=
  fppfCohomologyFunctor_zero_preservesFiniteLimits specInt

end SpecInt

end AlgebraicGeometry.Scheme

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Limits Opposite AlgebraicGeometry FppfCohomologyLES

namespace EtaleCohomologyLES

example : Scheme.etalePrecoverage.{u} ≤ Scheme.fppfPrecoverage :=
  Scheme.etalePrecoverage_le_fppfPrecoverage

example : Scheme.etaleTopology.{u} ≤ Scheme.fppfTopology :=
  Scheme.etaleTopology_le_fppfTopology

example : Scheme.zariskiTopology.{u} ≤ Scheme.etaleTopology :=
  Scheme.zariskiTopology_le_etaleTopology

instance etaleTopologySubcanonical : Scheme.etaleTopology.{u}.Subcanonical :=
  .of_le Scheme.etaleTopology_le_fppfTopology

section GenericChangeOfTopology

variable {C : Type u} [Category.{v} C]

def sheafInclusionOfLe {A : Type u₂} [Category.{v₂} A] {J K : GrothendieckTopology C}
    (hJK : J ≤ K) : Sheaf K A ⥤ Sheaf J A where
  obj F := ⟨F.obj, F.property.of_le hJK⟩
  map φ := ObjectProperty.homMk φ.hom
  map_id _ := Sheaf.hom_ext rfl
  map_comp _ _ := Sheaf.hom_ext rfl

@[simp]
theorem sheafInclusionOfLe_obj_obj {A : Type u₂} [Category.{v₂} A]
    {J K : GrothendieckTopology C} (hJK : J ≤ K) (F : Sheaf K A) :
    ((sheafInclusionOfLe hJK).obj F).obj = F.obj :=
  rfl

@[simp]
theorem sheafInclusionOfLe_map_hom {A : Type u₂} [Category.{v₂} A]
    {J K : GrothendieckTopology C} (hJK : J ≤ K) {F G : Sheaf K A} (φ : F ⟶ G) :
    ((sheafInclusionOfLe hJK).map φ).hom = φ.hom :=
  rfl

theorem faithful_sheafInclusionOfLe {A : Type u₂} [Category.{v₂} A]
    {J K : GrothendieckTopology C} (hJK : J ≤ K) :
    (sheafInclusionOfLe (A := A) hJK).Faithful where
  map_injective h := Sheaf.hom_ext (congrArg (fun ψ => ψ.hom) h)

theorem full_sheafInclusionOfLe {A : Type u₂} [Category.{v₂} A]
    {J K : GrothendieckTopology C} (hJK : J ≤ K) :
    (sheafInclusionOfLe (A := A) hJK).Full where
  map_surjective ψ := ⟨ObjectProperty.homMk ψ.hom, Sheaf.hom_ext rfl⟩

theorem additive_sheafInclusionOfLe {A : Type u₂} [Category.{v₂} A] [Preadditive A]
    {J K : GrothendieckTopology C} (hJK : J ≤ K) :
    (sheafInclusionOfLe (A := A) hJK).Additive where
  map_add := Sheaf.hom_ext rfl

theorem isContinuous_id_of_le {J K : GrothendieckTopology C} (hJK : J ≤ K) :
    Functor.IsContinuous (𝟭 C) J K :=
  ⟨fun G => Presieve.isSheaf_of_le _ hJK ((isSheaf_iff_isSheaf_of_type _ _).1 G.property)⟩

variable {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

noncomputable def sheafHZeroSectionsAddEquiv [(constantSheaf J AddCommGrpCat.{w}).Additive]
    {T : C} (hT : IsTerminal T) (G : Sheaf J AddCommGrpCat.{w}) :
    G.H 0 ≃+ G.obj.obj (op T) :=
  ((cohomologyZeroAddEquivHom G).trans
    ((constantSheafAdj J AddCommGrpCat.{w} hT).homAddEquiv _ _)).trans
    (Scheme.homULiftIntAddEquiv.{w} (G.obj.obj (op T)))

noncomputable def sheafInclusionHZeroAddEquiv {K : GrothendieckTopology C} (hJK : J ≤ K)
    [HasSheafify K AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf K AddCommGrpCat.{w})]
    [(constantSheaf J AddCommGrpCat.{w}).Additive]
    [(constantSheaf K AddCommGrpCat.{w}).Additive]
    {T : C} (hT : IsTerminal T) (F : Sheaf K AddCommGrpCat.{w}) :
    ((sheafInclusionOfLe (A := AddCommGrpCat.{w}) hJK).obj F).H 0 ≃+ F.H 0 :=
  (sheafHZeroSectionsAddEquiv hT ((sheafInclusionOfLe hJK).obj F)).trans
    (sheafHZeroSectionsAddEquiv hT F).symm

end GenericChangeOfTopology

section EtaleSite

instance etaleSheavesIsGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} Scheme.{u} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall Scheme.etaleTopology Ab.{u + 1}

example : HasExt.{u + 1} (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}) := inferInstance

example : HasSheafify Scheme.etaleTopology.{u} Ab.{u + 1} := inferInstance

noncomputable example : IsTerminal (Spec (CommRingCat.of ℤ)) := specZIsTerminal

section WithLocalInstances

variable [HasSheafify Scheme.etaleTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1})]

noncomputable abbrev EtaleH (F : Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}) (n : ℕ) :
    Type (u + 1) :=
  F.H n

theorem etaleH_eq_sheafH (F : Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}) (n : ℕ) :
    EtaleH F n = F.H n := rfl

theorem etale_les_exact_two {S : ShortComplex (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (cohomologyMap S.f n) (cohomologyMap S.g n) :=
  cohomology_exact_two hS n

theorem etale_les_exact_three {S : ShortComplex (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyMap S.g n₀) (cohomologyδ hS n₀ n₁ h) :=
  cohomology_exact_three hS n₀ n₁ h

theorem etale_les_exact_one {S : ShortComplex (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyδ hS n₀ n₁ h) (cohomologyMap S.f n₁) :=
  cohomology_exact_one hS n₀ n₁ h

theorem etale_sixTermLES {S : ShortComplex (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) :
    Function.Injective (cohomologyMap S.f 0) ∧
    Function.Exact (cohomologyMap S.f 0) (cohomologyMap S.g 0) ∧
    Function.Exact (cohomologyMap S.g 0) (cohomologyδ hS 0 1 rfl) ∧
    Function.Exact (cohomologyδ hS 0 1 rfl) (cohomologyMap S.f 1) ∧
    Function.Exact (cohomologyMap S.f 1) (cohomologyMap S.g 1) :=
  sixTermLES hS

theorem etale_composableArrowsLES_exact
    {S : ShortComplex (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (cohomologyComposableArrows hS n₀ n₁ h).Exact :=
  cohomologyComposableArrows_exact hS n₀ n₁ h

noncomputable def etaleCohomologyZeroAddEquivHom
    (F : Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}) :
    EtaleH F 0 ≃+ (constIntSheaf Scheme.etaleTopology.{u} ⟶ F) :=
  cohomologyZeroAddEquivHom F

noncomputable def etaleCohomologyFunctor (n : ℕ) :
    Sheaf Scheme.etaleTopology.{u} Ab.{u + 1} ⥤ Ab.{u + 1} :=
  Sheaf.functorH Scheme.etaleTopology.{u} n

open ZeroObject in

theorem etale_gate_zero_sheaf_subsingleton (n : ℕ) :
    Subsingleton ((0 : Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}).H n) :=
  Sheaf.subsingleton_H_of_isZero (Limits.isZero_zero _) n

theorem etale_satGate_biprodSES_shortExact (F G : Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}) :
    (biprodSES F G).ShortExact :=
  biprodSES_shortExact F G

theorem etale_satGate_les_applies (F G : Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}) (n : ℕ) :
    Function.Exact (cohomologyMap (biprodSES F G).f n) (cohomologyMap (biprodSES F G).g n) :=
  etale_les_exact_two (biprodSES_shortExact F G) n

theorem etale_satGate_delta_eq_zero (F G : Sheaf Scheme.etaleTopology.{u} Ab.{u + 1})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf Scheme.etaleTopology.{u}) (biprodSES F G).X₃ n₀) :
    cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x = 0 :=
  biprodSES_delta_apply_eq_zero F G n₀ n₁ h x

end WithLocalInstances

end EtaleSite

section EtaleFppfChangeOfTopology

instance idIsContinuousEtaleFppf :
    Functor.IsContinuous (𝟭 Scheme.{u}) Scheme.etaleTopology.{u} Scheme.fppfTopology.{u} :=
  isContinuous_id_of_le Scheme.etaleTopology_le_fppfTopology

theorem isSheafEtale_of_isSheafFppf {A : Type u₂} [Category.{v₂} A]
    {P : (Scheme.{u})ᵒᵖ ⥤ A} (h : Presheaf.IsSheaf Scheme.fppfTopology.{u} P) :
    Presheaf.IsSheaf Scheme.etaleTopology.{u} P :=
  h.of_le Scheme.etaleTopology_le_fppfTopology

noncomputable def fppfSheafToEtaleSheaf :
    Sheaf Scheme.fppfTopology.{u} Ab.{u + 1} ⥤ Sheaf Scheme.etaleTopology.{u} Ab.{u + 1} :=
  sheafInclusionOfLe Scheme.etaleTopology_le_fppfTopology

@[simp]
theorem fppfSheafToEtaleSheaf_obj_obj (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :
    (fppfSheafToEtaleSheaf.{u}.obj F).obj = F.obj :=
  rfl

@[simp]
theorem fppfSheafToEtaleSheaf_map_hom {F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}}
    (φ : F ⟶ G) :
    (fppfSheafToEtaleSheaf.{u}.map φ).hom = φ.hom :=
  rfl

instance : fppfSheafToEtaleSheaf.{u}.Faithful :=
  faithful_sheafInclusionOfLe Scheme.etaleTopology_le_fppfTopology

instance : fppfSheafToEtaleSheaf.{u}.Full :=
  full_sheafInclusionOfLe Scheme.etaleTopology_le_fppfTopology

instance : fppfSheafToEtaleSheaf.{u}.Additive :=
  additive_sheafInclusionOfLe Scheme.etaleTopology_le_fppfTopology

theorem fppfSheafToEtaleSheaf_eq_pushforward :
    fppfSheafToEtaleSheaf.{u} =
      (𝟭 Scheme.{u}).sheafPushforwardContinuous Ab.{u + 1}
        Scheme.etaleTopology.{u} Scheme.fppfTopology.{u} :=
  rfl

instance constSchemeOpAdditive :
    (Functor.const (Scheme.{u})ᵒᵖ : Ab.{u + 1} ⥤ ((Scheme.{u})ᵒᵖ ⥤ Ab.{u + 1})).Additive where
  map_add := by intros; ext; rfl

instance constantSheafEtaleAdditive :
    (constantSheaf Scheme.etaleTopology.{u} Ab.{u + 1}).Additive :=
  inferInstanceAs
    (Functor.const (Scheme.{u})ᵒᵖ ⋙ presheafToSheaf Scheme.etaleTopology.{u} Ab.{u + 1}).Additive

instance constantSheafFppfAdditive :
    (constantSheaf Scheme.fppfTopology.{u} Ab.{u + 1}).Additive :=
  inferInstanceAs
    (Functor.const (Scheme.{u})ᵒᵖ ⋙ presheafToSheaf Scheme.fppfTopology.{u} Ab.{u + 1}).Additive

section WithLocalInstances

variable [HasSheafify Scheme.etaleTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1})]
  [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

noncomputable def etaleHZeroSectionsAddEquiv {T : Scheme.{u}} (hT : IsTerminal T)
    (G : Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}) :
    G.H 0 ≃+ G.obj.obj (op T) :=
  sheafHZeroSectionsAddEquiv hT G

noncomputable def fppfHZeroSectionsAddEquiv {T : Scheme.{u}} (hT : IsTerminal T)
    (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :
    F.H 0 ≃+ F.obj.obj (op T) :=
  sheafHZeroSectionsAddEquiv hT F

noncomputable def fppfToEtaleHZeroAddEquiv {T : Scheme.{u}} (hT : IsTerminal T)
    (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :
    (fppfSheafToEtaleSheaf.{u}.obj F).H 0 ≃+ F.H 0 :=
  sheafInclusionHZeroAddEquiv Scheme.etaleTopology_le_fppfTopology hT F

end WithLocalInstances

end EtaleFppfChangeOfTopology

section SpecInt

noncomputable def etaleHZeroSpecIntAddEquiv (G : Sheaf Scheme.etaleTopology.{0} Ab.{1}) :
    G.H 0 ≃+ G.obj.obj (op (Spec (CommRingCat.of ℤ))) :=
  etaleHZeroSectionsAddEquiv specZIsTerminal G

noncomputable def fppfToEtaleHZeroSpecIntAddEquiv
    (F : Sheaf Scheme.fppfTopology.{0} Ab.{1}) :
    (fppfSheafToEtaleSheaf.{0}.obj F).H 0 ≃+ F.H 0 :=
  fppfToEtaleHZeroAddEquiv specZIsTerminal F

open ZeroObject in

theorem etale_gate_specInt_H1_zero_sheaf :
    Subsingleton ((0 : Sheaf Scheme.etaleTopology.{0} Ab.{1}).H 1) :=
  etale_gate_zero_sheaf_subsingleton 1

open ZeroObject in

theorem etale_gate_H0_fires_on_zero_sheaf :
    Subsingleton
      ((0 : Sheaf Scheme.etaleTopology.{0} Ab.{1}).obj.obj
        (op (Spec (CommRingCat.of ℤ)))) :=
  have : Subsingleton ((0 : Sheaf Scheme.etaleTopology.{0} Ab.{1}).H 0) :=
    etale_gate_zero_sheaf_subsingleton 0
  (etaleHZeroSpecIntAddEquiv (0 : Sheaf Scheme.etaleTopology.{0} Ab.{1})).symm.toEquiv.subsingleton

end SpecInt

end EtaleCohomologyLES

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section GenericSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

lemma cohomologyZeroAddEquivHom_apply_eq (F : Sheaf J AddCommGrpCat.{w}) (x : F.H 0) :
    cohomologyZeroAddEquivHom F x = Ext.addEquiv₀ x := rfl

lemma cohomologyZeroAddEquivHom_symm_apply (F : Sheaf J AddCommGrpCat.{w})
    (a : constIntSheaf J ⟶ F) :
    (cohomologyZeroAddEquivHom F).symm a = Ext.mk₀ a := by
  apply (cohomologyZeroAddEquivHom F).injective
  rw [AddEquiv.apply_symm_apply, cohomologyZeroAddEquivHom_apply_eq]
  exact ((Ext.mk₀_bijective (constIntSheaf J) F).injective
    (Ext.mk₀_addEquiv₀_apply (Ext.mk₀ a))).symm

theorem cohomologyZeroAddEquivHom_naturality {F G : Sheaf J AddCommGrpCat.{w}}
    (φ : F ⟶ G) (x : F.H 0) :
    cohomologyZeroAddEquivHom G (cohomologyMap φ 0 x) =
      cohomologyZeroAddEquivHom F x ≫ φ := by
  simp only [cohomologyZeroAddEquivHom_apply_eq, cohomologyMap_apply]
  exact Ext.addEquiv₀_comp_mk₀ x φ (add_zero 0)

theorem cohomologyZeroAddEquivHom_naturality_hom {F G : Sheaf J AddCommGrpCat.{w}}
    (φ : F ⟶ G) :
    ((cohomologyZeroAddEquivHom G).toAddMonoidHom).comp (cohomologyMap φ 0) =
      (Preadditive.rightComp (constIntSheaf J) φ).comp
        (cohomologyZeroAddEquivHom F).toAddMonoidHom := by

  refine AddMonoidHom.ext fun x => ?_
  exact cohomologyZeroAddEquivHom_naturality φ x

theorem cohomologyZeroAddEquivHom_symm_naturality {F G : Sheaf J AddCommGrpCat.{w}}
    (φ : F ⟶ G) (a : constIntSheaf J ⟶ F) :
    (cohomologyZeroAddEquivHom G).symm (a ≫ φ) =
      cohomologyMap φ 0 ((cohomologyZeroAddEquivHom F).symm a) := by
  apply (cohomologyZeroAddEquivHom G).injective
  rw [AddEquiv.apply_symm_apply, cohomologyZeroAddEquivHom_naturality,
    AddEquiv.apply_symm_apply]

theorem cohomologyMap_zero_mk₀ {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    (a : constIntSheaf J ⟶ F) :
    cohomologyMap φ 0 (Ext.mk₀ a) = Ext.mk₀ (a ≫ φ) := by
  rw [cohomologyMap_apply]
  exact Ext.mk₀_comp_mk₀ a φ

theorem cohomologyMap_zero_eq_equiv_conj {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    (x : F.H 0) :
    cohomologyMap φ 0 x =
      (cohomologyZeroAddEquivHom G).symm (cohomologyZeroAddEquivHom F x ≫ φ) := by
  apply (cohomologyZeroAddEquivHom G).injective
  rw [AddEquiv.apply_symm_apply]
  exact cohomologyZeroAddEquivHom_naturality φ x

noncomputable def homPostcompAddEquiv {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) :
    (constIntSheaf J ⟶ F) ≃+ (constIntSheaf J ⟶ G) where
  toFun a := a ≫ e.hom
  invFun b := b ≫ e.inv
  left_inv a := by
    show (a ≫ e.hom) ≫ e.inv = a
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv b := by
    show (b ≫ e.inv) ≫ e.hom = b
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  map_add' a b := by
    show (a + b) ≫ e.hom = a ≫ e.hom + b ≫ e.hom
    rw [Preadditive.add_comp]

@[simp]
lemma homPostcompAddEquiv_apply {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G)
    (a : constIntSheaf J ⟶ F) :
    homPostcompAddEquiv e a = a ≫ e.hom := rfl

@[simp]
lemma homPostcompAddEquiv_symm_apply {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G)
    (b : constIntSheaf J ⟶ G) :
    (homPostcompAddEquiv e).symm b = b ≫ e.inv := rfl

theorem cohomologyZeroAddEquivHom_conj_of_iso {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G)
    (y : G.H 0) :
    cohomologyZeroAddEquivHom G y =
      cohomologyZeroAddEquivHom F (cohomologyMap e.inv 0 y) ≫ e.hom := by
  rw [← cohomologyZeroAddEquivHom_naturality e.hom (cohomologyMap e.inv 0 y),
    ← cohomologyMap_comp, Iso.inv_hom_id, cohomologyMap_id]

theorem cohomologyZeroAddEquivHom_trans_of_iso {F G : Sheaf J AddCommGrpCat.{w}}
    (e : F ≅ G) :
    (cohomologyMapAddEquiv e 0).trans (cohomologyZeroAddEquivHom G) =
      (cohomologyZeroAddEquivHom F).trans (homPostcompAddEquiv e) := by

  refine AddEquiv.ext fun x => ?_
  simp only [AddEquiv.trans_apply, cohomologyMapAddEquiv_apply, homPostcompAddEquiv_apply]
  exact cohomologyZeroAddEquivHom_naturality e.hom x

theorem homPostcomp_injective_of_shortExact {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) :
    Function.Injective (fun a : constIntSheaf J ⟶ S.X₁ => a ≫ S.f) := by
  intro a b hab
  have h1 : cohomologyMap S.f 0 ((cohomologyZeroAddEquivHom S.X₁).symm a) =
      cohomologyMap S.f 0 ((cohomologyZeroAddEquivHom S.X₁).symm b) := by
    apply (cohomologyZeroAddEquivHom S.X₂).injective
    rw [cohomologyZeroAddEquivHom_naturality, cohomologyZeroAddEquivHom_naturality,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact hab
  exact (cohomologyZeroAddEquivHom S.X₁).symm.injective ((sixTermLES hS).1 h1)

theorem homPostcomp_exact_of_shortExact {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) :
    Function.Exact (fun a : constIntSheaf J ⟶ S.X₁ => a ≫ S.f)
      (fun b : constIntSheaf J ⟶ S.X₂ => b ≫ S.g) := by
  intro b
  constructor
  · intro hb
    have h1 : cohomologyMap S.g 0 ((cohomologyZeroAddEquivHom S.X₂).symm b) = 0 := by
      apply (cohomologyZeroAddEquivHom S.X₃).injective
      rw [cohomologyZeroAddEquivHom_naturality, AddEquiv.apply_symm_apply, map_zero]
      exact hb
    obtain ⟨y, hy⟩ :=
      (cohomology_exact_two hS 0 ((cohomologyZeroAddEquivHom S.X₂).symm b)).mp h1
    refine ⟨cohomologyZeroAddEquivHom S.X₁ y, ?_⟩
    show cohomologyZeroAddEquivHom S.X₁ y ≫ S.f = b
    rw [← cohomologyZeroAddEquivHom_naturality, hy, AddEquiv.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    show (a ≫ S.f) ≫ S.g = 0
    rw [Category.assoc, S.zero, comp_zero]

theorem homSections_leftExact_of_shortExact {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) :
    Function.Injective (fun a : constIntSheaf J ⟶ S.X₁ => a ≫ S.f) ∧
    Function.Exact (fun a : constIntSheaf J ⟶ S.X₁ => a ≫ S.f)
      (fun b : constIntSheaf J ⟶ S.X₂ => b ≫ S.g) :=
  ⟨homPostcomp_injective_of_shortExact hS, homPostcomp_exact_of_shortExact hS⟩

theorem satGate_h0_naturality_id (F : Sheaf J AddCommGrpCat.{w}) (x : F.H 0) :
    cohomologyZeroAddEquivHom F (cohomologyMap (𝟙 F) 0 x) =
        cohomologyZeroAddEquivHom F x ≫ 𝟙 F ∧
    cohomologyZeroAddEquivHom F (cohomologyMap (𝟙 F) 0 x) = cohomologyZeroAddEquivHom F x ∧
    cohomologyZeroAddEquivHom F x ≫ 𝟙 F = cohomologyZeroAddEquivHom F x :=
  ⟨cohomologyZeroAddEquivHom_naturality (𝟙 F) x,
    by rw [cohomologyMap_id],
    Category.comp_id _⟩

theorem satGate_h0_naturality_biprod_inl (F G : Sheaf J AddCommGrpCat.{w}) (x : F.H 0) :
    cohomologyZeroAddEquivHom (F ⊞ G) (cohomologyMap (biprod.inl : F ⟶ F ⊞ G) 0 x) =
      cohomologyZeroAddEquivHom F x ≫ biprod.inl :=
  cohomologyZeroAddEquivHom_naturality biprod.inl x

theorem satGate_h0_naturality_biprod_snd (F G : Sheaf J AddCommGrpCat.{w})
    (y : (F ⊞ G).H 0) :
    cohomologyZeroAddEquivHom G (cohomologyMap (biprod.snd : F ⊞ G ⟶ G) 0 y) =
      cohomologyZeroAddEquivHom (F ⊞ G) y ≫ biprod.snd :=
  cohomologyZeroAddEquivHom_naturality biprod.snd y

theorem satGate_h0_biprod_sections_comp_zero (F G : Sheaf J AddCommGrpCat.{w}) (x : F.H 0) :
    cohomologyZeroAddEquivHom G
        (cohomologyMap (biprod.snd : F ⊞ G ⟶ G) 0
          (cohomologyMap (biprod.inl : F ⟶ F ⊞ G) 0 x)) = 0 ∧
    cohomologyZeroAddEquivHom F x ≫ (biprod.inl : F ⟶ F ⊞ G) ≫ biprod.snd = 0 := by
  constructor
  · rw [satGate_h0_naturality_biprod_snd, satGate_h0_naturality_biprod_inl,
      Category.assoc, biprod.inl_snd, comp_zero]
  · rw [biprod.inl_snd, comp_zero]

theorem satGate_h0_conj_of_braiding (F G : Sheaf J AddCommGrpCat.{w}) (y : (G ⊞ F).H 0) :
    cohomologyZeroAddEquivHom (G ⊞ F) y =
      cohomologyZeroAddEquivHom (F ⊞ G)
          (cohomologyMap (biprod.braiding F G).inv 0 y) ≫ (biprod.braiding F G).hom :=
  cohomologyZeroAddEquivHom_conj_of_iso (biprod.braiding F G) y

theorem satGate_h0_leftExact_biprodSES (F G : Sheaf J AddCommGrpCat.{w}) :
    Function.Injective
        (fun a : constIntSheaf J ⟶ (biprodSES F G).X₁ => a ≫ (biprodSES F G).f) ∧
    Function.Exact
      (fun a : constIntSheaf J ⟶ (biprodSES F G).X₁ => a ≫ (biprodSES F G).f)
      (fun b : constIntSheaf J ⟶ (biprodSES F G).X₂ => b ≫ (biprodSES F G).g) :=
  homSections_leftExact_of_shortExact (biprodSES_shortExact F G)

theorem satGate_zero_injective_recovered {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    [Mono φ] :
    Function.Injective (cohomologyMap φ 0) := by
  intro x y hxy
  apply (cohomologyZeroAddEquivHom F).injective
  have h : cohomologyZeroAddEquivHom F x ≫ φ = cohomologyZeroAddEquivHom F y ≫ φ := by
    rw [← cohomologyZeroAddEquivHom_naturality, ← cohomologyZeroAddEquivHom_naturality, hxy]
  exact (cancel_mono φ).mp h

end GenericSite

section FppfSite

open AlgebraicGeometry

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

theorem fppf_h0_identification_naturality
    {F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}} (φ : F ⟶ G) (x : FppfH F 0) :
    fppfCohomologyZeroAddEquivHom G (cohomologyMap φ 0 x) =
      fppfCohomologyZeroAddEquivHom F x ≫ φ :=
  cohomologyZeroAddEquivHom_naturality φ x

theorem fppf_h0_identification_naturality_hom
    {F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}} (φ : F ⟶ G) :
    ((fppfCohomologyZeroAddEquivHom G).toAddMonoidHom).comp (cohomologyMap φ 0) =
      (Preadditive.rightComp (constIntSheaf Scheme.fppfTopology.{u}) φ).comp
        (fppfCohomologyZeroAddEquivHom F).toAddMonoidHom :=
  cohomologyZeroAddEquivHom_naturality_hom φ

theorem fppf_h0_identification_symm_naturality
    {F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}} (φ : F ⟶ G)
    (a : constIntSheaf Scheme.fppfTopology.{u} ⟶ F) :
    (fppfCohomologyZeroAddEquivHom G).symm (a ≫ φ) =
      cohomologyMap φ 0 ((fppfCohomologyZeroAddEquivHom F).symm a) :=
  cohomologyZeroAddEquivHom_symm_naturality φ a

theorem fppf_h0_identification_conj_of_iso
    {F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}} (e : F ≅ G) (y : FppfH G 0) :
    fppfCohomologyZeroAddEquivHom G y =
      fppfCohomologyZeroAddEquivHom F (cohomologyMap e.inv 0 y) ≫ e.hom :=
  cohomologyZeroAddEquivHom_conj_of_iso e y

theorem fppf_homSections_leftExact
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})} (hS : S.ShortExact) :
    Function.Injective
        (fun a : constIntSheaf Scheme.fppfTopology.{u} ⟶ S.X₁ => a ≫ S.f) ∧
    Function.Exact
      (fun a : constIntSheaf Scheme.fppfTopology.{u} ⟶ S.X₁ => a ≫ S.f)
      (fun b : constIntSheaf Scheme.fppfTopology.{u} ⟶ S.X₂ => b ≫ S.g) :=
  homSections_leftExact_of_shortExact hS

theorem fppf_satGate_h0_naturality_id (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})
    (x : FppfH F 0) :
    fppfCohomologyZeroAddEquivHom F (cohomologyMap (𝟙 F) 0 x) =
        fppfCohomologyZeroAddEquivHom F x ≫ 𝟙 F ∧
    fppfCohomologyZeroAddEquivHom F (cohomologyMap (𝟙 F) 0 x) =
        fppfCohomologyZeroAddEquivHom F x ∧
    fppfCohomologyZeroAddEquivHom F x ≫ 𝟙 F = fppfCohomologyZeroAddEquivHom F x :=
  satGate_h0_naturality_id F x

theorem fppf_satGate_h0_biprod_inl (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})
    (x : FppfH F 0) :
    fppfCohomologyZeroAddEquivHom (F ⊞ G)
        (cohomologyMap (biprod.inl : F ⟶ F ⊞ G) 0 x) =
      fppfCohomologyZeroAddEquivHom F x ≫ biprod.inl :=
  satGate_h0_naturality_biprod_inl F G x

theorem fppf_satGate_h0_sections_comp_zero (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})
    (x : FppfH F 0) :
    fppfCohomologyZeroAddEquivHom G
        (cohomologyMap (biprod.snd : F ⊞ G ⟶ G) 0
          (cohomologyMap (biprod.inl : F ⟶ F ⊞ G) 0 x)) = 0 ∧
    fppfCohomologyZeroAddEquivHom F x ≫ (biprod.inl : F ⟶ F ⊞ G) ≫ biprod.snd = 0 :=
  satGate_h0_biprod_sections_comp_zero F G x

theorem fppf_satGate_zero_injective_recovered
    {F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}} (φ : F ⟶ G) [Mono φ] :
    Function.Injective (cohomologyMap φ 0) :=
  satGate_zero_injective_recovered φ

end WithLocalInstances

end FppfSite

end FppfCohomologyLES


