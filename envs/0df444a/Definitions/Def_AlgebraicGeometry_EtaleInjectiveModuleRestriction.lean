-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleInjectiveModuleRestriction
-- name    : AlgebraicGeometry_EtaleInjectiveModuleRestriction
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-24T22:57:55.226878+00:00
-- url     : https://prove2.me/theorems/e1dea09f-233d-499e-aaa4-4630a741b48e
-- title:
--   Étale restriction and cohomology of injective module sheaves
-- statement:
--   Restriction along an étale morphism preserves injective module sheaves. The underlying abelian sheaf of an injective module sheaf has vanishing positive-degree étale cohomology.
-- source:
--   Stacks Project, Lemma 59.82.8, https://stacks.math.columbia.edu/tag/0A51.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Module.ZMod
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.Pullback

set_option maxHeartbeats 1600000

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)


namespace PhilipponEtaleSkyscraperAcyclicity

universe u

private abbrev Ab := AddCommGrpCat.{u}

private theorem epi_pi_map {I : Type u} {M N : I → Ab.{u}} (a : ∀ i, M i ⟶ N i)
    (ha : ∀ i, Epi (a i)) : Epi (Limits.Pi.map a) := by
  let b : Discrete.functor M ⟶ Discrete.functor N := Discrete.natTrans (fun i => a i.as)
  have : Epi b := (NatTrans.epi_iff_epi_app _).mpr (fun i => ha i.as)
  change Epi ((lim (J := Discrete I) (C := Ab.{u})).map b)
  exact preserves_epi_of_preservesColimit lim b

variable {X : Scheme.{u}} (Φ : X.smallEtaleTopology.Point.{u})

private abbrev skyscraper := Φ.skyscraperSheafFunctor (A := Ab.{u})

/-- A map of skyscraper sheaves induced by a surjection of coefficients
is surjective on every étale chart. -/
theorem skyscraper_app_epi {M N : Ab.{u}} (a : M ⟶ N) [Epi a] (W : X.Etaleᵒᵖ) :
    Epi (((skyscraper Φ).map a).hom.app W) :=
  epi_pi_map (fun _ : Φ.fiber.obj W.unop => a) (fun _ => inferInstance)

/-- A family of surjections on coefficients induces a surjection on each
chart after taking the product of the associated skyscraper sheaves. -/
theorem product_skyscraper_app_epi {I : Type u} (points : I → X.smallEtaleTopology.Point.{u})
    {M N : I → Ab.{u}} (a : ∀ i, M i ⟶ N i) (ha : ∀ i, Epi (a i)) (W : X.Etaleᵒᵖ) :
    Epi ((Limits.Pi.map (fun i => (skyscraper (points i)).map (a i))).hom.app W) := by
  let F := sheafToPresheaf X.smallEtaleTopology Ab.{u} ⋙ (evaluation _ _).obj W
  have : PreservesLimitsOfShape (Discrete I) F := comp_preservesLimitsOfShape _ _
  let S (i : I) := (skyscraper (points i)).obj (M i)
  let T (i : I) := (skyscraper (points i)).obj (N i)
  let f (i : I) : S i ⟶ T i := (skyscraper (points i)).map (a i)
  let eS := PreservesProduct.iso F S
  let eT := PreservesProduct.iso F T
  have h : F.map (Limits.Pi.map f) ≫ eT.hom = eS.hom ≫ Limits.Pi.map (fun i => F.map (f i)) := by
    apply Pi.hom_ext
    intro i
    simp only [eS, eT, Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π,
      piComparison_comp_π_assoc, Pi.map_π, ← F.map_comp]
  have : Epi (Limits.Pi.map (fun i => F.map (f i))) := epi_pi_map _ (fun i => by
    let : Epi (a i) := ha i
    exact skyscraper_app_epi (points i) (a i) W)
  change Epi (F.map (Limits.Pi.map f))
  apply (epi_comp_iff_of_isIso _ eT.hom).mp
  rw [h]
  infer_instance

/-- Skyscraper sheaves at a point of the étale site are exact in their
abelian coefficient group. -/
theorem preservesFiniteColimits : PreservesFiniteColimits (skyscraper Φ) := by
  let R := skyscraper Φ
  have : R.Additive := Functor.additive_of_preserves_binary_products R
  have : R.PreservesEpimorphisms := by
    constructor
    intro M N a _
    have : Epi ((R.map a).hom) :=
      (NatTrans.epi_iff_epi_app _).mpr (skyscraper_app_epi Φ a)
    exact Sheaf.Hom.epi_of_presheaf_epi (J := X.smallEtaleTopology) (A := Ab.{u}) (R.map a)
  have : R.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels R
  exact Functor.preservesFiniteColimits_of_preservesHomology R

variable {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X)

/-- The global sections of a skyscraper sheaf are its coefficient group. -/
def skyscraperGlobalSectionsIso :
    skyscraper (Scheme.pointSmallEtale s) ⋙ globalSections X ≅ 𝟭 Ab.{u} := by
  let T := Scheme.Etale.mk (𝟙 X)
  let I := (Scheme.pointSmallEtale s).fiber.obj T
  let t : I := Over.homMk s (Category.comp_id _)
  have ht (x : I) : x = t := by
    apply Over.OverMorphism.ext
    exact (Category.comp_id x.left).symm.trans (Over.w x)
  refine NatIso.ofComponents (fun M => ?_) (fun a => ?_)
  · refine ⟨Pi.π (fun _ : I => M) t, Pi.lift (fun _ : I => 𝟙 M), ?_, ?_⟩
    · apply Pi.hom_ext
      intro x
      rw [Category.assoc, Pi.lift_π]
      change Pi.π (fun _ : I => M) t ≫ 𝟙 M =
        𝟙 (∏ᶜ fun _ : I => M) ≫ Pi.π (fun _ : I => M) x
      rw [Category.comp_id, Category.id_comp, ht x]
    · exact Pi.lift_π (fun _ : I => 𝟙 M) t
  · exact Pi.map_π (fun _ : I => a) t

/-- A skyscraper sheaf at a geometric point has trivial positive étale
cohomology, with any abelian coefficient group. -/
theorem skyscraper_H_succ (M : Ab.{u}) (q : ℕ) :
    Subsingleton (((skyscraper (Scheme.pointSmallEtale s)).obj M).H (q + 1)) := by
  let Φ := Scheme.pointSmallEtale s
  let R := skyscraper Φ
  let Γ := globalSections X
  let : Γ.Additive := ⟨fun {_ _} _ _ => rfl⟩
  let : R.Additive := Functor.additive_of_preserves_binary_products R
  let : PreservesFiniteColimits R := preservesFiniteColimits Φ
  let : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      Φ.skyscraperSheafAdjunction
  let I := injectiveResolution M
  have hR (k : ℕ) : IsZero ((R.rightDerived (k + 1)).obj M) := by
    let L := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    have hL : L.ExactAt (k + 1) :=
      (show (I.cocomplex.sc (k + 1)).Exact from I.cocomplex_exactAt_succ k).map R
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hL).of_iso
      (I.isoRightDerivedObj R (k + 1))
  let J := PhilipponDerivedAdjunction.mapInjectiveResolution R I hR
  let H := HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℕ) (q + 1)
  let e := (NatIso.mapHomologicalComplex (skyscraperGlobalSectionsIso s) (ComplexShape.up ℕ) ≪≫
    Functor.mapHomologicalComplexIdIso Ab.{u} (ComplexShape.up ℕ)).app I.cocomplex
  have h0 : IsZero (H.obj I.cocomplex) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (I.cocomplex_exactAt_succ q)
  have h1 : IsZero (H.obj ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex)) :=
    h0.of_iso (H.mapIso e)
  let c := PhilipponEtaleDerivedSections.cohomologyEquivResolution (R.obj M) J (q + 1)
  exact ⟨fun a b => c.injective ((AddCommGrpCat.subsingleton_of_isZero h1).elim (c a) (c b))⟩

end PhilipponEtaleSkyscraperAcyclicity

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks (geometricMap geometricPoint)
open PhilipponEtaleSkyscraperAcyclicity (product_skyscraper_app_epi skyscraperGlobalSectionsIso)


namespace PhilipponEtaleSkyscraperProducts

universe u

private abbrev Ab := AddCommGrpCat.{u}
private abbrev Sh (X : Scheme.{u}) := Sheaf X.smallEtaleTopology Ab.{u}

variable {X : Scheme.{u}} {I : Type u} (points : I → X)

private abbrev Φ (i : I) := geometricPoint (points i)

private abbrev coefficients (I : Type u) := Discrete I ⥤ Ab.{u}

private abbrev adj (i : I) := (Φ points i).skyscraperSheafAdjunction (A := Ab.{u})

/-- The family of geometric stalks of a sheaf. -/
def stalks : Sh X ⥤ coefficients I where
  obj F := Discrete.functor (fun i => ((Φ points i).sheafFiber (A := Ab.{u})).obj F)
  map a := Discrete.natTrans (fun i => ((Φ points i.as).sheafFiber (A := Ab.{u})).map a)
  map_id F := by
    apply NatTrans.ext
    funext i
    exact ((Φ points i.as).sheafFiber (A := Ab.{u})).map_id F
  map_comp a b := by
    apply NatTrans.ext
    funext i
    exact ((Φ points i.as).sheafFiber (A := Ab.{u})).map_comp a b

private abbrev skyscrapers (M : coefficients I) (i : I) :=
  (Φ points i).skyscraperSheaf (M.obj ⟨i⟩)

/-- The product of the geometric skyscraper sheaves of a family of abelian groups. -/
def product : coefficients I ⥤ Sh X where
  obj M := ∏ᶜ skyscrapers points M
  map a := Limits.Pi.map (fun i => (Φ points i).skyscraperSheafFunctor.map (a.app ⟨i⟩))
  map_id M := by
    let S := skyscrapers points M
    have h : (fun i : I => (Φ points i).skyscraperSheafFunctor.map (𝟙 (M.obj ⟨i⟩))) =
        fun i => 𝟙 (S i) := funext fun i => (Φ points i).skyscraperSheafFunctor.map_id _
    exact (congrArg Limits.Pi.map h).trans Limits.Pi.map_id
  map_comp a b := by
    simp only [NatTrans.comp_app, Functor.map_comp]
    exact (Limits.Pi.map_comp_map _ _).symm

/-- The product of skyscraper sheaves is right adjoint to the family of stalks. -/
def productAdjunction : stalks points ⊣ product points :=
  Adjunction.mkOfHomEquiv
    { homEquiv F M :=
        { toFun := fun a => Pi.lift (fun i => (adj points i).homEquiv F (M.obj ⟨i⟩) (a.app ⟨i⟩))
          invFun := fun b => Discrete.natTrans (fun i =>
            ((adj points i.as).homEquiv F (M.obj i)).symm (b ≫ Pi.π _ i.as))
          left_inv := by
            intro a
            apply NatTrans.ext
            funext i
            change ((adj points i.as).homEquiv F (M.obj i)).symm
              (Pi.lift (fun j => (adj points j).homEquiv F (M.obj ⟨j⟩) (a.app ⟨j⟩)) ≫
                Pi.π _ i.as) = a.app i
            rw [Pi.lift_π]
            cases i
            exact Equiv.symm_apply_apply _ _
          right_inv := by
            intro b
            apply Pi.hom_ext
            intro i
            exact (Pi.lift_π _ _).trans (Equiv.apply_symm_apply _ _) }
      homEquiv_naturality_left_symm a b := by
        apply NatTrans.ext
        funext i
        exact (congrArg (((adj points i.as).homEquiv _ _).symm) (Category.assoc _ _ _)).trans
          ((adj points i.as).homEquiv_naturality_left_symm _ _)
      homEquiv_naturality_right {K M N} a b := by
        apply Pi.hom_ext
        intro i
        change Pi.lift (fun j => (adj points j).homEquiv K (N.obj ⟨j⟩) ((a ≫ b).app ⟨j⟩)) ≫
            Pi.π (skyscrapers points N) i =
          (Pi.lift (fun j => (adj points j).homEquiv K (M.obj ⟨j⟩) (a.app ⟨j⟩)) ≫
            Limits.Pi.map (fun j => (Φ points j).skyscraperSheafFunctor.map (b.app ⟨j⟩))) ≫
            Pi.π (skyscrapers points N) i
        simp only [Category.assoc, Pi.lift_π, Pi.map_π, Pi.lift_π_assoc, NatTrans.comp_app]
        exact (adj points i).homEquiv_naturality_right _ _ }

/-- Taking a product of geometric skyscraper sheaves is exact in the
family of abelian coefficient groups. -/
theorem product_preservesFiniteColimits : PreservesFiniteColimits (product points) := by
  let R := product points
  have : R.IsRightAdjoint := (productAdjunction points).isRightAdjoint
  have : R.Additive := Functor.additive_of_preserves_binary_products R
  have : R.PreservesEpimorphisms := by
    constructor
    intro M N a ha
    have h (i : I) : Epi (a.app ⟨i⟩) := (NatTrans.epi_iff_epi_app _).mp ha ⟨i⟩
    have : Epi ((R.map a).hom) :=
      (NatTrans.epi_iff_epi_app _).mpr
        (product_skyscraper_app_epi (Φ points) (fun i => a.app ⟨i⟩) h)
    exact Sheaf.Hom.epi_of_presheaf_epi (J := X.smallEtaleTopology) (A := Ab.{u}) (R.map a)
  have : R.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels R
  exact Functor.preservesFiniteColimits_of_preservesHomology R

private def sectionsIso : product points ⋙ globalSections X ≅ lim (J := Discrete I) (C := Ab.{u}) := by
  let Γ := globalSections X
  let U := Scheme.Etale.mk (𝟙 X)
  have : PreservesLimitsOfShape (Discrete I) Γ :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete I)
      (sheafToPresheaf X.smallEtaleTopology Ab.{u} ⋙ (evaluation _ _).obj (op U)))
  let σ (M : coefficients I) (i : I) : Γ.obj (skyscrapers points M i) ≅ M.obj ⟨i⟩ :=
    (skyscraperGlobalSectionsIso (geometricMap (points i))).app (M.obj ⟨i⟩)
  let e (M : coefficients I) : Γ.obj (∏ᶜ skyscrapers points M) ≅ limit M :=
    PreservesProduct.iso Γ (skyscrapers points M) ≪≫ Limits.Pi.mapIso (σ M) ≪≫ Pi.isoLimit M
  have he (M : coefficients I) (i : I) :
      (e M).hom ≫ limit.π M ⟨i⟩ = Γ.map (Pi.π (skyscrapers points M) i) ≫ (σ M i).hom := by
    simp only [e, Iso.trans_hom, Category.assoc, Pi.isoLimit_hom_π, Pi.mapIso_hom_π,
      PreservesProduct.iso_hom, piComparison_comp_π_assoc]
  refine NatIso.ofComponents e (fun {M N} a => ?_)
  apply limit.hom_ext
  rintro ⟨i⟩
  change (Γ.map (Limits.Pi.map (fun j => (Φ points j).skyscraperSheafFunctor.map (a.app ⟨j⟩))) ≫
      (e N).hom) ≫ limit.π N ⟨i⟩ = ((e M).hom ≫ limMap a) ≫ limit.π N ⟨i⟩
  rw [Category.assoc, he, ← Γ.map_comp_assoc, Pi.map_π, Γ.map_comp, Category.assoc,
    Category.assoc, limMap_π]
  have hσ : Γ.map ((Φ points i).skyscraperSheafFunctor.map (a.app ⟨i⟩)) ≫ (σ N i).hom =
      (σ M i).hom ≫ a.app ⟨i⟩ :=
    (skyscraperGlobalSectionsIso (geometricMap (points i))).hom.naturality (a.app ⟨i⟩)
  calc
    _ = Γ.map (Pi.π (skyscrapers points M) i) ≫ ((σ M i).hom ≫ a.app ⟨i⟩) := by
      simpa only [Category.assoc] using congrArg (Γ.map (Pi.π (skyscrapers points M) i) ≫ ·) hσ
    _ = _ := by
      simpa only [Category.assoc] using congrArg (· ≫ a.app ⟨i⟩) (he M i).symm

private instance : EnoughInjectives (coefficients I) where
  presentation M := by
    let J := Discrete.functor (fun i : I => Injective.under (M.obj ⟨i⟩))
    have (i : Discrete I) : Injective (J.obj i) :=
      inferInstanceAs (Injective (Injective.under (M.obj ⟨i.as⟩)))
    let b : M ⟶ J := Discrete.natTrans (fun i => Injective.ι (M.obj i))
    have hJ : Injective J := by
      constructor
      intro A B g f hf
      have (i : Discrete I) : Mono (f.app i) := (NatTrans.mono_iff_mono_app _).mp hf i
      let r : B ⟶ J := Discrete.natTrans (fun i => Injective.factorThru (g.app i) (f.app i))
      refine ⟨r, ?_⟩
      apply NatTrans.ext
      funext i
      exact Injective.comp_factorThru (g.app i) (f.app i)
    exact ⟨⟨J, hJ, b, (NatTrans.mono_iff_mono_app _).mpr (fun i => Injective.ι_mono (M.obj i))⟩⟩

/-- Arbitrary small products of geometric skyscraper sheaves have zero
positive étale cohomology. -/
theorem product_H_succ (M : coefficients I) (q : ℕ) :
    Subsingleton (((product points).obj M).H (q + 1)) := by
  let R := product points
  let Γ := globalSections X
  let G := lim (J := Discrete I) (C := Ab.{u})
  let : R.IsRightAdjoint := (productAdjunction points).isRightAdjoint
  let : Γ.Additive := ⟨fun {_ _} _ _ => rfl⟩
  let : R.Additive := Functor.additive_of_preserves_binary_products R
  let : G.Additive := Functor.additive_of_preserves_binary_products G
  let : PreservesFiniteColimits R := product_preservesFiniteColimits points
  let : (stalks points).PreservesMonomorphisms := by
    constructor
    intro A B f _
    exact (NatTrans.mono_iff_mono_app _).mpr (fun i =>
      inferInstanceAs (Mono (((Φ points i.as).sheafFiber (A := Ab.{u})).map f)))
  let : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (productAdjunction points)
  let J := injectiveResolution M
  have hf (k : ℕ) : IsZero ((R.rightDerived (k + 1)).obj M) := by
    let K := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    have hK : K.ExactAt (k + 1) :=
      (show (J.cocomplex.sc (k + 1)).Exact from J.cocomplex_exactAt_succ k).map R
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hK).of_iso
      (J.isoRightDerivedObj R (k + 1))
  let J' := PhilipponDerivedAdjunction.mapInjectiveResolution R J hf
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  have hK : K.ExactAt (q + 1) :=
    (show (J.cocomplex.sc (q + 1)).Exact from J.cocomplex_exactAt_succ q).map G
  let H := HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℕ) (q + 1)
  let e := (NatIso.mapHomologicalComplex (sectionsIso points) (ComplexShape.up ℕ)).app J.cocomplex
  have hZ : IsZero (H.obj ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj J'.cocomplex)) :=
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hK).of_iso (H.mapIso e)
  let c := PhilipponEtaleDerivedSections.cohomologyEquivResolution (R.obj M) J' (q + 1)
  exact ⟨fun a b => c.injective ((AddCommGrpCat.subsingleton_of_isZero hZ).elim (c a) (c b))⟩

/-- Products of geometric skyscraper sheaves are acyclic for étale direct
image along any scheme morphism. -/
theorem isZero_higherDirectImage_product {Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficients I) (q : ℕ) :
    IsZero (((pushforward f).rightDerived (q + 1)).obj ((product points).obj M)) := by
  let R := product points
  let D := pushforward f
  let : R.IsRightAdjoint := (productAdjunction points).isRightAdjoint
  let : R.Additive := Functor.additive_of_preserves_binary_products R
  let : PreservesFiniteColimits R := product_preservesFiniteColimits points
  let : (stalks points).PreservesMonomorphisms := by
    constructor
    intro A B a _
    exact (NatTrans.mono_iff_mono_app _).mpr (fun i =>
      inferInstanceAs (Mono (((Φ points i.as).sheafFiber (A := Ab.{u})).map a)))
  let : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (productAdjunction points)
  let P := R ⋙ D
  let : P.PreservesEpimorphisms := by
    constructor
    intro A B a ha
    have : Epi (P.map a).hom := by
      apply (NatTrans.epi_iff_epi_app _).mpr
      intro W
      change Epi ((R.map a).hom.app (op ((baseChange f).obj W.unop)))
      exact product_skyscraper_app_epi (Φ points) (fun i => a.app ⟨i⟩)
        (fun i => (NatTrans.epi_iff_epi_app _).mp ha ⟨i⟩) _
    exact Sheaf.Hom.epi_of_presheaf_epi (J := Y.smallEtaleTopology) (A := Ab.{u}) (P.map a)
  let : P.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels P
  let : PreservesFiniteColimits P := Functor.preservesFiniteColimits_of_preservesHomology P
  let J := injectiveResolution M
  have hR (k : ℕ) : IsZero ((R.rightDerived (k + 1)).obj M) := by
    apply IsZero.of_iso _ (J.isoRightDerivedObj R (k + 1))
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    exact (show (J.cocomplex.sc (k + 1)).Exact from J.cocomplex_exactAt_succ k).map R
  let J' := PhilipponDerivedAdjunction.mapInjectiveResolution R J hR
  let c := ComplexShape.up ℕ
  let H := HomologicalComplex.homologyFunctor (Sh Y) c (q + 1)
  let e := (Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ D)) c).app J.cocomplex
  refine IsZero.of_iso ?_ (J'.isoRightDerivedObj D (q + 1) ≪≫ H.mapIso e)
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
  exact (show (J.cocomplex.sc (q + 1)).Exact from J.cocomplex_exactAt_succ q).map P

end PhilipponEtaleSkyscraperProducts

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks (geometricPoint)


namespace PhilipponEtaleModuleSkyscrapers

universe u

variable {X : Scheme.{u}} {R : Type u} [Ring R]

private abbrev Modules := Sheaf X.smallEtaleTopology (ModuleCat.{u} R)

private abbrev stalk (x : X) := (geometricPoint x).sheafFiber (A := ModuleCat.{u} R)

private abbrev stalkAdjunction (x : X) :=
  (geometricPoint x).skyscraperSheafAdjunction (A := ModuleCat.{u} R)

private abbrev stalkSheaf (F : Modules (X := X) (R := R)) (x : X) :=
  (geometricPoint x).skyscraperSheaf ((stalk (R := R) x).obj F)

/-- The product of skyscraper sheaves of all the geometric stalks of a sheaf
of modules. -/
def pointProduct (F : Modules (X := X) (R := R)) : Modules (X := X) (R := R) :=
  ∏ᶜ stalkSheaf F

/-- The unit maps of the stalk-skyscraper adjunctions give a canonical
map into the product of geometric skyscrapers. -/
def toPointProduct (F : Modules (X := X) (R := R)) : F ⟶ pointProduct F :=
  Pi.lift fun x => (stalkAdjunction (R := R) x).unit.app F

private theorem mono_map_toPointProduct (F : Modules (X := X) (R := R)) (x : X) :
    Mono ((stalk (R := R) x).map (toPointProduct F)) := by
  let L := stalk (R := R) x
  let adj := stalkAdjunction (R := R) x
  have h : L.map (toPointProduct F) ≫
      (L.map (Pi.π (stalkSheaf F) x) ≫ adj.counit.app (L.obj F)) = 𝟙 (L.obj F) := by
    rw [← Category.assoc, ← L.map_comp, toPointProduct, Pi.lift_π]
    exact adj.left_triangle_components F
  exact mono_of_mono_fac h

/-- The geometric skyscraper product contains the original module sheaf as
a subobject. -/
theorem mono_toPointProduct (F : Modules (X := X) (R := R)) : Mono (toPointProduct F) := by
  let P : ObjectProperty (X.smallEtaleTopology.Point.{u}) :=
    ObjectProperty.ofObj (fun x : X => geometricPoint x)
  have hP : P.IsConservativeFamilyOfPoints := Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  let : ∀ Φ : P.FullSubcategory,
      Mono ((Φ.obj.sheafFiber (A := ModuleCat.{u} R)).map (toPointProduct F)) := by
    intro Φ
    have h := Φ.property
    change ObjectProperty.ofObj (fun x : X => geometricPoint x) Φ.obj at h
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp h
    rw [← hx]
    exact mono_map_toPointProduct F x
  exact (hP.jointlyReflectMonomorphisms (ModuleCat.{u} R)).mono (toPointProduct F)

/-- An injective étale sheaf of modules is a retract of its geometric
skyscraper product. -/
theorem exists_retraction (F : Modules (X := X) (R := R)) [Injective F] :
    ∃ r : pointProduct F ⟶ F, toPointProduct F ≫ r = 𝟙 F := by
  let : Mono (toPointProduct F) := mono_toPointProduct F
  exact ⟨Injective.factorThru (𝟙 F) (toPointProduct F), Injective.comp_factorThru _ _⟩

private abbrev forgetModule := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

private instance : X.smallEtaleTopology.HasSheafCompose (forgetModule (R := R)) where
  isSheaf P hP := by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat.{u})
    exact Presheaf.isSheaf_comp_of_isSheaf _ P (CategoryTheory.forget (ModuleCat.{u} R)) hP

/-- Forget the module structure of an étale sheaf. -/
abbrev underlying : Modules (X := X) (R := R) ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  sheafCompose X.smallEtaleTopology (forgetModule (R := R))

/-- Forgetting module structure preserves epimorphisms of étale sheaves. -/
theorem underlying_map_epi {F G : Modules (X := X) (R := R)}
    (a : F ⟶ G) [Epi a] : Epi (underlying.map a) := by
  let P : ObjectProperty (X.smallEtaleTopology.Point.{u}) :=
    ObjectProperty.ofObj (fun x : X => geometricPoint x)
  have hP : P.IsConservativeFamilyOfPoints := Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  let : ∀ Φ : P.FullSubcategory,
      Epi ((Φ.obj.sheafFiber (A := AddCommGrpCat.{u})).map (underlying.map a)) := by
    intro Φ
    let L := Φ.obj.sheafFiber (A := ModuleCat.{u} R)
    let U := forgetModule (R := R)
    let e := Φ.obj.sheafFiberCompIso U
    have : Epi (L.map a) := Functor.map_epi L a
    have : Epi (U.map (L.map a)) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    change Epi (((underlying ⋙ Φ.obj.sheafFiber (A := AddCommGrpCat.{u}))).map a)
    apply (epi_comp_iff_of_isIso _ (e.hom.app G)).mp
    rw [e.hom.naturality a]
    exact epi_comp (e.hom.app F) (U.map (L.map a))
  exact (hP.jointlyReflectEpimorphisms AddCommGrpCat.{u}).epi (underlying.map a)

/-- Forgetting module structure preserves finite limits of étale sheaves. -/
theorem underlying_preservesFiniteLimits :
    PreservesFiniteLimits (underlying (X := X) (R := R)) := by
  let U := forgetModule (R := R)
  let F := underlying (X := X) (R := R)
  let S := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let T := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} R)
  have : PreservesFiniteLimits (F ⋙ S) :=
    inferInstanceAs (PreservesFiniteLimits
      (T ⋙ (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj U))
  exact preservesFiniteLimits_of_reflects_of_preserves F S

/-- Forgetting module structure preserves finite colimits. This can be
checked at the geometric stalks, where it is the forgetful functor on modules. -/
theorem underlying_preservesFiniteColimits :
    PreservesFiniteColimits (underlying (X := X) (R := R)) := by
  let U := forgetModule (R := R)
  let F := underlying (X := X) (R := R)
  let P : ObjectProperty (X.smallEtaleTopology.Point.{u}) :=
    ObjectProperty.ofObj (fun x : X => geometricPoint x)
  have hP : P.IsConservativeFamilyOfPoints := Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  let C (Φ : P.FullSubcategory) := Φ.obj.sheafFiber (A := AddCommGrpCat.{u})
  constructor
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  have (Φ : P.FullSubcategory) : PreservesColimit (K ⋙ F) (C Φ) := by
    dsimp [C]
    infer_instance
  refine ⟨(hP.jointlyReflectIsomorphisms AddCommGrpCat.{u}).jointlyReflectsColimit
    (c := F.mapCocone c) ?_⟩
  intro Φ
  let e := Φ.obj.sheafFiberCompIso U
  have : PreservesColimitsOfShape J (F ⋙ C Φ) :=
    preservesColimitsOfShape_of_natIso e.symm
  change IsColimit ((F ⋙ C Φ).mapCocone c)
  exact isColimitOfPreserves (F ⋙ C Φ) hc

/-- The underlying abelian sheaf of a module skyscraper is the skyscraper
of its underlying abelian group. -/
def underlyingSkyscraperIso (Φ : X.smallEtaleTopology.Point.{u}) (M : ModuleCat.{u} R) :
    underlying.obj (Φ.skyscraperSheaf M) ≅ Φ.skyscraperSheaf ((forgetModule (R := R)).obj M) := by
  let U := forgetModule (R := R)
  let Q (W : X.Etaleᵒᵖ) (_ : Φ.fiber.obj W.unop) := M
  let T (W : X.Etaleᵒᵖ) (v : Φ.fiber.obj W.unop) := U.obj (Q W v)
  apply (fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
  refine NatIso.ofComponents (fun W => PreservesProduct.iso U (Q W)) ?_
  intro W V a
  apply Pi.hom_ext
  intro x
  let k := Φ.fiber.map a.unop
  change (U.map (Limits.Pi.map' (f := Q W) (g := Q V) k (fun v => 𝟙 (Q V v))) ≫
      piComparison U (Q V)) ≫ Pi.π (T V) x =
    (piComparison U (Q W) ≫ Limits.Pi.map' (f := T W) (g := T V) k (fun v => 𝟙 (T V v))) ≫
      Pi.π (T V) x
  rw [Category.assoc, Category.assoc, piComparison_comp_π, ← U.map_comp,
    Pi.map'_comp_π, Category.comp_id, Pi.map'_comp_π, Category.comp_id]
  exact (piComparison_comp_π U (Q W) (k x)).symm

/-- Forgetting the coefficient module commutes with the product of
geometric skyscraper sheaves. -/
def underlyingPointProductIso (F : Modules (X := X) (R := R)) :
    underlying.obj (pointProduct F) ≅
      ∏ᶜ fun x : X => (geometricPoint x).skyscraperSheaf
        ((forgetModule (R := R)).obj ((stalk (R := R) x).obj F)) := by
  let U := forgetModule (R := R)
  let Mod := ModuleCat.{u} R
  let Ab := AddCommGrpCat.{u}
  let S := sheafToPresheaf X.smallEtaleTopology Ab
  let T := sheafToPresheaf X.smallEtaleTopology Mod
  let G := underlying (X := X) (R := R)
  have : PreservesLimitsOfShape (Discrete X) (G ⋙ S) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete X)
      (T ⋙ (Functor.whiskeringRight X.Etaleᵒᵖ Mod Ab).obj U))
  have : PreservesLimitsOfShape (Discrete X) G :=
    preservesLimitsOfShape_of_reflects_of_preserves G S
  exact PreservesProduct.iso G (stalkSheaf F) ≪≫
    Pi.mapIso (fun x => underlyingSkyscraperIso (geometricPoint x) ((stalk (R := R) x).obj F))

/-- Acyclicity of the abelian skyscraper product implies acyclicity in the
same degree for the underlying abelian sheaf of an injective module sheaf. -/
theorem underlying_H_subsingleton_of_pointProduct (F : Modules (X := X) (R := R)) [Injective F]
    (q : ℕ) (h : Subsingleton ((∏ᶜ fun x : X => (geometricPoint x).skyscraperSheaf
      ((forgetModule (R := R)).obj ((stalk (R := R) x).obj F))).H q)) :
    Subsingleton ((underlying.obj F).H q) := by
  obtain ⟨r, hr⟩ := exists_retraction F
  let G := underlying (X := X) (R := R)
  let e := underlyingPointProductIso F
  let a := G.map (toPointProduct F) ≫ e.hom
  let b := e.inv ≫ G.map r
  have hab : a ≫ b = 𝟙 (G.obj F) := by
    dsimp only [a, b]
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp, hr, G.map_id]
  refine ⟨fun x y => ?_⟩
  have he := congrArg (Sheaf.H.map b q) (h.elim (Sheaf.H.map a q x) (Sheaf.H.map a q y))
  simpa only [← Sheaf.H.map_comp_apply, hab, Sheaf.H.map_id_apply] using he

/-- The underlying abelian sheaf of an injective étale module sheaf is
acyclic for global sections. -/
theorem underlying_H_succ (F : Modules (X := X) (R := R)) [Injective F] (q : ℕ) :
    Subsingleton ((underlying.obj F).H (q + 1)) := by
  apply underlying_H_subsingleton_of_pointProduct
  let M := Discrete.functor (fun x : X => (forgetModule (R := R)).obj ((stalk (R := R) x).obj F))
  exact PhilipponEtaleSkyscraperProducts.product_H_succ (fun x : X => x) M q

/-- The underlying abelian sheaf of an injective module sheaf is acyclic
for direct image along every morphism of schemes. -/
theorem underlying_isZero_higherDirectImage {Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules (X := X) (R := R)) [Injective F] (q : ℕ) :
    IsZero (((pushforward f).rightDerived (q + 1)).obj (underlying.obj F)) := by
  obtain ⟨r, hr⟩ := exists_retraction F
  let G := underlying (X := X) (R := R)
  let e := underlyingPointProductIso F
  let a := G.map (toPointProduct F) ≫ e.hom
  let b := e.inv ≫ G.map r
  have hab : a ≫ b = 𝟙 (G.obj F) := by
    dsimp only [a, b]
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp, hr, G.map_id]
  let M := Discrete.functor (fun x : X => (forgetModule (R := R)).obj ((stalk (R := R) x).obj F))
  let H := (pushforward f).rightDerived (q + 1)
  have hZero : IsZero (H.obj _) :=
    PhilipponEtaleSkyscraperProducts.isZero_higherDirectImage_product (fun x : X => x) f M q
  apply (IsZero.iff_id_eq_zero _).mpr
  calc
    𝟙 _ = H.map (a ≫ b) := by rw [hab, H.map_id]
    _ = H.map a ≫ H.map b := H.map_comp _ _
    _ = 0 := by rw [hZero.eq_zero_of_src (H.map b), comp_zero]

end PhilipponEtaleModuleSkyscrapers

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponModuleEtaleNeighborhoodRestriction

universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]

/-- Regard an étale scheme over an étale neighborhood as étale over the base. -/
abbrev along : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map ⊤ (show Etale f from inferInstance)

private def liftObj {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) : Y.Etale :=
  Scheme.Etale.mk (a.left ≫ U.hom)

private def liftIso {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) :
    (along f).obj (liftObj f a) ≅ V :=
  MorphismProperty.Over.isoMk (Iso.refl _)
    ((Category.id_comp _).trans ((MorphismProperty.Over.w a).symm.trans
      (Category.assoc a.left U.hom f).symm))

private theorem coverPreserving : CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (along f) := by
  constructor
  intro W S hS
  rw [← Sieve.ofArrows_category S, Scheme.ofArrows_mem_smallEtaleTopology_iff] at hS
  rw [← Sieve.ofArrows_category S, Sieve.functorPushforward_ofArrows,
    Scheme.ofArrows_mem_smallEtaleTopology_iff]
  exact hS

private theorem compatiblePreserving :
    CompatiblePreserving X.smallEtaleTopology (along f) := by
  constructor
  intro F T S z hz U₁ U₂ V a₁ a₂ g₁ g₂ h₁ h₂ h
  let V' := liftObj f a₁
  have hleft := congrArg (fun a => a.left) h
  change a₁.left ≫ g₁.left = a₂.left ≫ g₂.left at hleft
  let b₁ : V' ⟶ U₁ := MorphismProperty.Over.homMk a₁.left rfl trivial
  let b₂ : V' ⟶ U₂ := MorphismProperty.Over.homMk a₂.left (by
    change a₂.left ≫ U₂.hom = a₁.left ≫ U₁.hom
    rw [← MorphismProperty.Over.w g₂, ← MorphismProperty.Over.w g₁,
      ← Category.assoc, ← Category.assoc, hleft]) trivial
  have he : b₁ ≫ g₁ = b₂ ≫ g₂ := MorphismProperty.Over.Hom.ext hleft
  let e := liftIso f a₁
  have hₐ₁ : (along f).map b₁ = e.hom ≫ a₁ :=
    MorphismProperty.Over.Hom.ext (Category.id_comp a₁.left).symm
  have hₐ₂ : (along f).map b₂ = e.hom ≫ a₂ :=
    MorphismProperty.Over.Hom.ext (Category.id_comp a₂.left).symm
  have hz' : F.obj.map ((along f).map b₁).op (z g₁ h₁) =
      F.obj.map ((along f).map b₂).op (z g₂ h₂) := hz b₁ b₂ h₁ h₂ he
  apply (F.obj.mapIso e.op).toEquiv.injective
  simpa only [Iso.op_hom, Iso.toEquiv_fun, F.obj.mapIso_hom, ← Functor.map_comp_apply,
    ← op_comp, ← hₐ₁, ← hₐ₂] using hz'

instance along_isContinuous : (along f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving f) (coverPreserving f)

/-- Restriction to the small étale site of an étale neighborhood. -/
abbrev restrict : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (along f).sheafPushforwardContinuous AddCommGrpCat Y.smallEtaleTopology X.smallEtaleTopology

private def restrictAdjunction : restrict f ⊣ pushforward f := by
  let adj : along f ⊣ baseChange f :=
    MorphismProperty.Over.mapPullbackAdj (@Etale) ⊤ f inferInstance trivial
  exact adj.sheafPushforwardContinuous Y.smallEtaleTopology X.smallEtaleTopology

/-- Restriction to an étale neighborhood agrees with the ordinary inverse image. -/
def restrictionIso : restrict f ≅ pullbackSheaves f :=
  (restrictAdjunction f).leftAdjointUniq (pullbackAdjunction f)

section Fibers

variable (W : X.Etale)

private abbrev Lifts := {p : W.left ⟶ Y // p ≫ f = W.hom}
private abbrev Comma := CostructuredArrow (along f).op (op W)

private def liftObject (p : Lifts f W) : Y.Etale := by
  let : Etale (p.val ≫ f) := by rw [p.property]; infer_instance
  let : Etale p.val := Etale.of_comp p.val f
  exact Scheme.Etale.mk p.val

private def liftObjectIso (p : Lifts f W) : (along f).obj (liftObject f W p) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl W.left) ((Category.id_comp _).trans p.property.symm)

private def representative (p : Lifts f W) : Comma f W :=
  CostructuredArrow.mk ((liftObjectIso f W p).inv.op)

private def representatives : Discrete (Lifts f W) ⥤ Comma f W :=
  Discrete.functor (representative f W)

private def liftOfArrow (j : Comma f W) : Lifts f W :=
  ⟨j.hom.unop.left ≫ j.left.unop.hom,
    (Category.assoc _ _ _).trans (MorphismProperty.Over.w j.hom.unop)⟩

private theorem arrow_left_eq {j : Comma f W} {p : Lifts f W}
    (h : j ⟶ representative f W p) : h.left.unop.left = j.hom.unop.left := by
  have he := congrArg (fun a => a.unop.left) (CostructuredArrow.w h)
  change 𝟙 W.left ≫ h.left.unop.left = j.hom.unop.left at he
  exact (Category.id_comp _).symm.trans he

private theorem liftOfArrow_eq {j : Comma f W} {p : Lifts f W}
    (h : j ⟶ representative f W p) : liftOfArrow f W j = p := by
  apply Subtype.ext
  change j.hom.unop.left ≫ j.left.unop.hom = p.val
  rw [← arrow_left_eq f W h]
  exact MorphismProperty.Over.w h.left.unop

private def arrowToRepresentative (j : Comma f W) :
    j ⟶ representative f W (liftOfArrow f W j) := by
  let k : liftObject f W (liftOfArrow f W j) ⟶ j.left.unop :=
    MorphismProperty.Over.homMk j.hom.unop.left rfl trivial
  refine CostructuredArrow.homMk k.op ?_
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  exact Category.id_comp _

private theorem uniqueArrowToRepresentative {j : Comma f W} {p : Lifts f W}
    (a b : j ⟶ representative f W p) : a = b := by
  apply CostructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  exact (arrow_left_eq f W a).trans (arrow_left_eq f W b).symm

private instance representatives_final : (representatives f W).Final where
  out j := by
    let a : StructuredArrow j (representatives f W) :=
      StructuredArrow.mk (arrowToRepresentative f W j)
    apply isConnected_of_isInitial _ (x := a)
    refine IsInitial.ofUniqueHom (fun b => ?_) (fun b h => ?_)
    · let e : a.right = b.right := Discrete.ext (liftOfArrow_eq f W b.hom)
      exact StructuredArrow.homMk (eqToHom e) (uniqueArrowToRepresentative f W _ _)
    · apply StructuredArrow.hom_ext
      exact Subsingleton.elim _ _

end Fibers

section Coefficients

variable {M : Type (u + 1)} [Category.{u} M] [Abelian M]
  [HasColimitsOfSize.{u, u} M] [AB4OfSize.{u} M]

local instance hasPointwiseLeftKanExtension (P : Y.Etaleᵒᵖ ⥤ M) :
    (along f).op.HasPointwiseLeftKanExtension P := by
  intro V
  let W := V.unop
  change HasColimit (CostructuredArrow.proj (along f).op (op W) ⋙ P)
  exact Functor.Final.hasColimit_of_comp (representatives f W)

private abbrev leftKan :
    (Y.Etaleᵒᵖ ⥤ M) ⥤ X.Etaleᵒᵖ ⥤ M :=
  (along f).op.lan

private instance leftKan_preservesMonomorphisms : (leftKan (M := M) f).PreservesMonomorphisms where
  preserves {P Q} α hα := by
    rw [NatTrans.mono_iff_mono_app] at hα ⊢
    intro V
    let W := V.unop
    let L := (along f).op
    let R := representatives f W
    let D := R ⋙ CostructuredArrow.proj L (op W)
    let c (B : Y.Etaleᵒᵖ ⥤ M) : Cocone (D ⋙ B) :=
      ((Functor.LeftExtension.mk _ (L.leftKanExtensionUnit B)).coconeAt (op W)).whisker R
    let hc (B : Y.Etaleᵒᵖ ⥤ M) : IsColimit (c B) :=
      (Functor.Final.isColimitWhiskerEquiv R _).symm
        (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit B (op W))
    let e (B : Y.Etaleᵒᵖ ⥤ M) : ((leftKan f).obj B).obj (op W) ≅ colimit (D ⋙ B) :=
      (hc B).coconePointUniqueUpToIso (colimit.isColimit _)
    have he (B : Y.Etaleᵒᵖ ⥤ M) (j : Discrete (Lifts f W)) :
        (c B).ι.app j ≫ (e B).hom = colimit.ι (D ⋙ B) j :=
      (hc B).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) j
    let β := Functor.whiskerLeft D α
    have hAt (j : Discrete (Lifts f W)) :
        (c P).ι.app j ≫ ((leftKan f).map α).app (op W) = β.app j ≫ (c Q).ι.app j := by
      let t := R.obj j
      change ((L.lanUnit.app P).app t.left ≫ (L.lan.obj P).map t.hom) ≫
        (L.lan.map α).app (op W) = α.app t.left ≫ ((L.lanUnit.app Q).app t.left ≫
          (L.lan.obj Q).map t.hom)
      rw [Category.assoc, (L.lan.map α).naturality t.hom, ← Category.assoc]
      have hn := NatTrans.congr_app (L.lanUnit.naturality α) t.left
      change α.app t.left ≫ (L.lanUnit.app Q).app t.left =
        (L.lanUnit.app P).app t.left ≫ (L.lan.map α).app (L.obj t.left) at hn
      rw [← hn, Category.assoc]
    have hcomp : ((leftKan f).map α).app (op W) ≫ (e Q).hom =
        (e P).hom ≫ colim.map β := by
      apply (hc P).hom_ext
      intro j
      rw [← Category.assoc, hAt, Category.assoc, he Q, ← Category.assoc, he P]
      exact (colimit.ι_map β j).symm
    let : Mono β := (NatTrans.mono_iff_mono_app _).mpr (fun j => hα (D.obj j))
    let : PreservesFiniteLimits (colim (J := Discrete (Lifts f W)) (C := M)) :=
      HasExactColimitsOfShape.preservesFiniteLimits
    exact mono_of_mono_fac hcomp

/-- Restriction along an étale map preserves injectives with coefficients in an
abelian category with exact coproducts and left exact sheafification. -/
theorem restriction_preservesInjectiveObjects [HasSheafify X.smallEtaleTopology M] :
    ((along f).sheafPushforwardContinuous M Y.smallEtaleTopology
      X.smallEtaleTopology).PreservesInjectiveObjects := by
  let L := Functor.sheafPullbackConstruction.sheafPullback (along f) M
    Y.smallEtaleTopology X.smallEtaleTopology
  have : L.PreservesMonomorphisms := by
    unfold L Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (along f) M
      Y.smallEtaleTopology X.smallEtaleTopology)

end Coefficients

instance along_hasPointwiseLeftKanExtension (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (along f).op.HasPointwiseLeftKanExtension P :=
  hasPointwiseLeftKanExtension f P

instance restrict_preservesInjectiveObjects : (restrict f).PreservesInjectiveObjects :=
  restriction_preservesInjectiveObjects f

instance pullback_preservesInjectiveObjects : (pullbackSheaves f).PreservesInjectiveObjects where
  injective_obj h := Injective.of_iso ((restrictionIso f).app _)
    ((restrict f).injective_obj_of_injective h)

end PhilipponModuleEtaleNeighborhoodRestriction

end

section

open AlgebraicGeometry CategoryTheory
open PhilipponEtaleModuleSkyscrapers (underlying)
namespace PhilipponEtalePrimeTorsionComparison
universe u
variable {X : Scheme.{u}}
private abbrev Modules (X : Scheme.{u}) (N : ℕ) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))

theorem underlying_killed {N : ℕ} (J : Modules X N) :
    N • 𝟙 (underlying.obj J) = 0 := by
  have hz : (N : ULift.{u} (ZMod N)) = 0 := ULift.down_injective (ZMod.natCast_self N)
  apply Sheaf.hom_ext
  ext W a
  let b : J.obj.obj W := a
  change N • b = 0
  rw [← Nat.cast_smul_eq_nsmul (ULift.{u} (ZMod N)) N b, hz, zero_smul]

end PhilipponEtalePrimeTorsionComparison

end

end


