-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_closed_fiber_of_strictly_henselian
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-21T18:40:45.180839+00:00
-- url     : https://prove2.me/submissions/6617644f-3819-408a-97a8-6e107877b424
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Theorems.Thm_AlgebraicGeometry_Scheme_isIso_etale_globalSections_restrict_closed_fiber_of_strictly_henselian
import Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_etale_cohomology_restrict_injective_module_closed_fiber

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
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleBaseChangeMap (stalkToFiberSections stalkOfHigherImageIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)


namespace PhilipponEtalePullbackResolution

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

local instance (X : Scheme.{u}) : (globalSections X).Additive where
  map_add := rfl

local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullbackSheaves f).Additive :=
  (pullbackAdjunction f).left_adjoint_additive

private theorem extLarge (X : Scheme.{u}) : HasExt.{u + 1} (Ab X) := by
  have h (P Q : Ab X) (n : ℕ) : Small.{u + 1} (Ext.{u} P Q n) :=
    small_succ (Ext.{u} P Q n)
  exact (hasExt_iff_small_ext.{u + 1, u} (Ab X)).mpr h

private def extLift {X : Scheme.{u}} [HasExt.{u + 1} (Ab X)] (P Q : Ab X) (n : ℕ) :
    Ext.{u} P Q n ≃+ Ext.{u + 1} P Q n :=
  letI := HasDerivedCategory.standard (Ab X)
  Ext.homAddEquiv.trans Ext.homAddEquiv.symm

/-- An acyclic resolution computes positive étale cohomology by the
homology of its global sections. -/
def cohomologyEquivAcyclicResolution {X : Scheme.{u}} (F : Ab X)
    (K : CochainComplex (Ab X) ℕ) (e₀ : F ≅ K.cycles 0)
    (hExact : ∀ j : ℕ, K.ExactAt (j + 1))
    (hAcyclic : ∀ j k : ℕ, Subsingleton ((K.X j).H (k + 1)))
    (n : ℕ) : F.H (n + 1) ≃+
      (((globalSections X).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology (n + 1) := by
  letI : HasExt.{u + 1} (Ab X) := extLarge X
  let P := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  have hExt (j k : ℕ) : Subsingleton (Ext.{u + 1} P (K.X j) (k + 1)) := by
    have : Subsingleton (Ext.{u} P (K.X j) (k + 1)) := hAcyclic j k
    exact (extLift P (K.X j) (k + 1)).symm.injective.subsingleton
  let e := PhilipponAcyclicResolution.extEquivAcyclicComplex P F K e₀ hExact hExt n
  exact (extLift P F (n + 1)).trans
    (e.trans (PhilipponEtaleDerivedSections.homologyEquivGlobalSections K (n + 1)))

/-- Restrict global sections along the unit of étale inverse image. -/
def restrictGlobalSections {X Y : Scheme.{u}} (f : Y ⟶ X) :
    globalSections X ⟶ pullbackSheaves f ⋙ globalSections Y :=
  (Functor.leftUnitor (globalSections X)).inv ≫
    Functor.whiskerRight (pullbackAdjunction f).unit (globalSections X) ≫
    (Functor.associator (pullbackSheaves f) (pushforward f) (globalSections X)).hom ≫
    (Functor.isoWhiskerLeft (pullbackSheaves f) (globalSectionsIso f)).hom

/-- A natural comparison of global sections extends to positive étale
cohomology when an exact resolution has acyclic terms on both sites. -/
def cohomologyIsoOfAcyclicRestriction {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Ab X)
    (K : CochainComplex (Ab X) ℕ) (e₀ : F ≅ K.cycles 0)
    (hExact : ∀ j : ℕ, K.ExactAt (j + 1))
    (hAcyclic : ∀ j k : ℕ, Subsingleton ((K.X j).H (k + 1)))
    (hPullback : ∀ j k : ℕ, Subsingleton (((pullbackSheaves f).obj (K.X j)).H (k + 1)))
    (hSections : ∀ j, IsIso ((restrictGlobalSections f).app (K.X j)))
    (n : ℕ) : AddCommGrpCat.of (F.H (n + 1)) ≅
      AddCommGrpCat.of (((pullbackSheaves f).obj F).H (n + 1)) := by
  let L := pullbackSheaves f
  let K' := (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  haveI : L.IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint
  have hExact' (j : ℕ) : K'.ExactAt (j + 1) :=
    (show (K.sc (j + 1)).Exact from hExact j).map L
  let e₀' : L.obj F ≅ K'.cycles 0 := L.mapIso e₀ ≪≫ ((K.sc 0).mapCyclesIso L).symm
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) (n + 1)
  let e := (NatTrans.mapHomologicalComplex (restrictGlobalSections f) (ComplexShape.up ℕ)).app K
  have (j : ℕ) : IsIso (e.f j) := hSections j
  have : IsIso e := HomologicalComplex.Hom.isIso_of_components e
  exact (cohomologyEquivAcyclicResolution F K e₀ hExact hAcyclic n).toAddCommGrpIso ≪≫
    H.mapIso (asIso e) ≪≫
    (cohomologyEquivAcyclicResolution (L.obj F) K' e₀' hExact' hPullback n).symm.toAddCommGrpIso

end PhilipponEtalePullbackResolution

end

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

end PhilipponEtaleSkyscraperProducts

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
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

end PhilipponEtaleModuleSkyscrapers

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace PhilipponEtaleRelativeCoefficients
universe u

private def liftPresheaf {C : Type*} [Category* C] (N : ℕ)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (h : ∀ U (a : ↥(P.obj U)), N • a = 0) :
    Cᵒᵖ ⥤ ModuleCat.{u} (ZMod N) := by
  letI instModule (U : Cᵒᵖ) : Module (ZMod N) (P.obj U) := AddCommGroup.zmodModule (h U)
  refine {
    obj := fun U => ModuleCat.of (ZMod N) (P.obj U)
    map := fun f => ModuleCat.ofHom ((P.map f).hom.toZModLinearMap N)
    map_id := ?_
    map_comp := ?_ }
  · intro U
    apply ConcreteCategory.hom_ext
    intro a
    change P.map (𝟙 U) a = a
    rw [P.map_id]
    rfl
  · intro U V W f g
    apply ConcreteCategory.hom_ext
    intro a
    change P.map (f ≫ g) a = P.map g (P.map f a)
    rw [P.map_comp]
    rfl

/-- An abelian étale sheaf annihilated by an integer has a model as a
sheaf of modules over the corresponding quotient of the integers. -/
def boundedTorsionModule {X : Scheme.{u}} (N : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (h : N • 𝟙 F = 0) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod N)) := by
  have hSection (W : X.Etaleᵒᵖ) (a : ↥(F.obj.obj W)) : N • a = 0 :=
    congrArg (fun t : F ⟶ F => t.hom.app W a) h
  let P := liftPresheaf N F.obj hSection
  refine ⟨P, ?_⟩
  apply Presheaf.isSheaf_of_isSheaf_comp _ P (forget₂ (ModuleCat.{u} (ZMod N)) AddCommGrpCat.{u})
  exact F.property

/-- The underlying abelian presheaf of the module model is the original
presheaf. -/
theorem boundedTorsionModule_forget {X : Scheme.{u}} (N : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (h : N • 𝟙 F = 0) :
    (boundedTorsionModule N F h).obj ⋙ (forget₂ (ModuleCat.{u} (ZMod N)) AddCommGrpCat.{u}) =
      F.obj := rfl

end PhilipponEtaleRelativeCoefficients

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleModuleSkyscrapers
open PhilipponEtalePullbackResolution (cohomologyIsoOfAcyclicRestriction restrictGlobalSections)
open PhilipponEtaleRelativeCoefficients (boundedTorsionModule boundedTorsionModule_forget)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleTorsionResolution

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- A restriction preserving global sections also preserves positive
cohomology of a module sheaf if the restricted underlying sheaves of
injective modules are acyclic. -/
def cohomologyIsoOfModuleRestriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    {R : Type u} [Ring R] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (hSections : ∀ J : Sheaf X.smallEtaleTopology (ModuleCat.{u} R), Injective J →
      IsIso ((restrictGlobalSections f).app (underlying.obj J)))
    (hAcyclic : ∀ J : Sheaf X.smallEtaleTopology (ModuleCat.{u} R), Injective J →
      ∀ q : ℕ, Subsingleton (((pullbackSheaves f).obj (underlying.obj J)).H (q + 1)))
    (n : ℕ) : AddCommGrpCat.of ((underlying.obj F).H (n + 1)) ≅
      AddCommGrpCat.of (((pullbackSheaves f).obj (underlying.obj F)).H (n + 1)) := by
  let U := underlying (X := X) (R := R)
  let : U.Additive := ⟨fun {_ _} _ _ => rfl⟩
  let : PreservesFiniteLimits U := underlying_preservesFiniteLimits
  let : PreservesFiniteColimits U := underlying_preservesFiniteColimits
  let I := injectiveResolution F
  let K := (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hExact (j : ℕ) : K.ExactAt (j + 1) :=
    (show (I.cocomplex.sc (j + 1)).Exact from I.cocomplex_exactAt_succ j).map U
  refine cohomologyIsoOfAcyclicRestriction f (U.obj F) K (asIso (I.toRightDerivedZero' U))
    hExact ?_ ?_ ?_ n
  · intro j k
    let : Injective (I.cocomplex.X j) := I.injective j
    exact underlying_H_succ (I.cocomplex.X j) k
  · intro j k
    exact hAcyclic (I.cocomplex.X j) (I.injective j) k
  · intro j
    exact hSections (I.cocomplex.X j) (I.injective j)

private def HFunctor (X : Scheme.{u}) (n : ℕ) : Ab X ⥤ AddCommGrpCat.{u} :=
  extFunctorObj ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))) n

/-- The same reduction for bounded torsion abelian sheaves, with coefficients
in the quotient of the integers annihilating the sheaf. -/
def cohomologyIsoOfBoundedTorsionRestriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : ℕ) (F : Ab X) (h : N • 𝟙 F = 0)
    (hSections : ∀ J : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N))), Injective J →
      IsIso ((restrictGlobalSections f).app (underlying.obj J)))
    (hAcyclic : ∀ J : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N))), Injective J →
      ∀ q : ℕ, Subsingleton (((pullbackSheaves f).obj (underlying.obj J)).H (q + 1)))
    (n : ℕ) : AddCommGrpCat.of (F.H (n + 1)) ≅
      AddCommGrpCat.of (((pullbackSheaves f).obj F).H (n + 1)) := by
  let M₀ := boundedTorsionModule N F h
  let eR : ULift.{u} (ZMod N) ≃+* ZMod N := ULift.ringEquiv
  let liftCoefficients := ModuleCat.restrictScalars.{u} eR.toRingHom
  letI : liftCoefficients.IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars.{u} eR.toRingHom).IsEquivalence
  let M : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N))) :=
    ⟨M₀.obj ⋙ liftCoefficients,
      Presheaf.isSheaf_comp_of_isSheaf _ _ liftCoefficients M₀.property⟩
  let e : underlying.obj M ≅ F :=
    (fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
      (eqToIso (boundedTorsionModule_forget N F h))
  exact (HFunctor X (n + 1)).mapIso e.symm ≪≫
    cohomologyIsoOfModuleRestriction f M hSections hAcyclic n ≪≫
    (HFunctor Y (n + 1)).mapIso ((pullbackSheaves f).mapIso e)

end PhilipponEtaleTorsionResolution

end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (L : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf (pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) f).smallEtaleTopology AddCommGrpCat.{u})
    (adj : L ⊣ PhilipponEtaleClosedPushforward.pushforward (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) f))
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (N : ℕ) (hN : N ≠ 0) (htors : N • 𝟙 F = 0) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (F.H (q + 1)) ≅
      AddCommGrpCat.of ((L.obj F).H (q + 1))) := by
  let j := pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) f
  let U := PhilipponEtaleModuleSkyscrapers.underlying (X := Y) (R := ULift.{u} (ZMod N))
  let Γ := PhilipponEtaleAcyclicCohomology.globalSections Y
  let e := (PhilipponEtaleSmallSite.pullbackAdjunction j).leftAdjointUniq adj
  let H := extFunctorObj ((constantSheaf (pullback
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) f).smallEtaleTopology
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (q + 1)
  refine ⟨PhilipponEtaleTorsionResolution.cohomologyIsoOfBoundedTorsionRestriction j N F htors ?_ ?_ q ≪≫
    H.mapIso (e.app F)⟩
  · intro J _
    let G := U.obj J
    let : IsIso (Γ.map ((PhilipponEtaleSmallSite.pullbackAdjunction j).unit.app G)) :=
      AlgebraicGeometry.Scheme.isIso_etale_globalSections_restrict_closed_fiber_of_strictly_henselian R f G
    change IsIso ((PhilipponEtalePullbackResolution.restrictGlobalSections j).app G)
    simp only [PhilipponEtalePullbackResolution.restrictGlobalSections, NatTrans.comp_app,
      Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp]
    infer_instance
  · intro J hJ n
    exact AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_restrict_injective_module_closed_fiber R f N hN J hJ (U.obj J) rfl n


end
