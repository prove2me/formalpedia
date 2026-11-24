-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_of_henselian_pair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T22:44:21.194044+00:00
-- url     : https://prove2.me/submissions/c6034931-3a25-44f5-8719-b0c842fec0b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Module.ZMod
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_mono_effacing_etale_cohomology_of_affine_closed_immersion
import Theorems.Thm_AlgebraicGeometry_Scheme_isIso_restrictGlobalSections_of_henselian_pair

set_option maxHeartbeats 1400000

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

open CategoryTheory AlgebraicGeometry Opposite
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
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits


namespace PhilipponExtComparison

universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  {Q : C} {P : D} (p : P ⟶ R.obj Q)

/-- Apply an exact functor to Ext, then precompose with the comparison map. -/
def comparison (M : C) (n : ℕ) : Ext Q M n →+ Ext P (R.obj M) n :=
  ((Ext.mk₀ p).precomp (R.obj M) (zero_add n)).comp (R.mapExtAddHom Q M n)

private theorem comparison_comp {M N : C} {n k m : ℕ} (x : Ext Q M n) (a : Ext M N k)
    (h : n + k = m) :
    comparison R p N m (x.comp a h) =
      (comparison R p M n x).comp (a.mapExactFunctor R) h := by
  change (Ext.mk₀ p).comp ((x.comp a h).mapExactFunctor R) (zero_add m) = _
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc (Ext.mk₀ p) (x.mapExactFunctor R) (a.mapExactFunctor R)
    (zero_add n) h (by simpa using h)).symm

theorem comparison_mk₀ {M : C} (x : Q ⟶ M) :
    comparison R p M 0 (Ext.mk₀ x) = Ext.mk₀ (p ≫ R.map x) := by
  change (Ext.mk₀ p).comp ((Ext.mk₀ x).mapExactFunctor R) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

private theorem comparison_boundary {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (x : Ext Q S.X₃ n) :
    comparison R p S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (comparison R p S.X₃ n x).comp (hS.map_of_exact R).extClass rfl := by
  rw [comparison_comp, Ext.mapExactFunctor_extClass]

theorem comparison_post {M N : C} (a : M ⟶ N) (n : ℕ) (x : Ext Q M n) :
    comparison R p N n (x.comp (Ext.mk₀ a) (add_zero n)) =
      (comparison R p M n x).comp (Ext.mk₀ (R.map a)) (add_zero n) := by
  rw [comparison_comp, Ext.mapExactFunctor_mk₀]

theorem comparison_zero_bijective (M : C)
    (h : Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a)) :
    Function.Bijective (comparison R p M 0) := by
  have hz : (comparison R p M 0 : Ext Q M 0 → Ext P (R.obj M) 0) =
      fun x => Ext.mk₀ (p ≫ R.map (Ext.addEquiv₀ x)) := by
    funext x
    obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective Q M).surjective x
    rw [show Ext.addEquiv₀ (Ext.mk₀ a) = a from Ext.addEquiv₀.apply_symm_apply a]
    exact comparison_mk₀ R p a
  rw [hz]
  exact (Ext.mk₀_bijective _ _).comp (h.comp Ext.addEquiv₀.bijective)

/-- A class of coefficients admits comparison in all degrees if each class
on either side can be killed by a monomorphism with cokernel in the class. -/
theorem comparison_bijective_of_effacement (B : C → Prop)
    (h : ∀ M : C, B M → Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (left : ∀ M : C, B M → ∀ (n : ℕ) (x : Ext Q M (n + 1)),
      ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
        x.comp (Ext.mk₀ i) (add_zero (n + 1)) = 0)
    (right : ∀ M : C, B M → ∀ (n : ℕ) (x : Ext P (R.obj M) (n + 1)),
      ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
        x.comp (Ext.mk₀ (R.map i)) (add_zero (n + 1)) = 0)
    (n : ℕ) (M : C) (hM : B M) : Function.Bijective (comparison R p M n) := by
  induction n generalizing M with
  | zero => exact comparison_zero_bijective R p M (h M hM)
  | succ n ih =>
      constructor
      · apply (AddMonoidHom.ker_eq_bot_iff _).mp
        rw [AddSubgroup.eq_bot_iff_forall]
        intro x hx
        obtain ⟨J, i, hi, hJ, hQ, hkill⟩ := left M hM n x
        let _ : Mono i := hi
        let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
        have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
        have hSR := hS.map_of_exact R
        have hx' : comparison R p S.X₁ (n + 1) x = 0 := hx
        obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Q hS x hkill (n₀ := n) rfl
        have hzero : (comparison R p S.X₃ n y).comp hSR.extClass rfl = 0 := by
          rw [← comparison_boundary R p hS n y, hy]
          exact hx'
        obtain ⟨z', hz'⟩ := Ext.covariant_sequence_exact₃ P hSR _ rfl hzero
        obtain ⟨z, hz⟩ := (ih S.X₂ hJ).surjective z'
        have hyz : z.comp (Ext.mk₀ S.g) (add_zero n) = y := (ih S.X₃ hQ).injective (by
          rw [comparison_post, hz]
          exact hz')
        rw [← hy, ← hyz, Ext.comp_assoc_of_second_deg_zero,
          ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
      · intro x'
        obtain ⟨J, i, hi, _, hQ, hkill⟩ := right M hM n x'
        let _ : Mono i := hi
        let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
        have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
        have hSR := hS.map_of_exact R
        obtain ⟨y', hy'⟩ := Ext.covariant_sequence_exact₁ P hSR x' hkill (n₀ := n) rfl
        obtain ⟨y, hy⟩ := (ih S.X₃ hQ).surjective y'
        refine ⟨y.comp hS.extClass rfl, ?_⟩
        rw [comparison_boundary R p hS, hy]
        exact hy'
end PhilipponExtComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleModuleSkyscrapers (underlying underlying_H_succ underlying_preservesFiniteLimits)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleRelativeCoefficients (boundedTorsionModule boundedTorsionModule_forget)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtalePrimeTorsionComparison

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev constants (X : Scheme.{u}) := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Z := AddCommGrpCat.of (ULift.{u} ℤ)

private def constantAdj (X : Scheme.{u}) : constants X ⊣ globalSections X :=
  constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
    (IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) (Scheme.Etale.mk (𝟙 X)) Over.mkIdTerminal)

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

private def composedAdj :=
  ((constantAdj X).comp (pullbackAdjunction f)).ofNatIsoRight (globalSectionsIso f)

private def constantComparison : (constants Y).obj Z ⟶
    (pullbackSheaves f).obj ((constants X).obj Z) :=
  ((constantAdj Y).leftAdjointUniq (composedAdj f)).hom.app Z

private instance : (pullbackSheaves f).Additive := (pullbackAdjunction f).left_adjoint_additive
private instance : (pullbackSheaves f).IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint

/-- Restriction on étale cohomology, defined by applying the exact inverse
image to Ext and comparing the two constant integer sheaves. -/
def restrict (F : Ab X) (n : ℕ) : F.H n →+ ((pullbackSheaves f).obj F).H n :=
  PhilipponExtComparison.comparison (pullbackSheaves f) (constantComparison f) F n

private theorem homEquiv_restrict (F : Ab X) (a : (constants X).obj Z ⟶ F) :
    (constantAdj Y).homEquiv Z _ (constantComparison f ≫ (pullbackSheaves f).map a) =
      (constantAdj X).homEquiv Z F a ≫ (restrictGlobalSections f).app F := by
  let L := pullbackSheaves f
  let adj := pullbackAdjunction f
  let d := composedAdj f
  have hl : adj.homEquiv _ _ (L.map a) = a ≫ adj.unit.app F := by
    rw [Adjunction.homEquiv_unit]
    exact (adj.unit.naturality a).symm
  have hc : (constantAdj Y).homEquiv Z (L.obj ((constants X).obj Z)) (constantComparison f) =
      d.unit.app Z :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (constantAdj Y) d Z
  calc
    _ = d.homEquiv Z _ (L.map a) := by
      rw [Adjunction.homEquiv_naturality_right, hc, Adjunction.homEquiv_unit]
    _ = _ := by
      dsimp only [d, composedAdj]
      rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
      change (constantAdj X).homEquiv Z _ (adj.homEquiv _ _ (L.map a)) ≫
        (globalSectionsIso f).hom.app (L.obj F) = _
      rw [hl, Adjunction.homEquiv_naturality_right,
        PhilipponEtalePullbackComposition.restrictGlobalSections_app_eq, Category.assoc]

private theorem homComparison_bijective
    (F : Ab X) (hF : IsIso ((restrictGlobalSections f).app F)) :
    Function.Bijective (fun a : (constants X).obj Z ⟶ F =>
      constantComparison f ≫ (pullbackSheaves f).map a) := by
  rw [← Function.Bijective.of_comp_iff' ((constantAdj Y).homEquiv Z _).bijective]
  have h : ((constantAdj Y).homEquiv Z _) ∘ (fun a : (constants X).obj Z ⟶ F =>
      constantComparison f ≫ (pullbackSheaves f).map a) =
      (fun a : Z ⟶ (globalSections X).obj F => a ≫ (restrictGlobalSections f).app F) ∘
        (constantAdj X).homEquiv Z F := funext (homEquiv_restrict f F)
  rw [h]
  exact (Iso.homCongr (Iso.refl Z) (asIso ((restrictGlobalSections f).app F))).bijective.comp
    ((constantAdj X).homEquiv Z F).bijective

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

private def modulePresentation (N : ℕ) (F : Ab X) (hF : N • 𝟙 F = 0) :
    Σ M : Modules X N, underlying.obj M ≅ F := by
  let M₀ := boundedTorsionModule N F hF
  let eR : ULift.{u} (ZMod N) ≃+* ZMod N := ULift.ringEquiv
  let liftCoefficients := ModuleCat.restrictScalars.{u} eR.toRingHom
  let : liftCoefficients.IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars.{u} eR.toRingHom).IsEquivalence
  let M : Modules X N :=
    ⟨M₀.obj ⋙ liftCoefficients, Presheaf.isSheaf_comp_of_isSheaf _ _ liftCoefficients M₀.property⟩
  exact ⟨M, (fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
    (eqToIso (boundedTorsionModule_forget N F hF))⟩

private theorem exists_injective_module_embedding (N : ℕ)
    (F : Ab X) (hF : N • 𝟙 F = 0) :
    ∃ (J : Modules X N) (_ : Injective J) (i : F ⟶ underlying.obj J), Mono i := by
  let U := underlying (X := X) (R := ULift.{u} (ZMod N))
  have : PreservesFiniteLimits U := underlying_preservesFiniteLimits
  obtain ⟨M, e⟩ := modulePresentation N F hF
  exact ⟨Injective.under M, inferInstance, e.inv ≫ U.map (Injective.ι M), inferInstance⟩

private theorem cokernel_killed {U V : Ab X} (a : U ⟶ V) {N : ℕ} (hV : N • 𝟙 V = 0) :
    N • 𝟙 (cokernel a) = 0 := by
  apply (cancel_epi (cokernel.π a)).mp
  rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
  simpa only [Preadditive.nsmul_comp, Category.id_comp, zero_comp] using
    congrArg (fun b => b ≫ cokernel.π a) hV

/-- A degree-zero comparison and effacement of individual positive-degree
classes on the target imply comparison for sheaves killed by one integer. -/
theorem bijective_restrict_of_effacement (N : ℕ)
    (hSections : ∀ M : Ab X, N • 𝟙 M = 0 → IsIso ((restrictGlobalSections f).app M))
    (hEfface : ∀ M : Ab X, N • 𝟙 M = 0 → ∀ (q : ℕ) (x : ((pullbackSheaves f).obj M).H (q + 1)),
      ∃ (J : Ab X) (a : M ⟶ J), Mono a ∧ N • 𝟙 J = 0 ∧
        Sheaf.H.map ((pullbackSheaves f).map a) (q + 1) x = 0)
    (F : Ab X) (hF : N • 𝟙 F = 0) (n : ℕ) : Function.Bijective (restrict f F n) := by
  refine PhilipponExtComparison.comparison_bijective_of_effacement
    (pullbackSheaves f) (constantComparison f) (fun M => N • 𝟙 M = 0)
    (fun M hM => homComparison_bijective f M (hSections M hM)) ?_ ?_ n F hF
  · intro M hM q x
    obtain ⟨J, hJ, a, ha⟩ := exists_injective_module_embedding N M hM
    let : Injective J := hJ
    refine ⟨underlying.obj J, a, ha, underlying_killed J, cokernel_killed a (underlying_killed J), ?_⟩
    exact (underlying_H_succ J q).elim _ _
  · intro M hM q x
    obtain ⟨J, a, ha, hJ, hk⟩ := hEfface M hM q x
    exact ⟨J, a, ha, hJ, cokernel_killed a hJ, hk⟩
end PhilipponEtalePrimeTorsionComparison

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u

theorem solution
    (A B : Type u) [CommRing A] [CommRing B] (r : A →+* B) [HenselianRing A (RingHom.ker r)]
    (hr : Function.Surjective r) {Z : Scheme.{u}} (e : Z ≅ Spec (.of B))
    (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u})
    (N : ℕ) (hN : N ≠ 0) (hF : N • 𝟙 F = 0) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (F.H q) ≅
      AddCommGrpCat.of (((pullbackSheaves (e.hom ≫ Spec.map (CommRingCat.ofHom r))).obj F).H q)) := by
  let i := e.hom ≫ Spec.map (CommRingCat.ofHom r)
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom r)) := IsClosedImmersion.spec_of_surjective _ hr
  let : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (e.hom ≫ Spec.map (CommRingCat.ofHom r)))
  let h := PhilipponEtalePrimeTorsionComparison.bijective_restrict_of_effacement i N
    (fun G _ => AlgebraicGeometry.Scheme.isIso_restrictGlobalSections_of_henselian_pair A B r hr e G)
    (fun G hG d x => AlgebraicGeometry.Scheme.exists_mono_effacing_etale_cohomology_of_affine_closed_immersion i N hN G hG d x) F hF q
  exact ⟨(AddEquiv.ofBijective (PhilipponEtalePrimeTorsionComparison.restrict i F q) h).toAddCommGrpIso⟩

end

end
