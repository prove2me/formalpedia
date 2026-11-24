-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isZero_etale_higherDirectImage_of_prime_injective_projectiveLine_base_change
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T03:31:43.157932+00:00
-- url     : https://prove2.me/submissions/5f81051c-658b-4795-af1f-fb2f39086e66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_iso_projectiveLine_closed_fiber
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_iso_projectiveLine_field_extension
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_higher_stalk_iso_strict_local_cohomology

set_option maxHeartbeats 1300000

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
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks (geometricMap isZero_of_stalks)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleHigherFiberComparison

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- In degree `q`, the stalks of the higher direct image are the
cohomology groups of the geometric fibers with restricted coefficients. -/
def FiberComparison {X S : Scheme.{u}} (f : X ⟶ S) (F : Ab X) (q : ℕ) : Prop :=
  ∀ {K : Type u} [Field K] [IsSepClosed K] (s : Spec (.of K) ⟶ S)
    {T : Scheme.{u}} (r : T ⟶ Spec (.of K)) (j : T ⟶ X) (_ : IsPullback r j s f),
    Nonempty (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})).obj
      (((pushforward f).rightDerived q).obj F) ≅
      AddCommGrpCat.of (((pullbackSheaves j).obj F).H q))

/-- A geometric-fiber comparison for the two projections identifies the
stalks that control higher-image vanishing after base change. -/
theorem isZero_baseChange_of_fiberComparisons {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (g : X' ⟶ S') (a : X' ⟶ X) (b : S' ⟶ S) (h : IsPullback g a b f)
    (F : Ab X) (q : ℕ) (hf : FiberComparison f F q)
    (hg : FiberComparison g ((pullbackSheaves a).obj F) q)
    (hz : IsZero (((pushforward f).rightDerived q).obj F)) :
    IsZero (((pushforward g).rightDerived q).obj ((pullbackSheaves a).obj F)) := by
  apply isZero_of_stalks
  intro x
  let s := geometricMap x
  let t := pullback.fst s g
  let j := pullback.snd s g
  have hs : IsPullback t j s g := IsPullback.of_hasPullback s g
  obtain ⟨e⟩ := hg s t j hs
  obtain ⟨e₀⟩ := hf (s ≫ b) t (j ≫ a) (hs.paste_vert h)
  let e₁ := (Sheaf.functorH (pullback s g).smallEtaleTopology q).mapIso ((pullbackCompIso a j).app F)
  have hz₀ := ((Scheme.pointSmallEtale (s ≫ b)).sheafFiber (A := AddCommGrpCat.{u})).map_isZero hz
  exact hz₀.of_iso (e ≪≫ e₁ ≪≫ e₀.symm)

end PhilipponEtaleHigherFiberComparison

end

section

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleHenselianStalk (residueEmbedding)
open PhilipponEtaleHigherFiberComparison (FiberComparison isZero_baseChange_of_fiberComparisons)
open PhilipponEtaleLocalRing (evaluateGerm stalkRing)
open PhilipponEtaleModuleSkyscrapers (underlying underlying_isZero_higherDirectImage)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStrictHenselization (toBase closedPointInclusion evaluation_comp_toBase)


namespace PhilipponEtaleProjectiveLineFiberComparison

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Line (R : Type u) [CommRing R] := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)

/-- Comparison in positive degrees over a strictly henselian local base. -/
def ClosedComparison (R : Type u) [CommRing R] (N q : ℕ) : Prop :=
  ∀ (A : Type u) [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    (v : Spec (.of A) ⟶ Spec (.of R)) {P : Scheme.{u}} (r : P ⟶ Spec (.of A)) (d : P ⟶ Line R)
    (_ : IsPullback r d v (ProjSpace.π R 1)) (F : Ab P) (_ : N • 𝟙 F = 0),
    Nonempty (AddCommGrpCat.of (F.H (q + 1)) ≅
      AddCommGrpCat.of (((pullbackSheaves (pullback.snd
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) r)).obj F).H (q + 1)))

/-- Comparison after extension of a separably closed field. -/
def FieldComparison (R : Type u) [CommRing R] (N q : ℕ) : Prop :=
  ∀ (L E : Type u) [Field L] [IsSepClosed L] [Field E] [IsSepClosed E]
    (φ : L →+* E) (v : Spec (.of L) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of L)) (d : P ⟶ Line R) (_ : IsPullback r d v (ProjSpace.π R 1))
    (j : T ⟶ Spec (.of E)) (a : T ⟶ P) (_ : IsPullback j a (Spec.map (CommRingCat.ofHom φ)) r)
    (F : Ab P) (_ : N • 𝟙 F = 0),
    Nonempty (AddCommGrpCat.of (F.H (q + 1)) ≅ AddCommGrpCat.of (((pullbackSheaves a).obj F).H (q + 1)))

private theorem underlying_killed {X : Scheme.{u}} {N : ℕ} (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) :
    N • 𝟙 (underlying.obj J) = 0 := by
  have hz : (N : ULift.{u} (ZMod N)) = 0 := ULift.down_injective (ZMod.natCast_self N)
  apply Sheaf.hom_ext
  ext W a
  let b : J.obj.obj W := a
  change N • b = 0
  rw [← Nat.cast_smul_eq_nsmul (ULift.{u} (ZMod N)) N b, hz, zero_smul]

private lemma killed_pullback {U V : Scheme.{u}} (f : V ⟶ U) (N : ℕ) (F : Ab U)
    (hF : N • 𝟙 F = 0) : N • 𝟙 ((pullbackSheaves f).obj F) = 0 := by
  let L := pullbackSheaves f
  let : L.Additive := (pullbackAdjunction f).left_adjoint_additive
  simpa only [L.map_nsmul, L.map_id, L.map_zero] using congrArg (fun m => L.map m) hF

/-- Over a relative projective line, strict-local closed-fiber comparison
and the field comparison identify higher direct-image stalks. -/
theorem fiberComparison_of_restrictions (R : Type u) [CommRing R] (N q : ℕ)
    {P S : Scheme.{u}} (v : S ⟶ Spec (.of R)) (f : P ⟶ S) (e : P ⟶ Line R)
    (hf : IsPullback f e v (ProjSpace.π R 1)) (F : Ab P) (hF : N • 𝟙 F = 0)
    (hClosed : ClosedComparison R N q) (hField : FieldComparison R N q) :
    FiberComparison f F (q + 1) := by
  let : IsProper f := MorphismProperty.of_isPullback hf.flip (inferInstance : IsProper (ProjSpace.π R 1))
  intro E _ _ x T j d h
  let m := pullback.fst (toBase x) f
  let p := pullback.snd (toBase x) f
  let z := Spec.map (evaluateGerm x)
  have hm : IsPullback m (p ≫ e) (toBase x ≫ v) (ProjSpace.π R 1) :=
    (IsPullback.of_hasPullback (toBase x) f).paste_vert hf
  let l := pullback.lift (j ≫ z) d (by rw [Category.assoc, evaluation_comp_toBase, h.w])
  have hlj : l ≫ m = j ≫ z := pullback.lift_fst _ _ _
  have hld : l ≫ p = d := pullback.lift_snd _ _ _
  have hl : IsPullback j l z m := by
    apply IsPullback.of_bot ?_ hlj.symm (IsPullback.of_hasPullback (toBase x) f)
    rw [hld, evaluation_comp_toBase]
    exact h
  let k := IsLocalRing.ResidueField (stalkRing x)
  let g := Spec.map (CommRingCat.ofHom (residueEmbedding x))
  let c := closedPointInclusion x
  let i := pullback.snd c m
  let a := pullback.fst c m
  have ha : IsPullback a (i ≫ p ≫ e) (c ≫ toBase x ≫ v) (ProjSpace.π R 1) :=
    (IsPullback.of_hasPullback c m).paste_vert hm
  have hzc : g ≫ c = z := by
    change Spec.map (CommRingCat.ofHom (residueEmbedding x)) ≫ closedPointInclusion x =
      Spec.map (evaluateGerm x)
    rw [closedPointInclusion, ← Spec.map_comp]
    congr 1
  let w := pullback.lift (j ≫ g) l (by rw [Category.assoc, hzc, hlj])
  have hwj : w ≫ a = j ≫ g := pullback.lift_fst _ _ _
  have hwi : w ≫ i = l := pullback.lift_snd _ _ _
  have hw : IsPullback j w g a := by
    apply IsPullback.of_bot ?_ hwj.symm (IsPullback.of_hasPullback c m)
    rw [hwi, hzc]
    exact hl
  let A := (pullbackSheaves p).obj F
  let B := (pullbackSheaves i).obj A
  have hA : N • 𝟙 A = 0 := killed_pullback p N F hF
  have hB : N • 𝟙 B = 0 := killed_pullback i N A hA
  obtain ⟨e₁⟩ := hClosed (stalkRing x) (toBase x ≫ v) m (p ≫ e) hm A hA
  obtain ⟨e₂⟩ := hField k E (residueEmbedding x) (c ≫ toBase x ≫ v) a (i ≫ p ≫ e) ha j w hw B hB
  have he : w ≫ i ≫ p = d := by rw [← Category.assoc, hwi, hld]
  let β := (pullbackSheaves w).mapIso ((pullbackCompIso p i).app F) ≪≫
    (pullbackCompIso (i ≫ p) w).app F ≪≫ (eqToIso (congrArg pullbackSheaves he)).app F
  let H := Sheaf.functorH T.smallEtaleTopology (q + 1)
  exact ⟨Classical.choice (AlgebraicGeometry.Scheme.nonempty_etale_higher_stalk_iso_strict_local_cohomology f x F q) ≪≫ e₁ ≪≫ e₂ ≪≫ H.mapIso β⟩

/-- The two local comparisons suffice for positive injective
base-change vanishing on the projective line. -/
theorem isZero_baseChange_of_restrictions (R : Type u) [CommRing R] (N q : ℕ)
    {P S P' S' : Scheme.{u}} (v : S ⟶ Spec (.of R)) (f : P ⟶ S) (e : P ⟶ Line R)
    (hf : IsPullback f e v (ProjSpace.π R 1)) (g : P' ⟶ S') (a : P' ⟶ P) (b : S' ⟶ S)
    (h : IsPullback g a b f) (J : Sheaf P.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N))))
    (hJ : Injective J) (hClosed : ClosedComparison R N q) (hField : FieldComparison R N q) :
    IsZero (((pushforward g).rightDerived (q + 1)).obj ((pullbackSheaves a).obj (underlying.obj J))) := by
  let : Injective J := hJ
  let F := underlying.obj J
  have hF : N • 𝟙 F = 0 := underlying_killed J
  exact isZero_baseChange_of_fiberComparisons f g a b h F (q + 1)
    (fiberComparison_of_restrictions R N q v f e hf F hF hClosed hField)
    (fiberComparison_of_restrictions R N q (b ≫ v) g (a ≫ e) (h.paste_vert hf)
      ((pullbackSheaves a).obj F) (killed_pullback a N F hF) hClosed hField)
    (underlying_isZero_higherDirectImage f J q)

end PhilipponEtaleProjectiveLineFiberComparison

end

section

attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (R : Type u) [CommRing R] {S : Scheme.{u}} (v : S ⟶ Spec (.of R))
    {P' S' : Scheme.{u}} (c : P' ⟶ pullback v (ProjSpace.π R 1)) (b : S' ⟶ S) (r' : P' ⟶ S')
    (h : IsPullback r' c b (pullback.fst v (ProjSpace.π R 1)))
    (N : ℕ) (hN : N.Prime)
    (J : Sheaf (pullback v (ProjSpace.π R 1)).smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) (hJ : Injective J)
    (G : Sheaf (pullback v (ProjSpace.π R 1)).smallEtaleTopology AddCommGrpCat.{u})
    (hG : G.obj = J.obj ⋙ forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u})
    (q : ℕ) :
    IsZero (((PhilipponEtaleClosedPushforward.pushforward r').rightDerived (q + 1)).obj ((PhilipponEtaleSmallSite.pullbackSheaves c).obj G)) := by
  let U := PhilipponEtaleModuleSkyscrapers.underlying
    (X := pullback v (ProjSpace.π R 1)) (R := ULift.{u} (ZMod N))
  have hUnderlying : G = U.obj J := ObjectProperty.FullSubcategory.ext hG
  rw [hUnderlying]
  refine PhilipponEtaleProjectiveLineFiberComparison.isZero_baseChange_of_restrictions
    R N q v (pullback.fst v (ProjSpace.π R 1)) (pullback.snd v (ProjSpace.π R 1))
    (IsPullback.of_hasPullback v (ProjSpace.π R 1)) r' c b h J hJ ?_ ?_
  · intro A _ _ _ w P r d hr F hF
    exact AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_projectiveLine_closed_fiber R A w r d hr N hN F hF q
  · intro L E _ _ _ _ φ w P T r d hr j a ha F hF
    exact AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_projectiveLine_field_extension R L E φ w r d hr j a ha N hN F hF q

end

end
