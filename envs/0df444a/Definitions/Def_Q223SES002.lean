-- Prove2me | Definitions.Def_Q223SES002
-- name    : Q223SES002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:46:07.106227+00:00
-- url     : https://prove2.me/theorems/3a064d72-ce30-4051-8ab1-fba31ccc4cca
-- title:
--   Definitions bundle Q223SES002 of the split of OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 248 declarations of OpenAI's Lean: 146 definitions, 2 inductive types or structures, 28 instances and 72 theorems. The definitions and types are `OAI.MaximalSeshadri.FrameBertini.DifferentialFrame`, `OAI.MaximalSeshadri.FreeOpenUnit.isoFromHomEquiv`, `OAI.MaximalSeshadri.Geometry.BaseSections.BaseHom`, `OAI.MaximalSeshadri.Geometry.BaseSections.Sections`, `OAI.MaximalSeshadri.Geometry.BaseSections.baseHomModule`, `OAI.MaximalSeshadri.Geometry.BaseSections.basePrecomp`, `OAI.MaximalSeshadri.Geometry.BaseSections.chartMap`, `OAI.MaximalSeshadri.Geometry.BaseSections.chartPolynomialMap`, `OAI.MaximalSeshadri.Geometry.BaseSections.chartRes`, `OAI.MaximalSeshadri.Geometry.BaseSections.chartTop`, `OAI.MaximalSeshadri.Geometry.BaseSections.congr`, `OAI.MaximalSeshadri.Geometry.BaseSections.globalIntersection`, `OAI.MaximalSeshadri.Geometry.BaseSections.laurentModule`, `OAI.MaximalSeshadri.Geometry.BaseSections.nestedRestriction`, `OAI.MaximalSeshadri.Geometry.BaseSections.polynomialModule`, `OAI.MaximalSeshadri.Geometry.BaseSections.res`, `OAI.MaximalSeshadri.Geometry.BaseSections.restrictEquiv`, `OAI.MaximalSeshadri.Geometry.BaseSections.tripleBaseImage`, `OAI.MaximalSeshadri.Geometry.BaseSections.twoBaseImage`, `OAI.MaximalSeshadri.Geometry.BaseSections.twoBaseIntersection`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.ofIdeal`, `OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators`, `OAI.MaximalSeshadri.Geometry.LineBundle.pullback`, `OAI.MaximalSeshadri.Geometry.OpenSections`, `OAI.MaximalSeshadri.Geometry.affineComplexPoint`, `OAI.MaximalSeshadri.Geometry.affineMapAlgHom`, `OAI.MaximalSeshadri.Geometry.affineSpecSections`, `OAI.MaximalSeshadri.Geometry.affineToSpecModule`, `OAI.MaximalSeshadri.Geometry.centreComplement`, `OAI.MaximalSeshadri.Geometry.chartModuleEquiv`, `OAI.MaximalSeshadri.Geometry.chartModuleMap`, `OAI.MaximalSeshadri.Geometry.cohomologyIso`, `OAI.MaximalSeshadri.Geometry.complexSectionModule`, `OAI.MaximalSeshadri.Geometry.constantsInDegreeZeroIso`, `OAI.MaximalSeshadri.Geometry.disjointSupportCoverEquiv`, `OAI.MaximalSeshadri.Geometry.extSourceIso`, `OAI.MaximalSeshadri.Geometry.finiteSupportLocallyIsoGlobal`, `OAI.MaximalSeshadri.Geometry.frameGenerators`, `OAI.MaximalSeshadri.Geometry.freeUnitIso`, `OAI.MaximalSeshadri.Geometry.moduleIsoSections` and 108 more.
--
--   **Sources.** They come from these modules of lean/OAI/AlgebraicGeometry, in whole or in part: `Seshadri_Bertini_DifferentialFrames`, `Seshadri_Bertini_LinearFamilies`, `Seshadri_Blowup_BlowupIntegral`, `Seshadri_Blowup_FiniteCenters`, `Seshadri_Blowup_OrderContraction`, `Seshadri_Blowup_SchemeHartogs`, `Seshadri_Cohomology_CechPresentation`, `Seshadri_Cohomology_CohomologyIso`, `Seshadri_Cohomology_CurveCech`, `Seshadri_Cohomology_CurveH0Finite`, `Seshadri_Cohomology_FiniteCover`, `Seshadri_Cohomology_FreeVertices`, `Seshadri_Cohomology_IntegralExtension`, `Seshadri_Cohomology_LaurentLattices`, `Seshadri_Cohomology_LaurentPlane`, `Seshadri_Cohomology_LaurentSupport`, `Seshadri_Cohomology_LaurentTorsion`, `Seshadri_Cohomology_PlaneCechLinear`, `Seshadri_Cohomology_PlaneFreeCech`, `Seshadri_Cohomology_PlaneRelationCycles`, `Seshadri_Cohomology_RestrictionComparison`, `Seshadri_Cohomology_SheafExactness`, `Seshadri_Cohomology_SurfaceBaseCech`, `Seshadri_Cohomology_SurfaceCech`, `Seshadri_Cohomology_ToricFreeMap`, `Seshadri_Cohomology_ToricPresentation`, `Seshadri_Cohomology_TripleEvaluation`, `Seshadri_Cohomology_TripleExt`, `Seshadri_Cohomology_TripleTopExt`, `Seshadri_Configurations_AffinePointParameters`, `Seshadri_Configurations_Configurations`, `Seshadri_Definitions`, `Seshadri_Divisors_BaseSections`, `Seshadri_Divisors_OpenSectionsLinear`, `Seshadri_Divisors_PolynomialSections`, `Seshadri_Geometry_ChartCoherence`, `Seshadri_Geometry_ChartPolynomial`, `Seshadri_Geometry_CurveFinite`, `Seshadri_Geometry_FiniteSupportTwist`, `Seshadri_Geometry_LineClosedUnit`, `Seshadri_Geometry_NestedChart`, `Seshadri_Geometry_PencilCokernel`, `Seshadri_Geometry_SmoothAffineRefinement`, `Seshadri_Interpolation_CompressionRanks`, `Seshadri_Interpolation_ConvergentSeries`, `Seshadri_Interpolation_CyclicLattices`, `Seshadri_Interpolation_LaurentJets`, `Seshadri_Interpolation_LaurentMoments`, `Seshadri_Interpolation_Moments`, `Seshadri_Interpolation_PrimitiveDirections`, `Seshadri_Interpolation_QuadrilateralRows`, `Seshadri_Interpolation_RowCompression`, `Seshadri_Interpolation_TriangleJets`, `Seshadri_Interpolation_WeightedRescaling`, `Seshadri_Intersection_LocalSectionDegree`, `Seshadri_Intersection_PencilIntersection`, `Seshadri_Intersection_QuotientIntersection`, `Seshadri_Intersection_SurfaceCurveDegree`, `Seshadri_LocalAlgebra_SmoothCurvePrincipal`, `Seshadri_Nodal_NodalIdealDegree`, `Seshadri_Projective_AmpleEmbedding`, `Seshadri_Projective_PolynomialCharts`, `Seshadri_Projective_QuarticSubsystem`, `Seshadri_Projective_SectionMaps`, `Seshadri_Sheaves_AffineLocalizing`, `Seshadri_Sheaves_ChartModuleMap`, `Seshadri_Sheaves_FramedPullback`, `Seshadri_Sheaves_LineBundleCoherent`, `Seshadri_Sheaves_LinePullback`, `Seshadri_Sheaves_ModuleLocal`, `Seshadri_Sheaves_OpenBaseChange`, `Seshadri_Sheaves_OpenPullbackUnit`, `Seshadri_Sheaves_PlaneModules`, `Seshadri_Sheaves_PowerExtension`, `Seshadri_Sheaves_RestrictedSections`, `Seshadri_Sheaves_Restriction`, `Seshadri_Sheaves_RestrictionLocalization`, `Seshadri_Sheaves_SectionOpens`, `Seshadri_Sheaves_SupportedSheaf`, `Seshadri_Sheaves_TensorFrames`, `Seshadri_Sheaves_TensorOpenSquare`, `Seshadri_Sheaves_TensorPure`.
--
--   **Imports.** It imports the published bundle `Def_MaximalSeshadriConstants`.
--
--   **Imported by** (directly, in this split): the bundles `Q223SES004`, `Q223SES005` and `Q223SES006`.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/AlgebraicGeometry at commit adc7f12

import Mathlib
import Definitions.Def_MaximalSeshadriConstants

section
-- module Solutions.Q223_SES.Compat
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
end OAIVecLookup
end OAICompat434

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_DifferentialFrames
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.FrameBertini
noncomputable section
open KaehlerDifferential

structure DifferentialFrame (K R κ : Type*) [CommRing K] [CommRing R]
    [Algebra K R] [Fintype κ] where
  coord : Ω[R⁄K] →ₗ[R] (κ → R)
  vector : κ → Ω[R⁄K]
  sum_coord : ∀ x, ∑ j, coord x j • vector j = x

end
end MaximalSeshadri.FrameBertini

end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_LinearFamilies
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.LinearBertini
noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.FrameBertini
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

def universalSection (v : ι → R) : MvPolynomial ι R :=
  ∑ i, X i * C (v i)

def universalGradient (b : DifferentialFrame K R κ) (v : ι → R)
    (j : κ) : MvPolynomial ι R :=
  ∑ i, X i * C (b.coord (D K R (v i)) j)

def criticalIdeal (b : DifferentialFrame K R κ) (v : ι → R) :
    Ideal (MvPolynomial ι R) :=
  Ideal.span (insert (universalSection v) (Set.range (universalGradient b v)))

end

noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.FrameBertini
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

def specializedSection (v : ι → R) (t : ι → K) : R :=
  ∑ i, algebraMap K R (t i) * v i

def specializedGradient (b : DifferentialFrame K R κ) (v : ι → R)
    (t : ι → K) (j : κ) : R :=
  ∑ i, algebraMap K R (t i) * b.coord (D K R (v i)) j

end

end MaximalSeshadri.LinearBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SheafExactness
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.ModuleGrothendieck
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] (R₀ : Cᵒᵖ ⥤ RingCat.{u})

instance presheafHasSeparator : HasSeparator (PresheafOfModules.{u} R₀) :=
  ⟨⟨∐ (yoneda ⋙ PresheafOfModules.free R₀).obj,
    (PresheafOfModules.freeYoneda.isSeparating R₀).isSeparator_coproduct⟩⟩

end
end MaximalSeshadri.ModuleGrothendieck


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_Restriction
attribute [-instance] _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma tensorComparison_natural
    {Source Target : Type*} [Category Source] [Category Target]
    [MonoidalCategory Source] [MonoidalCategory Target]
    (pushforward : Source ⥤ Target) [pushforward.OplaxMonoidal]
    (restriction : Source ⥤ Target) (comparison : restriction ≅ pushforward)
    {first second third fourth : Source}
    (leftMap : first ⟶ second) (rightMap : third ⟶ fourth) :
    restriction.map (leftMap ⊗ₘ rightMap) ≫
        (comparison.hom.app (second ⊗ fourth) ≫
          Functor.OplaxMonoidal.δ pushforward second fourth ≫
          (comparison.inv.app second ⊗ₘ comparison.inv.app fourth)) =
      (comparison.hom.app (first ⊗ third) ≫
        Functor.OplaxMonoidal.δ pushforward first third ≫
        (comparison.inv.app first ⊗ₘ comparison.inv.app third)) ≫
          (restriction.map leftMap ⊗ₘ restriction.map rightMap) := by
  rw [← Category.assoc, comparison.hom.naturality, Category.assoc,
    ← Category.assoc (pushforward.map (leftMap ⊗ₘ rightMap)),
    ← Functor.OplaxMonoidal.δ_natural, Category.assoc,
    tensorHom_comp_tensorHom, comparison.inv.naturality,
    comparison.inv.naturality, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]

lemma sheafificationComparison_natural
    {Source SourceSheaves Target TargetSheaves : Type*}
    [Category Source] [Category SourceSheaves] [Category Target] [Category TargetSheaves]
    (sourceSheafification : Source ⥤ SourceSheaves)
    (restriction : SourceSheaves ⥤ TargetSheaves)
    (presheafRestriction : Source ⥤ Target) (sheafification : Target ⥤ TargetSheaves)
    (comparison : sourceSheafification ⋙ restriction ≅ presheafRestriction ⋙ sheafification)
    {first second : Source} {restrictedFirst restrictedSecond : Target}
    (sourceMap : first ⟶ second) (targetMap : restrictedFirst ⟶ restrictedSecond)
    (firstComparison : presheafRestriction.obj first ≅ restrictedFirst)
    (secondComparison : presheafRestriction.obj second ≅ restrictedSecond)
    (naturality : presheafRestriction.map sourceMap ≫ secondComparison.hom =
      firstComparison.hom ≫ targetMap) :
    restriction.map (sourceSheafification.map sourceMap) ≫
        (comparison.app second ≪≫ sheafification.mapIso secondComparison).hom =
      (comparison.app first ≪≫ sheafification.mapIso firstComparison).hom ≫
        sheafification.map targetMap := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  change (sourceSheafification ⋙ restriction).map sourceMap ≫ _ = _
  rw [← Category.assoc, comparison.hom.naturality, Functor.comp_map, Category.assoc,
    ← sheafification.map_comp, naturality, sheafification.map_comp, Category.assoc]

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorFrames
attribute [-instance] _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma tensor_unit_end {C : Type*} [Category C] [MonoidalCategory C]
    (f g : 𝟙_ C ⟶ 𝟙_ C) :
    (f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ (f ≫ g) := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc, leftUnitor_naturality, ← Category.assoc,
    unitors_equal, rightUnitor_naturality, Category.assoc]

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_SectionOpens
attribute [-instance] _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.SectionOpens
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N : X.Modules}

lemma isIso_of_stalks (f : M ⟶ N)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf)) :
    IsIso f := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  let A : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  let B : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let φ : A ⟶ B := ⟨f.mapPresheaf⟩
  let (x : U) : IsIso ((TopCat.Presheaf.stalkFunctor Ab x.val).map φ.hom) := h x.val
  exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso φ U

lemma stalk_isIso_of_restrict (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ]
    [IsIso ((Scheme.Modules.restrictFunctor φ).map f)] (y : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab (φ y)).map f.mapPresheaf) := by
  apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ y) f).mp
  change IsIso ((TopCat.Presheaf.stalkFunctor Ab y).map
    ((Scheme.Modules.toPresheaf Y).map ((Scheme.Modules.restrictFunctor φ).map f)))
  infer_instance

lemma restrict_isIso_of_stalks (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ]
    (h : ∀ y : Y, IsIso ((TopCat.Presheaf.stalkFunctor Ab (φ y)).map f.mapPresheaf)) :
    IsIso ((Scheme.Modules.restrictFunctor φ).map f) := by
  apply isIso_of_stalks
  intro y
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ y) f).mpr (h y)

lemma isIso_of_locally_isIso (f : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)) : IsIso f := by
  apply isIso_of_stalks
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  let := hU
  exact stalk_isIso_of_restrict f U.ι ⟨x, hx⟩

def isoOpen (f : M ⟶ N) : X.Opens :=
  ⨆ (U : X.Opens) (_ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)), U

lemma mem_isoOpen_iff (f : M ⟶ N) (x : X) :
    x ∈ isoOpen f ↔ ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  simp only [isoOpen, Opens.mem_iSup]
  aesop

theorem isIso_restrict_isoOpen (f : M ⟶ N) :
    IsIso ((Scheme.Modules.restrictFunctor (isoOpen f).ι).map f) := by
  apply restrict_isIso_of_stalks
  intro x
  obtain ⟨U, hx, hU⟩ := (mem_isoOpen_iff f x.val).mp x.property
  let := hU
  exact stalk_isIso_of_restrict f U.ι ⟨x.val, hx⟩

end
end MaximalSeshadri.SectionOpens

namespace MaximalSeshadri.SectionOpens
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N P : X.Modules}

lemma isoOpen_postcomp (f : M ⟶ N) (e : N ≅ P) :
    isoOpen (f ≫ e.hom) = isoOpen f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff (f ≫ e.hom) x).mp hx
    refine (mem_isoOpen_iff f x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp] at hU
    let := hU
    exact IsIso.of_isIso_comp_right
      ((Scheme.Modules.restrictFunctor U.ι).map f) ((Scheme.Modules.restrictFunctor U.ι).map e.hom)
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff f x).mp hx
    refine (mem_isoOpen_iff (f ≫ e.hom) x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp]
    let := hU
    infer_instance

lemma isoOpen_precomp (e : P ≅ M) (f : M ⟶ N) :
    isoOpen (e.hom ≫ f) = isoOpen f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff (e.hom ≫ f) x).mp hx
    refine (mem_isoOpen_iff f x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp] at hU
    let := hU
    exact IsIso.of_isIso_comp_left
      ((Scheme.Modules.restrictFunctor U.ι).map e.hom) ((Scheme.Modules.restrictFunctor U.ι).map f)
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff f x).mp hx
    refine (mem_isoOpen_iff (e.hom ≫ f) x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp]
    let := hU
    infer_instance

lemma isoOpen_restrict (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    isoOpen ((Scheme.Modules.restrictFunctor φ).map f) = φ ⁻¹ᵁ isoOpen f := by
  ext y
  constructor
  · intro hy
    obtain ⟨V, hyV, hV⟩ := (mem_isoOpen_iff _ y).mp hy
    let := hV
    apply (mem_isoOpen_iff f (φ y)).mpr
    refine ⟨φ ''ᵁ V, ⟨y, hyV, rfl⟩, ?_⟩
    apply restrict_isIso_of_stalks
    intro x
    obtain ⟨z, hz, he⟩ := x.property
    change φ z = x.val at he
    change IsIso ((TopCat.Presheaf.stalkFunctor Ab x.val).map f.mapPresheaf)
    rw [← he]
    apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ z) f).mp
    exact stalk_isIso_of_restrict ((Scheme.Modules.restrictFunctor φ).map f) V.ι ⟨z, hz⟩
  · intro hy
    change φ y ∈ isoOpen f at hy
    let U := φ ⁻¹ᵁ isoOpen f
    apply (mem_isoOpen_iff _ y).mpr
    refine ⟨U, hy, ?_⟩
    apply restrict_isIso_of_stalks
    intro z
    apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ z.val) f).mpr
    let := isIso_restrict_isoOpen f
    exact stalk_isIso_of_restrict f (isoOpen f).ι ⟨φ z.val, z.property⟩

end
end MaximalSeshadri.SectionOpens
namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

lemma isUnit_iff_basicOpen_top (c : Γ(X, ⊤)) :
    IsUnit c ↔ X.basicOpen c = ⊤ := by
  refine ⟨X.basicOpen_of_isUnit, fun h => ?_⟩
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ c
  intro x hx
  apply (X.mem_basicOpen c x hx).mp
  rw [h]
  trivial

end
end MaximalSeshadri.Frames


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PowerExtension
attribute [-instance] _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.TensorLocalization
noncomputable section
open CategoryTheory MonoidalCategory
universe v' u'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

lemma map_tensor_right_unit {P Q L : C} (f : P ⟶ Q) (e : L ≅ 𝟙_ C)
    [IsIso (F.map f)] : IsIso (F.map (f ⊗ₘ 𝟙 L)) := by
  let ε (A : C) : A ⊗ L ≅ A := tensorIso (Iso.refl A) e ≪≫ ρ_ A
  have h : (f ⊗ₘ 𝟙 L) ≫ (ε Q).hom = (ε P).hom ≫ f := by
    simp only [ε, Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    have ht : f ⊗ₘ e.hom = (𝟙 P ⊗ₘ e.hom) ≫ (f ⊗ₘ 𝟙 (𝟙_ C)) := by
      rw [tensorHom_comp_tensorHom]
      simp only [Category.id_comp, Category.comp_id]
    rw [ht, Category.assoc, tensorHom_id, rightUnitor_naturality, Category.assoc]
  have hh : IsIso (F.map ((f ⊗ₘ 𝟙 L) ≫ (ε Q).hom)) := by
    rw [h, F.map_comp]
    infer_instance
  rw [F.map_comp] at hh
  exact (isIso_comp_right_iff _ _).mp hh

end
end MaximalSeshadri.TensorLocalization


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_PolynomialCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] Classical.propDecidable

lemma homogeneous_eval₂_scale {R S σ : Type*} [CommRing R] [CommRing S]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (f : R →+* S) (u : σ → S) (a : S) :
    eval₂ f (fun j => a * u j) p = a ^ n * eval₂ f u p := by
  classical
  rw [p.as_sum]
  simp only [eval₂_sum, eval₂_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support hd]
  ring

attribute [local instance] MvPolynomial.gradedAlgebra

end

end MaximalSeshadri.Projective


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

abbrev centreComplement (I : X.IdealSheafData) : X.Opens := I.support.compl

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_OrderContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open MvPolynomial
variable (K : Type) [Field K]

def chartExponent (i : Fin 2) : (Fin 2 →₀ ℕ) →+ (Fin 2 →₀ ℕ) where
  toFun d := Finsupp.equivFunOnFinite.symm (fun j => if j = i then d 0 + d 1 else d j)
  map_zero' := by ext j; simp
  map_add' d e := by
    ext j
    change (if j = i then (d + e) 0 + (d + e) 1 else (d + e) j) =
      (if j = i then d 0 + d 1 else d j) + (if j = i then e 0 + e 1 else e j)
    simp only [Finsupp.add_apply]
    split_ifs <;> omega

@[simp] lemma chartExponent_apply (i j : Fin 2) (d : Fin 2 →₀ ℕ) :
    chartExponent i d j = if j = i then d 0 + d 1 else d j := rfl

end
end MaximalSeshadri.PlaneBlowup


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_FiniteCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.FinitePointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}

variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))

variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)

include hp
omit [Fintype α] in
lemma point_support (i : α) : ((p i).ker.support : Set X) =
    {p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))} := by
  let : IsClosedImmersion (p i) := isClosedImmersion_of_comp_eq_id f (p i) (hp i)
  rw [Scheme.Hom.support_ker, (p i).isClosedEmbedding.isClosed_range.closure_eq]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact congrArg (p i) (Subsingleton.elim _ _)
  · rintro rfl
    exact ⟨_, rfl⟩

end
end MaximalSeshadri.FinitePointBlowup

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_SchemeHartogs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.Hartogs
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable (K : Type) [Field K] (X : Scheme) [IsIntegral X] [IsAffine X]

local instance instNonemptyCarrierCarrierCommRingCatToSchemeTopOpens_solutions : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

end
end MaximalSeshadri.Hartogs

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneCechLinear
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

def cycles (A B C : Submodule K M) : Submodule K (A × B × C) :=
  LinearMap.ker
    ({ toFun := fun x => (x.1 : M) + (x.2.1 : M) + (x.2.2 : M)
       map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]; abel
       map_smul' := by intros; simp only [Prod.smul_fst, Prod.smul_snd,
        Submodule.coe_smul_of_tower, smul_add, RingHom.id_apply] } :
        (A × B × C) →ₗ[K] M)

def edgeAB (A B C : Submodule K M) : ↥(A ⊓ B) →ₗ[K] cycles A B C where
  toFun x := ⟨(⟨x,x.property.1⟩,⟨-x,B.neg_mem x.property.2⟩,0), by
    change (x : M) + -(x : M) + 0 = 0; simp⟩
  map_add' := by intros; ext <;> simp; all_goals abel
  map_smul' := by intros; ext <;> simp

def edgeAC (A B C : Submodule K M) : ↥(A ⊓ C) →ₗ[K] cycles A B C where
  toFun x := ⟨(⟨x,x.property.1⟩,0,⟨-x,C.neg_mem x.property.2⟩), by
    change (x : M) + 0 + -(x : M) = 0; simp⟩
  map_add' := by intros; ext <;> simp; all_goals abel
  map_smul' := by intros; ext <;> simp

def edgeBC (A B C : Submodule K M) : ↥(B ⊓ C) →ₗ[K] cycles A B C where
  toFun x := ⟨(0,⟨x,x.property.1⟩,⟨-x,C.neg_mem x.property.2⟩), by
    change 0 + (x : M) + -(x : M) = 0; simp⟩
  map_add' := by intros; ext <;> simp; all_goals abel
  map_smul' := by intros; ext <;> simp

def boundaries (A B C : Submodule K M)
    (N₀ : Submodule K ↥(A ⊓ B)) (N₁ : Submodule K ↥(A ⊓ C))
    (N₂ : Submodule K ↥(B ⊓ C)) : Submodule K (cycles A B C) :=
  N₀.map (edgeAB A B C) ⊔ N₁.map (edgeAC A B C) ⊔ N₂.map (edgeBC A B C)

end
end MaximalSeshadri.PlaneCech

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CechPresentation
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K M P : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup P] [Module K P]

def cycleMap (f : P →ₗ[K] M) (A B C : Submodule K P) (D E F : Submodule K M)
    (hA : ∀ x ∈ A, f x ∈ D) (hB : ∀ x ∈ B, f x ∈ E)
    (hC : ∀ x ∈ C, f x ∈ F) : cycles A B C →ₗ[K] cycles D E F where
  toFun x := ⟨(⟨f x.1.1,hA _ x.1.1.2⟩,⟨f x.1.2.1,hB _ x.1.2.1.2⟩,
      ⟨f x.1.2.2,hC _ x.1.2.2.2⟩),by
    change f (x.1.1 : P) + f (x.1.2.1 : P) + f (x.1.2.2 : P) = 0
    rw [← map_add,← map_add]
    rw [show (x.1.1 : P) + (x.1.2.1 : P) + (x.1.2.2 : P) = 0 from x.2, map_zero]⟩
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CohomologyIso
attribute [-instance] _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

variable {X : Scheme.{0}}

def cohomologyIso (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    let _ := Module.compHom (cohomology M n) (baseScalars f)
    let _ := Module.compHom (cohomology N n) (baseScalars f)
    cohomology M n ≃ₗ[ℂ] cohomology N n := by
  dsimp only
  letI := Module.compHom (cohomology M n) (baseScalars f)
  letI := Module.compHom (cohomology N n) (baseScalars f)
  let g := (Ext.mk₀ e.hom).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  let h := (Ext.mk₀ e.inv).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  refine
    { toFun := g
      invFun := h
      map_add' := g.map_add
      map_smul' := fun r x => g.map_smul (baseScalars f r) x
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change (x.comp (Ext.mk₀ e.hom) (add_zero n)).comp (Ext.mk₀ e.inv) (add_zero n) = x
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      e.hom_inv_id, Ext.comp_mk₀_id]
  · intro x
    change (x.comp (Ext.mk₀ e.inv) (add_zero n)).comp (Ext.mk₀ e.hom) (add_zero n) = x
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      e.inv_hom_id, Ext.comp_mk₀_id]

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_RestrictionComparison
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
universe u w
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def freeOpenFunctor : Opens X ⥤ SheafOfModules.{u} R :=
  yoneda ⋙ PresheafOfModules.free R.obj ⋙ PresheafOfModules.sheafification (𝟙 R.obj)

end
end MaximalSeshadri.ModuleMayerVietoris


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_FiniteCover
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.FreeOpenUnit
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
universe u v

def isoFromHomEquiv {C : Type u} [Category.{v} C] {A B : C}
    (e : ∀ M, (A ⟶ M) ≃ (B ⟶ M))
    (hnat : ∀ {M N} (f : A ⟶ M) (g : M ⟶ N), e N (f ≫ g) = e M f ≫ g) :
    A ≅ B where
  hom := (e B).symm (𝟙 B)
  inv := e A (𝟙 A)
  hom_inv_id := by
    apply (e A).injective
    rw [hnat, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    rw [← hnat, Category.id_comp, Equiv.apply_symm_apply]

end
end MaximalSeshadri.FreeOpenUnit

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_OpenSectionsLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X : Scheme.{0}}

def OpenSections (M : X.Modules) (U : X.Opens) := Γ(M,U)
instance instAddCommGroupCarrierOpenSections (M : X.Modules) (U : X.Opens) : AddCommGroup (OpenSections M U) :=
  inferInstanceAs (AddCommGroup Γ(M,U))
instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections (M : X.Modules) (U : X.Opens) : Module Γ(X,⊤) (OpenSections M U) :=
  Module.compHom Γ(M,U) (restrictScalar X U)

def openRestriction (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    OpenSections M V →ₗ[Γ(X,⊤)] OpenSections M U where
  toFun := M.val.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := by
    intro scalar value
    change Γ(M,V) at value
    let : Module Γ(X,V) Γ(M,V) := (M.val.obj (op V)).isModule
    let : Module Γ(X,U) Γ(M,U) := (M.val.obj (op U)).isModule
    change M.presheaf.map (homOfLE h).op (restrictScalar X V scalar • value) =
      restrictScalar X U scalar • M.presheaf.map (homOfLE h).op value
    exact (M.map_smul (homOfLE h) (restrictScalar X V scalar) value).trans
      (congrArg (fun coefficient : Γ(X,U) =>
        coefficient • M.presheaf.map (homOfLE h).op value)
        (restrictScalar_naturality X (homOfLE h) scalar))

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CurveCech
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                   
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian

variable {X : Scheme.{0}}

def twoChartImage (M : X.Modules) (U V : X.Opens) :
    Submodule Γ(X,⊤) (OpenSections M (U ⊓ V)) :=
  (openRestriction M (show U ⊓ V ≤ U from inf_le_left)).range ⊔
  (openRestriction M (show U ⊓ V ≤ V from inf_le_right)).range

def extSourceIso {E F : X.Modules} (e : E ≅ F) (M : X.Modules) (n : ℕ) :
    Ext.{1} E M n ≃ₗ[Γ(X,⊤)] Ext.{1} F M n where
  toFun := (Ext.mk₀ e.inv).precompOfLinear Γ(X,⊤) M (zero_add n)
  invFun := (Ext.mk₀ e.hom).precompOfLinear Γ(X,⊤) M (zero_add n)
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  right_inv x := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_CurveFinite
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                 
section

namespace MaximalSeshadri.Geometry
open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X] [T0Space X] [IrreducibleSpace X]

lemma proper_irreducible_closed_subsingleton
    (hd : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hi : IsIrreducible Z) (hp : Z ≠ Set.univ) : Z.Subsingleton := by
  let C : IrreducibleCloseds X := ⟨Z, hi, hZ⟩
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hmin : IsMin C := by
    rcases Order.krullDim_le_one_iff.mp hd C with hm | hm
    · exact hm
    · have he : C = T := le_antisymm (Set.subset_univ _) (hm (Set.subset_univ _))
      exact (hp (congrArg SetLike.coe he)).elim
  have hg (x : X) (hx : x ∈ Z) : IsGenericPoint x Z := by
    let D : IrreducibleCloseds X :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hle : D ≤ C := closure_minimal (Set.singleton_subset_iff.mpr hx) hZ
    have he : D = C := le_antisymm hle (hmin hle)
    exact congrArg SetLike.coe he
  intro x hx y hy
  exact (hg x hx).eq (hg y hy)

theorem proper_closed_finite_of_dimension_one [NoetherianSpace X]
    (hd : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hp : Z ≠ Set.univ) : Z.Finite := by
  obtain ⟨F, hF, hFc, hFi, hZF⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hZF]
  apply hF.sUnion
  intro C hC
  apply Set.Subsingleton.finite
  apply proper_irreducible_closed_subsingleton hd (hFc C hC) (hFi C hC)
  intro hc
  apply hp
  apply Set.eq_univ_of_univ_subset
  rw [hZF]
  exact hc ▸ Set.subset_sUnion_of_mem hC

end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_SectionMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
variable {A R σ : Type u} [CommRing A] [CommRing R] [SetLike σ A]
  [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
  (f : A →+* R)

def evalAway (s : A) (hs : IsUnit (f s)) : Away 𝒜 s →+* R :=
  (IsLocalization.Away.lift s hs : Localization.Away s →+* R).comp
    (algebraMap (Away 𝒜 s) (Localization.Away s))

lemma evalAway_val (s : A) (hs : IsUnit (f s)) (x : Away 𝒜 s) :
    evalAway f s hs x = IsLocalization.Away.lift s hs x.val := rfl

lemma evalAway_transition {s t : A} {d : ℕ} (ht : t ∈ 𝒜 d)
    (hs : IsUnit (f s)) (hst : IsUnit (f (s * t))) :
    (evalAway f (s * t) hst).comp (awayMap 𝒜 ht rfl) = evalAway f s hs := by
  have hunit : IsUnit (algebraMap A (Localization.Away (s * t)) s) :=
    IsLocalization.Away.isUnit_of_dvd (s * t) (dvd_mul_right s t)
  have H : (IsLocalization.Away.lift (s * t) hst : Localization.Away (s * t) →+* R).comp
      (Localization.awayLift (algebraMap A (Localization.Away (s * t))) s hunit) =
      (IsLocalization.Away.lift s hs : Localization.Away s →+* R) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    simp
  apply RingHom.ext
  intro x
  simpa only [RingHom.comp_apply, evalAway_val, val_awayMap] using RingHom.congr_fun H x.val

lemma evalAway_natural {T : Type u} [CommRing T] (g : R →+* T)
    (s : A) (hs : IsUnit (f s)) :
    g.comp (evalAway (𝒜 := 𝒜) f s hs) = evalAway (g.comp f) s (hs.map g) := by
  have H : g.comp (IsLocalization.Away.lift s hs : Localization.Away s →+* R) =
      (IsLocalization.Away.lift (g := g.comp f) s (hs.map g) : Localization.Away s →+* T) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    simp
  exact congrArg (fun h : Localization.Away s →+* T =>
    h.comp (algebraMap (Away 𝒜 s) (Localization.Away s))) H

lemma evalAway_mk_clear {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hu : IsUnit (f s))
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    evalAway f s hu (Away.mk 𝒜 hs n a ha) * f s ^ n = f a := by
  rw [evalAway_val, Away.val_mk, Localization.mk_eq_mk']
  have H := IsLocalization.mk'_spec (Localization.Away s) a
    (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s)
  apply_fun (IsLocalization.Away.lift s hu : Localization.Away s →+* R) at H
  simpa only [map_mul, IsLocalization.Away.lift_eq, map_pow] using H

lemma evalAway_scale {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hu : IsUnit (f s))
    (g : A →+* R) (hv : IsUnit (g s)) (c : Rˣ)
    (hscale : ∀ n a, a ∈ 𝒜 n → g a = (c : R) ^ n * f a) :
    evalAway (𝒜 := 𝒜) f s hu = evalAway g s hv := by
  apply RingHom.ext
  intro x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
  apply (hv.pow n).mul_right_cancel
  have Hf := evalAway_mk_clear f hs hu n a ha
  have Hg := evalAway_mk_clear g hs hv n a ha
  rw [Hg, hscale d s hs, hscale _ a ha, mul_pow, ← pow_mul]
  rw [smul_eq_mul, Nat.mul_comm n d]
  calc
    _ = (c : R) ^ (d * n) * (evalAway f s hu (Away.mk 𝒜 hs n a ha) * f s ^ n) := by ring
    _ = _ := by rw [Hf]

def fromUnitCoordinate {s : A} {d : ℕ} (hd : 0 < d) (hs : s ∈ 𝒜 d)
    (hu : IsUnit (f s)) : Spec (CommRingCat.of R) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (evalAway f s hu)) ≫ Proj.awayι 𝒜 s hs hd

lemma fromUnitCoordinate_mul {s t : A} {d e : ℕ} (hd : 0 < d)
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hu : IsUnit (f s))
    (hut : IsUnit (f (s * t))) :
    fromUnitCoordinate f hd hs hu =
      fromUnitCoordinate f (Nat.add_pos_left hd e) (SetLike.mul_mem_graded hs ht) hut := by
  unfold fromUnitCoordinate
  rw [← Proj.SpecMap_awayMap_awayι 𝒜 hs hd ht rfl, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, evalAway_transition f ht hu hut]

@[reassoc]
lemma fromUnitCoordinate_natural {T : Type u} [CommRing T] (g : R →+* T)
    {s : A} {d : ℕ} (hd : 0 < d) (hs : s ∈ 𝒜 d) (hu : IsUnit (f s)) :
    Spec.map (CommRingCat.ofHom g) ≫ fromUnitCoordinate f hd hs hu =
      fromUnitCoordinate (g.comp f) hd hs (hu.map g) := by
  unfold fromUnitCoordinate
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, evalAway_natural]

lemma fromUnitCoordinate_scale {s : A} {d : ℕ} (hd : 0 < d)
    (hs : s ∈ 𝒜 d) (hu : IsUnit (f s)) (g : A →+* R) (hv : IsUnit (g s))
    (c : Rˣ) (hscale : ∀ n a, a ∈ 𝒜 n → g a = (c : R) ^ n * f a) :
    fromUnitCoordinate f hd hs hu = fromUnitCoordinate g hd hs hv := by
  unfold fromUnitCoordinate
  rw [evalAway_scale f hs hu g hv c hscale]

theorem fromUnitCoordinate_eq {s t : A} {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hu : IsUnit (f s)) (hv : IsUnit (f t)) :
    fromUnitCoordinate f hd hs hu = fromUnitCoordinate f he ht hv := by
  have huv : IsUnit (f (s * t)) := by rw [map_mul]; exact hu.mul hv
  have hvu : IsUnit (f (t * s)) := by rw [map_mul]; exact hv.mul hu
  rw [fromUnitCoordinate_mul f hd hs ht hu huv,
    fromUnitCoordinate_mul f he ht hs hv hvu]
  congr 1 <;> ac_rfl


open MvPolynomial

end

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coordinates_X_mem (i : σ) : MvPolynomial.X i ∈ homogeneousSubmodule σ K 1 :=
  isHomogeneous_X K i

def coordinatesMap (X : Scheme.{u}) (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤))
    (i : σ) (hi : a i = 1) : X ⟶ Proj (homogeneousSubmodule σ K) :=
  X.toSpecΓ ≫ fromUnitCoordinate (eval₂Hom k a) (by decide)
    (coordinates_X_mem (K := K) i) (by simpa only [eval₂Hom_X', hi] using isUnit_one)

lemma coordinates_eval_natural {R T : Type u} [CommRing R] [CommRing T]
    (g : R →+* T) (k : K →+* R) (a : σ → R) :
    g.comp (eval₂Hom k a) = eval₂Hom (g.comp k) (fun j => g (a j)) := by
  apply MvPolynomial.ringHom_ext <;> intro j <;> simp

@[reassoc]
lemma coordinatesMap_natural {X Y : Scheme.{u}} (φ : Y ⟶ X)
    (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) :
    φ ≫ coordinatesMap X k a i hi =
      coordinatesMap Y (φ.appTop.hom.comp k) (fun j => φ.appTop (a j)) i
        (by simp only [hi, map_one]) := by
  unfold coordinatesMap
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ]
  congr 1
  change Spec.map (CommRingCat.ofHom φ.appTop.hom) ≫ _ = _
  rw [fromUnitCoordinate_natural]
  congr 1
  exact coordinates_eval_natural φ.appTop.hom k a

lemma coordinatesMap_scale (X : Scheme.{u}) (k : K →+* Γ(X, ⊤))
    (a b : σ → Γ(X, ⊤)) (i j : σ) (hi : a i = 1) (hj : b j = 1)
    (c : Γ(X, ⊤)ˣ) (hscale : ∀ q, b q = (c : Γ(X, ⊤)) * a q) :
    coordinatesMap X k a i hi = coordinatesMap X k b j hj := by
  let f := eval₂Hom k a
  let g := eval₂Hom k b
  have hf : IsUnit (f (MvPolynomial.X (R := K) i)) := by
    simpa only [f, eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(X, ⊤)))
  have hg : IsUnit (g (MvPolynomial.X (R := K) i)) := by
    simpa only [g, eval₂Hom_X', hscale i, hi, mul_one] using c.isUnit
  have hg' : IsUnit (g (MvPolynomial.X (R := K) j)) := by
    simpa only [g, eval₂Hom_X', hj] using (isUnit_one : IsUnit (1 : Γ(X, ⊤)))
  have H : ∀ n p, p ∈ homogeneousSubmodule σ K n →
      g p = (c : Γ(X, ⊤)) ^ n * f p := by
    intro n p hp
    change eval₂ k b p = _
    have hb : b = fun q => (c : Γ(X, ⊤)) * a q := funext hscale
    rw [hb]
    exact homogeneous_eval₂_scale hp k a c
  unfold coordinatesMap
  congr 1
  exact (fromUnitCoordinate_scale (𝒜 := homogeneousSubmodule σ K) (d := 1) f (by decide) (coordinates_X_mem (K := K) i)
    hf g hg c H).trans
      (fromUnitCoordinate_eq (𝒜 := homogeneousSubmodule σ K) (d := 1) (e := 1) g (by decide) (by decide)
        (coordinates_X_mem (K := K) i) (coordinates_X_mem (K := K) j) hg hg')

structure CoordinateAtlas (X : Scheme.{u}) where
  cover : X.OpenCover
  scalars : ∀ i : cover.I₀, K →+* Γ(cover.X i, ⊤)
  coordinates : ∀ i : cover.I₀, σ → Γ(cover.X i, ⊤)
  index : cover.I₀ → σ
  normalized : ∀ i, coordinates i (index i) = 1
  scalarOverlap : ∀ i j,
    (pullback.fst (cover.f i) (cover.f j)).appTop.hom.comp (scalars i) =
      (pullback.snd (cover.f i) (cover.f j)).appTop.hom.comp (scalars j)
  coordinateOverlap : ∀ i j,
    ∃ c : Γ(pullback (cover.f i) (cover.f j), ⊤)ˣ, ∀ q,
      (pullback.snd (cover.f i) (cover.f j)).appTop (coordinates j q) =
        (c : Γ(pullback (cover.f i) (cover.f j), ⊤)) *
          (pullback.fst (cover.f i) (cover.f j)).appTop (coordinates i q)

variable {X : Scheme.{u}} (D : CoordinateAtlas (K := K) (σ := σ) X)

def CoordinateAtlas.localMap (i : D.cover.I₀) :
    D.cover.X i ⟶ Proj (homogeneousSubmodule σ K) :=
  coordinatesMap _ (D.scalars i) (D.coordinates i) (D.index i) (D.normalized i)

lemma CoordinateAtlas.compatible (i j : D.cover.I₀) :
    pullback.fst (D.cover.f i) (D.cover.f j) ≫ D.localMap i =
      pullback.snd (D.cover.f i) (D.cover.f j) ≫ D.localMap j := by
  unfold CoordinateAtlas.localMap
  rw [coordinatesMap_natural, coordinatesMap_natural]
  obtain ⟨c, hc⟩ := D.coordinateOverlap i j
  simpa only [D.scalarOverlap i j] using
    coordinatesMap_scale _
      ((pullback.fst (D.cover.f i) (D.cover.f j)).appTop.hom.comp (D.scalars i))
      _ _ (D.index i) (D.index j)
      (by simp only [D.normalized, map_one])
      (by simp only [D.normalized, map_one]) c hc

def CoordinateAtlas.morphism : X ⟶ Proj (homogeneousSubmodule σ K) :=
  D.cover.glueMorphisms D.localMap D.compatible

@[reassoc, simp]
lemma CoordinateAtlas.cover_morphism (i : D.cover.I₀) :
    D.cover.f i ≫ D.morphism = D.localMap i :=
  D.cover.ι_glueMorphisms _ _ i

end

end MaximalSeshadri.Projective

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_RestrictedSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

lemma restrictScalar_appIso (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens)
    (r : Γ(X,⊤)) :
    (f.appIso U).inv (restrictScalar Y U (f.appTop r)) =
      restrictScalar X (f ''ᵁ U) r := by
  have h := congrArg (fun g : Γ(X,⊤) ⟶ Γ(X,f ''ᵁ U) => g r)
    (Scheme.Hom.appLE_appIso_inv f (U := ⊤) (V := U) (by simp))
  change (f.appIso U).inv ((f.appLE ⊤ U (by simp)) r) = _ at h
  have he : f.appLE ⊤ U (by simp) = f.appTop ≫ Y.presheaf.map U.leTop.op := by
    rfl
  rw [he] at h
  exact h

def restrictedOpenSections (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    (U : Y.Opens) :
    letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
    OpenSections (M.restrict f) U ≃ₗ[Γ(X,⊤)] OpenSections M (f ''ᵁ U) := by
  letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
  letI : Module Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) := (M.val.obj (op (f ''ᵁ U))).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _
      ((f.appIso U).inv (restrictScalar Y U (f.appTop r))) m =
    @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _ (restrictScalar X (f ''ᵁ U) r) m
  rw [restrictScalar_appIso]

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_BaseSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

def Sections (_ : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) := OpenSections M U
instance instAddCommGroupCarrierSections (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    AddCommGroup (Sections k M U) := inferInstanceAs (AddCommGroup (OpenSections M U))
instance globalModule (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module Γ(X,⊤) (Sections k M U) := inferInstanceAs (Module Γ(X,⊤) (OpenSections M U))
instance baseModule (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module K (Sections k M U) := Module.compHom (OpenSections M U) k

def res (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    Sections k M V →ₗ[K] Sections k M U where
  toFun := openRestriction M h
  map_add' := map_add _
  map_smul' r m := (openRestriction M h).map_smul (k r) m

def congr (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U = V) :
    Sections k M U ≃ₗ[K] Sections k M V := by
  subst V
  exact LinearEquiv.refl K _

def restrictEquiv (k : K →+* Γ(X,⊤)) (M : X.Modules)
    (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens) :
    Sections (f.appTop.hom.comp k) (M.restrict f) U ≃ₗ[K]
      Sections k M (f ''ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' r m := (restrictedOpenSections M f U).map_smul (k r) m

lemma chart_image_top (U : X.Opens) : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]

def chartTop (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤ ≃ₗ[K] Sections k M U :=
  (restrictEquiv k M U.ι ⊤).trans (congr k M (chart_image_top U))

end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_LineBundleCoherent
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

def freeUnitIso {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{0}) [HasColimits (SheafOfModules R)] :
    SheafOfModules.free (R := R) PUnit.{1} ≅ SheafOfModules.unit R := by
  change (∐ fun _ : PUnit.{1} => SheafOfModules.unit R) ≅ SheafOfModules.unit R
  refine
    { hom := Sigma.desc (fun _ => 𝟙 _)
      inv := Sigma.ι (fun _ : PUnit.{1} => SheafOfModules.unit R) PUnit.unit
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  ·
    apply Sigma.hom_ext
    intro i
    cases i
    rw [Sigma.ι_desc_assoc]
    change 𝟙 (SheafOfModules.unit R) ≫
      Sigma.ι (fun _ : PUnit.{1} => SheafOfModules.unit R) PUnit.unit =
      Sigma.ι (fun _ : PUnit.{1} => SheafOfModules.unit R) PUnit.unit ≫
        𝟙 (∐ fun _ : PUnit.{1} => SheafOfModules.unit R)
    simp only [Category.id_comp, Category.comp_id]
  · simp

variable {X : Scheme.{0}}

def overFrame {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm)

variable {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{0}} [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat]

def frameGenerators {M : SheafOfModules R} (e : M ≅ SheafOfModules.unit R) :
    M.GeneratingSections where
  I := PUnit.{1}
  s := M.freeHomEquiv ((freeUnitIso R).hom ≫ e.inv)
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

instance frameGenerators_finite {M : SheafOfModules R}
    (e : M ≅ SheafOfModules.unit R) : (frameGenerators e).IsFiniteType where
  finite := inferInstanceAs (Finite PUnit.{1})

instance frameGenerators_isIso {M : SheafOfModules R}
    (e : M ≅ SheafOfModules.unit R) : IsIso (frameGenerators e).π := by
  change IsIso ((M.freeHomEquiv (I := PUnit.{1})).symm
    (M.freeHomEquiv ((freeUnitIso R).hom ≫ e.inv)))
  rw [Equiv.symm_apply_apply]
  infer_instance

def LineBundle.localGenerators (L : LineBundle X) : L.sheaf.LocalGeneratorsData where
  I := X
  X x := (L.locallyRankOne x).choose
  coversTop := by
    rw [Opens.coversTop_iff, IsOpenCover]
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, (L.locallyRankOne x).choose_spec.1⟩
  generators x := frameGenerators (overFrame (L.locallyRankOne x).choose_spec.2.some)

instance LineBundle.localGenerators_locallyFree (L : LineBundle X) :
    L.localGenerators.IsLocallyFreeData where
  isIso _x := frameGenerators_isIso _

instance LineBundle.locallyFree (L : LineBundle X) : L.sheaf.IsLocallyFree :=
  L.localGenerators.isLocallyFree

instance LineBundle.quasicoherent (L : LineBundle X) : L.sheaf.IsQuasicoherent :=
  L.localGenerators.quasiCoherentData.isQuasicoherent

instance LineBundle.finitePresentation (L : LineBundle X) : L.sheaf.IsFinitePresentation where
  exists_quasicoherentData := by
    let q := L.localGenerators.quasiCoherentData
    have : q.IsFinitePresentation := by
      constructor
      intro i
      constructor
      · exact frameGenerators_finite _
      · constructor
        exact inferInstanceAs (Finite (ULift Empty))
    exact ⟨q, inferInstance⟩

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_AffineLocalizing
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

abbrev affineToSpecModule [IsAffine X] (M : X.Modules) :=
  (Scheme.Modules.pushforward X.toSpecΓ).obj M

def affineSpecSections [IsAffine X] (M : X.Modules)
    (U : (Spec Γ(X,⊤)).Opens) :
    ((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.obj (op U)) ≃ₗ[Γ(X,⊤)]
      OpenSections M (X.toSpecΓ ⁻¹ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    let : Module Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) :=
      (M.val.obj (op (X.toSpecΓ ⁻¹ᵁ U))).isModule
    change @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
      ((X.toSpecΓ.app U).hom
        ((Spec Γ(X,⊤)).presheaf.map U.leTop.op ((Scheme.ΓSpecIso Γ(X,⊤)).inv r))) m =
      @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
        (restrictScalar X (X.toSpecΓ ⁻¹ᵁ U) r) m
    congr 1
    have h := congrArg (fun f : Γ(Spec Γ(X,⊤),⊤) ⟶ Γ(X,X.toSpecΓ ⁻¹ᵁ U) =>
      f ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) (X.toSpecΓ.naturality U.leTop.op)
    simp only [CommRingCat.comp_apply, Scheme.toSpecΓ_appTop] at h
    change _ = restrictScalar X (X.toSpecΓ ⁻¹ᵁ U)
      ((Scheme.ΓSpecIso Γ(X,⊤)).hom ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) at h
    rw [(Scheme.ΓSpecIso Γ(X,⊤)).inv_hom_id_apply r] at h
    exact h

def openSectionsCongr (M : X.Modules) {U V : X.Opens} (h : U = V) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections M V := by
  subst V
  exact LinearEquiv.refl _ _

def openTopSections (M : X.Modules) :
    letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
    OpenSections M ⊤ ≃ₗ[Γ(X,⊤)] Γ(M,⊤) := by
  letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,⊤) Γ(M,⊤) _ (restrictScalar X ⊤ r) m =
    @SMul.smul Γ(X,⊤) Γ(M,⊤) _ r m
  congr 1
  change (X.presheaf.map (𝟙 (op ⊤))) r = r
  rw [X.presheaf.map_id]
  rfl

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_RestrictionLocalization
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y Z : Scheme.{0}}

def moduleIsoSections {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections N U where
  toFun := e.hom.val.app (op U)
  invFun := e.inv.val.app (op U)
  left_inv m := by
    have h := congrArg (fun f : M ⟶ M => f.val.app (op U) m) e.hom_inv_id
    exact h
  right_inv m := by
    have h := congrArg (fun f : N ⟶ N => f.val.app (op U) m) e.inv_hom_id
    exact h
  map_add' := map_add _
  map_smul' r m := (e.hom.val.app (op U)).hom.map_smul (restrictScalar X U r) m

def openImmersionTop (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f] :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    OpenSections M ⊤ →ₗ[Γ(X,⊤)] OpenSections (M.restrict f) ⊤ := by
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  exact (restrictedOpenSections M f ⊤).symm.toLinearMap ∘ₗ
    openRestriction M (show f ''ᵁ ⊤ ≤ ⊤ from le_top)

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ChartModuleMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

def chartModuleEquiv (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {N : Y.Modules} (e : M.restrict f ≅ N) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    OpenSections (M.restrict f) ⊤ ≃ₗ[Γ(X,⊤)] OpenSections N ⊤ := by
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let E := moduleIsoSections e ⊤
  exact { E.toEquiv with
    map_add' := E.map_add
    map_smul' := fun r m => E.map_smul (f.appTop r) m }

def chartModuleMap (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {N : Y.Modules} (e : M.restrict f ≅ N) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    OpenSections M ⊤ →ₗ[Γ(X,⊤)] OpenSections N ⊤ := by
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  exact (chartModuleEquiv M f e).toLinearMap ∘ₗ openImmersionTop M f

namespace BaseSections
variable {K : Type} [CommRing K]

def chartMap (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N) :
    Sections kX M ⊤ →ₗ[K] Sections kY N ⊤ := by
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  refine { toFun := chartModuleMap M f e
           map_add' := (chartModuleMap M f e).map_add
           map_smul' := ?_ }
  intro r m
  have h := (chartModuleMap M f e).map_smul (kX r) m
  change _ = (f.appTop (kX r)) • (chartModuleMap M f e m) at h
  exact h.trans (congrArg (fun c : Γ(Y,⊤) => c • chartModuleMap M f e m)
    (RingHom.congr_fun hk r))

lemma chartMap_smul (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N)
    (r : Γ(X,⊤)) (m : Sections kX M ⊤) :
    chartMap kX kY f hk M e (r • m) = f.appTop r • chartMap kX kY f hk M e m := by
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  exact (chartModuleMap M f e).map_smul r m

end BaseSections
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_ChartCoherence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [CommRing K] {X : Scheme.{0}}

lemma congr_apply (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens}
    (h : U = V) (m : Sections k M U) :
    congr k M h m = M.presheaf.map (eqToHom h.symm).op m := by
  subst V
  change m = M.presheaf.map (𝟙 (op U)) m
  exact congrArg (fun f : M.presheaf.obj (op U) ⟶ M.presheaf.obj (op U) => f m)
    (M.presheaf.map_id (op U)).symm

def nestedRestriction (M : X.Modules) {U W : X.Opens} (h : W ≤ U) :
    (M.restrict U.ι).restrict (X.homOfLE h) ≅ M.restrict W.ι :=
  ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M

lemma nestedBase (k : K →+* Γ(X,⊤)) {U W : X.Opens} (h : W ≤ U) :
    (X.homOfLE h).appTop.hom.comp (U.ι.appTop.hom.comp k) = W.ι.appTop.hom.comp k := by
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
    Scheme.homOfLE_ι]

lemma chartTop_nested (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U W : X.Opens} (h : W ≤ U)
    (m : Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤) :
    chartTop k M W (chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k)
      (X.homOfLE h) (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h) m) =
        res k M h (chartTop k M U m) := by
  simp only [chartTop, LinearEquiv.trans_apply, restrictEquiv, congr_apply,
    chartMap, chartModuleMap, LinearMap.coe_comp,
    chartModuleEquiv, moduleIsoSections, openImmersionTop, restrictedOpenSections,
    nestedRestriction, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ ≫
    M.presheaf.map _) m = (M.presheaf.map _ ≫ M.presheaf.map _) m
  simp only [← M.presheaf.map_comp]
  apply congrArg (fun morphism :
    M.presheaf.obj (op (U.ι ''ᵁ (⊤ : U.toScheme.Opens))) ⟶ M.presheaf.obj (op W) =>
      morphism m)
  exact (M.presheaf.map_comp _ _).symm.trans
    ((congrArg M.presheaf.map (Subsingleton.elim _ _)).trans
      (M.presheaf.map_comp _ _))

end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentLattices
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.LaurentLattices
noncomputable section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]

instance instIsPrincipalIdealRingLaurentPolynomial_solutions : IsPrincipalIdealRing K[T;T⁻¹] where
  principal I := by
    obtain ⟨a,ha⟩ := (IsPrincipalIdealRing.principal (I.under K[X])).principal
    refine ⟨⟨algebraMap K[X] K[T;T⁻¹] a, ?_⟩⟩
    rw [← IsLocalization.map_under (Submonoid.powers (Polynomial.X : K[X]))
      K[T;T⁻¹] I, ha, Ideal.map_span, Set.image_singleton]

def boundedBelow {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M]
    (b : Basis ι K[T;T⁻¹] M) (l : ℤ) : Submodule K M :=
  ⨅ i, (AddMonoidAlgebra.supported K K (Set.Ici l)).comap
    (((Finsupp.lapply i).comp b.repr.toLinearMap).restrictScalars K)

def boundedAbove {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M]
    (b : Basis ι K[T;T⁻¹] M) (u : ℤ) : Submodule K M :=
  ⨅ i, (AddMonoidAlgebra.supported K K (Set.Iic u)).comap
    (((Finsupp.lapply i).comp b.repr.toLinearMap).restrictScalars K)

end
end MaximalSeshadri.LaurentLattices
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentTorsion
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.LaurentLattices
noncomputable section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]

instance laurent_finiteType : Algebra.FiniteType K K[T;T⁻¹] := by
  let : IsScalarTower K K[X] K[T;T⁻¹] := IsScalarTower.of_algebraMap_eq (fun c => by
    simp only [Polynomial.algebraMap_eq, algebraMap_eq_toLaurent, Polynomial.toLaurent_C,
      ← LaurentPolynomial.C_eq_algebraMap])
  let : Algebra.FinitePresentation K[X] K[T;T⁻¹] :=
    IsLocalization.Away.finitePresentation (Polynomial.X : K[X])
  let : Algebra.FiniteType K[X] K[T;T⁻¹] := inferInstance
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K K[X]) inferInstance

end
end MaximalSeshadri.LaurentLattices
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_PolynomialSections
attribute [-instance] _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

variable {K : Type} [CommRing K] {X : Scheme.{0}}

@[instance_reducible]
def polynomialModule (k : K →+* Γ(X,⊤)) (t : Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module K[X] (Sections k M U) :=
  Module.compHom (Sections k M U) (Polynomial.eval₂RingHom k t)

end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_ChartPolynomial
attribute [-instance] _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

lemma eval_transport (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) (hk : f.appTop.hom.comp kX = kY) (t : Γ(X,⊤))
    (p : K[X]) : f.appTop ((Polynomial.eval₂RingHom kX t) p) =
      (Polynomial.eval₂RingHom kY (f.appTop t)) p := by
  have h : f.appTop.hom.comp (Polynomial.eval₂RingHom kX t) =
      Polynomial.eval₂RingHom kY (f.appTop t) := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa using RingHom.congr_fun hk r
    · simp
  exact RingHom.congr_fun h p

def chartPolynomialMap (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N) (t : Γ(X,⊤)) :
    letI := polynomialModule kX t M ⊤
    letI := polynomialModule kY (f.appTop t) N ⊤
    Sections kX M ⊤ →ₗ[K[X]] Sections kY N ⊤ := by
  letI := polynomialModule kX t M ⊤
  letI := polynomialModule kY (f.appTop t) N ⊤
  refine { toFun := chartMap kX kY f hk M e
           map_add' := (chartMap kX kY f hk M e).map_add
           map_smul' := ?_ }
  intro p m
  change chartMap kX kY f hk M e ((Polynomial.eval₂RingHom kX t) p • m) =
    (Polynomial.eval₂RingHom kY (f.appTop t)) p • chartMap kX kY f hk M e m
  rw [chartMap_smul, eval_transport kX kY f hk]

end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_PencilIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseIntersection (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens) :
    Submodule K (Sections k M (U ⊓ V)) :=
  (res k M (show U ⊓ V ≤ U from inf_le_left)).range ⊓
    (res k M (show U ⊓ V ≤ V from inf_le_right)).range

end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CurveH0Finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Abelian
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}}

lemma BaseSections.res_comp (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U V W : X.Opens} (h : U ≤ V) (g : V ≤ W) (m : Sections k M W) :
    res k M h (res k M g m) = res k M (h.trans g) m := by
  exact congrArg (fun morphism : M.presheaf.obj (op W) ⟶ M.presheaf.obj (op U) =>
    morphism m) (M.presheaf.map_comp (homOfLE g).op (homOfLE h).op).symm

def BaseSections.globalIntersection [IsIntegral X] (k : K →+* Γ(X,⊤))
    (L : LineBundle X) (U V : X.Opens) :
    Sections k L.sheaf ⊤ →ₗ[K] ↥(twoBaseIntersection k L.sheaf U V) :=
  (res k L.sheaf (show U ⊓ V ≤ ⊤ from le_top)).codRestrict _ (by
    intro m
    exact ⟨⟨res k L.sheaf (show U ≤ ⊤ from le_top) m,
      res_comp k L.sheaf inf_le_left le_top m⟩,
      ⟨res k L.sheaf (show V ≤ ⊤ from le_top) m,
      res_comp k L.sheaf inf_le_right le_top m⟩⟩)

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentPlane
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.LaurentPlane
noncomputable section

abbrev Ring (K : Type*) [CommRing K] := AddMonoidAlgebra K (ℤ × ℤ)

def T {K : Type*} [CommRing K] (z : ℤ × ℤ) : Ring K :=
  AddMonoidAlgebra.single z 1

@[simp] lemma T_zero {K : Type*} [CommRing K] : T (K := K) 0 = 1 := rfl
lemma T_add {K : Type*} [CommRing K] (a b : ℤ × ℤ) :
    T (K := K) (a+b) = T a * T b := by
  simp [T, AddMonoidAlgebra.single_mul_single]

section Evaluation
variable {K R : Type*} [CommRing K] [CommRing R]

def monomials (u v : Rˣ) : Multiplicative (ℤ × ℤ) →* R where
  toFun z := ↑(u ^ z.toAdd.1 * v ^ z.toAdd.2)
  map_one' := by simp
  map_mul' z w := by
    change ↑(u ^ (z.toAdd.1 + w.toAdd.1) * v ^ (z.toAdd.2 + w.toAdd.2)) =
      (↑(u ^ z.toAdd.1 * v ^ z.toAdd.2) : R) * ↑(u ^ w.toAdd.1 * v ^ w.toAdd.2)
    simp only [zpow_add, Units.val_mul]
    ring

def eval (k : K →+* R) (u v : Rˣ) : Ring K →+* R :=
  AddMonoidAlgebra.liftNCRingHom k (monomials u v) (fun _ _ => .all _ _)

@[simp] lemma eval_T (k : K →+* R) (u v : Rˣ) (z : ℤ × ℤ) :
    eval k u v (T z) = ↑(u ^ z.1 * v ^ z.2) := by
  simp [eval, T, monomials, AddMonoidAlgebra.liftNCRingHom_single]

@[simp] lemma eval_algebraMap (k : K →+* R) (u v : Rˣ) (a : K) :
    eval k u v (algebraMap K (Ring K) a) = k a := by
  change eval k u v (AddMonoidAlgebra.single 0 a) = k a
  simp [eval, monomials, AddMonoidAlgebra.liftNCRingHom_single]

end Evaluation

end
end MaximalSeshadri.LaurentPlane

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneFreeCech
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K : Type*} [Field K]

def laurentSupported (S : Set (ℤ × ℤ)) : Submodule K (LaurentPlane.Ring K) :=
  (Finsupp.supported K K S).comap (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

def coneA : Set (ℤ × ℤ) := {z | 0 ≤ z.2}
def coneB : Set (ℤ × ℤ) := {z | 0 ≤ z.1}
def coneC (d : ℤ) : Set (ℤ × ℤ) := {z | z.1 + z.2 ≤ d}

def freeA (ι : Type*) : Submodule K (ι → LaurentPlane.Ring K) :=
  Submodule.pi Set.univ (fun _ => laurentSupported coneA)
def freeB (ι : Type*) : Submodule K (ι → LaurentPlane.Ring K) :=
  Submodule.pi Set.univ (fun _ => laurentSupported coneB)
def freeC (ι : Type*) (d : ℤ) : Submodule K (ι → LaurentPlane.Ring K) :=
  Submodule.pi Set.univ (fun _ => laurentSupported (coneC d))

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentSupport
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K]

lemma laurentSupported_eq_span (S : Set (ℤ × ℤ)) :
    laurentSupported (K := K) S = Submodule.span K (T '' S) := by
  rw [laurentSupported,Submodule.comap_equiv_eq_map_symm,
    Finsupp.supported_eq_span_single,Submodule.map_span,Set.image_image]
  rfl

lemma supported_monomial_mul (S U : Set (ℤ × ℤ)) (z : ℤ × ℤ)
    (h : ∀ w ∈ S, z+w ∈ U) (r : LaurentPlane.Ring K) (hr : r ∈ laurentSupported S) :
    T z * r ∈ laurentSupported U := by
  rw [laurentSupported_eq_span] at hr ⊢
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨w,hw,rfl⟩ := hr
    rw [← T_add]
    exact Submodule.subset_span ⟨z+w,h w hw,rfl⟩
  | zero => simp
  | add r s hr hs ih ih' => simpa only [mul_add] using (Submodule.span K (T '' U)).add_mem ih ih'
  | smul a r hr ih => simpa only [mul_smul_comm] using (Submodule.span K (T '' U)).smul_mem a ih

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricFreeMap
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

def freeMap {ι : Type*} [Fintype ι] (e : ι → M) :
    (ι → LaurentPlane.Ring K) →ₗ[LaurentPlane.Ring K] M where
  toFun m := ∑ i, m i • e i
  map_add' := by intros; simp [add_smul,Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum,smul_smul]

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricPresentation
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M]

def weight : Fin 3 → ℤ × ℤ := ![(0,0),(1,0),(0,1)]
def vertexCone : Fin 3 → Set (ℤ × ℤ) :=
  ![coneA ∩ coneB,coneA ∩ coneC 0,coneB ∩ coneC 0]

lemma direction_mem (i j : Fin 3) (n : ℕ) : n • (weight j - weight i) ∈ vertexCone i := by
  fin_cases i <;> fin_cases j <;> simp [weight,vertexCone,coneA,coneB,coneC]

lemma vertexCone_add (i : Fin 3) {z w : ℤ × ℤ}
    (hz : z ∈ vertexCone i) (hw : w ∈ vertexCone i) : z+w ∈ vertexCone i := by
  fin_cases i <;> simp [vertexCone,coneA,coneB,coneC] at * <;> omega

def StandardGenerator (V : Fin 3 → Submodule K M) (n : ℕ) (e : M) : Prop :=
  ∀ i, T (K := K) (-(n • weight i)) • e ∈ V i

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SurfaceCech
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleMayerVietoris

variable {X : Scheme.{0}}
local instance surfaceCechLinear : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) :=
  sheafLinear X
local instance surfaceCechHasExt : HasExt.{1} (SheafOfModules X.ringCatSheaf) := schemeHasExt

def tripleOpen (U V W : X.Opens) : X.Opens := (U ⊓ W) ⊓ (V ⊓ W)

def tripleChartImage (M : X.Modules) (U V W : X.Opens) :
    Submodule Γ(X,⊤) (OpenSections M (tripleOpen U V W)) :=
  ((openRestriction M (show tripleOpen U V W ≤ U ⊓ W from inf_le_left)).range ⊔
   (openRestriction M (show tripleOpen U V W ≤ V ⊓ W from inf_le_right)).range) ⊔
   (openRestriction M (show tripleOpen U V W ≤ U ⊓ V from
      inf_le_inf inf_le_left inf_le_left)).range

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PlaneModules
attribute [-instance] _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.LaurentPlane

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

@[instance_reducible]
def laurentModule (k : K →+* Γ(Y,⊤)) (u v : Γ(Y,⊤)ˣ) (N : Y.Modules) :
    Module (LaurentPlane.Ring K) (Sections k N ⊤) :=
  Module.compHom (Sections k N ⊤) (LaurentPlane.eval k u v)

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_FreeVertices
attribute [-instance] _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K]

def twistCone (d : ℤ) (i : Fin 3) : Set (ℤ × ℤ) :=
  {z | z - d • weight i ∈ vertexCone i}
def freeVertex (ι : Type*) (d : ℤ) (i : Fin 3) : Submodule K (ι → LaurentPlane.Ring K) :=
  Submodule.pi Set.univ (fun _ => laurentSupported (twistCone d i))

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_IntegralExtension
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.Hartogs
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.Limits

def restrictedIdealOpenIso {X : Scheme} (J : X.IdealSheafData) (V : X.Opens) :
    (J.comap V.ι).subscheme ≅ (J.subschemeι ⁻¹ᵁ V).toScheme := by
  let f := (J.comapIso V.ι).hom ≫ pullback.snd V.ι J.subschemeι
  have hf : f.opensRange = J.subschemeι ⁻¹ᵁ V := by
    dsimp [f]
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    rw [Scheme.Hom.opensRange_pullbackSnd]
    simp
  have hset : Set.range f = (J.subschemeι ⁻¹ᵁ V : Set J.subscheme) := congrArg SetLike.coe hf
  exact IsOpenImmersion.isoOfRangeEq f (J.subschemeι ⁻¹ᵁ V).ι
    (by simpa only [Scheme.Opens.range_ι] using hset)

end
end MaximalSeshadri.Hartogs
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SurfaceBaseCech
attribute [-instance] _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [Field K] {X : Scheme.{0}}

def tripleBaseImage (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V W : X.Opens) :
    Submodule K (Sections k M (tripleOpen U V W)) :=
  ((res k M (show tripleOpen U V W ≤ U ⊓ W from inf_le_left)).range ⊔
   (res k M (show tripleOpen U V W ≤ V ⊓ W from inf_le_right)).range) ⊔
   (res k M (show tripleOpen U V W ≤ U ⊓ V from
      inf_le_inf inf_le_left inf_le_left)).range

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_NestedChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {K : Type} [Field K] {X : Scheme.{0}}

abbrev chartRes (k : K →+* Γ(X,⊤)) (M : X.Modules) {U W : X.Opens} (h : W ≤ U) :=
  chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k) (X.homOfLE h)
    (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h)

end
end MaximalSeshadri.Geometry.BaseSections

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_TripleEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {K : Type} [Field K] {X : Scheme.{0}}

def BaseHom (_k : K →+* Γ(X,⊤)) (A B : X.Modules) := A ⟶ B
instance baseHomGroup (baseMap : K →+* Γ(X,⊤)) (source target : X.Modules) :
    AddCommGroup (BaseHom baseMap source target) :=
  Preadditive.homGroup (C := X.Modules) _ _

local instance baseHomModule (k : K →+* Γ(X,⊤)) (A B : X.Modules) :
    Module K (BaseHom k A B) := Module.compHom (A ⟶ B) k

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneRelationCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames ModuleMayerVietoris MaximalSeshadri.Projective MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
attribute [local instance] baseHomModule

def basePrecomp (k : K →+* Γ(X,⊤)) {A B : X.Modules} (M : X.Modules) (f : A ⟶ B) :
    BaseHom k B M →ₗ[K] BaseHom k A M where
  toFun g := f ≫ g
  map_add' := Preadditive.comp_add (C := X.Modules) _ _ _ f
  map_smul' r g := Linear.comp_smul _ _ _ f (k r) g

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_TripleExt
attribute [-instance] _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleMayerVietoris

variable {X : Scheme.{0}}
local instance tripleExtLinear : Linear Γ(X,⊤) X.Modules := sheafLinear X
local instance tripleExtHasExt : HasExt.{1} X.Modules := schemeHasExt

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_TripleTopExt
attribute [-instance] _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleMayerVietoris

variable {X : Scheme.{0}}
local instance tripleTopExtLinear : Linear Γ(X,⊤) X.Modules := sheafLinear X
end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SmoothAffineRefinement
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

def openScalars (g : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

lemma openScalars_restrict (g : X ⟶ Spec (CommRingCat.of K)) {U V : X.Opens}
    (e : U ≤ V) :
    (X.presheaf.map (homOfLE e).op).hom.comp (openScalars g V) = openScalars g U := by
  exact congrArg (fun morphism : Γ(Spec (CommRingCat.of K), ⊤) ⟶ Γ(X, U) =>
    morphism.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    (Scheme.Hom.appLE_map g (show V ≤ g ⁻¹ᵁ ⊤ from by simp) (homOfLE e).op)

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_AffinePointParameters
attribute [-instance] _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma spec_openScalars {X : Scheme} (f : X ⟶ complexBase) (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (openScalars f U.1)) = U.2.fromSpec ≫ f := by
  change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ U.1 (by simp)) = _
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp)

def affineComplexPoint {X : Scheme} (f : X ⟶ complexBase) (U : X.affineOpens)
    (ρ : letI := (openScalars f U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ) :
    Over.mk (𝟙 complexBase) ⟶ Over.mk f := by
  letI := (openScalars f U.1).toAlgebra
  refine Over.homMk (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ U.2.fromSpec) ?_
  rw [Category.assoc,← spec_openScalars,← Spec.map_comp,← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  exact ρ.comp_algebraMap

def affineMapAlgHom {X Y : Scheme} (f : X ⟶ complexBase) (g : Y ⟶ complexBase)
    (h : X ⟶ Y) (hh : h ≫ g = f) (U : Y.affineOpens) (V : X.affineOpens)
    (hVU : V.1 ≤ h ⁻¹ᵁ U.1) :
    letI := (openScalars f V.1).toAlgebra
    letI := (openScalars g U.1).toAlgebra
    Γ(Y,U.1) →ₐ[ℂ] Γ(X,V.1) := by
  letI := (openScalars f V.1).toAlgebra
  letI := (openScalars g U.1).toAlgebra
  have he : CommRingCat.ofHom (openScalars g U.1) ≫ h.appLE U.1 V.1 hVU =
      CommRingCat.ofHom (openScalars f V.1) := by
    apply Spec.map_injective
    rw [Spec.map_comp,spec_openScalars,spec_openScalars,
      ← Category.assoc,IsAffineOpen.SpecMap_appLE_fromSpec h U.2 V.2 hVU,
      Category.assoc,hh]
  exact { (h.appLE U.1 V.1 hVU).hom with
    commutes' := fun c => CategoryTheory.congr_fun he c }

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_Configurations
attribute [-instance] _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

instance complexUncountable : Uncountable ℂ := by
  apply not_countable_iff.mp
  intro h
  let := h
  exact not_countable Complex.ofReal_injective.countable

instance projectiveSpaceToSpec_separated (N : ℕ) : IsSeparated (projectiveSpaceToSpec N) := by
  unfold projectiveSpaceToSpec
  exact IsSeparated.stableUnderComposition.comp_mem _ _ (Proj.isSeparated _) inferInstance

instance Surface.separated (S : Surface) : IsSeparated S.structureMap := by
  rw [← S.overComplex]
  exact IsSeparated.stableUnderComposition.comp_mem _ _ inferInstance inferInstance

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Definitions
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme.{0}}
abbrev complexSectionModule (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    Module ℂ (GlobalSections X M) :=
  Module.compHom _ (baseScalars f)

end
end MaximalSeshadri.Geometry

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PencilCokernel
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseImage (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens) :
    Submodule K (Sections k M (U ⊓ V)) :=
  (res k M (show U ⊓ V ≤ U from inf_le_left)).range ⊔
    (res k M (show U ⊓ V ≤ V from inf_le_right)).range

end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_SupportedSheaf
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.FiniteSupport
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

variable {X : TopCat.{0}}

lemma sections_subsingleton_of_stalks (F : X.Sheaf AddCommGrpCat.{0})
    (U : Opens X) (h : ∀ x ∈ U, Subsingleton (F.presheaf.stalk x)) :
    Subsingleton (F.obj.obj (op U)) := by
  constructor
  intro s t
  apply TopCat.Presheaf.section_ext F U s t
  intro x hx
  let := h x hx
  exact Subsingleton.elim _ _

end
end MaximalSeshadri.FiniteSupport
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_LocalSectionDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X Y : Scheme.{0}}

def sectionRestrictionLinear (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f] :
    Γ(M,⊤) →ₛₗ[f.appTop.hom] Γ(M.restrict f,⊤) where
  toFun m := (M.restrictAppIso f ⊤).inv
    (M.presheaf.map (homOfLE (le_top : f ''ᵁ ⊤ ≤ ⊤)).op m)
  map_add' := by intro a b; simp only [map_add]
  map_smul' r m := by
    change (M.restrictAppIso f ⊤).inv
      (M.presheaf.map (homOfLE (le_top : f ''ᵁ ⊤ ≤ ⊤)).op (r • m)) = _
    rw [M.map_smul, Scheme.Modules.smul_restrictAppIso_inv_apply]
    congr 1
    have hm := Scheme.Hom.appLE_appIso_inv f (U := ⊤) (V := ⊤) (by simp)
    have hApp : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
    rw [hApp] at hm
    have he := CategoryTheory.congr_fun hm r
    change (f.appIso ⊤).hom _ = f.appTop r
    rw [← he]
    exact ConcreteCategory.congr_hom (f.appIso ⊤).inv_hom_id (f.appTop r)

def moduleIsoTop {M N : X.Modules} (e : M ≅ N) :
    Γ(M,⊤) ≃ₗ[Γ(X,⊤)] Γ(N,⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  left_inv x := congrArg (fun t : M ⟶ M => t.app ⊤ x) e.hom_inv_id
  right_inv x := congrArg (fun t : N ⟶ N => t.app ⊤ x) e.inv_hom_id
  map_add' := by intro a b; exact map_add _ a b
  map_smul' := by intro r m; exact e.hom.app_smul r m

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_QuotientIntersection
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.LocalComparison
noncomputable section
variable {K R B : Type*} [Field K] [CommRing R] [CommRing B]
  [Algebra K R] [Algebra K B]

def principalIntersectionEquiv (π : R →ₐ[K] B) (hπ : Function.Surjective π)
    (g : R) (hg : RingHom.ker π.toRingHom = Ideal.span {g}) (f : R) :
    (R ⧸ Ideal.span {f,g}) ≃ₐ[K] (B ⧸ Ideal.span {π f}) := by
  let q := (Ideal.Quotient.mkₐ K (Ideal.span {π f})).comp π
  have hk : RingHom.ker q.toRingHom = Ideal.span {f,g} := by
    have hq : RingHom.ker q.toRingHom = (Ideal.span {π f}).comap π.toRingHom := by
      ext x
      change Ideal.Quotient.mk (Ideal.span {π f}) (π x) = 0 ↔ _
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [hq]
    have he : (Ideal.span {f}).map π.toRingHom = Ideal.span {π f} := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    rw [← he, Ideal.comap_map_of_surjective π.toRingHom hπ]
    change Ideal.span {f} ⊔ RingHom.ker π.toRingHom = _
    rw [hg, ← Ideal.span_union]
    congr 1
  exact (Ideal.quotientEquivAlgOfEq K hk.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      ((Ideal.Quotient.mk_surjective).comp hπ))
end
end MaximalSeshadri.LocalComparison
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_LinePullback
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {X Y : Scheme.{0}}

instance opensMap_final (f : Y ⟶ X) : (Opens.map f.base).Final := by
  let : PreservesLimit (Functor.empty.{0} X.Opens) (Opens.map f.base) := by
    apply preservesLimit_of_preserves_limit_cone (isTerminalTop (α := X.Opens))
    exact (isLimitMapConeEmptyConeEquiv (Opens.map f.base) (⊤ : X.Opens)).symm isTerminalTop
  infer_instance

def pullbackRestrictIso (f : Y ⟶ X) (L : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullback f).obj L).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj (L.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
  (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app L ≪≫
  (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app L ≪≫
  ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app L).symm ≪≫
  (Scheme.Modules.pullback (f ∣_ U)).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm

def LineBundle.pullback (L : LineBundle X) (f : Y ⟶ X) : LineBundle Y where
  sheaf := (Scheme.Modules.pullback f).obj L.sheaf
  locallyRankOne y := by
    obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
    refine ⟨f ⁻¹ᵁ U,hy,⟨pullbackRestrictIso f L.sheaf U ≪≫
      (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫ ?_⟩⟩
    letI : (Opens.map (f ∣_ U).base).Final := opensMap_final (f ∣_ U)
    letI : (SheafOfModules.pushforward (f ∣_ U).toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward (f ∣_ U)).IsRightAdjoint
    letI : IsIso (SheafOfModules.pullbackObjUnitToUnit
        (F := Opens.map (f ∣_ U).base) (f ∣_ U).toRingCatSheafHom) :=
      SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
        (F := Opens.map (f ∣_ U).base) (f ∣_ U).toRingCatSheafHom
    let unitIso :=
      asIso (C := SheafOfModules (f ⁻¹ᵁ U).toScheme.ringCatSheaf)
        (SheafOfModules.pullbackObjUnitToUnit (F := Opens.map (f ∣_ U).base)
        (f ∣_ U).toRingCatSheafHom)
    exact
      { hom := unitIso.hom
        inv := unitIso.inv
        hom_inv_id := unitIso.hom_inv_id
        inv_hom_id := unitIso.inv_hom_id }

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_FramedPullback
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

                                        

namespace MaximalSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

def pullbackRestrictNatIso (f : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
    (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
  Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
  Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
  (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm ≪≫
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
    (Scheme.Modules.pullback (f ∣_ U))

end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_AmpleEmbedding
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.projectiveSpaceToSpec_separated _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

lemma constantsInDegreeZero_bijective (N : ℕ) :
    Function.Bijective (constantsInDegreeZero N) := by
  constructor
  · intro a b h
    have h' : MvPolynomial.C a = (MvPolynomial.C b : MvPolynomial (Fin (N + 1)) ℂ) :=
      congrArg Subtype.val h
    exact MvPolynomial.C_injective _ _ h'
  · intro p
    have h : p.val.totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr p.property
    refine ⟨p.val.coeff 0, ?_⟩
    apply Subtype.ext
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h).symm

def constantsInDegreeZeroIso (N : ℕ) :
    CommRingCat.of ℂ ≅ CommRingCat.of (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0) :=
  (RingEquiv.ofBijective (constantsInDegreeZero N) (constantsInDegreeZero_bijective N)).toCommRingCatIso

instance constantsInDegreeZero_isIso (N : ℕ) :
    IsIso (CommRingCat.ofHom (constantsInDegreeZero N)) :=
  (constantsInDegreeZeroIso N).isIso_hom

instance projectiveSpaceToSpec_proper (N : ℕ) : IsProper (projectiveSpaceToSpec N) := by
  let A := MvPolynomial (Fin (N + 1)) ℂ
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ
  let : Algebra ℂ (𝒜 0) := SetLike.GradeZero.instAlgebra 𝒜
  let : IsScalarTower ℂ (𝒜 0) A := ⟨fun a b c => by
    change (a • (b : A)) * c = a • ((b : A) * c)
    exact smul_mul_assoc a (b : A) c⟩
  let : Algebra.FiniteType (𝒜 0) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (𝒜 0) A
  have hp : IsProper (Proj.toSpecZero 𝒜) :=
    Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat 𝒜
  have : IsIso (Spec.map (CommRingCat.ofHom (constantsInDegreeZero N))) := by infer_instance
  unfold projectiveSpaceToSpec
  exact IsProper.stableUnderComposition.comp_mem _ _ hp inferInstance

instance Surface.proper (S : Surface) : IsProper S.structureMap := by
  rw [← S.overComplex]
  infer_instance

instance Surface.compact (S : Surface) : CompactSpace S.scheme :=
  QuasiCompact.compactSpace_of_compactSpace S.structureMap

instance Surface.locallyNoetherian (S : Surface) : IsLocallyNoetherian S.scheme :=
  LocallyOfFiniteType.isLocallyNoetherian S.structureMap

instance Surface.noetherian (S : Surface) : IsNoetherian S.scheme where

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceCurveDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective
open MaximalSeshadri.LocalComparison
open scoped Topology

instance IntegralCurve.proper (S : Surface) (C : IntegralCurve S) :
    IsProper (C.embedding ≫ S.structureMap) := by infer_instance

instance IntegralCurve.noetherian (S : Surface) (C : IntegralCurve S) :
    IsNoetherian C.scheme := by
  let : IsLocallyNoetherian C.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian C.embedding
  let : CompactSpace C.scheme :=
    QuasiCompact.compactSpace_of_compactSpace C.embedding
  exact {}

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_FiniteSupportTwist
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

def openSectionModule (M : X.Modules) (U : X.Opens) : ModuleCat Γ(X,⊤) := by
  letI := Module.compHom Γ(M,U) (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
  exact ModuleCat.of Γ(X,⊤) Γ(M,U)

def openSectionRestriction (M : X.Modules) (U : X.Opens) :
    Γ(M,⊤) →ₗ[Γ(X,⊤)] openSectionModule M U where
  toFun := M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
  map_add' := map_add _
  map_smul' := fun r s => M.map_smul _ r s

def disjointSupportCoverEquiv (M : X.Modules) {ι : Type*} (D : ι → X.Opens)
    (hcover : ⊤ ≤ ⨆ i, D i)
    (hz : ∀ i j, i ≠ j → Subsingleton Γ(M,D i ⊓ D j)) :
    Γ(M,⊤) ≃ₗ[Γ(X,⊤)] ((i : ι) → openSectionModule M (D i)) := by
  let F : (X : TopCat).Sheaf AddCommGrpCat :=
    (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  let f := LinearMap.pi (fun i => openSectionRestriction M (D i))
  apply LinearEquiv.ofBijective f
  constructor
  · intro s t h
    apply F.eq_of_locally_eq' D ⊤ (fun _ => homOfLE le_top) hcover s t
    intro i
    exact congrFun h i
  · intro s
    have hc : TopCat.Presheaf.IsCompatible F.obj D s := by
      intro i j
      by_cases h : i = j
      · subst j; rfl
      · let : Subsingleton (F.obj.obj (op (D i ⊓ D j))) := hz i j h
        exact Subsingleton.elim _ _
    obtain ⟨t,ht,_⟩ := F.existsUnique_gluing' D ⊤ (fun _ => homOfLE le_top) hcover s hc
    exact ⟨t,funext ht⟩

def openSectionIso (M N : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ N.restrict U.ι) :
    openSectionModule M U ≃ₗ[Γ(X,⊤)] openSectionModule N U := by
  let etop := ((Scheme.Modules.toPresheaf U.toScheme).mapIso e).app (op ⊤)
  let a := (M.restrictAppIso U.ι ⊤).symm ≪≫ etop ≪≫ N.restrictAppIso U.ι ⊤
  have E : openSectionModule M (U.ι ''ᵁ ⊤) ≃ₗ[Γ(X,⊤)]
      openSectionModule N (U.ι ''ᵁ ⊤) := by
    refine { toFun := fun x => a.hom x
             invFun := fun x => a.inv x
             left_inv := by intro s; exact ConcreteCategory.congr_hom a.hom_inv_id s
             right_inv := by intro s; exact ConcreteCategory.congr_hom a.inv_hom_id s
             map_add' := map_add _
             map_smul' := ?_ }
    intro r s
    change Γ(M,U.ι ''ᵁ ⊤) at s
    change (N.restrictAppIso U.ι ⊤).hom
        (e.hom.app ⊤ ((M.restrictAppIso U.ι ⊤).inv
          ((X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op r) • s))) =
      (X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op r) • a.hom s
    rw [Scheme.Modules.smul_restrictAppIso_inv_apply,e.hom.app_smul,
      Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp only [← ConcreteCategory.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have htop : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange,Scheme.Opens.opensRange_ι]
  exact htop ▸ E

def finiteSupportLocallyIsoGlobal (M N : X.Modules) (S : Set X)
    (hfin : S.Finite) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hM : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x))
    (hN : ∀ x ∉ S, Subsingleton (N.presheaf.stalk x))
    (hloc : ∀ x ∈ S, ∃ U : X.Opens, x ∈ U ∧ Nonempty (M.restrict U.ι ≅ N.restrict U.ι)) :
    Γ(M,⊤) ≃ₗ[Γ(X,⊤)] Γ(N,⊤) := by
  classical
  choose U hx he using fun x : S => hloc x x.property
  let e : ∀ x : S, M.restrict (U x).ι ≅ N.restrict (U x).ι := fun x => (he x).some
  have hc : IsClosed S := by
    rw [← Set.biUnion_of_singleton S]
    exact hfin.isClosed_biUnion hclosed
  have hcx (x : S) : IsClosed (S \ {x.val}) := by
    rw [← Set.biUnion_of_singleton (S \ {x.val})]
    exact (hfin.subset Set.sdiff_subset).isClosed_biUnion (fun y hy => hclosed y hy.1)
  let V : S → X.Opens := fun x => U x ⊓ ⟨(S \ {x.val})ᶜ,(hcx x).isOpen_compl⟩
  let D : Option S → X.Opens := fun x => match x with
    | none => ⟨Sᶜ,hc.isOpen_compl⟩
    | some x => V x
  have hV (x : S) : x.val ∈ V x := ⟨hx x,fun h => h.2 rfl⟩
  have hcover : ⊤ ≤ ⨆ i, D i := by
    intro x _
    by_cases hs : x ∈ S
    · exact Opens.mem_iSup.mpr ⟨some ⟨x,hs⟩,hV ⟨x,hs⟩⟩
    · exact Opens.mem_iSup.mpr ⟨none,hs⟩
  have honly (x : X) (hs : x ∈ S) (i : Option S) (hi : x ∈ D i) :
      i = some ⟨x,hs⟩ := by
    cases i with
    | none => exact (hi hs).elim
    | some y =>
      congr 1
      apply Subtype.ext
      by_contra hne
      exact hi.2 ⟨hs,fun h => hne h.symm⟩
  have hz (P : X.Modules) (hP : ∀ x ∉ S, Subsingleton (P.presheaf.stalk x)) :
      ∀ i j, i ≠ j → Subsingleton Γ(P,D i ⊓ D j) := by
    intro i j hij
    apply FiniteSupport.sections_subsingleton_of_stalks
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj P)
    intro x hx
    apply hP
    intro hs
    exact hij ((honly x hs i hx.1).trans (honly x hs j hx.2).symm)
  have eD (i : Option S) : openSectionModule M (D i) ≃ₗ[Γ(X,⊤)] openSectionModule N (D i) := by
    cases i with
    | none =>
      letI : Subsingleton (openSectionModule M (D none)) := by
        change Subsingleton Γ(M,D none)
        exact FiniteSupport.sections_subsingleton_of_stalks
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) _ (fun x hx => hM x hx)
      letI : Subsingleton (openSectionModule N (D none)) := by
        change Subsingleton Γ(N,D none)
        exact FiniteSupport.sections_subsingleton_of_stalks
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) _ (fun x hx => hN x hx)
      exact LinearEquiv.ofSubsingleton _ _
    | some x =>
      let hVu : V x ≤ U x := inf_le_left
      let nest (P : X.Modules) : (P.restrict (U x).ι).restrict (X.homOfLE hVu) ≅ P.restrict (V x).ι :=
        ((Scheme.Modules.restrictFunctorComp (X.homOfLE hVu) (U x).ι).app P).symm ≪≫
          (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hVu)).app P
      exact openSectionIso M N (V x) ((nest M).symm ≪≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hVu)).mapIso (e x) ≪≫ nest N)
  exact (disjointSupportCoverEquiv M D hcover (hz M hM)).trans
    ((LinearEquiv.piCongrRight eD).trans (disjointSupportCoverEquiv N D hcover (hz N hN)).symm)

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ModuleLocal
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.ModuleLocal
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X : Scheme.{0}} {M N : X.Modules}

lemma app_zero_of_restrict (φ : M ⟶ N) (U W : X.Opens) (hW : W ≤ U)
    (h : (Scheme.Modules.restrictFunctor U.ι).map φ = 0) : φ.app W = 0 := by
  have hz := congrArg (fun q : M.restrict U.ι ⟶ N.restrict U.ι =>
    q.app (U.ι ⁻¹ᵁ W)) h
  have he : U.ι ''ᵁ U.ι ⁻¹ᵁ W = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  change φ.app (U.ι ''ᵁ U.ι ⁻¹ᵁ W) = 0 at hz
  suffices hh : ∀ A : X.Opens, A = W → φ.app A = 0 → φ.app W = 0 from hh _ he hz
  intro A hA hφ
  subst A
  exact hφ

lemma eq_zero_of_local (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (Scheme.Modules.restrictFunctor U.ι).map φ = 0) : φ = 0 := by
  ext W m
  change φ.app W m = 0
  let F : (X : TopCat).Sheaf AddCommGrpCat := (SheafOfModules.toSheaf X.ringCatSheaf).obj N
  apply TopCat.Presheaf.section_ext F W (φ.app W m) 0
  intro x hx
  obtain ⟨U,hxU,hU⟩ := h x
  let V : X.Opens := W ⊓ U
  have hv : φ.app V = 0 := app_zero_of_restrict φ U V inf_le_right hU
  change N.presheaf.germ W x hx (φ.app W m) = N.presheaf.germ W x hx 0
  rw [← TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE (show V ≤ W from inf_le_left))
    x (show x ∈ V from ⟨hx,hxU⟩)]
  have hn := CategoryTheory.congr_fun (φ.mapPresheaf.naturality
    (homOfLE (show V ≤ W from inf_le_left)).op) m
  change φ.app V (M.presheaf.map (homOfLE inf_le_left).op m) =
    N.presheaf.map (homOfLE inf_le_left).op (φ.app W m) at hn
  rw [← hn,hv]
  simp

lemma epi_of_local (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Epi ((Scheme.Modules.restrictFunctor U.ι).map φ)) : Epi φ := by
  apply (Preadditive.epi_iff_cancel_zero _).mpr
  intro P g hg
  apply eq_zero_of_local
  intro x
  obtain ⟨U,hx,hU⟩ := h x
  let := hU
  refine ⟨U,hx,?_⟩
  apply (cancel_epi ((Scheme.Modules.restrictFunctor U.ι).map φ)).mp
  rw [← Functor.map_comp,hg,Functor.map_zero,comp_zero]

lemma mono_of_local (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((Scheme.Modules.restrictFunctor U.ι).map φ)) : Mono φ := by
  apply (Preadditive.mono_iff_cancel_zero _).mpr
  intro P g hg
  apply eq_zero_of_local
  intro x
  obtain ⟨U,hx,hU⟩ := h x
  let := hU
  refine ⟨U,hx,?_⟩
  apply (cancel_mono ((Scheme.Modules.restrictFunctor U.ι).map φ)).mp
  rw [← Functor.map_comp,hg,Functor.map_zero,zero_comp]

lemma isIso_of_local (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) : IsIso φ := by
  have : Epi φ := epi_of_local φ (fun x => by
    obtain ⟨U,hx,hU⟩ := h x
    let := hU
    exact ⟨U,hx,inferInstance⟩)
  have : Mono φ := mono_of_local φ (fun x => by
    obtain ⟨U,hx,hU⟩ := h x
    let := hU
    exact ⟨U,hx,inferInstance⟩)
  exact isIso_of_mono_of_epi φ

end
end MaximalSeshadri.ModuleLocal

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_OpenBaseChange
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma restrict_unit_app {Z T : Scheme.{0}} (i : Z ⟶ T) [IsOpenImmersion i]
    (M : T.Modules) (W : T.Opens) :
    ((Scheme.Modules.restrictAdjunction i).unit.app M).app W =
      M.presheaf.map (homOfLE (i.image_preimage_le W)).op := rfl

lemma restrict_unit_app_iso {Z T : Scheme.{0}} (i : Z ⟶ T) [IsOpenImmersion i]
    (M : T.Modules) (W : T.Opens) (hW : W ≤ i.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction i).unit.app M).app W) := by
  rw [restrict_unit_app]
  have he : i ''ᵁ i ⁻¹ᵁ W = W := by
    rw [i.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW]
  have hi : IsIso (homOfLE (i.image_preimage_le W)) :=
    homOfLE_isIso_of_eq _ he
  have : IsIso (homOfLE (i.image_preimage_le W)).op :=
    isIso_op (homOfLE (i.image_preimage_le W))
  exact M.presheaf.map_isIso (homOfLE (i.image_preimage_le W)).op

def rightSquare :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp _ _ ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
      (Scheme.Modules.pushforwardComp _ _).symm

def hom (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ⟶
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) :=
  (Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M)) ≫
  (Scheme.Modules.restrictFunctor U.ι).map
    ((rightSquare f U).hom.app (M.restrict (f ⁻¹ᵁ U).ι)) ≫
  (Scheme.Modules.restrictAdjunction U.ι).counit.app
    ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι))

instance hom_isIso (M : X.Modules) : IsIso (hom f U M) := by
  have ha : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M))) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro W
    change IsIso (((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M).app
      (f ⁻¹ᵁ (U.ι ''ᵁ W)))
    apply restrict_unit_app_iso
    rw [Scheme.Opens.opensRange_ι]
    apply (Opens.map f.base).monotone
    simpa only [Scheme.Opens.opensRange_ι] using U.ι.image_le_opensRange W
  unfold hom
  infer_instance

def iso (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) := asIso (hom f U M)

end
end MaximalSeshadri.OpenBaseChange

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_OpenPullbackUnit
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

def leftSquare :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).symm (rightSquare f U)

end
end MaximalSeshadri.OpenBaseChange

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_LineClosedUnit
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.LineClosedUnit
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def map (L : LineBundle Y) : L.sheaf ⟶
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj L.sheaf) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf

end
end MaximalSeshadri.LineClosedUnit

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_CompressionRanks
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
abbrev JetIndex (r m : ℕ) := Fin r × Fin m × Fin m

noncomputable def finiteJetColumn (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (f : ℂ → ℂ → ℂ) : JetIndex r m → ℂ := fun j =>
  if (j.2.1 : ℕ) + (j.2.2 : ℕ) < m then
    iteratedDeriv j.2.2 (fun z => iteratedDeriv j.2.1 (fun u => f u z)
      (points j.1).1) (points j.1).2 else 0

noncomputable def polynomialJetMap (r m : ℕ) (points : Fin r → ℂ × ℂ) (q : ℤ) :
    Polynomial ℂ →ₗ[ℂ] (JetIndex r m → ℂ) :=
  LinearMap.pi fun j => if (j.2.1 : ℕ) + (j.2.2 : ℕ) < m then
    (iteratedDeriv j.2.1 (fun u : ℂ => u ^ q) (points j.1).1) •
      ((Polynomial.aeval (points j.1).2).toLinearMap.comp
        ((Polynomial.derivative : Module.End ℂ (Polynomial ℂ)) ^ (j.2.2 : ℕ)))
  else 0

noncomputable def compressionRowMap (s : ℂ) (B : ℕ) : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun P := (1 + Polynomial.C s * Polynomial.X) ^ B * P.comp (1 + Polynomial.C s * Polynomial.X)
  map_add' P Q := by simp [mul_add]
  map_smul' c P := by
    simp only [Polynomial.smul_eq_C_mul, RingHom.id_apply, Polynomial.mul_comp,
      Polynomial.C_comp]
    ring

@[simp] theorem compressionRowMap_pow (s : ℂ) (B j : ℕ) :
    compressionRowMap s B (Polynomial.X ^ j) = (1 + Polynomial.C s * Polynomial.X) ^ (B + j) := by
  simp [compressionRowMap, pow_add]


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_ConvergentSeries
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set

noncomputable def monomialDeriv (n a : ℕ) (x : ℂ) : ℂ :=
  (n.descFactorial a : ℂ) * x ^ (n - a)

lemma norm_monomialDeriv_le (n a : ℕ) (x : ℂ) (R : ℝ) (hx : ‖x‖ ≤ R) :
    ‖monomialDeriv n a x‖ ≤ (n.descFactorial a : ℝ) * R ^ (n - a) := by
  simp only [monomialDeriv, norm_mul, norm_natCast, norm_pow]
  gcongr


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_Moments
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MaximalSeshadri.Interpolation

open scoped BigOperators Pointwise

def rows (s : Finset (ℤ × ℤ)) : Finset ℤ := s.image Prod.snd

def row (s : Finset (ℤ × ℤ)) (y : ℤ) : Finset ℤ :=
  (s.filter (fun p => p.2 = y)).image Prod.fst

@[simp] theorem mem_row (s : Finset (ℤ × ℤ)) (x y : ℤ) :
    x ∈ row s y ↔ (x, y) ∈ s := by
  simp only [row, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨h, rfl⟩, rfl⟩
    exact h
  · intro h
    exact ⟨(x, y), ⟨h, rfl⟩, rfl⟩

def rowMoment (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (a : ℕ) (y : ℤ) : ℂ :=
  ∑ x ∈ row s y, c (x, y) * (x : ℂ) ^ a

def EulerJetZero (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m →
    ∑ y ∈ rows s, rowMoment s c a y * (y : ℂ) ^ b = 0

def planeForm (a b c : ℝ) (p : ℝ × ℝ) : ℝ := a * p.1 + b * p.2 + c

def transverse (x₀ y₀ shear sign : ℝ) (p : ℝ × ℝ) : ℝ :=
  sign * (p.1 - x₀ - shear * (p.2 - y₀))

def balancedStrip (ρ h x₀ y₀ shear sign : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ transverse x₀ y₀ shear sign p ∧
    h * transverse x₀ y₀ shear sign p ≤ ρ * (p.2 - y₀) ∧
    (ρ - h) * transverse x₀ y₀ shear sign p ≤ ρ * (y₀ + ρ - p.2)}


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_TriangleJets
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
def triangleDoubleArea (p₀ p₁ p₂ : ℝ × ℝ) : ℝ :=
  |(p₁.1 - p₀.1) * (p₂.2 - p₀.2) - (p₂.1 - p₀.1) * (p₁.2 - p₀.2)|

noncomputable def fallingSequence : Polynomial.Sequence ℂ where
  elems' := descPochhammer ℂ
  degree_eq' n := by
    rw [Polynomial.degree_eq_natDegree (monic_descPochhammer ℂ n).ne_zero,
      descPochhammer_natDegree]

noncomputable def polynomialMoment (xs : Finset ℤ) (d : ℤ → ℂ) :
    Polynomial ℂ →ₗ[ℂ] ℂ :=
  ∑ x ∈ xs, d x • Polynomial.leval (x : ℂ)

@[simp] theorem polynomialMoment_apply (xs : Finset ℤ) (d : ℤ → ℂ) (p : Polynomial ℂ) :
    polynomialMoment xs d p = ∑ x ∈ xs, d x * p.eval (x : ℂ) := by
  simp [polynomialMoment]

def FallingJetZero (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m →
    ∑ y ∈ rows s, (∑ x ∈ row s y,
      c (x, y) * (descPochhammer ℂ a).eval (x : ℂ)) *
        (descPochhammer ℂ b).eval (y : ℂ) = 0

noncomputable def laurentEval (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (u z : ℂ) : ℂ :=
  ∑ y ∈ rows s, (∑ x ∈ row s y, c (x, y) * u ^ x) * z ^ y

def MixedJetZero (f : ℂ → ℂ → ℂ) (u z : ℂ) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m →
    iteratedDeriv b (fun v : ℂ => iteratedDeriv a (fun w : ℂ => f w v) u) z = 0


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_LaurentMoments
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise

def MomentJetZero {α : Type*} (s : Finset α) (c x y : α → ℂ) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m → ∑ p ∈ s, c p * x p ^ a * y p ^ b = 0

noncomputable def affinePolynomial (a b c : ℂ) : MvPolynomial Bool ℂ :=
  MvPolynomial.C a * MvPolynomial.X true +
    MvPolynomial.C b * MvPolynomial.X false + MvPolynomial.C c


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_PrimitiveDirections
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise

def compressedTriangle (d H t : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(-(d * H / (1 + t)), 0), (d * H * t / (1 + t), 0), (0, 1 / d)}

def directionProjection (i j : ℤ) (p : ℝ × ℝ) : ℝ :=
  (i : ℝ) * p.2 - (j : ℝ) * p.1


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_CyclicLattices
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
def latticeHeight (i j : ℤ) (p : ℤ × ℤ) : ℤ := i * p.2 - j * p.1

def latticeCoord (r : ℕ) (i j a b : ℤ) (e p : ℤ × ℤ) : ℤ × ℤ :=
  (a * (p.1 - e.1) + b * (p.2 - e.2),
    (latticeHeight i j p - latticeHeight i j e) / (r : ℤ))

noncomputable def cyclicTorusPoint (ζ : ℂ) (i j : ℤ) (l : ℕ) : ℂ × ℂ :=
  (ζ ^ (-((l : ℤ) * j)), ζ ^ ((l : ℤ) * i))

noncomputable def latticeAffine (r : ℕ) (i j a b : ℤ) (e : ℤ × ℤ) :
    (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) where
  toFun p := ((a : ℝ) * (p.1 - e.1) + (b : ℝ) * (p.2 - e.2),
    ((i : ℝ) * (p.2 - e.2) - (j : ℝ) * (p.1 - e.1)) / r)
  linear :=
    { toFun := fun p => ((a : ℝ) * p.1 + (b : ℝ) * p.2,
        ((i : ℝ) * p.2 - (j : ℝ) * p.1) / r)
      map_add' := by intro p q; ext <;> dsimp <;> ring
      map_smul' := by intro c p; ext <;> dsimp <;> ring }
  map_vadd' := by intro p v; ext <;> dsimp <;> ring


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_RowCompression
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
abbrev RowIndex {Q : Type*} (n : Q → ℕ) := (q : Q) × Fin (n q + 1)

noncomputable def verticalJetScale (r m : ℕ) (s : ℂ) :
    (JetIndex r m → ℂ) →ₗ[ℂ] (JetIndex r m → ℂ) :=
  LinearMap.pi fun j => (s ^ (j.2.2 : ℕ)) • LinearMap.proj j


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_LaurentJets
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology

noncomputable def indexedLaurent {ι : Type*} (s : Finset ι) (e : ι → ℤ × ℤ)
    (c : ι → ℂ) (u z : ℂ) : ℂ := ∑ i ∈ s, c i * u ^ (e i).1 * z ^ (e i).2


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_QuadrilateralRows
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
def nodeQuadrilateral (a b c : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(0, 0), (a, 0), (c, c), (0, b)}

def rowTriangle (a b c : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(-b, 0), (a, 0), (0, c)}

def diagonalIndex (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - p.2

noncomputable def diagonalRows (s : Finset (ℕ × ℕ)) : Finset ℤ := s.image diagonalIndex

noncomputable def diagonalRow (s : Finset (ℕ × ℕ)) (q : ℤ) : Finset (ℕ × ℕ) :=
  s.filter (fun p => diagonalIndex p = q)

noncomputable def rowStart (q : ℤ) : ℕ := (-q).toNat

noncomputable def rowHeight (s : Finset (ℕ × ℕ)) (q : ℤ) : ℕ :=
  (diagonalRow s q).sup (fun p => min p.1 p.2)

noncomputable def rowEmbedding (s : Finset (ℕ × ℕ)) (p : s) :
    RowIndex (fun q : diagonalRows s => rowHeight s q) :=
  ⟨⟨diagonalIndex p, Finset.mem_image.mpr ⟨p, p.property, rfl⟩⟩,
    ⟨min p.val.1 p.val.2, Nat.lt_succ_of_le (by
      change min p.val.1 p.val.2 ≤ (diagonalRow s (diagonalIndex p.val)).sup _
      exact Finset.le_sup (f := fun t : ℕ × ℕ => min t.1 t.2)
        (b := p.val) (Finset.mem_filter.mpr ⟨p.property, rfl⟩))⟩⟩

open scoped BigOperators Topology
open Filter Set


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_WeightedRescaling
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set

noncomputable def dilationJetScale (r m : ℕ) (a b : ℂ) :
    (JetIndex r m → ℂ) →ₗ[ℂ] (JetIndex r m → ℂ) :=
  LinearMap.pi fun j => (a ^ j.2.1.val * b ^ j.2.2.val) • LinearMap.proj j


end MaximalSeshadri.Interpolation
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_SmoothCurvePrincipal
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.LocalCurve
noncomputable section
open IsLocalRing MvPolynomial

local instance residueKernelIsPrime {Scalar CoordinateRing : Type}
    [Field Scalar] [CommRing CoordinateRing] [Algebra Scalar CoordinateRing]
    (residue : CoordinateRing →ₐ[Scalar] Scalar) : (RingHom.ker residue).IsPrime :=
  RingHom.ker_isPrime residue

end
end MaximalSeshadri.LocalCurve

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Nodal_NodalIdealDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Projective MaximalSeshadri.Frames
open MaximalSeshadri.LocalComparison
open scoped Topology

def IntegralCurve.ofIdeal (S : Surface) (I : S.scheme.IdealSheafData)
    [IsIntegral I.subscheme] (hd : topologicalKrullDim I.subscheme = 1) : IntegralCurve S :=
  ⟨I.subscheme,I.subschemeι,inferInstance,inferInstance,hd⟩

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_QuarticSubsystem
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X : Scheme}

abbrev QuarticIndex (σ : Type) := σ × σ × Option σ × Option σ

end
end MaximalSeshadri.Projective

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorPure
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry
open MaximalSeshadri.Geometry

variable {X : Scheme.{0}}

local instance sectionModule (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (op U)) :=
  (M.val.obj (op U)).isModule

abbrev presheaf (M N : X.Modules) :=
  PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M.val N.val

abbrev adj (X : Scheme.{0}) :=
  PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

end
end MaximalSeshadri.TensorPure

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorOpenSquare
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.TensorPure

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma modules_comp_app {Z : Scheme.{0}} {M N P : Z.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (W : Z.Opens) : (a ≫ b).app W = a.app W ≫ b.app W := rfl

end
end MaximalSeshadri.OpenBaseChange

end

end OAI
end


