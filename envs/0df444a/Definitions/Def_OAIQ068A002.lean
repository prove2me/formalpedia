-- Prove2me | Definitions.Def_OAIQ068A002
-- name    : OAIQ068A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:38:56.840617+00:00
-- url     : https://prove2.me/theorems/9aec3ba6-35ab-48de-bf0b-65a2884242d1
-- title:
--   Definitions bundle OAIQ068A002 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 170 declarations of OpenAI's Lean: 55 definitions, 1 inductive type or structure, 13 instances and 101 theorems. The definitions and types are `OAI.PiExponent.AlgebraicJetPackets.triangularMap`, `OAI.PiExponent.CompactJetPolynomial.center`, `OAI.PiExponent.CompactJetPolynomial.centerPoint`, `OAI.PiExponent.CompactLogJetIdeal.base`, `OAI.PiExponent.CurveLocalOrder.enatToIntegerOrder`, `OAI.PiExponent.CurveLocalOrder.fractionAddValuation`, `OAI.PiExponent.CurveLocalOrder.localAddValuation`, `OAI.PiExponent.CurveProductFormula.placeOrder`, `OAI.PiExponent.CurveProductFormula.positivePlaces`, `OAI.PiExponent.CurveValuationCenter.NormalizedPlace`, `OAI.PiExponent.CurveValuationCenter.parameterCenterLocalHom`, `OAI.PiExponent.CurveValuationCenter.parameterCenterPlace`, `OAI.PiExponent.CurveValuationCenter.parameterChartValuationHom`, `OAI.PiExponent.CurveValuationCenter.parameterNormalizedPlace`, `OAI.PiExponent.CurveValuationCenter.parameterValuationCenter`, `OAI.PiExponent.CurveValuationCenter.positivePlaceEquivZeroPlaces`, `OAI.PiExponent.CurveZeroPole.parameterAlgebra`, `OAI.PiExponent.CurveZeroPole.parameterChart`, `OAI.PiExponent.CurveZeroPole.parameterEmbedding`, `OAI.PiExponent.CurveZeroPole.parameterPlaceValuation`, `OAI.PiExponent.CurveZeroPole.parameterPolynomialAlgebra`, `OAI.PiExponent.CurveZeroPole.parameterZeroPlaces`, `OAI.PiExponent.CurveZeroPole.parameterZeroPlacesFintype`, `OAI.PiExponent.CurveZeroPole.primeFieldValuation`, `OAI.PiExponent.CurveZeroPole.zeroFiberHeightOne`, `OAI.PiExponent.CurveZeroPole.zeroPrime`, `OAI.PiExponent.DVRValuationUnique.localFieldUnit`, `OAI.PiExponent.GlobalSectionClearing.OpenSections`, `OAI.PiExponent.RamifiedLocalLength.translatedPowerLocalAlgebra`, `OAI.PiExponent.RamifiedLocalLength.translatedPowerLocalMap`, `OAI.PiExponent.SeparablePointLength.contractedPoint`, `OAI.PiExponent.SeparablePointLength.pointLocalAlgebra`, `OAI.PiExponent.SeparablePointLength.pointLocalMap`, `OAI.PiExponent.WeightedBezout.pointIdeal`, `OAI.PiExponent.WeightedBezout.translatedPowerSubstitution`, `OAI.PiExponent.WeightedCompactification.affineMonomialMap`, `OAI.PiExponent.WeightedCurveDegree.integerOrder`, `OAI.PiExponent.projectiveGenericPoint`, `OAI.PiExponentSeshadri.BlowupGluing.baseCover`, `OAI.PiExponentSeshadri.BlowupGluing.localCentre` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_BlowupProperIntegral`, `PiExponent_Ampleness_BlowupSchemeExt`, `PiExponent_Ampleness_GlobalBlowupGluing`, `PiExponent_Ampleness_ReesRelativeSections`, `PiExponent_Ampleness_ReesUniversalUniqueness`, `PiExponent_Approximation_FramedPullback`, `PiExponent_Approximation_GlobalSectionClearing`, `PiExponent_Approximation_LinePullbackPowers`, `PiExponent_Approximation_OpenBaseChange`, `PiExponent_Approximation_PowerSectionExtension`, `PiExponent_Approximation_TensorOpenBaseChange`, `PiExponent_Approximation_TensorPure`, `PiExponent_Geometry_CurveLocalOrder`, `PiExponent_Geometry_CurveProductFormula`, `PiExponent_Geometry_CurveValuationCenter`, `PiExponent_Geometry_CurveZeroPole`, `PiExponent_Geometry_LineBundleGluingSections`, `PiExponent_Geometry_PolynomialProjectiveStructure`, `PiExponent_Geometry_ProjectiveDenseChart`, `PiExponent_Geometry_ProjectiveEmbeddingCharts`, `PiExponent_Geometry_ProjectiveO1ChartMap`, `PiExponent_Geometry_ProjectivePullbackFrames`, `PiExponent_Geometry_WeightedCurveDegree`, `PiExponent_Jets_AlgebraicJetPackets`, `PiExponent_Jets_CompactJetIdeal`, `PiExponent_Jets_CompactJetPolynomial`, `PiExponent_Jets_CompactLogJetIdeal`, `PiExponent_LocalAlgebra_DVRValuationUnique`, `PiExponent_LocalAlgebra_GlobalInvertibleIdeal`, `PiExponent_LocalAlgebra_InvertibleIdealLocal`, `PiExponent_LocalAlgebra_RamifiedPointMap`, `PiExponent_LocalAlgebra_SeparablePointLength`, `PiExponent_LocalAlgebra_WeightedBezout`, `PiExponent_Polynomials_WeightedMonomialMap`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A013`, `OAIQ068A014`, `OAIQ068A015`, `OAIQ068A016`, `OAIQ068A017`, `OAIQ068A018` and `OAIQ068A019`; the statements `OAI_PiExponent_CoordinateSliceComparison_length_eq_sliceFamily_of_normalBasis`, `OAI.PiExponent.CoordinateSliceComparison.length_eq_sliceFamily_of_normalBasis_q68`, `OAI_PiExponent_CoordinateSliceComparison_sliceFamily_mem_minimalPrimes_of_normalBasis`, `OAI.PiExponent.CoordinateSliceComparison.sliceFamily_mem_minimalPrimes_of_normalBasis_q68` and `OAI_PiExponent_CurveFieldRigidity_ordinary_coordinate_constant`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupSchemeExt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace SpecMaps
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}

def coordinate (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

lemma coordinate_ext {f g : X ⟶ Spec R} (h : coordinate f = coordinate g) : f = g :=
  (ΓSpec.adjunction.homEquiv X (Opposite.op R)).symm.injective
    (Opposite.unop_injective h)

@[simp] lemma coordinate_comp (f : X ⟶ Y) (g : Y ⟶ Spec R) :
    coordinate (f ≫ g) = coordinate g ≫ f.appTop := by
  simp [coordinate]

@[simp] lemma coordinate_spec (f : R ⟶ S) : coordinate (Spec.map f) = f ≫ (Scheme.ΓSpecIso S).inv := by
  simp [coordinate]

@[simp] lemma coordinate_comp_spec (f : X ⟶ Spec S) (g : R ⟶ S) :
    coordinate (f ≫ Spec.map g) = g ≫ coordinate f := by
  simp [coordinate]

lemma factor (f : X ⟶ Spec R) :
    X.toSpecΓ ≫ Spec.map (coordinate f) = f := by
  unfold coordinate
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

lemma preimage_basicOpen (f : X ⟶ Spec R) (a : R) :
    f ⁻¹ᵁ PrimeSpectrum.basicOpen a = X.basicOpen (coordinate f a) := by
  conv_lhs => rw [← factor f]
  erw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen]
  exact Scheme.toSpecΓ_preimage_basicOpen _ _

lemma isUnit_of_basicOpen_eq_top (a : Γ(X, ⊤)) (h : X.basicOpen a = ⊤) : IsUnit a := by
  apply RingedSpace.isUnit_of_isUnit_germ X.toLocallyRingedSpace.toRingedSpace ⊤ a
  intro x hx
  apply (Scheme.mem_basicOpen X a x hx).mp
  rw [h]
  trivial

lemma isUnit_coordinate_of_preimage_top (f : X ⟶ Spec R) (a : R)
    (h : f ⁻¹ᵁ PrimeSpectrum.basicOpen a = ⊤) : IsUnit (coordinate f a) := by
  apply isUnit_of_basicOpen_eq_top
  rwa [preimage_basicOpen] at h

lemma ideal_unit_generator (I : Ideal R) (f : X ⟶ Spec R)
    (hI : I.map (coordinate f).hom = ⊤) (x : X) :
    ∃ a : I, x ∈ f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val := by
  by_contra! hn
  have hle : I ≤ (f x).asIdeal := by
    intro a ha
    exact not_not.mp (hn ⟨a, ha⟩)
  have hmap : I.map (coordinate f).hom ≤ (X.toSpecΓ x).asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hm := hle ha
    rw [← factor f, Scheme.Hom.comp_apply, Spec.map_apply] at hm
    exact hm
  rw [hI] at hmap
  exact (X.toSpecΓ x).isPrime.ne_top (top_unique hmap)

end SpecMaps

namespace SchematicExt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable {W X Y Z : Scheme.{u}}

lemma ext_of_ker_eq_bot_of_isSeparated {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) (hι : ι.ker = ⊥) (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  let l : U' ⟶ equalizer f' g' := equalizer.lift ι' (by ext1; exact hU)
  have hl : l.left ≫ (equalizer.ι f' g').left = ι := by
    change (l ≫ equalizer.ι f' g').left = ι
    exact congrArg (fun k : U' ⟶ X' => k.left) (equalizer.lift_ι ι' _)
  have hk : (equalizer.ι f' g').left.ker = ⊥ := by
    apply bot_unique
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := l.left.le_ker_comp _
         _ = ⊥ := by rw [hl, hι]
  have : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

lemma basicOpen_ker_eq_bot [IsAffine X] (r : Γ(X, ⊤)) (hr : IsRegular r) :
    (X.basicOpen r).ι.ker = ⊥ := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  apply bot_unique
  apply ((X.basicOpen r).ι.ideal_ker_le ⟨⊤, isAffineOpen_top X⟩).trans
  apply le_of_eq
  rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  have hinj : Function.Injective (algebraMap Γ(X, ⊤) Γ(X.basicOpen r, ⊤)) :=
    IsLocalization.injective (Γ(X.basicOpen r, ⊤))
      (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp hr))
  apply hinj
  change (algebraMap Γ(X, ⊤) Γ(X.basicOpen r, ⊤)) x = 0 at hx
  simpa only [map_zero] using hx

end SchematicExt

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesUniversalUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ProjBase
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma basicOpenToSpec_eq (f : A) :
    Scheme.forgetToLocallyRingedSpace.map (Proj.basicOpenToSpec 𝒜 f) =
      ProjectiveSpectrum.Proj.toSpec 𝒜 f := by
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

lemma basicOpenToSpec_mem (f : A) (x : Proj.basicOpen 𝒜 f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ ((Proj.basicOpenToSpec 𝒜 f) x).asIdeal ↔
      z.num.val ∈ x.val.asHomogeneousIdeal := by
  have he := congr($(basicOpenToSpec_eq 𝒜 f).base x)
  change (Proj.basicOpenToSpec 𝒜 f) x = (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base x at he
  rw [he]
  exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 x z

lemma toSpecZero_mem (x : Proj 𝒜) (a : 𝒜 0) :
    a ∈ ((Proj.toSpecZero 𝒜) x).asIdeal ↔ a.val ∈ x.asHomogeneousIdeal := by
  simp only [Proj.toSpecZero, Scheme.Hom.comp_apply, Spec.map_apply]
  change HomogeneousLocalization.fromZeroRingHom 𝒜 (.powers (1 : A)) a ∈
    ((Proj.basicOpenToSpec 𝒜 1) _).asIdeal ↔ _
  rw [show HomogeneousLocalization.fromZeroRingHom 𝒜 (.powers (1 : A)) a =
    HomogeneousLocalization.mk ⟨0, a, 1, one_mem _⟩ from rfl]
  erw [basicOpenToSpec_mem]
  change a.val ∈ ((Proj.basicOpen 𝒜 (1 : A)).ι
    (((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv ((Proj 𝒜).topIso.inv x))).asHomogeneousIdeal ↔ _
  rw [← Scheme.Hom.comp_apply, Scheme.isoOfEq_inv_ι, ← Scheme.Hom.comp_apply]
  rw [Scheme.toIso_inv_ι]; rfl

end PiExponentSeshadri.ProjBase

namespace PiExponentSeshadri.ReesGrading
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

open SpecMaps

lemma principal_basicOpen_unit_ideal {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (r : Γ(Y, ⊤)) (hI : I.map (coordinate f).hom = Ideal.span {r}) :
    I.map (coordinate ((Y.basicOpen r).ι ≫ f)).hom = ⊤ := by
  rw [coordinate_comp]
  change I.map ((Y.basicOpen r).ι.appTop.hom.comp (coordinate f).hom) = ⊤
  rw [← Ideal.map_map, hI, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
  apply isUnit_of_basicOpen_eq_top
  rw [← Scheme.preimage_basicOpen_top]
  exact (Y.basicOpen r).ι_preimage_self

end PiExponentSeshadri.ReesGrading

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_PowerSectionExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma affine_function_denom [IsAffine X] (a : Γ(X, ⊤))
    (f : Γ((X.basicOpen a).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ g : Γ(X, ⊤),
      (X.basicOpen a).ι.appTop g = f * (X.basicOpen a).ι.appTop a ^ n := by
  obtain ⟨N, g, hg⟩ := IsLocalization.Away.surj a f
  refine ⟨N, fun n hn => ⟨g * a ^ (n - N), ?_⟩⟩
  change algebraMap Γ(X, ⊤) Γ((X.basicOpen a).toScheme, ⊤) (g * a ^ (n - N)) =
    f * algebraMap Γ(X, ⊤) Γ((X.basicOpen a).toScheme, ⊤) a ^ n
  rw [map_mul, map_pow, ← hg, mul_assoc, ← pow_add, Nat.add_sub_of_le hn]

end

open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry

end Geometry

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_InvertibleIdealLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.UnitEndomorphism
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}}
abbrev unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf
variable (g : unit X ⟶ unit X)

def equation (U : X.Opens) : Γ(X, U) := g.val.app (op U) (1 : Γ(X, U))

lemma app_eq_mul (U : X.Opens) (a : Γ(X, U)) :
    g.val.app (op U) a = equation g U * a := by
  let F : Γ(X, U) →ₗ[Γ(X, U)] Γ(X, U) := (g.val.app (op U)).hom
  have h := F.map_smul a (1 : Γ(X, U))
  simpa only [smul_eq_mul, mul_one, mul_comm a, one_mul, F, equation] using! h

lemma image_principal (U : X.Opens) :
    (show Ideal Γ(X, U) from (g.val.app (op U)).hom.range) = Ideal.span {equation g U} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact Ideal.mem_span_singleton.mpr ⟨b, app_eq_mul g U b⟩
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
    exact ⟨b, (app_eq_mul g U b).trans hb.symm⟩

lemma equation_regular [Mono g] (U : X.Opens) : IsRegular (equation g U) := by
  let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map g))
  have hinj := PresheafOfModules.injective_of_mono g.val (op U)
  apply (Commute.isRegular_iff (fun a => Commute.all _ a)).mpr
  intro a b hab
  apply hinj
  simpa only [app_eq_mul] using! hab

end PiExponentSeshadri.UnitEndomorphism
namespace PiExponentSeshadri.InvertibleLocal

section
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry
universe u
variable {X Y Z : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)

variable {I f}

theorem mono_iso_inv_comp_p1 {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (g : A ⟶ D) [Mono g] : Mono (e.inv ≫ g) := inferInstance

end

open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry

end PiExponentSeshadri.InvertibleLocal

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_GlobalInvertibleIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.InvertibleLocal
noncomputable section

section
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry
variable {X Y Z : Scheme} {I : X.IdealSheafData} {f : Y ⟶ X}

theorem mono_iso_inv_comp_p0 {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (g : A ⟶ D) [Mono g] : Mono (e.inv ≫ g) := inferInstance

end

open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry

end
end PiExponentSeshadri.InvertibleLocal

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_GlobalBlowupGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.BlowupGluing

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} (I : X.IdealSheafData)

abbrev baseCover (_I : X.IdealSheafData) : X.OpenCover := Scheme.AffineZariskiSite.directedCover X

local instance localAffine (U : X.AffineZariskiSite) : IsAffine U.toOpens.toScheme := U.2

abbrev localCentre (U : X.AffineZariskiSite) : U.toOpens.toScheme.IdealSheafData := I.comap U.toOpens.ι

lemma centre_transition {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    (localCentre I V).comap ((baseCover I).trans h) = localCentre I U := by
  rw [localCentre, ← Scheme.IdealSheafData.comap_comp]
  change I.comap ((baseCover I).trans h ≫ (baseCover I).f V) = _
  rw [Scheme.Cover.trans_map]

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry

end PiExponentSeshadri.BlowupGluing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupProperIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace PiExponentSeshadri.ProjectiveGeometry
open AlgebraicGeometry
universe u v
variable {A : Type u} {σ : Type v} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

instance homogeneous_isReduced (S : Submonoid A) [_root_.IsReduced A] :
    _root_.IsReduced (HomogeneousLocalization 𝒜 S) :=
  isReduced_of_injective (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S))
    (HomogeneousLocalization.val_injective S)

instance proj_isReduced [_root_.IsReduced A] : IsReduced (Proj 𝒜) := by
  have (x : Proj 𝒜) : _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) :=
    isReduced_of_injective (Proj.stalkIso' 𝒜 x) (Proj.stalkIso' 𝒜 x).injective
  exact isReduced_of_isReduced_stalk _

def genericPoint [IsDomain A] [Nonempty (Proj 𝒜)] : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := Ideal.isPrime_bot
  not_irrelevant_le h := by
    obtain ⟨x⟩ := ‹Nonempty (Proj 𝒜)›
    exact x.not_irrelevant_le (h.trans bot_le)

lemma genericPoint_dense [IsDomain A] [Nonempty (Proj 𝒜)] :
    closure ({genericPoint 𝒜} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 _ _).mp
    (show (genericPoint 𝒜).asHomogeneousIdeal ≤ x.asHomogeneousIdeal from bot_le)

instance proj_irreducible [IsDomain A] [Nonempty (Proj 𝒜)] :
    IrreducibleSpace (Proj 𝒜) := by
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
  rw [← genericPoint_dense 𝒜]
  exact (isIrreducible_singleton).closure

instance proj_isIntegral [IsDomain A] [Nonempty (Proj 𝒜)] : IsIntegral (Proj 𝒜) :=
  (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

end PiExponentSeshadri.ProjectiveGeometry

namespace PiExponentSeshadri.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

abbrev centreComplement (I : X.IdealSheafData) : X.Opens := I.support.compl

lemma complement_nonempty (hI : I.support ≠ ⊤) : Nonempty (centreComplement I).toScheme := by
  by_contra h
  apply hI
  ext x
  change x ∈ I.support ↔ True
  rw [iff_true]
  by_contra hx
  exact h ⟨⟨x, hx⟩⟩

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.ReesGrading
open AlgebraicGeometry Polynomial
variable {R : Type} [CommRing R] (I : Ideal R)

instance polynomial_isReduced [_root_.IsReduced R] : _root_.IsReduced R[X] where
  eq_zero p hp := by
    ext n
    exact (Polynomial.isNilpotent_iff.mp hp n).eq_zero

end PiExponentSeshadri.ReesGrading

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_OpenBaseChange
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.OpenBaseChange
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
  let e := @asIso _ _ _ _ (homOfLE (i.image_preimage_le W)) hi
  exact (M.presheaf.mapIso e.op).isIso_hom

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
end PiExponentSeshadri.OpenBaseChange

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TensorPure
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.TensorPure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
open MonoidalCategory

variable {X Y : Scheme.{0}}

local instance sectionModule {X : Scheme.{0}}
    (P : PresheafOfModules X.ringCatSheaf.obj) (U : X.Opens) :
    Module Γ(X, U) (P.obj (op U)) := (P.obj (op U)).isModule

abbrev presheaf (M N : X.Modules) :=
  PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M.val N.val

abbrev adj (X : Scheme.{0}) :=
  PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

end PiExponentSeshadri.TensorPure

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TensorOpenBaseChange
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.OpenBaseChange

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

def leftSquare :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).symm (rightSquare f U)

lemma unit_compatibility (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (iso f U ((Scheme.Modules.pullback f).obj M)).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M) := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction f
  let b := Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι
  let c := Scheme.Modules.restrictAdjunction U.ι
  let d := Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)
  have h := unit_conjugateEquiv_symm (a.comp b) (c.comp d) (rightSquare f U).hom M
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  change (a.unit.app M ≫ (Scheme.Modules.pushforward f).map
    (b.unit.app ((Scheme.Modules.pullback f).obj M))) ≫
      (rightSquare f U).hom.app _ =
    (c.unit.app M ≫ (Scheme.Modules.pushforward U.ι).map
      (d.unit.app (M.restrict U.ι))) ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M)) at h
  have hc := congrArg (fun q => (Scheme.Modules.restrictFunctor U.ι).map q ≫
    c.counit.app ((Scheme.Modules.pushforward (f ∣_ U)).obj
      (((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι))) h
  simp only [Functor.map_comp, Category.assoc] at hc
  change _ = _ at hc
  have hn := c.counit.naturality
    (d.unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [Functor.map_comp, Functor.map_comp] at hn
  rw [Category.assoc] at hn
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [hn] at hc
  simp only [← Category.assoc] at hc
  have ht := c.left_triangle_components M
  change (Scheme.Modules.restrictFunctor U.ι).map (c.unit.app M) ≫
    c.counit.app (M.restrict U.ι) = 𝟙 _ at ht
  rw [ht, Category.id_comp] at hc
  simpa only [a, b, c, d, iso, asIso_hom, hom, Category.assoc] using hc

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma modules_comp_app {Z : Scheme.{0}} {M N P : Z.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (W : Z.Opens) : (a ≫ b).app W = a.app W ≫ b.app W := rfl

lemma hom_app (M : X.Modules) (V : U.toScheme.Opens) :
    (hom f U M).app V = M.presheaf.map
      (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  change ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M).app
    (f ⁻¹ᵁ (U.ι ''ᵁ V)) ≫
      ((rightSquare f U).hom.app (M.restrict (f ⁻¹ᵁ U).ι)).app (U.ι ''ᵁ V) ≫
      ((Scheme.Modules.restrictAdjunction U.ι).counit.app
        ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι))).app V = _
  simp only [rightSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_counit_app_app]
  simp only [modules_comp_app,Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  simp only [Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.restrict_map]
  erw [Category.id_comp, Category.comp_id, ← Functor.map_comp, ← Functor.map_comp]
  congr 1

@[reassoc] lemma naturality {M N : X.Modules} (a : M ⟶ N) :
    (Scheme.Modules.restrictFunctor U.ι).map ((Scheme.Modules.pushforward f).map a) ≫
      (iso f U N).hom =
    (iso f U M).hom ≫ (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map a) := by
  ext V x
  change (hom f U N).app V (a.app (f ⁻¹ᵁ (U.ι ''ᵁ V)) x) =
    a.app ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) ((hom f U M).app V x)
  rw [hom_app,hom_app]
  exact (CategoryTheory.congr_fun (a.mapPresheaf.naturality
    (eqToHom (image_morphismRestrict_preimage f U V)).op) x).symm

end PiExponentSeshadri.OpenBaseChange

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_LinePullbackPowers
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.PullbackTensor
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma open_transpose (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      ((OpenBaseChange.leftSquare f U).hom.app M) =
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)).hom :=
  (OpenBaseChange.unit_compatibility f U M).symm

end PiExponentSeshadri.PullbackTensor

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesRelativeSections
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ReesGrading
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.SpecMaps

theorem mono_inv_comp {D : Type*} [Category D] {A B C : D}
    (e : A ≅ B) (f : A ⟶ C) (hf : Mono f) : Mono (e.inv ≫ f) := by
  let := hf
  infer_instance

theorem map_comp_through {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B T : C} {U V : D}
    (u : U ⟶ F.obj A) (s : A ⟶ B) (t : B ⟶ T) (v : F.obj T ⟶ V) :
    (u ≫ F.map s) ≫ F.map t ≫ v = (u ≫ F.map (s ≫ t)) ≫ v := by
  simp only [Functor.map_comp, Category.assoc]

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.SpecMaps
end PiExponentSeshadri.ReesGrading

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FramedPullback
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
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

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlobalSectionClearing
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GlobalSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}

def OpenSections (M : X.Modules) (U : X.Opens) := Γ(M,U)

end
end PiExponent.GlobalSectionClearing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_WeightedCurveDegree
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.WeightedCurveDegree

noncomputable def integerOrder {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) : ℤ :=
  (v (x : K)).untop ((AddValuation.top_iff v).not.mpr x.ne_zero)

@[simp] theorem coe_integerOrder {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) :
    (integerOrder v x : WithTop ℤ) = v (x : K) := WithTop.coe_untop _ _

@[simp] theorem integerOrder_one {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : integerOrder v 1 = 0 := by
  apply WithTop.coe_injective
  simp

@[simp] theorem integerOrder_mul {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x y : Kˣ) :
    integerOrder v (x * y) = integerOrder v x + integerOrder v y := by
  apply WithTop.coe_injective
  simp

@[simp] theorem integerOrder_pow {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) (n : ℕ) :
    integerOrder v (x ^ n) = n * integerOrder v x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, integerOrder_mul, ih]; push_cast; ring

@[simp] theorem integerOrder_prod {K ι : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (s : Finset ι) (x : ι → Kˣ) :
    integerOrder v (∏ i ∈ s, x i) = ∑ i ∈ s, integerOrder v (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

@[simp] theorem integerOrder_inv {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) :
    integerOrder v x⁻¹ = -integerOrder v x := by
  apply WithTop.coe_injective
  simp

@[simp] theorem integerOrder_div {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x y : Kˣ) :
    integerOrder v (x / y) = integerOrder v x - integerOrder v y := by
  simp [div_eq_mul_inv, sub_eq_add_neg]

end PiExponent.WeightedCurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveLocalOrder
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators nonZeroDivisors
open IsLocalRing IsDiscreteValuationRing

namespace PiExponent.CurveLocalOrder

def enatToIntegerOrder : ℕ∞ →+ WithTop ℤ where
  toFun := ENat.map (fun n : ℕ => (n : ℤ))
  map_zero' := by simp
  map_add' a b := ENat.map_add (Nat.castAddMonoidHom ℤ) a b

@[simp] theorem enatToIntegerOrder_top : enatToIntegerOrder ⊤ = ⊤ := rfl

@[simp] theorem enatToIntegerOrder_natCast (n : ℕ) :
    enatToIntegerOrder n = (n : WithTop ℤ) := rfl

@[simp] theorem enatToIntegerOrder_eq_top_iff (n : ℕ∞) :
    enatToIntegerOrder n = ⊤ ↔ n = ⊤ := ENat.map_eq_top_iff

theorem enatToIntegerOrder_monotone : Monotone enatToIntegerOrder := by
  apply ENat.monotone_map_iff.mpr
  intro m n h
  change (m : ℤ) ≤ (n : ℤ)
  exact_mod_cast h

noncomputable def localAddValuation
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    AddValuation A (WithTop ℤ) :=
  (IsDiscreteValuationRing.addVal A).map enatToIntegerOrder
    enatToIntegerOrder_top enatToIntegerOrder_monotone

@[simp] theorem localAddValuation_apply
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (a : A) :
    localAddValuation A a = enatToIntegerOrder (IsDiscreteValuationRing.addVal A a) := rfl

@[simp] theorem localAddValuation_eq_top_iff
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (a : A) :
    localAddValuation A a = ⊤ ↔ a = 0 := by
  rw [localAddValuation_apply, enatToIntegerOrder_eq_top_iff,
    IsDiscreteValuationRing.addVal_eq_top_iff]

theorem nonZeroDivisors_le_primeCompl
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    nonZeroDivisors A ≤ (localAddValuation A).toValuation.supp.primeCompl := by
  intro a ha
  change localAddValuation A a ≠ ⊤
  rw [ne_eq, localAddValuation_eq_top_iff]
  exact mem_nonZeroDivisors_iff_ne_zero.mp ha

noncomputable def fractionAddValuation
    (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] : AddValuation K (WithTop ℤ) :=
  AddValuation.ofValuation
    ((localAddValuation A).toValuation.extendToLocalization
      (nonZeroDivisors_le_primeCompl A) K)

@[simp] theorem fractionAddValuation_algebraMap
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (a : A) :
    fractionAddValuation A K (algebraMap A K a) = localAddValuation A a := by
  exact Valuation.extendToLocalization_apply_map_apply
    (localAddValuation A).toValuation (nonZeroDivisors_le_primeCompl A) K a

end PiExponent.CurveLocalOrder

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveZeroPole
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Polynomial nonZeroDivisors

namespace PiExponent.CurveZeroPole

theorem adjoin_inverse_eq {F E : Type*} [Field F] [Field E] [Algebra F E] (f : E) :
    IntermediateField.adjoin F {f⁻¹} = IntermediateField.adjoin F {f} := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.inv_mem _ (IntermediateField.subset_adjoin F {f} (by simp)))
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    simpa using IntermediateField.inv_mem (IntermediateField.adjoin F {f⁻¹})
      (show f⁻¹ ∈ IntermediateField.adjoin F {f⁻¹} from
        IntermediateField.subset_adjoin F {f⁻¹} (Set.mem_singleton _))

def parameterEmbedding {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : RatFunc F →ₐ[F] E :=
  (IntermediateField.val (IntermediateField.adjoin F {f})).comp
    (RatFunc.algEquivOfTranscendental f hf).toAlgHom

@[simp] theorem parameterEmbedding_X {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : parameterEmbedding f hf RatFunc.X = f := by
  simp [parameterEmbedding]

abbrev parameterAlgebra {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra (RatFunc F) E :=
  (parameterEmbedding f hf).toRingHom.toAlgebra

theorem parameter_finite {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    let := parameterAlgebra f hf
    FiniteDimensional (RatFunc F) E := by
  let := parameterAlgebra f hf
  let e := RatFunc.algEquivOfTranscendental f hf
  let b := Module.finBasis (IntermediateField.adjoin F {f}) E
  apply (b.mapCoeffs e.symm.toRingEquiv ?_).finiteDimensional_of_finite
  intro c x
  change (↑(e (e.symm c)) : E) * x = (c : E) * x
  rw [e.apply_symm_apply]

abbrev parameterPolynomialAlgebra {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra F[X] E :=
  ((parameterEmbedding f hf).toRingHom.comp (algebraMap F[X] (RatFunc F))).toAlgebra

theorem parameter_scalarTower {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    let := parameterAlgebra f hf
    let := parameterPolynomialAlgebra f hf
    IsScalarTower F[X] (RatFunc F) E := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl

def zeroPrime (F : Type*) [Field F] : Ideal F[X] :=
  RingHom.ker Polynomial.constantCoeff

theorem zeroPrime_eq_span_X (F : Type*) [Field F] :
    zeroPrime F = Ideal.span {Polynomial.X} := Polynomial.ker_constantCoeff

theorem constantCoeff_surjective (F : Type*) [Field F] :
    Function.Surjective (Polynomial.constantCoeff : F[X] →+* F) := by
  intro x
  exact ⟨Polynomial.C x, by simp⟩

instance zeroPrime_isMaximal (F : Type*) [Field F] : (zeroPrime F).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective Polynomial.constantCoeff (constantCoeff_surjective F)

def primeFieldValuation (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) : AddValuation E (WithTop ℤ) :=
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  CurveLocalOrder.fractionAddValuation A E

theorem zeroPrime_ne_bot (F : Type*) [Field F] : zeroPrime F ≠ ⊥ := by
  intro h
  have hx : Polynomial.X ∈ zeroPrime F := by
    change Polynomial.constantCoeff Polynomial.X = (0 : F)
    simp
  rw [h, Ideal.mem_bot] at hx
  exact Polynomial.X_ne_zero hx

def zeroFiberHeightOne (F S : Type*) [Field F] [CommRing S] [IsDomain S]
    [Algebra F[X] S] [FaithfulSMul F[X] S]
    (q : (zeroPrime F).primesOver S) : IsDedekindDomain.HeightOneSpectrum S :=
  ⟨q.1, q.2.1, Ideal.ne_bot_of_mem_primesOver (zeroPrime_ne_bot F) q.2⟩

abbrev parameterChart {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Type _ :=
  let := parameterPolynomialAlgebra f hf
  FunctionField.ringOfIntegers F E

abbrev parameterZeroPlaces {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Type _ :=
  let := parameterPolynomialAlgebra f hf
  (zeroPrime F).primesOver (parameterChart f hf)

abbrev parameterZeroPlacesFintype
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    Fintype (parameterZeroPlaces f hf) :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  (Algebra.QuasiFinite.finite_primesOver
    (R := F[X]) (S := FunctionField.ringOfIntegers F E) (zeroPrime F)).fintype

def parameterPlaceValuation
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) : AddValuation E (WithTop ℤ) :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  primeFieldValuation (parameterChart f hf) E
    (zeroFiberHeightOne F (parameterChart f hf) q)

theorem parameterPolynomialAlgebra_map
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : F[X]) :
    letI := parameterPolynomialAlgebra f hf
    algebraMap F[X] E p = Polynomial.aeval f p := by
  let := parameterPolynomialAlgebra f hf
  change parameterEmbedding f hf (algebraMap F[X] (RatFunc F) p) = Polynomial.aeval f p
  change (↑(RatFunc.algEquivOfTranscendental f hf (algebraMap F[X] (RatFunc F) p)) : E) = _
  rw [RatFunc.algEquivOfTranscendental_algebraMap]
  exact IntermediateField.AdjoinSimple.coe_aeval_gen_apply F f p

end PiExponent.CurveZeroPole

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_DVRValuationUnique
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped nonZeroDivisors
open PiExponent.WeightedCurveDegree PiExponent.CurveLocalOrder

namespace PiExponent.DVRValuationUnique

variable {A E : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field E] [Algebra A E] [IsFractionRing A E]

def localFieldUnit (a : A) (ha : a ≠ 0) : Eˣ :=
  Units.mk0 (algebraMap A E a) ((map_ne_zero_iff _ (IsFractionRing.injective A E)).mpr ha)

omit [IsDomain A] [IsDiscreteValuationRing A] in
@[simp] theorem localFieldUnit_val (a : A) (ha : a ≠ 0) :
    ((localFieldUnit (E := E) a ha : Eˣ) : E) = algebraMap A E a := rfl

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A E] in
theorem integerOrder_unit_eq_zero
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a)) (u : Aˣ) :
    integerOrder v (Units.map (algebraMap A E) u) = 0 := by
  have hpos : 0 ≤ integerOrder v (Units.map (algebraMap A E) u) := by
    apply WithTop.coe_le_coe.mp
    simpa using hregular (u : A)
  have hneg : 0 ≤ integerOrder v (Units.map (algebraMap A E) u⁻¹) := by
    apply WithTop.coe_le_coe.mp
    simpa using hregular (u⁻¹ : Aˣ)
  simp only [map_inv, integerOrder_inv] at hneg
  omega

theorem exists_order_eq_uniformizer_multiple
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a))
    {π : A} (hπ : Irreducible π) (a : A) (ha : a ≠ 0) :
    ∃ n : ℕ, integerOrder v (localFieldUnit (E := E) a ha) =
      (n : ℤ) * integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) ∧
      IsDiscreteValuationRing.addVal A a = n := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  refine ⟨n, ?_, IsDiscreteValuationRing.addVal_def' u hπ n⟩
  have he : localFieldUnit (E := E) ((u : A) * π ^ n) ha =
      Units.map (algebraMap A E) u * localFieldUnit (E := E) π hπ.ne_zero ^ n := by
    ext
    simp [localFieldUnit, map_mul, map_pow]
  rw [he, integerOrder_mul, integerOrder_pow, integerOrder_unit_eq_zero v hregular]
  simp

theorem uniformizer_order_dvd
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a))
    {π : A} (hπ : Irreducible π) (z : Eˣ) :
    integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) ∣ integerOrder v z := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A (z : E)
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by
    intro ha
    apply z.ne_zero
    rw [← hab, ha, map_zero, zero_div]
  have hz : z = localFieldUnit (E := E) a ha0 / localFieldUnit (E := E) b hb0 := by
    ext
    simpa only [Units.val_div_eq_div_val, localFieldUnit_val] using hab.symm
  obtain ⟨m, hm, _⟩ := exists_order_eq_uniformizer_multiple v hregular hπ a ha0
  obtain ⟨n, hn, _⟩ := exists_order_eq_uniformizer_multiple v hregular hπ b hb0
  rw [hz, integerOrder_div, hm, hn]
  exact ⟨(m : ℤ) - n, by ring⟩

theorem eq_fractionAddValuation
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a))
    (hcenter : ∀ a ∈ IsLocalRing.maximalIdeal A, a ≠ 0 → 0 < v (algebraMap A E a))
    (hnormalized : ∃ z : Eˣ, integerOrder v z = 1) :
    v = fractionAddValuation A E := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπmem : π ∈ IsLocalRing.maximalIdeal A := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton π)
  have hpos : 0 < integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) := by
    apply WithTop.coe_lt_coe.mp
    simpa using hcenter π hπmem hπ.ne_zero
  have hone : integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) = 1 := by
    obtain ⟨z, hz⟩ := hnormalized
    apply Int.eq_one_of_dvd_one hpos.le
    rw [← hz]
    exact uniformizer_order_dvd v hregular hπ z
  have hlocal (a : A) : v (algebraMap A E a) = localAddValuation A a := by
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, hn, hcanonical⟩ := exists_order_eq_uniformizer_multiple v hregular hπ a ha
    rw [hone, mul_one] at hn
    rw [localAddValuation_apply, hcanonical, enatToIntegerOrder_natCast]
    rw [← localFieldUnit_val a ha, ← coe_integerOrder, hn]
    rfl
  ext x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A x
  rw [AddValuation.map_div, AddValuation.map_div, hlocal, hlocal,
    fractionAddValuation_algebraMap, fractionAddValuation_algebraMap]

theorem fractionAddValuation_normalized :
    ∃ z : Eˣ, integerOrder (fractionAddValuation A E) z = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  refine ⟨localFieldUnit (E := E) π hπ.ne_zero, ?_⟩
  apply WithTop.coe_injective
  rw [coe_integerOrder, localFieldUnit_val, fractionAddValuation_algebraMap,
    localAddValuation_apply, IsDiscreteValuationRing.addVal_uniformizer hπ]
  rfl

end PiExponent.DVRValuationUnique

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveValuationCenter
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.CurveValuationCenter
open PiExponent.CurveZeroPole

theorem integral_mem_valuationSubring
    {R E Γ : Type*} [CommRing R] [Field E] [LinearOrderedCommGroupWithZero Γ]
    [Algebra R E] (v : Valuation E Γ)
    (hR : ∀ r : R, algebraMap R E r ∈ v.valuationSubring)
    {x : E} (hx : IsIntegral R x) : x ∈ v.valuationSubring := by
  let φ : R →+* v.valuationSubring :=
    { toFun := fun r => ⟨algebraMap R E r, hR r⟩
      map_zero' := by ext; simp
      map_one' := by ext; simp
      map_add' := by intros; ext; simp
      map_mul' := by intros; ext; simp }
  let : Algebra R v.valuationSubring := φ.toAlgebra
  let : IsScalarTower R v.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (Valuation.valuationSubring.integers v).mem_of_integral hx.tower_top

theorem aeval_mem_valuationSubring
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (f : E) (hf : 0 ≤ v f) (p : F[X]) :
    Polynomial.aeval f p ∈ v.toValuation.valuationSubring := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact v.toValuation.valuationSubring.toSubring.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact v.toValuation.valuationSubring.toSubring.mul_mem (hF a)
      (v.toValuation.valuationSubring.toSubring.pow_mem hf n)

theorem parameterChart_mem_valuationSubring
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) (x : parameterChart f hf) :
    (x : E) ∈ v.toValuation.valuationSubring := by
  let := parameterPolynomialAlgebra f hf
  apply integral_mem_valuationSubring v.toValuation
    (fun p => ?_) x.property
  rw [parameterPolynomialAlgebra_map f hf p]
  exact aeval_mem_valuationSubring v hF f hvf p

def parameterChartValuationHom
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) : parameterChart f hf →+* v.toValuation.valuationSubring where
  toFun x := ⟨x, parameterChart_mem_valuationSubring f hf v hF hvf x⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def parameterValuationCenter
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) : Ideal (parameterChart f hf) :=
  (IsLocalRing.maximalIdeal v.toValuation.valuationSubring).comap
    (parameterChartValuationHom f hf v hF hvf)

instance parameterValuationCenter_isPrime
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) : (parameterValuationCenter f hf v hF hvf).IsPrime :=
  inferInstanceAs (Ideal.comap _ (IsLocalRing.maximalIdeal _)).IsPrime

theorem mem_parameterValuationCenter_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) (x : parameterChart f hf) :
    x ∈ parameterValuationCenter f hf v hF hvf ↔ 0 < v (x : E) := by
  change parameterChartValuationHom f hf v hF hvf x ∈
    IsLocalRing.maximalIdeal v.toValuation.valuationSubring ↔ _
  exact v.toValuation.mem_maximalIdeal_iff

theorem parameterValuationCenter_liesOver
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 < v f) :
    letI := parameterPolynomialAlgebra f hf
    (parameterValuationCenter f hf v hF hvf.le).LiesOver (zeroPrime F) := by
  let := parameterPolynomialAlgebra f hf
  constructor
  apply (zeroPrime_isMaximal F).eq_of_le
  · exact Ideal.IsPrime.ne_top inferInstance
  rw [zeroPrime_eq_span_X, Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
  rw [mem_parameterValuationCenter_iff]
  change 0 < v (algebraMap F[X] E Polynomial.X)
  rw [parameterPolynomialAlgebra_map f hf Polynomial.X, Polynomial.aeval_X]
  exact hvf

def parameterCenterPlace
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 < v f) : parameterZeroPlaces f hf :=
  let := parameterPolynomialAlgebra f hf
  let := parameterValuationCenter_liesOver f hf v hF hvf
  Ideal.primesOver.mk (zeroPrime F) (parameterValuationCenter f hf v hF hvf.le)

def parameterCenterLocalHom
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) :
    Localization.AtPrime (parameterValuationCenter f hf v hF hvf) →+*
      v.toValuation.valuationSubring :=
  IsLocalization.lift (M := (parameterValuationCenter f hf v hF hvf).primeCompl)
    (g := parameterChartValuationHom f hf v hF hvf) (fun y => by
      have hy : parameterChartValuationHom f hf v hF hvf y ∉
          IsLocalRing.maximalIdeal v.toValuation.valuationSubring := y.property
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hy)

@[simp] theorem parameterCenterLocalHom_algebraMap
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) (x : parameterChart f hf) :
    parameterCenterLocalHom f hf v hF hvf
      (algebraMap (parameterChart f hf) _ x) = parameterChartValuationHom f hf v hF hvf x :=
  IsLocalization.lift_eq _ x

theorem parameterCenterLocalHom_comap_maximalIdeal
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) :
    (IsLocalRing.maximalIdeal v.toValuation.valuationSubring).comap
      (parameterCenterLocalHom f hf v hF hvf) =
    IsLocalRing.maximalIdeal (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) := by
  apply (Localization.AtPrime.eq_maximalIdeal_iff_under_eq
    (I := parameterValuationCenter f hf v hF hvf)).mp
  ext x
  change parameterCenterLocalHom f hf v hF hvf
    (algebraMap (parameterChart f hf) _ x) ∈
      IsLocalRing.maximalIdeal v.toValuation.valuationSubring ↔ _
  rw [parameterCenterLocalHom_algebraMap]
  rfl

theorem parameterCenterLocalHom_coe
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f)
    [Algebra (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    [IsScalarTower (parameterChart f hf)
      (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    (a : Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) :
    (parameterCenterLocalHom f hf v hF hvf a : E) = algebraMap _ E a := by
  have hm : v.toValuation.valuationSubring.subtype.comp
      (parameterCenterLocalHom f hf v hF hvf) = algebraMap _ E := by
    apply IsLocalization.ringHom_ext (parameterValuationCenter f hf v hF hvf).primeCompl
    ext x
    simp only [RingHom.comp_apply]
    rw [parameterCenterLocalHom_algebraMap]
    exact (IsScalarTower.algebraMap_apply (parameterChart f hf)
      (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E x)
  exact RingHom.congr_fun hm a

theorem parameterCenterLocal_nonneg
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f)
    [Algebra (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    [IsScalarTower (parameterChart f hf)
      (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    (a : Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) :
    0 ≤ v (algebraMap _ E a) := by
  rw [← parameterCenterLocalHom_coe f hf v hF hvf a]
  exact (parameterCenterLocalHom f hf v hF hvf a).property

theorem parameterCenterLocal_positive
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f)
    [Algebra (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    [IsScalarTower (parameterChart f hf)
      (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    (a : Localization.AtPrime (parameterValuationCenter f hf v hF hvf))
    (ha : a ∈ IsLocalRing.maximalIdeal _) : 0 < v (algebraMap _ E a) := by
  rw [← parameterCenterLocalHom_coe f hf v hF hvf a]
  apply v.toValuation.mem_maximalIdeal_iff.mp
  change a ∈ (IsLocalRing.maximalIdeal v.toValuation.valuationSubring).comap
    (parameterCenterLocalHom f hf v hF hvf)
  rw [parameterCenterLocalHom_comap_maximalIdeal]
  exact ha

theorem primeFieldValuation_algebraMap_localOrder
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) :
    letI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot
      (Localization.AtPrime q.asIdeal)
    primeFieldValuation S E q (algebraMap S E a) =
      CurveLocalOrder.enatToIntegerOrder
        (IsDiscreteValuationRing.addVal (Localization.AtPrime q.asIdeal)
          (algebraMap S (Localization.AtPrime q.asIdeal) a)) := by
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  change CurveLocalOrder.fractionAddValuation A E (algebraMap S E a) = _
  rw [IsScalarTower.algebraMap_apply S A E, CurveLocalOrder.fractionAddValuation_algebraMap]
  rfl

theorem primeFieldValuation_algebraMap_nonneg
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) :
    0 ≤ primeFieldValuation S E q (algebraMap S E a) := by
  rw [primeFieldValuation_algebraMap_localOrder]
  exact CurveLocalOrder.enatToIntegerOrder_monotone (show (0 : ℕ∞) ≤ _ from zero_le)

theorem enatToIntegerOrder_pos_iff (n : ℕ∞) :
    0 < CurveLocalOrder.enatToIntegerOrder n ↔ 0 < n := by
  rcases eq_or_ne n ⊤ with rfl | hn
  · simp
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hn
  rw [← hk]
  simp

theorem primeFieldValuation_positive_iff
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) :
    0 < primeFieldValuation S E q (algebraMap S E a) ↔ a ∈ q.asIdeal := by
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot
    (Localization.AtPrime q.asIdeal)
  rw [primeFieldValuation_algebraMap_localOrder, enatToIntegerOrder_pos_iff,
    pos_iff_ne_zero, ne_eq, IsDiscreteValuationRing.addVal_eq_zero_iff,
    IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q.asIdeal) q.asIdeal]
  simp

structure NormalizedPlace (F E : Type*) [Field F] [Field E] [Algebra F E] where
  valuation : AddValuation E (WithTop ℤ)
  constants_nonneg : ∀ c : F, 0 ≤ valuation (algebraMap F E c)
  normalized : ∃ z : Eˣ, WeightedCurveDegree.integerOrder valuation z = 1

@[ext] theorem NormalizedPlace.ext
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p q : NormalizedPlace F E} (h : p.valuation = q.valuation) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem valuation_eq_parameterPlaceValuation
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 < v f) (hnormalized : ∃ z : Eˣ, WeightedCurveDegree.integerOrder v z = 1) :
    v = parameterPlaceValuation f hf (parameterCenterPlace f hf v hF hvf) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  let q := parameterValuationCenter f hf v hF hvf.le
  have hq : q ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver (zeroPrime_ne_bot F)
      (parameterCenterPlace f hf v hF hvf).property
  let A := Localization.AtPrime q
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq A
  change v = CurveLocalOrder.fractionAddValuation A E
  apply PiExponent.DVRValuationUnique.eq_fractionAddValuation v
  · exact parameterCenterLocal_nonneg f hf v hF hvf.le
  · intro a ha _
    exact parameterCenterLocal_positive f hf v hF hvf.le a ha
  · exact hnormalized

theorem primeFieldValuation_normalized
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) :
    ∃ z : Eˣ, WeightedCurveDegree.integerOrder (primeFieldValuation S E q) z = 1 := by
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  exact PiExponent.DVRValuationUnique.fractionAddValuation_normalized

theorem parameterPlaceValuation_constants_nonneg
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) (c : F) :
    0 ≤ parameterPlaceValuation f hf q (algebraMap F E c) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  have hmap : algebraMap S E (algebraMap F[X] S (Polynomial.C c)) = algebraMap F E c := by
    rw [← IsScalarTower.algebraMap_apply F[X] S E,
      parameterPolynomialAlgebra_map f hf, Polynomial.aeval_C]
  change 0 ≤ primeFieldValuation S E (zeroFiberHeightOne F S q) (algebraMap F E c)
  rw [← hmap]
  exact primeFieldValuation_algebraMap_nonneg S E _ _

theorem parameterPlaceValuation_positive
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) : 0 < parameterPlaceValuation f hf q f := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  have hmap : algebraMap S E (algebraMap F[X] S Polynomial.X) = f := by
    rw [← IsScalarTower.algebraMap_apply F[X] S E,
      parameterPolynomialAlgebra_map f hf, Polynomial.aeval_X]
  change 0 < primeFieldValuation S E (zeroFiberHeightOne F S q) f
  have hx : algebraMap F[X] S Polynomial.X ∈ q.1 := by
    apply (Ideal.mem_of_liesOver q.1 (zeroPrime F) Polynomial.X).mp
    change Polynomial.constantCoeff Polynomial.X = (0 : F)
    simp
  have hp := (primeFieldValuation_positive_iff S E (zeroFiberHeightOne F S q)
    (algebraMap F[X] S Polynomial.X)).mpr hx
  exact lt_of_lt_of_eq hp (congrArg (primeFieldValuation S E (zeroFiberHeightOne F S q)) hmap)

def parameterNormalizedPlace
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) : NormalizedPlace F E where
  valuation := parameterPlaceValuation f hf q
  constants_nonneg := parameterPlaceValuation_constants_nonneg f hf q
  normalized := by
    let := parameterAlgebra f hf
    let := parameterPolynomialAlgebra f hf
    let := parameter_scalarTower f hf
    let := parameter_finite f hf
    let S := parameterChart f hf
    let : Module.IsTorsionFree F[X] S :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr
        (FunctionField.ringOfIntegers.algebraMap_injective F E)
    exact primeFieldValuation_normalized S E (zeroFiberHeightOne F S q)

theorem parameterCenterPlace_parameterNormalizedPlace
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) :
    parameterCenterPlace f hf (parameterNormalizedPlace f hf q).valuation
      (parameterNormalizedPlace f hf q).constants_nonneg
      (parameterPlaceValuation_positive f hf q) = q := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  apply Subtype.ext
  apply Ideal.ext
  intro x
  change x ∈ parameterValuationCenter f hf (parameterNormalizedPlace f hf q).valuation
    (parameterNormalizedPlace f hf q).constants_nonneg _ ↔ x ∈ q.1
  rw [mem_parameterValuationCenter_iff]
  exact primeFieldValuation_positive_iff S E (zeroFiberHeightOne F S q) x

def positivePlaceEquivZeroPlaces
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    {p : NormalizedPlace F E // 0 < p.valuation f} ≃ parameterZeroPlaces f hf where
  toFun p := parameterCenterPlace f hf p.1.valuation p.1.constants_nonneg p.2
  invFun q := ⟨parameterNormalizedPlace f hf q, parameterPlaceValuation_positive f hf q⟩
  left_inv p := by
    apply Subtype.ext
    apply NormalizedPlace.ext
    exact (valuation_eq_parameterPlaceValuation f hf p.1.valuation
      p.1.constants_nonneg p.2 p.1.normalized).symm
  right_inv q := parameterCenterPlace_parameterNormalizedPlace f hf q

theorem finite_positivePlaces
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    Set.Finite {p : NormalizedPlace F E | 0 < p.valuation f} := by
  let := parameterZeroPlacesFintype f hf
  have : Finite {p : NormalizedPlace F E // 0 < p.valuation f} :=
    Finite.of_equiv (parameterZeroPlaces f hf) (positivePlaceEquivZeroPlaces f hf).symm
  exact Set.finite_coe_iff.mp this

end PiExponent.CurveValuationCenter

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveProductFormula
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveProductFormula
open PiExponent.CurveZeroPole PiExponent.CurveValuationCenter
open PiExponent.WeightedCurveDegree

def placeOrder {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) : ℤ := integerOrder p.valuation z

@[simp] theorem placeOrder_inv {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) : placeOrder p z⁻¹ = -placeOrder p z := by
  exact integerOrder_inv p.valuation z

theorem valuation_pos_iff_order_pos {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) : 0 < p.valuation (z : E) ↔ 0 < placeOrder p z := by
  rw [← coe_integerOrder]
  exact WithTop.coe_lt_coe

def positivePlaces {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] : Finset (NormalizedPlace F E) :=
  (finite_positivePlaces f hf).toFinset

@[simp] theorem mem_positivePlaces
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] (p : NormalizedPlace F E) :
    p ∈ positivePlaces f hf ↔ 0 < p.valuation f := by
  classical
  exact (finite_positivePlaces f hf).mem_toFinset

end PiExponent.CurveProductFormula

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_LineBundleGluingSections
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.LineBundleGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}
  {ι : Type}
  {U : ι → X.Opens}

lemma sheafification_unit_counit_map (Z : Scheme.{0})
    (P : PresheafOfModules Z.ringCatSheaf.obj) (M : Z.Modules) (e : P ⟶ M.val) :
    (TensorPure.adj Z).unit.app P ≫
      ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map e).val ≫
      ((TensorPure.adj Z).counit.app M).val = e := by
  let F : PresheafOfModules Z.ringCatSheaf.obj ⥤ Z.Modules :=
    PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)
  let G : Z.Modules ⥤ PresheafOfModules Z.ringCatSheaf.obj :=
    SheafOfModules.forget Z.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)
  let a : F ⊣ G := TensorPure.adj Z
  have h := (a.unit_comp_map_eq_iff (F.map e ≫ a.counit.app M) e).mpr rfl
  have hm := congrArg (fun q => a.unit.app P ≫ q)
    (G.map_comp (F.map e) (a.counit.app M))
  exact hm.symm.trans h

end
end PiExponentSeshadri.LineBundleGluing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PolynomialProjectiveStructure
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable (R σ : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

instance instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions : IsScalarTower R (homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := homogeneousSubmodule σ R 0)
    (A := MvPolynomial σ R) (fun _ => rfl)

instance instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions [Finite σ] : Algebra.FiniteType (homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R
    (homogeneousSubmodule σ R 0) (MvPolynomial σ R)

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_WeightedMonomialMap
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial

variable {R ι σ : Type*} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

def affineMonomialMap (a : σ → ι →₀ ℕ) : MvPolynomial σ R →+* MvPolynomial ι R :=
  eval₂Hom C (fun s => monomial (a s) 1)

end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveDenseChart
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

section

open AlgebraicGeometry TopologicalSpace
open scoped HomogeneousIdeal

variable {A T : Type*} [CommRing A] [IsDomain A] [SetLike T A] [AddSubgroupClass T A]
  (𝒜 : ℕ → T) [GradedRing 𝒜]

def projectiveGenericPoint {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) (hne : s ≠ 0) :
    ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := by
    simpa only [HomogeneousIdeal.toIdeal_bot] using (inferInstance : (⊥ : Ideal A).IsPrime)
  not_irrelevant_le h := by
    have hm := h (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd hs)
    change s ∈ (⊥ : Ideal A) at hm
    exact hne (Ideal.mem_bot.mp hm)

end

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveEmbeddingCharts
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

universe u

namespace Projective

section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open scoped AlgebraicGeometry
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveConstants : K →+* homogeneousSubmodule σ K 0 where
  toFun r := ⟨C r, isHomogeneous_C _ _⟩
  map_one' := Subtype.ext C_1
  map_mul' _ _ := Subtype.ext C_mul
  map_zero' := Subtype.ext C_0
  map_add' _ _ := Subtype.ext C_add

def projectiveBase : Proj (homogeneousSubmodule σ K) ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (projectiveConstants (σ := σ)))

end

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

end Projective

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveO1ChartMap
attribute [-instance] _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open HomogeneousLocalization PiExponentSeshadri.Projective

variable {R σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem scalarPullback_factorization {A : Type} [CommRing A]
    {X Y : Scheme} (π : X ⟶ Spec (CommRingCat.of R)) (ι : Y ⟶ X)
    (g : Y ⟶ Spec (CommRingCat.of A)) (f : R →+* A)
    (h : ι ≫ π = g ≫ Spec.map (CommRingCat.ofHom f)) :
    ι.appTop.hom.comp (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ π.appTop).hom) =
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appTop).hom).comp f := by
  have hh := congrArg (fun t : Y ⟶ Spec (CommRingCat.of R) =>
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ t.appTop) h
  simp only [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc] at hh
  exact congrArg CommRingCat.Hom.hom hh

end PiExponent.ProjectiveO1

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectivePullbackFrames
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme.{0}}

def pullbackRestrictFactorNatIso (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (g : V.toScheme ⟶ U.toScheme) (h : V.ι ≫ f = g ≫ U.ι) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback g :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
    (Scheme.Modules.restrictFunctorIsoPullback V.ι) ≪≫
  Scheme.Modules.pullbackComp V.ι f ≪≫
  Scheme.Modules.pullbackCongr h ≪≫
  (Scheme.Modules.pullbackComp g U.ι).symm ≪≫
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
    (Scheme.Modules.pullback g)

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AlgebraicJetPackets
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AlgebraicJetPackets

open MvPolynomial
variable {R : Type*} [CommRing R] {m : ℕ}

def triangularMap (c : Fin m → R) (G : Fin m → Polynomial R) :
    MvPolynomial (Fin (m+1)) R →ₐ[R] MvPolynomial (Fin (m+1)) R :=
  MvPolynomial.aeval (Fin.cases (1 + X 0)
    (fun i => C (c i) + X i.succ + Polynomial.aeval (X 0) (G i)))

@[simp] theorem triangularMap_X_zero (c : Fin m → R) (G : Fin m → Polynomial R) :
    triangularMap c G (X 0) = 1 + X 0 := by simp [triangularMap]

@[simp] theorem triangularMap_X_succ (c : Fin m → R) (G : Fin m → Polynomial R)
    (i : Fin m) :
    triangularMap c G (X i.succ) = C (c i) + X i.succ + Polynomial.aeval (X 0) (G i) := by
  simp [triangularMap]

end PiExponent.AlgebraicJetPackets

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactJetIdeal
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace PiExponent.CompactJetIdeal

universe u
variable {U X S : Scheme.{u}}

theorem section_isClosedImmersion (π : X ⟶ S) [IsSeparated π]
    (p : S ⟶ X) (hp : p ≫ π = 𝟙 S) : IsClosedImmersion p := by
  have : IsClosedImmersion (p ≫ π) := by rw [hp]; infer_instance
  exact IsClosedImmersion.of_comp p π

theorem image_support_isClosed {J : Type*} [Finite J]
    (I : U.IdealSheafData) (j : U ⟶ X)
    (π : X ⟶ S) [IsSeparated π]
    (p : J → (S ⟶ U)) (hp : ∀ a, (p a ≫ j) ≫ π = 𝟙 S)
    (hsupport : (I.support : Set U) = ⋃ a, Set.range (p a)) :
    IsClosed (j '' (I.support : Set U)) := by
  have heq : j '' (I.support : Set U) = ⋃ a, Set.range (p a ≫ j) := by
    rw [hsupport, Set.image_iUnion]
    congr 1
    funext a
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro a
  have := section_isClosedImmersion π (p a ≫ j) (hp a)
  exact (p a ≫ j).isClosedEmbedding.isClosed_range

end PiExponent.CompactJetIdeal
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_WeightedBezout
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedBezout

open scoped BigOperators

variable {k σ τ : Type*} [Field k]

noncomputable def translatedPowerSubstitution (w : σ → ℕ) (a : σ → k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (a i) + MvPolynomial.X i ^ w i)

@[simp] theorem translatedPowerSubstitution_X (w : σ → ℕ) (a : σ → k) (i : σ) :
    translatedPowerSubstitution w a (MvPolynomial.X i) =
      MvPolynomial.C (a i) + MvPolynomial.X i ^ w i := by
  simp [translatedPowerSubstitution]

@[simp] theorem translatedPowerSubstitution_C (w : σ → ℕ) (a : σ → k) (c : k) :
    translatedPowerSubstitution w a (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [translatedPowerSubstitution]

noncomputable def pointIdeal (a : σ → k) : Ideal (MvPolynomial σ k) :=
  RingHom.ker (MvPolynomial.aeval a).toRingHom

instance pointIdeal_isMaximal (a : σ → k) : (pointIdeal a).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨MvPolynomial.C c, by simp⟩

@[simp] theorem mem_pointIdeal (a : σ → k) (p : MvPolynomial σ k) :
    p ∈ pointIdeal a ↔ MvPolynomial.aeval a p = 0 := Iff.rfl

theorem pointIdeal_eq_span (a : σ → k) :
    pointIdeal a = Ideal.span (Set.range (fun i =>
      MvPolynomial.X i - MvPolynomial.C (a i))) := by
  let J : Ideal (MvPolynomial σ k) := Ideal.span (Set.range (fun i =>
    MvPolynomial.X i - MvPolynomial.C (a i)))
  have hJ : J ≤ pointIdeal a := by
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    simp
  apply le_antisymm _ hJ
  have heval : Ideal.Quotient.mk J =
      ((Ideal.Quotient.mk J).comp MvPolynomial.C).comp (MvPolynomial.aeval a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      apply sub_eq_zero.mp
      rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨i, rfl⟩
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [heval]
  simp only [RingHom.comp_apply]
  change (Ideal.Quotient.mk J) (MvPolynomial.C (MvPolynomial.aeval a p)) = 0
  rw [(mem_pointIdeal a p).mp hp, map_zero, map_zero]

theorem translatedPowerSubstitution_eval_origin (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    (MvPolynomial.aeval (0 : σ → k)).comp (translatedPowerSubstitution w a) =
      MvPolynomial.aeval a := by
  ext i
  simp [translatedPowerSubstitution, zero_pow (hw i).ne']

theorem translatedPowerSubstitution_comap_origin (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    (pointIdeal (0 : σ → k)).comap (translatedPowerSubstitution w a).toRingHom =
      pointIdeal a := by
  ext p
  change MvPolynomial.aeval (0 : σ → k) (translatedPowerSubstitution w a p) = 0 ↔ _
  have h := congrArg (fun f : MvPolynomial σ k →ₐ[k] k => f p)
    (translatedPowerSubstitution_eval_origin w a hw)
  change MvPolynomial.aeval (0 : σ → k) (translatedPowerSubstitution w a p) =
    MvPolynomial.aeval a p at h
  rw [h]
  rfl

end PiExponent.WeightedBezout

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactJetPolynomial
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.CompactJetPolynomial

open MvPolynomial AlgebraicJetPackets
open scoped BigOperators

variable {k : Type*} [Field k] {m : ℕ}

def center (c : Fin m → k) : Fin (m+1) → k := Fin.cases 1 c

def centerPoint (c : Fin m → k) : PrimeSpectrum (MvPolynomial (Fin (m+1)) k) :=
  ⟨WeightedBezout.pointIdeal (center c), inferInstance⟩

end PiExponent.CompactJetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactLogJetIdeal
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace PiExponent.CompactLogJetIdeal
open CompactJetPolynomial

variable {m : ℕ}

abbrev base : Scheme := Spec (CommRingCat.of ℂ)

end PiExponent.CompactLogJetIdeal
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RamifiedPointMap
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.RamifiedLocalLength

open IsLocalRing WeightedBezout

variable {k σ : Type*} [Field k]

noncomputable def translatedPowerLocalMap (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    Localization.AtPrime (pointIdeal a) →ₐ[k]
      Localization.AtPrime (pointIdeal (0 : σ → k)) :=
  Localization.localAlgHom (pointIdeal a) (pointIdeal (0 : σ → k))
    (translatedPowerSubstitution w a)
    (translatedPowerSubstitution_comap_origin w a hw).symm

@[simp] theorem translatedPowerLocalMap_algebraMap (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) (p : MvPolynomial σ k) :
    translatedPowerLocalMap w a hw
      (algebraMap _ (Localization.AtPrime (pointIdeal a)) p) =
      algebraMap _ (Localization.AtPrime (pointIdeal (0 : σ → k)))
        (translatedPowerSubstitution w a p) :=
  Localization.localRingHom_to_map _ _ _
    (translatedPowerSubstitution_comap_origin w a hw).symm p

@[instance_reducible] noncomputable def translatedPowerLocalAlgebra (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    Algebra (Localization.AtPrime (pointIdeal a))
      (Localization.AtPrime (pointIdeal (0 : σ → k))) :=
  (translatedPowerLocalMap w a hw).toRingHom.toAlgebra

end PiExponent.RamifiedLocalLength

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_SeparablePointLength
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.SeparablePointLength

open IsLocalRing TensorProduct

variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable def contractedPoint (b : ι → E) : Ideal (MvPolynomial ι K) :=
  (WeightedBezout.pointIdeal b).comap (algebraMap (MvPolynomial ι K) (MvPolynomial ι E))

instance contractedPoint_isPrime (b : ι → E) : (contractedPoint (K := K) b).IsPrime := by
  unfold contractedPoint
  infer_instance

instance point_liesOver (b : ι → E) :
    (WeightedBezout.pointIdeal b).LiesOver (contractedPoint (K := K) b) := ⟨rfl⟩

noncomputable def pointLocalMap (b : ι → E) :
    Localization.AtPrime (contractedPoint (K := K) b) →+*
      Localization.AtPrime (WeightedBezout.pointIdeal b) :=
  Localization.localRingHom (contractedPoint (K := K) b) (WeightedBezout.pointIdeal b)
    (algebraMap (MvPolynomial ι K) (MvPolynomial ι E)) rfl

@[instance_reducible] noncomputable def pointLocalAlgebra (b : ι → E) :
    Algebra (Localization.AtPrime (contractedPoint (K := K) b))
      (Localization.AtPrime (WeightedBezout.pointIdeal b)) :=
  Localization.AtPrime.algebraOfLiesOver (contractedPoint (K := K) b) (WeightedBezout.pointIdeal b)

@[simp] theorem pointLocalMap_algebraMap (b : ι → E) (p : MvPolynomial ι K) :
    pointLocalMap (K := K) b (algebraMap _ (Localization.AtPrime (contractedPoint (K := K) b)) p) =
      algebraMap _ (Localization.AtPrime (WeightedBezout.pointIdeal b))
        (MvPolynomial.map (algebraMap K E) p) :=
  Localization.localRingHom_to_map _ _ _ rfl p

end PiExponent.SeparablePointLength

end OAI
end


