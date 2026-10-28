-- Prove2me | Definitions.Def_OAIQ068A035
-- name    : OAIQ068A035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:09:27.093388+00:00
-- url     : https://prove2.me/theorems/adabe862-5248-4311-b9ca-d0822b33e2c0
-- title:
--   Definitions bundle OAIQ068A035 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 1 definition, 4 instances and 30 theorems. The definitions and types are `OAI.PiExponentSeshadri.Geometry.IsBlowup.complementLift`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AdmissibleBlowupGeometry`, `PiExponent_Ampleness_AmpleCommonDegree`, `PiExponent_Ampleness_BlowupAffineSections`, `PiExponent_Ampleness_BlowupAmpleTwist`, `PiExponent_Ampleness_BlowupComplement`, `PiExponent_Ampleness_BlowupProperIntegral`, `PiExponent_Ampleness_ReesRelativeSections`, `PiExponent_Ampleness_RelativeAffineSectionAmple`, `PiExponent_Approximation_MixedFrameExtension`, `PiExponent_Approximation_MixedSectionExtension`, `PiExponent_Approximation_MixedSectionOpenExtension`, `PiExponent_Approximation_TensorMixedSection`, `PiExponent_Geometry_PlaceParameterModel`.
--
--   **Imports.** It imports the bundles `OAIQ068A028` and `OAIQ068A029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A040` and `OAIQ068A041`; the proofs of `OAI_PiExponent_NumericalAmpleness_exists_regular_twist_pair`, `OAI.PiExponent.NumericalAmpleness.exists_regular_twist_pair_q68`, `OAI_PiExponent_NumericalAmpleness_lineBundle_cohomology_zero_of_dimension_le` and `OAI.PiExponent.NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A028
import Definitions.Def_OAIQ068A029

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupComplement
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X Y B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.isIso_over_complement (hπ : IsBlowup I π) :
    IsIso (pullback.fst (Scheme.Opens.ι (X := X) I.support.compl) π) := by
  apply (hπ.open_baseChange (Scheme.Opens.ι (X := X) I.support.compl)).isIso_of_invertible
  have he : I.comap (Scheme.Opens.ι (X := X) I.support.compl) = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    ext x
    change (x.val ∈ I.support ↔ False)
    exact iff_false_intro x.property
  rw [he]
  exact invertible_top _

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupProperIntegral
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace PiExponentSeshadri.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

def IsBlowup.complementLift (hπ : IsBlowup I π) : (centreComplement I).toScheme ⟶ B := by
  let := hπ.isIso_over_complement
  exact inv (pullback.fst (centreComplement I).ι π) ≫
    pullback.snd (centreComplement I).ι π

@[reassoc (attr := simp)]
lemma IsBlowup.complementLift_comp (hπ : IsBlowup I π) :
    hπ.complementLift ≫ π = (centreComplement I).ι := by
  let := hπ.isIso_over_complement
  dsimp only [IsBlowup.complementLift]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

lemma IsBlowup.complementLift_range (hπ : IsBlowup I π) :
    Set.range hπ.complementLift = π ⁻¹' (centreComplement I : Set X) := by
  let := hπ.isIso_over_complement
  change Set.range ((pullback.snd (centreComplement I).ι π) ∘
    (inv (pullback.fst (centreComplement I).ι π))) = _
  rw [Set.range_comp]
  rw [(inv (pullback.fst (centreComplement I).ι π)).surjective.range_eq,
    Set.image_univ, Scheme.Pullback.range_snd]
  simp

lemma IsBlowup.nonempty_of_support_ne_top (hπ : IsBlowup I π) (hI : I.support ≠ ⊤) :
    Nonempty B :=
  (complement_nonempty hI).map hπ.complementLift

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme.{0}} [IrreducibleSpace X] (I : X.IdealSheafData)

lemma support_comap_ne_top_of_open (hI : I.support ≠ ⊤) (j : Y ⟶ X)
    [IsOpenImmersion j] [Nonempty Y] : (I.comap j).support ≠ ⊤ := by
  have hc : (centreComplement I : Set X).Nonempty := by
    obtain ⟨x⟩ := complement_nonempty hI
    exact ⟨x.val, x.property⟩
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    j.isOpenEmbedding.isOpen_range (centreComplement I).isOpen (Set.range_nonempty j) hc
  intro he
  have hyn : y ∈ (I.comap j).support := by rw [he]; trivial
  rw [Scheme.IdealSheafData.support_comap] at hyn
  exact hy hyn

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.BlowupGluing
open AlgebraicGeometry CategoryTheory TopologicalSpace PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [IsIntegral X] (I : X.IdealSheafData)

lemma localScheme_isIntegral (hI : I.support ≠ ⊤) (U : X.AffineZariskiSite)
    [Nonempty U.toOpens.toScheme] : IsIntegral (localScheme I U) := by
  let : IsIntegral U.toOpens.toScheme := isIntegral_of_isOpenImmersion U.toOpens.ι
  let : Nonempty (localScheme I U) := (local_isBlowup I U).nonempty_of_support_ne_top
    (support_comap_ne_top_of_open I hI U.toOpens.ι)
  infer_instance

lemma complement_dense (hI : I.support ≠ ⊤) :
    Dense (projection I ⁻¹' (centreComplement I : Set X)) := by
  rw [dense_iff_inter_open]
  intro V hV ⟨y, hyV⟩
  obtain ⟨U, z, rfl⟩ := (cover I).exists_eq y
  let : Nonempty U.toOpens.toScheme := ⟨localProjection I U z⟩
  let : IsIntegral ((cover I).X U) := localScheme_isIntegral I hI U
  have hc : (centreComplement I : Set X).Nonempty := by
    obtain ⟨x⟩ := complement_nonempty hI
    exact ⟨x.val, x.property⟩
  have hU : (U.toOpens : Set X).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U.toOpens.toScheme›
    exact ⟨x.val, x.property⟩
  obtain ⟨x, hxU, hxc⟩ := nonempty_preirreducible_inter
    U.toOpens.isOpen (centreComplement I).isOpen hU hc
  let b : scheme I := (isBlowup I).complementLift ⟨x, hxc⟩
  have hpb : projection I b = x :=
    congrArg (fun f : (centreComplement I).toScheme ⟶ X => f ⟨x, hxc⟩)
      (isBlowup I).complementLift_comp
  have hbr : b ∈ Set.range ((cover I).f U) := by
    erw [cover_range I U]
    change projection I b ∈ U.toOpens
    rwa [hpb]
  obtain ⟨w, hw⟩ := hbr
  have hwc : (cover I).f U w ∈ projection I ⁻¹' (centreComplement I : Set X) := by
    change projection I ((cover I).f U w) ∈ centreComplement I
    rwa [hw, hpb]
  obtain ⟨q, hqV, hqc⟩ := nonempty_preirreducible_inter
    (hV.preimage ((cover I).f U).continuous)
    (((centreComplement I).isOpen.preimage (projection I).continuous).preimage
      ((cover I).f U).continuous) ⟨z, hyV⟩ ⟨w, hwc⟩
  exact ⟨(cover I).f U q, hqV, hqc⟩

lemma scheme_isIntegral (hI : I.support ≠ ⊤) : IsIntegral (scheme I) := by
  let : Nonempty (centreComplement I).toScheme := complement_nonempty hI
  let : IsIntegral (centreComplement I).toScheme :=
    isIntegral_of_isOpenImmersion (centreComplement I).ι
  have hi : IsIrreducible (Set.range (isBlowup I).complementLift) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := (centreComplement I).toScheme)).image
        (isBlowup I).complementLift (isBlowup I).complementLift.continuous.continuousOn
  have hd : Dense (Set.range (isBlowup I).complementLift) := by
    rw [Geometry.IsBlowup.complementLift_range]
    exact complement_dense I hI
  let : IrreducibleSpace (scheme I) := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set (scheme I))
    rw [← hd.closure_eq]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end PiExponentSeshadri.BlowupGluing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleCommonDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

theorem LineBundle.common_degree (L : LineBundle X) {ι : Type} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (s : ∀ i, GlobalSections X (modulePow X L.sheaf (d i))) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : ι → GlobalSections X (modulePow X L.sheaf n),
      ∀ i, sectionOpen X (t i) = sectionOpen X (s i) := by
  classical
  let n := ∏ i, d i
  have hn : 0 < n := Finset.prod_pos (fun i _ => hd i)
  have hdiv (i : ι) : d i ∣ n := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have heq (i : ι) : d i * (n / d i) = n := Nat.mul_div_cancel' (hdiv i)
  let e (i : ι) : modulePow X (modulePow X L.sheaf (d i)) (n / d i) ≅
      modulePow X L.sheaf n :=
    linePowerMul L (d i) (n / d i) ≪≫ eqToIso (congrArg (modulePow X L.sheaf) (heq i))
  refine ⟨n, hn, fun i => powerSection (s i) (n / d i) ≫ (e i).hom, ?_⟩
  intro i
  change SectionOpens.isoOpen (powerSection (s i) (n / d i) ≫ (e i).hom) = _
  rw [SectionOpens.isoOpen_postcomp]
  exact (L.pow (d i)).sectionOpen_power (s i)
    (Nat.div_pos (Nat.le_of_dvd hn (hdiv i)) (hd i))

theorem LineBundle.ample_common_degree_cover [CompactSpace X] (L : LineBundle X)
    (hL : L.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ l : ℕ,
      ∃ s : Fin l → GlobalSections X (modulePow X L.sheaf n),
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) := by
  classical
  have hex (x : X) := hL x ⊤ (by trivial)
  choose d hd s hs hst ha using hex
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (s x) : Set X)) (fun x => (sectionOpen X (s x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hs x⟩)
  obtain ⟨n, hn, t, ht⟩ := L.common_degree (fun i : I => d i.val)
    (fun i => hd i.val) (fun i => s i.val)
  let e := (Fintype.equivFin I).symm
  refine ⟨n, hn, Fintype.card I, fun i => t (e i), ?_, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨e.symm ⟨i, hi⟩, ?_⟩
    change x ∈ sectionOpen X (t (e (e.symm ⟨i, hi⟩)))
    rw [Equiv.apply_symm_apply, ht]
    exact hx
  · intro i
    rw [ht]
    exact ha (e i).val
  · intro i
    rw [ht]
    exact ⟨(e i).val, hs (e i).val⟩

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceParameterModel
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.PlaceParameterModel
open CurveZeroPole CurveValuationCenter WeightedCurveDegree

theorem parameter_nonzero {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : parameter p ≠ 0 := (parameterUnit p).ne_zero

theorem parameter_value {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : p.valuation (parameter p) = 1 := by
  have h := coe_integerOrder p.valuation (parameterUnit p)
  rw [parameterUnit_order] at h
  exact h.symm

end PiExponent.PlaceParameterModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupGeometry
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open WeightedGeometryScale
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

instance compactification_isNoetherian : IsNoetherian (compactification d) := {}

instance projection_proper : IsProper (projection d) := by infer_instance
instance structureMap_proper : IsProper (structureMap d) := by
  dsimp [structureMap]
  infer_instance
instance blowup_compact : CompactSpace (blowup d) :=
  QuasiCompact.compactSpace_of_compactSpace (structureMap d)

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesRelativeSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ReesGrading
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SpecMaps

variable {R : Type} [CommRing R] (I : Ideal R)
variable {B : Scheme.{0}} (f : B ⟶ Spec (.of R))
  (J : LineBundle B) (ι : J.sheaf ⟶ O B)
  (hJ : PresentsPullbackIdeal (IdealPullback.specIdeal I) f J ι)
include hJ

theorem relative_generator_section (a : I) :
    ∃ s : O B ⟶ J.sheaf,
      s ≫ ι = scalarEnd ((coordinate f) a.val) := by
  let : Mono ι := hJ.1
  obtain ⟨s,hs,-⟩ := global_division_of_local_lifts ι
      (scalarEnd ((coordinate f) a.val)) (by
    intro x
    obtain ⟨U,hx,⟨e⟩,-⟩ := common_affine_frames J J x
    let r := endValue (e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι)
    have hI : I.map (coordinate (U.1.ι ≫ f)).hom = Ideal.span {r} := by
      rw [← IdealPullback.specIdeal_coordinate,Scheme.IdealSheafData.comap_comp]
      exact InvertibleLocal.frame_ideal J ι hJ U.1.ι e
    have hmem : coefficient (Scheme.Modules.restrictUnitIso U.1.ι)
        (restrictSection U.1.ι (scalarEnd ((coordinate f) a.val))) ∈ Ideal.span {r} := by
      rw [← hI]
      have he : coefficient (Scheme.Modules.restrictUnitIso U.1.ι)
          (restrictSection U.1.ι (scalarEnd ((coordinate f) a.val))) =
          coordinate (U.1.ι ≫ f) a.val := by
        erw [coefficient, endValue_restrict, endValue_scalarEnd]
        rw [coordinate_comp]
        rfl
      rw [he]
      exact Ideal.mem_map_of_mem _ a.property
    obtain ⟨t,ht⟩ := framed_local_division e (Scheme.Modules.restrictUnitIso U.1.ι)
      ((Scheme.Modules.restrictFunctor U.1.ι).map ι)
      (restrictSection U.1.ι (scalarEnd ((coordinate f) a.val))) hmem
    exact ⟨U.1,hx,t,ht⟩)
  exact ⟨s,hs⟩

theorem relative_generator_section_open (β : B ⟶ affineBlowup I) (hβ : β ≫ projection I = f) (a : I)
    (s : O B ⟶ J.sheaf)
    (hs : s ≫ ι = scalarEnd ((coordinate f) a.val)) :
    SectionOpens.isoOpen s = β ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) := by
  let : Mono ι := hJ.1
  ext x
  obtain ⟨U,hx,⟨e⟩,-⟩ := common_affine_frames J J x
  let g := e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι
  have hg : Mono g := mono_inv_comp e (InvertibleLocal.restrictedInclusion J ι U.1.ι)
    (@InvertibleLocal.restrictedInclusion_mono _ _ J ι U.1.ι inferInstance hJ.1)
  let r := endValue g
  have hr : IsRegular r := @UnitEndomorphism.equation_regular U.1.toScheme g hg ⊤
  have hI : I.map (coordinate (U.1.ι ≫ f)).hom = Ideal.span {r} := by
    rw [← IdealPullback.specIdeal_coordinate,Scheme.IdealSheafData.comap_comp]
    exact InvertibleLocal.frame_ideal J ι hJ U.1.ι e
  let h := principalScheme I U.1.toScheme (coordinate (U.1.ι ≫ f)).hom r hI hr
  have hh : h = U.1.ι ≫ β := by
    apply invertible_unique I h (U.1.ι ≫ β) (U.1.ι ≫ f)
    · exact (principalScheme_projection I U.1.toScheme _ r hI hr).trans (factor _)
    · rw [Category.assoc,hβ]
    · exact InvertibleLocal.invertible_restrict _ _ ⟨J,ι,hJ⟩ U.1.ι
  have hscalar : coefficient e (restrictSection U.1.ι s) * r =
      coordinate (U.1.ι ≫ f) a.val := by
    have hcomp : (restrictSection U.1.ι s ≫ e.hom) ≫ g =
        restrictSection U.1.ι (scalarEnd ((coordinate f) a.val)) ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom := by
      dsimp [g,InvertibleLocal.restrictedInclusion]
      simp only [Category.assoc,Iso.hom_inv_id_assoc]
      rw [← hs]
      simp only [restrictSection]
      exact map_comp_through (Scheme.Modules.restrictFunctor U.1.ι)
        (Scheme.Modules.restrictUnitIso U.1.ι).inv s ι
        (Scheme.Modules.restrictUnitIso U.1.ι).hom
    have H := congrArg (endValue (X := U.1.toScheme)) hcomp
    rw [coordinate_comp]
    exact ((endValue_comp (restrictSection U.1.ι s ≫ e.hom) g).symm.trans H).trans
      ((endValue_restrict U.1.ι (scalarEnd ((coordinate f) a.val))).trans
        (congrArg U.1.ι.appTop (endValue_scalarEnd ((coordinate f) a.val))))
  have hc : coefficient e (restrictSection U.1.ι s) =
      BlowupLift.coefficient I (coordinate (U.1.ι ≫ f)).hom r hI a := by
    apply hr.left
    exact (mul_comm _ _).trans (hscalar.trans
      (BlowupLift.mul_coefficient I _ r hI a).symm)
  have hloc : U.1.ι ⁻¹ᵁ SectionOpens.isoOpen s =
      U.1.ι ⁻¹ᵁ β ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) := by
    rw [preimage_isoOpen s U.1.ι e,hc]
    have H := principalScheme_preimage I U.1.toScheme _ r hI hr a
    change h ⁻¹ᵁ _ = _ at H
    rw [hh] at H
    exact H.symm
  exact SetLike.ext_iff.mp hloc ⟨x,hx⟩

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SpecMaps
variable {R : Type} [CommRing R] (I : Ideal R)
variable {B : Scheme.{0}} (f : B ⟶ Spec (.of R))
  (J : LineBundle B) (ι : J.sheaf ⟶ O B)
  (hJ : PresentsPullbackIdeal (IdealPullback.specIdeal I) f J ι)
include hJ

theorem relative_affine_section_cover (hf : IsBlowup (IdealPullback.specIdeal I) f) :
    ∃ s : I → (O B ⟶ J.sheaf),
      (⨆ a, SectionOpens.isoOpen (s a)) = ⊤ ∧
      ∀ a, IsAffineOpen (SectionOpens.isoOpen (s a)) := by
  classical
  let e : B ≅ affineBlowup I := hf.iso (rees_isBlowup I)
  let : IsIso e.hom := ⟨⟨e.inv,e.hom_inv_id,e.inv_hom_id⟩⟩
  choose s hs using relative_generator_section I f J ι hJ
  have ho a := relative_generator_section_open I f J ι hJ e.hom
    (hf.iso_hom_comp (rees_isBlowup I)) a (s a) (hs a)
  refine ⟨s,?_,fun a => ?_⟩
  · simp only [ho]
    exact e.hom.iSup_preimage_eq_top (iSup_generator_basicOpen I)
  · rw [ho]
    exact @IsAffineOpen.preimage_of_isIso B (affineBlowup I) _
      (Proj.isAffineOpen_basicOpen (piece I) (generator I a) (generator_mem I a)
        (by decide : 0 < (1:ℕ))) e.hom e.isIso_hom
end PiExponentSeshadri.ReesGrading

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupAffineSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.affine_section_cover [IsAffine X] (hπ : IsBlowup I π)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ (α : Type) (s : α → (O B ⟶ J.sheaf)),
      (⨆ a, SectionOpens.isoOpen (s a)) = ⊤ ∧
      ∀ a, IsAffineOpen (SectionOpens.isoOpen (s a)) := by
  let A := I.ideal ⟨⊤,isAffineOpen_top X⟩
  have hp := hπ.postIso X.isoSpec (IdealPullback.specIdeal A)
    (IdealPullback.specIdeal_comap_toSpec I)
  obtain ⟨s,hs,ha⟩ := ReesGrading.relative_affine_section_cover A
    (π ≫ X.isoSpec.hom) J ι (presents_post_toSpec J ι hJ) hp
  exact ⟨A,s,hs,ha⟩

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_MixedSectionExtension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}}

theorem local_affine_mixed_extension (L M : LineBundle X) (U : X.Opens) [IsAffine U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (s : O X ⟶ L.sheaf)
    (w : Γ(M.sheaf, U.ι ''ᵁ (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))))) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O U.toScheme ⟶ (((L.pow n).tensor M).sheaf.restrict U.ι),
      let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
      (((L.pow n).tensor M).sheaf).presheaf.map (homOfLE (U.ι_image_le V)).op
        (openSectionEquiv _ U t) =
      pure (L.pow n).sheaf M.sheaf (U.ι ''ᵁ V) ((powerSection s n).app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V))) w := by
  let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
  let b : Γ(U.toScheme,V) := d.hom.app V w
  let f : Γ(V.toScheme,⊤) := V.topIso.inv b
  obtain ⟨N,hN⟩ := local_affine_power_extension U e s f
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht⟩ := hN n hn
  let q : O U.toScheme ⟶ (((L.pow n).tensor M).sheaf.restrict U.ι) :=
    TensorPure.tensorSection t d.inv ≫ (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv
  refine ⟨q,?_⟩
  change (((L.pow n).tensor M).sheaf).presheaf.map (homOfLE (U.ι_image_le V)).op
    (openSectionEquiv _ U q) = _
  erw [openSectionEquiv_restrict_value ((L.pow n).tensor M).sheaf U q V]
  have he := congrArg (openSectionEquiv ((L.pow n).sheaf.restrict U.ι) V) ht
  erw [openSectionEquiv_restrict t V,
    openSectionEquiv_scalar ((L.pow n).sheaf.restrict U.ι) V f
      (restrictSection V.ι (restrictSection U.ι (powerSection s n))),
    openSectionEquiv_restrict (restrictSection U.ι (powerSection s n)) V] at he
  have hf : V.topIso.hom f = b := Iso.inv_hom_id_apply _ _
  rw [hf] at he
  have hp : (restrictSection U.ι (powerSection s n)).app V (1 : Γ(U.toScheme,V)) =
      (powerSection s n).app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V)) := by
    change (powerSection s n).app (U.ι ''ᵁ V) ((U.ι.appIso V).inv (1 : Γ(U.toScheme,V))) = _
    rw [map_one]
  have he := he.trans (congrArg (fun z : Γ((L.pow n).sheaf.restrict U.ι, V) => (b : Γ(U.toScheme,V)) • z) hp)
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf U.toScheme).mapIso
      (moduleTensorRestrict U (L.pow n).sheaf M.sheaf)).app (op V)).hom).injective
  change (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).hom.app V
      ((moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv.app V
        ((TensorPure.tensorSection t d.inv).app V (1 : Γ(U.toScheme,V)))) = _
  have hc : (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).hom.app V
      ((moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv.app V
        ((TensorPure.tensorSection t d.inv).app V (1 : Γ(U.toScheme,V)))) = (TensorPure.tensorSection t d.inv).app V (1 : Γ(U.toScheme,V)) := by
    change ((moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv ≫
      (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).hom).app V _ = _
    rw [Iso.inv_hom_id]
    rfl
  erw [hc,TensorPure.section_apply t d.inv V]
  refine (congrArg (fun z => pure ((L.pow n).sheaf.restrict U.ι) (M.sheaf.restrict U.ι) V
    z (d.inv.app V (1 : Γ(U.toScheme,V)))) he).trans ?_
  erw [pure_smul_left,← pure_smul_right]
  have hd : b • d.inv.app V (1 : Γ(U.toScheme,V)) = w := by
    erw [← d.inv.app_smul b (1 : Γ(U.toScheme,V)),smul_eq_mul,mul_one]
    change d.inv.app V (d.hom.app V w) = w
    change (d.hom ≫ d.inv).app V w = w
    rw [Iso.hom_inv_id]
    rfl
  erw [hd]
  exact (restrict_pure U (L.pow n).sheaf M.sheaf V _ w).symm

theorem LineBundle.finite_cover_mixed_extension [IsIntegral X] (L M : LineBundle X)
    {ι : Type*} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ i, IsAffine (U i).toScheme) (hU : ∀ i, (U i : Set X).Nonempty)
    (e : ∀ i, L.sheaf.restrict (U i).ι ≅ O (U i).toScheme)
    (d : ∀ i, M.sheaf.restrict (U i).ι ≅ O (U i).toScheme)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf, sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow n).tensor M).sheaf,
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow n).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s n).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  classical
  let D := sectionOpen X s
  let V (i : ι) := (U i).toScheme.basicOpen (coefficient (e i) (restrictSection (U i).ι s))
  let W (i : ι) := (U i).ι ''ᵁ V i
  have hV (i : ι) : V i = (U i).ι ⁻¹ᵁ D := (preimage_isoOpen s (U i).ι (e i)).symm
  have hW_eq (i : ι) : W i = U i ⊓ D := by
    simp only [W,hV,Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι]
  have hWU (i : ι) : W i ≤ U i := (U i).ι_image_le (V i)
  have hWD (i : ι) : W i ≤ D := (hW_eq i).le.trans inf_le_right
  have hW (i : ι) : (W i : Set X).Nonempty := by
    rw [hW_eq]
    exact nonempty_preirreducible_inter (U i).isOpen D.isOpen (hU i) hD
  let wi (i : ι) : Γ(M.sheaf,W i) := M.sheaf.presheaf.map (homOfLE (hWD i)).op w
  have hh (i : ι) := @local_affine_mixed_extension X L M (U i) (haff i) (e i) (d i) s (wi i)
  choose N hN using hh
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  have hn' (i : ι) : N i ≤ n := (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn
  choose t ht using fun i => hN i n (hn' i)
  let P := ((L.pow n).tensor M)
  let target : Γ(P.sheaf,D) := pure (L.pow n).sheaf M.sheaf D
    ((powerSection s n).app D (1 : Γ(X,D))) w
  have heq (i : ι) : P.sheaf.presheaf.map (homOfLE (hWU i)).op
      (openSectionEquiv P.sheaf (U i) (t i)) =
      P.sheaf.presheaf.map (homOfLE (hWD i)).op target := by
    refine (ht i).trans ?_
    have hr := pure_restrict (L.pow n).sheaf M.sheaf (homOfLE (hWD i))
      ((powerSection s n).app D (1 : Γ(X,D))) w
    have hp := section_value_natural (powerSection s n) (homOfLE (hWD i))
    exact (congrArg (fun z => pure (L.pow n).sheaf M.sheaf (W i) z (wi i)) hp).symm.trans hr.symm
  obtain ⟨g,hg,-⟩ := P.glue_dense_subopens D U W hcover hWU hWD hW
    (fun i => openSectionEquiv P.sheaf (U i) (t i)) target heq
  refine ⟨(moduleSectionEquiv P.sheaf).symm g,?_⟩
  have H := section_value_natural ((moduleSectionEquiv P.sheaf).symm g)
    (homOfLE (show D ≤ ⊤ from le_top))
  have Htop : ((moduleSectionEquiv P.sheaf).symm g).app ⊤ (1 : Γ(X,⊤)) = g :=
    (moduleSectionEquiv P.sheaf).apply_symm_apply g
  rw [Htop] at H
  exact H.symm.trans hg.2

theorem LineBundle.mixed_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow n).tensor M).sheaf,
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow n).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s n).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  classical
  choose U hUx he hd using common_affine_frames L M
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x).1 : X → Set X) (fun x => (U x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hUx x⟩)
  have hic (x : X) : ∃ i ∈ I, x ∈ (U i).1 := by
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    exact ⟨i,hi,hx⟩
  have : Nonempty I := by
    obtain ⟨x,-⟩ := hD
    obtain ⟨i,hi,-⟩ := hic x
    exact ⟨⟨i,hi⟩⟩
  exact L.finite_cover_mixed_extension M (fun i : I => (U i.val).1)
    (by intro x _; obtain ⟨i,hi,hx⟩ := hic x; exact Opens.mem_iSup.mpr ⟨⟨i,hi⟩,hx⟩)
    (fun i => (U i.val).2) (fun i => ⟨i.val,hUx i.val⟩)
    (fun i => Classical.choice (he i.val)) (fun i => Classical.choice (hd i.val)) s hD w

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TensorMixedSection
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.TensorPure

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma assoc_pure (L M N : LineBundle X) (U : X.Opens)
    (l : Γ(L.sheaf,U)) (m : Γ(M.sheaf,U)) (n : Γ(N.sheaf,U)) :
    (lineTensorAssoc L M N).hom.val.app (op U)
      (pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n) =
      pure L.sheaf (M.tensor N).sheaf U l (pure M.sheaf N.sheaf U m n) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  let P := L.sheaf.val ⊗ M.sheaf.val
  let Q := M.sheaf.val ⊗ N.sheaf.val
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let a := (lineTensorAssoc L M N)
  let v := ((adj X).unit.app (P ⊗ N.sheaf.val)).app (op U)
    ((l ⊗ₜ[Γ(X,U)] m) ⊗ₜ[Γ(X,U)] n)
  have hr : (sheafificationTensorRight P N).hom.val.app (op U) v =
      pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n := by
    have h := (adj X).unit.naturality
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
        ((adj X).unit.app P) (𝟙 N.sheaf.val))
    exact (congrArg (fun q => q.app (op U) ((l ⊗ₜ[Γ(X,U)] m) ⊗ₜ[Γ(X,U)] n)) h).symm
  have ha : (F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom).val.app (op U) v =
      ((adj X).unit.app (L.sheaf.val ⊗ Q)).app (op U)
        (l ⊗ₜ[Γ(X,U)] (m ⊗ₜ[Γ(X,U)] n)) := by
    have h := (adj X).unit.naturality (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom
    exact (congrArg (fun q => q.app (op U) ((l ⊗ₜ[Γ(X,U)] m) ⊗ₜ[Γ(X,U)] n)) h).symm
  have hl : (sheafificationTensorLeft Q L).hom.val.app (op U)
      (((adj X).unit.app (L.sheaf.val ⊗ Q)).app (op U)
        (l ⊗ₜ[Γ(X,U)] (m ⊗ₜ[Γ(X,U)] n))) =
      pure L.sheaf (M.tensor N).sheaf U l (pure M.sheaf N.sheaf U m n) := by
    have h := (adj X).unit.naturality
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
        (𝟙 L.sheaf.val) ((adj X).unit.app Q))
    exact (congrArg (fun q => q.app (op U) (l ⊗ₜ[Γ(X,U)] (m ⊗ₜ[Γ(X,U)] n))) h).symm
  change a.hom.val.app (op U) _ = _
  have hc : a.hom.val.app (op U) ((sheafificationTensorRight P N).hom.val.app (op U) v) =
      (sheafificationTensorLeft Q L).hom.val.app (op U)
        ((F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom).val.app (op U) v) := by
    change ((sheafificationTensorRight P N).hom ≫ a.hom).val.app (op U) v = _
    change ((sheafificationTensorRight P N).hom ≫
      (sheafificationTensorRight P N).inv ≫
      F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom ≫
      (sheafificationTensorLeft Q L).hom).val.app (op U) v = _
    have hs := (sheafificationTensorRight P N).hom_inv_id_assoc
      (F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom ≫
        (sheafificationTensorLeft Q L).hom)
    exact congrArg (fun q => q.val.app (op U) v) hs
  exact (congrArg (a.hom.val.app (op U)) hr).symm.trans (hc.trans ((congrArg
    ((sheafificationTensorLeft Q L).hom.val.app (op U)) ha).trans hl))

lemma assoc_inv_pure (L M N : LineBundle X) (U : X.Opens)
    (l : Γ(L.sheaf,U)) (m : Γ(M.sheaf,U)) (n : Γ(N.sheaf,U)) :
    (lineTensorAssoc L M N).inv.app U
      (pure L.sheaf (M.tensor N).sheaf U l (pure M.sheaf N.sheaf U m n)) =
      pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n := by
  have h := congrArg ((lineTensorAssoc L M N).inv.app U) (assoc_pure L M N U l m n)
  have hc : (lineTensorAssoc L M N).inv.app U
      ((lineTensorAssoc L M N).hom.val.app (op U)
        (pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n)) =
      pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n := by
    change ((lineTensorAssoc L M N).hom ≫ (lineTensorAssoc L M N).inv).app U _ = _
    rw [Iso.hom_inv_id]
    rfl
  exact h.symm.trans hc

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma unit_inv_apply (M : X.Modules) (U : X.Opens) (m : Γ(M,U)) :
    (moduleTensorUnit M).inv.app U m = pure (O X) M U (1 : Γ(X,U)) m := by
  have h := congrArg ((moduleTensorUnit M).inv.app U) (unit_pure M U (1 : Γ(X,U)) m)
  have hc : (moduleTensorUnit M).inv.app U
      ((moduleTensorUnit M).hom.app U (pure (O X) M U (1 : Γ(X,U)) m)) =
      pure (O X) M U (1 : Γ(X,U)) m := by
    change ((moduleTensorUnit M).hom ≫ (moduleTensorUnit M).inv).app U _ = _
    rw [Iso.hom_inv_id]
    rfl
  exact (congrArg ((moduleTensorUnit M).inv.app U) (one_smul Γ(X,U) m)).symm.trans (h.symm.trans hc)

lemma power_succ_apply {M : X.Modules} (s : O X ⟶ M) (n : ℕ) (U : X.Opens) :
    (powerSection s (n+1)).app U (1 : Γ(X,U)) =
      pure M (modulePow X M n) U (s.app U (1 : Γ(X,U)))
        ((powerSection s n).app U (1 : Γ(X,U))) := by
  change (moduleTensorMap s (modulePowMap s n)).app U
    ((moduleTensorUnit (modulePow X (O X) n)).inv.app U
      ((unitPowerIso n).inv.app U (1 : Γ(X,U)))) = _
  exact (congrArg ((moduleTensorMap s (modulePowMap s n)).app U)
    (unit_inv_apply _ U _)).trans (map_pure _ _ U _ _)

lemma openSection_tensor (M N : X.Modules) (U : X.Opens)
    (s : O U.toScheme ⟶ M.restrict U.ι) (t : O U.toScheme ⟶ N.restrict U.ι) :
    openSectionEquiv (moduleTensor X M N) U
      (tensorSection s t ≫ (moduleTensorRestrict U M N).inv) =
    pure M N U (openSectionEquiv M U s) (openSectionEquiv N U t) := by
  change (moduleTensor X M N).presheaf.map (eqToHom U.ι_image_top.symm).op
    ((moduleTensorRestrict U M N).inv.app ⊤ ((tensorSection s t).app ⊤ (1 : Γ(U.toScheme,⊤)))) = _
  have h := (congrArg ((moduleTensorRestrict U M N).inv.app ⊤)
    (section_apply s t ⊤)).trans (restrict_pure_inv U M N ⊤ _ _)
  exact (congrArg ((moduleTensor X M N).presheaf.map (eqToHom U.ι_image_top.symm).op) h).trans
    (pure_restrict M N (eqToHom U.ι_image_top.symm) _ _)

lemma mixed_value_restrict {M N : X.Modules} (U : X.Opens) (a : O X ⟶ M)
    (b : O U.toScheme ⟶ N.restrict U.ι) (t : O X ⟶ moduleTensor X M N)
    (ht : t.app U (1 : Γ(X,U)) = pure M N U (a.app U (1 : Γ(X,U))) (openSectionEquiv N U b)) :
    restrictSection U.ι t = tensorSection (restrictSection U.ι a) b ≫ (moduleTensorRestrict U M N).inv := by
  apply (openSectionEquiv (moduleTensor X M N) U).injective
  rw [openSectionEquiv_restrict,openSection_tensor,openSectionEquiv_restrict]
  exact ht

end PiExponentSeshadri.TensorPure

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_MixedFrameExtension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}}

theorem LineBundle.divisible_mixed_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t ≤ sectionOpen X s ∧
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow (n+1)).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s (n+1)).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  obtain ⟨N,hN⟩ := L.mixed_extension M s hD w
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht⟩ := hN n hn
  let q := tensorSection s t ≫ (lineTensorAssoc L (L.pow n) M).inv
  refine ⟨q,?_,?_⟩
  · change SectionOpens.isoOpen (tensorSection s t ≫ (lineTensorAssoc L (L.pow n) M).symm.hom) ≤ _
    erw [SectionOpens.isoOpen_postcomp,section_open L ((L.pow n).tensor M)]
    exact inf_le_left
  · let D := sectionOpen X s
    change (lineTensorAssoc L (L.pow n) M).inv.app D ((tensorSection s t).app D (1 : Γ(X,D))) = _
    have h := (section_apply s t D).trans
      (congrArg (pure L.sheaf ((L.pow n).tensor M).sheaf D (s.app D (1 : Γ(X,D)))) ht)
    exact (congrArg ((lineTensorAssoc L (L.pow n) M).inv.app D) h).trans
      ((assoc_inv_pure L (L.pow n) M D _ _ w).trans
       (congrArg (fun z => pure (L.pow (n+1)).sheaf M.sheaf D z w) (power_succ_apply s n D).symm))

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_MixedSectionOpenExtension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

theorem LineBundle.mixed_section_open_extension [IsIntegral X] [CompactSpace X]
    (L M : LineBundle X) (s : O X ⟶ L.sheaf)
    (hne : (sectionOpen X s : Set X).Nonempty)
    (w : O (sectionOpen X s).toScheme ⟶ M.sheaf.restrict (sectionOpen X s).ι) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t = (sectionOpen X s).ι ''ᵁ isoOpen w := by
  let U := sectionOpen X s
  obtain ⟨N,hN⟩ := L.divisible_mixed_extension M s hne (openSectionEquiv M.sheaf U w)
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht,hv⟩ := hN n hn
  have hi : IsIso (restrictSection U.ι (powerSection s (n+1))) :=
    isIso_restricted_section _ _ (L.sectionOpen_power s (by omega))
  have hpre : U.ι ⁻¹ᵁ isoOpen t = isoOpen w := by
    rw [← isoOpen_restrictSection]
    have hval := mixed_value_restrict U (powerSection s (n+1)) w t hv
    have hpost := isoOpen_postcomp (tensorSection (restrictSection U.ι (powerSection s (n+1))) w)
      (moduleTensorRestrict U (L.pow (n+1)).sheaf M.sheaf).symm
    have hopen := section_open ((L.pow (n+1)).restrict U.ι) (M.restrict U.ι)
      (restrictSection U.ι (powerSection s (n+1))) w
    refine (congrArg isoOpen hval).trans (hpost.trans (hopen.trans ?_))
    have he : isoOpen (restrictSection U.ι (powerSection s (n+1))) = ⊤ := by
      apply top_unique
      intro x _
      apply (mem_isoOpen_iff _ x).mpr
      exact ⟨⊤, trivial, by infer_instance⟩
    exact (congrArg (fun V : U.toScheme.Opens => V ⊓ isoOpen w) he).trans (top_inf_eq _)
  refine ⟨t,?_⟩
  change isoOpen t = _
  rw [← hpre,Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι]
  exact (inf_eq_right.mpr ht).symm
end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_RelativeAffineSectionAmple
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens PiExponentSeshadri.Projective
variable {X : Scheme.{0}}

theorem LineBundle.eventual_twist_affine_cover [IsIntegral X] [CompactSpace X]
    (P J : LineBundle X) {κ : Type} (t : κ → (O X ⟶ P.sheaf))
    (ht : (⨆ i,isoOpen (t i)) = ⊤)
    (hlocal : ∀ i, ∃ (α : Type)
      (w : α → (O (isoOpen (t i)).toScheme ⟶ J.sheaf.restrict (isoOpen (t i)).ι)),
        (⨆ a,isoOpen (w a)) = ⊤ ∧ ∀ a, IsAffineOpen (isoOpen (w a))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ (σ : Type) (_ : Fintype σ)
      (s : σ → (O X ⟶ ((P.pow (n+1)).tensor J).sheaf)),
        (⨆ a,isoOpen (s a)) = ⊤ ∧
        (∀ a, IsAffineOpen (isoOpen (s a))) ∧
        (∀ a, (isoOpen (s a) : Set X).Nonempty) := by
  classical
  choose α w hw hwa using hlocal
  have hex (x : X) : ∃ i, x ∈ isoOpen (t i) := by
    apply Opens.mem_iSup.mp
    rw [ht]; trivial
  choose i hi using hex
  have hex' (x : X) : ∃ a, (⟨x,hi x⟩ : (isoOpen (t (i x))).toScheme) ∈
      isoOpen (w (i x) a) := by
    apply Opens.mem_iSup.mp
    erw [hw]; trivial
  choose a ha using hex'
  let V (x : X) : X.Opens := (isoOpen (t (i x))).ι ''ᵁ isoOpen (w (i x) (a x))
  have hxV (x : X) : x ∈ V x := ⟨⟨x,hi x⟩,ha x,rfl⟩
  obtain ⟨F,hF⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hxV x⟩)
  choose N hN using fun x : F => P.mixed_section_open_extension J (t (i x.val))
    ⟨x.val,hi x.val⟩ (w (i x.val) (a x.val))
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose s hs using fun x : F => hN x n ((Finset.le_sup (Finset.mem_univ x)).trans hn)
  refine ⟨F,inferInstance,s,?_,?_,?_⟩
  · apply top_unique
    intro x _
    obtain ⟨y,hy⟩ := Set.mem_iUnion.mp (hF (show x ∈ Set.univ from trivial))
    obtain ⟨hyF,hxy⟩ := Set.mem_iUnion.mp hy
    apply Opens.mem_iSup.mpr
    refine ⟨⟨y,hyF⟩,?_⟩
    rw [show isoOpen (s ⟨y,hyF⟩) = V y from hs ⟨y,hyF⟩]
    exact hxy
  · intro x
    rw [show isoOpen (s x) = V x.val from hs x]
    exact (hwa (i x.val) (a x.val)).image_of_isOpenImmersion _
  · intro x
    rw [show isoOpen (s x) = V x.val from hs x]
    exact ⟨x.val,hxV x.val⟩

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupAmpleTwist
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens PiExponentSeshadri.Projective
variable {X : Scheme.{0}}

variable {B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.eventual_ample_exceptional_twist [IsIntegral B] [CompactSpace B]
    [CompactSpace X] (hπ : IsBlowup I π) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ a N : ℕ, 0 < a ∧ ∀ n : ℕ, N ≤ n →
      ((((L.pow a).pullback π).pow (n+1)).tensor J).IsAmple := by
  classical
  obtain ⟨a,ha,l,s,hs,hsa,-⟩ := L.ample_common_degree_cover hL
  let P := (L.pow a).pullback π
  let t (i : Fin l) : O B ⟶ P.sheaf := pullbackSection π (s i)
  have ht i : isoOpen (t i) = π ⁻¹ᵁ isoOpen (s i) := pullback_isoOpen_eq (L.pow a) (s i) π
  have hc : (⨆ i,isoOpen (t i)) = ⊤ := pullback_sections_cover s hs π
  have hloc (i : Fin l) : ∃ (α : Type)
      (w : α → (O (isoOpen (t i)).toScheme ⟶ J.sheaf.restrict (isoOpen (t i)).ι)),
        (⨆ a,isoOpen (w a)) = ⊤ ∧ ∀ a, IsAffineOpen (isoOpen (w a)) := by
    rw [ht]
    let U : X.affineOpens := ⟨isoOpen (s i),hsa i⟩
    let : IsAffine U.1.toScheme := U.2
    exact (hπ.morphismRestrict U.1).affine_section_cover (J.restrict (π ⁻¹ᵁ U.1).ι)
      (InvertibleLocal.restrictedInclusion J ι (π ⁻¹ᵁ U.1).ι)
      (presents_morphismRestrict J ι hJ U)
  obtain ⟨N,hN⟩ := P.eventual_twist_affine_cover J t hc hloc
  refine ⟨a,N,ha,fun n hn => ?_⟩
  obtain ⟨σ,hσ,q,hq,hqa,-⟩ := hN n hn
  exact ((P.pow (n+1)).tensor J).ample_of_affine_section_cover q hq hqa

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.exists_ample_exceptional_power_gt_one
    [IsIntegral B] [CompactSpace B] [CompactSpace X]
    (hπ : IsBlowup I π) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ a : ℕ, 1 < a ∧ (((L.pullback π).pow a).tensor J).IsAmple := by
  obtain ⟨a,N,ha,h⟩ := hπ.eventual_ample_exceptional_twist L hL J ι hJ
  refine ⟨a*(N+2), ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_right (N+2) (Nat.succ_le_of_lt ha)
    omega
  · apply PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _ _ (h (N+1) (by omega))
    exact moduleTensorIso
      ((modulePowFunctor (N+2)).mapIso (PullbackTensor.powIso π L a) ≪≫
        linePowerMul (L.pullback π) a (N+2)) (Iso.refl _)

end PiExponentSeshadri.Geometry

end

end OAI
end


