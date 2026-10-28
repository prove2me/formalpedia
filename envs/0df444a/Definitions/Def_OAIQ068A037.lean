-- Prove2me | Definitions.Def_OAIQ068A037
-- name    : OAIQ068A037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:12:45.754068+00:00
-- url     : https://prove2.me/theorems/7d489b7d-7d86-49ad-ad62-064c04fb1f5b
-- title:
--   Definitions bundle OAIQ068A037 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 76 declarations of OpenAI's Lean: 15 definitions and 61 theorems. The definitions and types are `OAI.PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearEquiv`, `OAI.PiExponent.CohomologyFiniteness.CohomologyFinite`, `OAI.PiExponent.GeometrySupport.CechExtFinite.comparisonStep`, `OAI.PiExponent.GeometrySupport.CechExtFinite.descent`, `OAI.PiExponent.GeometrySupport.CechExtFinite.mkZeroLinear`, `OAI.PiExponent.GeometrySupport.CechExtFinite.sourceIso`, `OAI.PiExponent.GeometrySupport.CechExtFinite.zeroComparison`, `OAI.PiExponent.GeometrySupport.CechZero.sectionsEquiv`, `OAI.PiExponent.GeometrySupport.LaurentCechFinite.cochainEquiv`, `OAI.PiExponent.GeometrySupport.LaurentCechFinite.cochainMap`, `OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesEquiv`, `OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesMap`, `OAI.PiExponent.NegativeTwistPresentations.coherentFinitePresentation`, `OAI.PiExponentSeshadri.Geometry.tensorInclusion`, `OAI.PiExponentSeshadri.Projective.negativeCoordinateFrame`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AmpleGlobalGeneration`, `PiExponent_Approximation_ClosedImmersionSerreTransfer`, `PiExponent_Approximation_ClosedPushforwardLinear`, `PiExponent_Approximation_GlobalSectionClearing`, `PiExponent_Approximation_NegativeTwistPresentations`, `PiExponent_Approximation_TwistGlobalExtension`, `PiExponent_Approximation_TwistSectionClearing`, `PiExponent_Approximation_TwistSectionScalars`, `PiExponent_Cohomology_CechExtFinite`, `PiExponent_Cohomology_CechHigher`, `PiExponent_Cohomology_CechLinear`, `PiExponent_Cohomology_CechZero`, `PiExponent_Cohomology_CohomologyFinite`, `PiExponent_Cohomology_LaurentCechFinite`, `PiExponent_Cohomology_LaurentExtFinite`, `PiExponent_Cohomology_ProjectiveFramedCech`, `PiExponent_Geometry_ProjectiveNegativeFrames`, `PiExponent_LocalAlgebra_CoherentExtFiniteness`, `PiExponent_LocalAlgebra_TensorIdealInclusion`, `PiExponent_LocalAlgebra_TwistLocalExtension`.
--
--   **Imports.** It imports the bundles `OAIQ068A028`, `OAIQ068A029`, `OAIQ068A030` and `OAIQ068A031` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A040`, `OAIQ068A041` and `OAIQ068A042`; the proofs of `OAI_PiExponent_NumericalAmpleness_exists_regular_twist_pair` and `OAI.PiExponent.NumericalAmpleness.exists_regular_twist_pair_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ068A028
import Definitions.Def_OAIQ068A029
import Definitions.Def_OAIQ068A030
import Definitions.Def_OAIQ068A031

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlobalSectionClearing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem compact_open_section_zero (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (U : X.Opens) (hU : IsCompact (U : Set X))
    (x : OpenSections M U)
    (hx : openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  classical
  obtain ⟨s, hs, e⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : X.Opens) := by
    ext1
    simpa using e
  have h₁ (i : s) : i.1.1 ≤ U := by
    rw [e]
    exact le_iSup (fun i : s => (i : X.Opens)) i
  have H (i : s) : ∃ N : ℕ, ∀ n ≥ N,
      openRestriction M (h₁ i) (r ^ n • x) = 0 := by
    let : IsAffine i.1.1.toScheme := i.1.2
    have hh := affine_immersion_zero_on M i.1.1.ι r U
      (by simpa only [Scheme.Opens.ι_image_top] using h₁ i) x hx
    obtain ⟨N, hN⟩ := hh
    exact ⟨N, fun n hn => openRestriction_zero_congr M i.1.1.ι_image_top _ _ _ (hN n hn)⟩
  choose n hn using H
  have := hs.to_subtype
  let := Fintype.ofFinite s
  refine ⟨Finset.univ.sup n, fun k hk => ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i : s => (i : X.Opens)) U
    (fun i => homOfLE (h₁ i)) (by rw [e])
  intro i
  have hi := hn i k ((Finset.le_sup (f := n) (Finset.mem_univ i)).trans hk)
  change M.presheaf.map _ (r ^ k • x) = M.presheaf.map _ 0
  rw [map_zero]
  exact hi

theorem clear_finite_overlap_discrepancies (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hcompact : ∀ i j, IsCompact ((U i ⊓ U j : X.Opens) : Set X))
    (x : OpenSections M (X.basicOpen r)) (N : ℕ) (y : ∀ i, OpenSections M (U i))
    (hy : ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
      r ^ N • openRestriction M inf_le_right x) :
    ∃ K : ℕ, ∀ i j,
      openRestriction M (show U i ⊓ U j ≤ U i from inf_le_left) (r ^ K • y i) =
      openRestriction M (show U i ⊓ U j ≤ U j from inf_le_right) (r ^ K • y j) := by
  classical
  have h (ij : ι × ι) := compact_open_section_zero M r (U ij.1 ⊓ U ij.2)
    (hcompact ij.1 ij.2) (overlapDifference M (y ij.1) (y ij.2))
    (overlapDifference_restrict_zero M r x N _ _ (hy ij.1) (hy ij.2))
  choose k hk using h
  let K := Finset.univ.sup k
  refine ⟨K, fun i j => ?_⟩
  apply (overlapDifference_smul_zero_iff M r (y i) (y j) K).mp
  exact hk (i,j) K (Finset.le_sup (f := k) (Finset.mem_univ (i,j)))

theorem finite_cover_power_gluing (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤)
    (hcompact : ∀ i j, IsCompact ((U i ⊓ U j : X.Opens) : Set X))
    (x : OpenSections M (X.basicOpen r)) (N : ℕ) (y : ∀ i, OpenSections M (U i))
    (hy : ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
      r ^ N • openRestriction M inf_le_right x) :
    ∃ K : ℕ, ∃ z : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) z = r ^ (N + K) • x := by
  obtain ⟨K, hK⟩ := clear_finite_overlap_discrepancies M r U hcompact x N y hy
  have hh := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ U ⊤
    (fun i => homOfLE (show U i ≤ ⊤ from le_top)) (by rw [hcover]) (fun i => r ^ K • y i) ?_
  · obtain ⟨z, hz, _⟩ := hh
    exact ⟨K, z, restriction_of_glued_power M r U hcover x N K y hy z hz⟩
  · intro i j
    exact hK i j

theorem global_section_extends [NoetherianSpace X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M (X.basicOpen r)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) y = r ^ n • x := by
  classical
  obtain ⟨s, hs, e⟩ :=
    (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (X := X)
      (U := ((⊤ : X.Opens) : Set X))).mp
      ⟨NoetherianSpace.isCompact _, (⊤ : X.Opens).2⟩
  have hcover : (⨆ i : s, (i : X.Opens)) = ⊤ := by
    ext1
    simpa using e.symm
  have := hs.to_subtype
  let := Fintype.ofFinite s
  obtain ⟨N, y, hy⟩ := finite_affine_local_extensions M r (fun i : s => (i : X.Opens))
    (fun i => i.1.2) x
  obtain ⟨K, z, hz⟩ := finite_cover_power_gluing M r (fun i : s => (i : X.Opens)) hcover
    (fun i j => NoetherianSpace.isCompact _) x N y hy
  refine ⟨N + K, fun n hn => ⟨r ^ (n - (N + K)) • z, ?_⟩⟩
  rw [map_smul, hz, ← mul_smul, ← pow_add, Nat.sub_add_cancel hn]

theorem global_section_extends_native [NoetherianSpace X]
    (M : X.Modules) [M.IsQuasicoherent] (r : Γ(X,⊤)) (x : Γ(M, X.basicOpen r)) :
    letI : Module Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
      (M.val.obj (op (X.basicOpen r))).isModule
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : Γ(M,⊤),
      M.presheaf.map (homOfLE (X.basicOpen_le r)).op y =
        (restrictScalar X (X.basicOpen r) r) ^ n • x := by
  let : Module Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
    (M.val.obj (op (X.basicOpen r))).isModule
  obtain ⟨N, hN⟩ := global_section_extends M r x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn
  refine ⟨y, ?_⟩
  change M.presheaf.map (homOfLE (X.basicOpen_le r)).op y =
    (restrictScalar X (X.basicOpen r) (r ^ n)) • x at hy
  simpa only [map_pow] using hy

end
end PiExponent.GlobalSectionClearing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TwistSectionScalars
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PiExponentSeshadri.TensorPure PiExponentSeshadri.Frames
variable {X : Scheme}

lemma moduleSectionMultiplyRight_restrict_frame (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (U : X.Opens)
    (e : L.restrict U.ι ≅ structureSheaf U.toScheme) (V : U.toScheme.Opens)
    (m : Γ(M,U.ι ''ᵁ V)) :
    ((moduleTensorRestrictFrame U L e).app M).hom.app V
      ((moduleSectionMultiplyRight M s).app (U.ι ''ᵁ V) m) =
      U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (coefficient e (restrictSection U.ι s)) •
        (show Γ(M.restrict U.ι,V) from m) := by
  change (moduleTensorFrame (M.restrict U.ι) e).hom.app V
    ((moduleTensorRestrict U M L).hom.app V
      ((moduleSectionMultiplyRight M s).app (U.ι ''ᵁ V) m)) = _
  have h₁ := moduleSectionMultiplyRight_pure M s (U.ι ''ᵁ V) m
  have h₂ := restrict_pure U M L V m (s.app (U.ι ''ᵁ V) (1 : Γ(X, U.ι ''ᵁ V)))
  have h₃ := moduleTensorFrame_pure (M.restrict U.ι) e V m
    (s.app (U.ι ''ᵁ V) (1 : Γ(X, U.ι ''ᵁ V)))
  refine ((congrArg (fun t => (moduleTensorFrame (M.restrict U.ι) e).hom.app V
      ((moduleTensorRestrict U M L).hom.app V t)) h₁).trans
    ((congrArg (fun t => (moduleTensorFrame (M.restrict U.ι) e).hom.app V t) h₂).trans h₃)).trans ?_
  have h := end_naturality (restrictSection U.ι s ≫ e.hom) V
  apply congrArg (fun a : Γ(U.toScheme,V) => a • (show Γ(M.restrict U.ι,V) from m))
  calc
    _ = (show Γ(U.toScheme,V) from e.hom.app V ((restrictSection U.ι s).app V
        (1 : Γ(U.toScheme,V)))) := by
      change e.hom.app V (s.app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V))) =
        e.hom.app V (s.app (U.ι ''ᵁ V) ((U.ι.appIso V).inv (1 : Γ(U.toScheme,V))))
      rw [show (U.ι.appIso V).inv (1 : Γ(U.toScheme,V)) =
        (1 : Γ(X,U.ι ''ᵁ V)) from (U.ι.appIso V).inv.hom.map_one]
    _ = _ := h

lemma moduleTwistForward_frame (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) (V : U.toScheme.Opens) (n k : ℕ)
    (m : Γ((moduleTwistFunctor L n).obj M,U.ι ''ᵁ V)) :
    ((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V
      (((moduleTwistForward L s n k).app M).app (U.ι ''ᵁ V) m) =
      (U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (coefficient e (restrictSection U.ι s))) ^ k •
          ((moduleTwistRestrictFrame L U e n).app M).hom.app V m := by
  induction k with
  | zero => simp only [moduleTwistForward, NatTrans.id_app, pow_zero, one_smul]; rfl
  | succ k ih =>
    change ((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V
      (((moduleTensorRestrictFrame U L.sheaf e).app ((moduleTwistFunctor L (n+k)).obj M)).hom.app V
        ((moduleSectionMultiplyRight ((moduleTwistFunctor L (n+k)).obj M) s).app
          (U.ι ''ᵁ V) (((moduleTwistForward L s n k).app M).app (U.ι ''ᵁ V) m))) = _
    rw [moduleSectionMultiplyRight_restrict_frame, Scheme.Modules.Hom.app_smul,
      ih, smul_smul, pow_succ']

lemma moduleTwistSection_frame (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) (V : U.toScheme.Opens) (n : ℕ) (m : Γ(M,U.ι ''ᵁ V)) :
    ((moduleTwistRestrictFrame L U e n).app M).hom.app V
      (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ V) m) =
      (U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (coefficient e (restrictSection U.ι s))) ^ n •
          (show Γ(M.restrict U.ι,V) from m) := by
  induction n with
  | zero =>
      simp only [moduleTwistSection, moduleTwistRestrictFrame, NatTrans.id_app, pow_zero]
      exact (one_smul Γ(U.toScheme, V) (show Γ(M.restrict U.ι, V) from m)).symm
  | succ n ih =>
    change ((moduleTwistRestrictFrame L U e n).app M).hom.app V
      (((moduleTensorRestrictFrame U L.sheaf e).app ((moduleTwistFunctor L n).obj M)).hom.app V
        ((moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj M) s).app
          (U.ι ''ᵁ V) (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ V) m))) = _
    rw [moduleSectionMultiplyRight_restrict_frame, Scheme.Modules.Hom.app_smul,
      ih, smul_smul, pow_succ']

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TwistSectionClearing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.TwistSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GlobalSectionClearing
variable {X : Scheme}

theorem frame_twistForward_zero_on (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (V : U.toScheme.Opens) (hV : IsCompact (V : Set U.toScheme))
    (x : Γ(((moduleTwistFunctor L n).obj M).restrict U.ι, V))
    (hx : (((moduleTwistFunctor L n).obj M).restrict U.ι).presheaf.map (homOfLE
      (show V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤ V from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K,
      (((moduleTwistForward L s n k).app M).app (U.ι ''ᵁ V)) x = 0 := by
  let c := coefficient e (restrictSection U.ι s)
  let E := (moduleTwistRestrictFrame L U e n).app M
  have hz := iso_section_restrict_zero_on E
    (show V ⊓ U.toScheme.basicOpen c ≤ V from inf_le_left) x hx
  obtain ⟨K, hK⟩ := compact_open_section_zero (M.restrict U.ι) c V hV (E.hom.app V x) hz
  refine ⟨K, fun k hk => ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V)).injective
  refine (moduleTwistForward_frame L s U e M V n k x).trans ?_
  have hh := hK k hk
  change (_root_.OAI.PiExponent.GlobalSectionClearing.restrictScalar U.toScheme V (c ^ k)) • E.hom.app V x = 0 at hh
  rw [map_pow] at hh
  exact hh.trans (map_zero (((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V).hom).symm

theorem frame_twistForward_ambient_zero [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (W : X.Opens)
    (x : Γ((moduleTwistFunctor L n).obj M, W))
    (hx : ((moduleTwistFunctor L n).obj M).presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K,
      ((moduleTwistFunctor L (n+k)).obj M).presheaf.map
        (homOfLE (show U ⊓ W ≤ W from inf_le_right)).op
        (((moduleTwistForward L s n k).app M).app W x) = 0 := by
  let : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set X)
  let V := U.ι ⁻¹ᵁ W
  have hVW : U.ι ''ᵁ V ≤ W := U.ι.image_preimage_le W
  have hlocal := frame_local_input_zero_on L s U e ((moduleTwistFunctor L n).obj M) W V hVW x hx
  obtain ⟨K, hK⟩ := frame_twistForward_zero_on L s U e M n V
    (NoetherianSpace.isCompact _) _ hlocal
  refine ⟨K, fun k hk => ?_⟩
  have hh : ((moduleTwistFunctor L (n+k)).obj M).presheaf.map (homOfLE hVW).op
      (((moduleTwistForward L s n k).app M).app W x) = 0 := by
    rw [hom_section_restriction]
    exact hK k hk
  have he : U.ι ''ᵁ V = U ⊓ W := by
    dsimp only [V]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact openRestriction_zero_congr ((moduleTwistFunctor L (n+k)).obj M) he _ _ _ hh

theorem twistForward_section_zero [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (W : X.Opens) (x : Γ((moduleTwistFunctor L n).obj M, W))
    (hx : ((moduleTwistFunctor L n).obj M).presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K, ((moduleTwistForward L s n k).app M).app W x = 0 := by
  classical
  choose U hxU he using L.locallyRankOne
  let e (a : X) := Classical.choice (he a)
  have hcover : IsOpenCover U := by
    rw [IsOpenCover]
    apply top_unique
    intro a ha
    exact Opens.mem_iSup.mpr ⟨a, hxU a⟩
  obtain ⟨I, hI⟩ := hcover.exists_finite_of_compactSpace
  have hI' : (⨆ i : I, U i.val) = ⊤ := hI
  choose K hK using fun i : I => frame_twistForward_ambient_zero L s (U i.val)
    (e i.val) M n W x hx
  refine ⟨Finset.univ.sup K, fun k hk => ?_⟩
  let P := (moduleTwistFunctor L (n+k)).obj M
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨P.presheaf, P.isSheaf⟩
    (fun i : I => U i.val ⊓ W) W (fun i => homOfLE inf_le_right)
    (by rw [← iSup_inf_eq, hI', top_inf_eq])
  intro i
  have hi := hK i k ((Finset.le_sup (f := K) (Finset.mem_univ i)).trans hk)
  change P.presheaf.map _ (((moduleTwistForward L s n k).app M).app W x) = P.presheaf.map _ 0
  rw [map_zero]
  exact hi

end
end PiExponent.TwistSectionClearing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_TwistLocalExtension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponentSeshadri.Frames PiExponent.GlobalSectionClearing
variable {X : Scheme}

theorem local_twist_extension (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens) [NoetherianSpace U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent]
    (x : Γ(M.restrict U.ι, U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)))) :
    let a := coefficient e (restrictSection U.ι s)
    let D := U.toScheme.basicOpen a
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : Γ(((moduleTwistFunctor L n).obj M).restrict U.ι,⊤),
      (((moduleTwistFunctor L n).obj M).restrict U.ι).presheaf.map
        (homOfLE (U.toScheme.basicOpen_le a)).op y =
      ((moduleTwistRestrictFrame L U e n).app M).inv.app D
        ((_root_.OAI.PiExponent.GlobalSectionClearing.restrictScalar U.toScheme D a)^n • x) := by
  dsimp only
  obtain ⟨N, hN⟩ := global_section_extends_native (M.restrict U.ι)
    (coefficient e (restrictSection U.ι s)) x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn
  let E := (moduleTwistRestrictFrame L U e n).app M
  refine ⟨E.inv.app ⊤ y, ?_⟩
  have h := CategoryTheory.congr_fun (E.inv.mapPresheaf.naturality
    (homOfLE (U.toScheme.basicOpen_le (coefficient e (restrictSection U.ι s)))).op) y
  exact h.symm.trans (congrArg (E.inv.app _) hy)

theorem local_twist_extension_section (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens) [NoetherianSpace U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent]
    (x : Γ(M.restrict U.ι, U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)))) :
    let a := coefficient e (restrictSection U.ι s)
    let D := U.toScheme.basicOpen a
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : Γ(((moduleTwistFunctor L n).obj M).restrict U.ι,⊤),
      (((moduleTwistFunctor L n).obj M).restrict U.ι).presheaf.map
        (homOfLE (U.toScheme.basicOpen_le a)).op y =
      ((moduleTwistSection L s n).app M).app (U.ι ''ᵁ D) x := by
  dsimp only
  obtain ⟨N, hN⟩ := local_twist_extension L s U e M x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn
  refine ⟨y, hy.trans ?_⟩
  let D := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
  let E := (moduleTwistRestrictFrame L U e n).app M
  have h := moduleTwistSection_frame L s U e M D n x
  calc
    _ = E.inv.app D (E.hom.app D (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ D) x)) :=
      congrArg (E.inv.app D) h.symm
    _ = _ := congrArg (fun q => q.app D
      (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ D) x)) E.hom_inv_id

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TwistGlobalExtension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.TwistGlobalExtension
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GlobalSectionClearing PiExponent.SheafSectionGluing
variable {X : Scheme}

theorem local_twist_extension_ambient (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens) [NoetherianSpace U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent] (x : _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections ((moduleTwistFunctor L n).obj M) U,
      _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction ((moduleTwistFunctor L n).obj M)
        (show U ⊓ sectionOpen X s ≤ U from inf_le_left) y =
      mapSection ((moduleTwistSection L s n).app M) (U ⊓ sectionOpen X s)
        (_root_.OAI.PiExponent.GlobalSectionClearing.openRestriction M inf_le_right x) := by
  let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
  let W := U.ι ''ᵁ V
  have hWU : W ≤ U := U.ι_image_le V
  have hW : W = U ⊓ sectionOpen X s := section_open_image s U e
  have hWD : W ≤ sectionOpen X s := hW.le.trans inf_le_right
  let x0 : Γ(M.restrict U.ι,V) := M.presheaf.map (homOfLE hWD).op x
  obtain ⟨N, hN⟩ := local_twist_extension_section L s U e M x0
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := hN n hn
  let P := (moduleTwistFunctor L n).obj M
  let z0 : _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections P (U.ι ''ᵁ ⊤) := z
  let y : _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections P U := _root_.OAI.PiExponent.GlobalSectionClearing.openSectionsCongr P U.ι_image_top z0
  refine ⟨y, ?_⟩
  have ht := openSectionsCongr_naturality P (rfl : W = W) U.ι_image_top
    (U.ι.image_mono (show V ≤ ⊤ from le_top)) hWU z0
  have hres : _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P hWU y =
      mapSection ((moduleTwistSection L s n).app M) W (_root_.OAI.PiExponent.GlobalSectionClearing.openRestriction M hWD x) := by
    exact ht.symm.trans hz
  have hh := congrArg (_root_.OAI.PiExponent.GlobalSectionClearing.openSectionsCongr P hW) hres
  rw [openSectionsCongr_naturality P hW rfl hWU inf_le_left, mapSection_congr] at hh
  change _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P (show U ⊓ sectionOpen X s ≤ U from inf_le_left) y =
    mapSection ((moduleTwistSection L s n).app M) (U ⊓ sectionOpen X s)
      (_root_.OAI.PiExponent.GlobalSectionClearing.openSectionsCongr M hW (_root_.OAI.PiExponent.GlobalSectionClearing.openRestriction M hWD x)) at hh
  rw [openSectionsCongr_naturality M hW rfl hWD inf_le_right] at hh
  exact hh

theorem finite_local_twist_extensions [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (e : ∀ i, L.sheaf.restrict (U i).ι ≅ structureSheaf (U i).toScheme)
    (x : _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∃ y : ∀ i, _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections ((moduleTwistFunctor L N).obj M) (U i),
      ∀ i, _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction ((moduleTwistFunctor L N).obj M)
        (show U i ⊓ sectionOpen X s ≤ U i from inf_le_left) (y i) =
      mapSection ((moduleTwistSection L s N).app M) (U i ⊓ sectionOpen X s)
        (_root_.OAI.PiExponent.GlobalSectionClearing.openRestriction M inf_le_right x) := by
  classical
  have H (i : ι) := by
    letI : NoetherianSpace (U i).toScheme := NoetherianSpace.set (U i : Set X)
    exact local_twist_extension_ambient L s (U i) (e i) M x
  choose N hN using H
  let m := Finset.univ.sup N
  choose y hy using fun i => hN i m (Finset.le_sup (f := N) (Finset.mem_univ i))
  exact ⟨m, y, hy⟩

theorem finite_cover_twist_gluing [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type*} [Fintype ι] (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (x : _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections M (sectionOpen X s)) (N : ℕ)
    (y : ∀ i, _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections ((moduleTwistFunctor L N).obj M) (U i))
    (hy : ∀ i, _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction ((moduleTwistFunctor L N).obj M)
        (show U i ⊓ sectionOpen X s ≤ U i from inf_le_left) (y i) =
      mapSection ((moduleTwistSection L s N).app M) (U i ⊓ sectionOpen X s)
        (_root_.OAI.PiExponent.GlobalSectionClearing.openRestriction M inf_le_right x)) :
    ∃ K : ℕ, ∃ z : _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections ((moduleTwistFunctor L (N+K)).obj M) ⊤,
      _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction ((moduleTwistFunctor L (N+K)).obj M)
        (show sectionOpen X s ≤ ⊤ from le_top) z =
      mapSection ((moduleTwistSection L s (N+K)).app M) (sectionOpen X s) x := by
  classical
  let P := (moduleTwistFunctor L N).obj M
  let a := mapSection ((moduleTwistSection L s N).app M) (sectionOpen X s) x
  have hya (i : ι) : _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P (show U i ⊓ sectionOpen X s ≤ U i from inf_le_left) (y i) =
      _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P inf_le_right a :=
    (hy i).trans (mapSection_naturality ((moduleTwistSection L s N).app M) inf_le_right x)
  let diff (ij : ι × ι) := _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P (show U ij.1 ⊓ U ij.2 ≤ U ij.1 from inf_le_left) (y ij.1) -
    _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P (show U ij.1 ⊓ U ij.2 ≤ U ij.2 from inf_le_right) (y ij.2)
  have H (ij : ι × ι) :=
    PiExponent.TwistSectionClearing.twistForward_section_zero L s M N (U ij.1 ⊓ U ij.2)
      (diff ij) (overlap_difference_zero U (sectionOpen X s) a y hya ij.1 ij.2)
  choose K hK using H
  let k := Finset.univ.sup K
  have hcompat (i j : ι) :
      mapSection ((moduleTwistForward L s N k).app M) (U i ⊓ U j)
        (_root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P inf_le_left (y i)) =
      mapSection ((moduleTwistForward L s N k).app M) (U i ⊓ U j)
        (_root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P inf_le_right (y j)) := by
    have h := hK (i,j) k (Finset.le_sup (f := K) (Finset.mem_univ (i,j)))
    change mapSection ((moduleTwistForward L s N k).app M) (U i ⊓ U j)
      (_root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P inf_le_left (y i) - _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P inf_le_right (y j)) = 0 at h
    rwa [map_sub, sub_eq_zero] at h
  obtain ⟨z, hz⟩ := glue_after_map ((moduleTwistForward L s N k).app M) U hcover y hcompat
  refine ⟨k, z, ?_⟩
  exact (restriction_of_glued_map ((moduleTwistForward L s N k).app M) U hcover
    (sectionOpen X s) a y hya z hz).trans (mapSection_twistSection_add L s M _ x N k)

theorem exists_global_twist_extension [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (x : _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∃ z : _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections ((moduleTwistFunctor L N).obj M) ⊤,
      _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction ((moduleTwistFunctor L N).obj M)
        (show sectionOpen X s ≤ ⊤ from le_top) z =
      mapSection ((moduleTwistSection L s N).app M) (sectionOpen X s) x := by
  classical
  choose U hUx he using L.locallyRankOne
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hUx x⟩)
  have hcover : (⨆ i : I, U i.val) = ⊤ := by
    apply le_antisymm le_top
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI hx)
    obtain ⟨hi, hxU⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxU⟩
  let e (i : I) := Classical.choice (he i.val)
  obtain ⟨N, y, hy⟩ := finite_local_twist_extensions L s M (fun i : I => U i.val) e x
  obtain ⟨K, z, hz⟩ := finite_cover_twist_gluing L s M (fun i : I => U i.val) hcover x N y hy
  exact ⟨N+K, z, hz⟩

theorem global_twist_extension [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (x : _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z : _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections ((moduleTwistFunctor L n).obj M) ⊤,
      _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction ((moduleTwistFunctor L n).obj M)
        (show sectionOpen X s ≤ ⊤ from le_top) z =
      mapSection ((moduleTwistSection L s n).app M) (sectionOpen X s) x := by
  obtain ⟨N, z, hz⟩ := exists_global_twist_extension L s M x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨mapSection ((moduleTwistForward L s N k).app M) ⊤ z, ?_⟩
  rw [← mapSection_naturality, hz]
  exact mapSection_twistSection_add L s M _ x N k

theorem global_twist_extension_native [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (x : Γ(M,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z : Γ((moduleTwistFunctor L n).obj M,⊤),
      ((moduleTwistFunctor L n).obj M).presheaf.map
        (homOfLE (show sectionOpen X s ≤ ⊤ from le_top)).op z =
      ((moduleTwistSection L s n).app M).app (sectionOpen X s) x :=
  global_twist_extension L s M x

end
end PiExponent.TwistGlobalExtension

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleGlobalGeneration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AmpleGlobalGeneration
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CoherentAffineFinite
variable {X : Scheme.{0}}

theorem eventual_global_generators_of_section_cover [NoetherianSpace X]
    (L : LineBundle X) (M : X.Modules) [M.IsFinitePresentation]
    {ι : Type} [Finite ι] (s : ι → (structureSheaf X ⟶ L.sheaf))
    (hcover : (⨆ i, sectionOpen X (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (sectionOpen X (s i))) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor L n).obj M).GeneratingSections, G.IsFiniteType := by
  classical
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  let U (i : ι) := sectionOpen X (s i)
  choose σ hσ using fun i => affine_local_generators M (U i) (haffine i)
  let (i : ι) : (σ i).IsFiniteType := hσ i
  let (i : ι) : Finite (σ i).I := (hσ i).finite
  let a (i : ι) (j : (σ i).I) :=
    (M.restrict (U i).ι).unitHomEquiv.symm ((σ i).s j)
  let x (i : ι) (j : (σ i).I) : Γ(M,U i) := openSectionEquiv M (U i) (a i j)
  choose d hd using fun ij : Σ i, (σ i).I =>
    PiExponent.TwistGlobalExtension.global_twist_extension_native L (s ij.1) M (x ij.1 ij.2)
  let : Fintype (Σ i, (σ i).I) := Fintype.ofFinite _
  let N := Finset.univ.sup d
  refine ⟨N, fun n hn => ?_⟩
  let Q := (moduleTwistFunctor L n).obj M
  have hn' (ij : Σ i, (σ i).I) : d ij ≤ n :=
    (Finset.le_sup (f := d) (Finset.mem_univ ij)).trans hn
  choose z hz using fun ij : Σ i, (σ i).I => hd ij n (hn' ij)
  let f (i : ι) : M.restrict (U i).ι ⟶ Q.restrict (U i).ι :=
    (Scheme.Modules.restrictFunctor (U i).ι).map ((moduleTwistSection L (s i) n).app M)
  have hf (i : ι) : IsIso (f i) := twistSection_isIso_restrict L (s i) M n
  let τ (i : ι) : (Q.restrict (U i).ι).GeneratingSections :=
    SheafOfModules.GeneratingSections.equivOfIso
      (@asIso _ _ _ _ (f i) (hf i)) (σ i)
  let (i : ι) : (τ i).IsFiniteType := ⟨(hσ i).finite⟩
  let t (i : ι) (j : (τ i).I) : GlobalSections X Q :=
    (moduleSectionEquiv Q).symm (z ⟨i,j⟩)
  have ht (i : ι) (j : (τ i).I) : restrictSection (U i).ι (t i j) =
      (Q.restrict (U i).ι).unitHomEquiv.symm ((τ i).s j) := by
    apply (openSectionEquiv Q (U i)).injective
    change openSectionEquiv Q (U i)
      (restrictSection (U i).ι ((moduleSectionEquiv Q).symm (z ⟨i,j⟩))) =
      openSectionEquiv Q (U i) ((Q.restrict (U i).ι).unitHomEquiv.symm
        (SheafOfModules.sectionsMap (f i) ((σ i).s j)))
    erw [openSectionEquiv_restrict_from_top, ← SheafOfModules.unitHomEquiv_symm_comp]
    erw [openSectionEquiv_postcomp]
    exact hz ⟨i,j⟩
  exact PiExponent.GlueGlobalGenerators.exists_finite_global_generators Q U hcover τ t ht

end
end PiExponent.AmpleGlobalGeneration

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedImmersionSerreTransfer
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite
open PiExponentSeshadri.FlasqueCohomology

namespace PiExponent.ClosedImmersionSerreTransfer

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

variable [PreservesFiniteColimits (Scheme.Modules.pushforward f)]

local instance instHasExtModules_solutions_rba2938_1 : HasExt.{u+1} X.Modules := HasExt.standard _
attribute [local instance] OAI.PiExponent.ClosedImmersionSerreTransfer.instHasExtModules_solutions_1
theorem cohomologyMap_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective (cohomologyMap f M n) := by
  let : EnoughInjectives X.Modules :=
    PiExponentSeshadri.ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  apply PiExponentSeshadri.ExtSectionComparison.mapFrom_bijective
  · exact globalHom_push_bijective f
  · intro I hI q x
    let : Injective (C := SheafOfModules X.ringCatSheaf) I := hI
    let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj I) :=
      PiExponentSeshadri.ModuleFlasque.injective_isFlasque X.ringCatSheaf I
    exact flasque_ext_zero Y.ringCatSheaf q ((Scheme.Modules.pushforward f).obj I) x

end PiExponent.ClosedImmersionSerreTransfer

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPushforwardLinear
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ClosedImmersionSerreTransfer

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

variable [IsClosedImmersion f]

local instance closedPushforwardLinearSourceHasExt_rba2938_1 : HasExt.{1} X.Modules := schemeHasExt
attribute [local instance] OAI.PiExponent.ClosedImmersionSerreTransfer.closedPushforwardLinearTargetHasExt
lemma typedCohomologyMap_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective (typedCohomologyMap f M n) :=
  cohomologyMap_bijective f M n

def cohomologyLinearEquiv (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
    cohomology M n ≃ₗ[ℂ] cohomology ((Scheme.Modules.pushforward f).obj M) n := by
  exact LinearEquiv.ofBijective (cohomologyLinearMap f p M n)
    (by rw [cohomologyLinearMap_eq]; exact typedCohomologyMap_bijective f M n)

theorem finiteDimensional_of_pushforward
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ)
    (hfinite : letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
      FiniteDimensional ℂ (cohomology ((Scheme.Modules.pushforward f).obj M) n)) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    FiniteDimensional ℂ (cohomology M n) := by
  let := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  have := hfinite
  exact FiniteDimensional.of_injective (cohomologyLinearEquiv f p M n).toLinearMap
    (cohomologyLinearEquiv f p M n).injective

end
end PiExponent.ClosedImmersionSerreTransfer

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoherentExtFiniteness
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CoherentExtFiniteness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry

universe w v u t k
variable {K : Type k} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
    [Linear K C] [HasExt.{w} C]

variable {X : Scheme.{0}}

theorem cohomology_finite_of_biproduct
    (p : X ⟶ Spec (CommRingCat.of ℂ)) {J : Type*} [Fintype J]
    {B : J → X.Modules} {c : Bicone B} (hc : c.IsBilimit) (q : ℕ)
    (hfinite : ∀ j, letI := Module.compHom (cohomology (B j) q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (B j) q)) :
    letI := Module.compHom (cohomology c.pt q) (baseScalars p)
    FiniteDimensional ℂ (cohomology c.pt q) := by
  let := sheafComplexLinear p
  have hfin : ∀ j, Module.Finite ℂ (Ext.{1} (structureSheaf X) (B j) q) := by
    intro j
    change @Module.Finite ℂ (cohomology (B j) q) _ _ (complexExtModule p (B j) q)
    rw [complexExtModule_eq]
    exact hfinite j
  have hf := ext_finite_of_biproduct (K := ℂ) (structureSheaf X) hc q hfin
  change @Module.Finite ℂ (cohomology c.pt q) _ _ (complexExtModule p c.pt q) at hf
  rw [complexExtModule_eq] at hf
  exact hf

end
end PiExponent.CoherentExtFiniteness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_NegativeTwistPresentations
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NegativeTwistPresentations
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport.TwistPresentations
variable {X : Scheme.{0}}

variable (L N : LineBundle X) {M : X.Modules} {n : ℕ}
    (s : ((moduleTwistFunctor L n).obj M).GeneratingSections)
    (e : moduleTensor X (L.pow n).sheaf N.sheaf ≅ structureSheaf X)

theorem middle_cohomology_finite (p : X ⟶ Spec (CommRingCat.of ℂ)) [hs : s.IsFiniteType]
    (q : ℕ)
    (hN : letI := Module.compHom (cohomology N.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf q)) :
    letI := Module.compHom
      (cohomology (moduleTensor X (SheafOfModules.free s.I) N.sheaf) q) (baseScalars p)
    FiniteDimensional ℂ (cohomology (moduleTensor X (SheafOfModules.free s.I) N.sheaf) q) := by
  let : Finite s.I := hs.finite
  let : Fintype s.I := Fintype.ofFinite s.I
  let : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts
  let B := ⨁ (fun _ : s.I => N.sheaf)
  let := Module.compHom (cohomology B q) (baseScalars p)
  let := Module.compHom
    (cohomology (moduleTensor X (SheafOfModules.free s.I) N.sheaf) q) (baseScalars p)
  have : FiniteDimensional ℂ (cohomology B q) :=
    CoherentExtFiniteness.cohomology_finite_of_biproduct p
      (biproduct.isBilimit (fun _ : s.I => N.sheaf)) q (fun _ => hN)
  exact Module.Finite.of_surjective (cohomologyIso p (middleIsoBiproduct L N s) q).symm.toLinearMap
    (cohomologyIso p (middleIsoBiproduct L N s) q).symm.surjective

def coherentFinitePresentation [IsLocallyNoetherian X] [M.IsFinitePresentation]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [s.IsFiniteType]
    (hN : ∀ q, letI := Module.compHom (cohomology N.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf q)) :
    CoherentExtFiniteness.CoherentFinitePresentation p M where
  kernel := kernel (presentationMap L N s e)
  kernel_coherent := kernel_isFinitePresentation L N s e
  middle := moduleTensor X (SheafOfModules.free s.I) N.sheaf
  left := kernel.ι (presentationMap L N s e)
  right := presentationMap L N s e
  comp_zero := kernel.condition (presentationMap L N s e)
  shortExact := presentation_shortExact L N s e
  middle_finite := fun q => middle_cohomology_finite L N s p q (hN q)

end
end PiExponent.NegativeTwistPresentations

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechHigher
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechHigher

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open CechOne
open scoped BigOperators

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

theorem connecting_cocycle (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) {q : ℕ}
    (hzero : ∀ (t : Fin (q + 1) → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (c : Cochain R U S.X₃ q) (hc : differential R U S.X₃ c = 0) :
    ∃ (b : Cochain R U S.X₂ q) (a : Cochain R U S.X₁ (q + 1)),
      map R U S.X₂ S.g b = c ∧
      map R U S.X₁ S.f a = differential R U S.X₂ b ∧
      differential R U S.X₁ a = 0 := by
  let : Mono S.f := hS.mono_f
  obtain ⟨b, hb⟩ := lift_cochain R U S hS q hzero c
  have hdb : map R U S.X₂ S.g (differential R U S.X₂ b) = 0 := by
    rw [map_differential, hb, hc]
  obtain ⟨a, ha⟩ := lift_kernel_cochain R U S hS _ hdb
  refine ⟨b, a, hb, ha, ?_⟩
  apply map_injective R U S.X₁ S.f
  rw [map_differential, ha, differential_squared, map_zero]

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

end
end PiExponent.GeometrySupport.CechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechLinear
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechLinear

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
open scoped BigOperators AlgebraicGeometry

universe v
variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
  {K : Type v} [Field K]

attribute [local instance] freeOpenHomAddCommGroup higherCochainAddCommGroup

attribute [local instance] freeOpenHomModule

variable (ρ : K →+* Γ(X, ⊤)) (M : X.Modules)

variable {M} {N P : X.Modules}

theorem mapCycles_boundary (g : M ⟶ N) (q : ℕ) (c : Cochain U ρ M q) :
    mapCycles U ρ g (q + 1) (boundaryToCycles U ρ M q c) =
      boundaryToCycles U ρ N q (mapLinear U ρ g q c) := by
  apply Subtype.ext
  exact mapLinear_differential U ρ g q c

end
end PiExponent.GeometrySupport.CechLinear

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechZero
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.CechZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
open scoped AlgebraicGeometry
open CechOne CechHigher

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

theorem sectionZero_restrict (c : CechHigher.Cochain R U M 0) (t : Fin 1 → J) :
    restrictHom R (iInf_le (fun j => U (t j)) 0) (sectionZero R U M c (t 0)) = c t := by
  simp only [sectionZero]
  erw [restrictHom_restrictHom]
  have ht : (fun _ : Fin 1 => t 0) = t := by
    funext k
    exact congrArg t (Subsingleton.elim 0 k)
  exact (restrict_cochain_congr R U M c ht
    ((iInf_le (fun j => U (t j)) 0).trans (le_iInf fun _ => le_rfl)) (le_refl _)).trans
    (restrictHom_refl R M (c t))

theorem sectionZero_injective : Function.Injective (sectionZero R U M) := by
  intro c d h
  funext t
  rw [← sectionZero_restrict R U M c t, ← sectionZero_restrict R U M d t, h]

theorem augmentation_injective (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) :
    Function.Injective (augmentation R U M V hUV) := by
  intro f g h
  apply hom_ext R U V hUV hcover M f g
  intro i
  have hi := congrArg (fun c => sectionZero R U M c i) h
  simpa only [sectionZero_augmentation] using hi

theorem augmentation_exists (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (c : CechHigher.Cochain R U M 0)
    (hc : differential R U M c = 0) :
    ∃ f : freeOpen R V ⟶ M, augmentation R U M V hUV f = c := by
  obtain ⟨f, hf⟩ := glue_zero_cocycle R U M V hUV hcover c hc
  refine ⟨f, sectionZero_injective R U M ?_⟩
  funext i
  rw [sectionZero_augmentation]
  exact hf i

theorem augmentation_comp (V : Opens X) (hUV : ∀ i, U i ≤ V)
    {N : SheafOfModules.{u} R} (f : freeOpen R V ⟶ M) (g : M ⟶ N) :
    augmentation R U N V hUV (f ≫ g) =
      CechHigher.map R U M g (augmentation R U M V hUV f) := by
  funext t
  exact restrictHom_comp R _ f g

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
open scoped AlgebraicGeometry

variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
  {K : Type*} [Field K] (ρ : K →+* Γ(X,⊤)) (M : X.Modules)

def sectionsEquiv (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) :
    letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
    letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
    (schemeFreeOpen V ⟶ M) ≃ₗ[K] CechLinear.cycles U ρ M 0 := by
  letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
  letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
  apply LinearEquiv.ofBijective (augmentationLinear U ρ M V hUV)
  constructor
  · intro f g h
    exact augmentation_injective X.ringCatSheaf U M V hUV hcover (congrArg Subtype.val h)
  · intro c
    obtain ⟨f, hf⟩ := augmentation_exists X.ringCatSheaf U M V hUV hcover c.val c.property
    exact ⟨f, Subtype.ext hf⟩

@[simp] theorem sectionsEquiv_val (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (f : schemeFreeOpen V ⟶ M) :
    (sectionsEquiv U ρ M V hUV hcover f).val =
      CechHigher.augmentation X.ringCatSheaf U M V hUV f := rfl

theorem sectionsEquiv_comp (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) {N : X.Modules}
    (f : schemeFreeOpen V ⟶ M) (g : M ⟶ N) :
    sectionsEquiv U ρ N V hUV hcover (f ≫ g) =
      CechLinear.mapCycles U ρ g 0 (sectionsEquiv U ρ M V hUV hcover f) := by
  apply Subtype.ext
  exact augmentation_comp X.ringCatSheaf U M V hUV f g

theorem sectionsEquiv_symm_mapCycles (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) {N : X.Modules} (g : M ⟶ N)
    (c : CechLinear.cycles U ρ M 0) :
    (sectionsEquiv U ρ N V hUV hcover).symm (CechLinear.mapCycles U ρ g 0 c) =
      (sectionsEquiv U ρ M V hUV hcover).symm c ≫ g := by
  apply (sectionsEquiv U ρ N V hUV hcover).injective
  rw [LinearEquiv.apply_symm_apply, sectionsEquiv_comp, LinearEquiv.apply_symm_apply]

end PiExponent.GeometrySupport.CechZero

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechExtFinite
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechExtFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Abelian
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
variable {K : Type*} [Field K] (ρ : K →+* Γ(X,⊤))

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

open CechLinear

def descent (S : ShortComplex X.Modules) [Injective S.X₂] (q : ℕ) :
    cycles U ρ S.X₁ (q+1) →ₗ[K] cycles U ρ S.X₃ q :=
  ((mapLinear U ρ S.g q).comp
    ((primitive U ρ S.X₂ q).comp (mapCycles U ρ S.f (q+1)))).codRestrict
      (cycles U ρ S.X₃ q) (fun a => by
        change differentialLinear U ρ S.X₃ q
          (mapLinear U ρ S.g q (primitive U ρ S.X₂ q (mapCycles U ρ S.f (q + 1) a))) = 0
        refine (mapLinear_differential U ρ S.g q _).symm.trans ?_
        refine (congrArg (mapLinear U ρ S.g (q + 1))
          (primitive_spec U ρ S.X₂ q (mapCycles U ρ S.f (q + 1) a))).trans ?_
        change mapLinear U ρ S.g (q + 1) (mapLinear U ρ S.f (q + 1) a.val) = 0
        rw [← LinearMap.comp_apply, ← mapLinear_comp, S.zero, mapLinear_zero]
        rfl)


lemma descent_lift (S : ShortComplex X.Modules) [Injective S.X₂] (q : ℕ)
    (a : cycles U ρ S.X₁ (q+1)) (b : Cochain U ρ S.X₂ q)
    (c : cycles U ρ S.X₃ q)
    (hdb : differentialLinear U ρ S.X₂ q b = mapLinear U ρ S.f (q+1) a.val)
    (hbg : mapLinear U ρ S.g q b = c.val) :
    ∃ z : cycles U ρ S.X₂ q, descent U ρ S q a - c = mapCycles U ρ S.g q z := by
  let β := primitive U ρ S.X₂ q (mapCycles U ρ S.f (q+1) a)
  have hβ : differentialLinear U ρ S.X₂ q β = mapLinear U ρ S.f (q+1) a.val :=
    primitive_spec U ρ S.X₂ q (mapCycles U ρ S.f (q+1) a)
  let z : cycles U ρ S.X₂ q := ⟨β-b, by
    change differentialLinear U ρ S.X₂ q (β-b) = 0
    rw [map_sub, hβ, hdb, sub_self]⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change mapLinear U ρ S.g q β - c.val = mapLinear U ρ S.g q (β-b)
  rw [map_sub, hbg]

def comparisonStep (A : X.Modules) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ)
    (F : cycles U ρ S.X₃ q →ₗ[K] ActualExt ρ A S.X₃ q) :
    cycles U ρ S.X₁ (q+1) →ₗ[K] ActualExt ρ A S.X₁ (q+1) :=
  (connecting ρ A S hS q).comp (F.comp (descent U ρ S q))

lemma comparisonStep_surjective (V : X.Opens) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ)
    (hlocal : LocallyAcyclic U S.X₁)
    (F : cycles U ρ S.X₃ q →ₗ[K] ActualExt ρ (schemeFreeOpen V) S.X₃ q)
    (hF : Function.Surjective F)
    (hmiddle : ∀ z : cycles U ρ S.X₂ q,
      connecting ρ (schemeFreeOpen V) S hS q (F (mapCycles U ρ S.g q z)) = 0) :
    Function.Surjective (comparisonStep U ρ (schemeFreeOpen V) S hS q F) := by
  intro x
  obtain ⟨y, hy⟩ := connecting_surjective ρ (schemeFreeOpen V) S hS q x
  obtain ⟨c, hc⟩ := hF y
  obtain ⟨b,a,hb,ha,had⟩ := CechHigher.connecting_cocycle X.ringCatSheaf U S hS
    (fun t z => hlocal q t 0 z) c.val c.property
  let a' : cycles U ρ S.X₁ (q+1) := ⟨a,had⟩
  obtain ⟨z,hz⟩ := descent_lift U ρ S q a' b c ha.symm hb
  let H := (connecting ρ (schemeFreeOpen V) S hS q).comp F
  have he : H (descent U ρ S q a') = H c := by
    apply sub_eq_zero.mp
    rw [← H.map_sub, hz]
    exact hmiddle z
  refine ⟨a', ?_⟩
  change H (descent U ρ S q a') = x
  rw [he]
  change connecting ρ (schemeFreeOpen V) S hS q (F c) = x
  rw [hc,hy]

lemma comparisonStep_boundary (A : X.Modules) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ)
    (F : cycles U ρ S.X₃ q →ₗ[K] ActualExt ρ A S.X₃ q)
    (hmiddle : ∀ z : cycles U ρ S.X₂ q,
      connecting ρ A S hS q (F (mapCycles U ρ S.g q z)) = 0)
    (b : Cochain U ρ S.X₁ q) :
    comparisonStep U ρ A S hS q F (boundaryToCycles U ρ S.X₁ q b) = 0 := by
  have hdb : differentialLinear U ρ S.X₂ q (mapLinear U ρ S.f q b) =
      mapLinear U ρ S.f (q+1) (boundaryToCycles U ρ S.X₁ q b).val :=
    (mapLinear_differential U ρ S.f q b).symm
  have hbg : mapLinear U ρ S.g q (mapLinear U ρ S.f q b) =
      (0 : cycles U ρ S.X₃ q).val := by
    rw [← LinearMap.comp_apply, ← mapLinear_comp, S.zero, mapLinear_zero]
    rfl
  obtain ⟨z,hz⟩ := descent_lift U ρ S q (boundaryToCycles U ρ S.X₁ q b)
    (mapLinear U ρ S.f q b) 0 hdb hbg
  rw [sub_zero] at hz
  change connecting ρ A S hS q (F (descent U ρ S q (boundaryToCycles U ρ S.X₁ q b))) = 0
  rw [hz]
  exact hmiddle z

def mkZeroLinear (A M : X.Modules) :
    letI : Module Γ(X,⊤) (A ⟶ M) := sheafHomModule X A M
    letI := Module.compHom (A ⟶ M) ρ
    (A ⟶ M) →ₗ[K] ActualExt ρ A M 0 := by
  letI : Module Γ(X,⊤) (A ⟶ M) := sheafHomModule X A M
  letI := Module.compHom (A ⟶ M) ρ
  refine {
    toFun := Ext.mk₀
    map_add' := Ext.mk₀_add
    map_smul' := ?_ }
  intro r f
  change Ext.mk₀ ((ρ r) • f) = (ρ r) • (show Ext.{1} A M 0 from Ext.mk₀ f)
  exact Ext.mk₀_smul (C := X.Modules) (R := Γ(X,⊤)) (X := A) (Y := M) (ρ r) f

@[simp] theorem mkZeroLinear_apply (A M : X.Modules) (f : A ⟶ M) :
    mkZeroLinear ρ A M f = Ext.mk₀ f := rfl

def zeroComparison (M : X.Modules) (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) :
    cycles U ρ M 0 →ₗ[K] ActualExt ρ (schemeFreeOpen V) M 0 := by
  letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
  letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
  exact (mkZeroLinear ρ (schemeFreeOpen V) M).comp
    (CechZero.sectionsEquiv U ρ M V hUV hcover).symm.toLinearMap

lemma zeroComparison_surjective (M : X.Modules) (V : X.Opens)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i) :
    Function.Surjective (zeroComparison U ρ M V hUV hcover) := by
  intro x
  obtain ⟨f,hf⟩ := (Ext.mk₀_bijective (schemeFreeOpen V) M).surjective x
  refine ⟨CechZero.sectionsEquiv U ρ M V hUV hcover f, ?_⟩
  change Ext.mk₀ ((CechZero.sectionsEquiv U ρ M V hUV hcover).symm
    (CechZero.sectionsEquiv U ρ M V hUV hcover f)) = x
  rw [LinearEquiv.symm_apply_apply,hf]

lemma zeroComparison_middle (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (z : cycles U ρ S.X₂ 0) :
    connecting ρ (schemeFreeOpen V) S hS 0
      (zeroComparison U ρ S.X₃ V hUV hcover (mapCycles U ρ S.g 0 z)) = 0 := by
  change Ext.comp (Ext.mk₀ ((CechZero.sectionsEquiv U ρ S.X₃ V hUV hcover).symm
    (mapCycles U ρ S.g 0 z))) hS.extClass rfl = 0
  rw [CechZero.sectionsEquiv_symm_mapCycles, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

theorem exists_comparison (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (n : ℕ) (M : X.Modules)
    (hlocal : LocallyAcyclic U M) :
    ∃ F : cycles U ρ M (n+1) →ₗ[K] ActualExt ρ (schemeFreeOpen V) M (n+1),
      Function.Surjective F ∧ ∀ b : Cochain U ρ M n, F (boundaryToCycles U ρ M n b) = 0 := by
  let : EnoughInjectives X.Modules := PiExponentSeshadri.ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let F := zeroComparison U ρ S.X₃ V hUV hcover
    have hmid := zeroComparison_middle U ρ V hUV hcover S hS
    exact ⟨comparisonStep U ρ (schemeFreeOpen V) S hS 0 F,
      comparisonStep_surjective U ρ V S hS 0 hlocal F
        (zeroComparison_surjective U ρ S.X₃ V hUV hcover) hmid,
      comparisonStep_boundary U ρ (schemeFreeOpen V) S hS 0 F hmid⟩
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨F,hF,hFb⟩ := ih S.X₃ (locallyAcyclic_quotient U S hS hlocal)
    have hmid (z : cycles U ρ S.X₂ (n+1)) :
        connecting ρ (schemeFreeOpen V) S hS (n+1)
          (F (mapCycles U ρ S.g (n+1) z)) = 0 := by
      obtain ⟨b,rfl⟩ := boundaryToCycles_surjective U ρ S.X₂ n z
      rw [mapCycles_boundary,hFb,map_zero]
    exact ⟨comparisonStep U ρ (schemeFreeOpen V) S hS (n+1) F,
      comparisonStep_surjective U ρ V S hS (n+1) hlocal F hF hmid,
      comparisonStep_boundary U ρ (schemeFreeOpen V) S hS (n+1) F hmid⟩

def sourceIso {A B : X.Modules} (e : A ≅ B) (M : X.Modules) (q : ℕ) :
    ActualExt ρ A M q ≃ₗ[K] ActualExt ρ B M q where
  toFun x := (Ext.mk₀ e.inv).comp x (zero_add q)
  invFun x := (Ext.mk₀ e.hom).comp x (zero_add q)
  left_inv x := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp (show Ext.{1} A M q from x) (zero_add q)) (zero_add q) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  right_inv x := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp (show Ext.{1} B M q from x) (zero_add q)) (zero_add q) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  map_add' x y := Ext.comp_add _ x y _
  map_smul' a x := by
    change (Ext.mk₀ e.inv).comp ((ρ a) • (show Ext.{1} A M q from x)) _ =
      (ρ a) • (Ext.mk₀ e.inv).comp x _
    exact Ext.comp_smul (C := X.Modules) (R := Γ(X, ⊤)) (Ext.mk₀ e.inv) x (zero_add q) (ρ a)

theorem affine_exists_comparison [IsNoetherian X] (hcover : ⊤ ≤ ⨆ i, U i)
    (M : X.Modules) [M.IsQuasicoherent]
    (haffine : ∀ (q : ℕ) (t : Fin (q+1) → J), IsAffineOpen (CechHigher.intersection U t))
    (n : ℕ) :
    ∃ F : cycles U ρ M (n+1) →ₗ[K] ActualExt ρ (structureSheaf X) M (n+1),
      Function.Surjective F ∧ ∀ b : Cochain U ρ M n, F (boundaryToCycles U ρ M n b) = 0 := by
  obtain ⟨F,hF,hFb⟩ := exists_comparison U ρ ⊤ (fun _ => le_top) hcover n M
    (fun q t k y => PiExponentSeshadri.FiniteCoverCohomology.affine_open_ext_zero
      (CechHigher.intersection U t) (haffine q t) M k y)
  let e := sourceIso (X := X) ρ (A := schemeFreeOpen ⊤) (B := structureSheaf X)
    (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf) M (n+1)
  refine ⟨e.toLinearMap.comp F, e.surjective.comp hF, ?_⟩
  intro b
  change e (F (boundaryToCycles U ρ M n b)) = 0
  rw [hFb,map_zero]

end
end PiExponent.GeometrySupport.CechExtFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_LaurentCechFinite
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.LaurentCechFinite
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open ProjectiveTwistCech

variable {X : Scheme.{0}} {ι K : Type} [Fintype ι] [Field K]
  {U : ι → X.Opens} {M : X.Modules} {d : ℤ}

attribute [local instance] freeOpenHomAddCommGroup

local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen_rba2938_1 (V : X.Opens) (N : X.Modules) :
    Module Γ(X, ⊤) (PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V ⟶ N) :=
  sheafHomModule X _ N
variable (ρ : K →+* Γ(X, ⊤)) (P : LaurentCechPresentation (K := K) U M d)
  (hlinear : ∀ q t (r : K) b,
    P.coefficient q t ((ρ r) • b) = r • P.coefficient q t b)

def cochainMap (q : ℕ) :
    CechLinear.Cochain U ρ M q →ₗ[K] ProjectiveMonomialCohomology.regularCochains (ι := ι) (K := K) d q where
  toFun c := ⟨P.toLaurent c, fun t => P.regular q t (c t)⟩
  map_add' c e := by
    apply Subtype.ext
    funext t
    exact map_add (P.coefficient q t) (c t) (e t)
  map_smul' r c := by
    apply Subtype.ext
    funext t
    exact hlinear q t r (c t)

theorem cochainMap_injective (q : ℕ) :
    Function.Injective (cochainMap ρ P hlinear q) := by
  intro c e h
  funext t
  apply P.injective q t
  exact congrFun (congrArg Subtype.val h) t

theorem cochainMap_surjective (q : ℕ) :
    Function.Surjective (cochainMap ρ P hlinear q) := by
  intro c
  choose b hb using fun t => P.surjective q t (c.val t) (c.property t)
  exact ⟨b, Subtype.ext (funext hb)⟩

def cochainEquiv (q : ℕ) :
    CechLinear.Cochain U ρ M q ≃ₗ[K] ProjectiveMonomialCohomology.regularCochains (ι := ι) (K := K) d q :=
  LinearEquiv.ofBijective (cochainMap ρ P hlinear q)
    ⟨cochainMap_injective ρ P hlinear q, cochainMap_surjective ρ P hlinear q⟩

def cyclesMap (q : ℕ) :
    CechLinear.cycles U ρ M q →ₗ[K] ProjectiveMonomialCohomology.cycles (ι := ι) (K := K) d q where
  toFun c := ⟨P.toLaurent c.val, fun t => P.regular q t _, by
    change ProjectiveMonomialCechHigher.differential (P.toLaurent c.val) = 0
    have hc : CechLinear.differentialLinear U ρ M q c.val = 0 := c.property
    refine (P.toLaurent_differential c.val).symm.trans
      ((congrArg (fun c : CechLinear.Cochain U ρ M (q + 1) => P.toLaurent c) hc).trans ?_)
    funext t
    exact map_zero _⟩
  map_add' c e := by
    apply Subtype.ext
    funext t
    exact map_add (P.coefficient q t) (c.val t) (e.val t)
  map_smul' r c := by
    apply Subtype.ext
    funext t
    exact hlinear q t r (c.val t)

theorem cyclesMap_injective (q : ℕ) :
    Function.Injective (cyclesMap ρ P hlinear q) := by
  intro c e h
  apply Subtype.ext
  funext t
  apply P.injective q t
  exact congrFun (congrArg Subtype.val h) t

theorem cyclesMap_surjective (q : ℕ) :
    Function.Surjective (cyclesMap ρ P hlinear q) := by
  intro c
  choose b hb using fun t => P.surjective q t (c.val t) (c.property.1 t)
  have he : P.toLaurent b = c.val := funext hb
  have hc : CechLinear.differentialLinear U ρ M q b = 0 := by
    funext t
    apply P.injective (q + 1) t
    have h := P.toLaurent_differential b
    have hc : ProjectiveMonomialCechHigher.differential c.val = 0 := c.property.2
    rw [he, hc] at h
    exact (congrFun h t).trans (map_zero (P.coefficient (q + 1) t)).symm
  exact ⟨⟨b, hc⟩, Subtype.ext he⟩

def cyclesEquiv (q : ℕ) :
    CechLinear.cycles U ρ M q ≃ₗ[K] ProjectiveMonomialCohomology.cycles (ι := ι) (K := K) d q :=
  LinearEquiv.ofBijective (cyclesMap ρ P hlinear q)
    ⟨cyclesMap_injective ρ P hlinear q, cyclesMap_surjective ρ P hlinear q⟩

theorem cyclesEquiv_boundary (q : ℕ) (c : CechLinear.Cochain U ρ M q) :
    cyclesEquiv ρ P hlinear (q + 1) (CechLinear.boundaryToCycles U ρ M q c) =
      ProjectiveMonomialCohomology.boundaryMap d q (cochainEquiv ρ P hlinear q c) := by
  apply Subtype.ext
  exact P.toLaurent_differential c

theorem cyclesEquiv_symm_boundary (q : ℕ) (b : ProjectiveMonomialCohomology.regularCochains (ι := ι) (K := K) d q) :
    (cyclesEquiv ρ P hlinear (q + 1)).symm (ProjectiveMonomialCohomology.boundaryMap d q b) =
      CechLinear.boundaryToCycles U ρ M q ((cochainEquiv ρ P hlinear q).symm b) := by
  apply (cyclesEquiv ρ P hlinear (q + 1)).injective
  rw [LinearEquiv.apply_symm_apply, cyclesEquiv_boundary, LinearEquiv.apply_symm_apply]

include P hlinear in

theorem degreeZero_finite : Module.Finite K (CechLinear.cycles U ρ M 0) := by
  let : Module.Finite K (ProjectiveMonomialCohomology.cycles (ι := ι) (K := K) d 0) :=
    ProjectiveMonomialCohomology.degreeZero_finite d
  exact Module.Finite.of_surjective (cyclesEquiv ρ P hlinear 0).symm.toLinearMap
    (cyclesEquiv ρ P hlinear 0).symm.surjective

include P hlinear in

theorem finite_of_comparison (q : ℕ) {V : Type*} [AddCommGroup V] [Module K V]
    (f : CechLinear.cycles U ρ M (q + 1) →ₗ[K] V)
    (hboundary : ∀ b, f (CechLinear.boundaryToCycles U ρ M q b) = 0)
    (hsurj : Function.Surjective f) : Module.Finite K V := by
  let g := f.comp (cyclesEquiv ρ P hlinear (q + 1)).symm.toLinearMap
  apply ProjectiveMonomialCohomology.finite_of_boundary_annihilating_surjective d q g
  · intro b
    change f ((cyclesEquiv ρ P hlinear (q + 1)).symm
      (ProjectiveMonomialCohomology.boundaryMap d q b)) = 0
    rw [cyclesEquiv_symm_boundary]
    exact hboundary _
  · exact hsurj.comp (cyclesEquiv ρ P hlinear (q + 1)).symm.surjective

end
end PiExponent.GeometrySupport.LaurentCechFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_LaurentExtFinite
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ActualLaurentExtFinite
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {ι K : Type} [Fintype ι] [Field K]
variable {U : ι → X.Opens} {M : X.Modules} {d : ℤ}
variable (ρ : K →+* Γ(X,⊤)) (P : ProjectiveTwistCech.LaurentCechPresentation (K := K) U M d)
variable (hlinear : ∀ q t (r : K) b,
  P.coefficient q t ((ρ r) • b) = r • P.coefficient q t b)
include P hlinear

theorem actualExt_zero_finite (hcover : ⊤ ≤ ⨆ i, U i) :
    Module.Finite K (CechExtFinite.ActualExt ρ (structureSheaf X) M 0) := by
  let := LaurentCechFinite.degreeZero_finite ρ P hlinear
  let F := CechExtFinite.zeroComparison U ρ M ⊤ (fun _ => le_top) hcover
  let e := CechExtFinite.sourceIso (X := X) ρ
    (A := schemeFreeOpen ⊤) (B := structureSheaf X)
    (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf) M 0
  exact Module.Finite.of_surjective (e.toLinearMap.comp F)
    (e.surjective.comp (CechExtFinite.zeroComparison_surjective U ρ M ⊤
      (fun _ => le_top) hcover))

theorem actualExt_succ_finite [IsNoetherian X] [M.IsQuasicoherent]
    (hcover : ⊤ ≤ ⨆ i, U i)
    (haffine : ∀ (q : ℕ) (t : Fin (q+1) → ι),
      IsAffineOpen (CechHigher.intersection U t)) (q : ℕ) :
    Module.Finite K (CechExtFinite.ActualExt ρ (structureSheaf X) M (q+1)) := by
  obtain ⟨F, hF, hboundary⟩ :=
    CechExtFinite.affine_exists_comparison U ρ hcover M haffine q
  exact LaurentCechFinite.finite_of_comparison ρ P hlinear q F hboundary hF

theorem actualExt_finite [IsNoetherian X] [M.IsQuasicoherent]
    (hcover : ⊤ ≤ ⨆ i, U i)
    (haffine : ∀ (q : ℕ) (t : Fin (q+1) → ι),
      IsAffineOpen (CechHigher.intersection U t)) (q : ℕ) :
    Module.Finite K (CechExtFinite.ActualExt ρ (structureSheaf X) M q) := by
  cases q with
  | zero => exact actualExt_zero_finite ρ P hlinear hcover
  | succ q => exact actualExt_succ_finite ρ P hlinear hcover haffine q

theorem cohomology_finite [IsNoetherian X] [M.IsQuasicoherent]
    (hcover : ⊤ ≤ ⨆ i, U i)
    (haffine : ∀ (q : ℕ) (t : Fin (q+1) → ι),
      IsAffineOpen (CechHigher.intersection U t)) (q : ℕ) :
    letI := Module.compHom (cohomology M q) ρ
    Module.Finite K (cohomology M q) := by
  exact actualExt_finite ρ P hlinear hcover haffine q

end
end PiExponent.GeometrySupport.ActualLaurentExtFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveFramedCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (N : X.Modules)
variable (e : ∀ i, N.restrict (SectionOpens.isoOpen (s i)).ι ≅
  structureSheaf (SectionOpens.isoOpen (s i)).toScheme) (d : ℤ)

lemma coordinateFramedOverlap_injective (i : σ) (a : Finset (ChartVariables i)) :
    Function.Injective (coordinateFramedOverlap M s k hc f hf N e d i a) :=
  framedLaurentOverlap_injective _ _ _ _ _ _ _

lemma coordinateFramedOverlap_regular (i : σ) (a : Finset (ChartVariables i))
    (b : schemeFreeOpen_p0 (coordinateFiniteOpen M s i a) ⟶ N) :
    RegularOn ({i} ∪ Subtype.val '' (a : Set (ChartVariables i)))
      (coordinateFramedOverlap M s k hc f hf N e d i a b) :=
  framedLaurentOverlap_regular _ _ _ _ _ _ _ b

attribute [local irreducible] coordinateFramedOverlap

lemma coordinateFramedTuple_injective (q : ℕ) (t : Fin (q + 1) → σ) :
    Function.Injective (coordinateFramedTuple M s k hc f hf N e d q t) := by
  intro b c h
  apply (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)).injective
  apply coordinateFramedOverlap_injective M s k hc f hf N e d (t 0) (tupleVariables t 0)
  exact h

lemma coordinateFramedTuple_regular (q : ℕ) (t : Fin (q + 1) → σ)
    (b : schemeFreeOpen_p0
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶ N) :
    RegularOn (Set.range t) (coordinateFramedTuple M s k hc f hf N e d q t b) := by
  have h := coordinateFramedOverlap_regular M s k hc f hf N e d (t 0) (tupleVariables t 0)
    (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0) b)
  change RegularOn (Set.range t) ((coordinateFramedOverlap M s k hc f hf N e d (t 0)
    (tupleVariables t 0)) ((freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)) b))
  simpa only [tupleVariables_support] using h

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveNegativeFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.InverseFrames
variable {X : Scheme} {M N : X.Modules}

def negativeCoordinateFrame (n : ℕ)
    (E : moduleTensor X (modulePow X M n) N ≅ O X) (si : O X ⟶ M) :
    N.restrict (SectionOpens.isoOpen si).ι ≅ O (SectionOpens.isoOpen si).toScheme :=
  inverseOpenFrame E _ (coordinatePowerFrame si n)

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CohomologyFinite
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CohomologyFiniteness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X Y : Scheme.{0}}

def CohomologyFinite (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (q : ℕ) : Prop :=
  letI := Module.compHom (cohomology M q) (baseScalars p)
  FiniteDimensional ℂ (cohomology M q)

theorem finiteDimensional (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (q : ℕ)
    (h : CohomologyFinite p M q) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := h

theorem closedPushforward_finite (i : X ⟶ Y) [IsClosedImmersion i]
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (q : ℕ)
    (h : CohomologyFinite p ((Scheme.Modules.pushforward i).obj M) q) :
    CohomologyFinite (i ≫ p) M q :=
  ClosedImmersionSerreTransfer.finiteDimensional_of_pushforward i p M q h

end
end PiExponent.CohomologyFiniteness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_TensorIdealInclusion
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

def tensorInclusion (J M : LineBundle X) (ι : J.sheaf ⟶ O X) :
    (J.tensor M).sheaf ⟶ M.sheaf :=
  moduleTensorMap ι (𝟙 M.sheaf) ≫ (moduleTensorUnit M.sheaf).hom

end
end PiExponentSeshadri.Geometry

end OAI
end


