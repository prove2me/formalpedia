-- Prove2me | Definitions.Def_OAIQ068A016
-- name    : OAIQ068A016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:46:53.529119+00:00
-- url     : https://prove2.me/theorems/72a1d40f-5613-40fb-9992-656051543642
-- title:
--   Definitions bundle OAIQ068A016 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 75 declarations of OpenAI's Lean: 12 definitions, 1 instance and 62 theorems. The definitions and types are `OAI.PiExponent.BranchContactIdeal.contact`, `OAI.PiExponent.CurveNormalizationModel.parameterChartFractionRing`, `OAI.PiExponent.DeterminantContradiction.FixedData`, `OAI.PiExponent.GeneratorsSectionCover.freeProjection`, `OAI.PiExponent.GeneratorsSectionCover.schemeInclusion`, `OAI.PiExponent.JetProductLocalization.residueAlgHom`, `OAI.PiExponent.LocalSectionOrder.localCoefficient`, `OAI.PiExponent.LocalSectionOrder.localFrameChange`, `OAI.PiExponent.LocalSectionOrder.sectionOrder`, `OAI.PiExponent.WeightedSectionOrder.coordinateFrame`, `OAI.PiExponentSeshadri.IdealModule.closedMap`, `OAI.PiExponentSeshadri.IdealModule.multiplyToNextPower`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_ExceptionalCurveDegree`, `PiExponent_Analysis_FormalLogTailOrder`, `PiExponent_Analysis_LogarithmicContactIdeal`, `PiExponent_Approximation_DeterminantContradiction`, `PiExponent_Approximation_GeneratorsSectionCover`, `PiExponent_Approximation_WeightedSectionOrder`, `PiExponent_Geometry_CurveGlobalMonomialLocal`, `PiExponent_Geometry_CurveLocalOrder`, `PiExponent_Geometry_CurveModelFieldEmbedding`, `PiExponent_Geometry_FiniteCurveZeros`, `PiExponent_Geometry_PrincipalCartierSequence`, `PiExponent_Geometry_ProjectiveEmbeddingCharts`, `PiExponent_Geometry_WeightedCurveDegree`, `PiExponent_Jets_BranchContact`, `PiExponent_Jets_BranchContactIdeal`, `PiExponent_Jets_CompactJetIdeal`, `PiExponent_Jets_CompactJetPolynomial`, `PiExponent_Jets_CompactLogJetIdeal`, `PiExponent_Jets_DVRBranch`, `PiExponent_Jets_DVRBranchOrder`, `PiExponent_Jets_FormalBranchContact`, `PiExponent_Jets_FormalBranchCoordinates`, `PiExponent_Jets_FormalBranchEvaluation`, `PiExponent_Jets_IntrinsicLength`, `PiExponent_Jets_JetProductLocalization`, `PiExponent_LocalAlgebra_IdealModule`, `PiExponent_LocalAlgebra_IdealPowerAnnihilator`, `PiExponent_LocalAlgebra_IdealPowerFiltration`, `PiExponent_LocalAlgebra_LocalSectionOrder`.
--
--   **Imports.** It imports the bundles `OAIQ068A000`, `OAIQ068A001`, `OAIQ068A002`, `OAIQ068A003`, `OAIQ068A005` and `OAIQ068A006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A024`, `OAIQ068A025`, `OAIQ068A026` and `OAIQ068A027`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A000
import Definitions.Def_OAIQ068A001
import Definitions.Def_OAIQ068A002
import Definitions.Def_OAIQ068A003
import Definitions.Def_OAIQ068A005
import Definitions.Def_OAIQ068A006

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealModule
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.IdealModule

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

lemma equationToIdeal_app (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0)
    (U : X.Opens) (a : Γ(X, U)) :
    (inclusion f).val.app (op U) ((equationToIdeal f r hr).val.app (op U) a) =
      X.presheaf.map (homOfLE le_top).op r * a :=
  congrArg (fun g => g.val.app (op U) a) (equationToIdeal_inclusion f r hr)

lemma isIso_equationToIdeal (f : Y ⟶ X) [QuasiCompact f]
    (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0)
    (hprincipal : ∀ U : X.affineOpens,
      f.ker.ideal U = Ideal.span {X.presheaf.map (homOfLE le_top).op r})
    (hregular : ∀ U : X.affineOpens,
      IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r)) :
    IsIso (equationToIdeal f r hr) := by
  apply isIso_of_affine_app
  intro U
  have hinj : Function.Injective ((inclusion f).val.app (op U.1)) := by
    let : Mono (inclusion f).val :=
      inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map (inclusion f)))
    exact PresheafOfModules.injective_of_mono (inclusion f).val (op U.1)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hregular U
    have he := congrArg ((inclusion f).val.app (op U.1)) hab
    change (inclusion f).val.app (op U.1) ((equationToIdeal f r hr).val.app (op U.1) a) =
      (inclusion f).val.app (op U.1) ((equationToIdeal f r hr).val.app (op U.1) b) at he
    exact (equationToIdeal_app f r hr U.1 a).symm.trans
      (he.trans (equationToIdeal_app f r hr U.1 b))
  · intro y
    have hy : (inclusion f).val.app (op U.1) y ∈ f.ker.ideal U := by
      rw [← image_eq_ideal f U]
      exact ⟨y, rfl⟩
    rw [hprincipal U] at hy
    have hd : X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r ∣
        (show Γ(X, U.1) from (inclusion f).val.app (op U.1) y) :=
      Ideal.mem_span_singleton.mp hy
    obtain ⟨a, ha⟩ := hd
    refine ⟨a, hinj ?_⟩
    exact (equationToIdeal_app f r hr U.1 a).trans ha.symm

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma structureMap_epi (f : X ⟶ Y) [IsClosedImmersion f] : Epi (structureMap f) := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have hloc : TopCat.Presheaf.IsLocallySurjective (F.map (structureMap f)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t y hy
    obtain ⟨_,⟨V,hA,rfl⟩,hyV,hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    obtain ⟨s,hs⟩ := f.app_surjective V hA
      (((F.obj ((Scheme.Modules.pushforward f).obj (unit X))).obj.map
        (homOfLE hVU).op) t)
    exact ⟨V,hVU,⟨s,hs⟩,hyV⟩
  let : Epi (F.map (structureMap f)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc
  exact F.epi_of_epi_map inferInstance

end PiExponentSeshadri.IdealModule

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveEmbeddingCharts
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

universe u

namespace Projective
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
variable {K σ R : Type u} [CommRing K] [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma normalized_evalAway_surjective (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) (h : Function.Surjective (eval₂Hom k a)) :
    Function.Surjective (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a)
      (X i) (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))) := by
  let F := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a)
    (X i) (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
  have hC (r : K) : C r ∈ homogeneousSubmodule σ K (0 • 1) := by simp
  have hX (j : σ) : X j ∈ homogeneousSubmodule σ K (1 • 1) := by
    simpa using isHomogeneous_X K j
  let c : K →+* Away (homogeneousSubmodule σ K) (X i) :=
    (HomogeneousLocalization.fromZeroRingHom _ _).comp
      { toFun := fun r => ⟨C r, isHomogeneous_C _ _⟩
        map_one' := Subtype.ext C_1
        map_mul' := fun _ _ => Subtype.ext C_mul
        map_zero' := Subtype.ext C_0
        map_add' := fun _ _ => Subtype.ext C_add }
  let b (j : σ) := Away.mk _ (isHomogeneous_X K i) 1 (X j) (hX j)
  have hc (r : K) : F (c r) = k r := by
    change F (Away.mk _ (isHomogeneous_X K i) 0 (C r) (hC r)) = k r
    have H := evalAway_mk_clear (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (X i)) by simpa only [eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) 0 (C r) (hC r)
    simpa only [F, eval₂Hom_C, eval₂Hom_X', pow_zero, mul_one] using H
  have hb (j : σ) : F (b j) = a j := by
    have H := evalAway_mk_clear (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (X i)) by simpa only [eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (X j) (hX j)
    simpa only [F, b, eval₂Hom_X', hi, one_pow, mul_one] using H
  have H : F.comp (eval₂Hom c b) = eval₂Hom k a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, eval₂Hom_C] using hc r
    · intro j
      simpa only [RingHom.comp_apply, eval₂Hom_X'] using hb j
  intro r
  obtain ⟨p, hp⟩ := h r
  exact ⟨eval₂Hom c b p, (RingHom.congr_fun H p).trans hp⟩

lemma normalized_coordinates_closed {X : Scheme.{u}} [IsAffine X]
    (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1)
    (h : Function.Surjective (eval₂Hom k a)) :
    IsClosedImmersion (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
        (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(X, ⊤))))))) := by
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a)
      (MvPolynomial.X i) (by simpa only [eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : Γ(X, ⊤))))))
    (normalized_evalAway_surjective k a i hi h)
  infer_instance

end Projective

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_IntrinsicLength
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

variable [IsLocalRing A]

theorem length_eq_coefficient_length (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    ∀ [Module K M] [IsScalarTower K A M], Module.length A M = Module.length K M := by
  induction hM with
  | of_subsingleton =>
    intro _ _
    simp only [Module.length_eq_zero]
  | @of_simple_quotient M _ _ N hsimple hN ih =>
    intro _ _
    have : IsSimpleModule K (M ⧸ N) := simple_over_coefficient_field ε hε
    have hexact : Function.Exact N.subtype N.mkQ := by
      rw [LinearMap.exact_iff, Submodule.range_subtype, Submodule.ker_mkQ]
    have hA := Module.length_eq_add_of_exact N.subtype N.mkQ
      (Submodule.subtype_injective N) (Submodule.mkQ_surjective N) hexact
    have hK := Module.length_eq_add_of_exact (N.subtype.restrictScalars K)
      (N.mkQ.restrictScalars K) (Submodule.subtype_injective N)
      (Submodule.mkQ_surjective N) hexact
    calc
      Module.length A M = Module.length A N + Module.length A (M ⧸ N) := hA
      _ = Module.length K N + Module.length K (M ⧸ N) := by
        rw [ih, Module.length_eq_one A (M ⧸ N), Module.length_eq_one K (M ⧸ N)]
      _ = Module.length K M := hK.symm

theorem module_length_eq_finrank_of_augmentation (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [Module.Finite K M] :
    Module.length A M = Module.finrank K M := by
  have : IsNoetherian A M := isNoetherian_of_tower K inferInstance
  have : IsArtinian A M := isArtinian_of_tower K inferInstance
  have hM : IsFiniteLength A M := isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨inferInstance, inferInstance⟩
  rw [length_eq_coefficient_length ε hε hM, Module.length_eq_finrank]

theorem ring_length_eq_finrank_of_augmentation [Module.Finite K A] (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k) :
    Module.length A A = Module.finrank K A :=
  module_length_eq_finrank_of_augmentation ε hε

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_WeightedCurveDegree
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.WeightedCurveDegree

theorem weightedPole_nonneg {ι : Type*} [Fintype ι] (w z : ι → ℚ) :
    0 ≤ weightedPole w z := by
  exact Finset.le_sup' (fun i : Option ι => i.elim 0 (fun j => -z j / w j))
    (Finset.mem_univ (none : Option ι))

theorem div_le_weightedPole {ι : Type*} [Fintype ι] (w z : ι → ℚ) (i : ι) :
    -z i / w i ≤ weightedPole w z := by
  exact Finset.le_sup' (fun o : Option ι => o.elim 0 (fun j => -z j / w j))
    (Finset.mem_univ (some i))

theorem monomial_pole_le {ι : Type*} [Fintype ι]
    (w z : ι → ℚ) (hw : ∀ i, 0 < w i) (a : ι → ℕ) {R : ℚ}
    (ha : (∑ i, w i * (a i : ℚ)) ≤ R) :
    -(∑ i, (a i : ℚ) * z i) ≤ R * weightedPole w z := by
  have hcoord (i : ι) : -z i ≤ w i * weightedPole w z := by
    have h := (div_le_iff₀ (hw i)).mp (div_le_weightedPole w z i)
    simpa [mul_comm] using h
  calc
    _ = ∑ i, (a i : ℚ) * (-z i) := by simp [Finset.sum_neg_distrib]
    _ ≤ ∑ i, (a i : ℚ) * (w i * weightedPole w z) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hcoord i) (Nat.cast_nonneg _)
    _ = (∑ i, w i * (a i : ℚ)) * weightedPole w z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ R * weightedPole w z :=
      mul_le_mul_of_nonneg_right ha (weightedPole_nonneg w z)

end PiExponent.WeightedCurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveLocalOrder
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators nonZeroDivisors
open IsLocalRing IsDiscreteValuationRing

namespace PiExponent.CurveLocalOrder

theorem fraction_order_eq_principal_colength
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {a : A} (ha : a ≠ 0) :
    fractionAddValuation A K (algebraMap A K a) =
      enatToIntegerOrder (Module.length A (A ⧸ Ideal.span {a})) := by
  rw [fractionAddValuation_algebraMap, localAddValuation_apply,
    length_quotient_span_eq_addVal ha]

theorem integerOrder_field_image_eq_length
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {a : A} (ha : a ≠ 0) :
    WeightedCurveDegree.integerOrder (fractionAddValuation A K)
      (Units.mk0 (algebraMap A K a) ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha)) =
        ((Module.length A (A ⧸ Ideal.span {a})).toNat : ℤ) := by
  apply WithTop.coe_injective
  rw [WeightedCurveDegree.coe_integerOrder]
  change fractionAddValuation A K (algebraMap A K a) = _
  rw [fraction_order_eq_principal_colength ha]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (principal_colength_ne_top ha)
  rw [← hn]
  simp

end PiExponent.CurveLocalOrder

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_BranchContact
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BranchContact

variable {ι : Type*} [Fintype ι]

theorem contact_le (v : ι → ℚ) (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (i : ι) (hi : a i ≠ 0) :
    contact v a hne ≤ ((a i).order.toNat : ℚ) / v i :=
  Finset.inf'_le _ ((mem_active a i).mpr hi)

theorem exists_attains (v : ι → ℚ) (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) :
    ∃ i, a i ≠ 0 ∧ contact v a hne = ((a i).order.toNat : ℚ) / v i := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' (active_nonempty a hne)
    (fun i => ((a i).order.toNat : ℚ) / v i)
  exact ⟨i,(mem_active a i).mp hi,he⟩

theorem contact_pos (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (hc : ∀ i, PowerSeries.constantCoeff (a i) = 0) : 0 < contact v a hne := by
  obtain ⟨i,hi,he⟩ := exists_attains v a hne
  rw [he]
  apply div_pos _ (hv i)
  have horder := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (hc i)
  rw [← PowerSeries.coe_toNat_order hi] at horder
  have hnat : 1 ≤ (a i).order.toNat := by exact_mod_cast horder
  exact_mod_cast (show 0 < (a i).order.toNat by omega)

theorem contact_bound (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) (i : ι) (k : ℕ)
    (hk : (a i).order = (k : ℕ∞)) : contact v a hne * v i ≤ (k : ℚ) := by
  have hi : a i ≠ 0 := by
    intro hz
    simp [hz] at hk
  have hnat : (a i).order.toNat = k := by simpa using congrArg ENat.toNat hk
  exact hnat ▸ (le_div_iff₀ (hv i)).mp (contact_le v a hne i hi)

theorem exists_attaining_add (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a t : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ht : ∀ i (k : ℕ), (t i).order = (k : ℕ∞) → contact v a hne * v i < (k : ℚ)) :
    ∃ i, a i + t i ≠ 0 ∧ (a i + t i).order = (a i).order ∧
      contact v a hne = ((a i + t i).order.toNat : ℚ) / v i := by
  obtain ⟨i,hi,he⟩ := exists_attains v a hne
  have heq : contact v a hne * v i = ((a i).order.toNat : ℚ) :=
    (eq_div_iff (ne_of_gt (hv i))).mp he
  have hord : (a i).order < (t i).order := by
    by_cases hzero : t i = 0
    · simpa [hzero] using PowerSeries.order_finite_iff_ne_zero.mpr hi
    · have ht' := ht i (t i).order.toNat (PowerSeries.coe_toNat_order hzero).symm
      rw [heq] at ht'
      have hnat : (a i).order.toNat < (t i).order.toNat := by exact_mod_cast ht'
      rw [← PowerSeries.coe_toNat_order hi, ← PowerSeries.coe_toNat_order hzero]
      exact_mod_cast hnat
  have hsum : (a i + t i).order = (a i).order := by
    rw [PowerSeries.order_add_of_order_ne _ _ hord.ne, inf_eq_left.mpr hord.le]
  have hne' : a i + t i ≠ 0 := by
    intro hz
    have hh := PowerSeries.order_eq_top.mpr hz
    rw [hsum] at hh
    exact hi (PowerSeries.order_eq_top.mp hh)
  exact ⟨i,hne',hsum,hsum ▸ he⟩

theorem add_not_all_zero (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a t : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ht : ∀ i (k : ℕ), (t i).order = (k : ℕ∞) → contact v a hne * v i < (k : ℚ)) :
    ∃ i, a i + t i ≠ 0 := by
  obtain ⟨i,hi,_⟩ := exists_attaining_add v hv a t hne ht
  exact ⟨i,hi⟩

end PiExponent.BranchContact

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_DVRBranchOrder
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.DVRBranchOrder

variable {A C : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field C]

variable [Algebra C A]

theorem algHom_order_eq_addVal (φ : A →ₐ[C] PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) (a : A) :
    PowerSeries.order (φ a) = IsDiscreteValuationRing.addVal A a :=
  order_eq_addVal φ.toRingHom π hπ hφπ a

end PiExponent.DVRBranchOrder
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_DVRBranch
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.DVRBranch
open CurveLocalOrder

variable (C A : Type*) [Field C] [IsAlgClosed C] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra C A]
    [Algebra.IsIntegral C (IsLocalRing.ResidueField A)]

theorem expansion_order (a : A) :
    PowerSeries.order (expansion C A a) = IsDiscreteValuationRing.addVal A a :=
  DVRBranchOrder.algHom_order_eq_addVal (expansion C A) (uniformizer A)
    (uniformizer_irreducible A) (expansion_uniformizer C A) a

end PiExponent.DVRBranch

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalBranchEvaluation
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.FormalBranchEvaluation
open MvPowerSeries
open FormalLogJet FormalLogTruncation

theorem branchCoordinates_hasSubst {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i) :
    HasSubst (branchCoordinates c y x) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  have ht : MvPowerSeries.constantCoeff (y-1) = 0 := by
    simpa only [map_sub, map_one, PowerSeries.constantCoeff_eq, sub_eq_zero] using hy
  cases i using Fin.cases with
  | zero => exact ht
  | succ i =>
    change MvPowerSeries.constantCoeff
      (x i - PowerSeries.C (c i) - PowerSeries.subst (y-1) (PowerSeries.log ℂ)) = 0
    rw [map_sub, PowerSeries.constantCoeff_subst_eq_zero ht _ (PowerSeries.constantCoeff_log),
      sub_zero, map_sub]
    change PowerSeries.constantCoeff (x i) - PowerSeries.constantCoeff (PowerSeries.C (c i)) = 0
    rw [hx i, PowerSeries.constantCoeff_C, sub_self]

end PiExponent.FormalBranchEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactJetIdeal
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
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

theorem restrict_extend (I : U.IdealSheafData) (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] : (extend I j).comap j = I := by
  apply Scheme.IdealSheafData.ext
  funext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have hsq : IsPullback I.subschemeι (𝟙 I.subscheme) j (I.subschemeι ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have h := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (I.subschemeι ≫ j) I.subschemeι (𝟙 I.subscheme) j hsq W
  simpa only [Scheme.IdealSheafData.ker_subschemeι, extend, Scheme.IdealSheafData.map] using h.symm

end PiExponent.CompactJetIdeal
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_BranchContactIdeal
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BranchContactIdeal
open IsDiscreteValuationRing

variable {A ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable [Fintype ι] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

def contact (v : ι → ℚ) (z : ι → A) (hne : ∃ i, z i ≠ 0) : ℚ :=
  BranchContact.contact v (fun i => DVRBranch.expansion ℂ A (z i)) (by
    obtain ⟨i,hi⟩ := hne
    exact ⟨i,(map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hi⟩)

theorem exists_generator_colength_eq_contact
    (v : ι → ℚ) (hv : ∀ i, 0 < v i) (z : ι → A) (hne : ∃ i, z i ≠ 0)
    (R : ℚ) (e : ι → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ∃ i, z i ≠ 0 ∧ powerIdeal z e = Ideal.span {z i ^ e i} ∧
      ((Module.length A (A ⧸ powerIdeal z e)).toNat : ℚ) = R * contact v z hne := by
  classical
  let a : ι → PowerSeries ℂ := fun i => DVRBranch.expansion ℂ A (z i)
  have han : ∃ i, a i ≠ 0 := by
    obtain ⟨i,hi⟩ := hne
    exact ⟨i,(map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hi⟩
  obtain ⟨i,hi,hatt⟩ := BranchContact.exists_attains v a han
  have hzi : z i ≠ 0 := fun hz => hi (by simp [a,hz])
  have hival : (contact v z hne) * v i = ((addVal A (z i)).toNat : ℚ) := by
    have h := (eq_div_iff (ne_of_gt (hv i))).mp hatt
    simpa only [contact, a, DVRBranch.expansion_order] using h
  have hiR : ((addVal A (z i ^ e i)).toNat : ℚ) = R * contact v z hne := by
    rw [addVal_pow_toNat hzi, Nat.cast_mul, ← hival, ← he i]
    ring
  have hmin : ∀ j, addVal A (z i ^ e i) ≤ addVal A (z j ^ e j) := by
    intro j
    by_cases hzj : z j = 0
    · by_cases hej : e j = 0
      · have hR : R = 0 := by simpa [hej] using (he j).symm
        have hi0 : e i = 0 := by
          have hh := he i
          rw [hR, mul_eq_zero] at hh
          exact_mod_cast hh.resolve_left (ne_of_gt (hv i))
        simp [hej,hi0]
      · simp [hzj,zero_pow hej]
    · have haj : a j ≠ 0 := (map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hzj
      have hb := BranchContact.contact_bound v hv a han j (a j).order.toNat
        (PowerSeries.coe_toNat_order haj).symm
      have hb' : contact v z hne * v j ≤ ((addVal A (z j)).toNat : ℚ) := by
        simpa only [contact, a, DVRBranch.expansion_order] using hb
      have hrat : ((addVal A (z i ^ e i)).toNat : ℚ) ≤
          ((addVal A (z j ^ e j)).toNat : ℚ) := by
        rw [hiR, addVal_pow_toNat hzj, Nat.cast_mul, ← he j]
        nlinarith [mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg (e j) : (0:ℚ) ≤ e j)]
      have hnat : (addVal A (z i ^ e i)).toNat ≤ (addVal A (z j ^ e j)).toNat := by
        exact_mod_cast hrat
      rw [← ENat.natCast_toNat (addVal_eq_top_iff.not.mpr (pow_ne_zero _ hzi)),
        ← ENat.natCast_toNat (addVal_eq_top_iff.not.mpr (pow_ne_zero _ hzj))]
      exact_mod_cast hnat
  have heq := powerIdeal_eq_singleton z e i hmin
  refine ⟨i,hzi,heq,?_⟩
  rw [heq, CurveLocalOrder.length_quotient_span_eq_addVal (pow_ne_zero _ hzi)]
  exact hiR

theorem colength_eq_contact
    (v : ι → ℚ) (hv : ∀ i, 0 < v i) (z : ι → A) (hne : ∃ i, z i ≠ 0)
    (R : ℚ) (e : ι → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length A (A ⧸ powerIdeal z e)).toNat : ℚ) = R * contact v z hne := by
  obtain ⟨_,_,_,h⟩ := exists_generator_colength_eq_contact v hv z hne R e he
  exact h

end PiExponent.BranchContactIdeal

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_FormalLogTailOrder
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchContact

open FormalLogTruncation

theorem composed_logTail_strict_contact {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (a : Fin (m+1) → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (i : Fin m) (k : ℕ)
    (hk : PowerSeries.order (PowerSeries.subst (a 0) (logTail (T i))) = (k : ℕ∞)) :
    BranchContact.contact v a hne * v i.succ < (k : ℚ) := by
  have hTi : 0 < T i := by
    by_contra h
    have hz : T i = 0 := by omega
    have hh := hT i
    rw [hz, Nat.cast_zero, zero_mul] at hh
    exact (not_lt_of_ge (hv i.succ).le) hh
  have hb := composed_logTail_order_ge (T i) (a 0) (ha 0)
  rw [hk] at hb
  have hfinite : (a 0).order ≠ ⊤ := by
    intro htop
    have hTi0 : (T i : ℕ∞) ≠ 0 := by exact_mod_cast hTi.ne'
    simp only [htop, ENat.mul_top hTi0] at hb
    simp at hb
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  rw [← hn] at hb
  have hnat : T i * n ≤ k := by exact_mod_cast hb
  have hcontact := BranchContact.contact_bound v hv a hne 0 n hn.symm
  have hμ := BranchContact.contact_pos v hv a hne ha
  calc
    BranchContact.contact v a hne * v i.succ <
        BranchContact.contact v a hne * ((T i : ℚ) * v 0) :=
      mul_lt_mul_of_pos_left (hT i) hμ
    _ = (T i : ℚ) * (BranchContact.contact v a hne * v 0) := by ring
    _ ≤ (T i : ℚ) * (n : ℚ) := mul_le_mul_of_nonneg_left hcontact (by positivity)
    _ ≤ (k : ℚ) := by exact_mod_cast hnat

end PiExponent.FormalBranchContact

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalBranchCoordinates
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchContact

open FormalBranchEvaluation FormalLogTruncation

theorem branchCoordinates_constantCoeff {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i) :
    ∀ i, PowerSeries.constantCoeff (branchCoordinates c y x i) = 0 := by
  intro i
  have hh := (branchCoordinates_hasSubst c y x hy hx).const_coeff i
  have hz := isNilpotent_iff_eq_zero.mp hh
  simpa only [PowerSeries.constantCoeff_eq] using hz

theorem truncatedBranchCoordinates_eq_add_tail {m : ℕ}
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (T : Fin m → ℕ) (hy : PowerSeries.constantCoeff y = 1) :
    truncatedBranchCoordinates c y x T =
      fun i => branchCoordinates c y x i + composedLogTails (branchCoordinates c y x) T i := by
  have ht : PowerSeries.constantCoeff (y-1) = 0 := by simp [hy]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ht
  funext i
  cases i using Fin.cases with
  | zero => simp [truncatedBranchCoordinates, branchCoordinates, composedLogTails]
  | succ i =>
    simp only [truncatedBranchCoordinates, branchCoordinates, composedLogTails,
      Fin.cases_succ, Fin.cases_zero, logTail, PowerSeries.subst_sub hs]
    ring

end PiExponent.FormalBranchContact

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalBranchContact
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchContact

open FormalBranchEvaluation

theorem composedLogTails_strict_contact {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (a : Fin (m+1) → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    ∀ i (k : ℕ), (composedLogTails a T i).order = (k : ℕ∞) →
      BranchContact.contact v a hne * v i < (k : ℚ) := by
  intro i k hk
  cases i using Fin.cases with
  | zero => simp [composedLogTails] at hk
  | succ i => exact composed_logTail_strict_contact v hv a hne ha T hT i k hk

theorem truncatedBranchCoordinates_not_all_zero {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (hne : ∃ i, branchCoordinates c y x i ≠ 0)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    ∃ i, truncatedBranchCoordinates c y x T i ≠ 0 := by
  rw [truncatedBranchCoordinates_eq_add_tail c y x T hy]
  exact BranchContact.add_not_all_zero v hv _ _ hne
    (composedLogTails_strict_contact v hv _ hne
      (branchCoordinates_constantCoeff c y x hy hx) T hT)

end PiExponent.FormalBranchContact

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_LogarithmicContactIdeal
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.LogarithmicContactIdeal

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem expansion_polynomial_aeval (z : A) (p : Polynomial ℂ) :
    DVRBranch.expansion ℂ A (Polynomial.aeval z p) =
      Polynomial.aeval (DVRBranch.expansion ℂ A z) p := by
  have hh : (DVRBranch.expansion ℂ A).comp (Polynomial.aeval z) =
      Polynomial.aeval (DVRBranch.expansion ℂ A z) := by
    apply Polynomial.algHom_ext
    simp
  exact AlgHom.congr_fun hh p

theorem expansion_truncatedCoordinates {m : ℕ}
    (c : Fin m → ℂ) (y : A) (x : Fin m → A) (T : Fin m → ℕ)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1) :
    (fun i => DVRBranch.expansion ℂ A (truncatedCoordinates c y x T i)) =
      FormalBranchContact.truncatedBranchCoordinates c (DVRBranch.expansion ℂ A y)
        (fun i => DVRBranch.expansion ℂ A (x i)) T := by
  have ht : PowerSeries.constantCoeff (DVRBranch.expansion ℂ A y - 1) = 0 := by
    simp [hy]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ht
  funext i
  cases i using Fin.cases with
  | zero => simp [truncatedCoordinates, FormalBranchContact.truncatedBranchCoordinates]
  | succ i =>
    simp only [truncatedCoordinates, FormalBranchContact.truncatedBranchCoordinates,
      Fin.cases_succ, map_sub, map_one, AlgHom.commutes, expansion_polynomial_aeval]
    rw [PowerSeries.subst_coe hs]
    rfl

end PiExponent.LogarithmicContactIdeal

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactJetPolynomial
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
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

theorem aeval_coordinates {A : Type*} [CommRing A] [Algebra ℂ A]
    (c : Fin m → ℂ) (T : Fin m → ℕ) (y : A) (x : Fin m → A) (i : Fin (m+1)) :
    MvPolynomial.aeval (Fin.cases y x) (coordinates c (logPolynomials T) i) =
      LogarithmicContactIdeal.truncatedCoordinates c y x T i := by
  cases i using Fin.cases with
  | zero => simp [coordinates, LogarithmicContactIdeal.truncatedCoordinates]
  | succ i =>
    simp only [coordinates, inverseTriangularMap_X_succ, map_sub,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, Fin.cases_succ,
      ← Polynomial.aeval_algHom_apply, Fin.cases_zero, map_one,
      LogarithmicContactIdeal.truncatedCoordinates]
    rfl

theorem map_powerIdeal_aeval {A : Type*} [CommRing A] [Algebra ℂ A]
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (y : A) (x : Fin m → A) :
    (powerIdeal c (logPolynomials T) e).map (MvPolynomial.aeval (Fin.cases y x)).toRingHom =
      LogarithmicContactIdeal.logarithmicIdeal c y x T e := by
  rw [powerIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change MvPolynomial.aeval (Fin.cases y x) (coordinates c (logPolynomials T) i ^ e i) =
    LogarithmicContactIdeal.truncatedCoordinates c y x T i ^ e i
  rw [map_pow, aeval_coordinates]

end PiExponent.CompactJetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactLogJetIdeal
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

theorem restrict_compactIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (compactIdeal c T e j).comap j = affineIdeal c T e :=
  CompactJetIdeal.restrict_extend _ j

end PiExponent.CompactLogJetIdeal
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_FiniteCurveZeros
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X Y : Scheme}

lemma proper_finite_germ_surjective (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] (x : X) :
    Function.Surjective (X.presheaf.germ ⊤ x trivial) := by
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite K Γ(X,⊤)
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let p : PrimeSpectrum Γ(X,⊤) := (isAffineOpen_top X).isoSpec.hom ⟨x,trivial⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x,trivial⟩
  exact IsArtinianRing.localization_surjective p.asIdeal.primeCompl (X.presheaf.stalk x)

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X : Scheme}

theorem proper_finite_finrank_eq_sum_stalks (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Fintype X] :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    Module.finrank K Γ(X,⊤) = ∑ x : X,
      let _ := structuralStalkAlgebra f x
      Module.finrank K (X.presheaf.stalk x) := by
  classical
  dsimp only
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite K Γ(X,⊤)
  let : Fintype (MaximalSpectrum Γ(X,⊤)) := Fintype.ofFinite _
  let e : X ≃ MaximalSpectrum Γ(X,⊤) :=
    (Equiv.Set.univ X).symm.trans ((isAffineOpen_top X).isoSpec.hom.homeomorph.toEquiv.trans
      IsArtinianRing.primeSpectrumEquivMaximalSpectrum)
  rw [PiExponent.FiniteZeroEuler.finrank_eq_sum_localizations Γ(X,⊤) K, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let : Algebra K (X.presheaf.stalk x) := structuralStalkAlgebra f x
  let : IsScalarTower K Γ(X,⊤) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (e x).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x,trivial⟩
  exact ((IsLocalization.algEquiv (e x).asIdeal.primeCompl
    (Localization.AtPrime (e x).asIdeal) (X.presheaf.stalk x)).restrictScalars K).toLinearEquiv.finrank_eq

end

open AlgebraicGeometry CategoryTheory

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GeneratorsSectionCover
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeneratorsSectionCover
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

abbrev schemeInclusion {X : Scheme.{0}} {ι : Type} (i : ι) :
    O X ⟶ schemeFree X ι := SheafOfModules.ιFree i

def freeProjection {ι : Type} [DecidableEq ι] (i : ι) :
    schemeFree X ι ⟶ O X :=
  Sigma.desc (C := X.Modules) (f := fun _ : ι => O X) (fun j => if j = i then 𝟙 _ else 0)

@[simp] theorem free_inclusion_projection {ι : Type} [DecidableEq ι] (i j : ι) :
    schemeInclusion j ≫ freeProjection (X := X) i = if j = i then 𝟙 _ else 0 := by
  exact Sigma.ι_desc (C := X.Modules) (f := fun _ : ι => O X) _ _

end
end PiExponent.GeneratorsSectionCover

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PrincipalCartierSequence
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.PrincipalSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

lemma scalarEnd_eq_multiply (r : Γ(X,⊤)) : scalarEnd r = IdealModule.multiply r := rfl

lemma end_regular_of_mono (a : O X ⟶ O X) [Mono a] : IsLeftRegular (endValue a) := by
  have hinj : Function.Injective (a.val.app (op ⊤)) :=
    PresheafOfModules.injective_of_mono
      ((Scheme.Modules.toPresheafOfModules X).map a) (op ⊤)
  intro r s hrs
  apply hinj
  change a.app ⊤ r = a.app ⊤ s
  rw [end_apply a ⊤ r, end_apply a ⊤ s]
  change r * endValue a = s * endValue a
  simpa only [mul_comm] using hrs

theorem exact [IsAffine Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (a : O Y ⟶ O Y) [Mono a]
    (h : f.ker.ideal ⟨⊤,isAffineOpen_top Y⟩ = Ideal.span {endValue a}) :
    ∃ hz : a ≫ IdealModule.structureMap f = 0,
      (ShortComplex.mk a (IdealModule.structureMap f) hz).ShortExact := by
  let r := endValue a
  have hr : f.appTop r = 0 := by
    change r ∈ RingHom.ker f.appTop.hom
    erw [← Scheme.Hom.ker_apply f ⟨⊤,isAffineOpen_top Y⟩, h]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hreg : IsLeftRegular r := end_regular_of_mono a
  have hprincipal (U : Y.affineOpens) : f.ker.ideal U =
      Ideal.span {Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r} := by
    rw [← f.ker.map_ideal (U := U) (V := ⟨⊤,isAffineOpen_top Y⟩) (by change U.1 ≤ ⊤; exact le_top), h]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  have hi : IsIso (IdealModule.equationToIdeal f r hr) :=
    IdealModule.isIso_equationToIdeal f r hr hprincipal
      (IdealModule.restriction_regular r hreg)
  have he : a = IdealModule.multiply r := by
    rw [← scalarEnd_eq_multiply]
    apply endValue_injective
    simp [r]
  have hz : a ≫ IdealModule.structureMap f = 0 := by
    rw [he]
    exact IdealModule.multiply_structure_zero f r hr
  refine ⟨hz,?_⟩
  let S := ShortComplex.mk a (IdealModule.structureMap f) hz
  let T := ShortComplex.mk (IdealModule.inclusion f) (IdealModule.structureMap f)
    (kernel.condition (IdealModule.structureMap f))
  let e : S ≅ T := ShortComplex.isoMk (@asIso Y.Modules _ _ _ (IdealModule.equationToIdeal f r hr) hi)
    (Iso.refl _) (Iso.refl _) (by
      change IdealModule.equationToIdeal f r hr ≫ IdealModule.inclusion f = a ≫ 𝟙 _
      exact (IdealModule.equationToIdeal_inclusion f r hr).trans
        (he.symm.trans (Category.comp_id a).symm)) (by exact (Category.id_comp _).trans (Category.comp_id _).symm)
  have hg : Epi (IdealModule.structureMap f) := IdealModule.structureMap_epi f
  exact { exact := ShortComplex.exact_of_iso e.symm (ShortComplex.exact_kernel _), epi_g := hg }

end
end PiExponentSeshadri.PrincipalSequence

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveModelFieldEmbedding
attribute [-instance] _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
open scoped Polynomial nonZeroDivisors
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]

abbrev parameterChartFractionRing : IsFractionRing (parameterChart f hf) E :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  inferInstance

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalSectionOrder
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
universe u

namespace PiExponent.LocalSectionOrder

def localCoefficient
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom (coefficient e s)

def localFrameChange
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e f : M ≅ O (Spec (CommRingCat.of A))) : Aˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (frameChange e f)

theorem localCoefficient_change
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e f : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) :
    localCoefficient f s = (localFrameChange e f : A) * localCoefficient e s := by
  unfold localCoefficient
  rw [coefficient_change e f s, map_mul]
  rfl

def sectionOrder
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) : ℕ∞ :=
  IsDiscreteValuationRing.addVal A (localCoefficient e s)

theorem sectionOrder_frame_independent
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {M : (Spec (CommRingCat.of A)).Modules}
    (e f : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) :
    sectionOrder e s = sectionOrder f s := by
  unfold sectionOrder
  rw [localCoefficient_change e f, AddValuation.map_mul,
    IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]

theorem localCoefficient_eq_zero_iff
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) : localCoefficient e s = 0 ↔ s = 0 := by
  constructor
  · intro h
    have hc : coefficient e s = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
      simpa only [localCoefficient, map_zero] using h
    have he : s ≫ e.hom = 0 := by
      ext U a
      change Γ(Spec (CommRingCat.of A), U) at a
      change (s ≫ e.hom).app U a = (0 : Γ(Spec (CommRingCat.of A), U))
      rw [end_apply, end_naturality]
      change a * (Spec (CommRingCat.of A)).presheaf.map _ (coefficient e s) = 0
      rw [hc, map_zero]
      exact mul_zero a
    apply (cancel_mono e.hom).mp
    simpa using he
  · intro h
    subst h
    unfold localCoefficient coefficient endValue
    rw [zero_comp]
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom (0 : Γ(Spec (CommRingCat.of A), ⊤)) = 0
    exact map_zero _

end PiExponent.LocalSectionOrder

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_JetProductLocalization
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.JetProductLocalization
open CompactJetPolynomial LogarithmicContactIdeal

variable {A : Type*} [CommRing A] [IsLocalRing A] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

def residueAlgHom : A →ₐ[ℂ] ℂ where
  __ := CurveLocalOrder.residueAugmentation ℂ A
  commutes' := CurveLocalOrder.residueAugmentation_algebraMap ℂ A

theorem residue_ne_zero_iff_isUnit (a : A) :
    CurveLocalOrder.residueAugmentation ℂ A a ≠ 0 ↔ IsUnit a := by
  change (CurveLocalOrder.residueCoefficientEquiv ℂ A).symm
    ((IsLocalRing.residue A) a) ≠ 0 ↔ IsUnit a
  rw [map_ne_zero_iff _ (CurveLocalOrder.residueCoefficientEquiv ℂ A).symm.injective,
    IsLocalRing.residue_ne_zero_iff_isUnit]

theorem residue_polynomial_aeval (a : A) (P : Polynomial ℂ) :
    CurveLocalOrder.residueAugmentation ℂ A (Polynomial.aeval a P) =
      P.eval (CurveLocalOrder.residueAugmentation ℂ A a) := by
  simpa [Polynomial.coe_aeval_eq_eval, residueAlgHom] using
    (Polynomial.aeval_algHom_apply (residueAlgHom (A := A)) a P).symm

theorem residue_truncatedCoordinates_succ {m : ℕ}
    (c : Fin m → ℂ) (T : Fin m → ℕ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1) (i : Fin m) :
    CurveLocalOrder.residueAugmentation ℂ A (truncatedCoordinates c y x T i.succ) =
      CurveLocalOrder.residueAugmentation ℂ A (x i) - c i := by
  have hlog : CurveLocalOrder.residueAugmentation ℂ A
      (Polynomial.aeval (y-1) (PowerSeries.trunc (T i) (PowerSeries.log ℂ))) = 0 := by
    rw [residue_polynomial_aeval, map_sub, map_one, hy, sub_self]
    exact logPolynomials_eval_zero T i
  simp only [truncatedCoordinates, Fin.cases_succ, map_sub,
    CurveLocalOrder.residueAugmentation_algebraMap, hlog, sub_zero]

theorem logarithmicIdeal_eq_top_of_residue_ne {m : ℕ}
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (y : A) (x : Fin m → A)
    (hne : ¬ (CurveLocalOrder.residueAugmentation ℂ A y = 1 ∧
      ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)) :
    logarithmicIdeal c y x T e = ⊤ := by
  classical
  have hunit : ∃ i : Fin (m+1), IsUnit (truncatedCoordinates c y x T i) := by
    by_cases hy : CurveLocalOrder.residueAugmentation ℂ A y = 1
    · have hx : ¬ ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i :=
        fun hx => hne ⟨hy, hx⟩
      obtain ⟨i, hi⟩ := not_forall.mp hx
      refine ⟨i.succ, (residue_ne_zero_iff_isUnit _).mp ?_⟩
      rw [residue_truncatedCoordinates_succ c T y x hy i]
      exact sub_ne_zero.mpr hi
    · refine ⟨0, (residue_ne_zero_iff_isUnit _).mp ?_⟩
      change CurveLocalOrder.residueAugmentation ℂ A (y-1) ≠ 0
      rw [map_sub, map_one]
      exact sub_ne_zero.mpr hy
  obtain ⟨i, hi⟩ := hunit
  apply Ideal.eq_top_of_isUnit_mem _
    (show truncatedCoordinates c y x T i ^ e i ∈ logarithmicIdeal c y x T e from
      Ideal.subset_span (Set.mem_range_self i))
  exact hi.pow (e i)

theorem map_powerIdeal_eq_top_of_ne {J : Type*} {m : ℕ}
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (y : A) (x : Fin m → A)
    (j k : J) (hkj : k ≠ j)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c j i) :
    (powerIdeal (c k) (logPolynomials T) e).map
      (MvPolynomial.aeval (Fin.cases y x)).toRingHom = ⊤ := by
  rw [map_powerIdeal_aeval]
  apply logarithmicIdeal_eq_top_of_residue_ne
  rw [hy]
  rintro ⟨_, hk⟩
  apply hkj
  apply hc
  funext i
  exact (hk i).symm.trans (hx i)

omit [IsLocalRing A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)] in
theorem map_polynomialIdeal {J : Type*} [Fintype J] {m : ℕ}
    (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (y : A) (x : Fin m → A) :
    (CompactLogJetIdeal.polynomialIdeal c T e).map
      (MvPolynomial.aeval (Fin.cases y x)).toRingHom =
        ∏ j, logarithmicIdeal (c j) y x T e := by
  unfold CompactLogJetIdeal.polynomialIdeal
  change Ideal.mapHom (MvPolynomial.aeval (Fin.cases y x)).toRingHom _ = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact map_powerIdeal_aeval (c j) T e y x

theorem map_polynomialIdeal_eq_selected {J : Type*} [Fintype J] {m : ℕ}
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (y : A) (x : Fin m → A) (j : J)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c j i) :
    (CompactLogJetIdeal.polynomialIdeal c T e).map
      (MvPolynomial.aeval (Fin.cases y x)).toRingHom = logarithmicIdeal (c j) y x T e := by
  classical
  rw [map_polynomialIdeal]
  apply Finset.prod_eq_single j
  · intro k _ hkj
    rw [Ideal.one_eq_top]
    rw [← map_powerIdeal_aeval]
    exact map_powerIdeal_eq_top_of_ne c hc T e y x j k hkj hy hx
  · simp

end PiExponent.JetProductLocalization

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPowerFiltration
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X : Scheme.{0}}

instance closedInclusion_mono (I : X.IdealSheafData) : Mono (closedInclusion I) :=
  inferInstanceAs (Mono (inclusion I.subschemeι))

lemma closedInclusion_structureMap_eq_zero {I J : X.IdealSheafData} (h : I ≤ J) :
    closedInclusion I ≫ structureMap J.subschemeι = 0 := by
  ext U x
  change J.subschemeι.app U ((closedInclusion I).app U x) = 0
  have hi : I.subschemeι.app U ((closedInclusion I).app U x) = 0 :=
    congrArg (fun f => f.app U x) (kernel.condition (structureMap I.subschemeι))
  rw [Scheme.Hom.congr_app (Scheme.IdealSheafData.inclusion_subschemeι h).symm U,
    Scheme.Hom.comp_app]
  change J.subscheme.presheaf.map _
    ((Scheme.IdealSheafData.inclusion h).app _
      (I.subschemeι.app U ((closedInclusion I).app U x))) = 0
  rw [hi, map_zero, map_zero]

def closedMap {I J : X.IdealSheafData} (h : I ≤ J) : closedModule I ⟶ closedModule J :=
  kernel.lift (structureMap J.subschemeι) (closedInclusion I)
    (closedInclusion_structureMap_eq_zero h)

@[reassoc (attr := simp)] lemma closedMap_inclusion {I J : X.IdealSheafData} (h : I ≤ J) :
    closedMap h ≫ closedInclusion J = closedInclusion I := kernel.lift_ι _ _ _

@[simp] lemma closedMap_refl (I : X.IdealSheafData) : closedMap (le_refl I) = 𝟙 _ := by
  apply (cancel_mono (closedInclusion I)).mp
  simp

@[reassoc (attr := simp)] lemma closedMap_comp {I J K : X.IdealSheafData}
    (hIJ : I ≤ J) (hJK : J ≤ K) : closedMap hIJ ≫ closedMap hJK = closedMap (hIJ.trans hJK) := by
  apply (cancel_mono (closedInclusion K)).mp
  simp

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPowerAnnihilator
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

lemma restriction_mem_ideal (I : X.IdealSheafData) (r : Γ(X,⊤))
    (hr : I.subschemeι.appTop r = 0) (U : X.affineOpens) :
    restrictScalar X U.1 r ∈ I.ideal U := by
  rw [← I.ker_subschemeι_app U, RingHom.mem_ker]
  unfold restrictScalar
  have h := congrArg (fun f => f r) (I.subschemeι.naturality
    (homOfLE (show U.1 ≤ ⊤ from le_top)).op)
  change I.subschemeι.app U.1 (X.presheaf.map (homOfLE le_top).op r) = _ at h
  rw [CommRingCat.comp_apply] at h
  exact h.trans ((congrArg _ hr).trans (map_zero _))

lemma smul_closedInclusion_structureMap_eq_zero (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    (r • closedInclusion (I^n)) ≫ structureMap (I^(n+1)).subschemeι = 0 := by
  apply hom_ext_affine
  intro U
  ext x
  change (I^(n+1)).subschemeι.app U.1
    (restrictScalar X U.1 r * (show Γ(X,U.1) from (closedInclusion (I^n)).app U.1 x)) = 0
  apply RingHom.mem_ker.mp
  rw [(I^(n+1)).ker_subschemeι_app U]
  change restrictScalar X U.1 r * (show Γ(X,U.1) from (closedInclusion (I^n)).app U.1 x) ∈
    I.ideal U ^ (n+1)
  rw [pow_succ']
  apply Ideal.mul_mem_mul (restriction_mem_ideal I r hr U)
  change (closedInclusion (I^n)).app U.1 x ∈ (I^n).ideal U
  rw [← closed_image (I^n) U]
  exact ⟨x,rfl⟩

def multiplyToNextPower (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    closedModule (I^n) ⟶ closedModule (I^(n+1)) :=
  kernel.lift (structureMap (I^(n+1)).subschemeι) (r • closedInclusion (I^n))
    (smul_closedInclusion_structureMap_eq_zero I n r hr)

@[reassoc (attr := simp)] lemma multiplyToNextPower_inclusion (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    multiplyToNextPower I n r hr ≫ closedInclusion (I^(n+1)) = r • closedInclusion (I^n) :=
  kernel.lift_ι _ _ _

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalCurveDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalCurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

theorem localIdeal_specIdeal {A B : Type} [CommRing A] [CommRing B]
    (I : Ideal B) (φ : B →+* A) :
    localIdeal (PiExponentSeshadri.IdealPullback.specIdeal I)
      (Spec.map (CommRingCat.ofHom φ)) = I.map φ := by
  unfold localIdeal
  rw [PiExponentSeshadri.IdealPullback.specIdeal_comap,
    PiExponentSeshadri.IdealPullback.specIdeal_top, Ideal.map_map]
  have he : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom = RingHom.id A := by
    ext a
    exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply a
  rw [he, Ideal.map_id]

theorem localIdeal_eq_top_of_not_mem {A : Type} [CommRing A] [IsLocalRing A]
    (I : X.IdealSheafData) (q : Spec (CommRingCat.of A) ⟶ X)
    (hq : q (IsLocalRing.closedPoint A) ∉ I.support) : localIdeal I q = ⊤ := by
  have havoid (a : Spec (CommRingCat.of A)) : q a ∉ I.support :=
    ((IsLocalRing.specializes_closedPoint a).map q.continuous).mem_open
      I.support.isClosed.isOpen_compl hq
  have ht := CompactJetIdeal.restrict_eq_top_of_disjoint I q havoid
  unfold localIdeal
  rw [ht]
  exact Ideal.map_top _

end
end PiExponent.ExceptionalCurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_DeterminantContradiction
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace PiExponent.DeterminantContradiction

abbrev FixedData (nu : ℝ) := AdmissibleParameters nu Arithmetic.lcmConstant collisionConstant

end PiExponent.DeterminantContradiction

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedSectionOrder
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedLocalSheaf PiExponent.WeightedLocalLattice
open PiExponent.LocalSectionOrder PiExponent.CurveLocalOrder
open scoped BigOperators

namespace PiExponent.WeightedSectionOrder


theorem coefficient_tilde_end {A : Type} [CommRing A] (f : A →ₗ[A] A) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (endValue (tildeSelf.inv ≫
        (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom f) ≫ tildeSelf.hom)) = f 1 := by
  have h := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (R := CommRingCat.of A) (ModuleCat.ofHom f) ⊤) (1 : A)
  change ((tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom f)).app ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv 1) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (f 1) at h
  rw [map_one] at h
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (((tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom f)).app ⊤ (1 : Γ(Spec (CommRingCat.of A), ⊤))) = f 1
  rw [h]
  simp

variable {A K : Type} {ι : Type*} [CommRing A] [IsDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K]

def coordinateFrame (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a}) :
    generatedSheaf (A := A) y s ≅ O (Spec (CommRingCat.of A)) :=
  (tilde.functor (CommRingCat.of A)).mapIso
    (coordinateBasis y s a ha hya hspan).symm.toModuleIso ≪≫ tildeSelf

end PiExponent.WeightedSectionOrder

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveGlobalMonomialLocal
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.CurveGlobalMonomialLocal
open AlgebraicGeometry CategoryTheory MvPolynomial
open WeightedSectionOrder
open WeightedLocalLattice PiExponentSeshadri.Projective
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem monomialCoordinates_eq_prod
    {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E] [Fintype ι]
    (a : σ → ι →₀ ℕ) (x : ι → E) (s : σ) :
    monomialCoordinates (F := F) a x s = ∏ j, x j ^ (a s j) := by
  rw [monomialCoordinates, eval₂Hom_monomial, map_one, one_mul]
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

end PiExponent.CurveGlobalMonomialLocal

end

end OAI
end


