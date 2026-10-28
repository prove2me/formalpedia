-- Prove2me | Definitions.Def_OAIQ068A004
-- name    : OAIQ068A004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:39:42.557744+00:00
-- url     : https://prove2.me/theorems/79c701ac-8f3e-45a6-96ff-32ac1024b41a
-- title:
--   Definitions bundle OAIQ068A004 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 158 declarations of OpenAI's Lean: 41 definitions, 1 inductive type or structure, 16 instances and 100 theorems. The definitions and types are `OAI.PiExponent.ClosedImmersionSerreTransfer.cohomologyMap`, `OAI.PiExponent.ClosedImmersionSerreTransfer.schemeUnit`, `OAI.PiExponent.ClosedImmersionSerreTransfer.structureMap`, `OAI.PiExponent.ClosedPushforwardAffine.transportPresentation`, `OAI.PiExponent.CurveBlowupImage.functionFieldIso`, `OAI.PiExponent.CurveBlowupImage.functionFieldMap`, `OAI.PiExponent.CurveFinitePushforwardCoherent.presentationOfIso`, `OAI.PiExponent.CurveImageAffineCoordinates.affinePart`, `OAI.PiExponent.CurveImageAffineCoordinates.affinePresentation`, `OAI.PiExponent.GeometrySupport.CechHigher.intersection`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.FullGroupAlgebra`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.standardExponent`, `OAI.PiExponent.ProjectiveCurveTwoAffine.linearEquation`, `OAI.PiExponent.ProjectiveCurveTwoAffine.linearEquationLinear`, `OAI.PiExponent.ProjectiveMonomialCechHigher.Cochain`, `OAI.PiExponent.SerreVanishing.schemeUnit`, `OAI.PiExponentSeshadri.AdicInjective.adicTorsion`, `OAI.PiExponentSeshadri.AffineDenominators.Aux`, `OAI.PiExponentSeshadri.AffineDenominators.res`, `OAI.PiExponentSeshadri.AffineDenominators.schemeBasicOpen`, `OAI.PiExponentSeshadri.AffineSchemeCohomology.restrictionEquivalence`, `OAI.PiExponentSeshadri.Cohomology.alternatingTrunc`, `OAI.PiExponentSeshadri.Cohomology.cohomologyBoundary`, `OAI.PiExponentSeshadri.Cohomology.cohomologyMap₁`, `OAI.PiExponentSeshadri.Cohomology.cohomologyMap₂`, `OAI.PiExponentSeshadri.Cohomology.extEuler`, `OAI.PiExponentSeshadri.ExtCokernel.quotientEquiv`, `OAI.PiExponentSeshadri.ExtSectionComparison.mapFrom`, `OAI.PiExponentSeshadri.FlasqueCohomology.globalHomEquiv`, `OAI.PiExponentSeshadri.FlasqueCohomology.sectionsTopEquiv`, `OAI.PiExponentSeshadri.FreeOpenUnit.isoFromHomEquiv`, `OAI.PiExponentSeshadri.Geometry.BaseSections.nestedRestriction`, `OAI.PiExponentSeshadri.Geometry.affineToSpecModule`, `OAI.PiExponentSeshadri.Geometry.disjointSupportCoverEquiv`, `OAI.PiExponentSeshadri.Geometry.finiteSupportLocallyIsoGlobal`, `OAI.PiExponentSeshadri.Geometry.openSectionIso`, `OAI.PiExponentSeshadri.Geometry.openSectionModule`, `OAI.PiExponentSeshadri.Geometry.openSectionRestriction`, `OAI.PiExponentSeshadri.LaurentLattices.boundedAbove`, `OAI.PiExponentSeshadri.LaurentLattices.boundedBelow` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_CoherentAffineFinite`, `PiExponent_Ampleness_CurveBlowupImageBase`, `PiExponent_Approximation_ClosedImmersionSerreTransfer`, `PiExponent_Approximation_ClosedPushforwardAffine`, `PiExponent_Approximation_ClosedPushforwardCoherent`, `PiExponent_Cohomology_CechHigher`, `PiExponent_Cohomology_CurveNormalizationEuler`, `PiExponent_Cohomology_EulerExact`, `PiExponent_Cohomology_FiniteCoverCohomology`, `PiExponent_Cohomology_PencilCohomologyCech`, `PiExponent_Cohomology_PencilCohomologyCharts`, `PiExponent_Cohomology_PencilCohomologyFiniteCharts`, `PiExponent_Cohomology_PencilCohomologyLaurent`, `PiExponent_Cohomology_PencilCohomologyPencil`, `PiExponent_Cohomology_PencilCohomologySections`, `PiExponent_Cohomology_ProjectiveLaurentTransitions`, `PiExponent_Cohomology_ProjectiveMonomialCechHigher`, `PiExponent_Cohomology_SerreVanishing`, `PiExponent_Geometry_CurveFinitePushforwardCoherent`, `PiExponent_Geometry_CurveImageAffineChart`, `PiExponent_Geometry_CurveImageOpenLocus`, `PiExponent_Geometry_CurveNormalizationDegree`, `PiExponent_Geometry_CurveNormalizationUnit`, `PiExponent_Geometry_CurveProperImageDimension`, `PiExponent_Geometry_ProjectiveCurveTwoAffine`, `PiExponent_Geometry_SupportedSheaf`, `PiExponent_LocalAlgebra_FiniteGlobalPresentation`, `PiExponent_LocalAlgebra_FiniteSupportLocalIso`, `PiExponent_LocalAlgebra_OpenIsoFunctionField`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A014`, `OAIQ068A015` and `OAIQ068A017`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_CoherentAffineFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CoherentAffineFinite
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

theorem finitePresentation_quasicoherent {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] : M.IsQuasicoherent :=
  (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent

theorem finite_generators_of_le {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (s : (M.restrict U.ι).GeneratingSections) [s.IsFiniteType] :
    ∃ t : (M.restrict V.ι).GeneratingSections, t.IsFiniteType := by
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤ SheafOfModules V.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor (X.homOfLE h)
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction (X.homOfLE h)).leftAdjoint_preservesColimits
  let t := s.map F
    (Scheme.Modules.restrictUnitIso (X.homOfLE h)).symm
  let e := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M
  simp only [X.homOfLE_ι h] at e
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e.symm t,
    ⟨SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := s)⟩⟩

theorem finite_isoSpec_sections {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [Module.Finite Γ(X,⊤) Γ(M,⊤)] :
    Module.Finite Γ(X,⊤)
      ((modulesSpecToSheaf.obj (M.restrict X.isoSpec.inv)).obj.obj (op ⊤)) := by
  let f := X.isoSpec.inv
  let R := Γ(X,⊤)
  let N : ModuleCat R := (modulesSpecToSheaf.obj (M.restrict f)).obj.obj (op ⊤)
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have : Module.Finite Γ(X,f ''ᵁ ⊤) Γ(M,f ''ᵁ ⊤) := by
    rw [hf]
    infer_instance
  let σ : Γ(X,f ''ᵁ ⊤) →+* R := (Scheme.ΓSpecIso R).hom.hom.comp (f.appIso ⊤).hom.hom
  let φ : Γ(M,f ''ᵁ ⊤) →ₛₗ[σ] N := {
    toFun := (M.restrictAppIso f ⊤).inv
    map_add' := map_add _
    map_smul' := by
      intro r m
      change (M.restrictAppIso f ⊤).inv (r • m) =
        ((Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom ((f.appIso ⊤).hom r))) •
          (M.restrictAppIso f ⊤).inv m
      rw [Iso.hom_inv_id_apply]
      exact congr($(M.smul_restrictAppIso_inv f ⊤ r) m) }
  exact Module.Finite.of_surjective φ
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).inv).surjective

end
end PiExponent.CoherentAffineFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_CurveBlowupImageBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem integral_scheme_image (f : X ⟶ Y) [QuasiCompact f] [IsIntegral X] : IsIntegral f.image := by
  let hred (U : Y.affineOpens) : _root_.IsReduced (Γ(Y,U.1) ⧸ f.ker.ideal U) := by
    rw [Scheme.Hom.ker_apply]
    exact isReduced_of_injective (RingHom.kerLift (f.app U.1).hom)
      (RingHom.kerLift_injective (f.app U.1).hom)
  let : ∀ U, AlgebraicGeometry.IsReduced (f.ker.subschemeCover.openCover.X U) := by
    intro U
    change IsReduced (Spec (.of (Γ(Y,U.1) ⧸ f.ker.ideal U)))
    exact (affine_isReduced_iff _).mpr (hred U)
  let : IsReduced f.image := IsReduced.of_openCover f.image f.ker.subschemeCover.openCover
  have hi : IsIrreducible (Set.range f.toImage) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := X)).image f.toImage
        f.toImage.continuous.continuousOn
  let : IrreducibleSpace f.image := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set f.image)
    rw [← f.toImage.denseRange.closure_range]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end PiExponentSeshadri.Geometry

namespace PiExponent.CurveBlowupImage
open PiExponentSeshadri.Geometry
variable {C X B : Scheme.{0}}

theorem toImage_restrict_isIso (f : C ⟶ X) [IsProper f] [IsIntegral C]
    (U : X.Opens) [IsClosedImmersion (f ∣_ U)] :
    IsIso (f.toImage ∣_ (f.imageι ⁻¹ᵁ U)) := by
  let := integral_scheme_image f
  let : IsClosedImmersion
      ((f.toImage ∣_ (f.imageι ⁻¹ᵁ U)) ≫ (f.imageι ∣_ U)) := by
    rw [← morphismRestrict_comp]
    exact Eq.mpr (congrArg (fun k : C ⟶ X => IsClosedImmersion (k ∣_ U))
      f.toImage_imageι) (inferInstance : IsClosedImmersion (f ∣_ U))
  let := IsClosedImmersion.of_comp_isClosedImmersion
    (f.toImage ∣_ (f.imageι ⁻¹ᵁ U)) (f.imageι ∣_ U)
  let : IsDominant (f.toImage ∣_ (f.imageι ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (inferInstance : IsDominant f.toImage) _
  exact isIso_of_isClosedImmersion_of_surjective _

theorem genericPoint_eq_of_isDominant (f : C ⟶ X)
    [IsIntegral C] [IsIntegral X] [IsDominant f] :
    f (genericPoint C) = genericPoint X := by
  apply IsGenericPoint.eq _ (genericPoint_spec X)
  simpa only [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec C).image f.continuous

theorem stalkMap_isIso_of_restrict (f : C ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (x : C) (hx : f x ∈ U) : IsIso (f.stalkMap x) := by
  let q : (f ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  have hi : IsIso (((f ⁻¹ᵁ U).ι ≫ f).stalkMap q) := by
    rw [← morphismRestrict_ι]
    infer_instance
  rw [Scheme.Hom.stalkMap_comp] at hi
  change IsIso (f.stalkMap x ≫ (f ⁻¹ᵁ U).ι.stalkMap q) at hi
  have hq : IsIso ((f ⁻¹ᵁ U).ι.stalkMap q) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp
      (inferInstance : IsOpenImmersion (f ⁻¹ᵁ U).ι)).2 q
  exact @IsIso.of_isIso_comp_right CommRingCat _ _ _ _
    (f.stalkMap x) ((f ⁻¹ᵁ U).ι.stalkMap q) hq hi

end PiExponent.CurveBlowupImage

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FiniteCoverCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace AdicInjective
universe u v
variable {R : Type u} [CommRing R]
variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

def adicTorsion : Submodule R M :=
  ⨆ n : ℕ, Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)

lemma torsion_mono : Monotone (fun n : ℕ => Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)) :=
  fun a b hab => Submodule.torsionBySet_le_torsionBySet_pow a b hab I

lemma mem_adicTorsion (x : M) : x ∈ adicTorsion I M ↔
    ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
  rw [adicTorsion, Submodule.mem_iSup_of_directed _ (torsion_mono I M).directed_le]
  simp only [Submodule.mem_torsionBySet_iff, Subtype.forall, SetLike.mem_coe]

lemma fg_uniform_exponent (N : Submodule R M) (hN : N.FG)
    (h : N ≤ adicTorsion I M) :
    ∃ n : ℕ, N ≤ Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R) := by
  classical
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _
    ((Submodule.fg_iff_compact N).mp hN)
    (fun n : ℕ => Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)) h
  refine ⟨s.sup id, hs.trans (iSup_le fun n => iSup_le fun hn => ?_)⟩
  exact torsion_mono I M (Finset.le_sup (f := id) hn)

lemma exists_power_inf_le [IsNoetherianRing R] (J : Ideal R) (n : ℕ) :
    ∃ m : ℕ, I ^ m ⊓ J ≤ I ^ n * J := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (M := R) J
  refine ⟨k+n, ?_⟩
  have h := hk (k+n) (Nat.le_add_right _ _)
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel_left] at h
  rw [h]
  exact Ideal.mul_mono le_rfl inf_le_right

theorem adicTorsion_injective [IsNoetherianRing R] [Small.{v} R]
    [Module.Injective R M] : Module.Injective R (adicTorsion I M) := by
  apply Module.Baer.injective
  intro J g
  let g₀ : J →ₗ[R] M := (adicTorsion I M).subtype.comp g
  have hg₀ : g₀.range ≤ adicTorsion I M := by
    rintro x ⟨y, rfl⟩
    exact (g y).property
  obtain ⟨n, hn⟩ := fg_uniform_exponent I M g₀.range (Submodule.fg_range g₀) hg₀
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R M J R
    J.subtype Subtype.val_injective g₀
  have hj : ∀ x : J, h x = g₀ x := fun x => LinearMap.congr_fun hh x
  have hzero : I ^ n * J ≤ h.ker := by
    apply Ideal.mul_le.mpr
    intro a ha b hb
    change h (a * b) = 0
    rw [← smul_eq_mul, h.map_smul, hj ⟨b, hb⟩]
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hn (LinearMap.mem_range_self g₀ ⟨b,hb⟩)) ⟨a,ha⟩
  obtain ⟨m, hm⟩ := exists_power_inf_le I J n
  let f : R →ₗ.[R] M := ⟨J, g₀⟩
  let z : R →ₗ.[R] M := ⟨I ^ m, 0⟩
  have hz : ∀ (x : f.domain) (y : z.domain), (x : R) = y → f x = z y := by
    intro x y hxy
    change g₀ x = 0
    rw [← hj x]
    exact hzero (hm ⟨hxy ▸ y.property, x.property⟩)
  let F := f.sup z hz
  obtain ⟨H, hH⟩ := Module.Injective.extension_property R M F.domain R
    F.domain.subtype Subtype.val_injective F.toFun
  have HF : ∀ x : F.domain, H x = F x := fun x => LinearMap.congr_fun hH x
  have HJ : ∀ x : J, H x = g₀ x := by
    intro x
    rw [HF ⟨x, (show J ≤ J ⊔ I ^ m from le_sup_left) x.property⟩]
    exact ((f.left_le_sup z hz).2 (x := x) (y := ⟨x, (show J ≤ J ⊔ I ^ m from le_sup_left) x.property⟩) rfl).symm
  have HI : ∀ a ∈ I ^ m, H a = 0 := by
    intro a ha
    rw [HF ⟨a, (show I ^ m ≤ J ⊔ I ^ m from le_sup_right) ha⟩]
    exact ((f.right_le_sup z hz).2 (x := ⟨a,ha⟩) (y := ⟨a,(show I ^ m ≤ J ⊔ I ^ m from le_sup_right) ha⟩) rfl).symm
  have Hmem : ∀ a, H a ∈ adicTorsion I M := by
    intro a
    apply (mem_adicTorsion I M _).mpr
    refine ⟨m, fun b hb => ?_⟩
    rw [← H.map_smul]
    exact HI (b * a) ((I ^ m).mul_mem_right a hb)
  refine ⟨H.codRestrict (adicTorsion I M) Hmem, ?_⟩
  intro x hx
  apply Subtype.ext
  exact HJ ⟨x,hx⟩

end AdicInjective

namespace InjectiveRange
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Small.{v} R]
variable {N : Type w} [AddCommGroup N] [Module R N] [Small.{w} R]

omit [Small.{w} R] in

lemma injective_of_retract [Module.Injective R M]
    (i : N →ₗ[R] M) (p : M →ₗ[R] N) (h : p.comp i = LinearMap.id) :
    Module.Injective R N := by
  apply Module.Baer.injective
  intro J g
  obtain ⟨f, hf⟩ := Module.Baer.of_injective (R := R) (Q := M) inferInstance J (i.comp g)
  refine ⟨p.comp f, fun x hx => ?_⟩
  change p (f x) = g ⟨x,hx⟩
  rw [hf x hx]
  exact LinearMap.congr_fun h (g ⟨x,hx⟩)

omit [Small.{w} R] in
lemma range_injective (r : M →ₗ[R] N) [Module.Injective R M]
    [Module.Injective R r.ker] : Module.Injective R r.range := by
  obtain ⟨p, hp⟩ := Module.Injective.extension_property R r.ker r.ker M
    r.ker.subtype Subtype.val_injective LinearMap.id
  let f : M →ₗ[R] M := LinearMap.id - r.ker.subtype.comp p
  have hf : r.ker ≤ f.ker := by
    intro x hx
    change x - (p x : M) = 0
    have hpx := LinearMap.congr_fun hp ⟨x,hx⟩
    exact sub_eq_zero.mpr (congrArg Subtype.val hpx).symm
  let i : r.range →ₗ[R] M := (r.ker.liftQ f hf).comp r.quotKerEquivRange.symm.toLinearMap
  apply injective_of_retract i r.rangeRestrict
  ext y
  rcases y with ⟨y,hy⟩
  obtain ⟨x,rfl⟩ := hy
  change r ((r.ker.liftQ f hf) (r.quotKerEquivRange.symm ⟨r x, LinearMap.mem_range_self r x⟩)) = r x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  change r (x - (p x : M)) = r x
  rw [map_sub, (p x).property, sub_zero]

lemma surjective_of_torsion_cokernel (I : Ideal R) (r : M →ₗ[R] N)
    [Module.Injective R M] [Module.Injective R r.ker]
    (hc : ∀ y : N, ∃ n : ℕ, ∀ a ∈ I ^ n, a • y ∈ r.range)
    (ht : ∀ y : N, (∃ n : ℕ, ∀ a ∈ I ^ n, a • y = 0) → y = 0) :
    Function.Surjective r := by
  let : Module.Injective R r.range := range_injective r
  obtain ⟨p, hp⟩ := Module.Injective.extension_property R r.range r.range N
    r.range.subtype Subtype.val_injective LinearMap.id
  intro y
  suffices h : y = (p y : N) from h ▸ (p y).property
  apply sub_eq_zero.mp
  apply ht
  obtain ⟨n, hn⟩ := hc y
  refine ⟨n, fun a ha => ?_⟩
  rw [smul_sub]
  have h := congrArg Subtype.val (LinearMap.congr_fun hp ⟨a • y, hn a ha⟩)
  change (p (a • y) : N) = a • y at h
  rw [map_smul] at h
  exact sub_eq_zero.mpr h.symm

end InjectiveRange

section
universe u
open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
open PrimeSpectrum
namespace AffineDenominators
variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

abbrev schemeBasicOpen (f : R) : (Spec R).Opens := PrimeSpectrum.basicOpen f

lemma schemeBasicOpen_mul (f g : R) :
    schemeBasicOpen (f * g) = schemeBasicOpen f ⊓ schemeBasicOpen g :=
  PrimeSpectrum.basicOpen_mul f g

lemma schemeBasicOpen_mul_le_left (f g : R) :
    schemeBasicOpen (f * g) ≤ schemeBasicOpen f :=
  PrimeSpectrum.basicOpen_mul_le_left f g

lemma schemeBasicOpen_mul_le_right (f g : R) :
    schemeBasicOpen (f * g) ≤ schemeBasicOpen g :=
  PrimeSpectrum.basicOpen_mul_le_right f g

lemma schemeIsSMulRegular {f : R} {U : (Spec R).Opens}
    (hle : U ≤ schemeBasicOpen f) : IsSMulRegular Γ(M, U) f :=
  M.isSMulRegular_of_le_basicOpen (U := U) hle

structure Aux (V : (Spec R).Opens) where
  existence (f : R) (hf : schemeBasicOpen f ≤ V) (s : Γ(M, schemeBasicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, V)), M.presheaf.map (homOfLE hf).op t = f ^ n • s
  uniqueness (f : R) (hf : schemeBasicOpen f ≤ V) (t : Γ(M, V)) :
    M.presheaf.map (.op <| homOfLE hf) t = (0 : Γ(M, schemeBasicOpen f)) →
    ∃ (n : ℕ), f ^ n • t = 0

lemma Aux.of_le {M : (Spec R).Modules} {V : (Spec R).Opens} (g : R) (hg : schemeBasicOpen g ≤ V)
    (hV : Aux M V) :
    Aux M (schemeBasicOpen g) where
  existence f hfg s := by
    obtain ⟨n, t, ht⟩ := hV.existence f (le_trans hfg hg) s
    use n, M.presheaf.map (homOfLE hg).op t
    simp [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, ht]
  uniqueness f hfg t ht := by
    obtain ⟨n, t', ht'⟩ := hV.existence g hg t
    obtain ⟨m, hm⟩ := hV.uniqueness _ (le_trans hfg hg) t' <| by
      rw [← homOfLE_comp hfg hg, op_comp, M.presheaf.map_comp_apply, ht', M.map_smul_Spec, ht]
      simp
    refine ⟨m, ((schemeIsSMulRegular M le_rfl).pow n).right_eq_zero_of_smul ?_⟩
    simp [smul_comm, ← ht', ← M.map_smul_Spec, hm]

lemma Aux.of_eq_iSup_basicOpen {M : (Spec R).Modules} (V : (Spec R).Opens)
    {ι : Type*} [Finite ι] (g : ι → R) (hg : V = ⨆ i, schemeBasicOpen (g i))
    (h₁ : ∀ (i : ι), Aux M (schemeBasicOpen (g i))) :
    Aux M V := by
  have h₂ (i j : ι) : Aux M (schemeBasicOpen (g i * g j)) :=
    .of_le _ (schemeBasicOpen_mul_le_left _ _) (h₁ i)
  have hgle (i : ι) : schemeBasicOpen (g i) ≤ V := by rw [hg]; exact le_iSup_of_le _ le_rfl
  have hug (i : ι) (m : ℕ) :
      IsUnit (algebraMap R (Module.End R Γ(M, schemeBasicOpen (g i))) (g i ^ m)) := by
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (g i) le_rfl).pow m

  refine ⟨fun f hf s ↦ ?_, fun f hf t hs ↦ ?_⟩
  · have hfgi (i : ι) : schemeBasicOpen (f * g i) ≤ schemeBasicOpen (g i) := schemeBasicOpen_mul_le_right f (g i)
    let s' (i : ι) : Γ(M, schemeBasicOpen (f * g i)) :=
      M.presheaf.map (homOfLE <| schemeBasicOpen_mul_le_left f (g i)).op s

    obtain ⟨N, t, ht⟩ : ∃ (N : ℕ) (t : ∀ i, Γ(M, schemeBasicOpen (g i))),
        ∀ i, f ^ N • s' i = M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_right f (g i))).op (t i) := by
      have (i : ι) : ∃ (n : ℕ) (t : Γ(M, schemeBasicOpen (g i))),
          f ^ n • s' i = M.presheaf.map (homOfLE (hfgi i)).op t := by
        obtain ⟨n, t', ht'⟩ := (h₁ i).existence (f * g i) (hfgi i) (s' i)
        rw [mul_pow, mul_smul, smul_comm] at ht'
        obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv (hug i n)
        use n, ψ t'
        apply (schemeIsSMulRegular M (schemeBasicOpen_mul_le_right f (g i))).pow n
        dsimp
        rw [← ht', ← Scheme.Modules.map_smul_Spec]
        congr 1
        exact congr($hψ t').symm
      choose n t' ht' using this
      have (i : ι) : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have hN (i : ι) : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by grind
      refine ⟨⨆ i, n i, fun i ↦ f ^ ((⨆ i, n i) - n i) • t' i, fun i ↦ ?_⟩
      conv_lhs => rw [hN i]
      rw [pow_add, mul_smul, ht', M.map_smul_Spec]

    obtain ⟨K, hK⟩ : ∃ (K : ℕ), ∀ (i j : ι),
        M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_left (g i) (g j))).op (f ^ K • t i) =
          M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_right (g i) (g j))).op (f ^ K • t j) := by
      have (i j : ι) : ∃ (m : ℕ),
          M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_left (g i) (g j))).op (f ^ m • t i) =
            M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_right (g i) (g j))).op (f ^ m • t j) := by
        have := (h₂ i j).uniqueness (f * (g i * g j)) (schemeBasicOpen_mul_le_right _ _)
          (M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_left (g i) (g j))).op (t i) -
            M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_right (g i) (g j))).op (t j)) ?_
        · obtain ⟨m, hm⟩ := this
          use m
          apply (schemeIsSMulRegular M le_rfl).pow m
          simpa [M.map_smul_Spec _ (f ^ m), ← mul_smul, ← mul_smul, ← mul_pow, ← mul_comm f,
            smul_sub, sub_eq_zero] using hm
        · have hfgigi : schemeBasicOpen (f * (g i * g j)) ≤ schemeBasicOpen (f * g i) := by
            rw [← mul_assoc]
            exact schemeBasicOpen_mul_le_left _ _
          have hfgigj : schemeBasicOpen (f * (g i * g j)) ≤ schemeBasicOpen (f * g j) := by
            rw [mul_comm (g i) (g j), ← mul_assoc]
            exact schemeBasicOpen_mul_le_left _ _
          rw [map_sub, ← M.presheaf.map_comp_apply, ← op_comp, ← M.presheaf.map_comp_apply,
            ← op_comp, homOfLE_comp, homOfLE_comp, ← homOfLE_comp hfgigi (hfgi i),
            ← homOfLE_comp hfgigj (hfgi j), op_comp, M.presheaf.map_comp_apply, ← ht i,
            M.map_smul_Spec, ← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, op_comp,
            M.presheaf.map_comp_apply, ← ht j, M.map_smul_Spec, ← M.presheaf.map_comp_apply,
            ← op_comp, homOfLE_comp]
          simp
      choose m hm using this
      let K := ⨆ i, ⨆ j, m i j
      refine ⟨K, fun i j ↦ ?_⟩
      have : m i j ≤ K :=
        le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) _)
      have : K = (K - m i j) + m i j := by lia
      rw [this, pow_add, mul_smul, mul_smul, M.map_smul_Spec, M.map_smul_Spec _ (f ^ (K - m i j)),
        hm i j]

    refine ⟨N + K, ?_⟩
    have := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ (fun i ↦ schemeBasicOpen (g i)) V
      (fun i ↦ homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl)) (by simp [hg])
      (fun i ↦ f ^ K • t i) ?_
    · obtain ⟨a, ha, -⟩ := this
      use a
      refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i ↦ schemeBasicOpen (f * g i)) _
          (fun i ↦ homOfLE (schemeBasicOpen_mul_le_left f (g i))) ?_ _ _ ?_
      · rw [left_eq_inf.mpr hf, hg, inf_iSup_eq]
        simp_rw [schemeBasicOpen_mul]
        exact le_rfl
      · intro i
        rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp (schemeBasicOpen_mul_le_right _ _) (hgle i), op_comp, M.presheaf.map_comp_apply,
          M.map_smul_Spec, ha, M.map_smul_Spec, pow_add, mul_smul, smul_comm, ht i]
    · intro i j
      have : Function.Injective (M.presheaf.map (eqToHom <| (schemeBasicOpen_mul (g i) (g j))).op) :=
        ConcreteCategory.injective_of_mono_of_preservesPullback _
      apply this
      dsimp [Opens.infLELeft, Opens.infLERight]
      simp_rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
      exact hK i j
  · have (i : ι) : ∃ (n : ℕ), M.presheaf.map (homOfLE (hgle i)).op (f ^ n • t) = 0 := by
      have := (h₁ i).uniqueness (f * g i) (schemeBasicOpen_mul_le_right f (g i))
        (M.presheaf.map (homOfLE (hgle i)).op t) ?_
      · obtain ⟨n, hn⟩ := this
        use n
        rw [mul_pow, mul_comm, mul_smul, ← Scheme.Modules.map_smul_Spec] at hn
        exact ((schemeIsSMulRegular M le_rfl).pow n).right_eq_zero_of_smul hn
      · rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp ((schemeBasicOpen_mul_le_left f (g i))) hf, op_comp, M.presheaf.map_comp_apply]
        simp [hs]
    choose n hn using this
    use ⨆ i, n i
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i ↦ schemeBasicOpen (g i)) _
      (fun i ↦ homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl))
    · simp [hg]
    · intro i
      have : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by lia
      rw [this, pow_add, mul_smul, Scheme.Modules.map_smul_Spec, hn i]
      simp

lemma isLocalizing_iff_aux (M : (Spec R).Modules) :
    IsLocalizing (modulesSpecToSheaf.obj M) ↔ Aux M ⊤ := by
  let φ (f : R) := ((modulesSpecToSheaf.obj M).obj.map (schemeBasicOpen f).leTop.op).hom
  refine ⟨fun h ↦ ?_, fun h f ↦ IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_⟩
  · have hf (f : R) : IsLocalizedModule.Away f (φ f) := h f
    refine ⟨fun f hle s ↦ ?_, fun f hle s hs ↦ ?_⟩
    · obtain ⟨n, y, hy⟩ := (hf f).surj _ _ s
      use n, y, hy.symm
    · obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f) (φ f)).mp hs
      use n, hn
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro x
    obtain ⟨n, t, ht⟩ := h.existence _ _ x
    use n, t, ht.symm
  · intro x hx
    obtain ⟨n, hn⟩ := h.uniqueness _ _ _ hx
    use n, hn

theorem aux_of_isCompact (V : (Spec R).Opens) (hV : IsCompact (V : Set (Spec R)))
    (h : IsLocalizing (modulesSpecToSheaf.obj M)) : Aux M V := by
  obtain ⟨ι, hι, g, hg⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact V hV
  let := hι
  exact Aux.of_eq_iSup_basicOpen V g hg (fun i =>
    Aux.of_le (g i) le_top ((isLocalizing_iff_aux M).mp h))

variable {M}

def res (U V : (Spec R).Opens) (h : U ≤ V) : Γ(M,V) →ₗ[R] Γ(M,U) :=
  ((modulesSpecToSheaf.obj M).obj.map (homOfLE h).op).hom

lemma res_comp {U V W : (Spec R).Opens} (h : U ≤ V) (k : V ≤ W) (s : Γ(M,W)) :
    res U V h (M := M) (res V W k s) = res U W (h.trans k) s := by
  exact (M.presheaf.map_comp_apply (homOfLE k).op (homOfLE h).op s).symm

lemma eq_zero_of_cover {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i)) (s : Γ(M,U))
    (h : ∀ i, res (schemeBasicOpen (g i)) U (hU ▸ le_iSup_of_le i le_rfl) s = 0) : s = 0 := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => schemeBasicOpen (g i)) U
    (fun i => homOfLE (hU ▸ le_iSup_of_le i le_rfl)) (by rw [hU])
  intro i
  change res (schemeBasicOpen (g i)) U _ s = res (schemeBasicOpen (g i)) U _ 0
  rw [map_zero]
  exact h i

lemma power_in_ideal_of_generator_powers {ι : Type*} [Finite ι]
    (g : ι → R) (J : Ideal R) (h : ∀ i, ∃ n : ℕ, g i ^ n ∈ J) :
    ∃ n : ℕ, Ideal.span (Set.range g) ^ n ≤ J := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact h i
  · exact Submodule.fg_span (Set.finite_range g)

lemma kernel_is_torsion {ι : Type*} [Finite ι] (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i))
    (hloc : IsLocalizing (modulesSpecToSheaf.obj M)) (s : Γ(M,⊤))
    (hs : res U ⊤ le_top s = 0) :
    ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0 := by
  let J : Ideal R := (LinearMap.toSpanSingleton R Γ(M,⊤) s).ker
  have hgen : ∀ i, ∃ n : ℕ, g i ^ n ∈ J := by
    intro i
    apply ((isLocalizing_iff_aux M).mp hloc).uniqueness (g i) le_top s
    change res (schemeBasicOpen (g i)) ⊤ le_top s = 0
    rw [← res_comp (hU ▸ le_iSup_of_le i le_rfl) le_top, hs, map_zero]
  obtain ⟨n,hn⟩ := power_in_ideal_of_generator_powers g J hgen
  exact ⟨n,fun a ha => hn ha⟩

lemma torsion_free {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i)) (s : Γ(M,U))
    (hs : ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0) : s = 0 := by
  obtain ⟨n,hn⟩ := hs
  apply eq_zero_of_cover g U hU s
  intro i
  have hm : g i ^ n ∈ Ideal.span (Set.range g) ^ n :=
    Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) n
  have h := congrArg (res (schemeBasicOpen (g i)) U (hU ▸ le_iSup_of_le i le_rfl)) (hn _ hm)
  rw [map_smul, map_zero] at h
  exact ((schemeIsSMulRegular M le_rfl).pow n).right_eq_zero_of_smul h

lemma torsion_in_kernel {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i)) (s : Γ(M,⊤))
    (hs : ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0) :
    res U ⊤ le_top s = 0 := by
  apply torsion_free g U hU
  obtain ⟨n,hn⟩ := hs
  refine ⟨n,fun a ha => ?_⟩
  rw [← map_smul, hn a ha, map_zero]

lemma cokernel_is_torsion {ι : Type*} [Finite ι] (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i)) (hU' : IsCompact (U : Set (Spec R)))
    (hloc : IsLocalizing (modulesSpecToSheaf.obj M)) (s : Γ(M,U)) :
    ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n,
      a • s ∈ (res U ⊤ le_top (M := M)).range := by
  let J : Ideal R := (res U ⊤ le_top (M := M)).range.comap
    (LinearMap.toSpanSingleton R Γ(M,U) s)
  have hgen : ∀ i, ∃ n : ℕ, g i ^ n ∈ J := by
    intro i
    let hgi : schemeBasicOpen (g i) ≤ U := hU ▸ le_iSup_of_le i le_rfl
    obtain ⟨m,t,ht⟩ := ((isLocalizing_iff_aux M).mp hloc).existence (g i) le_top
      (res (schemeBasicOpen (g i)) U hgi s)
    have hzero : res (schemeBasicOpen (g i)) U hgi (res U ⊤ le_top t - g i ^ m • s) = 0 := by
      rw [map_sub, map_smul, res_comp]
      exact sub_eq_zero.mpr ht
    obtain ⟨n,hn⟩ := (aux_of_isCompact M U hU' hloc).uniqueness (g i) hgi _ hzero
    refine ⟨n+m, ?_⟩
    change g i ^ (n+m) • s ∈ (res U ⊤ le_top (M := M)).range
    refine ⟨g i ^ n • t, ?_⟩
    rw [map_smul, pow_add, mul_smul]
    exact sub_eq_zero.mp (by simpa only [smul_sub] using hn)
  obtain ⟨n,hn⟩ := power_in_ideal_of_generator_powers g J hgen
  exact ⟨n,fun a ha => hn ha⟩

end AffineDenominators

end

namespace TildeFlasque
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AffineDenominators AdicInjective InjectiveRange
universe u
variable {R : CommRingCat.{u}} [IsNoetherianRing R]
variable (M : (Spec R).Modules)

theorem top_surjective (hloc : IsLocalizing (modulesSpecToSheaf.obj M))
    [Module.Injective R Γ(M,⊤)] (U : (Spec R).Opens) :
    Function.Surjective (res U ⊤ le_top (M := M)) := by
  have hU : IsCompact (U : Set (Spec R)) := NoetherianSpace.isCompact _
  obtain ⟨ι, hι, g, hg⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact U hU
  let := hι
  let I : Ideal R := Ideal.span (Set.range g)
  let r := res U ⊤ le_top (M := M)
  have hk : r.ker = adicTorsion I Γ(M,⊤) := by
    ext s
    change r s = 0 ↔ s ∈ adicTorsion I Γ(M,⊤)
    rw [mem_adicTorsion]
    exact ⟨kernel_is_torsion g U hg hloc s, torsion_in_kernel g U hg s⟩
  have hi : Module.Injective R (adicTorsion I Γ(M,⊤)) := adicTorsion_injective I Γ(M,⊤)
  let : Module.Injective R r.ker := Module.Baer.injective
    (Module.Baer.of_equiv (LinearEquiv.ofEq _ _ hk.symm) (Module.Baer.of_injective hi))
  apply surjective_of_torsion_cokernel I r
  · exact fun s => cokernel_is_torsion g U hg hU hloc s
  · exact fun s => torsion_free g U hg s

theorem flasque_of_injective_global (hloc : IsLocalizing (modulesSpecToSheaf.obj M))
    [Module.Injective R Γ(M,⊤)] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨t,ht⟩ := top_surjective M hloc V.unop s
    refine ⟨res U.unop ⊤ le_top t, ?_⟩
    change res V.unop U.unop (leOfHom i.unop) (res U.unop ⊤ le_top t) = s
    rw [res_comp]
    exact ht

instance tilde_injective_isFlasque (N : ModuleCat.{u} R) [Module.Injective R N] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde N)) := by
  let : Module.Injective R Γ(tilde N,⊤) := Module.Baer.injective
    (Module.Baer.of_equiv (asIso (tilde.toOpen N ⊤)).toLinearEquiv
      (Module.Baer.of_injective inferInstance))
  exact flasque_of_injective_global (tilde N) (isLocalizing_tilde N)

end TildeFlasque

namespace TildeExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {R : CommRingCat.{u}}

instance map_mono {M N : ModuleCat.{u} R} (f : M ⟶ N) [Mono f] : Mono (tilde.map f) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U s t h
  apply Subtype.ext
  funext x
  haveI : x.1.asIdeal.IsPrime := x.1.isPrime
  apply LocalizedModule.map_injective x.1.asIdeal.primeCompl f.hom
    ((ModuleCat.mono_iff_injective f).mp inferInstance)
  exact congrFun (congrArg Subtype.val h) x

instance preservesMonomorphisms : (tilde.functor R).PreservesMonomorphisms where
  preserves f _ := map_mono f

instance preservesHomology : (tilde.functor R).PreservesHomology :=
  (tilde.functor R).preservesHomology_of_preservesMonos_and_cokernels

end TildeExact

namespace ModuleGrothendieck
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] (R₀ : Cᵒᵖ ⥤ RingCat.{u})

instance presheafAB5 : AB5 (PresheafOfModules.{u} R₀) where
  ofShape J _ _ := HasExactColimitsOfShape.domain_of_functor J
    (PresheafOfModules.toPresheaf R₀)

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}]

instance sheafAB5 : AB5 (SheafOfModules.{u} R) where
  ofShape K _ _ :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K

lemma freeSheafSeparating :
    ObjectProperty.IsSeparating (.ofObj (fun U : C =>
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        ((PresheafOfModules.free R.obj).obj (yoneda.obj U)))) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  intro M N f g h
  apply (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map_injective
  apply PresheafOfModules.freeYoneda.isSeparating R.obj
  intro P hP a
  obtain ⟨U⟩ := hP
  obtain ⟨b, rfl⟩ := (adj.homEquiv _ _).surjective a
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_right]
  exact congrArg (adj.homEquiv _ _) (h _ ⟨U⟩ b)

instance sheafHasSeparator : HasSeparator (SheafOfModules.{u} R) :=
  ⟨⟨∐ (fun U : C => (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))),
    (freeSheafSeparating R).isSeparator_coproduct⟩⟩

instance sheafGrothendieck : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) where

theorem enoughInjectives : EnoughInjectives (SheafOfModules.{u} R) := inferInstance

end ModuleGrothendieck

namespace ModuleFlasque
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

lemma freeMap_mono {F G : (Opens X)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [Mono f] :
    Mono ((PresheafOfModules.free R.obj).map f) := by
  apply PresheafOfModules.mono_of_injective
  intro W
  change Function.Injective (Finsupp.mapDomain (f.app W))
  exact Finsupp.mapDomain_injective ((CategoryTheory.mono_iff_injective (f.app W)).mp
    inferInstance)

lemma freeYoneda_naturality {M : PresheafOfModules.{u} R.obj} {U V : Opens X}
    (i : U ⟶ V) (f : (PresheafOfModules.free R.obj).obj (yoneda.obj V) ⟶ M) :
    PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.free R.obj).map (yoneda.map i) ≫ f) =
      M.map i.op (PresheafOfModules.freeYonedaEquiv f) := by
  have h := (PresheafOfModules.freeAdjunction R.obj).homEquiv_naturality_left
    (yoneda.map i) f
  simp only [PresheafOfModules.freeAdjunction_homEquiv] at h
  exact (congrArg yonedaEquiv h).trans
    (yonedaEquiv_naturality (PresheafOfModules.freeHomEquiv f) i).symm

end ModuleFlasque

namespace ModuleSheafExact
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]

instance toSheafPreservesColimit {K : Type u} [Category.{u} K]
    (D : K ⥤ SheafOfModules.{u} R) : PreservesColimit D (SheafOfModules.toSheaf R) := by
  let F := PresheafOfModules.sheafification (𝟙 R.obj)
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let H := SheafOfModules.toSheaf R
  let adj : F ⊣ G := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have : PreservesColimitsOfSize.{u,u} (F ⋙ H) :=
    inferInstanceAs (PreservesColimitsOfSize.{u,u}
      (PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat))
  have : PreservesColimit (D ⋙ G ⋙ F) H :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves F (colimit.isColimit (D ⋙ G)))
      (isColimitOfPreserves (F ⋙ H) (colimit.isColimit (D ⋙ G)))
  exact preservesColimit_of_iso_diagram H
    ((Functor.isoWhiskerLeft D (asIso adj.counit)) ≪≫ D.rightUnitor)

instance toSheafPreservesColimits :
    PreservesColimitsOfSize.{u,u} (SheafOfModules.toSheaf.{u} R) where
  preservesColimitsOfShape := ⟨fun {_} => inferInstance⟩

theorem shortExact_map {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf R)).ShortExact := hS.map_of_exact _

end ModuleSheafExact

namespace FlasqueCohomology
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Abelian
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def sectionsTopEquiv (M : SheafOfModules.{u} R) : M.sections ≃ M.val.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun t := PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op t)
    (by
      intro U V i
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) t)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE le_top).op
  right_inv t := by
    change M.val.map (𝟙 (op ⊤)) t = t
    rw [M.val.map_id]
    rfl

def globalHomEquiv (M : SheafOfModules.{u} R) :
    (SheafOfModules.unit R ⟶ M) ≃ M.val.obj (op ⊤) :=
  M.unitHomEquiv.trans (sectionsTopEquiv R M)

lemma globalHomEquiv_comp {M N : SheafOfModules.{u} R}
    (f : SheafOfModules.unit R ⟶ M) (g : M ⟶ N) :
    globalHomEquiv R N (f ≫ g) = g.val.app (op ⊤) (globalHomEquiv R M f) := rfl

theorem globalHom_surjective {S : ShortComplex (SheafOfModules.{u} R)}
    (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)] :
    Function.Surjective (fun f : SheafOfModules.unit R ⟶ S.X₂ => f ≫ S.g) := by
  have h := ModuleSheafExact.shortExact_map R hS
  let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₁) :=
    ‹TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)›
  have he := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) h
  have hs := (AddCommGrpCat.epi_iff_surjective
    (((SheafOfModules.toSheaf R).map S.g).hom.app (op ⊤))).mp he
  intro f
  obtain ⟨t, ht⟩ := hs (globalHomEquiv R S.X₃ f)
  let t' : S.X₂.val.obj (op ⊤) := t
  have ht' : S.g.val.app (op ⊤) t' = globalHomEquiv R S.X₃ f := ht
  refine ⟨(globalHomEquiv R S.X₂).symm t', ?_⟩
  apply (globalHomEquiv R S.X₃).injective
  erw [globalHomEquiv_comp, Equiv.apply_symm_apply]
  exact ht'

instance moduleSheafHasExt : HasExt.{u+1} (SheafOfModules.{u} R) :=
  HasExt.standard _

end FlasqueCohomology

namespace RestrictionExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance restriction_flasque (M : Y.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M)] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (M.restrict f)) where
  epi {U V} i := by
    change Epi (((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).obj.map
      (f.opensFunctor.map i.unop).op)
    exact TopCat.Presheaf.IsFlasque.epi _

end RestrictionExact

namespace AffineSchemeCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open Scheme.Modules
universe u

def restrictionEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (restrictFunctor e.hom) (restrictFunctor e.inv)
    ((restrictFunctorId (X := Y)).symm ≪≫ (restrictFunctorCongr e.inv_hom_id).symm ≪≫
      restrictFunctorComp e.inv e.hom)
    ((restrictFunctorComp e.hom e.inv).symm ≪≫ restrictFunctorCongr e.hom_inv_id ≪≫
      restrictFunctorId (X := X))

local instance hasExtScheme (X : Scheme.{u}) : HasExt.{u+1} X.Modules := HasExt.standard _

end AffineSchemeCohomology

namespace ExtSectionComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe w w' v v' u u'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{w} C] [HasExt.{w'} D] {A : C} {B : D} (e : B ⟶ F.obj A)

def mapFrom (Y : C) (n : ℕ) : Ext.{w} A Y n →+ Ext.{w'} B (F.obj Y) n :=
  ((Ext.mk₀ e).precomp (F.obj Y) (zero_add n)).comp (F.mapExtAddHom A Y n)

lemma mapFrom_apply (Y : C) (n : ℕ) (x : Ext.{w} A Y n) :
    mapFrom F e Y n x = (Ext.mk₀ e).comp (x.mapExactFunctor F) (zero_add n) := rfl

@[simp] lemma mapFrom_mk₀ {Y : C} (f : A ⟶ Y) :
    mapFrom F e Y 0 (Ext.mk₀ f) = Ext.mk₀ (e ≫ F.map f) := by
  simp only [mapFrom_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

lemma mapFrom_comp {Y Z : C} {n m k : ℕ} (x : Ext.{w} A Y n)
    (y : Ext.{w} Y Z m) (h : n+m=k) :
    mapFrom F e Z k (x.comp y h) =
      (mapFrom F e Y n x).comp (y.mapExactFunctor F) h := by
  simp only [mapFrom_apply, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add _) h (by omega)).symm

theorem mapFrom_bijective [EnoughInjectives C]
    (hhom : ∀ Y : C, Function.Bijective (fun f : A ⟶ Y => e ≫ F.map f))
    (hacyclic : ∀ (I : C) [Injective I] (n : ℕ)
      (x : Ext.{w'} B (F.obj I) (n+1)), x = 0)
    (Y : C) (n : ℕ) : Function.Bijective (mapFrom F e Y n) := by
  induction n generalizing Y with
  | zero =>
    constructor
    · intro x y h
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
      obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
      rw [mapFrom_mk₀, mapFrom_mk₀] at h
      exact congrArg Ext.mk₀ ((hhom Y).injective ((Ext.mk₀_bijective _ _).injective h))
    · intro x
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
      obtain ⟨g, rfl⟩ := (hhom Y).surjective f
      exact ⟨Ext.mk₀ g, mapFrom_mk₀ F e g⟩
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    let : Injective S.X₂ := I.injective
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (mapFrom F e S.X₂ n) (mapFrom F e S.X₃ n) (mapFrom F e S.X₁ (n+1))
      ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hS n (n+1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' B (hS.map F) n (n+1) rfl))
      (ih _).surjective (ih _)
      (fun x => Ext.covariant_sequence_exact₁ A hS x (Ext.eq_zero_of_injective _) rfl)
      (fun x => Ext.covariant_sequence_exact₁ B (hS.map F) x (hacyclic S.X₂ n _) rfl)
    · ext x
      symm
      change mapFrom F e _ _ (x.comp (Ext.mk₀ S.g) (add_zero n)) =
        (mapFrom F e _ _ x).comp (Ext.mk₀ (F.map S.g)) (add_zero n)
      rw [mapFrom_comp, Ext.mapExactFunctor_mk₀]
    · ext x
      symm
      change mapFrom F e _ _ (x.comp hS.extClass rfl) =
        (mapFrom F e _ _ x).comp (hS.map F).extClass rfl
      rw [mapFrom_comp, Ext.mapExactFunctor_extClass]
      rfl

end ExtSectionComparison

namespace RestrictionCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open ModuleFlasque FlasqueCohomology
universe u
variable {X : Scheme.{u}} (U : X.Opens)

local instance hasExtScheme (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

end RestrictionCohomology

namespace ModuleMayerVietoris
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u w
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def freeOpenFunctor : Opens X ⥤ SheafOfModules.{u} R :=
  yoneda ⋙ PresheafOfModules.free R.obj ⋙ PresheafOfModules.sheafification (𝟙 R.obj)

end ModuleMayerVietoris

namespace FiniteCoverCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]

local instance hasExtScheme (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

end FiniteCoverCohomology

namespace FreeOpenUnit
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque FlasqueCohomology
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

end FreeOpenUnit

namespace FiniteCoverCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

local instance hasExtScheme' (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

end FiniteCoverCohomology

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FiniteGlobalPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FiniteGlobalPresentation
noncomputable section
universe u v₁ v₂ u₁ u₂
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponent.CoherentAffineFinite

theorem tilde_exists_finitePresentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    (N : ModuleCat R) [Module.Finite R N] :
    ∃ P : (tilde N).Presentation, P.IsFinite := by
  classical
  obtain ⟨s,hs⟩ := Module.Finite.fg_top (R := R) (M := N)
  let K := LinearMap.ker (Finsupp.linearCombination (M := N) R ((↑) : s → N))
  obtain ⟨t,ht⟩ := IsNoetherian.noetherian K
  let P := presentationTilde N (s : Set N) hs (t : Set (s →₀ R)) ht
  have : P.IsFinite := by
    constructor
    · constructor
      change Finite s
      infer_instance
    · constructor
      change Finite t
      infer_instance
  exact ⟨P,inferInstance⟩

end
end PiExponent.FiniteGlobalPresentation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPushforwardAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ClosedPushforwardAffine
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CoherentAffineFinite FiniteGlobalPresentation
variable {X Y : Scheme.{0}}

def transportPresentation {Z : Scheme.{0}}
    {M N : SheafOfModules Z.ringCatSheaf} (e : M ≅ N) (P : M.Presentation) :
    N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

end
end PiExponent.ClosedPushforwardAffine

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPushforwardCoherent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ClosedPushforward

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma sections_empty (M : X.Modules) (U : X.Opens) (hU : U = ⊥) :
    Subsingleton (M.val.obj (op U)) := by
  exact AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Sheaf.isTerminalOfEqEmpty ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj M) hU).isZero

open PiExponent.CoherentAffineFinite PiExponent.FiniteGlobalPresentation
open PiExponent.ClosedPushforwardAffine

end PiExponentSeshadri.ClosedPushforward

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedImmersionSerreTransfer
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
abbrev schemeUnit (Z : Scheme.{u}) : Z.Modules :=
  SheafOfModules.unit Z.ringCatSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def structureMap : schemeUnit Y ⟶
    (Scheme.Modules.pushforward f).obj (schemeUnit X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

lemma globalHom_push (M : X.Modules) (g : schemeUnit X ⟶ M) :
    globalHomEquiv Y.ringCatSheaf ((Scheme.Modules.pushforward f).obj M)
      (structureMap f ≫ (Scheme.Modules.pushforward f).map g) =
    globalHomEquiv X.ringCatSheaf M g := by
  change (g.val.app (op ⊤)) ((f.app ⊤) 1) = (g.val.app (op ⊤)) (1 : Γ(X,⊤))
  rw [map_one]
  rfl

instance pushforward_flasque (M : X.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pushforward f).obj M)) :=
  TopCat.Sheaf.IsFlasque.pushforward_isFlasque
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) f.base

local instance instHasExtModules_solutions_1 : HasExt.{u+1} Y.Modules := HasExt.standard _

variable [PreservesFiniteColimits (Scheme.Modules.pushforward f)]

local instance instHasExtModules_solutions_r5471f6_1 : HasExt.{u+1} X.Modules := HasExt.standard _
def cohomologyMap (M : X.Modules) (n : ℕ) :
    Ext.{u+1} (C := X.Modules) (schemeUnit X) M n →+
      Ext.{u+1} (C := Y.Modules) (schemeUnit Y)
        ((Scheme.Modules.pushforward f).obj M) n :=
  PiExponentSeshadri.ExtSectionComparison.mapFrom
    (Scheme.Modules.pushforward f) (structureMap f) M n

end PiExponent.ClosedImmersionSerreTransfer

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveMonomialCechHigher
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveMonomialCechHigher

noncomputable section
open scoped BigOperators

variable {ι A K : Type*} [AddCommGroup A]

abbrev Cochain (ι A : Type*) (q : ℕ) := (Fin (q + 1) → ι) → A

end
end PiExponent.ProjectiveMonomialCechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechHigher
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechHigher

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open scoped BigOperators

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

def intersection {n : ℕ} (t : Fin n → J) : Opens X := ⨅ i, U (t i)

theorem intersectionLE {m n : ℕ} (t : Fin n → J) (f : Fin m → Fin n) :
    intersection U t ≤ intersection U (t ∘ f) :=
  le_iInf fun i => iInf_le (fun j => U (t j)) (f i)

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

end
end PiExponent.GeometrySupport.CechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerExact
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Cohomology
open CategoryTheory CategoryTheory.Abelian

def alternatingTrunc (a : ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (d+1), (-1 : ℤ)^i * a i

lemma alternatingTrunc_succ (a : ℕ → ℤ) (d : ℕ) :
    alternatingTrunc a (d+1) = alternatingTrunc a d + (-1 : ℤ)^(d+1) * a (d+1) := by
  exact Finset.sum_range_succ _ _

lemma finrank_middle_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (hfg : Function.Exact f g) :
    Module.finrank K V = Module.finrank K f.range + Module.finrank K g.range := by
  have hh := LinearMap.finrank_range_add_finrank_ker g
  rw [hfg.linearMap_ker_eq] at hh
  omega

universe w v u t
variable {K : Type t} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C]

def extEuler (E M : C) (d : ℕ) : ℤ :=
  alternatingTrunc (fun n => Module.finrank K (Ext E M n)) d

variable (E : C) {S : ShortComplex C} (hS : S.ShortExact)

def cohomologyMap₁ (n : ℕ) : Ext E S.X₁ n →ₗ[K] Ext E S.X₂ n :=
  (Ext.mk₀ S.f).postcompOfLinear K E (add_zero n)

def cohomologyMap₂ (n : ℕ) : Ext E S.X₂ n →ₗ[K] Ext E S.X₃ n :=
  (Ext.mk₀ S.g).postcompOfLinear K E (add_zero n)

def cohomologyBoundary (n : ℕ) : Ext E S.X₃ n →ₗ[K] Ext E S.X₁ (n+1) :=
  hS.extClass.postcompOfLinear K E rfl

include hS in
lemma cohomology_exact₂ (n : ℕ) :
    Function.Exact (cohomologyMap₁ (K := K) E (S := S) n)
      (cohomologyMap₂ (K := K) E (S := S) n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₂ E hS x
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.f) (add_zero n)).comp (Ext.mk₀ S.g) (add_zero n) = 0
    simp [Ext.mk₀_comp_mk₀]

lemma cohomology_exact₃ (n : ℕ) :
    Function.Exact (cohomologyMap₂ (K := K) E (S := S) n)
      (cohomologyBoundary (K := K) E hS n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₃ E hS x rfl
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.g) (add_zero n)).comp hS.extClass rfl = 0
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

lemma cohomology_exact₁ (n : ℕ) :
    Function.Exact (cohomologyBoundary (K := K) E hS n)
      (cohomologyMap₁ (K := K) E (S := S) (n+1)) := by
  intro x
  constructor
  · exact fun hx => Ext.covariant_sequence_exact₁ E hS x hx rfl
  · rintro ⟨y, rfl⟩
    change (y.comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero (n+1)) = 0
    rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]

theorem extEuler_add_of_boundary_zero (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₃ n))
    (hvan : cohomologyBoundary (K := K) E hS d = 0) :
    extEuler (K := K) E S.X₂ d =
      extEuler (K := K) E S.X₁ d + extEuler (K := K) E S.X₃ d := by
  classical
  let a (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₁ n)
  let b (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₂ n)
  let c (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₃ n)
  let f (n : ℕ) : ℤ := Module.finrank K (cohomologyMap₁ (K := K) E (S := S) n).range
  let g (n : ℕ) : ℤ := Module.finrank K (cohomologyMap₂ (K := K) E (S := S) n).range
  let h (n : ℕ) : ℤ := Module.finrank K (cohomologyBoundary (K := K) E hS n).range
  have hB (n : ℕ) (hn : n ≤ d) : b n = f n + g n := by
    let := hfinite₂ n hn
    dsimp only [b, f, g]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₂ (K := K) E hS n)
  have hC (n : ℕ) (hn : n ≤ d) : c n = g n + h n := by
    let := hfinite₃ n hn
    dsimp only [c, g, h]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₃ (K := K) E hS n)
  have hA0 : a 0 = f 0 := by
    have : Mono S.f := hS.mono_f
    dsimp only [a, f]
    exact_mod_cast (LinearMap.finrank_range_of_inj
      (f := cohomologyMap₁ (K := K) E (S := S) 0)
      (Ext.postcomp_mk₀_injective_of_mono E S.f)).symm
  have hA (n : ℕ) (hn : n+1 ≤ d) : a (n+1) = h n + f (n+1) := by
    let := hfinite₁ (n+1) hn
    dsimp only [a, h, f]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₁ (K := K) E hS n)
  have hind (n : ℕ) (hn : n ≤ d) :
      alternatingTrunc b n - alternatingTrunc a n - alternatingTrunc c n =
        (-1 : ℤ)^(n+1) * h n := by
    induction n with
    | zero => simp [alternatingTrunc, hB 0 hn, hC 0 hn, hA0]
    | succ n ih =>
      have hi := ih (by omega)
      simp only [alternatingTrunc_succ]
      calc
        _ = (alternatingTrunc b n - alternatingTrunc a n - alternatingTrunc c n) +
          (-1 : ℤ)^(n+1) * (b (n+1) - a (n+1) - c (n+1)) := by ring
        _ = _ := by rw [hi, hB (n+1) hn, hC (n+1) hn, hA n hn, pow_succ _ (n+1)]; ring
  have hd : h d = 0 := by
    dsimp only [h]
    rw [hvan, LinearMap.range_zero]
    rw [finrank_bot]
    rfl
  have hh := hind d le_rfl
  rw [hd, mul_zero] at hh
  change alternatingTrunc b d = alternatingTrunc a d + alternatingTrunc c d
  omega

include hS in

theorem extEuler_add (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₃ n))
    [Subsingleton (Ext E S.X₁ (d+1))] :
    extEuler (K := K) E S.X₂ d =
      extEuler (K := K) E S.X₁ d + extEuler (K := K) E S.X₃ d :=
  extEuler_add_of_boundary_zero E hS d hfinite₁ hfinite₂ hfinite₃ (Subsingleton.elim _ _)

end Cohomology

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_SupportedSheaf
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PiExponentSeshadri.FiniteSupport
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

lemma finite_closed_support_restriction_surjective
    (F : X.Sheaf AddCommGrpCat.{0}) (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (F.presheaf.stalk x))
    {U V : Opens X} (i : V ⟶ U) : Function.Surjective (F.obj.map i.op) := by
  classical
  intro s
  have hcS : IsClosed (S ∩ V) := by
    rw [← Set.biUnion_of_singleton (S ∩ (V : Set X))]
    exact (hfin.subset Set.inter_subset_left).isClosed_biUnion
      (fun x hx => hclosed x hx.1)
  let W : Opens X := U ⊓ ⟨(S ∩ V)ᶜ,hcS.isOpen_compl⟩
  let D : Bool → Opens X := fun b => if b then V else W
  let e : ∀ b, D b ⟶ U := fun b => homOfLE (by
    cases b
    · exact inf_le_left
    · exact i.le)
  have hcover : U ≤ ⨆ b, D b := by
    intro x hx
    by_cases hv : x ∈ V
    · exact Opens.mem_iSup.mpr ⟨true,hv⟩
    · exact Opens.mem_iSup.mpr ⟨false,hx,fun h => hv h.2⟩
  let t : ∀ b, F.obj.obj (op (D b)) := fun b => match b with
    | true => s
    | false => 0
  have hz : ∀ b c, b ≠ c → Subsingleton (F.obj.obj (op (D b ⊓ D c))) := by
    intro b c hbc
    apply sections_subsingleton_of_stalks
    intro x hx
    apply hsupp
    intro hs
    cases b <;> cases c
    · exact hbc rfl
    · exact hx.1.2 ⟨hs,hx.2⟩
    · exact hx.2.2 ⟨hs,hx.1⟩
    · exact hbc rfl
  have hcomp : TopCat.Presheaf.IsCompatible F.obj D t := by
    intro b c
    by_cases he : b = c
    · subst c; rfl
    · let := hz b c he
      exact Subsingleton.elim _ _
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' D U e hcover t hcomp
  exact ⟨a,ha true⟩

lemma finite_closed_support_flasque (F : X.Sheaf AddCommGrpCat.{0})
    (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (F.presheaf.stalk x)) : F.IsFlasque where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (finite_closed_support_restriction_surjective F S hfin hclosed hsupp i.unop)

end
end PiExponentSeshadri.FiniteSupport

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FiniteSupportLocalIso
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
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
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem stalk_subsingleton_of_localIso (M N : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (e : M.restrict U.ι ≅ N.restrict U.ι)
    [Subsingleton (N.presheaf.stalk x)] : Subsingleton (M.presheaf.stalk x) := by
  let a := (Scheme.Modules.restrictStalkNatIso U.ι ⟨x,hx⟩).app M
  let b := (Scheme.Modules.restrictStalkNatIso U.ι ⟨x,hx⟩).app N
  let d := (Scheme.Modules.toPresheaf U.toScheme ⋙
    TopCat.Presheaf.stalkFunctor Ab (⟨x,hx⟩ : U.toScheme)).mapIso e
  let c := a.symm ≪≫ d ≪≫ b
  constructor
  intro s t
  apply (ConcreteCategory.bijective_of_isIso c.hom).injective
  exact Subsingleton.elim (α := N.presheaf.stalk x) _ _

end PiExponent.CurveNormalizationDegree

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveNormalizationEuler
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem finite_middle {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K U] [Module.Finite K W]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (h : Function.Exact f g) :
    Module.Finite K V := by
  have he : Function.Exact f g.rangeRestrict := by
    intro x
    rw [Subtype.ext_iff]
    exact h x
  exact Module.Finite.of_exact he g.surjective_rangeRestrict

end PiExponent.CurveNormalizationDegree

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologySections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

theorem quasicoherent_pushforward_iso (e : X ≅ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward e.hom).obj M).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward e.hom).obj M
  let q : (Scheme.Modules.pushforward e.inv).obj N ≅ M :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app M ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app M ≪≫
      (Scheme.Modules.pushforwardId X).app M
  let j : N ≅ M.restrict e.inv :=
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app N).symm ≪≫
      (Scheme.Modules.restrictFunctor e.inv).mapIso q
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso j.symm inferInstance

abbrev affineToSpecModule [IsAffine X] (M : X.Modules) :=
  (Scheme.Modules.pushforward X.toSpecΓ).obj M

instance affineToSpecModule_quasicoherent [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : (affineToSpecModule M).IsQuasicoherent :=
  quasicoherent_pushforward_iso X.isoSpec M

theorem affine_sections_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r
      (((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.map
        (PrimeSpectrum.basicOpen r).leTop.op).hom) :=
  ((isIso_fromTildeΓ_iff_isLocalizing (affineToSpecModule M)).mp inferInstance) r

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry.BaseSections

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

lemma chart_image_top (U : X.Opens) : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

end PiExponentSeshadri.Geometry.BaseSections

namespace PiExponentSeshadri.Geometry.BaseSections
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

end PiExponentSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyLaurent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.LaurentTails
open LaurentPolynomial
open scoped LaurentPolynomial
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module K[T;T⁻¹] M] [IsScalarTower K K[T;T⁻¹] M]

omit [IsScalarTower K K[T;T⁻¹] M] in
lemma positive_tail (A : Submodule K M)
    (hA : ∀ x ∈ A, (T 1 : K[T;T⁻¹]) • x ∈ A) {x : M} (hx : x ∈ A) :
    ∀ n : ℕ, (T (n : ℤ) : K[T;T⁻¹]) • x ∈ A := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, add_comm (n : ℤ) 1, T_add, mul_smul]
      using hA _ ih

omit [IsScalarTower K K[T;T⁻¹] M] in
lemma negative_tail (B : Submodule K M)
    (hB : ∀ x ∈ B, (T (-1) : K[T;T⁻¹]) • x ∈ B) {x : M} (hx : x ∈ B) :
    ∀ n : ℕ, (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ B := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have he : -((n + 1 : ℕ) : ℤ) = -1 + -(n : ℤ) := by omega
    simpa only [he, T_add, mul_smul] using hB _ ih

theorem quotient_finite [Module.Finite K[T;T⁻¹] M]
    (A B : Submodule K M)
    (hA : ∀ x ∈ A, (T 1 : K[T;T⁻¹]) • x ∈ A)
    (hB : ∀ x ∈ B, (T (-1) : K[T;T⁻¹]) • x ∈ B)
    (locA : ∀ x : M, ∃ n : ℕ, (T (n : ℤ) : K[T;T⁻¹]) • x ∈ A)
    (locB : ∀ x : M, ∃ n : ℕ, (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ B) :
    Module.Finite K (M ⧸ (A ⊔ B)) := by
  classical
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := K[T;T⁻¹]) (M := M)
  choose a ha using fun i : Fin n => locA (s i)
  choose b hb using fun i : Fin n => locB (s i)
  let q := (A ⊔ B).mkQ
  let J := (i : Fin n) × ↥(Finset.Icc (-(b i : ℤ)) (a i : ℤ))
  let g : J → M ⧸ (A ⊔ B) := fun v => q ((T v.2.val : K[T;T⁻¹]) • s v.1)
  let W := Submodule.span K (Set.range g)
  have monomial (i : Fin n) (z : ℤ) : q ((T z : K[T;T⁻¹]) • s i) ∈ W := by
    by_cases hzA : (a i : ℤ) ≤ z
    · have he : z = ((z - a i).toNat : ℤ) + a i := by omega
      have hm : (T z : K[T;T⁻¹]) • s i ∈ A := by
        rw [he, T_add, mul_smul]
        exact positive_tail A hA (ha i) _
      have hq : q ((T z : K[T;T⁻¹]) • s i) = 0 :=
        (Submodule.Quotient.mk_eq_zero (A ⊔ B)).mpr ((show A ≤ A ⊔ B from le_sup_left) hm)
      rw [hq]; exact W.zero_mem
    · by_cases hzB : z ≤ -(b i : ℤ)
      · have he : z = -((-(b i : ℤ) - z).toNat : ℤ) + -(b i : ℤ) := by omega
        have hm : (T z : K[T;T⁻¹]) • s i ∈ B := by
          rw [he, T_add, mul_smul]
          exact negative_tail B hB (hb i) _
        have hq : q ((T z : K[T;T⁻¹]) • s i) = 0 :=
          (Submodule.Quotient.mk_eq_zero (A ⊔ B)).mpr ((show B ≤ A ⊔ B from le_sup_right) hm)
        rw [hq]; exact W.zero_mem
      · exact Submodule.subset_span ⟨⟨i,⟨z,Finset.mem_Icc.mpr (by omega)⟩⟩,rfl⟩
  have scalar_monomial (i : Fin n) (p : K[T;T⁻¹]) : q (p • s i) ∈ W := by
    induction p using LaurentPolynomial.induction_on' with
    | add p p' hp hp' => simpa only [add_smul, map_add] using W.add_mem hp hp'
    | C_mul_T z c =>
      rw [mul_smul, C_eq_algebraMap, algebraMap_smul, map_smul]
      exact W.smul_mem c (monomial i z)
  have spans : W = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨m,rfl⟩ := (A ⊔ B).mkQ_surjective x
    have hm : m ∈ Submodule.span K[T;T⁻¹] (Set.range s) := hs ▸ Submodule.mem_top
    have hp : ∀ p : K[T;T⁻¹], q (p • m) ∈ W := by
      induction hm using Submodule.span_induction with
      | mem m hm => obtain ⟨i,rfl⟩ := hm; exact scalar_monomial i
      | zero => intro p; simp
      | add x y hx hy ihx ihy =>
        intro p
        simpa only [smul_add, map_add] using W.add_mem (ihx p) (ihy p)
      | smul a x hx ih => intro p; simpa only [smul_smul] using ih (p * a)
    change q m ∈ W
    simpa only [one_smul] using hp 1
  exact Module.Finite.of_fg_top (spans ▸ Submodule.fg_span (Set.finite_range g))

end PiExponentSeshadri.LaurentTails

namespace PiExponentSeshadri.LaurentCech
open LaurentPolynomial
open scoped LaurentPolynomial Polynomial
variable {K N P Q : Type*} [Field K]
  [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  [Module K N] [Module K P] [Module K Q]
  [Module K[X] N] [Module K[X] P] [Module K[X] Q]
  [IsScalarTower K K[X] N] [IsScalarTower K K[X] P] [IsScalarTower K K[X] Q]

omit [IsScalarTower K K[X] P] in
theorem cokernel_finite [Module.Finite K[X] N]
    (f : N →ₗ[K[X]] Q) [IsLocalizedModule.Away (Polynomial.X : K[X]) f]
    (g : P →ₗ[K] Q)
    (inverse_coordinate : ∀ y : P,
      (Polynomial.X : K[X]) • g ((Polynomial.X : K[X]) • y) = g y)
    (opposite_denominators : ∀ x : Q, ∃ n : ℕ, ∃ y : P,
      ((Polynomial.X : K[X])^n) • g y = x) :
    Module.Finite K (Q ⧸ ((f.restrictScalars K).range ⊔ g.range)) := by
  let : Module K[T;T⁻¹] Q := IsLocalizedModule.module
    (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K[X] K[T;T⁻¹] Q :=
    IsLocalizedModule.isScalarTower_module (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K K[T;T⁻¹] Q := .of_algebraMap_smul (fun c x => by
    rw [← C_eq_algebraMap, ← Polynomial.toLaurent_C,
      ← algebraMap_eq_toLaurent, algebraMap_smul]
    exact algebraMap_smul K[X] c x)
  let : Module.Finite K[T;T⁻¹] Q :=
    Module.Finite.of_isLocalizedModule (.powers (Polynomial.X : K[X])) f
  have pos (n : ℕ) (x : Q) : (T (n : ℤ) : K[T;T⁻¹]) • x =
      ((Polynomial.X : K[X])^n) • x := by
    rw [← Polynomial.toLaurent_X_pow, ← algebraMap_eq_toLaurent, algebraMap_smul]
  have pos1 (x : Q) : (T 1 : K[T;T⁻¹]) • x = (Polynomial.X : K[X]) • x := by
    simpa only [Nat.cast_one, pow_one] using pos 1 x
  have cancel (n : ℕ) (x : Q) : (T (-(n : ℤ)) : K[T;T⁻¹]) •
      ((T (n : ℤ) : K[T;T⁻¹]) • x) = x := by
    rw [← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul]
  apply LaurentTails.quotient_finite (A := (f.restrictScalars K).range) (B := g.range)
  · rintro _ ⟨y,rfl⟩
    refine ⟨(Polynomial.X : K[X]) • y, ?_⟩
    change f ((Polynomial.X : K[X]) • y) = (T 1 : K[T;T⁻¹]) • f y
    rw [map_smul, pos1]
  · rintro _ ⟨y,rfl⟩
    refine ⟨(Polynomial.X : K[X]) • y, ?_⟩
    have h := congrArg (fun z : Q => (T (-1) : K[T;T⁻¹]) • z)
      (inverse_coordinate y)
    rw [← pos1] at h
    have hc (z : Q) : (T (-1) : K[T;T⁻¹]) • ((T 1 : K[T;T⁻¹]) • z) = z := by
      simpa only [Nat.cast_one] using cancel 1 z
    rw [hc] at h
    exact h
  · intro x
    obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away (Polynomial.X : K[X]) f).surj _ _ x
    refine ⟨n, y, ?_⟩
    change f y = (T (n : ℤ) : K[T;T⁻¹]) • x
    rw [pos]
    exact hy.symm
  · intro x
    obtain ⟨n,y,hy⟩ := opposite_denominators x
    refine ⟨n,y,?_⟩
    rw [← hy, ← pos n, cancel n]
end PiExponentSeshadri.LaurentCech

namespace PiExponentSeshadri.LaurentLattices

section
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

variable {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
  [Module K M] [IsScalarTower K K[T;T⁻¹] M]

lemma mem_boundedBelow (b : Basis ι K[T;T⁻¹] M) (l : ℤ) (x : M) :
    x ∈ boundedBelow b l ↔ ∀ i z, z < l → ((b.repr x) i).coeff z = 0 := by
  simp only [boundedBelow, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Finsupp.lapply_apply, AddMonoidAlgebra.mem_supported',
    Set.mem_Ici, not_le]

lemma mem_boundedAbove (b : Basis ι K[T;T⁻¹] M) (u : ℤ) (x : M) :
    x ∈ boundedAbove b u ↔ ∀ i z, u < z → ((b.repr x) i).coeff z = 0 := by
  simp only [boundedAbove, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Finsupp.lapply_apply, AddMonoidAlgebra.mem_supported',
    Set.mem_Iic, not_le]

lemma coeff_T_mul (p : K[T;T⁻¹]) (n z : ℤ) :
    (T n * p).coeff z = p.coeff (z-n) := by
  simp only [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  congr 1
  omega

lemma below_shift (b : Basis ι K[T;T⁻¹] M) (l : ℤ) {x : M}
    (hx : x ∈ boundedBelow b l) (n : ℕ) :
    (T (n : ℤ) : K[T;T⁻¹]) • x ∈ boundedBelow b l := by
  rw [mem_boundedBelow] at hx ⊢
  intro i z hz
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, coeff_T_mul]
  exact hx i _ (by omega)

lemma above_shift (b : Basis ι K[T;T⁻¹] M) (u : ℤ) {x : M}
    (hx : x ∈ boundedAbove b u) (n : ℕ) :
    (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ boundedAbove b u := by
  rw [mem_boundedAbove] at hx ⊢
  intro i z hz
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, coeff_T_mul]
  exact hx i _ (by omega)

theorem band_finite [Fintype ι] (b : Basis ι K[T;T⁻¹] M) (l u : ℤ) :
    Module.Finite K ↥(boundedBelow b l ⊓ boundedAbove b u) := by
  classical
  let W := boundedBelow b l ⊓ boundedAbove b u
  let J := ι × ↥(Finset.Icc l u)
  let φ : W →ₗ[K] (J → K) := LinearMap.pi (fun j =>
    (Finsupp.lapply j.2.val).comp ((AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap.comp
      ((((Finsupp.lapply j.1).comp b.repr.toLinearMap).restrictScalars K).comp W.subtype)))
  apply Module.Finite.of_injective φ
  intro x y hxy
  apply Subtype.ext
  apply b.repr.injective
  ext i z
  by_cases hzL : z < l
  · rw [(mem_boundedBelow b l x.val).mp x.property.1 i z hzL,
      (mem_boundedBelow b l y.val).mp y.property.1 i z hzL]
  · by_cases hzU : u < z
    · rw [(mem_boundedAbove b u x.val).mp x.property.2 i z hzU,
        (mem_boundedAbove b u y.val).mp y.property.2 i z hzU]
    · exact congrFun hxy (i,⟨z,Finset.mem_Icc.mpr (by omega)⟩)

lemma finite_generators_bounded [Fintype ι] {κ : Type*} [Fintype κ]
    (b : Basis ι K[T;T⁻¹] M) (s : κ → M) :
    ∃ l u : ℤ, ∀ j, s j ∈ boundedBelow b l ∧ s j ∈ boundedAbove b u := by
  classical
  let S : Set ℤ := ⋃ i, ⋃ j, (↑((b.repr (s j)) i).coeff.support : Set ℤ)
  have hS : S.Finite := Set.finite_iUnion fun i => Set.finite_iUnion fun j =>
    Finset.finite_toSet _
  obtain ⟨l,hl⟩ := hS.bddBelow
  obtain ⟨u,hu⟩ := hS.bddAbove
  refine ⟨l,u,fun j => ⟨?_,?_⟩⟩
  · rw [mem_boundedBelow]
    intro i z hz
    by_contra hn
    have hm : z ∈ S := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
      ⟨j,Finsupp.mem_support_iff.mpr hn⟩⟩
    exact (not_le.mpr hz) (hl hm)
  · rw [mem_boundedAbove]
    intro i z hz
    by_contra hn
    have hm : z ∈ S := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
      ⟨j,Finsupp.mem_support_iff.mpr hn⟩⟩
    exact (not_le.mpr hz) (hu hm)

theorem intersection_finite [Module.Finite K[T;T⁻¹] M]
    [Module.IsTorsionFree K[T;T⁻¹] M]
    (A B : Submodule K M) {κ τ : Type*} [Fintype κ] [Fintype τ]
    (s : κ → M) (t : τ → M)
    (hA : A ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • s j.1)))
    (hB : B ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • t j.1))) :
    Module.Finite K ↥(A ⊓ B) := by
  let b := Module.Free.chooseBasis K[T;T⁻¹] M
  obtain ⟨l,_,hs⟩ := finite_generators_bounded b s
  obtain ⟨_,u,ht⟩ := finite_generators_bounded b t
  have hbelow : A ≤ boundedBelow b l := hA.trans (Submodule.span_le.mpr (by
    rintro _ ⟨⟨j,n⟩,rfl⟩
    exact below_shift b l (hs j).1 n))
  have habove : B ≤ boundedAbove b u := hB.trans (Submodule.span_le.mpr (by
    rintro _ ⟨⟨j,n⟩,rfl⟩
    exact above_shift b u (ht j).2 n))
  let := band_finite b l u
  exact Module.Finite.of_injective (Submodule.inclusion (inf_le_inf hbelow habove))
    (Submodule.inclusion_injective _)

end

section
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

lemma quotient_finite (a : K[T;T⁻¹]) (ha : a ≠ 0) :
    Module.Finite K (K[T;T⁻¹] ⧸ Ideal.span {a}) := by
  have hlen := isFiniteLength_quotient_span_singleton K[T;T⁻¹]
    (mem_nonZeroDivisors_of_ne_zero ha)
  let := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
  let : IsArtinianRing (K[T;T⁻¹] ⧸ Ideal.span {a}) :=
    isArtinian_of_tower K[T;T⁻¹] inferInstance
  exact Module.finite_of_isArtinianRing K _

theorem torsion_finite {M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M] [Module.Finite K[T;T⁻¹] M]
    (hM : Module.IsTorsion K[T;T⁻¹] M) : Module.Finite K M := by
  obtain ⟨a,ha,hn⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  have hkill : Module.IsTorsionBy K[T;T⁻¹] M a := fun x =>
    Submodule.mem_annihilator.mp ha x trivial
  let hset : Module.IsTorsionBySet K[T;T⁻¹] M (Ideal.span {a}) :=
    (Module.isTorsionBySet_span_singleton_iff a).mpr hkill
  let := hset.module
  let : IsScalarTower K[T;T⁻¹] (K[T;T⁻¹] ⧸ Ideal.span {a}) M := hset.isScalarTower
  let : IsScalarTower K (K[T;T⁻¹] ⧸ Ideal.span {a}) M := hset.isScalarTower
  let : Module.Finite (K[T;T⁻¹] ⧸ Ideal.span {a}) M :=
    Module.Finite.of_restrictScalars_finite K[T;T⁻¹] _ M
  let := quotient_finite a (nonZeroDivisors.ne_zero hn)
  exact Module.Finite.trans (K[T;T⁻¹] ⧸ Ideal.span {a}) M
end

section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
  [Module K M] [IsScalarTower K K[T;T⁻¹] M]

theorem intersection_finite_general [Module.Finite K[T;T⁻¹] M]
    (A B : Submodule K M) {κ τ : Type*} [Fintype κ] [Fintype τ]
    (s : κ → M) (t : τ → M)
    (hA : A ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • s j.1)))
    (hB : B ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • t j.1))) :
    Module.Finite K ↥(A ⊓ B) := by
  let D := Submodule.torsion K[T;T⁻¹] M
  let q := D.mkQ.restrictScalars K
  let : Module.Finite K D := torsion_finite Submodule.torsion_isTorsion
  have ha : A.map q ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • q (s j.1))) := by
    apply (Submodule.map_mono hA).trans
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨j,rfl⟩,rfl⟩
    exact ⟨j, (D.mkQ.map_smul _ _).symm⟩
  have hb : B.map q ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • q (t j.1))) := by
    apply (Submodule.map_mono hB).trans
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨j,rfl⟩,rfl⟩
    exact ⟨j, (D.mkQ.map_smul _ _).symm⟩
  let := intersection_finite (A.map q) (B.map q) (fun i => q (s i))
    (fun i => q (t i)) ha hb
  let f : ↥(A ⊓ B) →ₗ[K] ↥(A.map q ⊓ B.map q) :=
    (q.comp (A ⊓ B).subtype).codRestrict _ (fun x =>
      ⟨Submodule.mem_map.mpr ⟨x.val,x.property.1,rfl⟩,
        Submodule.mem_map.mpr ⟨x.val,x.property.2,rfl⟩⟩)
  let g : f.ker →ₗ[K] D :=
    (((A ⊓ B).subtype.comp f.ker.subtype).codRestrict (D.restrictScalars K)
      (fun x => by
        have h : q x.val.val = 0 := congrArg Subtype.val x.property
        exact (Submodule.Quotient.mk_eq_zero D).mp h))
  let : Module.Finite K f.ker := Module.Finite.of_injective g (by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : D => (z : M)) h)
  let : Module.Finite K (↥(A ⊓ B) ⧸ f.ker) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient f.ker
end

open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K N Q : Type*} [Field K] [AddCommGroup N] [AddCommGroup Q]
  [Module K N] [Module K Q] [Module K[X] N] [IsScalarTower K K[X] N]
  [Module K[T;T⁻¹] Q] [IsScalarTower K K[T;T⁻¹] Q]

omit [IsScalarTower K K[T;T⁻¹] Q] in
lemma range_le_lattice {ι : Type*} [Fintype ι] (s : ι → N)
    (hs : Submodule.span K[X] (Set.range s) = ⊤) (g : N →ₗ[K] Q) (d : ℤ)
    (hpow : ∀ (n : ℕ) (x : N), g ((Polynomial.X : K[X])^n • x) =
      (T (d*n) : K[T;T⁻¹]) • g x) :
    g.range ≤ Submodule.span K (Set.range (fun j : ι × ℕ =>
      (T (d*j.2) : K[T;T⁻¹]) • g (s j.1))) := by
  classical
  rintro _ ⟨x,rfl⟩
  obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp
    (show x ∈ Submodule.span K[X] (Set.range s) from hs ▸ trivial)
  rw [← hf, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [← Polynomial.sum_C_mul_X_pow_eq (f i), Polynomial.sum, Finset.sum_smul, map_sum]
  apply Submodule.sum_mem
  intro n hn
  rw [mul_smul, ← Polynomial.algebraMap_eq, algebraMap_smul, map_smul, hpow]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i,n),rfl⟩)

theorem range_intersection_finite [Module.Finite K[X] N]
    {P : Type*} [AddCommGroup P] [Module K P] [Module K[X] P]
    [IsScalarTower K K[X] P] [Module.Finite K[X] P]
    [Module.Finite K[T;T⁻¹] Q]
    (f : N →ₗ[K] Q) (g : P →ₗ[K] Q)
    (hf : ∀ x, f ((Polynomial.X : K[X]) • x) = (T 1 : K[T;T⁻¹]) • f x)
    (hg : ∀ x, g ((Polynomial.X : K[X]) • x) = (T (-1) : K[T;T⁻¹]) • g x) :
    Module.Finite K ↥(f.range ⊓ g.range) := by
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := K[X]) (M := N)
  obtain ⟨m,t,ht⟩ := Module.Finite.exists_fin (R := K[X]) (M := P)
  have hp (j : ℕ) (x : N) : f ((Polynomial.X : K[X])^j • x) =
      (T (1*(j : ℤ)) : K[T;T⁻¹]) • f x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_smul, hf, ih, ← mul_smul, ← T_add]
      congr 2
      omega
  have hn (j : ℕ) (x : P) : g ((Polynomial.X : K[X])^j • x) =
      (T ((-1)*(j : ℤ)) : K[T;T⁻¹]) • g x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_smul, hg, ih, ← mul_smul, ← T_add]
      congr 2
      omega
  apply intersection_finite_general f.range g.range (fun i => f (s i)) (fun i => g (t i))
  · simpa only [one_mul] using range_le_lattice s hs f 1 hp
  · simpa only [neg_one_mul] using range_le_lattice t ht g (-1) hn
end PiExponentSeshadri.LaurentLattices

namespace PiExponentSeshadri.LaurentCech
open LaurentPolynomial
open scoped LaurentPolynomial Polynomial
variable {K N P Q : Type*} [Field K]
  [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  [Module K N] [Module K P] [Module K Q]
  [Module K[X] N] [Module K[X] P] [Module K[X] Q]
  [IsScalarTower K K[X] N] [IsScalarTower K K[X] P] [IsScalarTower K K[X] Q]

theorem intersection_finite [Module.Finite K[X] N] [Module.Finite K[X] P]
    (f : N →ₗ[K[X]] Q) [IsLocalizedModule.Away (Polynomial.X : K[X]) f]
    (g : P →ₗ[K] Q)
    (inverse_coordinate : ∀ y : P,
      (Polynomial.X : K[X]) • g ((Polynomial.X : K[X]) • y) = g y) :
    Module.Finite K ↥((f.restrictScalars K).range ⊓ g.range) := by
  let : Module K[T;T⁻¹] Q := IsLocalizedModule.module
    (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K[X] K[T;T⁻¹] Q :=
    IsLocalizedModule.isScalarTower_module (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K K[T;T⁻¹] Q := .of_algebraMap_smul (fun c x => by
    rw [← C_eq_algebraMap, ← Polynomial.toLaurent_C,
      ← algebraMap_eq_toLaurent, algebraMap_smul]
    exact algebraMap_smul K[X] c x)
  let : Module.Finite K[T;T⁻¹] Q :=
    Module.Finite.of_isLocalizedModule (.powers (Polynomial.X : K[X])) f
  have pos (n : ℕ) (x : Q) : (T (n : ℤ) : K[T;T⁻¹]) • x =
      ((Polynomial.X : K[X])^n) • x := by
    rw [← Polynomial.toLaurent_X_pow, ← algebraMap_eq_toLaurent, algebraMap_smul]
  have pos1 (x : Q) : (T 1 : K[T;T⁻¹]) • x = (Polynomial.X : K[X]) • x := by
    simpa only [Nat.cast_one, pow_one] using pos 1 x
  have cancel (n : ℕ) (x : Q) : (T (-(n : ℤ)) : K[T;T⁻¹]) •
      ((T (n : ℤ) : K[T;T⁻¹]) • x) = x := by
    rw [← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul]
  apply LaurentLattices.range_intersection_finite (f.restrictScalars K) g
  · intro x
    change f ((Polynomial.X : K[X]) • x) = (T 1 : K[T;T⁻¹]) • f x
    rw [map_smul, pos1]
  · intro y
    have h := congrArg (fun z : Q => (T (-1) : K[T;T⁻¹]) • z)
      (inverse_coordinate y)
    rw [← pos1] at h
    have hc (z : Q) : (T (-1) : K[T;T⁻¹]) • ((T 1 : K[T;T⁻¹]) • z) = z := by
      simpa only [Nat.cast_one] using cancel 1 z
    rw [hc] at h
    exact h
end PiExponentSeshadri.LaurentCech

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ExtCokernel
open CategoryTheory CategoryTheory.Abelian
universe w v u t
variable {K : Type t} [CommRing K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C] {S : ShortComplex C}

def quotientEquiv (hS : S.ShortExact) (M : C)
    (hvan : ∀ x : Ext S.X₂ M 1, x = 0) :
    ((S.X₁ ⟶ M) ⧸ (LinearMap.range
      (Linear.leftComp K M S.f))) ≃ₗ[K] Ext S.X₃ M 1 := by
  let d : (S.X₁ ⟶ M) →ₗ[K] Ext S.X₃ M 1 :=
    (hS.extClass.precompOfLinear K M (add_zero 1)).comp Ext.linearEquiv₀.symm.toLinearMap
  have hd : Function.Surjective d := by
    intro x
    obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ hS M x (hvan _) (n₀ := 0) rfl
    refine ⟨Ext.linearEquiv₀ (R := K) y, ?_⟩
    change hS.extClass.comp (Ext.mk₀ (Ext.linearEquiv₀ (R := K) y)) (add_zero 1) = x
    rwa [Ext.mk₀_linearEquiv₀_apply]
  have hk : LinearMap.range (Linear.leftComp K M S.f) = d.ker := by
    ext f
    constructor
    · rintro ⟨g,rfl⟩
      change hS.extClass.comp (Ext.mk₀ (S.f ≫ g)) (add_zero 1) = 0
      rw [← Ext.mk₀_comp_mk₀]
      exact ShortComplex.ShortExact.extClass_comp_assoc hS _
    · intro hf
      change hS.extClass.comp (Ext.mk₀ f) (add_zero 1) = 0 at hf
      obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₁ hS M (Ext.mk₀ f) rfl hf
      refine ⟨Ext.linearEquiv₀ (R := K) y, ?_⟩
      apply (Ext.linearEquiv₀ (R := K)).symm.injective
      change Ext.mk₀ (S.f ≫ Ext.linearEquiv₀ (R := K) y) = Ext.mk₀ f
      simpa only [← Ext.mk₀_comp_mk₀,
        Ext.mk₀_linearEquiv₀_apply] using hy
  exact (Submodule.quotEquivOfEq _ _ hk).trans (d.quotKerEquivOfSurjective hd)

end PiExponentSeshadri.ExtCokernel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyFiniteCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K]

theorem pencil_polynomial_irrelevant_le :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X (R := K) : σ → MvPolynomial σ K)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ K
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

def projectiveCoordinateCover : (Proj (homogeneousSubmodule σ K)).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan _ (X (R := K))
    (m := fun _ => 1) (fun i => isHomogeneous_X K i) (fun _ => by decide)
    pencil_polynomial_irrelevant_le

lemma affine_evaluation_finite {R : Type} [CommRing R] {Y : Scheme}
    (f : R →+* Γ(Y,⊤)) [IsFinite (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f))] :
    f.Finite := by
  let g := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hEq : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop = CommRingCat.ofHom f := by
    simp only [g, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have h := g.finite_appTop.comp (RingHom.Finite.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.Finite at h
  simpa only [hEq, CommRingCat.hom_ofHom] using h

end

open AlgebraicGeometry CategoryTheory TopologicalSpace

end PiExponentSeshadri.Projective

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyPencil
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K : Type} [CommRing K] {X : Scheme.{0}}

def nestedRestriction (M : X.Modules) {U W : X.Opens} (h : W ≤ U) :
    (M.restrict U.ι).restrict (X.homOfLE h) ≅ M.restrict W.ι :=
  ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M

lemma nestedBase (k : K →+* Γ(X,⊤)) {U W : X.Opens} (h : W ≤ U) :
    (X.homOfLE h).appTop.hom.comp (U.ι.appTop.hom.comp k) = W.ι.appTop.hom.comp k := by
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
    Scheme.homOfLE_ι]

end
end PiExponentSeshadri.Geometry.BaseSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveLaurentTransitions
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveLaurentTransitions
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {ι R : Type*} [Fintype ι] [CommRing R]

def standardExponent (i : ι) (d : ℤ) : ι → ℤ := fun k => if k = i then d else 0

omit [Fintype ι] in
@[simp] theorem standardExponent_self (i : ι) (d : ℤ) : standardExponent i d i = d := by
  simp [standardExponent]

omit [Fintype ι] in
@[simp] theorem standardExponent_other (i k : ι) (d : ℤ) (hk : k ≠ i) :
    standardExponent i d k = 0 := by simp [standardExponent, hk]

abbrev FullGroupAlgebra := AddMonoidAlgebra R (ι → ℤ)

end
end PiExponent.GeometrySupport.ProjectiveLaurentTransitions

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_SerreVanishing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.SerreVanishing

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian

universe u

variable {X : Scheme.{u}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

abbrev schemeUnit (Y : Scheme.{u}) : Y.Modules :=
  SheafOfModules.unit Y.ringCatSheaf

end

end PiExponent.SerreVanishing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveFinitePushforwardCoherent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveFinitePushforwardCoherent
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CoherentAffineFinite FiniteGlobalPresentation ClosedPushforwardAffine
variable {X Y : Scheme.{0}}

def presentationOfIso (X : Scheme.{0})
    {M N : SheafOfModules X.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

end
end PiExponent.CurveFinitePushforwardCoherent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_OpenIsoFunctionField
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveBlowupImage
variable {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X]

def functionFieldMap (f : C ⟶ X) [IsDominant f] : X.functionField ⟶ C.functionField :=
  eqToHom (congrArg (fun x => X.presheaf.stalk x)
    (genericPoint_eq_of_isDominant f).symm) ≫ f.stalkMap (genericPoint C)

theorem functionFieldMap_isIso (f : C ⟶ X) [IsDominant f]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Nonempty (f ⁻¹ᵁ U)) :
    IsIso (functionFieldMap f) := by
  have hx : f (genericPoint C) ∈ U := by
    apply ((genericPoint_spec C).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr
    obtain ⟨q⟩ := hU
    exact ⟨q.1, trivial, q.2⟩
  let := stalkMap_isIso_of_restrict f U (genericPoint C) hx
  unfold functionFieldMap
  infer_instance

def functionFieldIso (f : C ⟶ X) [IsDominant f]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Nonempty (f ⁻¹ᵁ U)) :
    X.functionField ≅ C.functionField :=
  letI := functionFieldMap_isIso f U hU
  asIso (functionFieldMap f)

theorem eqToHom_fromSpecStalk (X : Scheme.{0}) {x y : X} (h : x = y) :
    Spec.map (eqToHom (congrArg (fun z => X.presheaf.stalk z) h)) ≫
      X.fromSpecStalk x = X.fromSpecStalk y := by
  subst y
  simp

theorem functionFieldMap_fromSpecStalk (f : C ⟶ X) [IsDominant f] :
    Spec.map (functionFieldMap f) ≫ X.fromSpecStalk (genericPoint X) =
      C.fromSpecStalk (genericPoint C) ≫ f := by
  unfold functionFieldMap
  rw [Spec.map_comp, Category.assoc,
    eqToHom_fromSpecStalk X (genericPoint_eq_of_isDominant f).symm]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f

end PiExponent.CurveBlowupImage

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveImageAffineChart
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveImageAffineCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {C X : Scheme.{0}} {ι : Type}

def affinePart (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j] : C.affineOpens :=
  ⟨i ⁻¹ᵁ j.opensRange, (isAffineOpen_opensRange j).preimage i⟩

def affinePresentation (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j] :
    Spec Γ(C,(affinePart i j).1) ⟶ Spec (.of (MvPolynomial ι ℂ)) :=
  (affinePart i j).2.isoSpec.inv ≫ (i ∣_ j.opensRange) ≫ j.isoOpensRange.inv

@[reassoc] theorem affinePresentation_comp (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j] :
    affinePresentation i j ≫ j = (affinePart i j).2.fromSpec ≫ i := by
  unfold affinePresentation IsAffineOpen.fromSpec
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (affinePart i j).2.isoSpec.inv ≫ k)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => (i ∣_ j.opensRange) ≫ k)
          (Scheme.Hom.isoOpensRange_inv_comp j)).trans
          (morphismRestrict_ι i j.opensRange)))).trans
      (Category.assoc _ _ _).symm)

theorem affinePart_nonempty (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j]
    (h : ∃ c : C, i c ∈ j.opensRange) : Nonempty (affinePart i j).1 := by
  obtain ⟨c,hc⟩ := h
  exact ⟨⟨c,hc⟩⟩

end PiExponent.CurveImageAffineCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveImageOpenLocus
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveBlowupImage
variable {C X : Scheme.{0}}

theorem exists_image_outside_closed_points [IsIntegral C] (f : C ⟶ X)
    (Z : Set X) (hZ : ∀ x ∈ Z, IsClosed ({x} : Set X))
    (hn : ¬ ∃ x : X, Set.range f ⊆ {x}) : ∃ c : C, f c ∉ Z := by
  by_contra h
  push Not at h
  have hc := hZ (f (genericPoint C)) (h (genericPoint C))
  apply hn
  refine ⟨f (genericPoint C), ?_⟩
  rintro _ ⟨c,rfl⟩
  have hh := ((genericPoint_spec C).specializes (Set.mem_univ c)).map f.continuous
  have hm := hh.mem_closure
  rwa [hc.closure_eq] at hm

end PiExponent.CurveBlowupImage

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationUnit
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem dominant_of_iso_restrict [IsIntegral X] (f : Y ⟶ X)
    (U : X.Opens) (hU : U ≠ ⊥) [IsIso (f ∣_ U)] : IsDominant f := by
  have hne : (U : Set X).Nonempty := by
    by_contra hn
    apply hU
    apply SetLike.coe_injective
    exact Set.not_nonempty_iff_eq_empty.mp hn
  let : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense hne)
  have : IsDominant ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  exact IsDominant.of_comp (f ⁻¹ᵁ U).ι f

end PiExponent.CurveNormalizationDegree

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveProperImageDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveProperImageDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
universe u

theorem image_nontrivial_of_nonconstant {C X : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ X) (hnonconstant : ¬ ∃ x : X, Set.range f ⊆ {x}) : Nontrivial f.image := by
  classical
  by_contra h
  let : Subsingleton f.image := not_nontrivial_iff_subsingleton.mp h
  apply hnonconstant
  refine ⟨f (genericPoint C), ?_⟩
  rintro _ ⟨c, rfl⟩
  change f c = f (genericPoint C)
  have hc : f.toImage c = f.toImage (genericPoint C) := Subsingleton.elim _ _
  have he := congrArg f.imageι hc
  simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] using he

end PiExponent.CurveProperImageDimension

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCurveTwoAffine
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveCurveTwoAffine
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] [Fintype σ]

def linearEquation (v : σ → K) : MvPolynomial σ K := ∑ i, C (v i) * X i

def linearEquationLinear : (σ → K) →ₗ[K] MvPolynomial σ K where
  toFun := linearEquation
  map_add' v w := by simp [linearEquation, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp [linearEquation, Algebra.smul_def, Finset.mul_sum, mul_assoc]

theorem linearEquation_single_one [DecidableEq σ] (i : σ) :
    linearEquation (Pi.single i (1 : K)) = X i := by
  classical
  simp [linearEquation, Pi.single_apply, apply_ite, ite_mul]

end
end PiExponent.ProjectiveCurveTwoAffine

end OAI
end


