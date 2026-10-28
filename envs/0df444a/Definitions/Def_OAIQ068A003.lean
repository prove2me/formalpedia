-- Prove2me | Definitions.Def_OAIQ068A003
-- name    : OAIQ068A003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:38:42.711206+00:00
-- url     : https://prove2.me/theorems/d4164bec-1723-481f-8e1c-3c6d90a8b19b
-- title:
--   Definitions bundle OAIQ068A003 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 146 declarations of OpenAI's Lean: 52 definitions, 1 inductive type or structure, 7 instances and 86 theorems. The definitions and types are `OAI.PiExponent.BlowupCurveMargin.marginCoefficient`, `OAI.PiExponent.BranchContact.active`, `OAI.PiExponent.BranchContact.contact`, `OAI.PiExponent.CoherentAffineFinite.LocallyFinitelyGenerated`, `OAI.PiExponent.CurveContactFamily.fullCenter`, `OAI.PiExponent.CurveImageAffineCoordinates.coordinates`, `OAI.PiExponent.CurveLocalOrder.residueAugmentation`, `OAI.PiExponent.CurveLocalOrder.residueCoefficientEquiv`, `OAI.PiExponent.CurveNormalizationModel.integralClosureTowerHom`, `OAI.PiExponent.CurveNormalizationModel.parameterLaurentAlgebra`, `OAI.PiExponent.CurveNormalizationModel.parameterLaurentChart`, `OAI.PiExponent.CurveNormalizationModel.parameterLaurentMap`, `OAI.PiExponent.CurveNormalizationModel.parameterOverlapProjection`, `OAI.PiExponent.CurveNormalizationModel.reciprocalLaurentChartEquiv`, `OAI.PiExponent.DVRBranch.expansion`, `OAI.PiExponent.DVRBranch.residueCoefficientMap`, `OAI.PiExponent.DVRBranch.uniformizer`, `OAI.PiExponent.DVRBranchExpansion.expansion`, `OAI.PiExponent.DVRBranchExpansion.expansionCoeff`, `OAI.PiExponent.DVRBranchExpansion.expansionHom`, `OAI.PiExponent.DVRBranchExpansion.remainder`, `OAI.PiExponent.DVRBranchExpansion.remainderLinear`, `OAI.PiExponent.DVRBranchJet.contact`, `OAI.PiExponent.DVRBranchJet.coordinates`, `OAI.PiExponent.FiniteGlobalPresentation.presentationOfIso`, `OAI.PiExponent.FiniteGlobalPresentation.presentationOver_of_restrict`, `OAI.PiExponent.FiniteGlobalPresentation.restrictIsoOfLE`, `OAI.PiExponent.FormalBranchEvaluation.branchCoordinates`, `OAI.PiExponent.GlobalSectionClearing.affineToSpecModule`, `OAI.PiExponent.GlobalSectionClearing.restrictScalar`, `OAI.PiExponent.IntegralAffineOpenDimension.functionFieldAlgebra`, `OAI.PiExponent.NumericalAmpleness.IntegralCurve`, `OAI.PiExponent.PolynomialPoleBound.realValuation`, `OAI.PiExponent.ProjectiveLine.constantsInDegreeZero`, `OAI.PiExponent.ProjectiveLine.degreeZeroEquiv`, `OAI.PiExponent.ProjectiveLine.infinityChartOverlap`, `OAI.PiExponent.ProjectiveLine.infinityPolynomialMap`, `OAI.PiExponent.ProjectiveLine.inverseCoordinateUnit`, `OAI.PiExponent.ProjectiveLine.lineEvaluation`, `OAI.PiExponent.ProjectiveLine.projectiveLine` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_BlowupCurveMargin`, `PiExponent_Ampleness_CoherentAffineFinite`, `PiExponent_Ampleness_NumericalAmpleness`, `PiExponent_Approximation_GlobalSectionClearing`, `PiExponent_Cohomology_CurveEuler`, `PiExponent_Cohomology_EulerExact`, `PiExponent_Cohomology_FiniteCoverCohomology`, `PiExponent_Cohomology_PencilCohomologyCharts`, `PiExponent_Cohomology_PencilCohomologySections`, `PiExponent_Cohomology_ProjectiveLineLaurent`, `PiExponent_Geometry_CurveCenters`, `PiExponent_Geometry_CurveContactFamily`, `PiExponent_Geometry_CurveContactSum`, `PiExponent_Geometry_CurveImageAffineCoordinates`, `PiExponent_Geometry_CurveInequalityIntrinsic`, `PiExponent_Geometry_CurveLocalOrder`, `PiExponent_Geometry_CurveMorphismFinite`, `PiExponent_Geometry_CurveNormalizationModel`, `PiExponent_Geometry_CurveNormalizationProper`, `PiExponent_Geometry_CurveParameterFinite`, `PiExponent_Geometry_CurveProperImageDimension`, `PiExponent_Geometry_CurveZeroPole`, `PiExponent_Geometry_FiniteCurveZeros`, `PiExponent_Geometry_LineBundleGluing`, `PiExponent_Geometry_PlaceLocalRing`, `PiExponent_Geometry_ProjectiveFrameNaturality`, `PiExponent_Geometry_ProjectiveLineCharts`, `PiExponent_Geometry_ProjectiveLineProper`, `PiExponent_Geometry_ProjectiveLineReciprocal`, `PiExponent_Geometry_SectionOrderDivisor`, `PiExponent_Geometry_WeightedCurveDegree`, `PiExponent_Jets_BranchContact`, `PiExponent_Jets_DVRBranch`, `PiExponent_Jets_DVRBranchExpansion`, `PiExponent_Jets_DVRBranchJet`, `PiExponent_Jets_DVRBranchOrder`, `PiExponent_Jets_FormalBranchEvaluation`, `PiExponent_LocalAlgebra_FiniteGlobalPresentation`, `PiExponent_LocalAlgebra_IntegralAffineOpenDimension`, `PiExponent_LocalAlgebra_ParameterResidueField`, `PiExponent_Polynomials_PolynomialPoleBound`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A013`, `OAIQ068A014`, `OAIQ068A015`, `OAIQ068A016`, `OAIQ068A017`, `OAIQ068A018` and `OAIQ068A019`; the statements `OAI_PiExponent_CurveFieldRigidity_ordinary_coordinate_constant` and `OAI_PiExponent_CurveInequality_excess_implies_fibre_coordinate_constant`; the proofs of `OAI_PiExponentJets_W28_LocalIntersection_exists_cyclic_filtration_all_local_counts` and `OAI.PiExponentJets.W28.LocalIntersection.exists_cyclic_filtration_all_local_counts_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ068_PI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- d13f23b's `Transcendental.ne_zero`: a transcendental element is nonzero (PiExponent CurveZeroPole,
oaiq-068). -/
theorem _root_.Transcendental.ne_zero {R A : Type*} [CommRing R] [Nontrivial R] [Ring A] [Algebra R A] {x : A}
    (h : Transcendental R x) : x ≠ 0 := fun hx => h (hx ▸ isAlgebraic_zero)
end OAICompat434

end OAI
end

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

theorem epi_iso_comp_iso {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (p : B ⟶ D) (hp : Epi p) (j : D ≅ E) :
    Epi (i.hom ≫ p ≫ j.hom) := by
  let : Epi p := hp
  infer_instance

def LocallyFinitelyGenerated {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    ∃ s : (M.restrict U.ι).GeneratingSections, s.IsFiniteType

end
end PiExponent.CoherentAffineFinite

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

abbrev schemeUnit (X : AlgebraicGeometry.Scheme) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

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

section PresentationMap
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S : Sheaf J' RingCat.{u}} [HasSheafify J' AddCommGrpCat.{u}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

def presentationOfIso {N : SheafOfModules.{u} R} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

end PresentationMap

theorem isFinitePresentation_of_presentation {X : Scheme.{u}} {M : X.Modules}
    (P : M.Presentation) [hP : P.IsFinite] : M.IsFinitePresentation := by
  let q := P.quasicoherentData
  have : q.IsFinitePresentation := by
    constructor
    intro U
    exact ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩
  exact { exists_quasicoherentData := ⟨q, inferInstance⟩ }

def presentationOver_of_restrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation := by
  let E := Scheme.Modules.overEquiv U
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤
      SheafOfModules (Sheaf.over X.ringCatSheaf U) := E.inverse
  let : PreservesColimitsOfSize.{u,u} F :=
    E.symm.toAdjunction.leftAdjoint_preservesColimits
  let e : E.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
      (E.unitIso.app (M.over U)).symm
  let : IsIso e.hom := e.isIso_hom
  exact presentationOfIso e (P.map F (E.unitIso.app _))

instance presentationOver_of_restrict_isFinite {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (P : (M.restrict U.ι).Presentation) [hP : P.IsFinite] :
    (presentationOver_of_restrict M U P).IsFinite := by
  exact ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩

theorem free_isFinitePresentation (X : Scheme.{u}) (I : Type u) [Finite I] :
    (SheafOfModules.free (R := X.ringCatSheaf) I).IsFinitePresentation := by
  let f : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Empty) ⟶
      SheafOfModules.free I := 0
  let P := SheafOfModules.presentationOfIsCokernelFree f (𝟙 _) (by simp [f])
    (CokernelCofork.IsColimit.ofId f rfl)
  have : P.IsFinite := by
    constructor
    · constructor
      change Finite I
      infer_instance
    · constructor
      change Finite (ULift.{u} Empty)
      infer_instance
  exact isFinitePresentation_of_presentation P

theorem exists_local_finitePresentation {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ P : (M.restrict U.ι).Presentation, P.IsFinite := by
  obtain ⟨q,hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have hcov := q.coversTop
  rw [Opens.coversTop_iff] at hcov
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, q.X i by rw [hcov]; trivial)
  let F : SheafOfModules (Sheaf.over X.ringCatSheaf (q.X i)) ⥤
      SheafOfModules (Scheme.Opens.toScheme (X := X) (q.X i)).ringCatSheaf :=
    (Scheme.Modules.overEquiv (q.X i)).functor
  let : PreservesColimitsOfSize.{u,u} F :=
    (Scheme.Modules.overEquiv (q.X i)).toAdjunction.leftAdjoint_preservesColimits
  let : (q.presentation i).IsFinite := hq.isFinite_presentation i
  let P := (q.presentation i).map F (Iso.refl _)
  let e := (Scheme.Modules.overFunctorEquiv (q.X i)).app M
  let : IsIso e.hom := e.isIso_hom
  exact ⟨q.X i, hi, presentationOfIso e P,
    ⟨⟨(hq.isFinite_presentation i).isFiniteType_generators.finite⟩,
      ⟨(hq.isFinite_presentation i).isFiniteType_relations.finite⟩⟩⟩

theorem isFinitePresentation_of_localPresentations {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ P : (M.restrict U.ι).Presentation, P.IsFinite) : M.IsFinitePresentation := by
  classical
  choose U hx P hP using h
  have hP' (x : X) : (P x).IsFinite := hP x
  let q : M.QuasicoherentData := {
    I := X
    X := U
    coversTop := by
      rw [Opens.coversTop_iff]
      apply top_unique
      intro x hxtop
      exact Opens.mem_iSup.mpr ⟨x,hx x⟩
    presentation x := presentationOver_of_restrict M (U x) (P x) }
  have : q.IsFinitePresentation := by
    constructor
    intro x
    change (presentationOver_of_restrict M (U x) (P x)).IsFinite
    infer_instance
  exact { exists_quasicoherentData := ⟨q, inferInstance⟩ }

theorem finitePresentation_of_le {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (P : (M.restrict U.ι).Presentation) [hP : P.IsFinite] :
    ∃ Q : (M.restrict V.ι).Presentation, Q.IsFinite := by
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤ SheafOfModules V.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor (X.homOfLE h)
  let : PreservesColimitsOfSize.{u,u} F :=
    (Scheme.Modules.restrictAdjunction (X.homOfLE h)).leftAdjoint_preservesColimits
  let Q := P.map F
    (Scheme.Modules.restrictUnitIso (X.homOfLE h)).symm
  let e := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M
  simp only [X.homOfLE_ι h] at e
  let : IsIso e.inv := e.isIso_inv
  exact ⟨presentationOfIso e.symm Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

def restrictIsoOfLE {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens}
    (h : V ≤ U) (e : M.restrict U.ι ≅ N.restrict U.ι) :
    M.restrict V.ι ≅ N.restrict V.ι := by
  let e' := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app N).symm
  simp only [X.homOfLE_ι h] at e'
  exact e'

theorem isFinitePresentation_of_locally_iso {X : Scheme.{u}} (M N : X.Modules)
    [M.IsFinitePresentation]
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ Nonempty (N.restrict V.ι ≅ M.restrict V.ι)) :
    N.IsFinitePresentation := by
  apply isFinitePresentation_of_localPresentations
  intro x
  obtain ⟨V,hxV,⟨e⟩⟩ := h x
  obtain ⟨U,hxU,P,hP⟩ := exists_local_finitePresentation M x
  obtain ⟨Q,hQ⟩ := finitePresentation_of_le M (V := U ⊓ V) inf_le_left P
  let e' := restrictIsoOfLE (V := U ⊓ V) inf_le_right e
  let : IsIso e'.inv := e'.isIso_inv
  exact ⟨U ⊓ V, ⟨hxU,hxV⟩, presentationOfIso e'.symm Q,
    ⟨⟨hQ.isFiniteType_generators.finite⟩, ⟨hQ.isFiniteType_relations.finite⟩⟩⟩

end
end PiExponent.FiniteGlobalPresentation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlobalSectionClearing
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

def restrictScalar (X : Scheme.{u}) (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom

lemma restrictScalar_naturality (X : Scheme.{u}) {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictScalar X V r) = restrictScalar X U r := by
  change (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map i.op) r = _
  rw [← X.presheaf.map_comp]
  rfl

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
end PiExponent.GlobalSectionClearing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_LineBundleGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.LineBundleGluing

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X : Scheme}

def restrictUnit {V W : X.Opens} (h : V ≤ W) : Γ(X,W)ˣ →* Γ(X,V)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom

@[simp] lemma restrictUnit_val {V W : X.Opens} (h : V ≤ W) (a : Γ(X,W)ˣ) :
    (restrictUnit h a : Γ(X,V)) = X.presheaf.map (homOfLE h).op (a : Γ(X,W)) := rfl

@[simp] lemma restrictUnit_trans {V W Z : X.Opens}
    (h : V ≤ W) (k : W ≤ Z) (a : Γ(X,Z)ˣ) :
    restrictUnit h (restrictUnit k a) = restrictUnit (h.trans k) a := by
  apply Units.ext
  change (X.presheaf.map (homOfLE k).op ≫ X.presheaf.map (homOfLE h).op) _ = _
  rw [← Functor.map_comp]
  rfl

@[simp] lemma restrictUnit_refl (V : X.Opens) (a : Γ(X,V)ˣ) :
    restrictUnit (le_refl V) a = a := by
  apply Units.ext
  simp [restrictUnit]

end PiExponentSeshadri.LineBundleGluing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveFrameNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X : Scheme} {U V : X.Opens} (M : X.Modules)

lemma topIso_hom_restrict (h : V ≤ U) (x : Γ(U.toScheme, ⊤)) :
    V.topIso.hom ((X.homOfLE h).appTop x) =
      X.presheaf.map (homOfLE h).op (U.topIso.hom x) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) x =
    (X.presheaf.map _ ≫ X.presheaf.map _) x
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 2

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable (X : Scheme)

def restrictScalar (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom

lemma restrictScalar_naturality {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictScalar X V r) = restrictScalar X U r := by
  change (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map i.op) r = _
  rw [← X.presheaf.map_comp]
  rfl

def sheafHomSMul {M N : X.Modules} (r : Γ(X, ⊤)) (f : M ⟶ N) : M ⟶ N where
  val := {
    app U := by
      letI : Module Γ(X, U.unop) (M.val.obj U) := (M.val.obj U).isModule
      letI : Module Γ(X, U.unop) (N.val.obj U) := (N.val.obj U).isModule
      let g : M.val.obj U →ₗ[Γ(X, U.unop)] N.val.obj U := (f.val.app U).hom
      exact ModuleCat.ofHom ((restrictScalar X U.unop r) • g)
    naturality {U V} g := by
      let : Module (X.presheaf.obj V) (N.presheaf.obj V) := (N.val.obj V).isModule
      ext m
      change restrictScalar X V.unop r • f.app V.unop (M.presheaf.map g m) =
        N.presheaf.map g (restrictScalar X U.unop r • f.app U.unop m)
      have hn := CategoryTheory.congr_fun (f.mapPresheaf.naturality g) m
      change f.app V.unop (M.presheaf.map g m) =
        N.presheaf.map g (f.app U.unop m) at hn
      rw [hn]
      calc
        _ = X.presheaf.map g (restrictScalar X U.unop r) •
            N.presheaf.map g (f.app U.unop m) := by
              exact congrArg (fun a : X.presheaf.obj V =>
                a • N.presheaf.map g (f.app U.unop m))
                (restrictScalar_naturality X g.unop r).symm
        _ = _ := (N.map_smul g.unop (restrictScalar X U.unop r) (f.app U.unop m)).symm }

instance sheafHomModule (M N : X.Modules) : Module Γ(X, ⊤) (M ⟶ N) where
  smul := sheafHomSMul X
  one_smul f := by
    ext U m
    change restrictScalar X U 1 • f.app U m = f.app U m
    simp
  mul_smul r s f := by
    ext U m
    change restrictScalar X U (r * s) • f.app U m =
      restrictScalar X U r • (restrictScalar X U s • f.app U m)
    simp [mul_smul]
  smul_zero r := by
    ext U m
    change restrictScalar X U r • (0 : Γ(N, U)) = 0
    exact smul_zero _
  smul_add r f g := by
    ext U m
    change restrictScalar X U r • (f.app U m + g.app U m) =
      restrictScalar X U r • f.app U m + restrictScalar X U r • g.app U m
    exact smul_add _ _ _
  zero_smul f := by
    ext U m
    change restrictScalar X U 0 • f.app U m = 0
    simp
  add_smul r s f := by
    ext U m
    change restrictScalar X U (r + s) • f.app U m =
      restrictScalar X U r • f.app U m + restrictScalar X U s • f.app U m
    simp [add_smul]

instance sheafLinear : Linear Γ(X, ⊤) X.Modules where
  smul_comp M N P r f g := by
    ext U m
    change g.app U (restrictScalar X U r • f.app U m) =
      restrictScalar X U r • g.app U (f.app U m)
    exact g.app_smul _ _
  comp_smul M N P f r g := by
    ext U m
    rfl

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {X : Scheme.{0}}

instance schemeHasExt : HasExt.{1} X.Modules := HasExt.standard X.Modules

def baseScalars (f : X ⟶ Spec (CommRingCat.of ℂ)) : ℂ →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Abelian Opposite

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerExact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open scoped AlgebraicGeometry
variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℂ))

@[instance_reducible]
def sheafComplexLinear : Linear ℂ X.Modules where
  homModule M N := Module.compHom _ (baseScalars f)
  smul_comp M N P r g h := by
    change ((baseScalars f r) • g) ≫ h = (baseScalars f r) • (g ≫ h)
    exact Linear.smul_comp _ _ _ _ _ _
  comp_smul M N P g r h := by
    change g ≫ ((baseScalars f r) • h) = (baseScalars f r) • (g ≫ h)
    exact Linear.comp_smul _ _ _ _ _ _

end Geometry

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_WeightedCurveDegree
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.WeightedCurveDegree

noncomputable def weightedPole {ι : Type*} [Fintype ι]
    (w z : ι → ℚ) : ℚ :=
  (Finset.univ : Finset (Option ι)).sup' Finset.univ_nonempty
    (fun i => i.elim 0 (fun j => -z j / w j))

end PiExponent.WeightedCurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveLocalOrder
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators nonZeroDivisors
open IsLocalRing IsDiscreteValuationRing

namespace PiExponent.CurveLocalOrder

noncomputable def residueCoefficientEquiv
    (F A : Type*) [Field F] [IsAlgClosed F] [CommRing A] [Algebra F A]
    [IsLocalRing A] [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] :
    F ≃ₐ[F] IsLocalRing.ResidueField A :=
  AlgEquiv.ofBijective (Algebra.ofId F (IsLocalRing.ResidueField A))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

noncomputable def residueAugmentation
    (F A : Type*) [Field F] [IsAlgClosed F] [CommRing A] [Algebra F A]
    [IsLocalRing A] [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] : A →+* F :=
  (residueCoefficientEquiv F A).symm.toRingHom.comp (IsLocalRing.residue A)

@[simp] theorem residueAugmentation_algebraMap
    (F A : Type*) [Field F] [IsAlgClosed F] [CommRing A] [Algebra F A]
    [IsLocalRing A] [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] (c : F) :
    residueAugmentation F A (algebraMap F A c) = c := by
  change (residueCoefficientEquiv F A).symm
    (algebraMap A (IsLocalRing.ResidueField A) (algebraMap F A c)) = c
  rw [← IsScalarTower.algebraMap_apply F A (IsLocalRing.ResidueField A)]
  exact (residueCoefficientEquiv F A).symm.commutes c

end PiExponent.CurveLocalOrder

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_FiniteCurveZeros
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
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

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X : Scheme}

theorem finite_subscheme_of_curve [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (hd : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    Finite I.subscheme := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  have hp : (I.support : Set X) ≠ Set.univ := by
    intro he
    apply hI
    exact Scheme.IdealSheafData.support_eq_top_iff.mp (SetLike.coe_injective he)
  have hf := proper_closed_finite_of_dimension_one hd I.support.isClosed hp
  have hr : (Set.range I.subschemeι).Finite := I.range_subschemeι ▸ hf
  let : Finite (Set.range I.subschemeι) := hr.to_subtype
  exact Finite.of_injective (fun x : I.subscheme =>
    (⟨I.subschemeι x, ⟨x,rfl⟩⟩ : Set.range I.subschemeι))
    (fun a b h => I.subschemeι.isEmbedding.injective (congrArg (fun z : Set.range I.subschemeι => (z : X)) h))

end

open AlgebraicGeometry CategoryTheory

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_NumericalAmpleness
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry
open scoped AlgebraicGeometry

structure IntegralCurve (X : Scheme) where
  scheme : Scheme
  embedding : scheme ⟶ X
  closedImmersion : IsClosedImmersion embedding
  integral : IsIntegral scheme
  dimension : topologicalKrullDim scheme = 1

attribute [instance] IntegralCurve.closedImmersion IntegralCurve.integral

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveMorphismFinite
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveMorphismFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
universe u

attribute [local instance] specializationOrder

theorem isClosed_singleton_of_ne_genericPoint (X : Scheme.{u}) [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) (hx : x ≠ genericPoint X) :
    IsClosed ({x} : Set X) := by
  apply closure_subset_iff_isClosed.mp
  intro y hy
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have hylt : y < x := lt_of_le_of_ne hyx (by simpa using hne)
  have hdim' : Order.krullDim X ≤ 1 := by
    change Order.krullDim (IrreducibleCloseds X) ≤ 1 at hdim
    rwa [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))] at hdim
  have hyco : Order.coheight y ≤ (1 : ℕ∞) := by
    exact_mod_cast (Order.coheight_le_krullDim y).trans hdim'
  have hxco : Order.coheight x < (1 : ℕ∞) :=
    Order.coheight_le_coe_iff.mp hyco x hylt
  have hxmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp hxco)
  exact hx hxmax.eq_top

end PiExponent.CurveMorphismFinite

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveParameterFinite
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveParameterFinite

theorem finiteDimensional_adjoin_singleton
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Algebra.EssFiniteType F E] (htrdeg : Algebra.trdeg F E ≤ 1)
    {g : E} (hg : Transcendental F g) :
    FiniteDimensional (IntermediateField.adjoin F {g}) E := by
  have hind : AlgebraicIndependent F (fun z : ({g} : Set E) => (z : E)) := by
    rw [algebraicIndependent_singleton_iff ⟨g, rfl⟩]
    exact hg
  have hb := hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htrdeg)
  have hrange : Set.range (fun z : ({g} : Set E) => (z : E)) = {g} :=
    Subtype.range_coe
  let : Algebra.IsAlgebraic (IntermediateField.adjoin F {g}) E := by
    have ha := hb.isAlgebraic_field
    rw [hrange] at ha
    exact ha
  let : Algebra.EssFiniteType (IntermediateField.adjoin F {g}) E :=
    Algebra.EssFiniteType.of_comp F (IntermediateField.adjoin F {g}) E
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem finite_over_every_parameter
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Algebra.EssFiniteType F E] (htrdeg : Algebra.trdeg F E = 1) :
    ∀ g : E, Transcendental F g →
      FiniteDimensional (IntermediateField.adjoin F {g}) E :=
  fun _ hg => finiteDimensional_adjoin_singleton F E htrdeg.le hg

end PiExponent.CurveParameterFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveZeroPole
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Polynomial nonZeroDivisors

namespace PiExponent.CurveZeroPole

theorem transcendental_inverse {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Transcendental F f⁻¹ := by
  simpa only [Transcendental, IsAlgebraic.inv_iff] using hf

end PiExponent.CurveZeroPole

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_BranchContact
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BranchContact

variable {ι : Type*} [Fintype ι]

def active (a : ι → PowerSeries ℂ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => a i ≠ 0)

@[simp] theorem mem_active (a : ι → PowerSeries ℂ) (i : ι) :
    i ∈ active a ↔ a i ≠ 0 := by
  classical
  simp [active]

theorem active_nonempty (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) :
    (active a).Nonempty := by
  obtain ⟨i,hi⟩ := hne
  exact ⟨i,(mem_active a i).mpr hi⟩

def contact (v : ι → ℚ) (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) : ℚ :=
  (active a).inf' (active_nonempty a hne) (fun i => ((a i).order.toNat : ℚ) / v i)

end PiExponent.BranchContact

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_DVRBranchExpansion
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.DVRBranchExpansion
open PowerSeries

variable {C A : Type*} [Field C] [CommRing A] [Algebra C A]
variable (ρ : A →ₐ[C] C) (π : A) (hπ : π ≠ 0)
variable (hker : RingHom.ker ρ.toRingHom = Ideal.span {π})

include hker in

theorem residue_sub_dvd (a : A) : π ∣ a - algebraMap C A (ρ a) := by
  apply Ideal.mem_span_singleton.mp
  rw [← hker]
  change ρ (a - algebraMap C A (ρ a)) = 0
  simp

def remainder (a : A) : A := Classical.choose (residue_sub_dvd ρ π hker a)

theorem mul_remainder (a : A) : π * remainder ρ π hker a = a - algebraMap C A (ρ a) :=
  (Classical.choose_spec (residue_sub_dvd ρ π hker a)).symm

variable [IsDomain A]

include hπ in
@[simp] theorem remainder_add (a b : A) :
    remainder ρ π hker (a+b) = remainder ρ π hker a + remainder ρ π hker b := by
  apply mul_left_cancel₀ hπ
  rw [mul_add, mul_remainder, mul_remainder, mul_remainder, map_add, map_add]
  ring

include hπ in
@[simp] theorem remainder_smul (c : C) (a : A) :
    remainder ρ π hker (c • a) = c • remainder ρ π hker a := by
  apply mul_left_cancel₀ hπ
  rw [Algebra.smul_def, mul_remainder, map_mul, AlgHom.commutes, map_mul]
  rw [Algebra.smul_def, mul_left_comm, mul_remainder]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

include hπ in
@[simp] theorem remainder_algebraMap (c : C) :
    remainder ρ π hker (algebraMap C A c) = 0 := by
  apply mul_left_cancel₀ hπ
  rw [mul_zero, mul_remainder, AlgHom.commutes]
  simp

include hker in
omit [IsDomain A] in
theorem residue_uniformizer : ρ π = 0 := by
  change π ∈ RingHom.ker ρ.toRingHom
  rw [hker]
  exact Ideal.subset_span (by simp)

include hπ in
@[simp] theorem remainder_uniformizer_mul (a : A) :
    remainder ρ π hker (π*a) = a := by
  apply mul_left_cancel₀ hπ
  rw [mul_remainder, map_mul, residue_uniformizer ρ π hker, zero_mul, map_zero, sub_zero]

def remainderLinear : A →ₗ[C] A where
  toFun := remainder ρ π hker
  map_add' := remainder_add ρ π hπ hker
  map_smul' := remainder_smul ρ π hπ hker

def expansionCoeff (n : ℕ) (a : A) : C := ρ ((remainderLinear ρ π hπ hker ^ n) a)

@[simp] theorem expansionCoeff_zero (a : A) : expansionCoeff ρ π hπ hker 0 a = ρ a := rfl

@[simp] theorem expansionCoeff_succ (n : ℕ) (a : A) :
    expansionCoeff ρ π hπ hker (n+1) a =
      expansionCoeff ρ π hπ hker n (remainder ρ π hker a) := by
  simp only [expansionCoeff, pow_succ, Module.End.mul_apply]
  rfl

@[simp] theorem expansionCoeff_add (n : ℕ) (a b : A) :
    expansionCoeff ρ π hπ hker n (a+b) =
      expansionCoeff ρ π hπ hker n a + expansionCoeff ρ π hπ hker n b := by
  simp [expansionCoeff]

@[simp] theorem expansionCoeff_smul (n : ℕ) (c : C) (a : A) :
    expansionCoeff ρ π hπ hker n (c • a) = c * expansionCoeff ρ π hπ hker n a := by
  simp [expansionCoeff]

def expansion (a : A) : PowerSeries C := PowerSeries.mk (fun n => expansionCoeff ρ π hπ hker n a)

@[simp] theorem coeff_expansion (a : A) (n : ℕ) :
    PowerSeries.coeff n (expansion ρ π hπ hker a) = expansionCoeff ρ π hπ hker n a :=
  PowerSeries.coeff_mk _ _

@[simp] theorem expansion_add (a b : A) :
    expansion ρ π hπ hker (a+b) = expansion ρ π hπ hker a + expansion ρ π hπ hker b := by
  ext n
  simp only [map_add, coeff_expansion, expansionCoeff_add]

@[simp] theorem expansion_smul (c : C) (a : A) :
    expansion ρ π hπ hker (c • a) = c • expansion ρ π hπ hker a := by
  ext n
  simp only [map_smul, coeff_expansion, expansionCoeff_smul, smul_eq_mul]

@[simp] theorem expansion_algebraMap (c : C) :
    expansion ρ π hπ hker (algebraMap C A c) = PowerSeries.C c := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_expansion, expansionCoeff_succ, remainder_algebraMap ρ π hπ hker]
    simp [expansionCoeff]

theorem expansion_rec (a : A) :
    expansion ρ π hπ hker a = PowerSeries.C (ρ a) +
      expansion ρ π hπ hker (remainder ρ π hker a) * PowerSeries.X := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp only [map_add, coeff_expansion, PowerSeries.coeff_succ_C,
      PowerSeries.coeff_succ_mul_X, expansionCoeff_succ, zero_add]

include hπ in

theorem remainder_mul (a b : A) :
    remainder ρ π hker (a*b) = remainder ρ π hker a * b +
      algebraMap C A (ρ a) * remainder ρ π hker b := by
  apply mul_left_cancel₀ hπ
  rw [mul_add, ← mul_assoc, mul_remainder, mul_left_comm π,
    mul_remainder, mul_remainder, map_mul, map_mul]
  ring

theorem expansion_mul (a b : A) :
    expansion ρ π hπ hker (a*b) = expansion ρ π hπ hker a * expansion ρ π hπ hker b := by
  apply PowerSeries.ext
  intro n
  induction n generalizing a b with
  | zero =>
    simp only [coeff_expansion, expansionCoeff_zero, map_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_expansion]
  | succ n ih =>
    calc
      PowerSeries.coeff (n+1) (expansion ρ π hπ hker (a*b)) =
          expansionCoeff ρ π hπ hker n (remainder ρ π hker (a*b)) := by
        rw [coeff_expansion, expansionCoeff_succ]
      _ = expansionCoeff ρ π hπ hker n (remainder ρ π hker a * b) +
          ρ a * expansionCoeff ρ π hπ hker n (remainder ρ π hker b) := by
        rw [remainder_mul ρ π hπ hker, ← Algebra.smul_def, expansionCoeff_add,
          expansionCoeff_smul]
      _ = PowerSeries.coeff n (expansion ρ π hπ hker (remainder ρ π hker a) *
          expansion ρ π hπ hker b) +
          ρ a * PowerSeries.coeff (n+1) (expansion ρ π hπ hker b) := by
        rw [← coeff_expansion, ih]
        rw [coeff_expansion, expansionCoeff_succ]
      _ = PowerSeries.coeff (n+1)
          ((expansion ρ π hπ hker (remainder ρ π hker a) * expansion ρ π hπ hker b) *
            PowerSeries.X + PowerSeries.C (ρ a) * expansion ρ π hπ hker b) := by
        simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C_mul]
      _ = PowerSeries.coeff (n+1) (expansion ρ π hπ hker a * expansion ρ π hπ hker b) := by
        conv_rhs => rw [expansion_rec ρ π hπ hker a]
        congr 1
        ring

def expansionHom : A →ₐ[C] PowerSeries C where
  toFun := expansion ρ π hπ hker
  map_zero' := by ext n; simp [expansionCoeff]
  map_one' := by simpa using expansion_algebraMap ρ π hπ hker (1 : C)
  map_add' := expansion_add ρ π hπ hker
  map_mul' := expansion_mul ρ π hπ hker
  commutes' := expansion_algebraMap ρ π hπ hker

@[simp] theorem constantCoeff_expansionHom (a : A) :
    PowerSeries.constantCoeff (expansionHom ρ π hπ hker a) = ρ a := by
  change PowerSeries.constantCoeff (expansion ρ π hπ hker a) = ρ a
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_expansion, expansionCoeff_zero]

theorem expansionHom_uniformizer : expansionHom ρ π hπ hker π = PowerSeries.X := by
  change expansion ρ π hπ hker π = PowerSeries.X
  rw [expansion_rec, residue_uniformizer ρ π hker, map_zero, zero_add]
  have hr : remainder ρ π hker π = 1 := by
    simpa using remainder_uniformizer_mul ρ π hπ hker (1 : A)
  rw [hr]
  have he : expansion ρ π hπ hker (1 : A) = 1 := by
    simpa using expansion_algebraMap ρ π hπ hker (1 : C)
  rw [he, one_mul]

end PiExponent.DVRBranchExpansion

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_DVRBranchOrder
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.DVRBranchOrder

variable {A C : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field C]

theorem order_eq_addVal (φ : A →+* PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) (a : A) :
    PowerSeries.order (φ a) = IsDiscreteValuationRing.addVal A a := by
  by_cases ha : a = 0
  · subst a
    rw [map_zero, PowerSeries.order_zero, IsDiscreteValuationRing.addVal_zero]
  · obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [map_mul, map_pow, hφπ, PowerSeries.order_mul, PowerSeries.order_X_pow,
      PowerSeries.order_zero_of_unit (u.isUnit.map φ), zero_add,
      IsDiscreteValuationRing.addVal_def' u hπ]

theorem injective (φ : A →+* PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) : Function.Injective φ := by
  intro a b hab
  have hz : φ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have ho := order_eq_addVal φ π hπ hφπ (a - b)
  rw [hz, PowerSeries.order_zero] at ho
  exact sub_eq_zero.mp (IsDiscreteValuationRing.addVal_eq_top_iff.mp ho.symm)

variable [Algebra C A]

theorem algHom_injective (φ : A →ₐ[C] PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) : Function.Injective φ :=
  injective φ.toRingHom π hπ hφπ

end PiExponent.DVRBranchOrder
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_DVRBranch
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
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

def residueCoefficientMap : A →ₐ[C] C where
  toRingHom := residueAugmentation C A
  commutes' := residueAugmentation_algebraMap C A

@[simp] theorem residueCoefficientMap_ker :
    RingHom.ker (residueCoefficientMap C A).toRingHom = IsLocalRing.maximalIdeal A := by
  ext a
  change (residueCoefficientEquiv C A).symm (IsLocalRing.residue A a) = 0 ↔
    a ∈ IsLocalRing.maximalIdeal A
  rw [map_eq_zero_iff _ (AlgEquiv.injective _)]
  exact IsLocalRing.residue_eq_zero_iff a

def uniformizer : A := Classical.choose (IsDiscreteValuationRing.exists_irreducible A)

theorem uniformizer_irreducible : Irreducible (uniformizer A) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible A)

theorem residueCoefficientMap_ker_span :
    RingHom.ker (residueCoefficientMap C A).toRingHom = Ideal.span {uniformizer A} := by
  rw [residueCoefficientMap_ker, (uniformizer_irreducible A).maximalIdeal_eq]

def expansion : A →ₐ[C] PowerSeries C :=
  DVRBranchExpansion.expansionHom (residueCoefficientMap C A) (uniformizer A)
    (uniformizer_irreducible A).ne_zero (residueCoefficientMap_ker_span C A)

@[simp] theorem expansion_uniformizer : expansion C A (uniformizer A) = PowerSeries.X :=
  DVRBranchExpansion.expansionHom_uniformizer _ _ _ _

theorem expansion_injective : Function.Injective (expansion C A) :=
  DVRBranchOrder.algHom_injective (expansion C A) (uniformizer A)
    (uniformizer_irreducible A) (expansion_uniformizer C A)

@[simp] theorem expansion_constantCoeff (a : A) :
    PowerSeries.constantCoeff (expansion C A a) = residueAugmentation C A a :=
  DVRBranchExpansion.constantCoeff_expansionHom _ _ _ _ a

end PiExponent.DVRBranch

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalBranchEvaluation
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.FormalBranchEvaluation
open MvPowerSeries

def branchCoordinates {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) : Fin (m+1) → PowerSeries ℂ :=
  Fin.cases (y-1) (fun i => x i - PowerSeries.C (c i) -
    PowerSeries.subst (y-1) (PowerSeries.log ℂ))

end PiExponent.FormalBranchEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_DVRBranchJet
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.DVRBranchJet
open FormalBranchEvaluation

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

def coordinates {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A) :
    Fin (m+1) → PowerSeries ℂ :=
  branchCoordinates c (DVRBranch.expansion ℂ A y)
    (fun i => DVRBranch.expansion ℂ A (x i))

theorem coordinates_nonzero {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    ∃ i, coordinates c y x i ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hy : y = 1 := by
    apply DVRBranch.expansion_injective ℂ A
    have h0 := hn 0
    change DVRBranch.expansion ℂ A y - 1 = 0 at h0
    simpa only [map_one] using sub_eq_zero.mp h0
  rcases hnc with hnc | ⟨i, hi⟩
  · exact hnc hy
  · apply hi
    apply DVRBranch.expansion_injective ℂ A
    have hs := hn i.succ
    change DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i) -
      PowerSeries.subst (DVRBranch.expansion ℂ A y - 1) (PowerSeries.log ℂ) = 0 at hs
    rw [hy, map_one, sub_self,
      PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log, sub_zero] at hs
    rw [AlgHom.commutes]
    change DVRBranch.expansion ℂ A (x i) = PowerSeries.C (c i)
    exact sub_eq_zero.mp hs

def contact {m : ℕ} (v : Fin (m+1) → ℚ) (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i)) : ℚ :=
  BranchContact.contact v (coordinates c y x) (coordinates_nonzero c y x hnc)

end PiExponent.DVRBranchJet

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialPoleBound
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.PolynomialPoleBound

variable {K C σ : Type*} [Field K] [CommRing C] [Algebra C K]

def realValuation (v : AddValuation K (WithTop ℤ)) : AddValuation K (WithTop ℝ) :=
  v.map (Int.castAddHom ℝ).withTopMap rfl
    ((show Monotone (fun z : ℤ => (z : ℝ)) from Int.cast_mono).withTop_map)

@[simp] theorem realValuation_apply (v : AddValuation K (WithTop ℤ)) (x : K) :
    realValuation v x = WithTop.map (fun z : ℤ => (z : ℝ)) (v x) := rfl

end PiExponent.PolynomialPoleBound

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContactSum
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveContactSum

open WeightedCurveDegree PolynomialPoleBound

theorem exists_constant_of_isAlgebraic {E : Type*} [Field E] [Algebra ℂ E]
    (f : E) (hf : IsAlgebraic ℂ f) : ∃ c : ℂ, algebraMap ℂ E c = f := by
  have hm : f ∈ algebraicClosure ℂ E := mem_algebraicClosure_iff.mpr hf
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure ℂ E)] at hm
  exact hm

end PiExponent.CurveContactSum

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveCenters
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveCenters

variable {E ι J : Type*} [Field E] [Algebra ℂ E]

theorem transcendental_sub_constant {x : E} (hx : Transcendental ℂ x) (c : ℂ) :
    Transcendental ℂ (x - algebraMap ℂ E c) := by
  intro h
  apply hx
  simpa only [sub_add_cancel] using h.add (isAlgebraic_algebraMap c)

theorem exists_transcendental_coordinate (x : ι → E)
    (hx : IntermediateField.adjoin ℂ (Set.range x) = ⊤)
    (hE : ∃ z : E, Transcendental ℂ z) : ∃ i, Transcendental ℂ (x i) := by
  by_contra hn
  push Not at hn
  have hle : IntermediateField.adjoin ℂ (Set.range x) ≤ ⊥ := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := CurveContactSum.exists_constant_of_isAlgebraic (x i) (by
      simpa only [Transcendental, not_not] using hn i)
    exact IntermediateField.mem_bot.mpr ⟨c, hc⟩
  obtain ⟨z, hz⟩ := hE
  have hzbot : z ∈ (⊥ : IntermediateField ℂ E) := hle (by simp [hx])
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hzbot
  exact hz (hc ▸ isAlgebraic_algebraMap c)

theorem Centered.exists_nonzero_difference (x : ι → E) (a : ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i)) :
    ∃ i, x i ≠ algebraMap ℂ E (a i) := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  intro he
  exact hi (he.symm ▸ isAlgebraic_algebraMap (a i))

end PiExponent.CurveCenters
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContactFamily
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveContactFamily

open CurveCenters

variable {E : Type*} [Field E] {m K : ℕ}

def fullCenter (c : Fin m → ℂ) : Fin (m+1) → ℂ := Fin.cases 1 c

@[simp] theorem fullCenter_zero (c : Fin m → ℂ) : fullCenter c 0 = 1 := rfl
@[simp] theorem fullCenter_succ (c : Fin m → ℂ) (i : Fin m) : fullCenter c i.succ = c i := rfl

variable [Algebra ℂ E]

theorem nonconstant (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) :
    ∃ i, z i ≠ algebraMap ℂ E ((fullCenter c) i) :=
  Centered.exists_nonzero_difference z (fullCenter c) hz

end PiExponent.CurveContactFamily
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ParameterResidueField
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ParameterResidueField
open scoped Polynomial nonZeroDivisors
open CurveZeroPole

theorem residue_finite {F S : Type*} [Field F] [CommRing S] [Algebra F S]
    [Algebra.FiniteType F S] (q : Ideal S) [q.IsMaximal] : Module.Finite F q.ResidueField := by
  let : Algebra.FiniteType F q.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom F S q.ResidueField)
      (Ideal.algebraMap_residueField_surjective q)
  exact finite_of_finite_type_of_isJacobsonRing F q.ResidueField

end PiExponent.ParameterResidueField

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceLocalRing
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PlaceLocalRing
open CurveZeroPole

theorem residue_integral_of_algEquiv
    {F A B : Type*} [Field F] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] [IsLocalRing A] [IsLocalRing B]
    [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] (e : A ≃ₐ[F] B) :
    Algebra.IsIntegral F (IsLocalRing.ResidueField B) := by
  constructor
  intro x
  obtain ⟨y,rfl⟩ := (IsLocalRing.ResidueField.mapAlgEquiv e).surjective x
  exact (Algebra.IsIntegral.isIntegral y).map (IsLocalRing.ResidueField.mapAlgEquiv e).toAlgHom

end PiExponent.PlaceLocalRing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveInequalityIntrinsic
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveInequality

open CurveContactFamily


variable {E : Type*} [Field E] [Algebra ℂ E]

theorem nonconstant_coordinates {n : ℕ} (z : Fin n → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ∃ i, Transcendental ℂ (z i) := by
  let : Algebra.Transcendental ℂ E := trdeg_ne_zero_iff.mp (by rw [htrdeg]; exact one_ne_zero)
  exact CurveCenters.exists_transcendental_coordinate z hgen
    (Algebra.Transcendental.transcendental (R := ℂ) (A := E))

end PiExponent.CurveInequality
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupCurveMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BlowupCurveMargin
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open NumericalAmpleness
variable {B X : Scheme.{0}}

def marginCoefficient (a : ℕ) (σ : ℝ) : ℝ := σ / ((a : ℝ) * (1 + σ) - 1)


end PiExponent.BlowupCurveMargin

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologySections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X : Scheme.{0}}

def OpenSections (M : X.Modules) (U : X.Opens) := Γ(M,U)

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyCharts
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

def Sections (_k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) := OpenSections M U

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

end PiExponentSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveLineLaurent
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry
universe u
variable (F : Type u) [CommRing F]

def zeroPolynomialMap : Polynomial F →+* LaurentPolynomial F :=
  Polynomial.toLaurent

def infinityPolynomialMap : Polynomial F →+* LaurentPolynomial F :=
  Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))

@[simp] theorem zeroPolynomialMap_C (r : F) :
    zeroPolynomialMap F (Polynomial.C r) = LaurentPolynomial.C r := by
  simp [zeroPolynomialMap]

@[simp] theorem zeroPolynomialMap_X :
    zeroPolynomialMap F Polynomial.X = LaurentPolynomial.T 1 := by
  simp [zeroPolynomialMap]

@[simp] theorem infinityPolynomialMap_C (r : F) :
    infinityPolynomialMap F (Polynomial.C r) = LaurentPolynomial.C r := by
  simp [infinityPolynomialMap]

@[simp] theorem infinityPolynomialMap_X :
    infinityPolynomialMap F Polynomial.X = LaurentPolynomial.T (-1) := by
  simp [infinityPolynomialMap]

def zeroChartOverlap :
    Spec (CommRingCat.of (LaurentPolynomial F)) ⟶ Spec (CommRingCat.of (Polynomial F)) :=
  Spec.map (CommRingCat.ofHom (zeroPolynomialMap F))

def infinityChartOverlap :
    Spec (CommRingCat.of (LaurentPolynomial F)) ⟶ Spec (CommRingCat.of (Polynomial F)) :=
  Spec.map (CommRingCat.ofHom (infinityPolynomialMap F))

end PiExponent.ProjectiveLine

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationModel
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.CurveNormalizationModel

open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole

def integralClosureTowerHom
    {R S E : Type*} [CommRing R] [CommRing S] [CommRing E]
    [Algebra R S] [Algebra R E] [Algebra S E] [IsScalarTower R S E] :
    integralClosure R E →+* integralClosure S E where
  toFun x := ⟨x.1, x.2.tower_top⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem integralClosureTower_isLocalizationAway
    {R S E : Type*} [CommRing R] [CommRing S] [CommRing E]
    [Algebra R S] [Algebra R E] [Algebra S E] [IsScalarTower R S E]
    (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (algebraMap R E r) E] :
    letI : Algebra (integralClosure R E) (integralClosure S E) :=
      integralClosureTowerHom.toAlgebra
    IsLocalization.Away (algebraMap R (integralClosure R E) r) (integralClosure S E) := by
  let : Algebra (integralClosure R E) (integralClosure S E) :=
    integralClosureTowerHom.toAlgebra
  have : IsScalarTower (integralClosure R E) (integralClosure S E) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R (integralClosure R E) (integralClosure S E) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact IsLocalization.Away.integralClosure (S := E) (Rf := S) (Sf := E) r

theorem integralClosureTower_SpecMap_isOpenImmersion
    {R S E : Type*} [CommRing R] [CommRing S] [CommRing E]
    [Algebra R S] [Algebra R E] [Algebra S E] [IsScalarTower R S E]
    (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (algebraMap R E r) E] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (integralClosureTowerHom (R := R) (S := S) (E := E)))) := by
  let : Algebra (integralClosure R E) (integralClosure S E) :=
    integralClosureTowerHom.toAlgebra
  have : IsLocalization.Away (algebraMap R (integralClosure R E) r) (integralClosure S E) :=
    integralClosureTower_isLocalizationAway r
  exact IsOpenImmersion.of_isLocalization (algebraMap R (integralClosure R E) r)

def parameterLaurentMap {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : LaurentPolynomial F →+* E :=
  LaurentPolynomial.eval₂ (algebraMap F E) (Units.mk0 f hf.ne_zero)

abbrev parameterLaurentAlgebra {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra (LaurentPolynomial F) E :=
  (parameterLaurentMap f hf).toAlgebra

@[simp]
theorem parameterLaurentMap_T {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    parameterLaurentMap f hf (LaurentPolynomial.T 1) = f := by
  simp [parameterLaurentMap, LaurentPolynomial.eval₂_T]

@[simp]
theorem parameterLaurentMap_T_inv {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    parameterLaurentMap f hf (LaurentPolynomial.T (-1)) = f⁻¹ := by
  simp [parameterLaurentMap, LaurentPolynomial.eval₂_T]

abbrev parameterLaurentChart {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Type _ :=
  let := parameterLaurentAlgebra f hf
  integralClosure (LaurentPolynomial F) E

theorem parameterLaurentMap_invert
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    (parameterLaurentMap f hf).comp (LaurentPolynomial.invert (R := F)).toRingHom =
      parameterLaurentMap f⁻¹ (transcendental_inverse f hf) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : F[X]))
  apply Polynomial.ringHom_ext
  · intro c
    simp [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      parameterLaurentMap, LaurentPolynomial.eval₂_C]
  · simp [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent]

theorem isIntegralElem_comp_equiv
    {R S E : Type*} [CommRing R] [CommRing S] [CommRing E]
    (g : S →+* E) (e : R ≃+* S) (x : E) :
    (g.comp e.toRingHom).IsIntegralElem x ↔ g.IsIntegralElem x := by
  constructor
  · exact RingHom.isIntegralElem.of_comp e.toRingHom g
  · intro hx
    apply RingHom.isIntegralElem.of_comp e.symm.toRingHom (g.comp e.toRingHom)
    have heq : (g.comp e.toRingHom).comp e.symm.toRingHom = g := by ext; simp
    rwa [heq]

def reciprocalLaurentChartEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    parameterLaurentChart f hf ≃+*
      parameterLaurentChart f⁻¹ (transcendental_inverse f hf) where
  toFun x := ⟨x.1, by
    have hx := (isIntegralElem_comp_equiv (parameterLaurentMap f hf)
      (LaurentPolynomial.invert (R := F)).toRingEquiv x.1).mpr x.2
    rw [parameterLaurentMap_invert] at hx
    exact hx⟩
  invFun x := ⟨x.1, by
    apply (isIntegralElem_comp_equiv (parameterLaurentMap f hf)
      (LaurentPolynomial.invert (R := F)).toRingEquiv x.1).mp
    rw [parameterLaurentMap_invert]
    exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IntegralAffineOpenDimension
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.IntegralAffineOpenDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (.of k))

@[instance_reducible] def functionFieldAlgebra : Algebra k X.functionField :=
  (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra

end PiExponent.IntegralAffineOpenDimension

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveImageAffineCoordinates
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveImageAffineCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {C X : Scheme.{0}} [IsIntegral C]
variable {ι : Type}

def coordinates (U : C.affineOpens) [Nonempty U.1]
    (q : Spec Γ(C,U.1) ⟶ Spec (.of (MvPolynomial ι ℂ))) : ι → C.functionField :=
  fun i => C.germToFunctionField U.1 ((Spec.preimage q) (MvPolynomial.X i))

end PiExponent.CurveImageAffineCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveLineProper
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

abbrev projectiveLine (F : Type u) [CommRing F] : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule Bool F)

def constantsInDegreeZero (F : Type u) [CommRing F] :
    F →+* (MvPolynomial.homogeneousSubmodule Bool F 0) where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩
  map_one' := Subtype.ext MvPolynomial.C_1
  map_mul' a b := Subtype.ext (MvPolynomial.C_mul (a := a) (a' := b))
  map_zero' := Subtype.ext MvPolynomial.C_0
  map_add' a b := Subtype.ext (MvPolynomial.C_add (a := a) (a' := b))

theorem constantsInDegreeZero_bijective (F : Type u) [CommRing F] :
    Function.Bijective (constantsInDegreeZero F) := by
  constructor
  · intro a b h
    exact MvPolynomial.C_injective _ _ (congrArg Subtype.val h)
  · intro p
    have h : p.val.totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr p.property
    refine ⟨p.val.coeff 0, ?_⟩
    apply Subtype.ext
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h).symm

def degreeZeroEquiv (F : Type u) [CommRing F] :
    F ≃+* (MvPolynomial.homogeneousSubmodule Bool F 0) :=
  RingEquiv.ofBijective (constantsInDegreeZero F) (constantsInDegreeZero_bijective F)

instance constantsInDegreeZero_isIso (F : Type u) [CommRing F] :
    IsIso (CommRingCat.ofHom (constantsInDegreeZero F)) :=
  (degreeZeroEquiv F).toCommRingCatIso.isIso_hom

def structureMap (F : Type u) [CommRing F] :
    projectiveLine F ⟶ Spec (CommRingCat.of F) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule Bool F) ≫
    Spec.map (CommRingCat.ofHom (constantsInDegreeZero F))

instance structureMap_isProper (F : Type u) [CommRing F] :
    IsProper (structureMap F) := by
  let A := MvPolynomial Bool F
  let 𝒜 := MvPolynomial.homogeneousSubmodule Bool F
  let : Algebra F (𝒜 0) := SetLike.GradeZero.instAlgebra 𝒜
  let : IsScalarTower F (𝒜 0) A := ⟨fun a b c => by
    change (a • (b : A)) * c = a • ((b : A) * c)
    exact smul_mul_assoc a (b : A) c⟩
  let : Algebra.FiniteType (𝒜 0) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType F (𝒜 0) A
  have hp : IsProper (Proj.toSpecZero 𝒜) := inferInstance
  have : IsIso (Spec.map (CommRingCat.ofHom (constantsInDegreeZero F))) := inferInstance
  unfold structureMap
  exact IsProper.stableUnderComposition.comp_mem _ _ hp inferInstance

end PiExponent.ProjectiveLine

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveLineCharts
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (F : Type u) [CommRing F]

def lineEvaluation (i : Bool) : MvPolynomial Bool F →+* Polynomial F :=
  MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = i then 1 else Polynomial.X)

@[simp] theorem lineEvaluation_X (i j : Bool) :
    lineEvaluation F i (MvPolynomial.X j) = if j = i then 1 else Polynomial.X := by
  simp [lineEvaluation]

@[simp] theorem lineEvaluation_C (i : Bool) (r : F) :
    lineEvaluation F i (MvPolynomial.C r) = Polynomial.C r := by
  simp [lineEvaluation]

end PiExponent.ProjectiveLine

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveLineReciprocal
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (F : Type u) [CommRing F]

def inverseCoordinateUnit : (LaurentPolynomial F)ˣ where
  val := LaurentPolynomial.T (-1)
  inv := LaurentPolynomial.T 1
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

lemma zeroEvaluation_eq :
    (zeroPolynomialMap F).comp (lineEvaluation F false) =
      MvPolynomial.eval₂Hom LaurentPolynomial.C
        (fun j : Bool => if j = false then 1 else LaurentPolynomial.T 1) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [zeroPolynomialMap]
  · intro j
    cases j <;> simp [zeroPolynomialMap]

lemma infinityEvaluation_eq :
    (infinityPolynomialMap F).comp (lineEvaluation F true) =
      MvPolynomial.eval₂Hom LaurentPolynomial.C
        (fun j : Bool => LaurentPolynomial.T (-1) *
          (if j = false then 1 else LaurentPolynomial.T 1)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, lineEvaluation_C, infinityPolynomialMap_C, MvPolynomial.eval₂Hom_C]
  · intro j
    simp only [RingHom.comp_apply, lineEvaluation_X, MvPolynomial.eval₂Hom_X']
    cases j with
    | false =>
      change infinityPolynomialMap F Polynomial.X = LaurentPolynomial.T (-1) * 1
      rw [infinityPolynomialMap_X, mul_one]
    | true =>
      change infinityPolynomialMap F 1 = LaurentPolynomial.T (-1) * LaurentPolynomial.T 1
      rw [map_one, ← LaurentPolynomial.T_add]
      norm_num

end PiExponent.ProjectiveLine

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationProper
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def parameterOverlapProjection : Spec (.of (parameterLaurentChart f hf)) ⟶
    Spec (.of (LaurentPolynomial F)) :=
  letI := parameterLaurentAlgebra f hf
  Spec.map (CommRingCat.ofHom (algebraMap (LaurentPolynomial F) (parameterLaurentChart f hf)))

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveProperImageDimension
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveProperImageDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
universe u

theorem genericPoint_map {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (f : C ⟶ Y) [IsDominant f] : f (genericPoint C) = genericPoint Y := by
  have h : IsGenericPoint (f (genericPoint C)) (Set.univ : Set Y) := by
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec C).image f.continuous
  exact h.eq (genericPoint_spec Y)

end PiExponent.CurveProperImageDimension

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_SectionOrderDivisor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry

namespace PiExponent.SectionOrderDivisor


variable {X : Scheme.{0}} [IsIntegral X]

abbrev CurvePoint (X : Scheme.{0}) [IsIntegral X] := {x : X // x ≠ genericPoint X}

end PiExponent.SectionOrderDivisor

end

end OAI
end


