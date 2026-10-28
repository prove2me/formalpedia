-- Prove2me | Definitions.Def_OAIQ068A012
-- name    : OAIQ068A012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:45:14.870336+00:00
-- url     : https://prove2.me/theorems/e5153960-8e67-44fb-81df-3aa5f3bb1d72
-- title:
--   Definitions bundle OAIQ068A012 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 147 declarations of OpenAI's Lean: 76 definitions, 2 instances and 69 theorems. The definitions and types are `OAI.PiExponent.AdmissibleBlowupGeometry.affineChart`, `OAI.PiExponent.AdmissibleBlowupGeometry.compactification`, `OAI.PiExponent.AdmissibleBlowupGeometry.constantIndex`, `OAI.PiExponent.AdmissibleBlowupGeometry.coordinateIndex`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.decode`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.encode`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.exponentEquiv`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.fullEncode`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.fullExponentEquiv`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebraToLaurent`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.natExponentHom`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapLaurent`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapToGroupAlgebra`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.polynomialToGroupAlgebra`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.productExponent`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.vertexLaurent`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.vertexPolynomialEquiv`, `OAI.PiExponent.ProjectiveO1.chartRatios`, `OAI.PiExponent.ProjectiveO1.coordinateCocycle`, `OAI.PiExponent.ProjectiveO1.coordinateCoefficients`, `OAI.PiExponent.ProjectiveO1.coordinateOpenFrame`, `OAI.PiExponent.ProjectiveO1.coordinateSection`, `OAI.PiExponent.ProjectiveO1.lineBundle`, `OAI.PiExponent.ProjectiveO1.ratioUnit`, `OAI.PiExponent.ProjectiveO1.scalars`, `OAI.PiExponent.WeightedCompactification.coordinateSection`, `OAI.PiExponent.WeightedCompactification.lineBundle`, `OAI.PiExponentSeshadri.Geometry.InvertiblePullbackIdeal`, `OAI.PiExponentSeshadri.Geometry.LineBundle.pow`, `OAI.PiExponentSeshadri.Geometry.LineBundle.pullback`, `OAI.PiExponentSeshadri.Geometry.PresentsPullbackIdeal`, `OAI.PiExponentSeshadri.Geometry.coordinatePowerFrame`, `OAI.PiExponentSeshadri.Geometry.endPower`, `OAI.PiExponentSeshadri.Geometry.globalPowerFrame`, `OAI.PiExponentSeshadri.Geometry.localPowerFrame`, `OAI.PiExponentSeshadri.Geometry.modulePow`, `OAI.PiExponentSeshadri.Geometry.modulePowFrame`, `OAI.PiExponentSeshadri.Geometry.modulePowFunctor`, `OAI.PiExponentSeshadri.Geometry.modulePowMap`, `OAI.PiExponentSeshadri.Geometry.modulePowRestrict` and 36 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AdmissibleBlowupGeometry`, `PiExponent_Ampleness_BlowupIdeal`, `PiExponent_Approximation_CoherentTwistPresentation`, `PiExponent_Approximation_FrameTensorPowers`, `PiExponent_Approximation_LinePowerLaws`, `PiExponent_Approximation_LinePullback`, `PiExponent_Approximation_SectionPowerFrames`, `PiExponent_Approximation_SectionPowerOpens`, `PiExponent_Approximation_TensorPowerRestriction`, `PiExponent_Cohomology_ProjectiveLaurentVertex`, `PiExponent_Geometry_LineBundleGluing`, `PiExponent_Geometry_LineBundleTensor`, `PiExponent_Geometry_ProjectiveChartOverlaps`, `PiExponent_Geometry_ProjectiveChartSections`, `PiExponent_Geometry_ProjectiveCharts`, `PiExponent_Geometry_ProjectiveCoordinateFiniteSections`, `PiExponent_Geometry_ProjectiveCoordinateSections`, `PiExponent_Geometry_ProjectiveCoordinates`, `PiExponent_Geometry_ProjectiveO1ChartMap`, `PiExponent_Geometry_ProjectiveO1Morphism`, `PiExponent_Geometry_ProjectiveO1Sections`, `PiExponent_Geometry_ProjectiveRatioCocycle`, `PiExponent_Geometry_WeightedProjectiveLineBundle`.
--
--   **Imports.** It imports the bundles `OAIQ068A000` and `OAIQ068A001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A020`, `OAIQ068A021`, `OAIQ068A022`, `OAIQ068A023`, `OAIQ068A024`, `OAIQ068A025`, `OAIQ068A026` and `OAIQ068A027`; the statement `OAI_PiExponentJets_W22_actualMultiplicityCycle_parent_budget`; the proofs of `OAI_PiExponentJets_W22_ActualRegularCutHistory_local_length_bound`, `OAI_PiExponentJets_W22_actualMultiplicityCycle_parent_budget`, `OAI_PiExponentSiegel_W58_polynomialLocal_exists_degree_bounded_regular_parameters` and `OAI_PiExponent_CurveFieldRigidity_logarithmic_coordinate_eq_one`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A000
import Definitions.Def_OAIQ068A001

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_LineBundleTensor
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable (X : Scheme)

def modulePow (M : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => moduleTensor X M (modulePow M n)

end Geometry

open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace Geometry

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def moduleTensorRestrict (U : X.Opens) (M N : X.Modules) :
    (moduleTensor X M N).restrict U.ι ≅
      moduleTensor U.toScheme (M.restrict U.ι) (N.restrict U.ι) :=
  (moduleSheafificationRestrict U.ι).app _ ≪≫
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).mapIso
      (modulePresheafTensorRestrict U M.val N.val)

def moduleTensorIso {M N P Q : X.Modules} (e : M ≅ N) (f : P ≅ Q) :
    moduleTensor X M P ≅ moduleTensor X N Q := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (tensorIso ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso f))

def moduleTensorUnit (M : X.Modules) :
    moduleTensor X (structureSheaf X) M ≅ M := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).counit).app M

def modulePowFrame {M : X.Modules} (U : X.Opens)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    ∀ n, (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 => moduleTensorRestrict U M (modulePow X M n) ≪≫
    moduleTensorIso e (modulePowFrame U e n) ≪≫ moduleTensorUnit _

def LineBundle.pow (L : LineBundle X) (n : ℕ) : LineBundle X where
  sheaf := modulePow X L.sheaf n
  locallyRankOne x := by
    obtain ⟨U, hx, ⟨frame⟩⟩ := L.locallyRankOne x
    exact ⟨U, hx, ⟨modulePowFrame U frame n⟩⟩

def moduleTensorMap {M N P Q : X.Modules} (f : M ⟶ N) (g : P ⟶ Q) :
    moduleTensor X M P ⟶ moduleTensor X N Q :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) f.val g.val)

@[simp] lemma moduleTensorMap_id (M N : X.Modules) :
    moduleTensorMap (𝟙 M) (𝟙 N) = 𝟙 (moduleTensor X M N) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((𝟙 M.val) ⊗ₘ (𝟙 N.val)) = _
  rw [id_tensorHom_id]
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_id _

@[reassoc] lemma moduleTensorMap_comp {M N P Q R T : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (h : Q ⟶ R) (k : R ⟶ T) :
    moduleTensorMap (f ≫ g) (h ≫ k) = moduleTensorMap f h ≫ moduleTensorMap g k := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((f.val ≫ g.val) ⊗ₘ (h.val ≫ k.val)) = _
  rw [← tensorHom_comp_tensorHom]
  exact Functor.map_comp _ _ _

instance moduleTensorMap_isIso {M N P Q : X.Modules} (f : M ⟶ N)
    (g : P ⟶ Q) [IsIso f] [IsIso g] : IsIso (moduleTensorMap f g) := by
  refine ⟨⟨moduleTensorMap (inv f) (inv g), ?_, ?_⟩⟩ <;>
    rw [← moduleTensorMap_comp] <;> simp

def modulePowMap {M N : X.Modules} (f : M ⟶ N) :
    ∀ n, modulePow X M n ⟶ modulePow X N n
  | 0 => 𝟙 _
  | n + 1 => moduleTensorMap f (modulePowMap f n)

@[simp] lemma modulePowMap_id (M : X.Modules) (n : ℕ) :
    modulePowMap (𝟙 M) n = 𝟙 (modulePow X M n) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    change moduleTensorMap (𝟙 M) (modulePowMap (𝟙 M) n) = 𝟙 (moduleTensor X M (modulePow X M n))
    rw [hn, moduleTensorMap_id]

@[reassoc] lemma modulePowMap_comp {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    modulePowMap (f ≫ g) n = modulePowMap f n ≫ modulePowMap g n := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n hn =>
    change moduleTensorMap (f ≫ g) (modulePowMap (f ≫ g) n) =
      moduleTensorMap f (modulePowMap f n) ≫ moduleTensorMap g (modulePowMap g n)
    rw [hn, moduleTensorMap_comp]

instance modulePowMap_isIso {M N : X.Modules} (f : M ⟶ N) [IsIso f] (n : ℕ) :
    IsIso (modulePowMap f n) := by
  induction n with
  | zero => change IsIso (𝟙 (structureSheaf X)); infer_instance
  | succ n hn => change IsIso (moduleTensorMap f (modulePowMap f n)); infer_instance

def modulePowFunctor (n : ℕ) : X.Modules ⥤ X.Modules where
  obj M := modulePow X M n
  map f := modulePowMap f n
  map_id := fun _ => modulePowMap_id _ n
  map_comp := fun _ _ => modulePowMap_comp _ _ n

def unitPowerIso : ∀ n, modulePow X (structureSheaf X) n ≅ structureSheaf X
  | 0 => Iso.refl _
  | n + 1 => moduleTensorUnit _ ≪≫ unitPowerIso n

def powerSection {M : X.Modules} (s : structureSheaf X ⟶ M) (n : ℕ) :
    structureSheaf X ⟶ modulePow X M n :=
  (unitPowerIso n).inv ≫ modulePowMap s n

@[simp] lemma powerSection_zero {M : X.Modules} (s : structureSheaf X ⟶ M) :
    powerSection s 0 = 𝟙 (structureSheaf X) := by
  change 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X) = 𝟙 (structureSheaf X)
  exact Category.id_comp _

def moduleTensorRightUnit (M : X.Modules) :
    moduleTensor X M (structureSheaf X) ≅ M := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (ρ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).counit).app M

end Geometry

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupIdeal
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry

def sectionImageIdeal {X : Scheme} (J : LineBundle X)
    (ι : J.sheaf ⟶ structureSheaf X) (U : X.Opens) : Ideal Γ(X, U) := by
  letI : Module Γ(X, U) (J.sheaf.val.obj (Opposite.op U)) :=
    (J.sheaf.val.obj (Opposite.op U)).isModule
  let φ : J.sheaf.val.obj (Opposite.op U) →ₗ[Γ(X, U)] Γ(X, U) :=
    (ι.val.app (Opposite.op U)).hom
  exact φ.range

def PresentsPullbackIdeal {X Y : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y) : Prop :=
  Mono ι ∧ ∀ (U : Y.affineOpens) (V : X.affineOpens)
    (e : U.1 ≤ f ⁻¹ᵁ V.1),
    sectionImageIdeal J ι U.1 = (I.ideal V).map (f.appLE V.1 U.1 e).hom

def InvertiblePullbackIdeal {X Y : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X) : Prop :=
  ∃ (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y), PresentsPullbackIdeal I f J ι

end Geometry

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoherentTwistPresentation
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace PiExponentSeshadri.Geometry
open MonoidalCategory
variable {X : Scheme}

lemma moduleTensorRestrict_natural (U : X.Opens) {M N P Q : X.Modules}
    (f : M ⟶ N) (g : P ⟶ Q) :
    (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f g) ≫
      (moduleTensorRestrict U N Q).hom =
    (moduleTensorRestrict U M P).hom ≫
      moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map f)
        ((Scheme.Modules.restrictFunctor U.ι).map g) := by
  let K : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let R : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let Rpre : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  let S : PresheafOfModules U.toScheme.ringCatSheaf.obj ⥤ U.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  let e : K ⋙ R ≅ Rpre ⋙ S := moduleSheafificationRestrict U.ι
  let h := PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) f.val g.val
  let k := PresheafOfModules.Monoidal.tensorHom (R := U.toScheme.presheaf)
    (Rpre.map f.val) (Rpre.map g.val)
  let a := (modulePresheafTensorRestrict U M.val P.val).hom
  let b := (modulePresheafTensorRestrict U N.val Q.val).hom
  change R.map (K.map h) ≫ (e.hom.app _ ≫ S.map b) =
    (e.hom.app _ ≫ S.map a) ≫ S.map k
  have ht : Rpre.map h ≫ b = a ≫ k := modulePresheafTensorRestrict_natural U f.val g.val
  calc
    _ = (R.map (K.map h) ≫ e.hom.app _) ≫ S.map b :=
      (Category.assoc _ _ _).symm
    _ = (e.hom.app _ ≫ S.map (Rpre.map h)) ≫ S.map b :=
      congrArg (· ≫ S.map b) (e.hom.naturality h)
    _ = e.hom.app _ ≫ (S.map (Rpre.map h) ≫ S.map b) := Category.assoc _ _ _
    _ = e.hom.app _ ≫ S.map (Rpre.map h ≫ b) :=
      congrArg (e.hom.app _ ≫ ·) (S.map_comp _ _).symm
    _ = e.hom.app _ ≫ S.map (a ≫ k) :=
      congrArg (fun t => e.hom.app _ ≫ S.map t) ht
    _ = e.hom.app _ ≫ (S.map a ≫ S.map k) :=
      congrArg (e.hom.app _ ≫ ·) (S.map_comp _ _)
    _ = _ := (Category.assoc _ _ _).symm

def moduleTensorRightFunctor (L : X.Modules) : X.Modules ⥤ X.Modules where
  obj M := moduleTensor X M L
  map f := moduleTensorMap f (𝟙 L)
  map_id M := moduleTensorMap_id M L
  map_comp f g := by simpa using moduleTensorMap_comp f g (𝟙 L) (𝟙 L)

@[simp] theorem moduleTensorIso_hom {M N P Q : X.Modules}
    (e : M ≅ N) (f : P ≅ Q) :
    (moduleTensorIso e f).hom = moduleTensorMap e.hom f.hom := rfl

@[reassoc] theorem moduleTensorRightUnit_natural {M N : X.Modules} (f : M ⟶ N) :
    moduleTensorMap f (𝟙 (structureSheaf X)) ≫ (moduleTensorRightUnit N).hom =
      (moduleTensorRightUnit M).hom ≫ f := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  let S : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)
  change S.map (f.val ⊗ₘ 𝟙 _) ≫ (S.map (ρ_ N.val).hom ≫ adj.counit.app N) =
    (S.map (ρ_ M.val).hom ≫ adj.counit.app M) ≫ f
  have hu : (f.val ⊗ₘ 𝟙 _) ≫ (ρ_ N.val).hom = (ρ_ M.val).hom ≫ f.val := by
    simpa only [tensorHom_id] using rightUnitor_naturality f.val
  have hS : S.map (f.val ⊗ₘ 𝟙 _) ≫ S.map (ρ_ N.val).hom =
      S.map (ρ_ M.val).hom ≫ S.map f.val :=
    (S.map_comp _ _).symm.trans ((congrArg S.map hu).trans (S.map_comp _ _))
  calc
    _ = (S.map (f.val ⊗ₘ 𝟙 _) ≫ S.map (ρ_ N.val).hom) ≫ adj.counit.app N :=
      (Category.assoc _ _ _).symm
    _ = (S.map (ρ_ M.val).hom ≫ S.map f.val) ≫ adj.counit.app N :=
      congrArg (· ≫ adj.counit.app N) hS
    _ = S.map (ρ_ M.val).hom ≫ (S.map f.val ≫ adj.counit.app N) :=
      Category.assoc _ _ _
    _ = S.map (ρ_ M.val).hom ≫ (adj.counit.app M ≫ f) :=
      congrArg (S.map (ρ_ M.val).hom ≫ ·) (adj.counit.naturality f)
    _ = _ := (Category.assoc _ _ _).symm

def moduleTensorFrame (M : X.Modules) {L : X.Modules}
    (e : L ≅ structureSheaf X) : moduleTensor X M L ≅ M :=
  moduleTensorIso (Iso.refl M) e ≪≫ moduleTensorRightUnit M

@[reassoc] theorem moduleTensorFrame_natural {M N L : X.Modules}
    (f : M ⟶ N) (e : L ≅ structureSheaf X) :
    moduleTensorMap f (𝟙 L) ≫ (moduleTensorFrame N e).hom =
      (moduleTensorFrame M e).hom ≫ f := by
  simp only [moduleTensorFrame, Iso.trans_hom, moduleTensorIso_hom, Iso.refl_hom]
  calc
    _ = moduleTensorMap f e.hom ≫ (moduleTensorRightUnit N).hom := by
      rw [← Category.assoc, ← moduleTensorMap_comp]
      simp only [Category.comp_id, Category.id_comp]
    _ = moduleTensorMap (𝟙 M) e.hom ≫
        moduleTensorMap f (𝟙 (structureSheaf X)) ≫ (moduleTensorRightUnit N).hom := by
      rw [← Category.assoc, ← moduleTensorMap_comp]
      simp only [Category.comp_id, Category.id_comp]
    _ = _ := by rw [moduleTensorRightUnit_natural, Category.assoc]

def moduleTwistFunctor (L : LineBundle X) : ℕ → X.Modules ⥤ X.Modules
  | 0 => 𝟭 _
  | n + 1 => moduleTwistFunctor L n ⋙ moduleTensorRightFunctor L.sheaf

def moduleTensorComm (M N : X.Modules) : moduleTensor X M N ≅ moduleTensor X N M := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.symmetricCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (β_ M.val N.val)

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FrameTensorPowers
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

lemma moduleTensorUnit_scalar (f g : structureSheaf X ⟶ structureSheaf X) :
    moduleTensorMap f g ≫ (moduleTensorUnit (structureSheaf X)).hom =
      (moduleTensorUnit (structureSheaf X)).hom ≫ (f ≫ g) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let G : X.Modules ⥤ PresheafOfModules X.ringCatSheaf.obj :=
    SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let ε : G ⋙ F ⟶ 𝟭 X.Modules :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  have h : (f.val ⊗ₘ g.val) ≫ (λ_ (structureSheaf X).val).hom =
      (λ_ (structureSheaf X).val).hom ≫ (f ≫ g).val := by
    let f₀ : 𝟙_ (PresheafOfModules X.ringCatSheaf.obj) ⟶
        𝟙_ (PresheafOfModules X.ringCatSheaf.obj) := f.val
    let g₀ : 𝟙_ (PresheafOfModules X.ringCatSheaf.obj) ⟶
        𝟙_ (PresheafOfModules X.ringCatSheaf.obj) := g.val
    exact tensor_unit_end f₀ g₀
  change F.map (f.val ⊗ₘ g.val) ≫ (F.map (λ_ (structureSheaf X).val).hom ≫ ε.app (structureSheaf X)) =
    (F.map (λ_ (structureSheaf X).val).hom ≫ ε.app (structureSheaf X)) ≫ (f ≫ g)
  erw [← Category.assoc, ← F.map_comp, h, F.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact ε.naturality (f ≫ g)

def endPower (f : structureSheaf X ⟶ structureSheaf X) : ℕ → (structureSheaf X ⟶ structureSheaf X)
  | 0 => 𝟙 _
  | n + 1 => f ≫ endPower f n

lemma endValue_endPower (f : structureSheaf X ⟶ structureSheaf X) (n : ℕ) :
    endValue (endPower f n) = endValue f ^ n := by
  induction n with
  | zero =>
    change (1 : Γ(X, ⊤)) = endValue f ^ 0
    exact (pow_zero _).symm
  | succ n hn =>
    calc
      endValue (endPower f (n + 1)) = endValue f * endValue (endPower f n) :=
        endValue_comp f (endPower f n)
      _ = endValue f * endValue f ^ n := congrArg (endValue f * ·) hn
      _ = _ := (pow_succ' _ _).symm

lemma moduleTensorUnit_natural {M N : X.Modules} (g : M ⟶ N) :
    moduleTensorMap (𝟙 (structureSheaf X)) g ≫ (moduleTensorUnit N).hom =
      (moduleTensorUnit M).hom ≫ g := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let G : X.Modules ⥤ PresheafOfModules X.ringCatSheaf.obj :=
    SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let ε : G ⋙ F ⟶ 𝟭 X.Modules :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  change F.map ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫
    (F.map (λ_ N.val).hom ≫ ε.app N) =
    (F.map (λ_ M.val).hom ≫ ε.app M) ≫ g
  have h : ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫ (λ_ N.val).hom =
      (λ_ M.val).hom ≫ g.val := by
    rw [id_tensorHom]
    exact leftUnitor_naturality g.val
  have hF : F.map (𝟙 (structureSheaf X).val ⊗ₘ g.val) ≫ F.map (λ_ N.val).hom =
      F.map (λ_ M.val).hom ≫ F.map g.val :=
    (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ ε.app N) hF).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (F.map (λ_ M.val).hom ≫ ·) (ε.naturality g)).trans ?_
  exact (Category.assoc _ _ _).symm

lemma modulePowMap_unitPower (f : structureSheaf X ⟶ structureSheaf X) (n : ℕ) :
    modulePowMap f n ≫ (unitPowerIso n).hom =
      (unitPowerIso n).hom ≫ endPower f n := by
  induction n with
  | zero =>
    change 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X) = 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X)
    rfl
  | succ n hn =>
    change moduleTensorMap f (modulePowMap f n) ≫
      ((moduleTensorUnit _).hom ≫ (unitPowerIso n).hom) =
        ((moduleTensorUnit _).hom ≫ (unitPowerIso n).hom) ≫ (f ≫ endPower f n)
    calc
      _ = moduleTensorMap f (modulePowMap f n) ≫
          moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [moduleTensorUnit_natural]
      _ = moduleTensorMap f ((unitPowerIso n).hom ≫ endPower f n) ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.comp_id, hn]
      _ = moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
          moduleTensorMap f (endPower f n) ≫ (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.id_comp]
      _ = (moduleTensorUnit (modulePow X (structureSheaf X) n)).hom ≫
          (unitPowerIso n).hom ≫ (f ≫ endPower f n) := by
        rw [moduleTensorUnit_scalar, ← Category.assoc, moduleTensorUnit_natural,
          Category.assoc]
      _ = _ := by simp only [Category.assoc]

def globalPowerFrame {M : X.Modules} (e : M ≅ structureSheaf X) (n : ℕ) :
    modulePow X M n ≅ structureSheaf X :=
  (modulePowFunctor n).mapIso e ≪≫ unitPowerIso n

lemma powerSection_coefficient {M : X.Modules} (e : M ≅ structureSheaf X)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (globalPowerFrame e n) (powerSection s n) = coefficient e s ^ n := by
  change endValue ((unitPowerIso n).inv ≫ modulePowMap s n ≫
    (modulePowMap e.hom n ≫ (unitPowerIso n).hom)) = _
  erw [← Category.assoc (modulePowMap s n), ← modulePowMap_comp,
    modulePowMap_unitPower, Iso.inv_hom_id_assoc, endValue_endPower]
  rfl

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TensorPowerRestriction
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def modulePowRestrict (U : X.Opens) (M : X.Modules) :
    ∀ n, (modulePow X M n).restrict U.ι ≅ modulePow U.toScheme (M.restrict U.ι) n
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 => moduleTensorRestrict U M (modulePow X M n) ≪≫
      moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)

lemma modulePowRestrict_natural (U : X.Opens) {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n) ≫
      (modulePowRestrict U N n).hom =
    (modulePowRestrict U M n).hom ≫
      modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n := by
  induction n with
  | zero =>
    change (Scheme.Modules.restrictFunctor U.ι).map (𝟙 (structureSheaf X)) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom =
      (Scheme.Modules.restrictUnitIso U.ι).hom ≫ 𝟙 _
    erw [(Scheme.Modules.restrictFunctor U.ι).map_id, Category.id_comp]
  | succ n hn =>
    change (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f (modulePowMap f n)) ≫
      ((moduleTensorRestrict U N (modulePow X N n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U N n)).hom) =
      ((moduleTensorRestrict U M (modulePow X M n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)).hom) ≫
          moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map f)
            (modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n)
    simp only [moduleTensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, moduleTensorRestrict_natural, Category.assoc,
      ← moduleTensorMap_comp, Category.comp_id, hn]
    rw [Category.assoc, ← moduleTensorMap_comp, Category.id_comp]

lemma modulePowMap_restrict_isIso (U : X.Opens) {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n)) := by
  have h := modulePowRestrict_natural U f n
  have heq : (Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n) =
      (modulePowRestrict U M n).hom ≫
        modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n ≫
          (modulePowRestrict U N n).inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

lemma powerSection_restrict_isIso (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (powerSection s n)) := by
  let := modulePowMap_restrict_isIso U s n
  unfold powerSection
  rw [(Scheme.Modules.restrictFunctor U.ι).map_comp]
  infer_instance

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

def powerRestrictionUnit (U : X.Opens) (n : ℕ) :
    structureSheaf U.toScheme ≅ structureSheaf U.toScheme :=
  (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso (unitPowerIso n).symm ≪≫
      modulePowRestrict U (structureSheaf X) n ≪≫
        (modulePowFunctor n).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
          unitPowerIso n

lemma restrictPowerSection_factor (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom =
      (powerRestrictionUnit U n).hom ≫
        powerSection (restrictSection U.ι s) n := by
  have hs : (Scheme.Modules.restrictUnitIso U.ι).hom ≫ restrictSection U.ι s =
      (Scheme.Modules.restrictFunctor U.ι).map s := by
    let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let e : F.obj (structureSheaf X) ≅ structureSheaf U.toScheme :=
      Scheme.Modules.restrictUnitIso U.ι
    exact e.hom_inv_id_assoc (F.map s)
  dsimp only [restrictSection, powerSection, powerRestrictionUnit, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, modulePowFunctor]
  erw [(Scheme.Modules.restrictFunctor U.ι).map_comp]
  repeat' erw [Category.assoc]
  erw [modulePowRestrict_natural]
  erw [Iso.hom_inv_id_assoc, ← modulePowMap_comp]
  erw [show (Scheme.Modules.restrictUnitIso U.ι).hom ≫
      ((Scheme.Modules.restrictUnitIso U.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map s) =
        (Scheme.Modules.restrictFunctor U.ι).map s from hs]
  rfl

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SectionPowerOpens
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

def localPowerFrame (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) :
    (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme :=
  modulePowRestrict U M n ≪≫ globalPowerFrame e n

lemma local_powerSection_coefficient (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (localPowerFrame U e n) (restrictSection U.ι (powerSection s n)) =
      endValue (powerRestrictionUnit U n).hom *
        coefficient e (restrictSection U.ι s) ^ n := by
  change coefficient (globalPowerFrame e n)
    (restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom) = _
  calc
    _ = coefficient (globalPowerFrame e n)
        ((powerRestrictionUnit U n).hom ≫ powerSection (restrictSection U.ι s) n) :=
      congrArg (coefficient (globalPowerFrame e n)) (restrictPowerSection_factor U s n)
    _ = endValue (powerRestrictionUnit U n).hom *
        coefficient (globalPowerFrame e n) (powerSection (restrictSection U.ι s) n) :=
      coefficient_precompose _ _ _
    _ = _ := congrArg (endValue (powerRestrictionUnit U n).hom * ·)
      (powerSection_coefficient e _ n)

end Geometry

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_LinePullback
attribute [-instance] _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {X Y : Scheme.{0}}

def LineBundle.pullback (L : LineBundle X) (f : Y ⟶ X) : LineBundle Y where
  sheaf := (Scheme.Modules.pullback f).obj L.sheaf
  locallyRankOne y := by
    obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
    refine ⟨f ⁻¹ᵁ U,hy,⟨pullbackRestrictIso f L.sheaf U ≪≫
      (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫ ?_⟩⟩
    letI : (Opens.map (f ∣_ U).base).Final := opensMap_final (f ∣_ U)
    letI : (SheafOfModules.pushforward (f ∣_ U).toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward (f ∣_ U)).IsRightAdjoint
    let hu : IsIso (SheafOfModules.pullbackObjUnitToUnit (f ∣_ U).toRingCatSheafHom) :=
      SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (f ∣_ U).toRingCatSheafHom
    let a : (SheafOfModules.pullback (f ∣_ U).toRingCatSheafHom).obj
        (SheafOfModules.unit U.toScheme.ringCatSheaf) ≅
        SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
      @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit (f ∣_ U).toRingCatSheafHom) hu
    exact { hom := a.hom, inv := a.inv, hom_inv_id := a.hom_inv_id, inv_hom_id := a.inv_hom_id }

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_LinePowerLaws
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma sheafification_tensor_right_isIso
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ Q) (L : LineBundle X)
    [IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) f (𝟙 L.sheaf.val))) := by
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  apply PiExponent.NumericalAmpleness.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  let S : PresheafOfModules U.toScheme.ringCatSheaf.obj ⥤ U.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := U.toScheme.presheaf)
  have hf : IsIso (S.map (R.map f)) := by
    apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) f).mp
    change IsIso ((Scheme.Modules.restrictFunctor U.ι).map (F.map f))
    let : IsIso (F.map f) := inferInstanceAs
      (IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f))
    exact (Scheme.Modules.restrictFunctor U.ι).map_isIso (F.map f)
  let ep : R.obj L.sheaf.val ≅ 𝟙_ (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    (SheafOfModules.forget _).mapIso e
  have ht : IsIso (S.map ((R.map f) ⊗ₘ 𝟙 (R.obj L.sheaf.val))) :=
    TensorLocalization.map_tensor_right_unit S (R.map f) ep
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) _).mpr
  let g := PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) f (𝟙 L.sheaf.val)
  change IsIso (S.map (R.map g))
  have heq := modulePresheafTensorRestrict_natural U f (𝟙 L.sheaf.val)
  let : IsIso (S.map (modulePresheafTensorRestrict U P L.sheaf.val).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U P L.sheaf.val)).isIso_hom
  let : IsIso (S.map (modulePresheafTensorRestrict U Q L.sheaf.val).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U Q L.sheaf.val)).isIso_hom
  have hcomp : IsIso (S.map (R.map g ≫
      (modulePresheafTensorRestrict U Q L.sheaf.val).hom)) := by
    erw [heq, S.map_comp]
    have ht' : IsIso (S.map
        (PresheafOfModules.Monoidal.tensorHom (R := U.toScheme.presheaf)
          (R.map f) (R.map (𝟙 L.sheaf.val)))) := by
      rw [R.map_id]
      exact ht
    exact (inferInstance : IsIso (C := U.toScheme.Modules)
      (S.map (modulePresheafTensorRestrict U P L.sheaf.val).hom ≫ S.map
        (PresheafOfModules.Monoidal.tensorHom (R := U.toScheme.presheaf)
          (R.map f) (R.map (𝟙 L.sheaf.val)))))
  erw [S.map_comp] at hcomp
  exact (isIso_comp_right_iff (C := U.toScheme.Modules) _ _).mp hcomp

end

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory BraidedCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def sheafificationTensorRight (P : PresheafOfModules X.ringCatSheaf.obj)
    (L : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P L.sheaf.val) ≅
    moduleTensor X ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P)
      L.sheaf := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  have : IsIso (F.map η) :=
    isIso_of_comp_hom_eq_id _
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components P)
  let ht : IsIso (F.map (PresheafOfModules.Monoidal.tensorHom
      (R := X.presheaf) η (𝟙 L.sheaf.val))) := sheafification_tensor_right_isIso η L
  exact @asIso _ _ _ _ (F.map (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
    η (𝟙 L.sheaf.val))) ht

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCharts
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] Classical.propDecidable

variable {R σ : Type*} [CommRing R] (i : σ)
attribute [local instance] MvPolynomial.gradedAlgebra

def polyToChart : MvPolynomial (ChartVariables i) R →+* PolyChart (R := R) i :=
  eval₂Hom (chartConstants i) (fun j => chartCoordinate i j.val)

lemma chartToPoly_comp_polyToChart :
    (chartToPoly (R := R) i).comp (polyToChart i) = RingHom.id _ := by
  classical
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [polyToChart]
  · intro j
    simp [polyToChart, j.property]

lemma chart_val_mk (n : ℕ) (p : MvPolynomial σ R)
    (hp : p ∈ PolyGrade R σ (n • 1)) :
    (Away.mk _ (poly_X_mem (R := R) i) n p hp).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) p *
        (IsLocalization.Away.invSelf (X (R := R) i)) ^ n := by
  rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  congr 1
  rw [IsLocalization.Away.invSelf, ← IsLocalization.mk'_pow]
  simp only [one_pow]
  rfl

lemma chart_val_constants (r : R) :
    (chartConstants i r).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (C r) := by
  exact (chart_val_mk i 0 (C r) (by simp)).trans
    (by simp only [pow_zero, mul_one])

lemma chart_val_coordinate (j : σ) :
    (chartCoordinate (R := R) i j).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (X j) *
        IsLocalization.Away.invSelf (X (R := R) i) := by
  rw [chartCoordinate, chart_val_mk, pow_one]

lemma chart_dehomogenize_val :
    (algebraMap (PolyChart (R := R) i) (Localization.Away (X i))).comp
      ((polyToChart i).comp (dehomogenize i)) =
    eval₂Hom ((algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i))).comp C)
      (fun j => IsLocalization.Away.invSelf (X (R := R) i) *
        algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (X j)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [dehomogenize, polyToChart, chart_val_constants]
  · intro j
    by_cases h : j = i
    · subst j
      simp only [RingHom.comp_apply, dehomogenize_X_self, map_one, eval₂Hom_X']
      symm
      rw [mul_comm]
      exact IsLocalization.Away.mul_invSelf (X i)
    · simp [dehomogenize, polyToChart, h, chart_val_coordinate, mul_comm]

lemma polyToChart_comp_chartToPoly :
    (polyToChart (R := R) i).comp (chartToPoly i) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (poly_X_mem (R := R) i) x
  apply HomogeneousLocalization.val_injective _
  simp only [RingHom.comp_apply, RingHom.id_apply, chartToPoly_mk, chart_val_mk]
  have he := RingHom.congr_fun (chart_dehomogenize_val (R := R) i) p
  change (polyToChart i (dehomogenize i p)).val = _ at he
  rw [he]
  change eval₂ _ _ p = _
  rw [homogeneous_eval₂_scale (by simpa using hp)]
  have hid : eval₂Hom ((algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i))).comp C)
      (fun j => algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (X j)) =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) := by
    apply MvPolynomial.ringHom_ext <;> intro r <;> simp
  change _ * (eval₂Hom _ _ p) = _
  rw [hid]
  exact mul_comm _ _

def polynomialChartEquiv : PolyChart (R := R) i ≃+* MvPolynomial (ChartVariables i) R :=
  { chartToPoly i with
    invFun := polyToChart i
    left_inv := fun p => RingHom.congr_fun (polyToChart_comp_chartToPoly i) p
    right_inv := fun p => RingHom.congr_fun (chartToPoly_comp_polyToChart i) p }

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

lemma standardChart_cover :
    (⨆ i : σ, Proj.basicOpen (PolyGrade R σ) (X i)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ R
  rw [← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

end PiExponentSeshadri.Projective

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinates
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
variable {A R σ : Type u} [CommRing A] [CommRing R] [SetLike σ A]
  [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
  (f : A →+* R)

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

lemma fromUnitCoordinate_preimage {s t : A} {e : ℕ} (hs : s ∈ 𝒜 1)
    (hu : IsUnit (f s)) (hsone : f s = 1) (he : 0 < e) (ht : t ∈ 𝒜 e) :
    fromUnitCoordinate f (by decide) hs hu ⁻¹ᵁ Proj.basicOpen 𝒜 t =
      PrimeSpectrum.basicOpen (f t) := by
  rw [fromUnitCoordinate, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜 hs (by decide) ht he, SpecMap_preimage_basicOpen]
  congr 1
  change evalAway f s hu (Away.isLocalizationElem hs ht) = f t
  have H := evalAway_mk_clear f hs hu e (t ^ 1)
    (show t ^ 1 ∈ 𝒜 (e • 1) from by simpa using ht)
  simpa only [Away.isLocalizationElem, hsone, one_pow, mul_one, pow_one] using H

theorem fromUnitCoordinate_eq {s t : A} {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hu : IsUnit (f s)) (hv : IsUnit (f t)) :
    fromUnitCoordinate f hd hs hu = fromUnitCoordinate f he ht hv := by
  have huv : IsUnit (f (s * t)) := by rw [map_mul]; exact hu.mul hv
  have hvu : IsUnit (f (t * s)) := by rw [map_mul]; exact hv.mul hu
  rw [fromUnitCoordinate_mul f hd hs ht hu huv,
    fromUnitCoordinate_mul f he ht hs hv hvu]
  congr 1 <;> ac_rfl

end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinatesMap (X : Scheme.{u}) (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤))
    (i : σ) (hi : a i = 1) : X ⟶ Proj (homogeneousSubmodule σ K) :=
  X.toSpecΓ ≫ fromUnitCoordinate (eval₂Hom k a) (by decide)
    (coordinates_X_mem (K := K) i) (by simpa only [eval₂Hom_X', hi] using isUnit_one)

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

lemma coordinatesMap_preimage (X : Scheme.{u}) (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) (j : σ) :
    coordinatesMap X k a i hi ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j) = X.basicOpen (a j) := by
  rw [coordinatesMap, Scheme.Hom.comp_preimage,
    fromUnitCoordinate_preimage _ (coordinates_X_mem (K := K) i) _
      (by simpa only [eval₂Hom_X'] using hi) (by decide) (coordinates_X_mem (K := K) j),
    eval₂Hom_X', Scheme.toSpecΓ_preimage_basicOpen]

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

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}

def atlasOfFramedSections {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (𝒰 : X.OpenCover)
    (e : ∀ i, M.restrict (𝒰.f i) ≅ O (𝒰.X i)) (index : 𝒰.I₀ → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (𝒰.f i) (s (index i))) = 1) :
    CoordinateAtlas (K := K) (σ := σ) X where
  cover := 𝒰
  scalars i := (𝒰.f i).appTop.hom.comp k
  coordinates i q := coefficient (e i) (restrictSection (𝒰.f i) (s q))
  index := index
  normalized := hnorm
  scalarOverlap i j := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    congr 1
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      congrArg (fun f : pullback (𝒰.f i) (𝒰.f j) ⟶ X => f.appTop.hom)
        (pullback.condition (f := 𝒰.f i) (g := 𝒰.f j))
  coordinateOverlap i j := by
    obtain ⟨c, hc⟩ := overlap_coefficients (𝒰.f i) (𝒰.f j)
      (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd (𝒰.f i) (𝒰.f j))
      (pullback.condition (f := 𝒰.f i) (g := 𝒰.f j)) (e i) (e j)
    exact ⟨c, fun q => hc (s q)⟩

def sectionFrame {M : X.Modules} (s : O X ⟶ M) :
    M.restrict (SectionOpens.isoOpen s).ι ≅ O (SectionOpens.isoOpen s).toScheme := by
  letI := SectionOpens.isIso_restrict_isoOpen s
  exact (asIso ((Scheme.Modules.restrictFunctor (SectionOpens.isoOpen s).ι).map s)).symm ≪≫
    Scheme.Modules.restrictUnitIso (SectionOpens.isoOpen s).ι

lemma sectionFrame_normalized {M : X.Modules} (s : O X ⟶ M) :
    coefficient (sectionFrame s) (restrictSection (SectionOpens.isoOpen s).ι s) = 1 := by
  change coefficient (sectionFrame s) (sectionFrame s).inv = 1
  exact coefficient_frame (sectionFrame s)

def sectionsMorphism {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K) :=
  (atlasOfFramedSections k s
    (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover)
    (fun i => sectionFrame (s i)) id (fun i => sectionFrame_normalized (s i))).morphism

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma sectionsMorphism_local {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (i : σ) :
    (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hcover =
      coordinatesMap (SectionOpens.isoOpen (s i)).toScheme
        ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))) i
        (sectionFrame_normalized (s i)) := by
  exact CoordinateAtlas.cover_morphism
    (atlasOfFramedSections k s
      (X.openCoverOfIsOpenCover (fun a => SectionOpens.isoOpen (s a)) hcover)
      (fun a => sectionFrame (s a)) id (fun a => sectionFrame_normalized (s a))) i

theorem sectionsMorphism_preimage {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (j : σ) :
    sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j) =
      SectionOpens.isoOpen (s j) := by
  ext x
  have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let U := SectionOpens.isoOpen (s i)
  have H : U.ι ⁻¹ᵁ (sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j)) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen (s j) := by
    rw [← Scheme.Hom.comp_preimage, sectionsMorphism_local,
      coordinatesMap_preimage, preimage_isoOpen (s j) U.ι (sectionFrame (s i))]
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : U.toScheme)

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames

end PiExponentSeshadri.Projective

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveChartOverlaps
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R σ : Type*} [CommRing R] (i j : σ)
lemma coordinate_chart_preimage :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (X j) =
      PrimeSpectrum.basicOpen (chartCoordinate (R := R) i j) := by
  rw [Proj.awayι_preimage_basicOpen _ _ (by decide) (poly_X_mem j) (by decide)]
  congr 1
  apply HomogeneousLocalization.val_injective _
  simp [HomogeneousLocalization.Away.isLocalizationElem, chartCoordinate,
    HomogeneousLocalization.Away.val_mk]

lemma coordinate_finset_preimage (s : Finset σ) :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      (s.inf fun j => Proj.basicOpen (PolyGrade R σ) (X j)) =
      PrimeSpectrum.basicOpen (∏ j ∈ s, chartCoordinate (R := R) i j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; rfl
  | @insert j s hjs ih =>
    simp only [Finset.inf_insert, Finset.prod_insert hjs, Scheme.Hom.preimage_inf, ih,
      coordinate_chart_preimage, PrimeSpectrum.basicOpen_mul]
    rfl

def chartFiniteSectionRingEquiv (s : Finset σ) :
    Γ(Proj (PolyGrade R σ),
      Proj.basicOpen (PolyGrade R σ) (X i) ⊓
        s.inf (fun j => Proj.basicOpen (PolyGrade R σ) (X j))) ≃+*
      Localization.Away (∏ j ∈ s, chartCoordinate (R := R) i j) := by
  let f := Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)
  have e := IsOpenImmersion.ΓIso f (s.inf fun j => Proj.basicOpen (PolyGrade R σ) (X j))
  dsimp only [f] at e
  rw [Proj.opensRange_awayι, coordinate_finset_preimage] at e
  let z := ∏ j ∈ s, chartCoordinate (R := R) i j
  letI : Algebra (PolyChart (R := R) i)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) :=
    AlgebraicGeometry.StructureSheaf.openAlgebra _ _
  letI : IsLocalization.Away z
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen _ _
  exact e.symm.commRingCatIsoToRingEquiv.trans
    (IsLocalization.algEquiv (Submonoid.powers z)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z)
      (Localization.Away z)).toRingEquiv

def chartFinitePolynomialRingEquiv (s : Finset σ) :
    Γ(Proj (PolyGrade R σ),
      Proj.basicOpen (PolyGrade R σ) (X i) ⊓
        s.inf (fun j => Proj.basicOpen (PolyGrade R σ) (X j))) ≃+*
      Localization.Away (∏ j ∈ s, chartToPoly (R := R) i (chartCoordinate i j)) :=
  (chartFiniteSectionRingEquiv i s).trans
    (IsLocalization.ringEquivOfRingEquiv
      (M := Submonoid.powers (∏ j ∈ s, chartCoordinate (R := R) i j))
      (T := Submonoid.powers (∏ j ∈ s, chartToPoly (R := R) i (chartCoordinate i j)))
      (Localization.Away (∏ j ∈ s, chartCoordinate (R := R) i j))
      (Localization.Away (∏ j ∈ s, chartToPoly (R := R) i (chartCoordinate i j)))
      (polynomialChartEquiv i) (by
      rw [Submonoid.map_powers]
      congr 1
      exact map_prod (polynomialChartEquiv i) _ _))

def chartVariableOverlapRingEquiv (s : Finset (ChartVariables i)) :
    Γ(Proj (PolyGrade R σ),
      Proj.basicOpen (PolyGrade R σ) (X i) ⊓
        s.inf (fun j => Proj.basicOpen (PolyGrade R σ) (X j.val))) ≃+*
      Localization.Away (∏ j ∈ s, (X j : MvPolynomial (ChartVariables i) R)) := by
  classical
  have hprod : (∏ j ∈ s.image Subtype.val,
      chartToPoly (R := R) i (chartCoordinate i j)) =
      ∏ j ∈ s, (X j : MvPolynomial (ChartVariables i) R) := by
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro j hj
      simp [chartToPoly_coordinate, j.property]
    · intro a ha b hb hab
      exact Subtype.ext hab
  have e := chartFinitePolynomialRingEquiv (R := R) i (s.image Subtype.val)
  rw [hprod, Finset.inf_image] at e
  exact e

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SectionPowerFrames
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme} {M : X.Modules}

def normalizedPowerFrame (U : X.Opens) (s : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] (n : ℕ) :
    (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme := by
  letI := powerSection_restrict_isIso U s n
  exact (asIso ((Scheme.Modules.restrictFunctor U.ι).map (powerSection s n))).symm ≪≫
    Scheme.Modules.restrictUnitIso U.ι

lemma normalizedPowerFrame_normalized (U : X.Opens) (s : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] (n : ℕ) :
    coefficient (normalizedPowerFrame U s n) (restrictSection U.ι (powerSection s n)) = 1 := by
  change coefficient (normalizedPowerFrame U s n) (normalizedPowerFrame U s n).inv = 1
  exact coefficient_frame _

lemma normalizedPowerFrame_coefficient (U : X.Opens) (si sj : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map si)]
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (hi : coefficient e (restrictSection U.ι si) = 1) (n : ℕ) :
    coefficient (normalizedPowerFrame U si n) (restrictSection U.ι (powerSection sj n)) =
      coefficient e (restrictSection U.ι sj) ^ n := by
  have hc := coefficient_change (localPowerFrame U e n) (normalizedPowerFrame U si n)
    (restrictSection U.ι (powerSection sj n))
  have hbase := coefficient_change (localPowerFrame U e n) (normalizedPowerFrame U si n)
    (restrictSection U.ι (powerSection si n))
  rw [normalizedPowerFrame_normalized, local_powerSection_coefficient, hi,
    one_pow, mul_one] at hbase
  rw [local_powerSection_coefficient, ← mul_assoc, ← hbase, one_mul] at hc
  exact hc

def coordinatePowerFrame (s : structureSheaf X ⟶ M) (n : ℕ) :
    (modulePow X M n).restrict (SectionOpens.isoOpen s).ι ≅
      structureSheaf (SectionOpens.isoOpen s).toScheme := by
  letI := SectionOpens.isIso_restrict_isoOpen s
  exact normalizedPowerFrame _ s n

lemma coordinatePowerFrame_coefficient (si sj : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (coordinatePowerFrame si n)
      (restrictSection (SectionOpens.isoOpen si).ι (powerSection sj n)) =
    coefficient (PiExponentSeshadri.Projective.sectionFrame si)
      (restrictSection (SectionOpens.isoOpen si).ι sj) ^ n := by
  exact @normalizedPowerFrame_coefficient X M _ si sj
    (SectionOpens.isIso_restrict_isoOpen si) (PiExponentSeshadri.Projective.sectionFrame si)
    (PiExponentSeshadri.Projective.sectionFrame_normalized si) n

@[simp] lemma coordinatePowerFrame_normalized (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (coordinatePowerFrame s n)
      (restrictSection (SectionOpens.isoOpen s).ι (powerSection s n)) = 1 := by
  erw [coordinatePowerFrame_coefficient, PiExponentSeshadri.Projective.sectionFrame_normalized, one_pow]
  rfl

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveLaurentVertex
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.ProjectiveLaurentVertex

section

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech

variable {ι : Type*} [Fintype ι]

def encode (i : ι) (d : ℤ) (b : ChartExponent i) : Monomial ι d := by
  classical
  let a : ι → ℤ := fun j => if h : j = i then
    d - ∑ k : {j : ι // j ≠ i}, (b k : ℤ) else (b ⟨j, h⟩ : ℤ)
  have hi : a i = d - ∑ k : {j : ι // j ≠ i}, (b k : ℤ) := by simp [a]
  have ho : ∀ j : {j : ι // j ≠ i}, a j = (b j : ℤ) := by
    intro j
    simp [a, j.property]
  refine ⟨a, ?_⟩
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hi]
  simp_rw [ho]
  omega

@[simp] theorem encode_self (i : ι) (d : ℤ) (b : ChartExponent i) :
    (encode i d b).val i = d - ∑ k : {j : ι // j ≠ i}, (b k : ℤ) := by
  classical
  simp [encode]

@[simp] theorem encode_other (i : ι) (d : ℤ) (b : ChartExponent i)
    (j : {j : ι // j ≠ i}) : (encode i d b).val j = (b j : ℤ) := by
  classical
  simp [encode, j.property]

theorem encode_regular (i : ι) (d : ℤ) (b : ChartExponent i) :
    encode i d b ∈ VertexMonomialSet i d := by
  intro j hj
  simpa only [encode_other i d b ⟨j, hj⟩] using Int.natCast_nonneg (b ⟨j, hj⟩)

def decode (i : ι) (d : ℤ) (a : VertexMonomialSet i d) : ChartExponent i :=
  Finsupp.equivFunOnFinite.symm (fun j => (a.val.val j).toNat)

@[simp] theorem decode_apply (i : ι) (d : ℤ) (a : VertexMonomialSet i d)
    (j : {j : ι // j ≠ i}) : decode i d a j = (a.val.val j).toNat := rfl

@[simp] theorem decode_encode (i : ι) (d : ℤ) (b : ChartExponent i) :
    decode i d ⟨encode i d b, encode_regular i d b⟩ = b := by
  ext j
  simp

@[simp] theorem encode_decode (i : ι) (d : ℤ) (a : VertexMonomialSet i d) :
    encode i d (decode i d a) = a.val := by
  classical
  apply Subtype.ext
  funext j
  by_cases hj : j = i
  · subst j
    rw [encode_self]
    have h := a.val.property
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i] at h
    have hs : (∑ k : {j : ι // j ≠ i}, ((decode i d a k : ℕ) : ℤ)) =
        ∑ k : {j : ι // j ≠ i}, a.val.val k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Int.toNat_of_nonneg (a.property k k.property)
    rw [hs]
    omega
  · change (encode i d (decode i d a)).val (⟨j, hj⟩ : {j : ι // j ≠ i}) = _
    rw [encode_other, decode_apply, Int.toNat_of_nonneg (a.property j hj)]

def exponentEquiv (i : ι) (d : ℤ) : ChartExponent i ≃ VertexMonomialSet i d where
  toFun b := ⟨encode i d b, encode_regular i d b⟩
  invFun := decode i d
  left_inv := decode_encode i d
  right_inv a := Subtype.ext (encode_decode i d a)

variable {R : Type*} [CommRing R]

def vertexPolynomialEquiv (i : ι) (d : ℤ) :
    MvPolynomial {j : ι // j ≠ i} R ≃ₗ[R]
      Finsupp.supported R R (VertexMonomialSet i d) :=
  (AddMonoidAlgebra.coeffLinearEquiv R).trans <|
    (Finsupp.domLCongr (exponentEquiv i d)).trans
      (Finsupp.supportedEquivFinsupp (VertexMonomialSet i d)).symm

def vertexLaurent (i : ι) (d : ℤ) :
    MvPolynomial {j : ι // j ≠ i} R →ₗ[R] Laurent ι R d :=
  (Finsupp.supported R R (VertexMonomialSet i d)).subtype.comp
    (vertexPolynomialEquiv i d).toLinearMap

@[simp] theorem vertexLaurent_monomial (i : ι) (d : ℤ) (b : ChartExponent i) (r : R) :
    vertexLaurent i d (MvPolynomial.monomial b r) = Finsupp.single (encode i d b) r := by
  classical
  simp [vertexLaurent, vertexPolynomialEquiv, MvPolynomial.monomial, exponentEquiv]

@[simp] theorem vertexLaurent_coefficient (i : ι) (d : ℤ) (b : ChartExponent i)
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    vertexLaurent i d p (encode i d b) = p.coeff b := by
  classical
  simp [vertexLaurent, vertexPolynomialEquiv, Finsupp.extendDomain_apply,
    encode_regular, exponentEquiv]
  rfl

end

section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

def fullEncode (i : ι) (d : ℤ) (b : {j : ι // j ≠ i} → ℤ) : Monomial ι d := by
  classical
  let a : ι → ℤ := fun j => if h : j = i then
    d - ∑ k : {j : ι // j ≠ i}, b k else b ⟨j, h⟩
  have hi : a i = d - ∑ k : {j : ι // j ≠ i}, b k := by simp [a]
  have ho : ∀ j : {j : ι // j ≠ i}, a j = b j := by
    intro j
    simp [a, j.property]
  refine ⟨a, ?_⟩
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hi]
  simp_rw [ho]
  omega

@[simp] theorem fullEncode_self (i : ι) (d : ℤ) (b : {j : ι // j ≠ i} → ℤ) :
    (fullEncode i d b).val i = d - ∑ k : {j : ι // j ≠ i}, b k := by
  classical
  simp [fullEncode]

@[simp] theorem fullEncode_other (i : ι) (d : ℤ) (b : {j : ι // j ≠ i} → ℤ)
    (j : {j : ι // j ≠ i}) : (fullEncode i d b).val j = b j := by
  classical
  simp [fullEncode, j.property]

def fullExponentEquiv (i : ι) (d : ℤ) : ({j : ι // j ≠ i} → ℤ) ≃ Monomial ι d where
  toFun := fullEncode i d
  invFun a j := a.val j
  left_inv b := by funext j; simp
  right_inv a := by
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · subst j
      rw [fullEncode_self]
      have h := a.property
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i] at h
      change d - (∑ k : {j : ι // j ≠ i}, a.val k) = a.val i
      omega
    · exact fullEncode_other i d _ ⟨j, hj⟩

def natExponentHom (i : ι) : ChartExponent i →+ ({j : ι // j ≠ i} → ℤ) where
  toFun b j := b j
  map_zero' := by ext j; simp
  map_add' := by intro a b; ext j; simp

def polynomialToGroupAlgebra (i : ι) :
    MvPolynomial {j : ι // j ≠ i} R →+* chartGroupAlgebra (R := R) i :=
  AddMonoidAlgebra.mapDomainRingHom R (natExponentHom i)

def groupAlgebraToLaurent (i : ι) (d : ℤ) : chartGroupAlgebra (R := R) i ≃+ Laurent ι R d :=
  (AddMonoidAlgebra.coeffAddEquiv).trans (Finsupp.domCongr (fullExponentEquiv i d))

omit [Fintype ι] in
@[simp] theorem polynomialToGroupAlgebra_X (i : ι) (j : {j : ι // j ≠ i}) :
    polynomialToGroupAlgebra (R := R) i (MvPolynomial.X j) =
      AddMonoidAlgebra.single (natExponentHom i (Finsupp.single j 1)) 1 := by
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single _ _) = _
  exact AddMonoidAlgebra.mapDomain_single

omit [Fintype ι] in
theorem groupAlgebra_product_isUnit (i : ι) (s : Finset {j : ι // j ≠ i}) :
    IsUnit (polynomialToGroupAlgebra (R := R) i (chartProduct i s)) := by
  rw [chartProduct, map_prod]
  exact IsUnit.prod_iff.mpr fun j _ => by
    rw [polynomialToGroupAlgebra_X]
    exact groupAlgebra_single_isUnit i _

def overlapToGroupAlgebra (i : ι) (s : Finset {j : ι // j ≠ i}) :
    Localization.Away (chartProduct (R := R) i s) →+* chartGroupAlgebra (R := R) i :=
  Localization.awayLift (polynomialToGroupAlgebra i) (chartProduct i s)
    (groupAlgebra_product_isUnit i s)

omit [Fintype ι] in
@[simp] theorem overlapToGroupAlgebra_base (i : ι) (s : Finset {j : ι // j ≠ i})
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    overlapToGroupAlgebra i s (algebraMap _ _ p) = polynomialToGroupAlgebra i p := by
  exact IsLocalization.Away.lift_eq (chartProduct i s) (groupAlgebra_product_isUnit i s) p

def overlapLaurent (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i}) :
    Localization.Away (chartProduct (R := R) i s) →+ Laurent ι R d :=
  (groupAlgebraToLaurent i d).toAddMonoidHom.comp (overlapToGroupAlgebra i s).toAddMonoidHom

def productExponent (i : ι) (s : Finset {j : ι // j ≠ i}) : {j : ι // j ≠ i} → ℤ :=
  ∑ j ∈ s, natExponentHom i (Finsupp.single j 1)

omit [Fintype ι] in
@[simp] theorem polynomialToGroupAlgebra_product (i : ι)
    (s : Finset {j : ι // j ≠ i}) :
    polynomialToGroupAlgebra (R := R) i (chartProduct i s) =
      AddMonoidAlgebra.single (productExponent i s) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [chartProduct, productExponent, Finset.prod_empty, Finset.sum_empty, map_one]
      rfl
  | @insert j s hj ih =>
      simp only [chartProduct, Finset.prod_insert hj, map_mul] at *
      rw [polynomialToGroupAlgebra_X, ih, AddMonoidAlgebra.single_mul_single]
      simp [productExponent, hj]

@[simp] theorem groupAlgebraToLaurent_coefficient (i : ι) (d : ℤ)
    (p : chartGroupAlgebra (R := R) i) (a : Monomial ι d) :
    groupAlgebraToLaurent i d p a = p.coeff (fun j => a.val j) := by
  simp [groupAlgebraToLaurent, fullExponentEquiv]
  rfl

@[simp] theorem fullEncode_nat (i : ι) (d : ℤ) (b : ChartExponent i) :
    fullEncode i d (natExponentHom i b) = encode i d b := rfl

end

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
end PiExponent.GeometrySupport.ProjectiveLaurentVertex

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveChartSections
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ProjectiveChartSections

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology

variable {X : Scheme} (U : X.Opens) (M : X.Modules)

def framedSectionsEquiv (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    Γ(M,U) ≃+ Γ(U.toScheme,⊤) :=
  (restrictionSectionsIso U M).addCommGroupIsoToAddEquiv.symm.trans
    { toFun := fun x => e.hom.val.app (op ⊤) x
      invFun := fun x => e.inv.val.app (op ⊤) x
      left_inv := fun x => by
        have h := congrArg (fun f => f.val.app (op ⊤) x) e.hom_inv_id
        exact h
      right_inv := fun x => by
        have h := congrArg (fun f => f.val.app (op ⊤) x) e.inv_hom_id
        exact h
      map_add' := fun x y => map_add _ _ _ }

def framedCoefficientsEquiv (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    Γ(M,U) ≃+ Γ(X,U) :=
  (framedSectionsEquiv U M e).trans U.topIso.commRingCatIsoToRingEquiv.toAddEquiv

def framedHomCoefficientsEquiv (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    (schemeFreeOpen_p0 X U ⟶ M) ≃+ Γ(X,U) :=
  (freeOpenAddEquiv U M).trans (framedCoefficientsEquiv U M e)

def framedHomRingEquiv {A : Type*} [CommRing A]
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (r : Γ(X,U) ≃+* A) :
    (schemeFreeOpen_p0 X U ⟶ M) ≃+ A :=
  (framedHomCoefficientsEquiv U M e).trans r.toAddEquiv

open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
variable {R ι : Type} [CommRing R] [Fintype ι] (i : ι) (d : ℤ)

def framedLaurentOverlap (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s)) :
    (schemeFreeOpen_p0 X U ⟶ M) →+ Laurent ι R d :=
  (overlapLaurent i d s).comp (framedHomRingEquiv U M e r).toAddMonoidHom

end PiExponentSeshadri.ProjectiveChartSections

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateSections
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (k : K →+* Γ(X,⊤))
variable (s : σ → (O X ⟶ M)) (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
include hf

lemma sectionOpen_eq_coordinate_preimage (i : σ) :
    SectionOpens.isoOpen (s i) = f.hom ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) := by
  rw [← hf]
  exact (sectionsMorphism_preimage k s hc i).symm

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateFiniteSections
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final
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
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (s : σ → (O X ⟶ M))

def coordinateFiniteOpen (i : σ) (a : Finset (ChartVariables i)) : X.Opens :=
  SectionOpens.isoOpen (s i) ⊓ a.inf (fun j => SectionOpens.isoOpen (s j.val))

variable (k : K →+* Γ(X,⊤)) (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
include hf

lemma coordinateFiniteOpen_eq_preimage (i : σ) (a : Finset (ChartVariables i)) :
    coordinateFiniteOpen M s i a = f.hom ⁻¹ᵁ
      (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) ⊓
        a.inf (fun j => Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X j.val))) := by
  classical
  unfold coordinateFiniteOpen
  rw [Scheme.Hom.preimage_inf, ← sectionOpen_eq_coordinate_preimage M k s hc f hf i]
  congr 1
  induction a using Finset.induction_on with
  | empty => simp
  | @insert j a hj ih =>
    rw [Finset.inf_insert, Finset.inf_insert, Scheme.Hom.preimage_inf,
      ← sectionOpen_eq_coordinate_preimage M k s hc f hf j.val, ih]

def coordinateFiniteRingEquiv (i : σ) (a : Finset (ChartVariables i)) :
    Γ(X,coordinateFiniteOpen M s i a) ≃+*
      Localization.Away (chartProduct (R := K) i a) :=
  (X.presheaf.mapIso (eqToIso
    (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).symm).op).commRingCatIsoToRingEquiv.trans
      ((isoPreimageSectionRingEquiv f _).trans (chartVariableOverlapRingEquiv i a))

variable [Fintype σ]

def coordinatePowerOverlap (n : ℕ) (i : σ) (a : Finset (ChartVariables i)) :
    (schemeFreeOpen_p1 X (coordinateFiniteOpen M s i a) ⟶ modulePow X M n) →+
      Laurent σ K n :=
  framedLaurentOverlap _ (modulePow X M n) i n a
    (restrictOpenFrame (show coordinateFiniteOpen M s i a ≤ SectionOpens.isoOpen (s i) from inf_le_left)
      (coordinatePowerFrame (s i) n))
    (coordinateFiniteRingEquiv M s k hc f hf i a)

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_LineBundleGluing
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.LineBundleGluing

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry

variable {X : Scheme} {ι : Type} (U : ι → X.Opens)

variable {U} (c : Cocycle U)

def lineBundle (hcover : ⊤ ≤ ⨆ i, U i) : LineBundle X where
  sheaf := sheaf c
  locallyRankOne x := by
    have hx : x ∈ ⨆ i, U i := hcover (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨U i,hi,⟨openFrame c i (U i) le_rfl⟩⟩

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

end PiExponentSeshadri.LineBundleGluing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveRatioCocycle
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open HomogeneousLocalization PiExponentSeshadri.Projective
open PiExponentSeshadri.LineBundleGluing

variable {R σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateRatio_self (i : σ) (W : (projectiveSpace R σ).Opens)
    (hi : W ≤ coordinateOpen i) : coordinateRatio i i W hi = 1 := by
  apply Subtype.ext
  funext x
  let : x.1.asHomogeneousIdeal.toIdeal.IsPrime := x.1.isPrime
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.mk ⟨1, ⟨X i, poly_X_mem i⟩, ⟨X i, poly_X_mem i⟩, hi x.2⟩).val = (1 : HomogeneousLocalization.AtPrime (PolyGrade R σ) x.1.asHomogeneousIdeal.toIdeal).val
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one]
  exact Localization.mk_self (⟨X i, hi x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)

def ratioUnit (i j : σ) (W : (projectiveSpace R σ).Opens)
    (hi : W ≤ coordinateOpen i) (hj : W ≤ coordinateOpen j) : Γ(projectiveSpace R σ, W)ˣ where
  val := coordinateRatio i j W hi
  inv := coordinateRatio j i W hj
  val_inv := (coordinateRatio_mul i j i W hi hj).trans (coordinateRatio_self i W hi)
  inv_val := (coordinateRatio_mul j i j W hj hi).trans (coordinateRatio_self j W hj)

def coordinateCocycle : Cocycle (coordinateOpen (R := R) (σ := σ)) where
  transition := ratioUnit
  restriction := fun i j {_ _} h hi _ => coordinateRatio_restrict i j h hi
  identity i W hi := Units.ext (coordinateRatio_self i W hi)
  cocycle i j k W hi hj _ := Units.ext (coordinateRatio_mul i j k W hi hj)

def lineBundle : PiExponentSeshadri.Geometry.LineBundle (projectiveSpace R σ) :=
  PiExponentSeshadri.LineBundleGluing.lineBundle coordinateCocycle
    (by rw [show (⨆ i : σ, coordinateOpen (R := R) i) = ⊤ from standardChart_cover])

end PiExponent.ProjectiveO1

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveO1ChartMap
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final
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

def scalars : R →+* Γ(projectiveSpace R σ, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (polynomialProjectiveProjection R σ).appTop).hom

def chartRatios (i : σ) (j : σ) : Γ((coordinateOpen (R := R) i).toScheme, ⊤) :=
  (coordinateOpen (R := R) i).topIso.inv (coordinateRatio i j (coordinateOpen i) le_rfl)

@[simp] theorem chartRatios_self (i : σ) : chartRatios (R := R) i i = 1 := by
  simp [chartRatios, coordinateRatio_self]

end PiExponent.ProjectiveO1

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveO1Sections
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.LineBundleGluing PiExponentSeshadri.Frames

variable {R σ : Type} [CommRing R]

def coordinateCoefficients (k : σ) (V : (projectiveSpace R σ).Opens) :
    sections (coordinateCocycle (R := R) (σ := σ)) V :=
  ⟨fun p => coordinateRatio p.1 k p.2.val p.2.property.2,
   ⟨fun i _ _ _ hi h => coordinateRatio_restrict i k h hi,
    fun i j W _ hi hj => (coordinateRatio_mul i j k W hi hj).symm⟩⟩

def coordinateSection (k : σ) :
    O (projectiveSpace R σ) ⟶ (lineBundle (R := R) (σ := σ)).sheaf :=
  globalSection coordinateCocycle (coordinateCoefficients k ⊤)

end PiExponent.ProjectiveO1

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveO1Morphism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.LineBundleGluing

variable {R σ : Type} [CommRing R]

def coordinateOpenFrame (i : σ) :
    (lineBundle (R := R) (σ := σ)).sheaf.restrict (coordinateOpen i).ι ≅
      O (coordinateOpen (R := R) i).toScheme :=
  openFrame (coordinateCocycle (R := R) (σ := σ)) i (coordinateOpen i) le_rfl

attribute [local irreducible] coordinateSection lineBundle coordinateCocycle scalars coordinateOpenFrame
  sectionsMorphism CoordinateAtlas.morphism atlasOfFramedSections

end PiExponent.ProjectiveO1

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_WeightedProjectiveLineBundle
attribute [-instance] _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.LineBundleGluing

variable {R ι σ : Type} [CommRing R]

def lineBundle (a : σ → ι →₀ ℕ) : LineBundle (Proj (imageGrade (R := R) a)) :=
  (ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback (projectiveMonomialMap a)

def coordinateSection (a : σ → ι →₀ ℕ) (s : σ) :
    O (Proj (imageGrade (R := R) a)) ⟶ (lineBundle a).sheaf :=
  pullbackSection (projectiveMonomialMap a) (ProjectiveO1.coordinateSection s)

end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupGeometry
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

abbrev constantIndex : Index d := (scale d).constantIndex d.curveDegreeWeights_pos
abbrev coordinateIndex : Fin (d.m+1) → Index d :=
  (scale d).coordinateIndex d.curveDegreeWeights_pos

abbrev compactification : Scheme := Proj (WeightedCompactification.imageGrade (R := ℂ) (exponents d))

def affineChart : CompactLogJetIdeal.affineSpace d.m ⟶ compactification d :=
  WeightedCompactification.affineChartMap (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end


