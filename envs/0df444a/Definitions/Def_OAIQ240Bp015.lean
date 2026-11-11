-- Prove2me | Definitions.Def_OAIQ240Bp015
-- name    : OAIQ240Bp015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:36:56.0782+00:00
-- url     : https://prove2.me/theorems/b51815cd-5955-41be-b4d0-6069781fe188
-- title:
--   Definitions bundle OAIQ240Bp015 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 216 declarations of OpenAI's Lean: 113 definitions, 2 inductive types or structures, 4 instances and 97 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst11`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst12`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst13`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst14`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.lsoInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.affineCorrection`, `OAI.HigherDimensionalBallPacking.Rigidity.angularPole`, `OAI.HigherDimensionalBallPacking.Rigidity.circlePlane`, `OAI.HigherDimensionalBallPacking.Rigidity.correctedPrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.curveDensity`, `OAI.HigherDimensionalBallPacking.Rigidity.curvePrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.defectEnergy`, `OAI.HigherDimensionalBallPacking.Rigidity.parametricObstruction`, `OAI.HigherDimensionalBallPacking.Rigidity.planeRotation`, `OAI.HigherDimensionalBallPacking.Rigidity.poleSum`, `OAI.HigherDimensionalBallPacking.Rigidity.sourceRadialCutoff`, `OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure`, `OAI.HigherDimensionalBallPacking.Rigidity.symplecticEnergy`, `OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare`, `OAI.PackingSufficiencySupport.CubicModel.CubicConeModel`, `OAI.PackingSufficiencySupport.CubicModel.CubicConeSpace`, `OAI.PackingSufficiencySupport.CubicModel.CubicPhysicalModel`, `OAI.PackingSufficiencySupport.CubicModel.CubicPhysicalSpace`, `OAI.PackingSufficiencySupport.CubicModel.ambientWeightedCoefficient`, `OAI.PackingSufficiencySupport.CubicModel.centralCubicCoordinates`, `OAI.PackingSufficiencySupport.CubicModel.centralCubicPrimitive`, `OAI.PackingSufficiencySupport.CubicModel.coefficientNorm`, `OAI.PackingSufficiencySupport.CubicModel.conePolynomial`, `OAI.PackingSufficiencySupport.CubicModel.cubicAmbientForm` and 75 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `BallPacking_Annuli_AnnularChartNormalization`, `BallPacking_Annuli_AnnularEmbeddedChart`, `BallPacking_Annuli_AnnularHandleCurvature`, `BallPacking_Annuli_AnnularHandleDensity`, `BallPacking_Annuli_QuadricCylinderChart`, `BallPacking_Annuli_SurfacePathPositivity`, `BallPacking_Annuli_SurfaceSuspensionCoefficients`, `BallPacking_BallMaps_SixCubicInnerNormalPacking`, `BallPacking_BallMaps_SphereCartesianDescent`, `BallPacking_Campanato_MeasureEnergy`, `BallPacking_Campanato_TranslatedSquare`, `BallPacking_CircleAction_CircleRelativeRadialMoser`, `BallPacking_Compactness_AffineCorrectionInfinity`, `BallPacking_Compactness_GradientBounds`, `BallPacking_Compactness_JetCauchy`, `BallPacking_DiskMaps_CubicAreaExhaustion`, `BallPacking_Energy_CircularEnergy`, `BallPacking_Energy_ResidualEnergy`, `BallPacking_Forms_CubicFubiniStudy`, `BallPacking_Fredholm_CompactFredholmAlternative`, `BallPacking_Fredholm_FrameFredholm`, `BallPacking_Fredholm_NonlinearReduction`, `BallPacking_Hamiltonian_AnnularDensityMass`, `BallPacking_Hamiltonian_CartesianMomentSlices`, `BallPacking_Hamiltonian_LiftedCompact`, `BallPacking_Hamiltonian_ScaledPlanarMotion`, `BallPacking_Hopf_DegreeHopfDeformation`, `BallPacking_Hopf_DegreeRelativeShell`, `BallPacking_Hopf_SixLargeQuadricPacking`, `BallPacking_Models_RationalSlack`, `BallPacking_Moser_ManifoldExteriorNaturality`, `BallPacking_Normal_CompactDegenerationTransfer`, `BallPacking_Normal_CubicToricAmbient`, `BallPacking_Projective_CubicEndCoordinates`, `BallPacking_Projective_SixLargeCubicPacking`, `BallPacking_Residues_AreaPolarChart`, `BallPacking_Rigidity_AngularPoles`, `BallPacking_Rigidity_Correction`, `BallPacking_Rigidity_CurveArea`, `BallPacking_SurfaceArea_CubicRadialEndSmooth`, `BallPacking_SurfaceArea_QuadricEndResidueMass`, `BallPacking_SurfaceArea_QuadricSmoothExhaustion`, `BallPacking_Surfaces_QuadricAnnulusDomain`, `BallPacking_Surfaces_QuadricCurveManifold`, `BallPacking_Surfaces_QuadricInfinityDiffeomorph`, `BallPacking_Toric_CubicCoefficientDifferential`, `BallPacking_Toric_RadialDiskSmooth`, `BallPacking_Toric_RestrictedMassIndependence`, `BallPacking_Toric_StationaryManifoldPullback`.
--
--   **Imports.** It imports the published bundle `Def_BallPacking`; the bundles `OAIQ240Bp010`, `OAIQ240Bp011` and `OAIQ240Bp012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp017`, `OAIQ240Bp018` and `OAIQ240Bp019`; the statements `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_framedJetPrincipal_add_compact_fredholm`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.framedJetPrincipal_add_compact_fredholm_bp240`, `OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_exact_family_with_zero_bp240` and `OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_normal_transfer_into_bp240`; the proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.disk_nonlinear_jet_cauchy_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_framedJetPrincipal_add_compact_fredholm`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.framedJetPrincipal_add_compact_fredholm_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_exact_fibre_embedding_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_exact_fibre_embedding_into_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_radial_exact_moser_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_rounded_intervals_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_uniform_compact_exact_fibre_embedding_central_into_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.horizontal_moser_endpoint_bp240` and `OAI.PackingSufficiencySupport.Hamiltonian.manifold_exact_sublevel_moser_bp240`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp010
import Definitions.Def_OAIQ240Bp011
import Definitions.Def_OAIQ240Bp012

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricCurveManifold
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter
section
variable {m : ℕ} (a : Fin m → ℂ) [ha : Fact (Injective a)] [ha0 : Fact (∀ j,a j≠0)]

instance curveChartedSpace : ChartedSpace ℂ (locus a) where
  atlas := range (fun x => (normalChartAt a x).sliceChart x)
  chartAt x := (normalChartAt a x).sliceChart x
  mem_chart_source x := mem_normalChartAt a x
  chart_mem_atlas x := mem_range_self x

instance realSurfaceChartedSpace : ChartedSpace RealModel (locus a) where
  atlas := range (realChart a)
  chartAt := realChart a
  mem_chart_source x := by rw [realChart_source]; exact mem_normalChartAt a x
  chart_mem_atlas x := mem_range_self x

theorem real_inclusion_contMDiff :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,Affine m) ∞ (Subtype.val : locus a → Affine m) := by
  intro x
  have he : chartAt RealModel x=realChart a x := rfl
  rw [contMDiffAt_iff]
  constructor
  · exact continuous_subtype_val.continuousAt
  · have hs := ((normalChartAt a x).sliceChart_inverse_smooth x).restrict_scalars ℝ
    have hp : (chartAt ℂ x x)∈((normalChartAt a x).sliceChart x).target :=
      ((normalChartAt a x).sliceChart x).map_source (mem_normalChartAt a x)
    have ht := (hs _ hp).contDiffAt (((normalChartAt a x).sliceChart x).open_target.mem_nhds hp)
    have hc := ht.comp (x := Complex.equivRealProdCLM (chartAt ℂ x x))
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt
    have heC : chartAt ℂ x=(normalChartAt a x).sliceChart x := rfl
    simpa only [mfld_simps,he,heC,realChart,chartAt_self_eq,
      OpenPartialHomeomorph.refl_apply,Function.comp_def,
      ContinuousLinearEquiv.coe_toHomeomorph,
      ← ContinuousLinearEquiv.toHomeomorph_symm] using hc.contDiffWithinAt

end
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → locus a} {s : Set E} {x : E}

theorem real_contMDiffWithinAt_of_ambient
    (hf : ContDiffWithinAt ℝ ∞ (fun t => (f t : Affine m)) s x) :
    ContMDiffWithinAt 𝓘(ℝ,E) 𝓘(ℝ,RealModel) ∞ f s x := by
  rw [contMDiffWithinAt_iff_target]
  refine ⟨tendsto_subtype_rng.mpr hf.continuousWithinAt,?_⟩
  have he : chartAt RealModel (f x)=realChart a (f x) := rfl
  have hc := Complex.equivRealProdCLM.contDiff.comp_contDiffWithinAt
    (((curveCoordinate (normalChartAt a (f x)).coordinate).contDiff.restrict_scalars ℝ).comp_contDiffWithinAt hf)
  apply contMDiffWithinAt_iff_contDiffWithinAt.mpr
  simpa only [mfld_simps,he,realChart,NormalChart.sliceChart_apply,
    ContinuousLinearEquiv.coe_toHomeomorph,Function.comp_def] using hc

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricInfinityDiffeomorph
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian
open scoped BigOperators
section
variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
  (ε : Fin m → Bool)

theorem realInfinityChart_smooth :
    ContMDiffOn 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (realInfinityChart a ε) (realInfinityChart a ε).source := by
  intro x hx
  rw [realInfinityChart_source] at hx
  apply real_contMDiffWithinAt_of_ambient
  have hc := ((infinityPoint_contDiffAt a ε hx).restrict_scalars ℝ).comp x
    Complex.equivRealProdCLM.symm.contDiff.contDiffAt
  apply hc.contDiffWithinAt.congr
  · intro y hy
    have hyD : Complex.equivRealProdCLM.symm y∈infinityDomain a := by
      simpa only [realInfinityChart_source,mem_preimage] using hy
    rw [realInfinityChart_apply,infinityInverse_val a ε hyD.1]
    rfl
  · rw [realInfinityChart_apply,infinityInverse_val a ε hx.1]
    rfl

theorem realInfinityChart_symm_smooth :
    ContMDiffOn 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (realInfinityChart a ε).symm
      (realInfinityChart a ε).target := by
  intro x hx
  rw [realInfinityChart_target] at hx
  have hi : ContDiffAt ℂ ∞ (fun z : ℂ => z⁻¹) x.val.1 := contDiffAt_id.inv hx.1
  have hp := (ContinuousLinearMap.fst ℝ ℂ (Fin m → ℂ)).contDiff.contMDiff.comp
    (real_inclusion_contMDiff a)
  exact (Complex.equivRealProdCLM.contDiff.contMDiff.contMDiffAt.comp x
    (((hi.restrict_scalars ℝ).contMDiffAt).comp x hp.contMDiffAt)).contMDiffWithinAt

def infinityDiffeomorph : PartialDiffeomorph 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel)
    RealModel (locus a) ∞ where
  __ := realInfinityChart a ε
  contMDiffOn_toFun := realInfinityChart_smooth a ε
  contMDiffOn_invFun := realInfinityChart_symm_smooth a ε

@[simp] theorem infinityDiffeomorph_source :
    (infinityDiffeomorph a ε).source=Complex.equivRealProdCLM.symm ⁻¹' infinityDomain a :=
  realInfinityChart_source a ε

@[simp] theorem infinityDiffeomorph_target :
    (infinityDiffeomorph a ε).target=infinityBranch a ε := realInfinityChart_target a ε

end
section

variable {m : ℕ} {a : Fin m → ℂ}
namespace NormalChart
variable (e : NormalChart a) (x : locus a)

def inclusionChart (z : ℂ) : Affine m := (e.sliceChart x).symm z

end NormalChart

end
section

variable {m : ℕ}

def projectionDomain (a : Fin m → ℂ) (R : ℝ) : Set (locus a) :=
  {x | ‖x.val.1‖≤R}

theorem fibre_norm_bound {a : Fin m → ℂ} {x : Affine m} (hx : x∈locus a)
    {R : ℝ} (hR : 0≤R) (ht : ‖x.1‖≤R) (j : Fin m) :
    ‖x.2 j‖≤R^2+‖a j‖+1 := by
  have he := congrArg norm (mem_locus.mp hx j)
  rw [norm_pow] at he
  have hle := norm_sub_le (x.1^2) (a j)
  rw [norm_pow,←he] at hle
  have ht2 : ‖x.1‖^2≤R^2 := sq_le_sq₀ (norm_nonneg _) hR |>.mpr ht
  have hA : 0≤R^2+‖a j‖ := add_nonneg (sq_nonneg R) (norm_nonneg _)
  nlinarith [sq_nonneg (‖x.2 j‖-1),norm_nonneg (x.2 j)]

theorem projectionDomain_compact (a : Fin m → ℂ) (R : ℝ) :
    IsCompact (projectionDomain a R) := by
  by_cases hR : 0≤R
  · let A : ℝ := R^2+∑ j,‖a j‖+1
    let S : Set (Affine m) := locus a ∩ {x | ‖x.1‖≤R}
    have hc : IsClosed S := (locus_isClosed a).inter (isClosed_le continuous_fst.norm continuous_const)
    have hb : Bornology.IsBounded S := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨max R A,?_⟩
      intro x hx
      rw [Prod.norm_def]
      apply max_le
      · exact hx.2.trans (le_max_left _ _)
      · apply (pi_norm_le_iff_of_nonneg (le_trans (by positivity : 0≤R) (le_max_left R A))).mpr
        intro j
        have ha : ‖a j‖≤∑ k,‖a k‖ := Finset.single_le_sum (fun k _ => norm_nonneg (a k)) (Finset.mem_univ j)
        exact (fibre_norm_bound hx.1 hR hx.2 j).trans
          ((by dsimp [A]; linarith : R^2+‖a j‖+1≤A).trans (le_max_right _ _))
    have hcomp : IsCompact S := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hc,hb⟩
    have hpre := (locus_isClosed a).isClosedEmbedding_subtypeVal.isCompact_preimage hcomp
    convert hpre using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    change (‖x.val.1‖≤R) ↔ (x.val∈locus a ∧ ‖x.val.1‖≤R)
    exact ⟨fun hx => ⟨x.property,hx⟩,fun hx => hx.2⟩
  · have he : projectionDomain a R=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hR ((norm_nonneg x.val.1).trans hx)
    rw [he]
    exact isCompact_empty

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem curveSigmaCompact : SigmaCompactSpace (locus a) :=
  IsClosed.sigmaCompactSpace (locus_isClosed a)

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricAnnulusDomain
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit

 def inclusion (x : BaseCurve) : PlaneBase := projection x.val

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_CubicFubiniStudy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 def planeAffine : PlaneBase →L[ℂ] Affine 1 :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.snd ℂ ℂ ℂ)

 def cubicChart (b : BaseCurve) : ℂ → Affine 1 :=
  planeAffine ∘ projection ∘ (normalChartAt (parameters 0) b).inclusionChart b

def weightedProjection (D m : ℕ) (z : PlaneBase) : Affine 3 :=
  (z.1^(D-m),![z.2^(D-m),z.1^(D-m)*z.2^m,z.1^m*z.2^(D-m)])

 def weightedInclusion (D m : ℕ) (x : BaseCurve) : Affine 3 :=
  weightedProjection D m (inclusion x)

 def weightedPhaseInclusion (D m : ℕ) (x : BaseCurve) : PlanePhase (Option (Fin 3)) :=
  affinePhase 3 (weightedInclusion D m x)

 def weightedFSPrimitive (D m : ℕ) (c : ℝ) : ManifoldOneForm RealModel BaseCurve :=
  manifoldPullbackOneForm (fun _ => affineFSPrimitive c) (weightedPhaseInclusion D m) 0

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_CubicEndCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

def affineComplex (m : ℕ) : Affine m →L[ℂ] (Option (Fin m) → ℂ) :=
  ContinuousLinearMap.pi fun j => match j with
    | none => ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)
    | some j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ))

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 def coefficientNorm (D m : ℕ) (x : BaseCurve) : ℝ :=
  1+phaseSq (weightedPhaseInclusion D m x)

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicCoefficientDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι]

def radialProbability (k : ι → ℕ × ℕ) (D m : ι → ℕ) (p : Radial.Plane)
    (x : BaseCurve) (i : ι) : ℝ :=
  Radial.selected k (fun j => coefficientNorm (D j) (m j) x) p i

def radialPrimitive (k : ι → ℕ × ℕ) (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane) :
    ManifoldOneForm RealModel BaseCurve :=
  fun x => ∑ i,radialProbability k D m p x i • weightedFSPrimitive (D i) (m i) c x

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricEndResidueMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open Hamiltonian

variable {m : ℕ} {a : Fin m → ℂ} [Fact (Injective a)] [Fact (∀ j,a j≠0)]

namespace NormalChart
variable (e : NormalChart a) (x : locus a)

def realSliceChart : OpenPartialHomeomorph (locus a) RealModel :=
  (e.sliceChart x).trans Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
@[simp] theorem realSliceChart_source : (e.realSliceChart x).source=(e.sliceChart x).source := by
  simp [realSliceChart]

end NormalChart

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_CubicRadialEndSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open MeasureTheory

local instance cubicRadialEndSmoothSigmaCompact : SigmaCompactSpace BaseCurve :=
  curveSigmaCompact (parameters 0)

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricSmoothExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold

variable {m : ℕ} {a : Fin m → ℂ}

 def signFlip (j : Fin m) (x : locus a) : locus a :=
  ⟨(x.val.1,fun i => if i=j then -x.val.2 i else x.val.2 i), by
    apply mem_locus.mpr
    intro i
    dsimp only
    split_ifs <;> simpa only [neg_sq] using mem_locus.mp x.property i⟩

@[simp] theorem signFlip_projection (j : Fin m) (x : locus a) : (signFlip j x).val.1=x.val.1 := rfl

 def fiberMix (x y : locus a) (hxy : x.val.1=y.val.1) (F : Finset (Fin m)) : locus a :=
  ⟨(x.val.1,fun j => if j∈F then y.val.2 j else x.val.2 j),by
    apply mem_locus.mpr
    intro j
    dsimp only
    split_ifs
    · rw [hxy]; exact mem_locus.mp y.property j
    · exact mem_locus.mp x.property j⟩

@[simp] theorem fiberMix_empty (x y : locus a) (hxy : x.val.1=y.val.1) :
    fiberMix x y hxy ∅=x := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  funext j
  simp [fiberMix]

@[simp] theorem fiberMix_univ (x y : locus a) (hxy : x.val.1=y.val.1) :
    fiberMix x y hxy Finset.univ=y := by
  apply Subtype.ext
  refine Prod.ext hxy ?_
  funext j
  simp [fiberMix]

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CubicAreaExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian
open scoped BigOperators
open FiniteMoment

local instance radialCubicCompactAreaSigmaCompact : SigmaCompactSpace BaseCurve :=
  curveSigmaCompact (parameters 0)

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_SurfacePathPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter

variable (m : ℕ)

def realAnnulusChart : OpenPartialHomeomorph RealModel (Surface m) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph.trans (annulusChart m).symm

@[simp] theorem realAnnulusChart_source :
    (realAnnulusChart m).source=Complex.equivRealProdCLM.symm ⁻¹' annulusDomain m := by
  simp [realAnnulusChart]

@[simp] theorem realAnnulusChart_target : (realAnnulusChart m).target=annulusBranch m := by
  simp [realAnnulusChart]

@[simp] theorem realAnnulusChart_apply (x : RealModel) :
    realAnnulusChart m x=annulusInverse m (Complex.equivRealProdCLM.symm x) := rfl

@[simp] theorem realAnnulusChart_symm_apply (x : Surface m) :
    (realAnnulusChart m).symm x=Complex.equivRealProdCLM (annulusCoordinate m x.val) := rfl

theorem realAnnulusChart_smooth :
    ContMDiffOn 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (realAnnulusChart m) (realAnnulusChart m).source := by
  intro x hx
  rw [realAnnulusChart_source] at hx
  apply real_contMDiffWithinAt_of_ambient
  have hc := ((annulusPoint_contDiffAt m hx).restrict_scalars ℝ).comp x
    Complex.equivRealProdCLM.symm.contDiff.contDiffAt
  apply hc.contDiffWithinAt.congr
  · intro y hy
    have hyD : Complex.equivRealProdCLM.symm y∈annulusDomain m := by
      simpa only [realAnnulusChart_source,mem_preimage] using hy
    rw [realAnnulusChart_apply,annulusInverse_val m hyD.1]
    rfl
  · rw [realAnnulusChart_apply,annulusInverse_val m hx.1]
    rfl

theorem realAnnulusChart_symm_smooth :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (realAnnulusChart m).symm := by
  have hc := (Complex.equivRealProdCLM.contDiff.contMDiff).comp
    (((annulusCoordinate m).restrictScalars ℝ).contDiff.contMDiff.comp
      (real_inclusion_contMDiff (parameters m)))
  exact hc

def annulusDiffeomorph : PartialDiffeomorph 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel)
    RealModel (Surface m) ∞ where
  __ := realAnnulusChart m
  contMDiffOn_toFun := realAnnulusChart_smooth m
  contMDiffOn_invFun := (realAnnulusChart_symm_smooth m).contMDiffOn

@[simp] theorem annulusDiffeomorph_source :
    (annulusDiffeomorph m).source=Complex.equivRealProdCLM.symm ⁻¹' annulusDomain m :=
  realAnnulusChart_source m

@[simp] theorem annulusDiffeomorph_target :
    (annulusDiffeomorph m).target=annulusBranch m := realAnnulusChart_target m

def transverseAnnulusPoint (z : ℂ) : Affine (m+2) :=
  (plus z,fun j => if j=0 then minus z
    else Complex.I*Complex.sqrt (parameters m j-plus z^2))

@[simp] theorem transverseAnnulusPoint_zero (z : ℂ) :
    (transverseAnnulusPoint m z).2 0=minus z := by simp [transverseAnnulusPoint]

theorem transverseAnnulusPoint_mem {z : ℂ} (hz : z≠0) :
    transverseAnnulusPoint m z∈locus (parameters m) := by
  rw [mem_locus]
  intro j
  by_cases hj : j=0
  · subst j
    simp only [transverseAnnulusPoint,ite_true, if_true,parameters_zero]
    linear_combination -(plus_sq_sub_minus_sq hz)
  · simp only [transverseAnnulusPoint,ite_eq_right hj,mul_pow,Complex.I_sq,sqrt_sq_complex]
    ring

def transverseAnnulusDomain : Set ℂ := {z | z≠0 ∧
  ∀ j : Fin (m+2),j≠0 → 0<(parameters m j-plus z^2).re}

theorem transverseAnnulusDomain_isOpen : IsOpen (transverseAnnulusDomain m) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hc := ((plus_contDiffAt hz.1).pow 2).continuousAt
  have h0 : ∀ᶠ w in 𝓝 z,w≠0 := isOpen_compl_singleton.mem_nhds hz.1
  have hj : ∀ j : Fin (m+2),∀ᶠ w in 𝓝 z,j≠0 → 0<(parameters m j-plus w^2).re := by
    intro j
    by_cases h : j=0
    · exact Filter.Eventually.of_forall (fun _ hn => (hn h).elim)
    · exact ((Complex.continuous_re.continuousAt.comp (continuousAt_const.sub hc)).eventually
        (Ioi_mem_nhds (hz.2 j h))).mono (fun _ hw _ => hw)
  filter_upwards [h0,Filter.eventually_all.mpr hj] with w hw0 hwj
  exact ⟨hw0,hwj⟩

theorem transverseAnnulusPoint_contDiffAt {z : ℂ} (hz : z∈transverseAnnulusDomain m) :
    ContDiffAt ℂ ∞ (transverseAnnulusPoint m) z := by
  apply ContDiffAt.prodMk (plus_contDiffAt hz.1)
  apply contDiffAt_pi.mpr
  intro j
  by_cases hj : j=0
  · subst j
    simpa only [ite_true, if_true] using minus_contDiffAt hz.1
  · have hb : ContDiffAt ℂ ∞ (fun w : ℂ => parameters m j-plus w^2) z :=
      contDiffAt_const.sub ((plus_contDiffAt hz.1).pow 2)
    have hr := (sqrt_contDiffAt (hz.2 j hj)).comp z hb
    simpa only [transverseAnnulusPoint,ite_eq_right hj] using
      (contDiffAt_const.mul hr : ContDiffAt ℂ ∞ (fun w => Complex.I*Complex.sqrt (parameters m j-plus w^2)) z)

def transverseCoordinate : Affine (m+2) →L[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ (Fin (m+2) → ℂ))+
  ((ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ ℂ (Fin (m+2) → ℂ)))

@[simp] theorem transverseCoordinate_apply (x : Affine (m+2)) :
    transverseCoordinate m x=x.1+x.2 0 := rfl

@[simp] theorem transverseCoordinate_point (z : ℂ) :
    transverseCoordinate m (transverseAnnulusPoint m z)=z := by
  simp [transverseCoordinate_apply,transverseAnnulusPoint]

theorem transverseCoordinate_mul {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    transverseCoordinate m x*(x.1-x.2 0)=1 := by
  have h0 := mem_locus.mp hx 0
  simp only [parameters_zero] at h0
  change (x.1+x.2 0)*(x.1-x.2 0)=1
  linear_combination -h0

theorem transverseCoordinate_ne_zero {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    transverseCoordinate m x≠0 := by
  intro h
  have he := transverseCoordinate_mul m hx
  rw [h,zero_mul] at he
  exact zero_ne_one he

theorem inverse_transverseCoordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    (transverseCoordinate m x)⁻¹=x.1-x.2 0 := by
  apply mul_left_cancel₀ (transverseCoordinate_ne_zero m hx)
  rw [mul_inv_cancel₀ (transverseCoordinate_ne_zero m hx),transverseCoordinate_mul m hx]

theorem plus_transverseCoordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    plus (transverseCoordinate m x)=x.1 := by
  rw [plus,inverse_transverseCoordinate m hx,transverseCoordinate_apply]
  ring

theorem minus_transverseCoordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    minus (transverseCoordinate m x)=x.2 0 := by
  rw [minus,inverse_transverseCoordinate m hx,transverseCoordinate_apply]
  ring

def transverseBranch : Set (Surface m) := {x | transverseCoordinate m x.val∈transverseAnnulusDomain m ∧
  ∀ j : Fin (m+2),j≠0 → 0<(x.val.2 j).im}

theorem transverseAnnulusPoint_positive {z : ℂ} (hz : z∈transverseAnnulusDomain m) :
    ∀ j : Fin (m+2),j≠0 → 0<((transverseAnnulusPoint m z).2 j).im := by
  intro j hj
  simpa only [transverseAnnulusPoint,ite_eq_right hj,Complex.mul_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add] using sqrt_re_pos (hz.2 j hj)

theorem transverseAnnulusPoint_coordinate {x : Surface m} (hx : x∈transverseBranch m) :
    transverseAnnulusPoint m (transverseCoordinate m x.val)=x.val := by
  apply Prod.ext (plus_transverseCoordinate m x.property)
  funext j
  by_cases hj : j=0
  · subst j
    exact (transverseAnnulusPoint_zero m _).trans (minus_transverseCoordinate m x.property)
  · have hp : 0<(-Complex.I*x.val.2 j).re := by
      simpa only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,
        Complex.I_im,neg_zero,zero_mul,neg_mul,one_mul,zero_sub,neg_neg] using hx.2 j hj
    have he : parameters m j-plus (transverseCoordinate m x.val)^2=(-Complex.I*x.val.2 j)^2 := by
      rw [plus_transverseCoordinate m x.property,mul_pow,neg_pow,Complex.I_sq]
      have hjx := mem_locus.mp x.property j
      linear_combination hjx
    simp only [transverseAnnulusPoint,ite_eq_right hj,he,sqrt_of_sq_pos hp]
    rw [← mul_assoc]
    simp

def transverseAnnulusInverse (z : ℂ) : Surface m := by
  classical
  exact if h : z≠0 then ⟨transverseAnnulusPoint m z,transverseAnnulusPoint_mem m h⟩ else annulusBasepoint m

@[simp] theorem transverseAnnulusInverse_val {z : ℂ} (hz : z≠0) :
    (transverseAnnulusInverse m z).val=transverseAnnulusPoint m z := by
  simp only [transverseAnnulusInverse,dite_eq_left hz]

theorem transverseBranch_isOpen : IsOpen (transverseBranch m) := by
  have hc : Continuous (fun x : Surface m => transverseCoordinate m x.val) :=
    (transverseCoordinate m).continuous.comp continuous_subtype_val
  have hw : ∀ j : Fin (m+2),Continuous (fun x : Surface m => (x.val.2 j).im) :=
    fun j => Complex.continuous_im.comp
      ((continuous_apply j).comp (continuous_snd.comp continuous_subtype_val))
  change IsOpen ((fun x : Surface m => transverseCoordinate m x.val) ⁻¹' transverseAnnulusDomain m ∩
    {x : Surface m | ∀ j,j≠0 → 0<(x.val.2 j).im})
  refine ((transverseAnnulusDomain_isOpen m).preimage hc).inter ?_
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (hw j)

def transverseAnnulusChart : OpenPartialHomeomorph (Surface m) ℂ where
  toFun x := transverseCoordinate m x.val
  invFun := transverseAnnulusInverse m
  source := transverseBranch m
  target := transverseAnnulusDomain m
  map_source' _ hx := hx.1
  map_target' z hz := by
    refine ⟨?_,?_⟩
    · rw [transverseAnnulusInverse_val m hz.1,transverseCoordinate_point]
      exact hz
    · rw [transverseAnnulusInverse_val m hz.1]
      exact transverseAnnulusPoint_positive m hz
  left_inv' x hx := by
    apply Subtype.ext
    rw [transverseAnnulusInverse_val m hx.1.1]
    exact transverseAnnulusPoint_coordinate m hx
  right_inv' z hz := by
    rw [transverseAnnulusInverse_val m hz.1,transverseCoordinate_point]
  open_source := transverseBranch_isOpen m
  open_target := transverseAnnulusDomain_isOpen m
  continuousOn_toFun := ((transverseCoordinate m).continuous.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_induced_rng.mpr
    have hc : ContinuousOn (transverseAnnulusPoint m) (transverseAnnulusDomain m) :=
      fun z hz => (transverseAnnulusPoint_contDiffAt m hz).continuousAt.continuousWithinAt
    rw [continuousOn_iff_continuous_domRestrict] at hc
    exact hc.congr fun z => (transverseAnnulusInverse_val m z.property.1).symm

def realTransverseChart : OpenPartialHomeomorph RealModel (Surface m) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph.trans (transverseAnnulusChart m).symm

@[simp] theorem realTransverseChart_source :
    (realTransverseChart m).source=Complex.equivRealProdCLM.symm ⁻¹' transverseAnnulusDomain m := by
  simp [realTransverseChart,transverseAnnulusChart]

@[simp] theorem realTransverseChart_target : (realTransverseChart m).target=transverseBranch m := by
  simp [realTransverseChart,transverseAnnulusChart]

@[simp] theorem realTransverseChart_apply (x : RealModel) :
    realTransverseChart m x=transverseAnnulusInverse m (Complex.equivRealProdCLM.symm x) := rfl

@[simp] theorem realTransverseChart_symm_apply (x : Surface m) :
    (realTransverseChart m).symm x=Complex.equivRealProdCLM (transverseCoordinate m x.val) := rfl

theorem realTransverseChart_smooth :
    ContMDiffOn 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (realTransverseChart m) (realTransverseChart m).source := by
  intro x hx
  rw [realTransverseChart_source] at hx
  apply real_contMDiffWithinAt_of_ambient
  have hc := ((transverseAnnulusPoint_contDiffAt m hx).restrict_scalars ℝ).comp x
    Complex.equivRealProdCLM.symm.contDiff.contDiffAt
  apply hc.contDiffWithinAt.congr
  · intro y hy
    have hyD : Complex.equivRealProdCLM.symm y∈transverseAnnulusDomain m := by
      simpa only [realTransverseChart_source,mem_preimage] using hy
    rw [realTransverseChart_apply,transverseAnnulusInverse_val m hyD.1]
    rfl
  · rw [realTransverseChart_apply,transverseAnnulusInverse_val m hx.1]
    rfl

theorem realTransverseChart_symm_smooth :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (realTransverseChart m).symm := by
  exact (Complex.equivRealProdCLM.contDiff.contMDiff).comp
    (((transverseCoordinate m).restrictScalars ℝ).contDiff.contMDiff.comp
      (real_inclusion_contMDiff (parameters m)))

def transverseDiffeomorph : PartialDiffeomorph 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel)
    RealModel (Surface m) ∞ where
  __ := realTransverseChart m
  contMDiffOn_toFun := realTransverseChart_smooth m
  contMDiffOn_invFun := (realTransverseChart_symm_smooth m).contMDiffOn

@[simp] theorem transverseDiffeomorph_source :
    (transverseDiffeomorph m).source=Complex.equivRealProdCLM.symm ⁻¹' transverseAnnulusDomain m :=
  realTransverseChart_source m

@[simp] theorem transverseDiffeomorph_target :
    (transverseDiffeomorph m).target=transverseBranch m := realTransverseChart_target m

end PackingSufficiencySupport.DiagonalQuadrics.Explicit
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_QuadricCylinderChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable (m : ℕ)

def transverseCylinder : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel)
    HandleCylinder (Surface m) ∞ :=
  (cylinderComplexDiffeomorph.trans
    Complex.equivRealProdCLM.toDiffeomorph.toPartialDiffeomorph).trans (transverseDiffeomorph m)

@[simp] theorem transverseCylinder_apply (q : HandleCylinder) :
    transverseCylinder m q=transverseAnnulusInverse m (cylinderComplexMap q) := rfl

@[simp] theorem transverseCylinder_symm_apply (x : Surface m) :
    (transverseCylinder m).symm x=cylinderComplexInverse (transverseCoordinate m x.val) := by
  change cylinderComplexInverse (Complex.equivRealProdCLM.symm
    (Complex.equivRealProdCLM (transverseCoordinate m x.val)))=_
  rw [ContinuousLinearEquiv.symm_apply_apply]

@[simp] theorem transverseCylinder_source : (transverseCylinder m).source=
    cylinderComplexMap ⁻¹' transverseAnnulusDomain m := by
  ext q
  simp [transverseCylinder,PartialDiffeomorph.trans,cylinderComplexDiffeomorph,
    Diffeomorph.toPartialDiffeomorph,transverseDiffeomorph_source]
  change Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (cylinderComplexMap q))∈transverseAnnulusDomain m ↔ _
  rw [ContinuousLinearEquiv.symm_apply_apply]

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularChartNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

structure AnnularHandleData (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] where
  width : ℝ
  width_pos : 0<width
  chart : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) HandleCylinder M ∞
  source_eq : chart.source=Ioo (-width) width ×ˢ univ
  compact_target : IsCompact (closure chart.target)
  clock : Circle → ℝ
  clock_smooth : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ clock
  clock_nonneg : ∀ z,0 ≤ clock z
  clock_support : tsupport clock⊆({1}ᶜ : Set Circle)
  clock_integral : (∫ t in (0:ℝ)..1,clock (circleTurn t))=1
  dual : ManifoldOneForm E M
  dual_smooth : SmoothOneFormFamily (fun _ : ℝ => dual)
  dual_compact : HasCompactSupport dual
  dual_closed : ∀ x,manifoldExteriorOneForm dual x=0
  dual_pullback : ∀ z∈chart.source,∀ v : CylinderModel,
    dual (chart z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) chart z v)=
      clock z.2*circleAngular z.2 v.2

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

def cylinderRadialForm (b : ℝ) : ManifoldOneForm CylinderModel HandleCylinder :=
  manifoldScalarDifferential (fun z : HandleCylinder => intervalClock (-b) b z.1)

theorem cylinder_fst_smooth :
    ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ (Prod.fst : HandleCylinder → ℝ) := by
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod]
  exact contMDiff_fst

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularHandleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

def radial (H : AnnularHandleData E M) (b : ℝ) : ManifoldOneForm E M :=
  handlePushforwardOneForm H.chart (cylinderRadialForm b)

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

def cylinderRectangleInverse (z : HandleCylinder) : Plane :=
  (z.1,positiveCircleArgument z.2)

theorem cylinderRectangleInverse_smooth {z : HandleCylinder}
    (hz : z.2∈positiveCircleCoordinate.target) :
    ContMDiffAt 𝓘(ℝ,CylinderModel) 𝓘(ℝ,Plane) ∞ cylinderRectangleInverse z := by
  have hg := positiveCircleCoordinate.contMDiffOn_invFun.contMDiffAt
    (positiveCircleCoordinate.open_target.mem_nhds hz)
  exact (contMDiffAt_prod_module_iff _).2
    ⟨cylinder_fst_smooth.contMDiffAt,hg.comp z cylinder_snd_smooth.contMDiffAt⟩

def cylinderRectangle :
    PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) Plane HandleCylinder ∞ where
  toFun := cylinderCover
  invFun := cylinderRectangleInverse
  source := univ ×ˢ Ioo (0:ℝ) 1
  target := univ ×ˢ positiveCircleCoordinate.target
  map_source' _z hz := ⟨mem_univ _,positiveCircleCoordinate.map_source hz.2⟩
  map_target' _z hz := ⟨mem_univ _,positiveCircleCoordinate.map_target hz.2⟩
  left_inv' _z hz := Prod.ext rfl (positiveCircleCoordinate.left_inv hz.2)
  right_inv' _z hz := Prod.ext rfl (positiveCircleCoordinate.right_inv hz.2)
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := isOpen_univ.prod positiveCircleCoordinate.open_target
  contMDiffOn_toFun := cylinderCover_smooth.contMDiffOn
  contMDiffOn_invFun := fun _ hz => (cylinderRectangleInverse_smooth hz.2).contMDiffWithinAt

namespace AnnularHandleData
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def densityChart (H : AnnularHandleData Plane M) :
    PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞ :=
  cylinderRectangle.trans H.chart

@[simp] theorem densityChart_apply (H : AnnularHandleData Plane M) (y : Plane) :
    H.densityChart y=H.chart (cylinderCover y) := rfl

end AnnularHandleData

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_SurfaceSuspensionCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

def handleFirstCorrection
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (p : ℝ × V) : ManifoldOneForm E M := fun x =>
  surfaceSuspensionCoefficient Φ (intervalClock (-b) b)
      (p,(D.chart.symm x).1) • D.radial b x +
  surfaceFirstCorrectionCoefficient Φ (intervalClock (-b) b) H
      (p,(D.chart.symm x).1) • D.dual x

def globalSurfaceFirstPrimitive
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (p : ℝ × V) : ManifoldOneForm E M :=
  Γ p.2 + extendManifoldOneForm D.chart.target
    (handleFirstCorrection D b Φ H p)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem globalSurfaceFirstPrimitive_zero
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (v : V) :
    globalSurfaceFirstPrimitive D b Φ H Γ (0,v)=Γ v := by
  funext x
  by_cases hx : x∈D.chart.target
  · simp [globalSurfaceFirstPrimitive,extendManifoldOneForm_inside hx,handleFirstCorrection]
  · simp [globalSurfaceFirstPrimitive,extendManifoldOneForm_outside hx]

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {ι : Type*} [Fintype ι]

def surfaceSecondCorrectionCoefficient (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (p : (ℝ × V) × ℝ) : ℝ :=
  surfaceInterpolatedLayer S K H h (Φ.map 1).symm ρ ρ₀ p.1.1
    (p.2,Φ.map (S p.2) p.1.2) - S p.2*H p.1.2 - p.1.1*(K p.1.2-H p.1.2)

def surfaceSecondExtraCoefficient (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (p : (ℝ × V) × ℝ) : ℝ :=
  surfaceSecondCorrectionCoefficient Φ S K H h ρ ρ₀ p -
    surfaceFirstCorrectionCoefficient Φ S H ((1,p.1.2),p.2)

@[simp] theorem surfaceSecondExtraCoefficient_zero (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (v : V) (s : ℝ) : surfaceSecondExtraCoefficient Φ S K H h ρ ρ₀ ((0,v),s)=0 := by
  simp only [surfaceSecondExtraCoefficient,surfaceSecondCorrectionCoefficient,
    surfaceFirstCorrectionCoefficient,surfaceInterpolatedLayer,surfaceFirstLayer,
    sub_zero,zero_mul,one_mul,add_zero]
  ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {ι : Type*} [Fintype ι]

def handleSecondExtra
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (p : ℝ × V) : ManifoldOneForm E M := fun x =>
  surfaceSecondExtraCoefficient Φ (intervalClock (-b) b) K H h ρ ρ₀
    (p,(D.chart.symm x).1) • D.dual x

def globalSurfaceSecondPrimitive
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (p : ℝ × V) : ManifoldOneForm E M :=
  globalSurfaceFirstPrimitive D b Φ H Γ (1,p.2) +
    (p.1*(K p.2-H p.2)) • D.dual +
    extendManifoldOneForm D.chart.target
      (handleSecondExtra D b Φ K H h ρ ρ₀ p)

@[simp] theorem globalSurfaceSecondPrimitive_zero
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (v : V) :
    globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (0,v)=
      globalSurfaceFirstPrimitive D b Φ H Γ (1,v) := by
  funext x
  by_cases hx : x∈D.chart.target
  · simp [globalSurfaceSecondPrimitive,extendManifoldOneForm_inside hx,handleSecondExtra]
  · simp [globalSurfaceSecondPrimitive,extendManifoldOneForm_outside hx]

end
section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 def handleAnnularCover
    (D : AnnularHandleData E M)
    : Plane → M := D.chart ∘ cylinderCover

 theorem handleAnnularCover_derivative
    (D : AnnularHandleData E M)
    {q : Plane} (hq : cylinderCover q∈D.chart.source) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q=
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) D.chart (cylinderCover q)).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q) :=
  mfderiv_comp q (D.chart.mdifferentiableAt (by simp) hq)
    (cylinderCover_smooth.mdifferentiableAt (by simp))

end

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularHandleCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 def handleAnnularCover
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) : Plane → M := (handleAnnularChart e a) ∘ cylinderCover

 theorem handleAnnularCover_derivative
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {q : Plane} (hq : cylinderCover q∈(handleAnnularChart e a).source) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q=
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) (handleAnnularChart e a) (cylinderCover q)).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q) :=
  mfderiv_comp q ((handleAnnularChart e a).mdifferentiableAt (by simp) hq)
    (cylinderCover_smooth.mdifferentiableAt (by simp))

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem cylinderCover_derivative_bijective (q : Plane) :
    Bijective (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q) := by
  constructor
  · intro v w h
    change (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q : Plane →L[ℝ] CylinderModel) v =
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q : Plane →L[ℝ] CylinderModel) w at h
    erw [cylinderCover_derivative,cylinderCover_derivative] at h
    have hx := congrArg (fun z : CylinderModel => z.1) h
    refine Prod.ext hx ?_
    have he := congrArg (fun z : CylinderModel => circleAngular (circleTurn q.2) z.2) h
    simpa only [circleAngular_unit_pullback] using he
  · intro v
    exact ⟨(v.1,circleAngular (circleTurn q.2) v.2),cylinderCover_derivative_right_inverse q v⟩

theorem handleAnnularCover_derivative_bijective
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {q : Plane} (hq : cylinderCover q∈(handleAnnularChart e a).source) :
    Bijective (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q) := by
  let c := handleAnnularChart e a
  let A : CylinderModel →L[ℝ] E := mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) c (cylinderCover q)
  let B : E →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) c.symm (c (cylinderCover q))
  have hBA : B.comp A=ContinuousLinearMap.id ℝ CylinderModel := handle_mfderiv_symm_comp c hq
  have hAB : A.comp B=ContinuousLinearMap.id ℝ E := by
    have h := handle_mfderiv_symm_comp c.symm (c.map_source hq)
    change (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) c (c.symm (c (cylinderCover q)))).comp B=
      ContinuousLinearMap.id ℝ E at h
    erw [c.left_inv hq] at h
    exact h
  have hA : Bijective A := by
    constructor
    · intro v w h
      have he := congrArg B h
      have hv := congrArg (fun L : CylinderModel →L[ℝ] CylinderModel => L v) hBA
      have hw := congrArg (fun L : CylinderModel →L[ℝ] CylinderModel => L w) hBA
      exact hv.symm.trans (he.trans hw)
    · intro v
      exact ⟨B v,congrArg (fun L : E →L[ℝ] E => L v) hAB⟩
  rw [handleAnnularCover_derivative e a hq]
  exact hA.comp (cylinderCover_derivative_bijective q)

def handleAnnularCoverLinearEquiv
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {q : Plane} (hq : cylinderCover q∈(handleAnnularChart e a).source) : Plane ≃L[ℝ] E :=
  (LinearEquiv.ofBijective
    (show Plane →L[ℝ] E from mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q).toLinearMap
    (handleAnnularCover_derivative_bijective e a hq)).toContinuousLinearEquiv

@[simp] theorem handleAnnularCoverLinearEquiv_apply
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {q : Plane} (hq : cylinderCover q∈(handleAnnularChart e a).source) (v : Plane) :
    handleAnnularCoverLinearEquiv e a hq v=
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q v := rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem handleAnnularCover_derivative_bijective
    (D : AnnularHandleData E M)
    {q : Plane} (hq : cylinderCover q∈D.chart.source) :
    Bijective (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q) := by
  let c := D.chart
  let A : CylinderModel →L[ℝ] E := mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) c (cylinderCover q)
  let B : E →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) c.symm (c (cylinderCover q))
  have hBA : B.comp A=ContinuousLinearMap.id ℝ CylinderModel := handle_mfderiv_symm_comp c hq
  have hAB : A.comp B=ContinuousLinearMap.id ℝ E := by
    have h := handle_mfderiv_symm_comp c.symm (c.map_source hq)
    change (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) c (c.symm (c (cylinderCover q)))).comp B=
      ContinuousLinearMap.id ℝ E at h
    erw [c.left_inv hq] at h
    exact h
  have hA : Bijective A := by
    constructor
    · intro v w h
      have he := congrArg B h
      have hv := congrArg (fun L : CylinderModel →L[ℝ] CylinderModel => L v) hBA
      have hw := congrArg (fun L : CylinderModel →L[ℝ] CylinderModel => L w) hBA
      exact hv.symm.trans (he.trans hw)
    · intro v
      exact ⟨B v,congrArg (fun L : E →L[ℝ] E => L v) hAB⟩
  rw [D.handleAnnularCover_derivative hq]
  exact hA.comp (cylinderCover_derivative_bijective q)

def handleAnnularCoverLinearEquiv
    (D : AnnularHandleData E M)
    {q : Plane} (hq : cylinderCover q∈D.chart.source) : Plane ≃L[ℝ] E :=
  (LinearEquiv.ofBijective
    (show Plane →L[ℝ] E from mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q).toLinearMap
    (D.handleAnnularCover_derivative_bijective hq)).toContinuousLinearEquiv

@[simp] theorem handleAnnularCoverLinearEquiv_apply
    (D : AnnularHandleData E M)
    {q : Plane} (hq : cylinderCover q∈D.chart.source) (v : Plane) :
    D.handleAnnularCoverLinearEquiv hq v=
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q v := rfl

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularEmbeddedChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

@[simp] theorem handleAnnularCover_eq_densityChart
    (D : AnnularHandleData Plane M)
     : D.handleAnnularCover = D.densityChart := rfl

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def handleDensityChart
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a : ℝ) : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞ :=
  restrictHandleDiffeomorph (torusRectangle.trans e) (Ioo (-a) a ×ˢ Ioo (0:ℝ) 1)
    (isOpen_Ioo.prod isOpen_Ioo)

@[simp] theorem handleDensityChart_apply
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a : ℝ) (y : Plane) : handleDensityChart e a y=e (torusTurns y) := rfl

end

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

@[simp] theorem handleAnnularCover_eq_densityChart
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a : ℝ) : handleAnnularCover e a = handleDensityChart e a := rfl

variable {Ω : V →L[ℝ] V →L[ℝ] ℝ}

def annularUnshearMap
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) : Plane × V → M × V :=
  flatProductMap (handleAnnularCover e a) ∘
    (hamiltonianBaseShear Φ (intervalClock (-b) b) (intervalClock_smooth (-b) b)).symm

@[simp] theorem annularUnshearMap_apply
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (p : Plane × V) :
    annularUnshearMap e a b Φ p =
      (handleAnnularCover e a p.1,(Φ.map (intervalClock (-b) b p.1.1)).symm p.2) := rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

def annularUnshearMap
    (D : AnnularHandleData Plane M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) : Plane × V → M × V :=
  flatProductMap (D.handleAnnularCover) ∘
    (hamiltonianBaseShear Φ (intervalClock (-b) b) (intervalClock_smooth (-b) b)).symm

@[simp] theorem annularUnshearMap_apply
    (D : AnnularHandleData Plane M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (p : Plane × V) :
    annularUnshearMap D b Φ p =
      (D.handleAnnularCover p.1,(Φ.map (intervalClock (-b) b p.1.1)).symm p.2) := rfl

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_StationaryManifoldPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped Topology
open scoped Manifold
open Manifold

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def toricHorizontalCoefficient (F : Plane × (ι → ℝ) → ℝ)
    (x : Plane × PlanePhase ι) : ℝ := F (x.1,planeMoments x.2)

omit [DecidableEq ι] in
@[fun_prop] theorem toricHorizontalCoefficient_smooth {F : Plane × (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (toricHorizontalCoefficient F) :=
  hF.comp (contDiff_fst.prodMk (planeMoments_smooth.comp contDiff_snd))

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_AnnularDensityMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

def toricPrimitiveInterpolation (Γ₀ Γ₁ : P → ManifoldOneForm E M)
    (q : ℝ × P) : ManifoldOneForm E M := (1-q.1) • Γ₀ q.2+q.1 • Γ₁ q.2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M] [ChartedSpace E M] in
@[simp] theorem toricPrimitiveInterpolation_zero (Γ₀ Γ₁ : P → ManifoldOneForm E M) (p : P) :
    toricPrimitiveInterpolation Γ₀ Γ₁ (0,p)=Γ₀ p := by simp [toricPrimitiveInterpolation]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M] [ChartedSpace E M] in
@[simp] theorem toricPrimitiveInterpolation_one (Γ₀ Γ₁ : P → ManifoldOneForm E M) (p : P) :
    toricPrimitiveInterpolation Γ₀ Γ₁ (1,p)=Γ₁ p := by simp [toricPrimitiveInterpolation]

end

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

structure PlanarHamiltonianMotion (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P] where
  hamiltonian : (P × ℝ) × Plane → ℝ
  smooth : ContDiff ℝ ∞ hamiltonian
  compact : HasCompactSupport hamiltonian
  trace : P → ℝ → Plane → Plane
  continuous : Continuous (fun p : (P × ℝ) × Plane => trace p.1.1 p.1.2 p.2)
  zero : ∀ y x, trace y 0 x = x
  flow : ∀ y t x, HasDerivAt (fun s => trace y s x)
    (planarHamiltonianField (fderiv ℝ (fun z => hamiltonian ((y,t),z)) (trace y t x))) t

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_ScaledPlanarMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

@[simp] theorem planarHamiltonianField_smul (c : ℝ) (α : Plane →L[ℝ] ℝ) :
    planarHamiltonianField (c • α) = c • planarHamiltonianField α := by
  ext <;> simp [planarHamiltonianField]

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_CartesianMomentSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators
open Set Function
open Hamiltonian Comparison

variable {m N : ℕ}

@[simp] theorem assemble_outerMoments (j : Fin m) (z : PlanePhase (Fin m)) :
    assemble j (baseProjection j (outerMoments j z)) (radialArea (z j)) = planeMoments z := by
  funext i
  by_cases hi : i=j
  · subst i; simp [planeMoments]
  · simp [assemble,hi,baseProjection,planeMoments]

@[simp] theorem baseProjection_outerMoments (j : Fin m) (z : PlanePhase (Fin m)) :
    baseProjection j (outerMoments j z) = baseProjection j (planeMoments z) := by
  funext i
  simp [baseProjection,planeMoments,i.property]

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open Comparison
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def liftArgument (j : ι) (p : ℝ × PlanePhase ι) : ((ι → ℝ) × ℝ) × Plane :=
  ((outerMoments j p.2,p.1),p.2 j)

def liftedHamiltonian (j : ι) (B : ((ι → ℝ) × ℝ) × Plane → ℝ) : ℝ × PlanePhase ι → ℝ :=
  B ∘ liftArgument j

@[fun_prop] theorem liftArgument_smooth (j : ι) : ContDiff ℝ ∞ (liftArgument j) := by
  unfold liftArgument
  exact ((outerMoments_smooth j |>.comp contDiff_snd).prodMk contDiff_fst).prodMk
    ((contDiff_apply ℝ Plane j).comp contDiff_snd)

@[fun_prop] theorem liftedHamiltonian_smooth (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (liftedHamiltonian j B) :=
  hB.comp (liftArgument_smooth j)

def liftedAngularSpeed (j i : ι) (B : ((ι → ℝ) × ℝ) × Plane → ℝ)
    (p : ℝ × PlanePhase ι) : ℝ :=
  2*Real.pi*fderiv ℝ B (liftArgument j p) ((Pi.single i 1,0),0)

@[fun_prop] theorem liftedAngularSpeed_smooth (j i : ι)
    {B : ((ι → ℝ) × ℝ) × Plane → ℝ} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (liftedAngularSpeed j i B) := by
  exact contDiff_const.mul (((hB.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp (liftArgument_smooth j)).clm_apply
    contDiff_const)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_LiftedCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open Comparison
open scoped BigOperators
open MeasureTheory
section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def trajectoryAngularSpeed (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (y : ι → ℝ) (x : Plane) (i : ι) (t : ℝ) : ℝ :=
  2*Real.pi*fderiv ℝ Ψ.hamiltonian ((y,t),Ψ.trace y t x) ((Pi.single i 1,0),0)

@[fun_prop] theorem trajectoryAngularSpeed_continuous
    (Ψ : PlanarHamiltonianMotion (ι → ℝ)) (y : ι → ℝ) (x : Plane) (i : ι) :
    Continuous (trajectoryAngularSpeed Ψ y x i) := by
  have hmap : Continuous (fun t : ℝ => Ψ.trace y t x) :=
    Ψ.continuous.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const)
  have hs : ContDiff ℝ ∞ (fun p => fderiv ℝ Ψ.hamiltonian p) :=
    Ψ.smooth.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact continuous_const.mul ((hs.continuous.comp
    ((continuous_const.prodMk continuous_id).prodMk hmap)).clm_apply continuous_const)

def trajectoryAngle (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (y : ι → ℝ) (x : Plane) (i : ι) (t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..t, trajectoryAngularSpeed Ψ y x i s

def liftedTrajectory (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (z : PlanePhase ι) (t : ℝ) : PlanePhase ι := fun i =>
  if i=j then Ψ.trace (outerMoments j z) t (z j)
  else planeRotate (trajectoryAngle Ψ (outerMoments j z) (z j) i t) (z i)

@[simp] theorem liftedTrajectory_inner (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (z : PlanePhase ι) (t : ℝ) :
    liftedTrajectory Ψ j z t j = Ψ.trace (outerMoments j z) t (z j) := by
  simp [liftedTrajectory]

@[simp] theorem liftedTrajectory_moments (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (z : PlanePhase ι) (t : ℝ) :
    outerMoments j (liftedTrajectory Ψ j z t) = outerMoments j z := by
  funext i
  by_cases hij : i=j
  · subst i; simp
  · simp [outerMoments,liftedTrajectory,hij]

@[simp] theorem liftedTrajectory_zero (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (z : PlanePhase ι) : liftedTrajectory Ψ j z 0 = z := by
  funext i
  by_cases hij : i=j
  · subst i
    simp [Ψ.zero]
  · simp [liftedTrajectory,hij,trajectoryAngle]

end

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def weightedMoment (b : ι → ℝ) (z : PlanePhase ι) : ℝ := ∑ i, b i*radialArea (z i)

omit [DecidableEq ι] in
@[fun_prop] theorem weightedMoment_smooth (b : ι → ℝ) : ContDiff ℝ ∞ (weightedMoment b) := by
  unfold weightedMoment
  fun_prop

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_RationalSlack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

local instance instSigmaCompactSpaceElemAffineHAddNatOfNatBaseCurve : SigmaCompactSpace BaseCurve := curveSigmaCompact (parameters 0)

def physicalParameter (L : ℝ) (p : Moments 2) : Radial.Plane := (L*p 0,L*p 1)

def cubicExhaustion (ℓ : ℕ) : Set BaseCurve :=
  projectionDomain (parameters 0) (exhaustionRadius (parameters 0) ℓ)

theorem cubicExhaustion_compact (ℓ : ℕ) : IsCompact (cubicExhaustion ℓ) :=
  projectionDomain_compact (parameters 0) _

def physicalPrimitive {A B : ℕ} (D S : ℕ) (c L : ℝ) (p : Moments 2) :
    ManifoldOneForm RealModel BaseCurve :=
  radialPrimitive (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c
    (physicalParameter L p)

def physicalArea (D S : ℕ) (c L : ℝ) (p : Moments 2) : ℝ :=
  c*(3*((D:ℝ)-3*(L*p 0+L*p 1))-2*max ((S:ℝ)-(L*p 0+L*p 1)) 0)*Real.pi

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RadialDiskSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def weightedCoefficient (D m : ℕ) (x : BaseCurve) : WeightedHomogeneousIndex → ℂ :=
  complexAffineLift ((complexCartesian (ι := Option (Fin 3))).symm (weightedPhaseInclusion D m x))

 def cubicCoefficients {A B : ℕ} (D S : ℕ) (x : BaseCurve)
    (i : TrapezoidWeight A B) : WeightedHomogeneousIndex → ℂ :=
  weightedCoefficient (cubicDegree D i) (cubicMarkedOrder S i) x

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_CubicToricAmbient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

abbrev CubicConeModel := RealModel × DiskPair
abbrev CubicConeSpace := BaseCurve × DiskPair

 def ambientWeightedCoefficient (D m : ℕ) (z : PlaneBase) : WeightedHomogeneousIndex → ℂ :=
  complexAffineLift ((complexCartesian (ι := Option (Fin 3))).symm
    (affinePhase 3 (weightedProjection D m z)))

 def conePolynomial {A B : ℕ} (D S : ℕ) (p : CubicConeTarget) :
    TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ :=
  toricLift latticeIndex (fun i => ambientWeightedCoefficient (cubicDegree D i) (cubicMarkedOrder S i) p.1) p.2

 def cubicConePrimitive {A B : ℕ} (D S : ℕ) (c : ℝ) : CubicConeTarget → CubicConeTarget →L[ℝ] ℝ :=
  primitivePullback (hopfPrimitive c) (complexCartesian ∘ conePolynomial (A := A) (B := B) D S)

 def cubicAmbientPrimitive {A B : ℕ} (D S : ℕ) (c t : ℝ) : CubicAmbient → CubicAmbient →L[ℝ] ℝ :=
  primitivePullback (cubicConePrimitive (A := A) (B := B) D S c) (cubicNormalCoordinates t)

 def cubicAmbientForm {A B : ℕ} (D S : ℕ) (c t : ℝ) :=
  euclideanExteriorOneForm (cubicAmbientPrimitive (A := A) (B := B) D S c t)

 def centralCubicCoordinates (p : CubicConeSpace) : CubicConeTarget := (inclusion p.1,p.2)

 def centralCubicPrimitive {A B : ℕ} (D S : ℕ) (c : ℝ) : ManifoldOneForm CubicConeModel CubicConeSpace :=
  manifoldPullbackOneForm (fun _ => cubicConePrimitive (A := A) (B := B) D S c) centralCubicCoordinates 0

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_CompactDegenerationTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

abbrev CubicPhysicalModel := RealModel × PlanePhase (Fin 2)
abbrev CubicPhysicalSpace := BaseCurve × PlanePhase (Fin 2)

def cubicPhysicalForm {A B : ℕ} (D S : ℕ) (L : ℝ) : ManifoldTwoForm CubicPhysicalModel CubicPhysicalSpace :=
  globalHorizontalCoupling phaseArea (physicalPrimitive (A := A) (B := B) D S (1/(L*Real.pi)) L ∘ planeMoments)

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_SixLargeCubicPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def outerAmbientPrimitive {A B : ℕ} (L S : ℕ) (c t δ : ℝ) : CubicAmbient → CubicAmbient →L[ℝ] ℝ :=
  primitivePullback (hopfPrimitive c)
    (complexCartesian ∘ outerPolynomial (A := A) (B := B) L S t δ ∘ firstQuadricChart)

 def outerAmbientForm {A B : ℕ} (L S : ℕ) (c t δ : ℝ) :=
  euclideanExteriorOneForm (outerAmbientPrimitive (A := A) (B := B) L S c t δ)

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_SixLargeQuadricPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped BigOperators
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cartesianConjugate (P : (ι → ℂ) → (κ → ℂ)) : PlanePhase ι → PlanePhase κ :=
  fun z => complexCartesian (P (complexCartesian.symm z))

@[simp] theorem cartesianConjugate_cartesian (P : (ι → ℂ) → (κ → ℂ)) (z : ι → ℂ) :
    cartesianConjugate P (complexCartesian z)=complexCartesian (P z) := by
  simp only [cartesianConjugate,ContinuousLinearEquiv.symm_apply_apply]

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_DegreeHopfDeformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def cubicBubblePrimitive {A B : ℕ} (L S m p N : ℕ) (t δ c d ε : ℝ) :
     (Fin 3 → ℂ) → (Fin 3 → ℂ) →L[ℝ] ℝ :=
   (1-(L:ℝ)*d)•primitivePullback (affineFSPrimitive c)
     (fun z => complexCartesian ((ε:ℂ)•z))+
   d•primitivePullback (hopfPrimitive c)
     (fun z => complexCartesian (cubicBubbleResidual (A := A) (B := B) L S m p N t δ ε z))

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldExteriorNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 @[simp] theorem cutoff_phaseSq_zero : phaseSq (0:PlanePhase ι)=0 := by simp [phaseSq]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_CircleAction_CircleRelativeRadialMoser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped BigOperators

variable {ι : Type} [Fintype ι]

 def phaseRotate (s : ℝ) : PlanePhase ι →L[ℝ] PlanePhase ι :=
  Real.cos s • ContinuousLinearMap.id ℝ _+Real.sin s • phaseJ

 omit [Fintype ι] in
 @[simp] theorem phaseRotate_zero (z : PlanePhase ι) : phaseRotate 0 z=z := by
  simp [phaseRotate]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_DegreeRelativeShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold
open scoped ContDiff Manifold Topology BigOperators

section

variable {ι : Type} [Fintype ι]

 def phaseOptionSplit : (PlanePhase ι × Plane) ≃L[ℝ] PlanePhase (Option ι) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p j => match j with | none => p.2 | some i => p.1 i
      invFun := fun z => (fun i => z (some i),z none)
      left_inv := by intro p; rfl
      right_inv := by intro z; funext j; cases j <;> rfl
      map_add' := by intros; funext j; cases j <;> rfl
      map_smul' := by intros; funext j; cases j <;> rfl }

 def phaseInfinityInclusion : PlanePhase ι →L[ℝ] PlanePhase (Option ι) := splitInclusion phaseOptionSplit

 @[simp] theorem phaseInfinityInclusion_none (z : PlanePhase ι) : phaseInfinityInclusion z none=0 := rfl
 @[simp] theorem phaseInfinityInclusion_some (z : PlanePhase ι) (i : ι) : phaseInfinityInclusion z (some i)=z i := rfl

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_SphereCartesianDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Hamiltonian

def affineComplexEquiv (m : ℕ) : Affine m ≃L[ℝ] (Option (Fin m) → ℂ) :=
  ((LinearEquiv.piOptionEquivProd ℝ (M := fun _ : Option (Fin m) => ℂ)).symm).toContinuousLinearEquiv

@[simp] theorem affineComplexEquiv_apply (m : ℕ) (z : Affine m) :
    affineComplexEquiv m z=affineComplex m z := by
  funext j
  cases j <;> rfl

@[simp] theorem affineComplexEquiv_symm_apply (m : ℕ) (z : Option (Fin m) → ℂ) :
    (affineComplexEquiv m).symm z=(z none,fun j => z (some j)) := rfl

@[simp] theorem affineComplex_cartesian (m : ℕ) (z : Affine m) :
    complexCartesian (affineComplex m z)=affinePhase m z := by
  funext j
  cases j <;> rfl

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def cubicOuterBubblePrimitive {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ)
     (D : ℝ → ℝ) (ε : ℝ) : CubicAmbient → CubicAmbient →L[ℝ] ℝ :=
   (1-(L:ℝ)*D ε)•primitivePullback (hopfPrimitive c) (complexCartesian ∘ firstBubbleLift)+
     D ε•primitivePullback (hopfPrimitive c)
       (complexCartesian ∘ cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε ∘ firstBubbleLift)

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_SixCubicInnerNormalPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope
open FiniteMoment.Radial

 def cubicOuterBubbleForm {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ) (D : ℝ → ℝ) (ε : ℝ) :=
   euclideanExteriorOneForm (cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D ε)

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CurveArea
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

def curveDensity {n : ℕ} (σ τ : ℝ) (u : ℂ → Phase n) (z : Plane) : ℝ :=
  radialForm σ τ (realCurve u z)
    (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1))

def curvePrimitive {n : ℕ} (σ τ : ℝ) (u : ℂ → Phase n) : Plane → Plane →L[ℝ] ℝ :=
  planarPullback (realCurve u) (radialPrimitiveCLM σ τ)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Correction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

def planeRotation (z : Plane) : Plane := (-z.2,z.1)



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_AngularPoles
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

def angularPole (p : Plane) (z : Plane) : Plane →L[ℝ] ℝ := angularOneForm (z-p)

def poleSum (P : Finset Plane) (c : Plane → ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  ∑ p ∈ P, c p • angularPole p z


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

def correctedPrimitive {n : ℕ} (S T : ℝ) (U : Fin 2 → Set (Phase n))
    (f : Fin 2 → Phase n → Phase n) (σ τ : Fin 2 → ℝ) (y : Phase n) : Phase n →L[ℝ] ℝ :=
  radialPrimitiveCLM S T y + chartCorrection (U 0) (f 0) (σ 0) (τ 0) y +
    chartCorrection (U 1) (f 1) (σ 1) (τ 1) y


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane)



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_AffineCorrectionInfinity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open SymplecticBallPacking.Hamiltonian (Plane)
namespace HigherDimensionalBallPacking.Rigidity
variable {n : ℕ}

def affineCorrection (u : ℂ → Phase n) (a : Phase n) (z : ℂ) : Phase n := u z-z • a

end HigherDimensionalBallPacking.Rigidity

end
noncomputable section
open scoped ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {n : ℕ}

local instance ceInst1_rd3e885_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ceInst2_rd3e885_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
def defectEnergy (A : End n) (v : Phase n) : ℝ :=
  stdDot n ((A-standardJ n) v) ((A-standardJ n) v)

def symplecticEnergy (A : End n) (v : Phase n) : ℝ := stdOmega n v (A v)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_GradientBounds
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (b : ContDiffBump (0:ℂ))

omit [CompleteSpace E] in
@[simp] lemma cutoffTransport_apply (h z : ℂ) (v : E) : cutoffTransport b h z v=(fderiv ℝ b z h) • v := rfl
omit [CompleteSpace E] in
@[simp] lemma cutoffCommute_apply (z : ℂ) (v : E) :
    cutoffCommute b z v=(fderiv ℝ b z Complex.I) • v-Complex.I • ((fderiv ℝ b z 1) • v) := rfl


end
open scoped Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_JetCauchy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.lsoInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.lsoInst2
local instance lsoInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_CompactFredholmAlternative
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst2
local instance linCRInst4_rd3e885_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance linCRInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance

variable {K : Set ℂ}

local instance linCRInst6_rd3e885_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance linCRInst7_rd3e885_1 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst8_rd3e885_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst9_rd3e885_1 : NormedAddCommGroup (COne ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst10_rd3e885_1 : NormedSpace ℝ (COne ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst11_rd3e885_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance linCRInst12_rd3e885_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance linCRInst13_rd3e885_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance linCRInst14_rd3e885_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
lemma frameCRCoefficient_zero_outside (hK : IsClosed K) (M : COne ℂ (E →L[ℝ] E)) (c : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E) :
    ∀ z ∉ K, valueCLM _ (frameCRCoefficient M) z = 0 := by
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  rw [frameCRCoefficient_value,coefficientDeriv_zero_outside hK M c hM hz]
  simp only [zero_apply,smul_zero,sub_self]

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FrameFredholm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [ProperSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst2
local instance frameFredInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance frameFredInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance frameFredInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance frameFredInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
variable {K : Set ℂ} (hK : IsCompact K)
local instance frameFredInst7 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance frameFredInst8 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance frameFredInst9 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance frameFredInst10 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
local instance frameFredInst11 : AddCommGroup (markedModel (E := E) K) :=
  (frameFredInst7 (E := E) (K := K)).toAddCommGroup
local instance frameFredInst12 : Module ℝ (markedModel (E := E) K) :=
  (frameFredInst8 (E := E) (K := K)).toModule
local instance frameFredInst13 : AddCommGroup (supportedHolder (E := E) K) :=
  (frameFredInst9 (E := E) (K := K)).toAddCommGroup
local instance frameFredInst14 : Module ℝ (supportedHolder (E := E) K) :=
  (frameFredInst10 (E := E) (K := K)).toModule


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst2
local instance ccFrameInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance ccFrameInst4_rd3e885_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance ccFrameInst5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Energy_ResidualEnergy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

def sourceRadialCutoff (A : ℝ) (z : Plane) : ℝ := outerProfile A (radiusSq z)


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Energy_CircularEnergy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

def circlePlane (r θ : ℝ) : Plane := (r*Real.cos θ,r*Real.sin θ)


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Campanato_MeasureEnergy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}


def squareMeasure (a b : ℝ) : Measure Plane :=
  (volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))

instance squareMeasure_finite (a b : ℝ) : IsFiniteMeasure (squareMeasure a b) := by
  unfold squareMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Campanato_TranslatedSquare
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

def translatedSquare (c : Plane) (r : ℝ) : Measure Plane :=
  Measure.map (fun z => z+c) (squareMeasure (-r) r)

instance translatedSquare_finite (c : Plane) (r : ℝ) : IsFiniteMeasure (translatedSquare c r) := by
  unfold translatedSquare
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_NonlinearReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)

variable {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) {t : ℝ} {x : X}
  (hD : HasFDerivAt (fun y => F (t,y)) D x)

def parametricObstruction (v : ℝ × pkg.decDom.X₀) : pkg.decCodom.X₀ :=
  ((codCoords pkg) (F (v.1,parametricSolution pkg hF hD v))).2

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.pfrK
local instance pfrC_rd3e885_1 : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.pfrX
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.pfrY
lemma parametricInfiniteSolution_base :
    parametricInfiniteSolution pkg hF hD (t,((domCoords pkg) x).2)=((domCoords pkg) x).1 :=
  (parametricEssential_smooth pkg hF).contDiffAt.implicitFunction_apply_self (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    (parametricEssential_invertible pkg hF hD)

lemma parametricSolution_base : parametricSolution pkg hF hD (t,((domCoords pkg) x).2)=x := by
  rw [parametricSolution,parametricInfiniteSolution_base]
  exact (domCoords pkg).symm_apply_apply x

lemma parametricSolution_smooth :
    ContDiffAt ℝ ∞ (parametricSolution pkg hF hD) (t,((domCoords pkg) x).2) :=
  (domCoords pkg).symm.contDiff.contDiffAt.comp _
    (((parametricEssential_smooth pkg hF).contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      (parametricEssential_invertible pkg hF hD)).prodMk contDiffAt_snd)

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end


