-- Prove2me | Definitions.Def_OAIQ059C003
-- name    : OAIQ059C003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:38:41.515997+00:00
-- url     : https://prove2.me/theorems/f9d7a39f-47fa-4ae7-950c-2042b07ab0d4
-- title:
--   Definitions bundle OAIQ059C003 of the split of OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 352 declarations of OpenAI's Lean: 112 definitions, 10 inductive types or structures, 1 instance and 229 theorems. The definitions and types are `OAI.ScalarConductivity.BoundedRootSources`, `OAI.ScalarConductivity.BoundedRootSources.coefficient`, `OAI.ScalarConductivity.BoundedRootSources.finiteSource`, `OAI.ScalarConductivity.BoundedRootSources.form`, `OAI.ScalarConductivity.BoundedRootSources.initial`, `OAI.ScalarConductivity.BoundedRootSources.root`, `OAI.ScalarConductivity.BoundedRootSources.seed`, `OAI.ScalarConductivity.BoundedRootSources.sourceHarmonic`, `OAI.ScalarConductivity.CentralGradients`, `OAI.ScalarConductivity.CentralVariationalEquation`, `OAI.ScalarConductivity.CompactCompatibleReplacement`, `OAI.ScalarConductivity.CompactCompatibleReplacement.constantRank`, `OAI.ScalarConductivity.CompactCompatibleReplacement.unchanged`, `OAI.ScalarConductivity.CompactGlobalUpdate`, `OAI.ScalarConductivity.CompactGlobalUpdate.fieldPair`, `OAI.ScalarConductivity.CompactGlobalUpdate.refl`, `OAI.ScalarConductivity.CompactGlobalUpdate.trans`, `OAI.ScalarConductivity.CompactSelectedReplacement`, `OAI.ScalarConductivity.CompactSelectedReplacement.affineTransfer`, `OAI.ScalarConductivity.CompactSelectedReplacement.changeOld`, `OAI.ScalarConductivity.CompactTwoFieldReplacement`, `OAI.ScalarConductivity.CompactTwoFieldReplacement.changeOld`, `OAI.ScalarConductivity.CompactTwoFieldReplacement.forgetRank`, `OAI.ScalarConductivity.CoordBump`, `OAI.ScalarConductivity.CylinderTraceAmbient`, `OAI.ScalarConductivity.ParametricCorrectionBox`, `OAI.ScalarConductivity.ParametricCorrectionBox.toVanishing`, `OAI.ScalarConductivity.PhysicalFiniteEndingData`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.compression`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.flatTensor`, `OAI.ScalarConductivity.RegularCorrectionBox`, `OAI.ScalarConductivity.RegularCorrectionBox.region`, `OAI.ScalarConductivity.SmoothVanishingPairFamily`, `OAI.ScalarConductivity.SourceSupported`, `OAI.ScalarConductivity.TorusEndingData`, `OAI.ScalarConductivity.VanishingCorrectionRegion`, `OAI.ScalarConductivity.attachedCartesianMatrix`, `OAI.ScalarConductivity.attachedFlatTensor`, `OAI.ScalarConductivity.attachedVariableTensor`, `OAI.ScalarConductivity.ballWholePiComponentCLM` and 82 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Conductivity_Branching_BranchFiniteEnding`, `Conductivity_Branching_ChildCoordinateAnalysis`, `Conductivity_Branching_ChildInverse`, `Conductivity_Branching_FlatEndingSplice`, `Conductivity_Branching_MeasurableDisjointGluing`, `Conductivity_Branching_ParametricCorrectionTransport`, `Conductivity_Branching_ParentLocalizedJet`, `Conductivity_Branching_PhysicalFiniteEndingData`, `Conductivity_Branching_PhysicalFlatTransport`, `Conductivity_Branching_PhysicalOpenBlock`, `Conductivity_Branching_RegularMomentTransport`, `Conductivity_Branching_SmoothFamilyCorrectionTransport`, `Conductivity_Branching_TorusEndingCorrection`, `Conductivity_Flux_AttachedFlatTensor`, `Conductivity_Flux_CentralCylinderGreen`, `Conductivity_Flux_CentralDistribution`, `Conductivity_Flux_CollarCartesianDifferential`, `Conductivity_Flux_CompactInteriorDivergence`, `Conductivity_Flux_FiniteEndPhysicalTensor`, `Conductivity_Flux_FlatBackgroundTensor`, `Conductivity_Flux_PhysicalBlockTensor`, `Conductivity_Flux_PhysicalChildTensor`, `Conductivity_Flux_PhysicalSplicedGreen`, `Conductivity_Flux_PhysicalTensorPatch`, `Conductivity_Flux_PiolaFluxAdd`, `Conductivity_Flux_SmoothFluxIntegrable`, `Conductivity_Flux_TorusCylinderGreenReal`, `Conductivity_Flux_VariableBlockTensor`, `Conductivity_Flux_VariableCollarTensor`, `Conductivity_Fourier_AngularIntegratedTrace`, `Conductivity_Fourier_AngularIntegration`, `Conductivity_Fourier_AngularNormalTrace`, `Conductivity_Fourier_AngularSignedTrace`, `Conductivity_Fourier_EndPoissonJets`, `Conductivity_Fourier_EndPoissonRepresentative`, `Conductivity_Fourier_FourierMatchingElliptic`, `Conductivity_Fourier_RectangularTorusAtlas`, `Conductivity_Fourier_RectangularTorusInverse`, `Conductivity_Fourier_TorusPoissonContinuous`, `Conductivity_Geometry_BoxCoordinateBridge`, `Conductivity_Geometry_BoxIteration`, `Conductivity_Geometry_BoxMomentRightInverse`, `Conductivity_Geometry_CollarVolumeBound`, `Conductivity_Geometry_ExtendedCollar`, `Conductivity_Geometry_PhysicalCollarTrace`, `Conductivity_Geometry_PhysicalEndRegions`, `Conductivity_Geometry_RegularPotentialCoordinates`, `Conductivity_Geometry_TorusFaceIntegration`, `Conductivity_Scalarization_UpdateFieldPair`, `Conductivity_Sobolev_CentralPhysicalRegion`, `Conductivity_Sobolev_CentralPoincare`, `Conductivity_Sobolev_ChildH10Transport`, `Conductivity_Sobolev_CompactUpdateLp`, `Conductivity_Sobolev_CylinderSobolevGraph`, `Conductivity_Sobolev_ParentCompletionJoin`, `Conductivity_Sobolev_SobolevSmoothTests`, `Conductivity_Sources_BranchCombine`, `Conductivity_Sources_CopiedEnergyAlgebra`, `Conductivity_Sources_CopiedScalarCoefficient`, `Conductivity_Sources_FacePasting`, `Conductivity_Sources_LocalPhysicalCorrection`, `Conductivity_Sources_NestedGeometry`, `Conductivity_Sources_ParametricSymmetricSources`, `Conductivity_Sources_PhysicalMaximum`, `Conductivity_Sources_WordGeometry`, `Conductivity_Variational_C1VoltageApproximation`, `Conductivity_Variational_CentralEnergySpace`, `Conductivity_Variational_CentralEuclideanBridge`, `Conductivity_Variational_CentralUnnormalizedVariational`, `Conductivity_Variational_CentralVariational`, `Conductivity_Variational_ChangeOld`, `Conductivity_Variational_CompactCompatibleReplacement`, `Conductivity_Variational_CompactGlobalUpdate`, `Conductivity_Variational_CompactPhysicalCorrections`, `Conductivity_Variational_CompactRegularCorrection`, `Conductivity_Variational_CompactSelectedReplacement`, `Conductivity_Variational_FieldVectorCLM`, `Conductivity_Variational_FullWeakEndEnergy`, `Conductivity_Variational_GlobalRegularCorrection`, `Conductivity_Variational_ParametricLocalRegularCorrection`, `Conductivity_Variational_PhysicalFlatEllipticity`, `Conductivity_Variational_PhysicalOpenVoltage`, `Conductivity_Variational_PhysicalOuterTrace`, `Conductivity_Variational_PhysicalOverlapMoments`, `Conductivity_Variational_PhysicalTraceBounds`, `Conductivity_Variational_QuantitativePhysicalMoments`, `Conductivity_Variational_Refl`, `Conductivity_Variational_SymmetricQuadraticBound`, `Conductivity_Variational_Unchanged`, `Conductivity_Variational_UnitSquarePoincare`, `Conductivity_Variational_WholeBallJet`, `Conductivity_Walls_ParametricWallTensors`, `Conductivity_Walls_WallSideMoments`.
--
--   **Imports.** It imports the published bundle `Def_Conductivity`; the bundles `OAIQ059C000` and `OAIQ059C001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ059C006` and `OAIQ059C007`; the statements `OAI.ScalarConductivity.boundedRootSources_nonempty`, `OAI.ScalarConductivity.central_pair_regular_exists`, `OAI.ScalarConductivity.elliptic_fourier_matching_regular`, `OAI.ScalarConductivity.fine_global_scalar_tensor_approximation` and `OAI.ScalarConductivity.physicalFiniteEndingData_nonempty`.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C000
import Definitions.Def_OAIQ059C001

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_NestedGeometry
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def sourceDomain : Set R3 := {x | sourceHole < max (|x 0|/sourceLength) |x 1| ∧
    max (|x 0|/sourceLength) |x 1| < 1 ∧ |x 2| < 1}

def sourceOuterBox : Set R3 := {x | |x 0| ≤ sourceLength ∧ |x 1| ≤ 1 ∧ |x 2| ≤ 1}

def sourceShift (σ : ℝ) : R3 := EuclideanSpace.single 0 (σ*sourceOffset)

def sourceSimilarity (σ : ℝ) : R3 ≃ₜ R3 where
  toFun x := sourceScale • sourceSwap x+sourceShift σ
  invFun x := sourceSwap.symm (sourceScale⁻¹ • (x-sourceShift σ))
  left_inv x := by simp [sourceScale,smul_smul]
  right_inv x := by simp [sourceScale,smul_smul]
  continuous_toFun := (sourceSwap.continuous.const_smul sourceScale).add
    (continuous_const : Continuous (fun _ : R3 => sourceShift σ))
  continuous_invFun := sourceSwap.symm.continuous.comp
    ((continuous_id.sub (continuous_const : Continuous (fun _ : R3 => sourceShift σ))).const_smul sourceScale⁻¹)

lemma sourceSimilarity_coord (σ : ℝ) (x : R3) :
    sourceSimilarity σ x 0=sourceScale*x 1+σ*sourceOffset ∧
    sourceSimilarity σ x 1=sourceScale*x 0 ∧
    sourceSimilarity σ x 2=sourceScale*x 2 := by
  change (sourceScale • sourceSwap x+sourceShift σ) 0=_ ∧
    (sourceScale • sourceSwap x+sourceShift σ) 1=_ ∧
    (sourceScale • sourceSwap x+sourceShift σ) 2=_
  simp [sourceShift,PiLp.add_apply,PiLp.smul_apply,(sourceSwap_apply x).1,
    (sourceSwap_apply x).2.1,(sourceSwap_apply x).2.2]

lemma sourceDomain_isOpen : IsOpen sourceDomain := by
  have h₀ : Continuous (fun x : R3 => |x 0|/sourceLength) :=
    (EuclideanSpace.proj 0).continuous.abs.div_const _
  have h₁ : Continuous (fun x : R3 => |x 1|) := (EuclideanSpace.proj 1).continuous.abs
  have h₂ : Continuous (fun x : R3 => |x 2|) := (EuclideanSpace.proj 2).continuous.abs
  exact (isOpen_lt continuous_const (h₀.max h₁)).inter
    ((isOpen_lt (h₀.max h₁) continuous_const).inter (isOpen_lt h₂ continuous_const))

lemma sourceOuterBox_isClosed : IsClosed sourceOuterBox := by
  exact (isClosed_le (EuclideanSpace.proj 0).continuous.abs continuous_const).inter
    ((isClosed_le (EuclideanSpace.proj 1).continuous.abs continuous_const).inter
      (isClosed_le (EuclideanSpace.proj 2).continuous.abs continuous_const))

lemma sourceDomain_subset_box : sourceDomain⊆sourceOuterBox := by
  intro x hx
  have h₀ := (max_lt_iff.mp hx.2.1).1
  have h₁ := (max_lt_iff.mp hx.2.1).2
  refine ⟨?_,h₁.le,hx.2.2.le⟩
  dsimp [sourceLength] at *
  linarith

lemma sourceClosure_subset_box : closure sourceDomain⊆sourceOuterBox :=
  closure_minimal sourceDomain_subset_box sourceOuterBox_isClosed

lemma sourceBox_norm_bound {x : R3} (hx : x∈sourceOuterBox) : ‖x‖ < 5/2 := by
  have hn := EuclideanSpace.real_norm_sq_eq x
  simp [Fin.sum_univ_succ] at hn
  have h₀ := abs_le.mp hx.1
  have h₁ := abs_le.mp hx.2.1
  have h₂ := abs_le.mp hx.2.2
  dsimp [sourceLength] at h₀
  have hq₀ : (x 0)^2 ≤ (8/5:ℝ)^2 := by
    have hh : |x 0|^2 ≤ (8/5:ℝ)^2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr hx.1
    simpa only [sq_abs] using hh
  have hq₁ : (x 1)^2 ≤ 1 := by nlinarith [sq_le_sq₀ (abs_nonneg (x 1)) (by norm_num : (0:ℝ) ≤ 1) |>.mpr hx.2.1]
  have hq₂ : (x 2)^2 ≤ 1 := by nlinarith [sq_le_sq₀ (abs_nonneg (x 2)) (by norm_num : (0:ℝ) ≤ 1) |>.mpr hx.2.2]
  nlinarith [norm_nonneg x]

lemma sourceClosure_subset_ball : closure sourceDomain⊆Metric.ball (0:R3) (5/2) := by
  intro x hx
  simpa only [Metric.mem_ball,dist_zero_right] using sourceBox_norm_bound (sourceClosure_subset_box hx)

lemma sourceDomain_isBounded : Bornology.IsBounded sourceDomain :=
  (Metric.isBounded_ball (x := (0:R3)) (r := (5/2:ℝ))).subset
    (fun _ hx => sourceClosure_subset_ball (subset_closure hx))

lemma sourceClosure_isCompact : IsCompact (closure sourceDomain) :=
  (Metric.isCompact_iff_isClosed_bounded).mpr ⟨isClosed_closure,sourceDomain_isBounded.closure⟩

lemma source_children_coords {x : R3} (hx : x∈sourceOuterBox) :
    (24/100:ℝ) ≤ sourceSimilarity 1 x 0 ∧ sourceSimilarity 1 x 0 ≤ 138/100 ∧
    -(138/100:ℝ) ≤ sourceSimilarity (-1) x 0 ∧ sourceSimilarity (-1) x 0 ≤ -(24/100:ℝ) ∧
    |sourceSimilarity 1 x 1| ≤ 912/1000 ∧ |sourceSimilarity (-1) x 1| ≤ 912/1000 ∧
    |sourceSimilarity 1 x 2| ≤ 57/100 ∧ |sourceSimilarity (-1) x 2| ≤ 57/100 := by
  have h₀ := abs_le.mp hx.1
  have h₁ := abs_le.mp hx.2.1
  have h₂ := abs_le.mp hx.2.2
  rw [(sourceSimilarity_coord 1 x).1,(sourceSimilarity_coord (-1) x).1,
    (sourceSimilarity_coord 1 x).2.1,(sourceSimilarity_coord (-1) x).2.1,
    (sourceSimilarity_coord 1 x).2.2,(sourceSimilarity_coord (-1) x).2.2]
  simp only [abs_mul,sourceScale,sourceOffset,abs_of_pos (by norm_num : (0:ℝ) < 57/100)]
  dsimp [sourceLength] at h₀
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · have hh : |x 0| ≤ (8/5:ℝ) := hx.1; linarith
  constructor; · have hh : |x 0| ≤ (8/5:ℝ) := hx.1; linarith
  constructor <;> linarith [hx.2.2]

lemma source_positive_child_in_parent {x : R3} (hx : x∈sourceOuterBox) :
    sourceSimilarity 1 x∈sourceDomain := by
  obtain ⟨hmin,hmax,_,_,hy,_,hz,_⟩ := source_children_coords hx
  have hpos : 0 ≤ sourceSimilarity 1 x 0 := by linarith
  change sourceHole < max _ _ ∧ max _ _ < 1 ∧ _
  refine ⟨lt_of_lt_of_le ?_ (le_max_left _ _),max_lt ?_ ?_,?_⟩
  · rw [abs_of_nonneg hpos]; norm_num [sourceHole,sourceLength]; linarith
  · rw [abs_of_nonneg hpos]; norm_num [sourceLength]; linarith
  · linarith
  · linarith

lemma source_negative_child_in_parent {x : R3} (hx : x∈sourceOuterBox) :
    sourceSimilarity (-1) x∈sourceDomain := by
  obtain ⟨_,_,hmin,hmax,_,hy,_,hz⟩ := source_children_coords hx
  have hneg : sourceSimilarity (-1) x 0 ≤ 0 := by linarith
  change sourceHole < max _ _ ∧ max _ _ < 1 ∧ _
  refine ⟨lt_of_lt_of_le ?_ (le_max_left _ _),max_lt ?_ ?_,?_⟩
  · rw [abs_of_nonpos hneg]; norm_num [sourceHole,sourceLength]; linarith
  · rw [abs_of_nonpos hneg]; norm_num [sourceLength]; linarith
  · linarith
  · linarith

theorem source_children_compact_inside :
    IsCompact (sourceSimilarity 1 '' closure sourceDomain) ∧
    IsCompact (sourceSimilarity (-1) '' closure sourceDomain) ∧
    sourceSimilarity 1 '' closure sourceDomain⊆sourceDomain ∧
    sourceSimilarity (-1) '' closure sourceDomain⊆sourceDomain ∧
    Disjoint (sourceSimilarity 1 '' closure sourceDomain)
      (sourceSimilarity (-1) '' closure sourceDomain) := by
  refine ⟨sourceClosure_isCompact.image (sourceSimilarity 1).continuous,
    sourceClosure_isCompact.image (sourceSimilarity (-1)).continuous,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact source_positive_child_in_parent (sourceClosure_subset_box hx)
  · rintro _ ⟨x,hx,rfl⟩
    exact source_negative_child_in_parent (sourceClosure_subset_box hx)
  · rw [Set.disjoint_left]
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    have h₁ := (source_children_coords (sourceClosure_subset_box hx)).1
    have h₂ := (source_children_coords (sourceClosure_subset_box hy)).2.2.2.1
    have hh := congrArg (fun p : R3 => p 0) he
    linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_RectangularTorusAtlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def squareFaceParameter (i : Fin 4) (v : Fin 2 → ℝ) : ℝ :=
  squareFaceDirection i 0*v 0+squareFaceDirection i 1*v 1

lemma squareFace_parameter (i : Fin 4) (a r : ℝ) :
    squareFaceParameter i (r • squareFace i a)=r*a := by
  fin_cases i <;> simp [squareFaceParameter,squareFace,squareFaceBase,squareFaceDirection]

lemma squareFace_determinant (i : Fin 4) (a : ℝ) :
    squareFace i a 0*squareFaceDirection i 1-
      squareFaceDirection i 0*squareFace i a 1=1 := by
  fin_cases i <;> simp [squareFace,squareFaceBase,squareFaceDirection]

def sourceCollarJacobian (i j : Fin 4) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![-sourceLength*sourceRadialWidth*squareFace j (x 2) 0*squareFace i (x 1) 0,
       sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFaceDirection i 0,
       sourceLength*sourceRadialWidth*(1-x 0)*squareFaceDirection j 0*squareFace i (x 1) 0],
    ![-sourceRadialWidth*squareFace j (x 2) 0*squareFace i (x 1) 1,
       sourceCollarRadius j (x 0) (x 2)*squareFaceDirection i 1,
       sourceRadialWidth*(1-x 0)*squareFaceDirection j 0*squareFace i (x 1) 1],
    ![-squareFace j (x 2) 1,0,(1-x 0)*squareFaceDirection j 1]]

def sourceCollarDerivative (i j : Fin 4) (x : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (Matrix.toLin' (sourceCollarJacobian i j x)).toContinuousLinearMap

lemma squareFace_coord_hasFDeriv (i : Fin 4) (k : Fin 2) (l : Fin 3) (x : Fin 3 → ℝ) :
    HasFDerivAt (fun y : Fin 3 → ℝ => squareFace i (y l) k)
      (squareFaceDirection i k • (ContinuousLinearMap.proj l : (Fin 3 → ℝ) →L[ℝ] ℝ)) x := by
  convert (hasFDerivAt_const (𝕜 := ℝ) (squareFaceBase i k) x).add
      ((hasFDerivAt_apply (𝕜 := ℝ) l x).mul_const (squareFaceDirection i k)) using 1 <;> first | rfl | simp

lemma sourceCollarPiece_hasFDeriv (i j : Fin 4) (x : Fin 3 → ℝ) :
    HasFDerivAt (sourceCollarPiece i j) (sourceCollarDerivative i j x) x := by
  have ht := (hasFDerivAt_const (1:ℝ) x).sub (hasFDerivAt_apply (𝕜 := ℝ) 0 x)
  have hr := (hasFDerivAt_const sourceRadialCenter x).add
    ((ht.const_mul sourceRadialWidth).mul (squareFace_coord_hasFDeriv j 0 2 x))
  have hf0 := (hr.const_mul sourceLength).mul (squareFace_coord_hasFDeriv i 0 1 x)
  have hf1 := hr.mul (squareFace_coord_hasFDeriv i 1 1 x)
  have hf2 := ht.mul (squareFace_coord_hasFDeriv j 1 2 x)
  have hcoord (k : Fin 3) : HasFDerivAt (fun y => sourceCollarPiece i j y k)
      ((ContinuousLinearMap.proj k : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
        (sourceCollarDerivative i j x)) x := by
    fin_cases k
    · convert hf0 using 1 <;> try rfl
      ext y
      simp [sourceCollarDerivative,sourceCollarJacobian,Matrix.toLin',LinearMap.toMatrix',Matrix.mulVecLin,Matrix.mulVecBilin,
        Matrix.mulVec,Fin.sum_univ_succ,dotProduct,sourceCollarRadius]
      ring
    · convert hf1 using 1 <;> try rfl
      ext y
      simp [sourceCollarDerivative,sourceCollarJacobian,Matrix.toLin',LinearMap.toMatrix',Matrix.mulVecLin,Matrix.mulVecBilin,
        Matrix.mulVec,Fin.sum_univ_succ,dotProduct,sourceCollarRadius]
      ring
    · convert hf2 using 1 <;> try rfl
      ext y
      simp [sourceCollarDerivative,sourceCollarJacobian,Matrix.toLin',LinearMap.toMatrix',Matrix.mulVecLin,Matrix.mulVecBilin,
        Matrix.mulVec,Fin.sum_univ_succ,dotProduct,sourceCollarRadius]
      ring
  have hfull := hasFDerivAt_pi.mpr hcoord
  convert hfull using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma sourceCollarJacobian_det (i j : Fin 4) (x : Fin 3 → ℝ) :
    (sourceCollarJacobian i j x).det =
      -sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0) := by
  rw [Matrix.det_fin_three]
  simp [sourceCollarJacobian]
  calc
    _= -sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0)*
        (squareFace i (x 1) 0*squareFaceDirection i 1-
          squareFaceDirection i 0*squareFace i (x 1) 1)*
        (squareFace j (x 2) 0*squareFaceDirection j 1-
          squareFaceDirection j 0*squareFace j (x 2) 1) := by ring
    _= _ := by rw [squareFace_determinant,squareFace_determinant]; ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_RectangularTorusInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def sourceCollarInverse (i j : Fin 4) (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![sourceCollarTime y,
    squareFaceParameter i ![y 0/sourceLength,y 1]/sourceRadial y,
    squareFaceParameter j (sourceCrossCoordinates y)/(1-sourceCollarTime y)]

lemma sourceCollarPiece_angular (i j : Fin 4) (x : Fin 3 → ℝ) :
    ![sourceCollarPiece i j x 0/sourceLength,sourceCollarPiece i j x 1]=
      sourceCollarRadius j (x 0) (x 2) • squareFace i (x 1) := by
  have hL : sourceLength≠0 := by norm_num [sourceLength]
  ext k; fin_cases k
  · change sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0/sourceLength=_
    simp only [Pi.smul_apply,smul_eq_mul]
    field_simp
    rfl
  · rfl

lemma sourceCollarDerivative_det (i j : Fin 4) (x : Fin 3 → ℝ) :
    (sourceCollarDerivative i j x).det =
      -sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0) := by
  change LinearMap.det (Matrix.toLin' (sourceCollarJacobian i j x))=_
  rw [LinearMap.det_toLin',sourceCollarJacobian_det]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_UnitSquarePoincare
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def unitCubeAverage (f : Box3 → ℝ) : ℝ :=
  unitSquareAverage (fun y => unitAverage (fun x => f (y,x)))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_ExtendedCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

lemma sourceCollarPiece_radial_pos (i j : Fin 4) {x : Fin 3 → ℝ}
    (hr : 0≤ sourceCollarRadius j (x 0) (x 2)) (ha : |x 1|≤1) :
    sourceRadial (sourceCollarPiece i j x)=sourceCollarRadius j (x 0) (x 2) := by
  have hL : 0 < sourceLength := by norm_num [sourceLength]
  simp only [sourceRadial,sourceCollarPiece,Matrix.cons_val_zero,Matrix.cons_val_one,
    abs_mul,abs_of_pos hL,abs_of_nonneg hr]
  have he : sourceLength*sourceCollarRadius j (x 0) (x 2)*|squareFace i (x 1) 0|/sourceLength =
      sourceCollarRadius j (x 0) (x 2)*|squareFace i (x 1) 0| := by field_simp
  rw [he,←mul_max_of_nonneg _ _ hr,squareFace_max i ha,mul_one]

lemma sourceCollarPiece_cross_pos (i j : Fin 4) {x : Fin 3 → ℝ}
    (hr : 0≤ sourceCollarRadius j (x 0) (x 2)) (ha : |x 1|≤1) :
    sourceCrossCoordinates (sourceCollarPiece i j x)=(1-x 0) • squareFace j (x 2) := by
  ext k; fin_cases k
  · change (sourceRadial (sourceCollarPiece i j x)-sourceRadialCenter)/sourceRadialWidth=
      (1-x 0)*squareFace j (x 2) 0
    rw [sourceCollarPiece_radial_pos i j hr ha,sourceCollarRadius]
    simp only [add_sub_cancel_left]
    have hw : sourceRadialWidth≠0 := by norm_num [sourceRadialWidth,sourceHole]
    field_simp
  · simp [sourceCrossCoordinates,sourceCollarPiece]

lemma sourceCollarPiece_time_pos (i j : Fin 4) {x : Fin 3 → ℝ}
    (hr : 0≤ sourceCollarRadius j (x 0) (x 2)) (ht : x 0≤1)
    (ha : |x 1|≤1) (hb : |x 2|≤1) :
    sourceCollarTime (sourceCollarPiece i j x)=x 0 := by
  rw [sourceCollarTime,sourceCollarPiece_cross_pos i j hr ha]
  simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht)]
  rw [←mul_max_of_nonneg _ _ (sub_nonneg.mpr ht),squareFace_max j hb]
  ring

lemma sourceCollarInverse_left_pos (i j : Fin 4) {x : Fin 3 → ℝ}
    (hr : 0 < sourceCollarRadius j (x 0) (x 2)) (ht : x 0<1)
    (ha : |x 1|≤1) (hb : |x 2|≤1) :
    sourceCollarInverse i j (sourceCollarPiece i j x)=x := by
  have hq : 1-x 0≠0 := (sub_pos.mpr ht).ne'
  ext k; fin_cases k
  · exact sourceCollarPiece_time_pos i j hr.le ht.le ha hb
  · change squareFaceParameter i ![sourceCollarPiece i j x 0/sourceLength,
        sourceCollarPiece i j x 1]/sourceRadial (sourceCollarPiece i j x)=x 1
    rw [sourceCollarPiece_angular,squareFace_parameter,sourceCollarPiece_radial_pos i j hr.le ha]
    exact mul_div_cancel_left₀ _ hr.ne'
  · change squareFaceParameter j (sourceCrossCoordinates (sourceCollarPiece i j x))/
        (1-sourceCollarTime (sourceCollarPiece i j x))=x 2
    rw [sourceCollarPiece_cross_pos i j hr.le ha,squareFace_parameter,
      sourceCollarPiece_time_pos i j hr.le ht.le ha hb]
    exact mul_div_cancel_left₀ _ hq

lemma sourceCollarRadius_extended (j : Fin 4) {t b : ℝ}
    (ht : t∈Icc (-(1:ℝ)/100) (1/100)) (hb : |b|≤1) :
    (1:ℝ)/50≤ sourceCollarRadius j t b ∧ sourceCollarRadius j t b≤2 := by
  have hq : |squareFace j b 0|≤1 := (le_max_left _ _).trans (squareFace_max j hb).le
  have hh := abs_le.mp hq
  have hprod : |(1-t)*squareFace j b 0|≤101/100 := by
    rw [abs_mul,abs_of_nonneg (by linarith [ht.2] : 0≤1-t)]
    nlinarith [ht.1,ht.2]
  have hh' := abs_le.mp hprod
  dsimp [sourceCollarRadius,sourceRadialCenter,sourceRadialWidth,sourceHole]
  constructor <;> linarith

lemma sourceExtendedBox_injOn (i j : Fin 4) {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    InjOn (sourceCollarPiece i j) (sourceExtendedBox l r) := by
  have hi (x : Fin 3 → ℝ) (hx : x∈sourceExtendedBox l r) :
      sourceCollarInverse i j (sourceCollarPiece i j x)=x := by
    obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
    exact sourceCollarInverse_left_pos i j
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/50)
        (sourceCollarRadius_extended j ⟨hl.trans ht.1,ht.2.trans hr⟩ hb).1)
      (by linarith [ht.2]) ha hb
  intro x hx y hy he
  apply_fun sourceCollarInverse i j at he
  rwa [hi x hx,hi y hy] at he

lemma sourceExtended_jacobian_lower (i j : Fin 4) {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox l r) :
    (1:ℝ)/100≤abs ((sourceCollarDerivative i j x).det) := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  have ht' : x 0∈Icc (-(1:ℝ)/100) (1/100) := ⟨hl.trans ht.1,ht.2.trans hr⟩
  have hR := (sourceCollarRadius_extended j ht' hb).1
  rw [sourceCollarDerivative_det]
  have he : -sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0)=
      -(sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0)) := by ring
  rw [he,abs_neg,abs_of_nonneg (by
    have : 0≤ sourceCollarRadius j (x 0) (x 2) := by linarith
    have : 0≤1-x 0 := by linarith [ht'.2]
    norm_num [sourceLength,sourceRadialWidth,sourceHole]; positivity)]
  have hh := mul_le_mul hR (show (99:ℝ)/100≤1-x 0 by linarith [ht'.2])
    (by norm_num : (0:ℝ)≤99/100) (by linarith : 0≤ sourceCollarRadius j (x 0) (x 2))
  norm_num [sourceLength,sourceRadialWidth,sourceHole]
  nlinarith

theorem sourceExtended_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i j : Fin 4) {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (g : (Fin 3 → ℝ) → F) :
    (∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y)=
      ∫ x in sourceExtendedBox l r,abs ((sourceCollarDerivative i j x).det) •
        g (sourceCollarPiece i j x) := by
  exact integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_Icc
    (fun x _ => (sourceCollarPiece_hasFDeriv i j x).hasFDerivWithinAt)
    (sourceExtendedBox_injOn i j hl hr) g

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularNormalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

def sourceAngularVelocity (x : UnitAddTorus (Fin 2)) : Fin 3 → ℝ :=
  let z := sourceRayCoordinates x
  ![-sourceLength*z 2*z 0,-z 2*z 1,-z 3]

lemma sourceAngular_affine (t a : ℝ) (x : UnitAddTorus (Fin 2)) :
    sourceAngularCollar (t+a) x=sourceAngularCollar t x+a • sourceAngularVelocity x := by
  ext i
  fin_cases i <;> simp [sourceAngularCollar,sourceAngularPolynomial,sourceAngularVelocity] <;> ring

lemma sourceAngularVelocity_norm (x : UnitAddTorus (Fin 2)) : ‖sourceAngularVelocity x‖≤8 := by
  have hz := sourceRayCoordinates_mem x
  have hb (i : Fin 4) : |sourceRayCoordinates x i|≤2 := abs_le.mpr ⟨hz.1 i,hz.2 i⟩
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤8)).mpr
  intro i
  fin_cases i <;> simp [sourceAngularVelocity,Real.norm_eq_abs]
  · have hh := mul_le_mul (hb 2) (hb 0) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
    norm_num [sourceLength] at *
    nlinarith [abs_nonneg (sourceRayCoordinates x 2*sourceRayCoordinates x 0)]
  · have hh := mul_le_mul (hb 2) (hb 1) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
    linarith
  · linarith [hb 3]

lemma continuous_sourceAngularVelocity : Continuous sourceAngularVelocity := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [sourceAngularVelocity]
  · exact (continuous_const.mul ((continuous_apply (2 : Fin 4)).comp continuous_sourceRayCoordinates)).mul
      ((continuous_apply (0 : Fin 4)).comp continuous_sourceRayCoordinates)
  · exact (((continuous_apply (2 : Fin 4)).comp continuous_sourceRayCoordinates).neg).mul
      ((continuous_apply (1 : Fin 4)).comp continuous_sourceRayCoordinates)
  · exact ((continuous_apply (3 : Fin 4)).comp continuous_sourceRayCoordinates).neg

lemma sourceAngular_normal_deriv {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (t a : ℝ) (x : UnitAddTorus (Fin 2)) :
    deriv (fun s => f (sourceAngularCollar (t+s) x)) a=
      fderiv ℝ f (sourceAngularCollar (t+a) x) (sourceAngularVelocity x) := by
  have hd := (((hf.differentiable (by simp) (sourceAngularCollar t x+a • sourceAngularVelocity x)).hasFDerivAt).comp_hasDerivAt a
    (((hasDerivAt_id a).smul_const (sourceAngularVelocity x)).const_add (sourceAngularCollar t x))).deriv
  change deriv (fun s : ℝ => f (sourceAngularCollar t x+s • sourceAngularVelocity x)) a=_ at hd
  simpa only [sourceAngular_affine,one_smul] using hd

theorem sourceAngular_pointwise_trace {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (t : ℝ) {η : ℝ} (hη : 0<η)
    (x : UnitAddTorus (Fin 2)) :
    (f (sourceAngularCollar t x))^2≤(1+1/η)*(∫ a in (0:ℝ)..η,
      64*‖fderiv ℝ f (sourceAngularCollar (t+a) x)‖^2+
        2*(f (sourceAngularCollar (t+a) x))^2) := by
  have hq : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun a : ℝ => f (sourceAngularCollar (t+a) x)) := by
    simp_rw [sourceAngular_affine]
    exact hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hh := fourier_mode_trace_energy hq hη (m:=1) (by norm_num)
  simp only [add_zero,one_pow,one_mul] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on hη.le
  · exact (((hq.continuous_deriv (by simp)).pow 2).add
      (continuous_const.mul (hq.continuous.pow 2))).intervalIntegrable _ _
  · have hc : Continuous (fun a : ℝ => sourceAngularCollar (t+a) x) := by
      simp_rw [sourceAngular_affine]; fun_prop
    exact ((continuous_const.mul ((hf.continuous_fderiv (by simp)).comp hc |>.norm.pow 2)).add
      (continuous_const.mul (hq.continuous.pow 2))).intervalIntegrable _ _
  · intro a _
    rw [sourceAngular_normal_deriv hf]
    have hb := (fderiv ℝ f (sourceAngularCollar (t+a) x)).le_opNorm (sourceAngularVelocity x)
    have hb' := hb.trans (mul_le_mul_of_nonneg_left (sourceAngularVelocity_norm x) (norm_nonneg _))
    have hs := mul_self_le_mul_self (norm_nonneg _) hb'
    simp only [Real.norm_eq_abs,←pow_two,sq_abs] at hs
    nlinarith

lemma faceRayAngle_endpoints {w : ℝ} (hw : 0<w) :
    (∀ j : Fin 3,faceRayAngle w j.castSucc 1=faceRayAngle w j.succ (-1)) ∧
    faceRayAngle w 3 1=faceRayAngle w 0 (-1)+1 := by
  have hx := Real.arctan_inv_of_pos hw
  constructor
  · intro j
    fin_cases j <;> simp [faceRayAngle,one_div,neg_div,Real.arctan_neg,hx] <;> ring
  · simp [faceRayAngle,one_div,neg_div,Real.arctan_neg,hx]
    field_simp
    ring

lemma hasDerivAt_faceRayAngle (w : ℝ) (j : Fin 4) (b : ℝ) :
    HasDerivAt (faceRayAngle w j) (faceRayDensity w j b) b := by
  have h0 := ((Real.hasDerivAt_arctan (b/w)).comp b ((hasDerivAt_id b).div_const w)).div_const (2*Real.pi)
  have h1 := (((Real.hasDerivAt_arctan (w*b)).comp b ((hasDerivAt_id b).const_mul w)).const_add (Real.pi/2)).div_const (2*Real.pi)
  have h2 := (((Real.hasDerivAt_arctan (b/w)).comp b ((hasDerivAt_id b).div_const w)).const_add Real.pi).div_const (2*Real.pi)
  have h3 := (((Real.hasDerivAt_arctan (w*b)).comp b ((hasDerivAt_id b).const_mul w)).const_add (3*Real.pi/2)).div_const (2*Real.pi)
  unfold faceRayAngle faceRayDensity
  fin_cases j
  · simpa [faceRayAngle,faceRayDensity,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h0
  · simpa [faceRayAngle,faceRayDensity,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h1
  · simpa [faceRayAngle,faceRayDensity,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h2
  · simpa [faceRayAngle,faceRayDensity,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h3

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularIntegratedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma continuous_sourceAngular (t : ℝ) :
    Continuous (fun z : ℝ×UnitAddTorus (Fin 2) => sourceAngularCollar (t+z.1) z.2) := by
  simp_rw [sourceAngular_affine]
  exact ((continuous_sourceAngularCollar t).comp continuous_snd).add
    (continuous_fst.smul (continuous_sourceAngularVelocity.comp continuous_snd))

lemma sourcePhysicalEnergy_nonneg (f : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) :
    0≤ sourcePhysicalEnergy f y := by unfold sourcePhysicalEnergy; positivity

theorem sourceAngular_integrated_trace {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (t : ℝ) {η : ℝ} (hη : 0<η) :
    (∫ x : UnitAddTorus (Fin 2),(f (sourceAngularCollar t x))^2)≤
      (1+1/η)*(∫ a in (0:ℝ)..η,∫ x : UnitAddTorus (Fin 2),
        sourcePhysicalEnergy f (sourceAngularCollar (t+a) x)) := by
  apply integrate_torus_interval_bound (F:=fun x => (f (sourceAngularCollar t x))^2)
    (G:=fun a x => sourcePhysicalEnergy f (sourceAngularCollar (t+a) x))
    ((hf.continuous.comp (continuous_sourceAngularCollar t)).pow 2)
    ((continuous_sourcePhysicalEnergy hf).comp (continuous_sourceAngular t)) hη.le
  intro x
  exact sourceAngular_pointwise_trace hf t hη x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildCoordinateAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma sourceChildDerivative_norm : ‖sourceChildDerivative‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [sourceChildDerivative_apply,one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  have h0 := norm_le_pi_norm x (0 : Fin 3)
  have h1 := norm_le_pi_norm x (1 : Fin 3)
  have h2 := norm_le_pi_norm x (2 : Fin 3)
  simp only [Real.norm_eq_abs] at h0 h1 h2
  fin_cases i <;> simp only [Fin.isValue,
    Real.norm_eq_abs] <;> norm_num [sourceScale] <;> nlinarith [abs_nonneg (x 0),abs_nonneg (x 1),abs_nonneg (x 2)]

lemma sourceChild_energy {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (σ : ℝ) (x : Fin 3 → ℝ) :
    sourcePhysicalEnergy (f ∘ sourceChildCoordinates σ) x≤ sourcePhysicalEnergy f (sourceChildCoordinates σ x) := by
  have he := ((hf.differentiable (by simp) _).hasFDerivAt.comp x (sourceChildCoordinates_hasFDeriv σ x)).fderiv
  have hn := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ f (sourceChildCoordinates σ x)) sourceChildDerivative
  have hl := hn.trans (mul_le_of_le_one_right (norm_nonneg _) sourceChildDerivative_norm)
  have hs := mul_self_le_mul_self (norm_nonneg _) hl
  dsimp only [sourcePhysicalEnergy,Function.comp_apply]
  rw [he]
  nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularSignedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma sourceAngular_signed_deriv {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (t a σ : ℝ) (x : UnitAddTorus (Fin 2)) :
    deriv (fun s => f (sourceAngularCollar (t+σ*s) x)) a=
      fderiv ℝ f (sourceAngularCollar (t+σ*a) x) (σ • sourceAngularVelocity x) := by
  have hd := (((hf.differentiable (by simp) (sourceAngularCollar t x+(σ*a) • sourceAngularVelocity x)).hasFDerivAt).comp_hasDerivAt a
    ((((hasDerivAt_id a).const_mul σ).smul_const (sourceAngularVelocity x)).const_add (sourceAngularCollar t x))).deriv
  change deriv (fun s : ℝ => f (sourceAngularCollar t x+(σ*s) • sourceAngularVelocity x)) a=_ at hd
  simpa only [sourceAngular_affine,mul_one] using hd

lemma continuous_sourceAngular_signed (t σ : ℝ) :
    Continuous (fun z : ℝ×UnitAddTorus (Fin 2) => sourceAngularCollar (t+σ*z.1) z.2) := by
  simp_rw [sourceAngular_affine]
  exact ((continuous_sourceAngularCollar t).comp continuous_snd).add
    ((continuous_const.mul continuous_fst).smul (continuous_sourceAngularVelocity.comp continuous_snd))

lemma sourceAngular_signed_pointwise {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (t σ : ℝ) (hσ : |σ|≤1)
    {η : ℝ} (hη : 0<η) (x : UnitAddTorus (Fin 2)) :
    (f (sourceAngularCollar t x))^2≤(1+1/η)*(∫ a in (0:ℝ)..η,
      sourcePhysicalEnergy f (sourceAngularCollar (t+σ*a) x)) := by
  have hq : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun a : ℝ => f (sourceAngularCollar (t+σ*a) x)) := by
    simp_rw [sourceAngular_affine]
    exact hf.comp (contDiff_const.add ((contDiff_const.mul contDiff_id).smul contDiff_const))
  have hh := fourier_mode_trace_energy hq hη (m:=1) (by norm_num)
  simp only [mul_zero,add_zero,one_pow,one_mul] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on hη.le
  · exact (((hq.continuous_deriv (by simp)).pow 2).add
      (continuous_const.mul (hq.continuous.pow 2))).intervalIntegrable _ _
  · have hc : Continuous (fun a : ℝ => sourceAngularCollar (t+σ*a) x) := by
      simp_rw [sourceAngular_affine]; fun_prop
    exact ((continuous_sourcePhysicalEnergy hf).comp hc).intervalIntegrable _ _
  · intro a _
    rw [sourceAngular_signed_deriv hf]
    have hv : ‖σ • sourceAngularVelocity x‖≤8 := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul hσ (sourceAngularVelocity_norm x) (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    have hb := (fderiv ℝ f (sourceAngularCollar (t+σ*a) x)).le_opNorm (σ • sourceAngularVelocity x)
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
    have hs := mul_self_le_mul_self (norm_nonneg _) hb'
    simp only [Real.norm_eq_abs,←pow_two,sq_abs] at hs
    unfold sourcePhysicalEnergy
    nlinarith

theorem sourceAngular_signed_trace {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (t σ : ℝ) (hσ : |σ|≤1)
    {η : ℝ} (hη : 0<η) :
    (∫ x : UnitAddTorus (Fin 2),(f (sourceAngularCollar t x))^2)≤
      (1+1/η)*(∫ a in (0:ℝ)..η,∫ x : UnitAddTorus (Fin 2),
        sourcePhysicalEnergy f (sourceAngularCollar (t+σ*a) x)) := by
  apply integrate_torus_interval_bound (F:=fun x => (f (sourceAngularCollar t x))^2)
    (G:=fun a x => sourcePhysicalEnergy f (sourceAngularCollar (t+σ*a) x))
    ((hf.continuous.comp (continuous_sourceAngularCollar t)).pow 2)
    ((continuous_sourcePhysicalEnergy hf).comp (continuous_sourceAngular_signed t σ)) hη.le
  intro x
  exact sourceAngular_signed_pointwise hf t σ hσ hη x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_BoxIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma sourceExtendedBox_image (l r : ℝ) :
    threeArrow '' sourceExtendedBox l r=Icc l r ×ˢ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) := by
  ext z
  rw [MeasurableEquiv.image_eq_preimage_symm]
  simp [threeArrow_symm_apply,mem_sourceExtendedBox,abs_le,Prod.le_def]
  tauto

lemma integral_sourceExtendedBox {g : (Fin 3 → ℝ) → ℝ} (hg : Continuous g)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in sourceExtendedBox l r,g x)=
      ∫ t in l..r,∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,g ![t,a,b] := by
  have hc : Continuous (fun z : ℝ×(ℝ×ℝ) => g ![z.1,z.2.1,z.2.2]) := hg.comp (by fun_prop)
  have hi := hc.continuousOn.integrableOn_compact (μ:=volume)
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc) :
      IsCompact (Icc l r ×ˢ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)))
  have he := threeArrow_volume.setIntegral_image_emb threeArrow.measurableEmbedding
    (fun z : ℝ×(ℝ×ℝ) => g ![z.1,z.2.1,z.2.2]) (sourceExtendedBox l r)
  simp only [threeArrow_apply] at he
  have hid (x : Fin 3 → ℝ) : ![x 0,x 1,x 2]=x := by ext i; fin_cases i <;> rfl
  simp_rw [hid] at he
  have him := sourceExtendedBox_image l r
  simp only [threeArrow_apply] at him
  rw [←he,him]
  change (∫ y in Icc l r ×ˢ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1),
    g ![y.1,y.2.1,y.2.2] ∂volume.prod volume)=_
  rw [setIntegral_prod _ hi]
  simp_rw [intervalIntegral.integral_of_le hlr,
    intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1),←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  exact setIntegral_prod _ ((hc.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

theorem integral_circle_faces {w : ℝ} (hw : 0<w) {F : UnitAddCircle → ℝ}
    (hF : Continuous F) :
    (∫ θ,F θ ∂AddCircle.haarAddCircle)=
      ∑ j : Fin 4,∫ b in (-1:ℝ)..1,
        F ((faceRayAngle w j b:ℝ):UnitAddCircle)*faceRayDensity w j b := by
  have hc : Continuous (fun a : ℝ => F (a:UnitAddCircle)) :=
    hF.comp (AddCircle.continuous_mk' 1)
  have hh (j : Fin 4) :
      (∫ b in (-1:ℝ)..1,F ((faceRayAngle w j b:ℝ):UnitAddCircle)*faceRayDensity w j b)=
      ∫ a in faceRayAngle w j (-1)..faceRayAngle w j 1,F (a:UnitAddCircle) := by
    exact intervalIntegral.integral_comp_mul_deriv
      (fun b _ => hasDerivAt_faceRayAngle w j b) (continuous_faceRayDensity w j).continuousOn hc
  simp_rw [hh]
  have he := faceRayAngle_endpoints hw
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one,one_smul]
  rw [←AddCircle.intervalIntegral_preimage 1 (faceRayAngle w 0 (-1))]
  rw [Fin.sum_univ_four,←he.2]
  have h0 := he.1 (0:Fin 3)
  have h1 := he.1 (1:Fin 3)
  have h2 := he.1 (2:Fin 3)
  change faceRayAngle w 0 1=faceRayAngle w 1 (-1) at h0
  change faceRayAngle w 1 1=faceRayAngle w 2 (-1) at h1
  change faceRayAngle w 2 1=faceRayAngle w 3 (-1) at h2
  rw [←h0,←h1,←h2]
  rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusFaceIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma continuous_faceRayAngle (w : ℝ) (j : Fin 4) : Continuous (faceRayAngle w j) :=
  continuous_iff_continuousAt.mpr (fun b => (hasDerivAt_faceRayAngle w j b).continuousAt)

def torusFaceTerm (w₀ w₁ : ℝ) (F : UnitAddTorus (Fin 2) → ℝ)
    (j k : Fin 4) (a b : ℝ) : ℝ :=
  F ![((faceRayAngle w₀ j a:ℝ):UnitAddCircle),((faceRayAngle w₁ k b:ℝ):UnitAddCircle)]*
    faceRayDensity w₁ k b

lemma continuous_torusFaceTerm (w₀ w₁ : ℝ) {F : UnitAddTorus (Fin 2) → ℝ}
    (hF : Continuous F) (j k : Fin 4) :
    Continuous (Function.uncurry (torusFaceTerm w₀ w₁ F j k)) := by
  have h0 := (AddCircle.continuous_mk' 1).comp (continuous_faceRayAngle w₀ j)
  have h1 := (AddCircle.continuous_mk' 1).comp (continuous_faceRayAngle w₁ k)
  have hv : Continuous (fun p : ℝ×ℝ =>
      ![((faceRayAngle w₀ j p.1:ℝ):UnitAddCircle),((faceRayAngle w₁ k p.2:ℝ):UnitAddCircle)]) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact h0.comp continuous_fst
    · exact h1.comp continuous_snd
  exact (hF.comp hv).mul ((continuous_faceRayDensity w₁ k).comp continuous_snd)

theorem integral_unitTorus_faces {w₀ w₁ : ℝ} (hw₀ : 0<w₀) (hw₁ : 0<w₁)
    {F : UnitAddTorus (Fin 2) → ℝ} (hF : Continuous F) :
    (∫ x,F x)=∑ j : Fin 4,∑ k : Fin 4,∫ a in (-1:ℝ)..1,
      (∫ b in (-1:ℝ)..1,torusFaceTerm w₀ w₁ F j k a b)*faceRayDensity w₀ j a := by
  rw [integral_unitTorus_iterated hF,integral_circle_faces hw₀ (continuous_torus_partial_integral hF)]
  apply Finset.sum_congr rfl
  intro j _
  have hi (a : ℝ) := integral_circle_faces (w:=w₁) hw₁
    (F:=fun φ : UnitAddCircle => F ![((faceRayAngle w₀ j a:ℝ):UnitAddCircle),φ])
    (hF.comp (by fun_prop))
  simp_rw [hi,Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum (fun k _ =>
    ((continuous_parametric_unitInterval (continuous_torusFaceTerm w₀ w₁ hF j k)).mul
      (continuous_faceRayDensity w₀ j)).intervalIntegrable _ _)

lemma sourceAngularFace_continuous (t : ℝ) (i j : Fin 4) :
    Continuous (fun p : ℝ×ℝ => sourceCollarPiece i j ![t,p.1,p.2]) := by
  exact (sourceCollarPiece_contDiff i j).continuous.comp (by fun_prop)

theorem integral_sourceAngular_le {f : (Fin 3 → ℝ) → ℝ}
    (hf : Continuous f) (hn : ∀ z,0≤f z) (t : ℝ) :
    (∫ x : UnitAddTorus (Fin 2),f (sourceAngularCollar t x))≤
      ((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi))*
        ∑ i : Fin 4,∑ j : Fin 4,∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,
          f (sourceCollarPiece i j ![t,a,b]) := by
  have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hw' : sourceRadialWidth≤1 := by norm_num [sourceRadialWidth,sourceHole]
  let c₀ : ℝ := 1/(2*Real.pi)
  let c₁ : ℝ := (1/sourceRadialWidth)/(2*Real.pi)
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  change _≤ c₁*c₀*_
  rw [integral_unitTorus_faces (F:=fun x => f (sourceAngularCollar t x)) (w₀:=1) (w₁:=sourceRadialWidth) (by norm_num) hw
    (hf.comp (continuous_sourceAngularCollar t))]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact ((continuous_parametric_unitInterval
      (continuous_torusFaceTerm 1 sourceRadialWidth (hf.comp (continuous_sourceAngularCollar t)) i j)).mul
        (continuous_faceRayDensity 1 i)).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_parametric_unitInterval (f:=fun a b => f (sourceCollarPiece i j ![t,a,b]))
      (hf.comp (sourceAngularFace_continuous t i j)))).intervalIntegrable _ _
  · intro a ha
    have hinner : (∫ b in (-1:ℝ)..1,
        torusFaceTerm 1 sourceRadialWidth (fun x => f (sourceAngularCollar t x)) i j a b)≤
        c₁*(∫ b in (-1:ℝ)..1,f (sourceCollarPiece i j ![t,a,b])) := by
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact ((continuous_torusFaceTerm 1 sourceRadialWidth
          (hf.comp (continuous_sourceAngularCollar t)) i j).comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      · exact (continuous_const.mul ((hf.comp (sourceAngularFace_continuous t i j)).comp
          (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
      · intro b hb
        dsimp only [torusFaceTerm]
        rw [sourceAngular_face t a b i j (abs_le.mpr ha) (abs_le.mpr hb)]
        exact (mul_le_mul_of_nonneg_left (faceRayDensity_bounds hw hw' j b).2 (hn _)).trans_eq
          (mul_comm _ _)
    have hnint : 0≤ ∫ b in (-1:ℝ)..1,f (sourceCollarPiece i j ![t,a,b]) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => hn _)
    have hden := faceRayDensity_bounds (w:=1) (by norm_num) (by norm_num) i a
    have hden' : faceRayDensity 1 i a ≤ c₀ := by simpa [c₀] using hden.2
    calc
      _≤(c₁*(∫ b in (-1:ℝ)..1,f (sourceCollarPiece i j ![t,a,b])))*c₀ :=
        mul_le_mul hinner hden' hden.1 (mul_nonneg hc₁ hnint)
      _=_ := by ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CollarVolumeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

theorem sourceExtended_integral_bound {g : (Fin 3 → ℝ) → ℝ}
    (hg : Continuous g) (hn : ∀ y,0≤g y) (i j : Fin 4) {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    (∫ x in sourceExtendedBox l r,g (sourceCollarPiece i j x))≤
      100*(∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y) := by
  rw [sourceExtended_integral i j hl hr,←integral_const_mul]
  apply setIntegral_mono_on
  · exact (hg.comp (sourceCollarPiece_contDiff i j).continuous).continuousOn.integrableOn_compact isCompact_Icc
  · have hc : Continuous (fun x : Fin 3 → ℝ => abs ((sourceCollarDerivative i j x).det)) := by
      simp_rw [sourceCollarDerivative_det]
      unfold sourceCollarRadius squareFace
      fun_prop
    exact (continuous_const.mul (hc.mul (hg.comp (sourceCollarPiece_contDiff i j).continuous))).continuousOn.integrableOn_compact isCompact_Icc
  · exact measurableSet_Icc
  · intro x hx
    have hh := sourceExtended_jacobian_lower i j hl hr hx
    change g (sourceCollarPiece i j x)≤100*(abs ((sourceCollarDerivative i j x).det)*g (sourceCollarPiece i j x))
    nlinarith [mul_nonneg (hn (sourceCollarPiece i j x)) (show 0≤abs ((sourceCollarDerivative i j x).det)-1/100 by linarith)]

lemma continuous_collarFace_integral {g : (Fin 3 → ℝ) → ℝ} (hg : Continuous g) (i j : Fin 4) :
    Continuous (fun t : ℝ => ∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,g (sourceCollarPiece i j ![t,a,b])) := by
  apply continuous_parametric_unitInterval (f:=fun t a => ∫ b in (-1:ℝ)..1,g (sourceCollarPiece i j ![t,a,b]))
  apply continuous_parametric_unitInterval (f:=fun p : ℝ×ℝ => fun b => g (sourceCollarPiece i j ![p.1,p.2,b]))
  exact hg.comp ((sourceCollarPiece_contDiff i j).continuous.comp (by fun_prop))

theorem sourceAngular_volume_bound {g : (Fin 3 → ℝ) → ℝ}
    (hg : Continuous g) (hn : ∀ y,0≤g y) {l r : ℝ}
    (hlr : l ≤ r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    (∫ t in l..r,∫ x : UnitAddTorus (Fin 2),g (sourceAngularCollar t x))≤
      (100*((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi)))*
        ∑ i : Fin 4,∑ j : Fin 4,∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y := by
  let c : ℝ := ((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi))
  have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcont : Continuous (fun t : ℝ => ∫ x : UnitAddTorus (Fin 2),g (sourceAngularCollar t x)) := by
    have hcs : Continuous (fun p : ℝ×UnitAddTorus (Fin 2) => sourceAngularCollar p.1 p.2) := by
      simpa only [zero_add] using continuous_sourceAngular 0
    have hh := continuous_parametric_integral_of_continuous (μ:=volume)
      (f:=fun t (x : UnitAddTorus (Fin 2)) => g (sourceAngularCollar t x))
      (hg.comp hcs) (s:=univ) isCompact_univ
    simpa using hh
  have hsum : Continuous (fun t : ℝ => ∑ i : Fin 4,∑ j : Fin 4,
      ∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,g (sourceCollarPiece i j ![t,a,b])) :=
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => continuous_collarFace_integral hg i j))
  calc
    _≤∫ t in l..r,c*(∑ i : Fin 4,∑ j : Fin 4,
        ∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,g (sourceCollarPiece i j ![t,a,b])) :=
      intervalIntegral.integral_mono_on hlr (hcont.intervalIntegrable l r)
        ((continuous_const.mul hsum).intervalIntegrable l r) (fun t _ => integral_sourceAngular_le hg hn t)
    _=c*(∑ i : Fin 4,∑ j : Fin 4,∫ x in sourceExtendedBox l r,g (sourceCollarPiece i j x)) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_finsetSum (fun i _ =>
        (continuous_finsetSum _ (fun j _ => continuous_collarFace_integral hg i j)).intervalIntegrable l r)]
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_finsetSum (fun j _ => (continuous_collarFace_integral hg i j).intervalIntegrable l r)]
      apply Finset.sum_congr rfl
      intro j _
      exact (integral_sourceExtendedBox (hg.comp (sourceCollarPiece_contDiff i j).continuous) hlr).symm
    _ ≤ c*(∑ i : Fin 4,∑ j : Fin 4,100*(∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y)) := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact sourceExtended_integral_bound hg hn i j hl hr
    _=_ := by simp_rw [←Finset.mul_sum]; dsimp [c]; ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus

lemma sourceAngular_volume_in {g : (Fin 3 → ℝ) → ℝ}
    (hg : Continuous g) (hn : ∀ y,0≤g y) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    {l r : ℝ} (hlr : l ≤ r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hsub : ∀ i j,sourceCollarPiece i j '' sourceExtendedBox l r⊆K) :
    (∫ t in l..r,∫ x : UnitAddTorus (Fin 2),g (sourceAngularCollar t x))≤
      physicalRayConstant*(∫ y in K,g y) := by
  have hh := sourceAngular_volume_bound hg hn hlr hl hr
  have hc : 0≤100*((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi)) := by
    have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
    positivity
  have hi : IntegrableOn g K := hg.continuousOn.integrableOn_compact hK
  have hm := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => Finset.sum_le_sum (s:=Finset.univ)
    (fun j _ => setIntegral_mono_set hi (Filter.Eventually.of_forall hn) (Filter.Eventually.of_forall (hsub i j))))
  have hsum : (∑ i : Fin 4,∑ j : Fin 4,∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y)≤
      16*(∫ y in K,g y) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hm
    change (∑ i : Fin 4,∑ j : Fin 4,∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y)≤
      4*(4*(∫ y in K,g y)) at hm
    linarith
  apply hh.trans
  calc
    _≤(100*((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi)))*(16*(∫ y in K,g y)) :=
      mul_le_mul_of_nonneg_left hsum hc
    _=_ := by unfold physicalRayConstant; ring

theorem sourceAngular_physical_trace_forward {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (t : ℝ) {η : ℝ} (hη : 0<η) (hl : -(1:ℝ)/100≤t) (hr : t+η≤1/100)
    (hsub : ∀ i j,sourceCollarPiece i j '' sourceExtendedBox t (t+η)⊆K) :
    (∫ x : UnitAddTorus (Fin 2),(f (sourceAngularCollar t x))^2)≤
      ((1+1/η)*physicalRayConstant)*(∫ y in K,sourcePhysicalEnergy f y) := by
  have ht := sourceAngular_integrated_trace hf t hη
  have he := intervalIntegral.integral_comp_add_left
    (fun a => ∫ x : UnitAddTorus (Fin 2),sourcePhysicalEnergy f (sourceAngularCollar a x))
    (a:=0) (b:=η) t
  rw [he,add_zero] at ht
  have hv := sourceAngular_volume_in (continuous_sourcePhysicalEnergy hf)
    (sourcePhysicalEnergy_nonneg f) hK (by linarith : t≤t+η) hl hr hsub
  exact ht.trans (by have hh := mul_le_mul_of_nonneg_left hv (show 0≤1+1/η by positivity); nlinarith [hh])

theorem sourceAngular_physical_trace_backward {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (t : ℝ) {η : ℝ} (hη : 0<η) (hl : -(1:ℝ)/100≤t-η) (hr : t≤1/100)
    (hsub : ∀ i j,sourceCollarPiece i j '' sourceExtendedBox (t-η) t⊆K) :
    (∫ x : UnitAddTorus (Fin 2),(f (sourceAngularCollar t x))^2)≤
      ((1+1/η)*physicalRayConstant)*(∫ y in K,sourcePhysicalEnergy f y) := by
  have ht := sourceAngular_signed_trace hf t (-1) (by norm_num) hη
  simp only [neg_one_mul,←sub_eq_add_neg] at ht
  have he := intervalIntegral.integral_comp_sub_left
    (fun a => ∫ x : UnitAddTorus (Fin 2),sourcePhysicalEnergy f (sourceAngularCollar a x))
    (a:=0) (b:=η) t
  rw [he,sub_zero] at ht
  have hv := sourceAngular_volume_in (continuous_sourcePhysicalEnergy hf)
    (sourcePhysicalEnergy_nonneg f) hK (by linarith : t-η≤t) hl hr hsub
  exact ht.trans (by have hh := mul_le_mul_of_nonneg_left hv (show 0≤1+1/η by positivity); nlinarith [hh])

end

open Set MeasureTheory

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPoincare
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

open Set MeasureTheory
open scoped ENNReal

abbrev CentralGradients := PiLp 2 (fun _ : Fin 3 => CentralL2)

def centralJetD : CentralJets →L[ℝ] CentralGradients :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => CentralL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 3 => PiLp.proj 2 (fun _ : Fin 4 => CentralL2) i.succ))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralVariational
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

def spectralGraphWeight {ι : Type*} (w : ι → ℝ) :
    spectralTraceGraph w →L[ℝ] SpectralL2 ι :=
  ((PiLp.proj 2 (fun _ : Fin 2 => SpectralL2 ι) 1).comp
    (spectralTraceGraph w).subtypeL).restrictScalars ℝ

def spectralGraphMean {ι : Type*} [Zero ι] (w : ι → ℝ) :
    spectralTraceGraph w →L[ℝ] ℝ :=
  Complex.reCLM.comp (((lp.evalCLM ℂ (fun _ : ι => ℂ) 2 0).comp
    ((PiLp.proj 2 (fun _ : Fin 2 => SpectralL2 ι) 0).comp
      (spectralTraceGraph w).subtypeL)).restrictScalars ℝ)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndPoissonJets
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

def endModeCoefficient (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) : Fin 4 → ℂ :=
  ![a,-(torusRate s h:ℂ)*a,Complex.I*(h 0:ℂ)*a,Complex.I*(h 1:ℂ)*a]

end

open Set MeasureTheory Filter Topology
open scoped ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndPoissonRepresentative
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

def endPoissonModeField (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) (j : Fin 4)
    (z : ℝ × UnitAddTorus (Fin 2)) : ℂ :=
  (Real.exp (-torusRate s h*z.1):ℂ)*endModeCoefficient s h a j*mFourier h z.2

def endPoissonField (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s)) (j : Fin 4)
    (z : ℝ × UnitAddTorus (Fin 2)) : ℂ :=
  ∑' h,endPoissonModeField s h (f.val 0 h) j z

end

open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusPoissonContinuous
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance torusPoissonContinuousMeasureSpace_r19559c_1 : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
def torusPoissonContinuous (s : Fin 3 → ℝ) (t : ℝ) (f : TorusL2) :
    C(UnitAddTorus (Fin 2),ℂ) :=
  ∑' h, ((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h) • mFourier h

end

open MeasureTheory Filter Topology UnitAddTorus Real Set
open scoped ENNReal

local instance torusAnglesMeasureSpace_r19559c_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
def torusRealContinuation (s : Fin 3 → ℝ) (f : TorusL2) (x : Fin 3 → ℝ) : ℝ :=
  (torusPoissonContinuous s (x 0) f (torusAngles x)).re

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CylinderSobolevGraph
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

abbrev CylinderTraceAmbient (s : Fin 3 → ℝ) (R : ℝ) :=
  FiniteCylinderJets R × (spectralTraceGraph (torusRate s) × spectralTraceGraph (torusRate s))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CollarCartesianDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped Matrix.Norms.Elementwise

def sourceFaceAngleMatrix (i j : Fin 4) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![1,2*Real.pi*faceRayDensity 1 i (x 1),
    2*Real.pi*faceRayDensity sourceRadialWidth j (x 2)]

lemma sourceFaceAngles_hasFDeriv (i j : Fin 4) (x : Fin 3 → ℝ) :
    HasFDerivAt (sourceFaceAngles i j)
      (Matrix.toLin' (sourceFaceAngleMatrix i j x)).toContinuousLinearMap x := by
  have h1 := ((hasDerivAt_faceRayAngle 1 i (x 1)).comp_hasFDerivAt x
    (hasFDerivAt_apply (𝕜:=ℝ) 1 x)).const_mul (2*Real.pi)
  have h2 := ((hasDerivAt_faceRayAngle sourceRadialWidth j (x 2)).comp_hasFDerivAt x
    (hasFDerivAt_apply (𝕜:=ℝ) 2 x)).const_mul (2*Real.pi)
  have hcoord (k : Fin 3) : HasFDerivAt (fun y => sourceFaceAngles i j y k)
      ((ContinuousLinearMap.proj k : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
        (Matrix.toLin' (sourceFaceAngleMatrix i j x)).toContinuousLinearMap) x := by
    fin_cases k
    · convert! hasFDerivAt_apply (𝕜:=ℝ) (0:Fin 3) x using 1
      all_goals try with_reducible_and_instances rfl
      ext v
      simp [sourceFaceAngleMatrix,Matrix.toLin'_apply,Matrix.mulVec_diagonal]
    · convert! h1 using 1
      all_goals try with_reducible_and_instances rfl
      ext v
      simp [sourceFaceAngleMatrix,Matrix.toLin'_apply,Matrix.mulVec_diagonal]
      ring
    · convert! h2 using 1
      all_goals try with_reducible_and_instances rfl
      ext v
      simp [sourceFaceAngleMatrix,Matrix.toLin'_apply,Matrix.mulVec_diagonal]
      ring
  convert! hasFDerivAt_pi.mpr hcoord using 1
  all_goals try with_reducible_and_instances rfl

lemma continuous_sourceCollarJacobian (i j : Fin 4) : Continuous (sourceCollarJacobian i j) := by
  unfold sourceCollarJacobian sourceCollarRadius squareFace
  fun_prop

lemma continuous_sourceFaceAngleMatrix (i j : Fin 4) : Continuous (sourceFaceAngleMatrix i j) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  by_cases hab : a=b
  · subst b
    fin_cases a <;> simp only [sourceFaceAngleMatrix,Matrix.diagonal_apply_eq]
    · exact continuous_const
    · exact continuous_const.mul ((continuous_faceRayDensity 1 i).comp (continuous_apply 1))
    · exact continuous_const.mul ((continuous_faceRayDensity sourceRadialWidth j).comp (continuous_apply 2))
  · simp only [sourceFaceAngleMatrix,Matrix.diagonal_apply_ne _ hab]
    exact continuous_const

lemma sourceCollarJacobian_extended_ne_zero (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    (sourceCollarJacobian i j x).det≠0 := by
  have h := sourceExtended_jacobian_lower i j (le_refl _) (le_refl _) hx
  rw [sourceCollarDerivative_det,←sourceCollarJacobian_det] at h
  exact abs_pos.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/100) h)

def sourceCartesianGradientMatrix (i j : Fin 4) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (sourceCollarJacobian i j x)ᵀ⁻¹*sourceFaceAngleMatrix i j x

lemma continuousOn_sourceCartesianGradientMatrix (i j : Fin 4) :
    ContinuousOn (sourceCartesianGradientMatrix i j)
      (sourceExtendedBox (-(1:ℝ)/100) (1/100)) := by
  intro x hx
  have hi : ContinuousAt (fun x => (sourceCollarJacobian i j x)ᵀ⁻¹) x :=
    (continuousAt_matrix_inv _ (by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (by
        rw [Matrix.det_transpose]
        exact sourceCollarJacobian_extended_ne_zero i j hx))).comp
          (continuous_sourceCollarJacobian i j).matrix_transpose.continuousAt
  exact (hi.mul (continuous_sourceFaceAngleMatrix i j).continuousAt).continuousWithinAt

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralEnergySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory
open scoped ENNReal

def centralAmbientD (s : Fin 3 → ℝ) : CentralAmbient s →L[ℝ] CentralGradients :=
  centralJetD.comp (WithLp.fstL 2 ℝ CentralJets (CentralTraceFields s))

def centralAmbientT (s : Fin 3 → ℝ) (i : Fin 3) :
    CentralAmbient s →L[ℝ] spectralTraceGraph (torusRate s) :=
  (PiLp.proj 2 (fun _ : Fin 3 => spectralTraceGraph (torusRate s)) i).comp
    (WithLp.sndL 2 ℝ CentralJets (CentralTraceFields s))

def centralAmbientM (s : Fin 3 → ℝ) : CentralAmbient s →L[ℝ] ℝ :=
  (spectralGraphMean (torusRate s)).comp (centralAmbientT s 0)

def centralD (s : Fin 3 → ℝ) : centralEnergySpace s →L[ℝ] CentralGradients :=
  (centralAmbientD s).comp (centralEnergySpace s).subtypeL

def centralT (s : Fin 3 → ℝ) (i : Fin 3) :
    centralEnergySpace s →L[ℝ] spectralTraceGraph (torusRate s) :=
  (centralAmbientT s i).comp (centralEnergySpace s).subtypeL

def centralM (s : Fin 3 → ℝ) : centralEnergySpace s →L[ℝ] ℝ :=
  (centralAmbientM s).comp (centralEnergySpace s).subtypeL

end

open Set MeasureTheory

def centralAmbientJ (s : Fin 3 → ℝ) : CentralAmbient s →L[ℝ] CentralJets :=
  WithLp.fstL 2 ℝ CentralJets (CentralTraceFields s)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralUnnormalizedVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma angularArea_ge_one : 1≤angularArea := by
  have hp := Real.pi_gt_three
  dsimp only [angularArea]
  nlinarith [sq_nonneg (Real.pi-3)]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CentralDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def centralAmbientComponent (s : Fin 3 → ℝ) (i : Fin 4) :
    CentralAmbient s →L[ℝ] CentralL2 :=
  (PiLp.proj 2 (fun _ : Fin 4 => CentralL2) i).comp (centralAmbientJ s)

def CentralVariationalEquation (s slopes : Fin 3 → ℝ) (p : centralEnergySpace s) : Prop :=
  ∀ v : centralEnergySpace s,
    inner ℝ (centralD s p) (centralD s v)+
      angularArea*(∑ i : Fin 3,inner ℝ (spectralGraphWeight (torusRate s) (centralT s i p))
        (spectralGraphWeight (torusRate s) (centralT s i v)))=
      angularArea*(∑ i : Fin 3,slopes i*spectralGraphMean (torusRate s) (centralT s i v))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_SobolevSmoothTests
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

lemma smoothH1_mem_H10 (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (hs : tsupport f⊆ball) : smoothH1 f hf∈H10 :=
  (Submodule.le_topologicalClosure _) (Submodule.subset_span
    ⟨f,hf,hc,hs,smoothJet_memLp hf,rfl⟩)

open Set MeasureTheory Filter Topology Real

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ParentLocalizedJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : a<0)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

def physicalFourJetCLM : (Fin 4 → Lp ℝ 2 (volume : Measure (Fin 3 → ℝ))) →L[ℝ] JetSpace :=
  (lpRestrictionCLM ball).comp
    (((Lp.compMeasurePreservingₗᵢ ℝ ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph.toMeasurableEquiv)
      (PiLp.volume_preserving_ofLp (Fin 3))).toContinuousLinearMap).comp (lpFourJetCLM volume))

lemma physicalFourJetCLM_ae (f : Fin 4 → Lp ℝ 2 (volume : Measure (Fin 3 → ℝ))) :
    physicalFourJetCLM f=ᵐ[ballMeasure] (fun x => WithLp.toLp 2 (fun i => f i (WithLp.ofLp x))) := by
  apply (lpRestrictionCLM_ae ball _).trans
  apply ae_restrict_of_ae
  apply (Lp.coeFn_compMeasurePreserving _ (PiLp.volume_preserving_ofLp (Fin 3))).trans
  exact (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp (lpFourJetCLM_ae volume f)

end

open Set MeasureTheory Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ParentCompletionJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) {c : ℝ≥0∞}
  (hc : c≠∞) (hmap : Measure.map e μ ≤ c • ν)

lemma sourceChildCoordinates_translate (σ : ℝ) :
    sourceChildCoordinates σ=(fun y : Fin 3 → ℝ => y+![σ*sourceOffset,0,0]) ∘ sourceChildDerivative := by
  funext y
  rw [Function.comp_apply,sourceChildDerivative_apply]
  ext i
  fin_cases i <;> simp [sourceChildCoordinates]

lemma sourceChildCoordinates_map_volume (σ : ℝ) :
    Measure.map (sourceChildCoordinates σ) volume=ENNReal.ofReal ((sourceScale^3)⁻¹) • volume := by
  have hd : sourceChildDerivative.det≠0 := by rw [sourceChildDerivative_det]; norm_num [sourceScale]
  rw [sourceChildCoordinates_translate]
  rw [←Measure.map_map (g:=fun y : Fin 3 → ℝ => y+![σ*sourceOffset,0,0])
    (f:=sourceChildDerivative) (continuous_id.add continuous_const).measurable sourceChildDerivative.continuous.measurable]
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin 3 → ℝ)) hd
  change Measure.map sourceChildDerivative volume=ENNReal.ofReal |sourceChildDerivative.det⁻¹| • volume at hm
  rw [hm,Measure.map_smul,
    (measurePreserving_add_right volume ![σ*sourceOffset,0,0]).map_eq]
  congr 2
  rw [sourceChildDerivative_det,inv_neg,abs_neg,abs_of_nonneg]
  exact inv_nonneg.mpr (by norm_num [sourceScale])

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPhysicalRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceCollarTime_ge_iff (y : Fin 3 → ℝ) (b : ℝ) :
    b ≤ sourceCollarTime y ↔
      |y 2| ≤ 1-b ∧ sourceHole+sourceRadialWidth*b ≤ sourceRadial y ∧
        sourceRadial y ≤ 1-sourceRadialWidth*b := by
  have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hd : sourceRadialCenter-sourceRadialWidth=sourceHole := by
    norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole]
  have hd' : sourceRadialCenter+sourceRadialWidth=1 := by
    norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole]
  simp only [sourceCollarTime,sourceCrossCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [le_sub_iff_add_le,←le_sub_iff_add_le',max_le_iff,abs_le]
  constructor
  · rintro ⟨⟨hl,hr⟩,hz⟩
    refine ⟨hz,?_,?_⟩
    · have h := (le_div_iff₀ hw).mp hl
      nlinarith
    · have h := (div_le_iff₀ hw).mp hr
      nlinarith
  · rintro ⟨hz,hl,hr⟩
    refine ⟨⟨(le_div_iff₀ hw).mpr ?_,(div_le_iff₀ hw).mpr ?_⟩,hz⟩ <;> nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

lemma sourceChildInverse_map_volume (σ : ℝ) :
    Measure.map (sourceChildHomeomorph σ).symm volume=ENNReal.ofReal (sourceScale^3) • volume := by
  apply (sourceChildHomeomorph σ).toMeasurableEquiv.measurableEmbedding.map_injective
  change Measure.map (sourceChildHomeomorph σ) (Measure.map (sourceChildHomeomorph σ).symm volume)=
    Measure.map (sourceChildHomeomorph σ) (ENNReal.ofReal (sourceScale^3) • volume)
  rw [Measure.map_map (sourceChildHomeomorph σ).measurable (sourceChildHomeomorph σ).symm.measurable]
  have he : (sourceChildHomeomorph σ) ∘ (sourceChildHomeomorph σ).symm=id :=
    funext (sourceChildHomeomorph σ).apply_symm_apply
  rw [he,Measure.map_id,Measure.map_smul]
  change volume=ENNReal.ofReal (sourceScale^3) • Measure.map (sourceChildCoordinates σ) volume
  rw [sourceChildCoordinates_map_volume,smul_smul,←ENNReal.ofReal_mul (by norm_num [sourceScale])]
  norm_num [sourceScale]

lemma sourceChildInverse_quasi (σ : ℝ) :
    Measure.QuasiMeasurePreserving (sourceChildHomeomorph σ).symm volume volume := by
  refine ⟨(sourceChildHomeomorph σ).symm.measurable,?_⟩
  rw [sourceChildInverse_map_volume]
  exact Measure.smul_absolutelyContinuous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sourceChildPushforwardCLM (σ : ℝ) : Lp E 2 (volume : Measure (Fin 3 → ℝ)) →L[ℝ]
    Lp E 2 (volume : Measure (Fin 3 → ℝ)) :=
  lpBoundedPullbackCLM (sourceChildHomeomorph σ).symm.toMeasurableEquiv ENNReal.ofReal_ne_top
    (le_of_eq (sourceChildInverse_map_volume σ))

lemma sourceChildPushforwardCLM_ae (σ : ℝ) (f : Lp E 2 (volume : Measure (Fin 3 → ℝ))) :
    sourceChildPushforwardCLM σ f=ᵐ[volume] (fun y => f ((sourceChildHomeomorph σ).symm y)) :=
  lpBoundedPullbackCLM_ae _ _ _ f

lemma sourceChildInverse_contDiff (σ : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) ((sourceChildHomeomorph σ).symm : (Fin 3 → ℝ) → (Fin 3 → ℝ)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [sourceChildHomeomorph]
  all_goals fun_prop

def sourceChildInverseDerivative : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (sourceScale^2)⁻¹ • sourceChildDerivative

lemma sourceChildInverseDerivative_apply (y : Fin 3 → ℝ) :
    sourceChildInverseDerivative y=![y 1/sourceScale,y 0/sourceScale,y 2/sourceScale] := by
  rw [sourceChildInverseDerivative,smul_apply,sourceChildDerivative_apply]
  ext i
  fin_cases i <;> norm_num [sourceScale] <;> ring

lemma sourceChildInverse_hasFDeriv (σ : ℝ) (y : Fin 3 → ℝ) :
    HasFDerivAt ((sourceChildHomeomorph σ).symm : (Fin 3 → ℝ) → (Fin 3 → ℝ)) sourceChildInverseDerivative y := by
  have he : ((sourceChildHomeomorph σ).symm : (Fin 3 → ℝ) → (Fin 3 → ℝ))=
      fun y => sourceChildInverseDerivative y+![0,-σ*sourceOffset/sourceScale,0] := by
    funext y
    rw [sourceChildInverseDerivative_apply]
    ext i
    fin_cases i <;> simp [sourceChildHomeomorph]; ring
  rw [he]
  exact sourceChildInverseDerivative.hasFDerivAt.add_const _

lemma sourceChildInverse_single (i : Fin 3) :
    sourceChildInverseDerivative (Pi.single i 1)=sourceScale⁻¹ • Pi.single (childAxis i) 1 := by
  rw [sourceChildInverseDerivative_apply]
  fin_cases i <;> ext j <;> fin_cases j <;> norm_num [childAxis,Pi.single_apply,Fin.ext_iff,sourceScale]

end

open Set MeasureTheory Filter Topology

lemma sourceChildEuclidean_symm_contDiff (σ : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) ((sourceChildEuclidean σ).symm : R3 → R3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp
    ((sourceChildInverse_contDiff σ).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff)

lemma sourceChildEuclidean_comp_support (k : Fin 2) {f : R3 → ℝ}
    (hs : tsupport f⊆ball) :
    tsupport (f ∘ (sourceChildEuclidean (actualChildSign k)).symm)⊆ball := by
  intro x hx
  have hy := tsupport_comp_subset_preimage f (sourceChildEuclidean (actualChildSign k)).symm.continuous hx
  have him : x∈sourceChildEuclidean (actualChildSign k) '' ball :=
    ⟨(sourceChildEuclidean (actualChildSign k)).symm x,hs hy,(sourceChildEuclidean (actualChildSign k)).apply_symm_apply x⟩
  exact sourceChildEuclidean_ball k him

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WholeBallJet
attribute [-instance] _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def ballWholePiComponentCLM (i : Fin 4) : JetSpace →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  ((EuclideanSpace.proj i).compLpL 2 volume).comp ballWholePiJetCLM

lemma ballWholePiJetCLM_smooth_ae (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hs : tsupport f⊆ball) :
    ballWholePiJetCLM (smoothH1 f hf).val=ᵐ[volume]
      (fun y => smoothJet f (WithLp.toLp 2 y)) := by
  have he := lpZeroExtensionCLM_ae_of_ae (D:=ball) Metric.isOpen_ball.measurableSet
    (smoothH1 f hf).val (smoothJet_memLp hf).coeFn_toLp
  have he' : lpZeroExtensionCLM (D:=ball) Metric.isOpen_ball.measurableSet (smoothH1 f hf).val=ᵐ[volume] smoothJet f := by
    filter_upwards [he] with x hx
    rw [hx]
    by_cases hb : x∈ball
    · exact indicator_of_mem hb _
    · rw [indicator_of_notMem hb]
      exact (smoothJet_zero_of_notMem_support (fun h => hb (hs h))).symm
  apply (Lp.coeFn_compMeasurePreserving _ (PiLp.volume_preserving_toLp (Fin 3))).trans
  exact (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp he'

lemma ballWholePiComponentCLM_ae (i : Fin 4) (z : JetSpace) :
    ballWholePiComponentCLM i z=ᵐ[volume] (fun y => ballWholePiJetCLM z y i) := by
  simp only [ballWholePiComponentCLM,ContinuousLinearMap.comp_apply]
  have he := (EuclideanSpace.proj (𝕜:=ℝ) i).coeFn_compLpL (p:=2)
    (μ:=(volume : Measure (Fin 3 → ℝ))) (ballWholePiJetCLM z)
  simpa only [EuclideanSpace.proj,PiLp.proj_apply] using he

lemma ballWholePiComponentCLM_smooth_ae (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hs : tsupport f⊆ball) (i : Fin 4) :
    ballWholePiComponentCLM i (smoothH1 f hf).val=ᵐ[volume]
      (fun y => smoothJet f (WithLp.toLp 2 y) i) := by
  filter_upwards [ballWholePiComponentCLM_ae i (smoothH1 f hf).val,
    ballWholePiJetCLM_smooth_ae f hf hs] with y hx hy
  rw [hx,hy]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ChildH10Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

lemma sourceChildEuclidean_symm_gradient (σ : ℝ) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (x : R3) (i : Fin 3) :
    gradient (f ∘ (sourceChildEuclidean σ).symm) x i=
      sourceScale⁻¹*gradient f ((sourceChildEuclidean σ).symm x) (childAxis i) := by
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hD := E.symm.hasFDerivAt.comp (E x) (sourceChildInverse_hasFDeriv σ (E x))
  have hC := (hf.differentiable (by simp) ((sourceChildEuclidean σ).symm x)).hasFDerivAt.comp x
    (hD.comp x E.hasFDerivAt)
  have hi : E.toContinuousLinearMap (EuclideanSpace.single i 1)=Pi.single i 1 := rfl
  have hj : E.symm.toContinuousLinearMap (Pi.single (childAxis i) 1)=EuclideanSpace.single (childAxis i) 1 := rfl
  rw [gradient_apply_single,gradient_apply_single]
  rw [hC.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,hi,sourceChildInverse_single,map_smul,hj,map_smul,smul_eq_mul]

def childTransportComponentCLM (k : Fin 2) (i : Fin 4) : JetSpace →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  Fin.cases ((sourceChildPushforwardCLM (actualChildSign k)).comp (ballWholePiComponentCLM 0))
    (fun j => sourceScale⁻¹ • ((sourceChildPushforwardCLM (actualChildSign k)).comp
      (ballWholePiComponentCLM (childAxis j).succ))) i

def childTransportJetCLM (k : Fin 2) : JetSpace →L[ℝ] JetSpace :=
  physicalFourJetCLM.comp (ContinuousLinearMap.pi (childTransportComponentCLM k))

lemma childTransportComponentCLM_smooth_ae (k : Fin 2) (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hs : tsupport f⊆ball) (i : Fin 4) :
    childTransportComponentCLM k i (smoothH1 f hf).val=ᵐ[volume]
      (fun y => smoothJet (f ∘ (sourceChildEuclidean (actualChildSign k)).symm) (WithLp.toLp 2 y) i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change sourceChildPushforwardCLM (actualChildSign k) (ballWholePiComponentCLM 0 (smoothH1 f hf).val)=ᵐ[volume] _
    apply (sourceChildPushforwardCLM_ae _ _).trans
    apply ((sourceChildInverse_quasi _).ae_eq_comp (ballWholePiComponentCLM_smooth_ae f hf hs 0)).trans
    exact Filter.Eventually.of_forall (fun y => rfl)
  · simp only [childTransportComponentCLM,Fin.cases_succ,smul_apply,
      ContinuousLinearMap.comp_apply]
    apply (Lp.coeFn_smul _ _).trans
    have he := (sourceChildPushforwardCLM_ae (actualChildSign k)
      (ballWholePiComponentCLM (childAxis j).succ (smoothH1 f hf).val)).trans
      ((sourceChildInverse_quasi _).ae_eq_comp (ballWholePiComponentCLM_smooth_ae f hf hs (childAxis j).succ))
    filter_upwards [he] with y hy
    simp only [Pi.smul_apply,smul_eq_mul,hy,smoothJet,Fin.cases_succ,WithLp.ofLp_toLp]
    exact (sourceChildEuclidean_symm_gradient (actualChildSign k) hf (WithLp.toLp 2 y) j).symm

lemma childTransportJetCLM_smooth (k : Fin 2) (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hs : tsupport f⊆ball) :
    childTransportJetCLM k (smoothH1 f hf).val=
      (smoothH1 (f ∘ (sourceChildEuclidean (actualChildSign k)).symm)
        (hf.comp (sourceChildEuclidean_symm_contDiff _))).val := by
  apply Lp.ext
  have he (i : Fin 4) := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
      (childTransportComponentCLM_smooth_ae k f hf hs i))
  filter_upwards [physicalFourJetCLM_ae (fun i => childTransportComponentCLM k i (smoothH1 f hf).val),
    ae_all_iff.mpr he,(smoothJet_memLp (hf.comp (sourceChildEuclidean_symm_contDiff (actualChildSign k)))).coeFn_toLp] with x hx hi hf'
  change physicalFourJetCLM (fun i => childTransportComponentCLM k i (smoothH1 f hf).val) x=_
  change (smoothH1 (f ∘ (sourceChildEuclidean (actualChildSign k)).symm)
    (hf.comp (sourceChildEuclidean_symm_contDiff _))).val x=_ at hf'
  rw [hx,hf']
  ext i
  exact hi i

lemma childTransportJetCLM_H10 (k : Fin 2) {z : JetSpace} (hz : z∈zeroTraceAmbient) :
    childTransportJetCLM k z∈zeroTraceAmbient := by
  let T := zeroTraceAmbient.comap (childTransportJetCLM k).toLinearMap
  have ht : IsClosed (T : Set JetSpace) :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ compactSmoothJets)).preimage
      (childTransportJetCLM k).continuous
  have hs : Submodule.span ℝ compactSmoothJets≤T := by
    apply Submodule.span_le.mpr
    rintro z ⟨f,hf,hc,hs,hL,rfl⟩
    have he : hL.toLp (smoothJet f)=(smoothH1 f hf).val := by apply Lp.ext; exact hL.coeFn_toLp.trans (smoothJet_memLp hf).coeFn_toLp.symm
    change childTransportJetCLM k (hL.toLp (smoothJet f))∈zeroTraceAmbient
    rw [he,childTransportJetCLM_smooth k f hf hs]
    exact smoothH1_mem_H10 _ (hf.comp (sourceChildEuclidean_symm_contDiff _)) (hc.comp_homeomorph (sourceChildEuclidean (actualChildSign k)).symm)
      (sourceChildEuclidean_comp_support k hs)
  exact (Submodule.topologicalClosure_minimal _ hs ht) hz

def childH10Transport (k : Fin 2) : H10 →L[ℝ] H1 :=
  ((childTransportJetCLM k).comp (H1Space.subtypeL.comp H10.subtypeL)).codRestrict H1Space
    (fun u => zeroTraceAmbient_le_H1Space (childTransportJetCLM_H10 k u.property))

lemma childH10Transport_mem_H10 (k : Fin 2) (u : H10) : childH10Transport k u∈H10 :=
  childTransportJetCLM_H10 k u.property

open Set MeasureTheory Filter Topology

end

open Set MeasureTheory Filter Topology

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CentralCylinderGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceFaceAngleMatrix_det (i j : Fin 4) (x : Fin 3 → ℝ) :
    (sourceFaceAngleMatrix i j x).det=
      angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2) := by
  rw [sourceFaceAngleMatrix,Matrix.det_diagonal]
  simp [Fin.prod_univ_succ,angularArea]
  ring

lemma sourceFaceAngleMatrix_det_pos (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    0<(sourceFaceAngleMatrix i j x).det := by
  obtain ⟨_,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  rw [sourceFaceAngleMatrix_det]
  have h0 := (faceRayDensityLower_pos (w:=1) (by norm_num)).trans_le
    (faceRayDensity_lower (w:=1) (by norm_num) i ha)
  have hw : 0 < sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have h1 := (faceRayDensityLower_pos hw).trans_le (faceRayDensity_lower hw j hb)
  exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one angularArea_ge_one) h0) h1

lemma sourceCartesianGradientMatrix_det_ne_zero (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    (sourceCartesianGradientMatrix i j x).det≠0 := by
  rw [sourceCartesianGradientMatrix,Matrix.det_mul,Matrix.det_nonsing_inv,
    Matrix.det_transpose,Ring.inverse_eq_inv']
  exact mul_ne_zero (inv_ne_zero (sourceCollarJacobian_extended_ne_zero i j hx))
    (sourceFaceAngleMatrix_det_pos i j hx).ne'

def sourceFlatDensity (i j : Fin 4) (x : Fin 3 → ℝ) : ℝ :=
  (sourceFaceAngleMatrix i j x).det/|(sourceCollarJacobian i j x).det|

lemma sourceFlatDensity_pos (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    0 < sourceFlatDensity i j x :=
  div_pos (sourceFaceAngleMatrix_det_pos i j hx)
    (abs_pos.mpr (sourceCollarJacobian_extended_ne_zero i j hx))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFlatEllipticity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma continuousOn_sourceFlatDensity (i j : Fin 4) :
    ContinuousOn (sourceFlatDensity i j) (sourceExtendedBox (-(1:ℝ)/100) (1/100)) := by
  intro x hx
  exact ((continuous_sourceFaceAngleMatrix i j).matrix_det.continuousAt.div
    ((continuous_sourceCollarJacobian i j).matrix_det.abs.continuousAt)
      (abs_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j hx))).continuousWithinAt

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalFlatTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceCollarInverse_extended (i j : Fin 4) {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox l r) :
    sourceCollarInverse i j (sourceCollarPiece i j x)=x := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  exact sourceCollarInverse_left_pos i j
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/50)
      (sourceCollarRadius_extended j ⟨hl.trans ht.1,ht.2.trans hr⟩ hb).1)
    (by linarith [ht.2]) ha hb

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AttachedFlatTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def attachedCartesianMatrix (a : ℝ) (i j : Fin 4) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ := sourceCartesianGradientMatrix i j x*endAxialMatrix a

lemma attachedCartesianMatrix_det_ne_zero {a : ℝ} (ha : a≠0) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    (attachedCartesianMatrix a i j x).det≠0 := by
  rw [attachedCartesianMatrix,Matrix.det_mul]
  apply mul_ne_zero (sourceCartesianGradientMatrix_det_ne_zero i j hx)
  simpa [endAxialMatrix,Matrix.det_diagonal,Fin.prod_univ_succ] using ha

def attachedFlatTensor (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (|a| *sourceFlatDensity i j x) •
    (((attachedCartesianMatrix a i j x)⁻¹)ᵀ*flatCylinderMatrix s*
      (attachedCartesianMatrix a i j x)⁻¹)

lemma attachedFlatTensor_energy (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) (v w : Fin 3 → ℝ) :
    (attachedCartesianMatrix a i j x*ᵥv) ⬝ᵥ
      (attachedFlatTensor s a i j x*ᵥ(attachedCartesianMatrix a i j x*ᵥw))=
        |a| *sourceFlatDensity i j x*(v ⬝ᵥ (flatCylinderMatrix s*ᵥw)) :=
  inverse_congruence_energy _ _ (attachedCartesianMatrix_det_ne_zero ha i j hx) _ _ _

lemma continuousOn_attachedCartesianMatrix (a : ℝ) (i j : Fin 4) :
    ContinuousOn (attachedCartesianMatrix a i j) (sourceExtendedBox (-(1:ℝ)/100) (1/100)) :=
  (continuousOn_sourceCartesianGradientMatrix i j).mul continuousOn_const

lemma continuousOn_attachedFlatTensor (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0) (i j : Fin 4) :
    ContinuousOn (attachedFlatTensor s a i j) (sourceExtendedBox (-(1:ℝ)/100) (1/100)) := by
  have hi : ContinuousOn (fun x => (attachedCartesianMatrix a i j x)⁻¹)
      (sourceExtendedBox (-(1:ℝ)/100) (1/100)) := by
    intro x hx
    have hn := attachedCartesianMatrix_det_ne_zero ha i j hx
    exact (continuousAt_matrix_inv _ (by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hn)).comp_continuousWithinAt
        (continuousOn_attachedCartesianMatrix a i j x hx)
  exact (continuousOn_const.mul (continuousOn_sourceFlatDensity i j)).smul
    ((((continuous_id.matrix_transpose :
        Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => Aᵀ)).comp_continuousOn hi).mul
          continuousOn_const).mul hi)

theorem attachedFlatTensor_elliptic (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a : ℝ} (ha : a≠0) (i j : Fin 4) :
    ∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ x∈sourceExtendedBox (-(1:ℝ)/100) (1/100),
      ∀ v : Fin 3 → ℝ,c*‖v‖^2≤v ⬝ᵥ (attachedFlatTensor s a i j x*ᵥv) ∧
        v ⬝ᵥ (attachedFlatTensor s a i j x*ᵥv)≤C*‖v‖^2 := by
  apply compact_matrix_energy_bounds isCompact_Icc _ (continuousOn_attachedFlatTensor s ha i j)
  intro x hx v hv
  exact flat_inverse_congruence_positive s hs _ (attachedCartesianMatrix_det_ne_zero ha i j hx)
    (mul_pos (abs_pos.mpr ha) (sourceFlatDensity_pos i j hx)) hv

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_FiniteEndPhysicalTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

attribute [local instance] OAI.ScalarConductivity.finiteEndPhysicalTensorMeasurableSpace
local instance finiteEndPhysicalTensorBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

lemma measurable_real_matrix_inverse : Measurable (fun A : Mat3 => A⁻¹) := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv']
  exact continuous_id.matrix_det.measurable.inv.smul
    continuous_id.matrix_adjugate.measurable

lemma measurable_sourceCartesianGradientMatrix (i j : Fin 4) :
    Measurable (sourceCartesianGradientMatrix i j) := by
  unfold sourceCartesianGradientMatrix
  exact measurable_real_matrix_mul (measurable_real_matrix_inverse.comp
    (continuous_sourceCollarJacobian i j).matrix_transpose.measurable)
      (continuous_sourceFaceAngleMatrix i j).measurable

lemma measurable_attachedCartesianMatrix (a : ℝ) (i j : Fin 4) :
    Measurable (attachedCartesianMatrix a i j) :=
  measurable_real_matrix_mul (measurable_sourceCartesianGradientMatrix i j) measurable_const

lemma measurable_sourceFlatDensity (i j : Fin 4) : Measurable (sourceFlatDensity i j) :=
  (continuous_sourceFaceAngleMatrix i j).matrix_det.measurable.div
    (continuous_sourceCollarJacobian i j).matrix_det.abs.measurable

def attachedVariableTensor (K : Coord3 → Mat3) (a : ℝ) (i j : Fin 4)
    (x : Coord3) : Mat3 :=
  (|a| *sourceFlatDensity i j x) •
    ((attachedCartesianMatrix a i j x)⁻¹ᵀ*K x*(attachedCartesianMatrix a i j x)⁻¹)

lemma attachedVariableTensor_measurable {K : Coord3 → Mat3} (hK : Measurable K)
    (a : ℝ) (i j : Fin 4) : Measurable (attachedVariableTensor K a i j) := by
  have hi := measurable_real_matrix_inverse.comp (measurable_attachedCartesianMatrix a i j)
  have ht := (continuous_id.matrix_transpose : Continuous (fun A : Mat3 => Aᵀ)).measurable.comp hi
  exact (measurable_const.mul (measurable_sourceFlatDensity i j)).smul (measurable_real_matrix_mul (measurable_real_matrix_mul ht hK) hi)

lemma attachedVariableTensor_symmetric {K : Coord3 → Mat3} (hK : ∀ x,(K x)ᵀ=K x)
    (a : ℝ) (i j : Fin 4) (x : Coord3) :
    (attachedVariableTensor K a i j x)ᵀ=attachedVariableTensor K a i j x := by
  simp only [attachedVariableTensor,Matrix.transpose_smul,Matrix.transpose_mul,
    Matrix.transpose_transpose,hK,Matrix.mul_assoc]

lemma attachedVariableTensor_energy (K : Coord3 → Mat3) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (v w : Coord3) :
    (attachedCartesianMatrix a i j x*ᵥv) ⬝ᵥ
      (attachedVariableTensor K a i j x*ᵥ(attachedCartesianMatrix a i j x*ᵥw))=
        |a| *sourceFlatDensity i j x*(v ⬝ᵥ(K x*ᵥw)) :=
  inverse_congruence_energy _ _ (attachedCartesianMatrix_det_ne_zero ha i j hx) _ _ _

theorem attachedVariableTensor_elliptic {K : Coord3 → Mat3} {c C : ℝ}
    (hc : 0 < c) (hcC : c≤C)
    (hK : ∀ x w,c*(w ⬝ᵥ w)≤w ⬝ᵥ(K x*ᵥw) ∧ w ⬝ᵥ(K x*ᵥw)≤C*(w ⬝ᵥ w))
    {a : ℝ} (ha : a≠0) (i j : Fin 4) :
    ∃ l L : ℝ,0<l ∧ l<L ∧ ∀ x∈sourceExtendedBox (-(1:ℝ)/100) (1/100),
      ∀ v : Coord3,l*‖v‖^2≤v ⬝ᵥ(attachedVariableTensor K a i j x*ᵥv) ∧
        v ⬝ᵥ(attachedVariableTensor K a i j x*ᵥv)≤L*‖v‖^2 := by
  obtain ⟨l,L,hl,hlL,hbound⟩ := attachedFlatTensor_elliptic ![1,0,1]
    (by intro x y; norm_num [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]; nlinarith [sq_nonneg x,sq_nonneg y]) ha i j
  refine ⟨c*l,C*L,mul_pos hc hl,?_,?_⟩
  · exact (mul_lt_mul_of_pos_left hlL hc).trans_le
      (mul_le_mul_of_nonneg_right hcC (hl.trans hlL).le)
  · intro x hx v
    let u := (attachedCartesianMatrix a i j x)⁻¹*ᵥv
    have hu : attachedCartesianMatrix a i j x*ᵥu=v := by
      dsimp [u]
      rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
        (isUnit_iff_ne_zero.mpr (attachedCartesianMatrix_det_ne_zero ha i j hx)),Matrix.one_mulVec]
    have hid : flatCylinderMatrix ![1,0,1]=(1:Mat3) := by
      ext k l
      fin_cases k <;> fin_cases l <;> rfl
    have href := attachedFlatTensor_energy ![1,0,1] ha i j hx u u
    rw [hu,hid,Matrix.one_mulVec] at href
    have he := attachedVariableTensor_energy K ha i j hx u u
    rw [hu] at he
    have hd : 0≤|a| *sourceFlatDensity i j x :=
      mul_nonneg (abs_nonneg _) (sourceFlatDensity_pos i j hx).le
    have hh := hK x u
    have hlow := mul_le_mul_of_nonneg_left hh.1 hd
    have hupp := mul_le_mul_of_nonneg_left hh.2 hd
    have hb := hbound x hx v
    rw [href] at hb
    rw [he]
    constructor
    · calc
        c*l*‖v‖^2 = c*(l*‖v‖^2) := by ring
        _ ≤ c*(|a| *sourceFlatDensity i j x*(u ⬝ᵥ u)) := mul_le_mul_of_nonneg_left hb.1 hc.le
        _ = |a| *sourceFlatDensity i j x*(c*(u ⬝ᵥ u)) := by ring
        _ ≤ _ := hlow
    · calc
        _ ≤ |a| *sourceFlatDensity i j x*(C*(u ⬝ᵥ u)) := hupp
        _ = C*(|a| *sourceFlatDensity i j x*(u ⬝ᵥ u)) := by ring
        _ ≤ C*(L*‖v‖^2) := mul_le_mul_of_nonneg_left hb.2 (hc.le.trans hcC)
        _ = C*L*‖v‖^2 := by ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PiolaFluxAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

noncomputable def conductivityFlux (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (x : Coord3) : Matrix (Fin 3) (Fin 2) ℝ :=
  (A x).val * gradientColumns (fderiv ℝ u x)

structure CompactTwoFieldReplacement (μ : Measure Coord3) (O : Set Coord3)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) where
  du : Coord3 → Fin 2 → ℝ
  dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ
  tensor : Coord3 → Symmetric3
  smooth_du : ContDiff ℝ (↑(⊤ : ℕ∞)) du
  compact_du : HasCompactSupport du
  support_du : tsupport du ⊆ O
  smooth_dF : ContDiff ℝ (↑(⊤ : ℕ∞)) dF
  compact_dF : HasCompactSupport dF
  support_dF : tsupport dF ⊆ O
  cauchy_dF : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
    (∫ x, fderiv ℝ ψ x ((dF x).col j) ∂μ) = 0
  smooth_tensor : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (tensor x).val) O
  rank : ∀ x ∈ O, LinearIndependent ℝ
    (gradientColumns (fderiv ℝ (fun y => u y+du y) x)).col
  constitutive : ∀ x ∈ O, (tensor x).val *
    gradientColumns (fderiv ℝ (fun y => u y+du y) x) = conductivityFlux u A x + dF x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ChangeOld
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

def CompactTwoFieldReplacement.changeOld
    {μ : Measure Coord3} {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    (R : CompactTwoFieldReplacement μ O u A) (he : EqOn u v O) (hAB : EqOn A B O) :
    CompactTwoFieldReplacement μ O v B where
  du := R.du
  dF := R.dF
  tensor := R.tensor
  smooth_du := R.smooth_du
  compact_du := R.compact_du
  support_du := R.support_du
  smooth_dF := R.smooth_dF
  compact_dF := R.compact_dF
  support_dF := R.support_dF
  cauchy_dF := R.cauchy_dF
  smooth_tensor := R.smooth_tensor
  rank := by
    intro x hx
    rw [← fderiv_eq_of_eqOn_open hO (show EqOn (fun y => u y+R.du y)
      (fun y => v y+R.du y) O from fun y hy => by dsimp only; rw [he hy]) hx]
    exact R.rank x hx
  constitutive := by
    intro x hx
    rw [← fderiv_eq_of_eqOn_open hO (show EqOn (fun y => u y+R.du y)
      (fun y => v y+R.du y) O from fun y hy => by dsimp only; rw [he hy]) hx]
    rw [R.constitutive x hx]
    simp only [conductivityFlux, hAB hx, fderiv_eq_of_eqOn_open hO he hx]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactSelectedReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

structure CompactSelectedReplacement (J : Set (Fin 2)) (μ : Measure Coord3) (O : Set Coord3)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) where
  du : Coord3 → Fin 2 → ℝ
  dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ
  tensor : Coord3 → Symmetric3
  smooth_du : ContDiff ℝ (↑(⊤ : ℕ∞)) du
  compact_du : HasCompactSupport du
  support_du : tsupport du ⊆ O
  smooth_dF : ContDiff ℝ (↑(⊤ : ℕ∞)) dF
  compact_dF : HasCompactSupport dF
  support_dF : tsupport dF ⊆ O
  cauchy_dF : ∀ j ∈ J, ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
    (∫ x, fderiv ℝ ψ x ((dF x).col j) ∂μ) = 0
  smooth_tensor : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (tensor x).val) O
  rank : ∀ x ∈ O, LinearIndependent ℝ
    (gradientColumns (fderiv ℝ (fun y => u y+du y) x)).col
  constitutive : ∀ x ∈ O, (tensor x).val *
    gradientColumns (fderiv ℝ (fun y => u y+du y) x) = conductivityFlux u A x + dF x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactCompatibleReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory
open scoped Matrix.Norms.Elementwise

structure CompactCompatibleReplacement (μ : Measure Coord3) (O : Set Coord3)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) where
  du : Coord3 → Fin 2 → ℝ
  dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ
  tensor : Coord3 → Symmetric3
  smooth_du : ContDiff ℝ (↑(⊤ : ℕ∞)) du
  compact_du : HasCompactSupport du
  support_du : tsupport du ⊆ O
  smooth_dF : ContDiff ℝ (↑(⊤ : ℕ∞)) dF
  compact_dF : HasCompactSupport dF
  support_dF : tsupport dF ⊆ O
  cauchy_dF : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
    (∫ x, fderiv ℝ ψ x ((dF x).col j) ∂μ) = 0
  smooth_tensor : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (tensor x).val) O
  constitutive : ∀ x ∈ O, (tensor x).val *
    gradientColumns (fderiv ℝ (fun y => u y+du y) x) = conductivityFlux u A x + dF x

def CompactTwoFieldReplacement.forgetRank {μ : Measure Coord3} {O : Set Coord3}
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactTwoFieldReplacement μ O u A) : CompactCompatibleReplacement μ O u A where
  du := R.du
  dF := R.dF
  tensor := R.tensor
  smooth_du := R.smooth_du
  compact_du := R.compact_du
  support_du := R.support_du
  smooth_dF := R.smooth_dF
  compact_dF := R.compact_dF
  support_dF := R.support_dF
  cauchy_dF := R.cauchy_dF
  smooth_tensor := R.smooth_tensor
  constitutive := R.constitutive

lemma gradientColumns_affine_column {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {l κ : Fin 2 → ℝ}
    (he : ∀ x ∈ O, ∀ j, u x j = l j * v x 0 + κ j)
    (hv : DifferentiableOn ℝ v O) {x : Coord3} (hx : x ∈ O) (i : Fin 3) (j : Fin 2) :
    gradientColumns (fderiv ℝ u x) i j = l j * gradientColumns (fderiv ℝ v x) i 0 := by
  let w : Coord3 → Fin 2 → ℝ := fun x j => l j * v x 0 + κ j
  have hw : HasFDerivAt w
      (ContinuousLinearMap.pi (fun j => l j •
        ((ContinuousLinearMap.proj 0).comp (fderiv ℝ v x)))) x := by
    apply hasFDerivAt_pi.mpr
    intro j
    exact (((ContinuousLinearMap.proj 0).hasFDerivAt.comp x
      (hv x hx |>.differentiableAt (hO.mem_nhds hx)).hasFDerivAt).const_mul (l j)).add_const (κ j)
  have heq : EqOn u w O := fun y hy => funext (he y hy)
  rw [fderiv_eq_of_eqOn_open hO heq hx, hw.fderiv]
  rfl

def CompactSelectedReplacement.affineTransfer
    {μ : Measure Coord3} {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {l κ : Fin 2 → ℝ}
    (he : ∀ x ∈ O, ∀ j, u x j = l j * v x 0 + κ j)
    (hv : ContDiffOn ℝ (↑(⊤ : ℕ∞)) v O)
    (R : CompactSelectedReplacement {0} μ O v A) :
    CompactCompatibleReplacement μ O u A := by
  classical
  let du : Coord3 → Fin 2 → ℝ := fun x j => l j * R.du x 0
  let dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun x i j => l j * R.dF x i 0
  have hdu : ContDiff ℝ (↑(⊤ : ℕ∞)) du :=
    contDiff_pi.mpr (fun j => contDiff_const.mul (contDiff_pi.mp R.smooth_du 0))
  have hdF : ContDiff ℝ (↑(⊤ : ℕ∞)) dF :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => contDiff_const.mul
      (contDiff_pi.mp (contDiff_pi.mp R.smooth_dF i) 0)))
  have hsu : Function.support du ⊆ Function.support R.du := by
    intro x hx hz
    apply hx
    ext j
    simp [du, hz]
  have hsF : Function.support dF ⊆ Function.support R.dF := by
    intro x hx hz
    apply hx
    ext i j
    simp [dF, hz]
  have hsdu : tsupport du ⊆ tsupport R.du := closure_mono hsu
  have hsdF : tsupport dF ⊆ tsupport R.dF := closure_mono hsF
  refine ⟨du, dF, R.tensor, hdu, R.compact_du.mono hsu, hsdu.trans R.support_du,
    hdF, R.compact_dF.mono hsF, hsdF.trans R.support_dF, ?_, R.smooth_tensor, ?_⟩
  · intro j ψ hψ
    have hecol : (fun x => (dF x).col j) = fun x => l j • (R.dF x).col 0 := rfl
    simp_rw [show ∀ x, (dF x).col j = l j • (R.dF x).col 0 from fun x => congrFun hecol x,
      map_smul, smul_eq_mul]
    rw [integral_const_mul, R.cauchy_dF 0 (by simp) ψ hψ, mul_zero]
  · intro x hx
    have hnew (y : Coord3) (hy : y ∈ O) (j : Fin 2) :
        (u y + du y) j = l j * (v y + R.du y) 0 + κ j := by
      simp only [Pi.add_apply, du, he y hy j]
      ring
    have hvd := hv.differentiableOn (by simp)
    have hvo := (hv.add R.smooth_du.contDiffOn).differentiableOn (by simp)
    ext i j
    change (∑ k, (R.tensor x).val i k * gradientColumns (fderiv ℝ (fun y => u y+du y) x) k j) =
      (∑ k, (A x).val i k * gradientColumns (fderiv ℝ u x) k j) + l j * R.dF x i 0
    simp_rw [gradientColumns_affine_column hO hnew hvo hx,
      gradientColumns_affine_column hO he hvd hx]
    have hr := congrFun (congrFun (R.constitutive x hx) i) 0
    change (∑ k, (R.tensor x).val i k * gradientColumns (fderiv ℝ (fun y => v y+R.du y) x) k 0) =
      (∑ k, (A x).val i k * gradientColumns (fderiv ℝ v x) k 0) + R.dF x i 0 at hr
    calc
      ∑ k, (R.tensor x).val i k * (l j * gradientColumns (fderiv ℝ (fun y => v y+R.du y) x) k 0) =
          l j * ∑ k, (R.tensor x).val i k * gradientColumns (fderiv ℝ (fun y => v y+R.du y) x) k 0 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      _ = l j * ((∑ k, (A x).val i k * gradientColumns (fderiv ℝ v x) k 0) + R.dF x i 0) := by rw [hr]
      _ = (∑ k, (A x).val i k * (l j * gradientColumns (fderiv ℝ v x) k 0)) + l j * R.dF x i 0 := by
        rw [mul_add, Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro k _; ring

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

def CompactSelectedReplacement.changeOld
    {J : Set (Fin 2)}
    {μ : Measure Coord3} {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    (R : CompactSelectedReplacement J μ O u A) (he : EqOn u v O) (hAB : EqOn A B O) :
    CompactSelectedReplacement J μ O v B where
  du := R.du
  dF := R.dF
  tensor := R.tensor
  smooth_du := R.smooth_du
  compact_du := R.compact_du
  support_du := R.support_du
  smooth_dF := R.smooth_dF
  compact_dF := R.compact_dF
  support_dF := R.support_dF
  cauchy_dF := R.cauchy_dF
  smooth_tensor := R.smooth_tensor
  rank := by
    intro x hx
    rw [← fderiv_eq_of_eqOn_open hO (show EqOn (fun y => u y+R.du y)
      (fun y => v y+R.du y) O from fun y hy => by dsimp only; rw [he hy]) hx]
    exact R.rank x hx
  constitutive := by
    intro x hx
    rw [← fderiv_eq_of_eqOn_open hO (show EqOn (fun y => u y+R.du y)
      (fun y => v y+R.du y) O from fun y hy => by dsimp only; rw [he hy]) hx]
    rw [R.constitutive x hx]
    simp only [conductivityFlux, hAB hx, fderiv_eq_of_eqOn_open hO he hx]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_Unchanged
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

def CompactCompatibleReplacement.unchanged
    (μ : Measure Coord3) (O : Set Coord3) (u : Coord3 → Fin 2 → ℝ)
    (A : Coord3 → Symmetric3)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) O) :
    CompactCompatibleReplacement μ O u A where
  du := 0
  dF := 0
  tensor := A
  smooth_du := contDiff_const
  compact_du := by simp [HasCompactSupport]
  support_du := by simp
  smooth_dF := contDiff_const
  compact_dF := by simp [HasCompactSupport]
  support_dF := by simp
  cauchy_dF := by
    intro j ψ _
    change (∫ x, fderiv ℝ ψ x (0 : Coord3) ∂μ) = 0
    simp
  smooth_tensor := hA
  constitutive := by intro x _; simp only [Pi.zero_apply, add_zero, conductivityFlux]

lemma gradientColumns_zero_fderiv_of_constant {O : Set Coord3} (hO : IsOpen O)
    {u : Coord3 → Fin 2 → ℝ} {κ : Fin 2 → ℝ}
    (he : ∀ x ∈ O, u x = κ) {x : Coord3} (hx : x ∈ O) :
    gradientColumns (fderiv ℝ u x) = 0 := by
  rw [fderiv_eq_of_eqOn_open hO he hx]
  have hz : fderiv ℝ (fun _ : Coord3 => κ) x = 0 := congrFun (fderiv_const (𝕜 := ℝ) κ) x
  rw [hz]
  rfl

def CompactCompatibleReplacement.constantRank
    (μ : Measure Coord3) {O : Set Coord3} (hO : IsOpen O)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    {κ : Fin 2 → ℝ} (he : ∀ x ∈ O, u x = κ) (S : Symmetric3) :
    CompactCompatibleReplacement μ O u A where
  du := 0
  dF := 0
  tensor := fun _ => S
  smooth_du := contDiff_const
  compact_du := by simp [HasCompactSupport]
  support_du := by simp
  smooth_dF := contDiff_const
  compact_dF := by simp [HasCompactSupport]
  support_dF := by simp
  cauchy_dF := by
    intro j ψ _
    change (∫ x, fderiv ℝ ψ x (0 : Coord3) ∂μ) = 0
    simp
  smooth_tensor := contDiffOn_const
  constitutive := by
    intro x hx
    simp only [Pi.zero_apply, add_zero, conductivityFlux,
      gradientColumns_zero_fderiv_of_constant hO he hx, Matrix.mul_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalTensorPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def sourceFlatPatch (i j : Fin 4) : Set (Fin 3 → ℝ) :=
  sourceCollarPiece i j '' sourceExtendedBox (-(1:ℝ)/100) (1/100)

lemma isCompact_sourceFlatPatch (i j : Fin 4) : IsCompact (sourceFlatPatch i j) :=
  isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullWeakEndEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceCollarClosedPiece_subset {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (i j : Fin 4) :
    sourceCollarPiece i j '' sourceExtendedBox l r ⊆ sourceClosedCollarBand l r := by
  rw [sourceClosedCollarBand_eq l r hl hr]
  exact (subset_iUnion_of_subset i (subset_iUnion_of_subset j (Subset.rfl)))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactRegularCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma cubePartial_smooth {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (v : Box3) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cubePartial f v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma cubePartial_compact {f : Box3 → ℝ} (hf : HasCompactSupport f) (v : Box3) :
    HasCompactSupport (cubePartial f v) := hf.fderiv_apply ℝ v

lemma cube_integration_by_parts {f g : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hs : HasCompactSupport g) (v : Box3) :
    (∫ p, f p*cubePartial g v p)= -(∫ p, cubePartial f v p*g p) := by
  let : (volume : Measure Box3).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ×ℝ)) (volume : Measure ℝ)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (((continuous_cubePartial hf v).mul hg.continuous).integrable_of_hasCompactSupport hs.mul_left)
    ((hf.continuous.mul (continuous_cubePartial hg v)).integrable_of_hasCompactSupport (μ := volume)
      (cubePartial_compact hs v).mul_left)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hs.mul_left)
    (fun p _ => hf.differentiable (by simp) p) (fun p _ => hg.differentiable (by simp) p)

lemma cubePartial_snd_fst (v p : Box3) : cubePartial (fun x => x.1.2) v p=v.1.2 := by
  have hh : HasFDerivAt (fun x : Box3 => x.1.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ)) p :=
    hasFDerivAt_snd.comp p hasFDerivAt_fst
  rw [cubePartial,hh.fderiv]; rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_BoxCoordinateBridge
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def boxCoordinates : Coord3 ≃L[ℝ] Box3 :=
  (show Coord3 ≃ₗ[ℝ] Box3 from
    { toFun := fun x => ((x 0,x 1),x 2)
      invFun := fun p => ![p.1.1,p.1.2,p.2]
      left_inv := by intro x; ext i; fin_cases i <;> rfl
      right_inv := by intro p; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }).toContinuousLinearEquiv

lemma boxCoordinates_volume : MeasurePreserving boxCoordinates := by
  exact (volume_preserving_prodAssoc.symm (MeasurableEquiv.prodAssoc : Box3≃ᵐ ℝ×(ℝ×ℝ))).comp
    threeArrow_volume

lemma boxCoordinates_integral (f : Box3 → ℝ) :
    (∫ x,f (boxCoordinates x))=(∫ p,f p) :=
  boxCoordinates_volume.integral_comp boxCoordinates.toHomeomorph.measurableEmbedding f

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CompactInteriorDivergence
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma cubePartial_tsupport {f : Box3 → ℝ} (v : Box3) :
    tsupport (cubePartial f v)⊆tsupport f := tsupport_fderiv_apply_subset ℝ v

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_BoxMomentRightInverse
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma exists_unit_box_bump {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i) :
    ∃ K : Box3 → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) K ∧ HasCompactSupport K ∧
      tsupport K⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) ∧
      (∫ p,K p)=1 := by
  obtain ⟨η₁,h₁,hs₁,hv₁,hi₁⟩ := exists_unit_global_interval_bump (hab 0)
  obtain ⟨η₂,h₂,hs₂,hv₂,hi₂⟩ := exists_unit_global_interval_bump (hab 1)
  obtain ⟨η₃,h₃,hs₃,hv₃,hi₃⟩ := exists_unit_global_interval_bump (hab 2)
  let K : Box3 → ℝ := fun p => (η₁ p.1.1*η₂ p.1.2)*η₃ p.2
  have hK : ContDiff ℝ (↑(⊤ : ℕ∞)) K :=
    ((h₁.comp (contDiff_fst.comp contDiff_fst)).mul
      (h₂.comp (contDiff_snd.comp contDiff_fst))).mul (h₃.comp contDiff_snd)
  have hsK : HasCompactSupport K := by
    apply HasCompactSupport.of_support_subset_isCompact ((hs₁.prod hs₂).prod hs₃)
    intro p hp
    have hh := mul_ne_zero_iff.mp hp
    have hh' := mul_ne_zero_iff.mp hh.1
    exact ⟨⟨subset_tsupport η₁ hh'.1,subset_tsupport η₂ hh'.2⟩,subset_tsupport η₃ hh.2⟩
  have htK : tsupport K⊆(tsupport η₁ ×ˢ tsupport η₂) ×ˢ tsupport η₃ := by
    apply closure_minimal _ ((hs₁.isClosed.prod hs₂.isClosed).prod hs₃.isClosed)
    intro p hp
    have hh := mul_ne_zero_iff.mp hp
    have hh' := mul_ne_zero_iff.mp hh.1
    exact ⟨⟨subset_tsupport η₁ hh'.1,subset_tsupport η₂ hh'.2⟩,subset_tsupport η₃ hh.2⟩
  refine ⟨K,hK,hsK,htK.trans (prod_mono (prod_mono hv₁ hv₂) hv₃),?_⟩
  change (∫ p : (ℝ×ℝ)×ℝ,(η₁ p.1.1*η₂ p.1.2)*η₃ p.2)=1
  rw [Measure.volume_eq_prod,integral_prod_mul (fun p : ℝ×ℝ => η₁ p.1*η₂ p.2) η₃,
    Measure.volume_eq_prod,integral_prod_mul η₁ η₂,hi₁,hi₂,hi₃]
  norm_num

lemma cubePartial_integral_zero {K : Box3 → ℝ}
    (hK : ContDiff ℝ (↑(⊤ : ℕ∞)) K) (hs : HasCompactSupport K) (v : Box3) :
    (∫ p,cubePartial K v p)=0 := by
  have hh := cube_integration_by_parts (f := fun _ => (1:ℝ)) contDiff_const hK hs v
  simpa [cubePartial] using hh

theorem box_moment_right_inverse {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i)
    (m : Fin 3 → ℝ) :
    ∃ r₁ r₂ : Box3 → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) r₁ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) r₂ ∧
      HasCompactSupport r₁ ∧ HasCompactSupport r₂ ∧
      tsupport r₁⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) ∧
      tsupport r₂⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) ∧
      (∫ p,r₁ p)=m 0 ∧ (∫ p,r₂ p)=m 1 ∧
      (∫ p,p.1.2*r₁ p-p.1.1*r₂ p)=m 2 := by
  obtain ⟨K,hK,hs,hv,hi⟩ := exists_unit_box_bump hab
  let D := cubePartial K ((0,1),0)
  let c := m 0*(∫ p : Box3,p.1.2*K p)-m 1*(∫ p : Box3,p.1.1*K p)-m 2
  let r₁ := fun p => m 0*K p+c*D p
  let r₂ := fun p => m 1*K p
  have hD : ContDiff ℝ (↑(⊤ : ℕ∞)) D := cubePartial_smooth hK _
  have hsD : HasCompactSupport D := cubePartial_compact hs _
  have hvD : tsupport D⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) :=
    (cubePartial_tsupport _).trans hv
  have iK : Integrable K := hK.continuous.integrable_of_hasCompactSupport hs
  have iD : Integrable D := hD.continuous.integrable_of_hasCompactSupport hsD
  have hDz : (∫ p,D p)=0 := cubePartial_integral_zero hK hs _
  have hf₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Box3 => p.1.1) := contDiff_fst.comp contDiff_fst
  have hf₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Box3 => p.1.2) := contDiff_snd.comp contDiff_fst
  have hDm : (∫ p : Box3,p.1.2*D p)= -1 := by
    have hh := cube_integration_by_parts hf₂ hK hs ((0,1),0)
    simpa only [cubePartial_snd_fst,one_mul,hi] using hh
  have iK₁ : Integrable (fun p : Box3 => p.1.1*K p) :=
    (hf₁.continuous.mul hK.continuous).integrable_of_hasCompactSupport hs.mul_left
  have iK₂ : Integrable (fun p : Box3 => p.1.2*K p) :=
    (hf₂.continuous.mul hK.continuous).integrable_of_hasCompactSupport hs.mul_left
  have iD₂ : Integrable (fun p : Box3 => p.1.2*D p) :=
    (hf₂.continuous.mul hD.continuous).integrable_of_hasCompactSupport hsD.mul_left
  refine ⟨r₁,r₂,(contDiff_const.mul hK).add (contDiff_const.mul hD),
    contDiff_const.mul hK,(hs.mul_left).add hsD.mul_left,hs.mul_left,?_,?_,?_,?_,?_⟩
  · exact (tsupport_add _ _).trans (union_subset
      (tsupport_mul_subset_right.trans hv) (tsupport_mul_subset_right.trans hvD))
  · exact tsupport_mul_subset_right.trans hv
  · dsimp only [r₁]
    rw [integral_add (iK.const_mul _) (iD.const_mul _),integral_const_mul,integral_const_mul,hi,hDz]
    ring
  · dsimp only [r₂]
    rw [integral_const_mul,hi,mul_one]
  · have he : (fun p : Box3 => p.1.2*r₁ p-p.1.1*r₂ p)=
        (fun p => m 0*(p.1.2*K p)+c*(p.1.2*D p)-m 1*(p.1.1*K p)) := by
      funext p; dsimp only [r₁,r₂]; ring
    have iKD : Integrable (fun p : Box3 => m 0*(p.1.2*K p)+c*(p.1.2*D p)) :=
      (iK₂.const_mul _).add (iD₂.const_mul _)
    rw [he,integral_sub iKD (iK₁.const_mul _),
      integral_add (iK₂.const_mul _) (iD₂.const_mul _),integral_const_mul,integral_const_mul,
      integral_const_mul,hDm]
    dsimp only [c]
    ring

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalOverlapMoments
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma localPiolaSource_torque (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    (r₁ r₂ : Coord3 → ℝ) (h₁ : Function.support r₁⊆X.source)
    (h₂ : Function.support r₂⊆X.source) :
    (∫ y,(X.symm y) 1*localPiolaSource X r₁ y-
      (X.symm y) 0*localPiolaSource X r₂ y)=
      (∫ x,x 1*r₁ x-x 0*r₂ x) := by
  let r : Coord3 → ℝ := fun x => x 1*r₁ x-x 0*r₂ x
  have hs : Function.support r⊆X.source := by
    intro x hx
    by_contra hn
    have hz₁ : r₁ x=0 := Function.notMem_support.mp (fun hh => hn (h₁ hh))
    have hz₂ : r₂ x=0 := Function.notMem_support.mp (fun hh => hn (h₂ hh))
    exact hx (by simp only [r,hz₁,hz₂,mul_zero,sub_self])
  have hp := localPiolaSource_pairing volume X hX
    (fun _ hx => local_fderiv_det_ne_zero X hX hXi hx) r hs (fun _ => 1)
  simp only [one_mul] at hp
  rw [←hp]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases ht : y∈X.target
  · simp only [localPiolaSource,ite_eq_left ht,r]
    ring
  · simp only [localPiolaSource,ite_eq_right ht,mul_zero,sub_self]

theorem physical_overlap_moment_inverse
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i)
    (hbox : boxCoordinates ⁻¹' ((Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))⊆X.source)
    (m : Fin 3 → ℝ) :
    ∃ R₁ R₂ : Coord3 → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) R₁ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) R₂ ∧
      HasCompactSupport R₁ ∧ HasCompactSupport R₂ ∧
      tsupport R₁⊆X.target ∧ tsupport R₂⊆X.target ∧
      (∫ y,R₁ y)=m 0 ∧ (∫ y,R₂ y)=m 1 ∧
      (∫ y,(X.symm y) 1*R₁ y-(X.symm y) 0*R₂ y)=m 2 := by
  obtain ⟨r₁,r₂,hr₁,hr₂,hc₁,hc₂,hs₁,hs₂,hm₁,hm₂,hmt⟩ := box_moment_right_inverse hab m
  let p₁ : Coord3 → ℝ := r₁∘boxCoordinates
  let p₂ : Coord3 → ℝ := r₂∘boxCoordinates
  have hp₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) p₁ := hr₁.comp boxCoordinates.contDiff
  have hp₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) p₂ := hr₂.comp boxCoordinates.contDiff
  have hpc₁ : HasCompactSupport p₁ := hc₁.comp_homeomorph boxCoordinates.toHomeomorph
  have hpc₂ : HasCompactSupport p₂ := hc₂.comp_homeomorph boxCoordinates.toHomeomorph
  have hps₁ : tsupport p₁⊆X.source :=
    ((tsupport_comp_subset_preimage r₁ boxCoordinates.continuous).trans (preimage_mono hs₁)).trans hbox
  have hps₂ : tsupport p₂⊆X.source :=
    ((tsupport_comp_subset_preimage r₂ boxCoordinates.continuous).trans (preimage_mono hs₂)).trans hbox
  have hd := hX.differentiableOn (by simp)
  have hdi := hXi.differentiableOn (by simp)
  have hdet : ∀ x∈X.source,(fderiv ℝ X x).det≠0 :=
    fun _ hx => local_fderiv_det_ne_zero X hd hdi hx
  refine ⟨localPiolaSource X p₁,localPiolaSource X p₂,
    localPiolaSource_smooth X hX hXi p₁ hp₁ hpc₁ hps₁,
    localPiolaSource_smooth X hX hXi p₂ hp₂ hpc₂ hps₂,
    (localPiolaSource_compact X p₁ hpc₁ hps₁).1,
    (localPiolaSource_compact X p₂ hpc₂ hps₂).1,
    (localPiolaSource_compact X p₁ hpc₁ hps₁).2,
    (localPiolaSource_compact X p₂ hpc₂ hps₂).2,?_,?_,?_⟩
  · have h := localPiolaSource_pairing volume X hd hdet p₁ (subset_tsupport p₁ |>.trans hps₁) (fun _ => 1)
    simp only [one_mul] at h
    rw [h]
    exact (boxCoordinates_integral r₁).trans hm₁
  · have h := localPiolaSource_pairing volume X hd hdet p₂ (subset_tsupport p₂ |>.trans hps₂) (fun _ => 1)
    simp only [one_mul] at h
    rw [h]
    exact (boxCoordinates_integral r₂).trans hm₂
  · rw [localPiolaSource_torque X hd hdi p₁ p₂
      (subset_tsupport p₁ |>.trans hps₁) (subset_tsupport p₂ |>.trans hps₂)]
    exact (boxCoordinates_integral (fun p => p.1.2*r₁ p-p.1.1*r₂ p)).trans hmt

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_LocalPhysicalCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

def correctionBox (a b : Fin 3 → ℝ) : Set Coord3 :=
  boxCoordinates ⁻¹' ((Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPotentialCoordinates
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

def potentialCompletion (D : Coord3 →L[ℝ] (Fin 2 → ℝ)) : Mat3 :=
  ![(gradientColumns D).col 0,(gradientColumns D).col 1,
    crossProduct ((gradientColumns D).col 0) ((gradientColumns D).col 1)]

lemma potentialCompletion_det_ne_zero (D : Coord3 →L[ℝ] (Fin 2 → ℝ))
    (hD : Function.Surjective D) : (potentialCompletion D).det≠0 := by
  have hc : crossProduct ((gradientColumns D).col 0) ((gradientColumns D).col 1)≠0 := by
    apply crossProduct_ne_zero_iff_linearIndependent.mpr
    have he : ![(gradientColumns D).col 0,(gradientColumns D).col 1] =
        (gradientColumns D).col := by
      ext j i
      fin_cases j <;> rfl
    rw [he]
    exact gradientColumns_rank D hD
  rw [potentialCompletion,←triple_product_eq_det,
    triple_product_permutation ((gradientColumns D).col 0),
    triple_product_permutation ((gradientColumns D).col 1)]
  exact mt dotProduct_self_eq_zero.mp hc

lemma potentialCompletion_pairing (D : Coord3 →L[ℝ] (Fin 2 → ℝ)) (x : Coord3) :
    coordinatePair (potentialCompletion D*ᵥx)=D x := by
  rw [←gradientColumns_apply D x]
  ext j
  fin_cases j <;> rfl

def potentialCompletionEquiv (D : Coord3 →L[ℝ] (Fin 2 → ℝ))
    (hD : Function.Surjective D) : Coord3 ≃L[ℝ] Coord3 :=
  (LinearMap.equivOfDetNeZero (Matrix.toLin' (potentialCompletion D))
    (by rw [LinearMap.det_toLin']; exact potentialCompletion_det_ne_zero D hD)).toContinuousLinearEquiv

lemma potentialCompletionEquiv_pairing (D : Coord3 →L[ℝ] (Fin 2 → ℝ))
    (hD : Function.Surjective D) (x : Coord3) :
    coordinatePair (potentialCompletionEquiv D hD x)=D x :=
  potentialCompletion_pairing D x

theorem exists_regular_potential_coordinates
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (a : Coord3) (hD : Function.Surjective (fderiv ℝ u a))
    {U : Set Coord3} (hU : IsOpen U) (ha : a∈U) :
    ∃ X : OpenPartialHomeomorph Coord3 Coord3,
      a∈X.target ∧ X.target⊆U ∧
      ContDiffOn ℝ (↑(⊤:ℕ∞)) X X.source ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) X.symm ∧
      u=coordinatePair∘X.symm := by
  obtain ⟨Y,haY,hYU,hY,hYi,he,hder⟩ := exists_potential_chart hu a hD hU ha
  let L : Coord3 ≃L[ℝ] Coord3 := potentialCompletionEquiv (fderiv ℝ u a) hD
  let Z := Y.transHomeomorph L.toHomeomorph
  refine ⟨Z.symm,haY,hYU,?_,?_,?_⟩
  · change ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun z => Y.symm (L.symm z)) {z | L.symm z∈Y.target}
    exact hYi.comp L.symm.contDiff.contDiffOn (fun _ hx => hx)
  · change ContDiff ℝ (↑(⊤:ℕ∞)) (fun z => L (Y z))
    exact L.contDiff.comp hY
  · funext x
    exact (he x).symm.trans (potentialCompletionEquiv_pairing _ hD (Y x)).symm

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma mem_correctionBox {a b x : Coord3} : x∈correctionBox a b ↔ ∀ i,a i<x i ∧ x i<b i := by
  constructor
  · rintro ⟨⟨h0,h1⟩,h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro h
    exact ⟨⟨h 0,h 1⟩,h 2⟩

lemma exists_correctionBox_inside {U : Set Coord3} (hU : IsOpen U) {x : Coord3} (hx : x∈U) :
    ∃ a b : Coord3,(∀ i,a i<b i) ∧ x∈correctionBox a b ∧ correctionBox a b⊆U := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨fun i => x i-ε,fun i => x i+ε,fun i => by linarith,
    mem_correctionBox.mpr (fun i => by constructor <;> linarith),?_⟩
  intro y hy
  apply hball
  rw [Metric.mem_ball,dist_pi_lt_iff hε]
  intro i
  rw [Real.dist_eq,abs_lt]
  have hi := mem_correctionBox.mp hy i
  constructor <;> linarith

structure RegularCorrectionBox (u : Coord3 → Fin 2 → ℝ) (U : Set Coord3) where
  chart : OpenPartialHomeomorph Coord3 Coord3
  lower : Coord3
  upper : Coord3
  widths : ∀ i,lower i<upper i
  subset_source : correctionBox lower upper⊆chart.source
  smooth : ContDiffOn ℝ (↑(⊤:ℕ∞)) chart chart.source
  inverse_smooth : ContDiffOn ℝ (↑(⊤:ℕ∞)) chart.symm chart.target
  potentials : EqOn u (coordinatePair∘chart.symm) chart.target
  target_subset : chart.target⊆U

namespace RegularCorrectionBox
variable {u : Coord3 → Fin 2 → ℝ} {U : Set Coord3}
def region (B : RegularCorrectionBox u U) : Set Coord3 :=
  B.chart '' correctionBox B.lower B.upper

end RegularCorrectionBox

theorem exists_regular_correction_box
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {U : Set Coord3} (hU : IsOpen U) {p : Coord3} (hp : p∈U)
    (hD : Function.Surjective (fderiv ℝ u p)) :
    ∃ B : RegularCorrectionBox u U,p∈B.region := by
  obtain ⟨X,hpX,hXU,hX,hXi,he⟩ := exists_regular_potential_coordinates hu p hD hU hp
  obtain ⟨a,b,hab,hx,hs⟩ := exists_correctionBox_inside X.open_source (X.map_target hpX)
  let B : RegularCorrectionBox u U := ⟨X,a,b,hab,hs,hX,hXi.contDiffOn,fun _ _ => congrFun he _,hXU⟩
  exact ⟨B,X.symm p,hx,X.right_inv hpX⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactPhysicalCorrections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

def physicalSourceMoment (u : Coord3 → Fin 2 → ℝ) (r : PhysicalSourcePair) : Coord3 :=
  ![∫ x,r 0 x,∫ x,r 1 x,∫ x,u x 1*r 0 x-u x 0*r 1 x]

namespace CompactSmoothPair
variable {r s : PhysicalSourcePair}
lemma zero : CompactSmoothPair 0 := fun _ => ⟨contDiff_const,HasCompactSupport.zero⟩
lemma add (hr : CompactSmoothPair r) (hs : CompactSmoothPair s) : CompactSmoothPair (r+s) :=
  fun j => ⟨(hr j).1.add (hs j).1,(hr j).2.add (hs j).2⟩
lemma sub (hr : CompactSmoothPair r) (hs : CompactSmoothPair s) : CompactSmoothPair (r-s) :=
  fun j => ⟨(hr j).1.sub (hs j).1,(hr j).2.sub (hs j).2⟩
lemma integrable (hr : CompactSmoothPair r) (j : Fin 2) : Integrable (r j) :=
  (hr j).1.continuous.integrable_of_hasCompactSupport (hr j).2
lemma torque_integrable (hr : CompactSmoothPair r) {u : Coord3 → Fin 2 → ℝ}
    (hu : Continuous u) : Integrable (fun x => u x 1*r 0 x-u x 0*r 1 x) :=
  ((continuous_apply 1 |>.comp hu).mul (hr 0).1.continuous |>.integrable_of_hasCompactSupport
    (hr 0).2.mul_left).sub
  ((continuous_apply 0 |>.comp hu).mul (hr 1).1.continuous |>.integrable_of_hasCompactSupport
    (hr 1).2.mul_left)
end CompactSmoothPair

namespace PairSupported
variable {r s : PhysicalSourcePair} {U V : Set Coord3}
lemma mono (hr : PairSupported r U) (hUV : U⊆V) : PairSupported r V :=
  fun j => (hr j).trans hUV
lemma zero : PairSupported 0 U := by intro j; simp [tsupport_zero]
lemma add (hr : PairSupported r U) (hs : PairSupported s U) : PairSupported (r+s) U :=
  fun j => (tsupport_add (r j) (s j)).trans (union_subset (hr j) (hs j))
lemma sub (hr : PairSupported r U) (hs : PairSupported s U) : PairSupported (r-s) U :=
  fun j => (tsupport_sub (r j) (s j)).trans (union_subset (hr j) (hs j))
end PairSupported

lemma physicalSourceMoment_zero (u : Coord3 → Fin 2 → ℝ) : physicalSourceMoment u 0=0 := by
  simp [physicalSourceMoment]

lemma physicalSourceMoment_add {u : Coord3 → Fin 2 → ℝ} (hu : Continuous u)
    {r s : PhysicalSourcePair} (hr : CompactSmoothPair r) (hs : CompactSmoothPair s) :
    physicalSourceMoment u (r+s)=physicalSourceMoment u r+physicalSourceMoment u s := by
  have he : (fun x => u x 1*(r+s) 0 x-u x 0*(r+s) 1 x)=
      (fun x => (u x 1*r 0 x-u x 0*r 1 x)+(u x 1*s 0 x-u x 0*s 1 x)) := by
    funext x; change u x 1*(r 0 x+s 0 x)-u x 0*(r 1 x+s 1 x)=_; ring
  ext i
  fin_cases i
  · exact integral_add (hr.integrable 0) (hs.integrable 0)
  · exact integral_add (hr.integrable 1) (hs.integrable 1)
  · change (∫ x,u x 1*(r+s) 0 x-u x 0*(r+s) 1 x)=_
    rw [he,integral_add (hr.torque_integrable hu) (hs.torque_integrable hu)]
    rfl

lemma physicalSourceMoment_sub {u : Coord3 → Fin 2 → ℝ} (hu : Continuous u)
    {r s : PhysicalSourcePair} (hr : CompactSmoothPair r) (hs : CompactSmoothPair s) :
    physicalSourceMoment u (r-s)=physicalSourceMoment u r-physicalSourceMoment u s := by
  have he := physicalSourceMoment_add hu (hr.sub hs) hs
  rw [sub_add_cancel] at he
  exact eq_sub_iff_add_eq.mpr he.symm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_ParametricSymmetricSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace ScalarConductivity
open Set Filter Topology
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma compact_supported_family_C1_small {f : P×Coord3 → ℝ} {p : P} {V : Set P}
    (hV : IsOpen V) (hp : p∈V) (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f (V×ˢuniv))
    {K : Set Coord3} (hK : IsCompact K)
    (hs : ∀ᶠ q in 𝓝 p,tsupport (fun x => f (q,x))⊆K)
    (hz : ∀ x,f (p,x)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,UniformC1Bound (fun x => f (q,x)) ε := by
  have hopen : IsOpen (V×ˢ(univ : Set Coord3)) := hV.prod isOpen_univ
  have hc (x : Coord3) : ContDiffAt ℝ (↑(⊤:ℕ∞)) f (p,x) :=
    hf.contDiffAt (hopen.mem_nhds ⟨hp,mem_univ x⟩)
  have hd := spatialFDeriv_smoothOn hopen hf
  have he : (fun x => f (p,x))=fun _ => 0 := funext hz
  have hzD (x : Coord3) : spatialFDeriv f (p,x)=0 := by
    dsimp [spatialFDeriv]; rw [he]; simp
  have hv := compact_parametric_norm_small hK (fun x _ => (hc x).continuousAt)
    (fun x _ => hz x) hε
  have hder := compact_parametric_norm_small hK
    (fun x _ => (hd.contDiffAt (hopen.mem_nhds ⟨hp,mem_univ x⟩)).continuousAt)
    (fun x _ => hzD x) hε
  filter_upwards [hs,hv,hder] with q hq hv hd
  intro x
  by_cases hx : x∈K
  · exact ⟨by simpa only [Real.norm_eq_abs] using hv x hx,hd x hx⟩
  · have hn : x∉tsupport (fun y => f (q,y)) := fun hh => hx (hq hh)
    have hv : f (q,x)=0 := image_eq_zero_of_notMem_tsupport (f:=fun y => f (q,y)) hn
    have hd := fderiv_of_notMem_tsupport ℝ hn
    exact ⟨by change |f (q,x)|≤ε; rw [hv,abs_zero]; exact hε.le,by rw [hd,norm_zero]; exact hε.le⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_ParametricWallTensors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology

def wallPositiveCut (δ : ℝ) (f : Coord3 → ℝ) (x : Coord3) : ℝ :=
  Real.smoothTransition (x 2/δ)*f x

lemma wallPositiveCut_smooth {δ : ℝ} {f : Coord3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (wallPositiveCut δ f) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_apply ℝ ℝ (2:Fin 3)).div_const δ)).mul hf

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_RegularMomentTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

theorem exists_physical_moments_in_open
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {U O : Set Coord3} (hO : IsOpen O) (hne : O.Nonempty) (hOU : O⊆U)
    (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p)) (m : Coord3) :
    ∃ r : PhysicalSourcePair,CompactSmoothPair r ∧ PairSupported r O ∧
      physicalSourceMoment u r=m := by
  obtain ⟨p,hp⟩ := hne
  obtain ⟨B,_⟩ := exists_regular_correction_box hu hO hp (hD p (hOU hp))
  obtain ⟨r₀,r₁,hr₀,hr₁,hc₀,hc₁,hs₀,hs₁,hm₀,hm₁,hmt⟩ :=
    physical_overlap_moment_inverse B.chart B.smooth B.inverse_smooth B.widths B.subset_source m
  let r : PhysicalSourcePair := ![r₀,r₁]
  have hr : CompactSmoothPair r := by
    intro j; fin_cases j
    · exact ⟨hr₀,hc₀⟩
    · exact ⟨hr₁,hc₁⟩
  have hs : PairSupported r B.chart.target := by
    intro j; fin_cases j
    · exact hs₀
    · exact hs₁
  refine ⟨r,hr,hs.mono B.target_subset,?_⟩
  ext i
  fin_cases i
  · exact hm₀
  · exact hm₁
  · change (∫ x,u x 1*r₀ x-u x 0*r₁ x)=m 2
    rw [←hmt]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈B.chart.target
    · have he := B.potentials hx
      rw [he]
      rfl
    · have h₀ : r₀ x=0 := Function.notMem_support.mp (fun hh => hx (hs₀ (subset_tsupport r₀ hh)))
      have h₁ : r₁ x=0 := Function.notMem_support.mp (fun hh => hx (hs₁ (subset_tsupport r₁ hh)))
      simp [h₀,h₁]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_GlobalRegularCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma CompactSmoothPair.sum {ι : Type*} (s : Finset ι) (r : ι → PhysicalSourcePair)
    (hr : ∀ i∈s,CompactSmoothPair (r i)) : CompactSmoothPair (∑ i∈s,r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CompactSmoothPair.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hr a (Finset.mem_insert_self a s)).add (ih fun i hi => hr i (Finset.mem_insert_of_mem hi))

lemma PairSupported.sum {ι : Type*} (s : Finset ι) (r : ι → PhysicalSourcePair)
    {U : Set Coord3} (hr : ∀ i∈s,PairSupported (r i) U) : PairSupported (∑ i∈s,r i) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PairSupported.zero (U := U)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hr a (Finset.mem_insert_self a s)).add (ih fun i hi => hr i (Finset.mem_insert_of_mem hi))

lemma physicalSourceMoment_sum {ι : Type*} (s : Finset ι) (r : ι → PhysicalSourcePair)
    {u : Coord3 → Fin 2 → ℝ} (hu : Continuous u)
    (hr : ∀ i∈s,CompactSmoothPair (r i)) :
    physicalSourceMoment u (∑ i∈s,r i)=∑ i∈s,physicalSourceMoment u (r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using physicalSourceMoment_zero u
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha,physicalSourceMoment_add hu
      (hr a (Finset.mem_insert_self a s))
      (CompactSmoothPair.sum s r (fun i hi => hr i (Finset.mem_insert_of_mem hi)))]
    rw [ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_QuantitativePhysicalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma CompactSmoothPair.smul {r : PhysicalSourcePair} (hr : CompactSmoothPair r) (a : ℝ) :
    CompactSmoothPair (a • r) := by
  intro j
  change ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => a*r j x) ∧ HasCompactSupport (fun x => a*r j x)
  exact ⟨contDiff_const.mul (hr j).1,(hr j).2.mul_left⟩

lemma PairSupported.smul {r : PhysicalSourcePair} {U : Set Coord3} (hr : PairSupported r U) (a : ℝ) :
    PairSupported (a • r) U := by
  intro j
  change tsupport (fun x => a*r j x)⊆U
  exact tsupport_mul_subset_right.trans (hr j)

lemma physicalSourceMoment_smul {u : Coord3 → Fin 2 → ℝ} (r : PhysicalSourcePair) (a : ℝ) :
    physicalSourceMoment u (a • r)=a • physicalSourceMoment u r := by
  have he : (fun x => u x 1*(a • r) 0 x-u x 0*(a • r) 1 x)=
      (fun x => a*(u x 1*r 0 x-u x 0*r 1 x)) := by
    funext x; simp only [Pi.smul_apply,smul_eq_mul]; ring
  ext i
  fin_cases i
  · exact integral_const_mul a (r 0)
  · exact integral_const_mul a (r 1)
  · change (∫ x,u x 1*(a • r) 0 x-u x 0*(a • r) 1 x)=_
    rw [he,integral_const_mul]; rfl

lemma integral_bound_on_compact {K : Set Coord3} (hK : IsCompact K) {f : Coord3 → ℝ}
    (hs : Function.support f⊆K) {C : ℝ} (hb : ∀ x∈K,|f x|≤C) :
    |∫ x,f x|≤C*volume.real K := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => Function.notMem_support.mp (fun h => hx (hs h)))]
  have he := norm_integral_le_of_norm_le_const (μ := volume.restrict K) (f := f) (C := C)
    (ae_restrict_of_forall_mem hK.measurableSet (fun x hx => by simpa only [Real.norm_eq_abs] using hb x hx))
  simpa only [Real.norm_eq_abs,Measure.real,Measure.restrict_apply_univ] using he

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ParametricLocalRegularCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma physicalSourceMoment_parametric_continuous
    {u : P×Coord3 → Fin 2 → ℝ} (hu : Continuous u)
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r) :
    Continuous (fun p => physicalSourceMoment (fun x => u (p,x)) r) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · exact continuous_const
  · let K := tsupport (r 0)∪tsupport (r 1)
    have hK : IsCompact K := (hr 0).2.isCompact.union (hr 1).2.isCompact
    have hcont : Continuous (fun q : P×Coord3 => u q 1*r 0 q.2-u q 0*r 1 q.2) :=
      ((continuous_apply 1|>.comp hu).mul ((hr 0).1.continuous.comp continuous_snd)).sub
        ((continuous_apply 0|>.comp hu).mul ((hr 1).1.continuous.comp continuous_snd))
    have he (p : P) : physicalSourceMoment (fun x => u (p,x)) r 2=
        ∫ x in K,u (p,x) 1*r 0 x-u (p,x) 0*r 1 x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have h0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
      have h1 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
      simp [h0,h1]
    change Continuous (fun p => physicalSourceMoment (fun x => u (p,x)) r 2)
    simp_rw [he]
    exact continuous_parametric_integral_of_continuous hcont hK

theorem parametric_bounded_physical_moments
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P)
    {U O : Set Coord3} (hO : IsOpen O) (hne : O.Nonempty) (hOU : O⊆U)
    (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x)) :
    ∃ (Q : P → Coord3 → PhysicalSourcePair) (L : ℝ),0<L ∧
      (∀ q m,CompactSmoothPair (Q q m)) ∧ (∀ q m,PairSupported (Q q m) O) ∧
      ∀ᶠ q in 𝓝 p, (∀ m,physicalSourceMoment (fun x => u (q,x)) (Q q m)=m) ∧
        ∀ m j,UniformC1Bound (Q q m j) (L*‖m‖) := by
  classical
  have hup : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => u (p,x)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  choose g hg hs hm using fun i : Fin 3 =>
    exists_physical_moments_in_open hup hO hne hOU hD (Pi.single i 1)
  let A : P → Matrix (Fin 3) (Fin 3) ℝ := fun q i j =>
    physicalSourceMoment (fun x => u (q,x)) (g j) i
  have hA : Continuous A := continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).comp (physicalSourceMoment_parametric_continuous hu.continuous (hg j))
  have hAp : A p=1 := by
    ext i j
    simp [A,hm,Pi.single_apply,Matrix.one_apply]
  obtain ⟨C,hC,hnear⟩ := matrix_inverse_locally_bounded hA.continuousAt
    (show IsUnit (A p) by rw [hAp]; exact isUnit_one)
  let Q : P → Coord3 → PhysicalSourcePair := fun q m => ∑ i,((A q)⁻¹*ᵥm) i • g i
  have hQ (q m) : CompactSmoothPair (Q q m) :=
    CompactSmoothPair.sum _ _ (fun i _ => (hg i).smul _)
  have hQs (q m) : PairSupported (Q q m) O :=
    PairSupported.sum _ _ (fun i _ => (hs i).smul _)
  choose B hB hb using fun j : Fin 2 => fun n : Fin 2 =>
    fixed_smooth_tests_bound (fun i : Fin 3 => g i j) (fun i => (hg i j).1) (fun i => (hg i j).2) n.val
  let D := ∑ j : Fin 2,∑ n : Fin 2,B j n
  have hDpos : 0<D := Finset.sum_pos (fun j _ => Finset.sum_pos (fun n _ => hB j n) Finset.univ_nonempty)
    Finset.univ_nonempty
  have hBD (j n) : B j n≤D :=
    (Finset.single_le_sum (fun k _ => (hB j k).le) (Finset.mem_univ n)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => (hB k l).le)) (Finset.mem_univ j))
  refine ⟨Q,D*C,mul_pos hDpos hC,hQ,hQs,?_⟩
  filter_upwards [hnear] with q hq
  constructor
  · intro m
    have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => u (q,x)) :=
      hu.comp (contDiff_const.prodMk contDiff_id)
    change physicalSourceMoment (fun x => u (q,x)) (∑ i,((A q)⁻¹*ᵥm) i • g i)=m
    rw [physicalSourceMoment_sum _ _ huq.continuous (fun i _ => (hg i).smul _)]
    simp_rw [physicalSourceMoment_smul]
    have he := (hq.2 m).1
    ext i
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm,Matrix.mulVec,dotProduct,A] using congrFun he i
  · intro m j x
    have hcoef := (hq.2 m).2
    have h0 := hb j 0 ((A q)⁻¹*ᵥm) (C*‖m‖) (mul_nonneg hC.le (norm_nonneg _)) hcoef x
    have h1 := hb j 1 ((A q)⁻¹*ᵥm) (C*‖m‖) (mul_nonneg hC.le (norm_nonneg _)) hcoef x
    simp only [Fin.val_zero,norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h0
    simp only [Fin.val_one,norm_iteratedFDeriv_one] at h1
    have he : Q q m j=(fun x => ∑ i,((A q)⁻¹*ᵥm) i • g i j x) := by
      funext x; simp [Q,Finset.sum_apply]
    rw [he]
    have hmul (n) : B j n*(C*‖m‖)≤(D*C)*‖m‖ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hBD j n) (mul_nonneg hC.le (norm_nonneg _))
    exact ⟨h0.trans (hmul 0),h1.trans (hmul 1)⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ParametricCorrectionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma parametric_physical_source_moment_bound
    {u : P×Coord3 → Fin 2 → ℝ} (hu : Continuous u) (p : P) {V : Set Coord3}
    (hV : Bornology.IsBounded V) :
    ∃ L : ℝ,0<L ∧ ∀ᶠ q in 𝓝 p,∀ r : PhysicalSourcePair,PairSupported r V →
      ∀ M : ℝ,0≤M → (∀ j x,|r j x|≤M) →
      ‖physicalSourceMoment (fun x => u (q,x)) r‖≤L*M := by
  let K := closure V
  have hK : IsCompact K := hV.isCompact_closure
  obtain ⟨B,hB⟩ := ((isCompact_closedBall p 1).prod hK).exists_bound_of_continuousOn hu.continuousOn
  let A := |B|+1
  let W := volume.real K
  have hA : 0<A := by dsimp [A]; positivity
  have hW : 0≤W := ENNReal.toReal_nonneg
  refine ⟨(1+2*A)*(W+1),by positivity,?_⟩
  filter_upwards [Metric.ball_mem_nhds p zero_lt_one] with q hq
  intro r hs M hM hb
  have huB (x) (hx : x∈K) (j : Fin 2) : |u (q,x) j|≤A :=
    (norm_le_pi_norm (u (q,x)) j).trans
      ((hB (q,x) ⟨Metric.ball_subset_closedBall hq,hx⟩).trans (by dsimp [A]; linarith [le_abs_self B]))
  have hrK (j) : tsupport (r j)⊆K := (hs j).trans subset_closure
  have hi (j) : |∫ x,r j x|≤M*W :=
    integral_bound_on_compact hK ((subset_tsupport _).trans (hrK j)) (fun x _ => hb j x)
  have htK : Function.support (fun x => u (q,x) 1*r 0 x-u (q,x) 0*r 1 x)⊆K := by
    intro x hx
    by_contra hn
    have h0 := image_eq_zero_of_notMem_tsupport (fun h => hn (hrK 0 h))
    have h1 := image_eq_zero_of_notMem_tsupport (fun h => hn (hrK 1 h))
    exact hx (by simp [h0,h1])
  have ht : |∫ x,u (q,x) 1*r 0 x-u (q,x) 0*r 1 x|≤(2*A*M)*W := by
    apply integral_bound_on_compact hK htK
    intro x hx
    calc
      _ ≤ |u (q,x) 1*r 0 x|+|u (q,x) 0*r 1 x| := abs_sub _ _
      _ ≤ A*M+A*M := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul (huB x hx 1) (hb 0 x) (abs_nonneg _) hA.le)
          (mul_le_mul (huB x hx 0) (hb 1 x) (abs_nonneg _) hA.le)
      _ = _ := by ring
  apply pi_norm_le_iff_of_nonneg (by positivity) |>.mpr
  intro j
  have hmass : M*W≤((1+2*A)*(W+1))*M := by
    nlinarith [mul_nonneg hM hW,mul_nonneg hA.le (mul_nonneg hM hW),mul_nonneg hA.le hM]
  have htorque : (2*A*M)*W≤((1+2*A)*(W+1))*M := by
    nlinarith [mul_nonneg hM hW,mul_nonneg hA.le hM]
  fin_cases j
  · exact (hi 0).trans hmass
  · exact (hi 1).trans hmass
  · exact ht.trans htorque

structure ParametricCorrectionBox (u : P×Coord3 → Fin 2 → ℝ) (p : P) (U : Set Coord3) where
  region : Set Coord3
  region_open : IsOpen region
  region_nonempty : region.Nonempty
  region_subset : region⊆U
  region_bounded : Bornology.IsBounded region
  bounded_solver : ∃ L : ℝ,0<L ∧ ∀ᶠ q in 𝓝 p,
    ∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r region →
      physicalSourceMoment (fun x => u (q,x)) r=0 → ∀ M : ℝ,0≤M →
      (∀ j,UniformC1Bound (r j) M) →
      BoundedPhysicallyCorrectable (fun x => u (q,x)) U r (L*M)

lemma ParametricCorrectionBox.bounded_transfer
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (hD : ∀ x∈U,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    (B C : ParametricCorrectionBox u p U) (hBC : (B.region∩C.region).Nonempty) :
    ∃ L : ℝ,0<L ∧ ∀ᶠ t in 𝓝 p,∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r B.region →
      ∀ M : ℝ,0≤M → (∀ j,UniformC1Bound (r j) M) →
      ∃ q : PhysicalSourcePair,CompactSmoothPair q ∧ PairSupported q C.region ∧
        physicalSourceMoment (fun x => u (t,x)) q=physicalSourceMoment (fun x => u (t,x)) r ∧
        (∀ j,UniformC1Bound (q j) (L*M)) ∧
        BoundedPhysicallyCorrectable (fun x => u (t,x)) U (r-q) (L*M) := by
  obtain ⟨Q,R,hR,hQ,hQs,hQnear⟩ := parametric_bounded_physical_moments hu p
    (B.region_open.inter C.region_open) hBC (inter_subset_left.trans B.region_subset) hD
  obtain ⟨Z,hZ,hZnear⟩ := parametric_physical_source_moment_bound hu.continuous p B.region_bounded
  obtain ⟨D,hDpos,hsolve⟩ := B.bounded_solver
  let L := (D+1)*(1+R*Z)
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨L,hL,?_⟩
  filter_upwards [hQnear,hZnear,hsolve] with t ht hZb solve
  intro r hr hs M hM hb
  let v := fun x => u (t,x)
  have hv : ContDiff ℝ (↑(⊤:ℕ∞)) v := hu.comp (contDiff_const.prodMk contDiff_id)
  let q := Q t (physicalSourceMoment v r)
  have hq : CompactSmoothPair q := hQ _ _
  have hqm : physicalSourceMoment v q=physicalSourceMoment v r := ht.1 _
  have hqb (j) : UniformC1Bound (q j) ((R*Z)*M) := (ht.2 _ j).mono
    ((mul_le_mul_of_nonneg_left (hZb r hs M hM (fun j x => (hb j x).1)) hR.le).trans_eq (by ring))
  have hsmall : (R*Z)*M≤L*M := by
    dsimp [L]
    nlinarith [mul_nonneg hR.le hZ.le,mul_nonneg hDpos.le (mul_nonneg hR.le hZ.le)]
  have hrq : CompactSmoothPair (r-q) := hr.sub hq
  have hsrc : physicalSourceMoment v (r-q)=0 := by
    rw [physicalSourceMoment_sub hv.continuous hr hq,hqm,sub_self]
  have hdif (j) : UniformC1Bound ((r-q) j) ((1+R*Z)*M) := by
    change UniformC1Bound (fun x => r j x-q j x) ((1+R*Z)*M)
    convert (hb j).sub ((hr j).1.differentiable (by simp)) ((hq j).1.differentiable (by simp)) (hqb j) using 1 <;> first | rfl | ring
  have hc := solve (r-q) hrq (hs.sub ((hQs t _).mono inter_subset_left)) hsrc
    ((1+R*Z)*M) (by positivity) hdif
  refine ⟨q,hq,(hQs t _).mono inter_subset_right,hqm,fun j => (hqb j).mono hsmall,hc.mono ?_⟩
  dsimp [L]
  nlinarith [mul_nonneg hR.le hZ.le,mul_nonneg (add_nonneg zero_le_one (mul_nonneg hR.le hZ.le)) hM]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_SmoothFamilyCorrectionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def SmoothVanishingPairFamily (p : P) (W : Set Coord3)
    (r : Fin 2 → P×Coord3 → ℝ) : Prop :=
  (∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j)) ∧ (∀ j x,r j (p,x)=0) ∧
    ∃ K : Set Coord3,IsCompact K ∧ K⊆W ∧ ∀ q,PairSupported (fun j x => r j (q,x)) K

namespace SmoothVanishingPairFamily
omit [FiniteDimensional ℝ P]
variable {p : P} {W V : Set Coord3} {r s : Fin 2 → P×Coord3 → ℝ}
lemma compact (hr : SmoothVanishingPairFamily p W r) (q : P) :
    CompactSmoothPair (fun j x => r j (q,x)) := by
  obtain ⟨hsm,_,K,hK,_,hs⟩ := hr
  exact fun j => ⟨(hsm j).comp (contDiff_const.prodMk contDiff_id),
    hK.of_isClosed_subset (isClosed_tsupport _) (hs q j)⟩
end SmoothVanishingPairFamily

structure VanishingCorrectionRegion (u : P×Coord3 → Fin 2 → ℝ) (p : P) (U : Set Coord3) where
  region : Set Coord3
  region_open : IsOpen region
  region_nonempty : region.Nonempty
  region_subset : region⊆U
  region_bounded : Bornology.IsBounded region
  solve : ∀ (r : Fin 2 → P×Coord3 → ℝ),SmoothVanishingPairFamily p region r →
    ∀ ε : ℝ,0<ε → ∀ᶠ q in 𝓝 p,
      physicalSourceMoment (fun x => u (q,x)) (fun j x => r j (q,x))=0 →
      BoundedPhysicallyCorrectable (fun x => u (q,x)) U (fun j x => r j (q,x)) ε

def ParametricCorrectionBox.toVanishing
    {u : P×Coord3 → Fin 2 → ℝ} (p : P) {U : Set Coord3}
    (B : ParametricCorrectionBox u p U) : VanishingCorrectionRegion u p U := by
  refine ⟨B.region,B.region_open,B.region_nonempty,B.region_subset,B.region_bounded,?_⟩
  intro r hr ε hε
  obtain ⟨L,hL,solve⟩ := B.bounded_solver
  obtain ⟨hsm,hz,K,hK,hKW,hs⟩ := hr
  have hsmall (j) := compact_supported_family_C1_small isOpen_univ (mem_univ p)
    (hsm j).contDiffOn hK (Filter.Eventually.of_forall (fun q => hs q j)) (hz j) (div_pos hε hL)
  filter_upwards [solve,Filter.eventually_all.mpr hsmall] with q hq hb hm
  have hrs : CompactSmoothPair (fun j x => r j (q,x)) :=
    SmoothVanishingPairFamily.compact ⟨hsm,hz,K,hK,hKW,hs⟩ q
  have h := hq _ hrs ((hs q).mono hKW) hm (ε/L) (div_pos hε hL).le hb
  simpa only [mul_div_cancel₀ ε hL.ne'] using h

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_WallSideMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

lemma CompactSmoothPair.wallPositiveCut {r : PhysicalSourcePair} (hr : CompactSmoothPair r) (δ : ℝ) :
    CompactSmoothPair (fun j => wallPositiveCut δ (r j)) := fun j =>
  ⟨wallPositiveCut_smooth (hr j).1,(hr j).2.mul_left⟩

lemma PairSupported.wallPositiveCut {r : PhysicalSourcePair} {K : Set Coord3}
    (hr : PairSupported r K) (δ : ℝ) :
    PairSupported (fun j => wallPositiveCut δ (r j)) K := fun j =>
  tsupport_mul_subset_right.trans (hr j)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_FlatBackgroundTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def flatBackgroundTensor (s : Fin 3→ℝ) : Mat3 := !![1,0,0;0,s 0,s 1;0,s 1,s 2]

lemma flatBackgroundTensor_symm (s : Fin 3→ℝ) : (flatBackgroundTensor s).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierMatchingElliptic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise

lemma matrix_quadratic_elementwise_bound (H : Mat3) (v : Coord3) :
    |v ⬝ᵥ (H*ᵥv)| ≤ 3*‖H‖*(v ⬝ᵥ v) := by
  change |∑ i : Fin 3,v i*∑ j : Fin 3,H i j*v j| ≤ _
  simp_rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i : Fin 3,∑ j : Fin 3,|v i*(H i j*v j)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3,∑ j : Fin 3,‖H‖*((v i)^2+(v j)^2)/2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hh : |H i j|≤‖H‖ := by
        change ‖H i j‖≤‖H‖
        exact Matrix.norm_entry_le_entrywise_sup_norm H
      rw [abs_mul,abs_mul]
      have hmul := mul_le_mul_of_nonneg_left hh (mul_nonneg (abs_nonneg (v i)) (abs_nonneg (v j)))
      have hs := mul_nonneg (norm_nonneg H) (sq_nonneg (|v i|-|v j|))
      rw [sub_sq,sq_abs,sq_abs] at hs
      nlinarith
    _ = _ := by simp [Fin.sum_univ_three,dotProduct]; ring

lemma flatBackgroundTensor_lower {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (v : Coord3) :
    (1/2)*(v ⬝ᵥ v) ≤ v ⬝ᵥ (flatBackgroundTensor s*ᵥv) := by
  have h := hs (v 1) (v 2)
  simp [flatBackgroundTensor,dotProduct,Matrix.mulVec,Fin.sum_univ_three] at *
  nlinarith [sq_nonneg (v 0)]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_MeasurableDisjointGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

instance instMeasurableSpaceSymmetric3 : MeasurableSpace Symmetric3 := borel Symmetric3

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactGlobalUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

structure CompactGlobalUpdate (μ : Measure Coord3) (U : Set Coord3)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) where
  du : Coord3 → Fin 2 → ℝ
  dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ
  tensor : Coord3 → Symmetric3
  smooth_du : ContDiff ℝ (↑(⊤ : ℕ∞)) du
  compact_du : HasCompactSupport du
  support_du : tsupport du ⊆ U
  smooth_dF : ContDiff ℝ (↑(⊤ : ℕ∞)) dF
  compact_dF : HasCompactSupport dF
  support_dF : tsupport dF ⊆ U
  cauchy_dF : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
    (∫ x, fderiv ℝ ψ x ((dF x).col j) ∂μ) = 0
  measurable_tensor : Measurable tensor
  constitutive : ∀ x, conductivityFlux (fun y => u y+du y) tensor x = conductivityFlux u A x+dF x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_SmoothFluxIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

lemma smooth_matrix_column {F : Coord3 → Matrix (Fin 3) (Fin 2) ℝ}
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (j : Fin 2) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (F x).col j) := by
  exact contDiff_pi.mpr (fun i => (contDiff_pi.mp (contDiff_pi.mp hF i) j))

lemma compact_matrix_column {F : Coord3 → Matrix (Fin 3) (Fin 2) ℝ}
    (hF : HasCompactSupport F) (j : Fin 2) : HasCompactSupport (fun x => (F x).col j) := by
  apply hF.mono
  intro x hx hzero
  apply hx
  change (F x).col j = 0
  rw [hzero]
  rfl

def CompactGlobalUpdate.trans
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    (S : CompactGlobalUpdate μ U (fun x => u x+R.du x) R.tensor) :
    CompactGlobalUpdate μ U u A where
  du := R.du+S.du
  dF := R.dF+S.dF
  tensor := S.tensor
  smooth_du := R.smooth_du.add S.smooth_du
  compact_du := R.compact_du.add S.compact_du
  support_du := (tsupport_add _ _).trans (union_subset R.support_du S.support_du)
  smooth_dF := R.smooth_dF.add S.smooth_dF
  compact_dF := R.compact_dF.add S.compact_dF
  support_dF := (tsupport_add _ _).trans (union_subset R.support_dF S.support_dF)
  cauchy_dF := by
    intro j ψ hψ
    change (∫ x, fderiv ℝ ψ x ((R.dF x).col j+(S.dF x).col j) ∂μ) = 0
    simp_rw [map_add]
    rw [integral_add (smooth_flux_integrable_pairing μ
      (fun x => (R.dF x).col j) (smooth_matrix_column R.smooth_dF j).continuous (compact_matrix_column R.compact_dF j) ψ hψ)
      (smooth_flux_integrable_pairing μ
      (fun x => (S.dF x).col j) (smooth_matrix_column S.smooth_dF j).continuous (compact_matrix_column S.compact_dF j) ψ hψ),
      R.cauchy_dF j ψ hψ,S.cauchy_dF j ψ hψ,add_zero]
  measurable_tensor := S.measurable_tensor
  constitutive := by
    intro x
    have he : (fun y => u y+(R.du+S.du) y) = (fun y => (u y+R.du y)+S.du y) := by
      funext y; exact (add_assoc _ _ _).symm
    rw [he,S.constitutive x,R.constitutive x]
    exact add_assoc _ _ _

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FieldVectorCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

noncomputable def gradientVectorCLM : (Coord3 →L[ℝ] (Fin 2 → ℝ)) →L[ℝ] FieldVector :=
  ({ toFun := fun D => fieldVector (gradientColumns D)
     map_add' := by intro D E; ext ij; simp [fieldVector,gradientColumns,LinearMap.toMatrix']
     map_smul' := by intro c D; ext ij; simp [fieldVector,gradientColumns,LinearMap.toMatrix'] } :
     (Coord3 →L[ℝ] (Fin 2 → ℝ)) →ₗ[ℝ] FieldVector).toContinuousLinearMap

noncomputable def voltageGradient (u : Coord3 → Fin 2 → ℝ) (x : Coord3) : FieldVector :=
  gradientVectorCLM (fderiv ℝ u x)

noncomputable def voltageFlux (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (x : Coord3) : FieldVector :=
  fieldVector (conductivityFlux u A x)

lemma continuous_voltageGradient {u : Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) : Continuous (voltageGradient u) :=
  gradientVectorCLM.continuous.comp (hu.continuous_fderiv (by simp))

lemma compact_voltageGradient {u : Coord3 → Fin 2 → ℝ} (hc : HasCompactSupport u) :
    HasCompactSupport (voltageGradient u) :=
  (hc.fderiv ℝ).comp_left (map_zero gradientVectorCLM)

lemma memLp_voltageGradient_smooth_compact
    (μ : Measure Coord3) [IsFiniteMeasureOnCompacts μ]
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (hc : HasCompactSupport u) :
    MemLp (voltageGradient u) 2 μ :=
  (continuous_voltageGradient hu).memLp_of_hasCompactSupport (compact_voltageGradient hc)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CompactUpdateLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma CompactGlobalUpdate.memLp_gradient_correction
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) :
    MemLp (voltageGradient R.du) 2 (μ.restrict U) :=
  (memLp_voltageGradient_smooth_compact μ R.smooth_du R.compact_du).restrict U

lemma CompactGlobalUpdate.memLp_flux_correction
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) :
    MemLp (fun x => fieldVector (R.dF x)) 2 (μ.restrict U) :=
  ((R.smooth_dF.continuous.memLp_of_hasCompactSupport R.compact_dF).continuousLinearMap_comp fieldVectorCLM).restrict U

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_Refl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

def CompactGlobalUpdate.refl
    (μ : Measure Coord3) (U : Set Coord3) (u : Coord3 → Fin 2 → ℝ)
    (A : Coord3 → Symmetric3) (hA : Measurable A) : CompactGlobalUpdate μ U u A where
  du := 0
  dF := 0
  tensor := A
  smooth_du := contDiff_const
  compact_du := by simp [HasCompactSupport]
  support_du := by simp
  smooth_dF := contDiff_const
  compact_dF := by simp [HasCompactSupport]
  support_dF := by simp
  cauchy_dF := by
    intro j ψ _
    change (∫ x, fderiv ℝ ψ x (0 : Coord3) ∂μ) = 0
    simp
  measurable_tensor := hA
  constitutive := by intro x; simp only [Pi.zero_apply,add_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_UpdateFieldPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology

def CompactGlobalUpdate.fieldPair
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) :
    Lp FieldVector 2 (μ.restrict U) × Lp FieldVector 2 (μ.restrict U) :=
  (hE.toLp _ + (R.memLp_gradient_correction μ).toLp _,
    hF.toLp _ + (R.memLp_flux_correction μ).toLp _)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_C1VoltageApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped ENNReal Convolution

abbrev CoordBump := ContDiffBump (0 : Coord3)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_TorusEndingCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

structure TorusEndingData (s : Fin 3 → ℝ) (f : Fin 2 → TorusL2) where
  d : ℝ
  e : ℝ
  R : ℝ
  d_pos : 0<d
  e_pos : 0<e
  overlap_lt : d+e<R
  w : WeakFiniteTensorPair {x : Coord3 | d<x 0}
  periodic_v : AngularPeriodic (2*Real.pi) w.v
  periodic_E : AngularPeriodic (2*Real.pi) w.E
  initial_v : ∀ x,x 0∈Icc d (d+e) → w.v x=
    ![x 0+torusRealContinuation s (f 0) x,torusRealContinuation s (f 1) x]
  initial_E : ∀ x,x 0∈Icc d (d+e) → w.E x=flatBackgroundTensor s
  terminal_v : ∀ x,R≤x 0 → w.v x=
    ![x 0+(mFourierCoeff (f 0) 0).re,(mFourierCoeff (f 1) 0).re]
  terminal_E : ∀ x,R≤x 0 → w.E x*ᵥPi.single 0 1=Pi.single 0 1

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusCylinderGreenReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal

variable {F : Coord3 → Coord3}

local instance torusCylinderGreenRealFluxMeasureSpaceUnitAddCircle_r19559c_1 : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
def torusSpectralSynthesis (s : Fin 3 → ℝ) : spectralTraceGraph (torusRate s) →L[ℂ] TorusL2 :=
  ((mFourierBasis (d:=Fin 2)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((PiLp.proj 2 (fun _ : Fin 2 => SpectralL2 TorusModes) 0).comp (spectralTraceGraph (torusRate s)).subtypeL)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralEuclideanBridge
attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

def centralEuclideanCLE : R3 ≃L[ℝ] Box3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).trans boxCoordinates

lemma centralEuclidean_volume : MeasurePreserving centralEuclideanCLE :=
  boxCoordinates_volume.comp (PiLp.volume_preserving_ofLp (Fin 3))

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

def centralHarmonicRegion : Set R3 := {x | centralEuclideanCLE x∈centralClosed ∧
  ∀ (i : Fin 3) y,centralEuclideanCLE x≠centralBoundary i y}

def centralZeroExtension (f : CentralL2) : R3 → ℝ :=
  fun x => centralClosed.indicator f (centralEuclideanCLE x)

lemma centralZeroExtension_memLp (f : CentralL2) : MemLp (centralZeroExtension f) 2 volume :=
  ((memLp_indicator_iff_restrict centralClosed_compact.measurableSet).mpr
    (Lp.memLp f)).comp_measurePreserving centralEuclidean_volume

def centralWholeL2 (f : CentralL2) : WholeL2 :=
  (centralZeroExtension_memLp f).toLp (centralZeroExtension f)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_BranchFiniteEnding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

def branchFinitePair {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) : WeakFiniteTensorPair {x : Coord3 | z.d<x 0} :=
  z.w.output (branchNormalizeEquiv i) 0

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_FlatEndingSplice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

local instance flatEndingSpliceMeasurableSpaceMat3 : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i f))

def branchSplicedTensor (x : Coord3) : Mat3 :=
  if x 0<z.d+5*z.e/8 then flatBackgroundTensor s else (branchFinitePair i z).E x

local instance flatEndingSpliceBorelSpaceMat3_r19559c_1 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
lemma branchSplicedTensor_measurable : Measurable (branchSplicedTensor i z) := by
  exact Measurable.ite (measurableSet_lt (measurable_pi_apply 0) measurable_const)
    measurable_const (branchFinitePair i z).measurable

lemma branchSplicedTensor_symm (x : Coord3) : (branchSplicedTensor i z x).IsSymm := by
  unfold branchSplicedTensor
  split
  · exact flatBackgroundTensor_symm s
  · exact (branchFinitePair i z).symm x

lemma branchSplicedTensor_elliptic
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ c C : ℝ,0 < c ∧ c≤C ∧ ∀ x v,
      c*(v ⬝ᵥ v)≤v ⬝ᵥ(branchSplicedTensor i z x*ᵥv) ∧
        v ⬝ᵥ(branchSplicedTensor i z x*ᵥv)≤C*(v ⬝ᵥ v) := by
  obtain ⟨c,C,hc,hcC,hb⟩ := (branchFinitePair i z).elliptic
  refine ⟨min c (1/2),max C (3*‖flatBackgroundTensor s‖+1),
    lt_min hc (by norm_num),(min_le_left _ _).trans (hcC.trans (le_max_left _ _)),?_⟩
  intro x v
  have hv : 0≤v ⬝ᵥ v := Finset.sum_nonneg (fun k _ => mul_self_nonneg (v k))
  unfold branchSplicedTensor
  split
  · constructor
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hv).trans
        (flatBackgroundTensor_lower hs v)
    · exact ((le_abs_self _).trans (matrix_quadratic_elementwise_bound _ v)).trans
        (mul_le_mul_of_nonneg_right
          ((le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)).trans (le_max_right _ _)) hv)
  · exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hv).trans (hb x v).1,
      (hb x v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalChildTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def sourceChildTensorPush (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => sourceScale⁻¹ *
    A ((sourceChildHomeomorph (actualChildSign k)).symm y) (childAxis i) (childAxis j)

lemma sourceChildTensorPush_symmetric (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ y,(A y).IsSymm) (y : Fin 3 → ℝ) :
    (sourceChildTensorPush k A y).IsSymm := by
  ext i j
  exact congrArg (fun z : ℝ => sourceScale⁻¹*z)
    (congrFun (congrFun (hA ((sourceChildHomeomorph (actualChildSign k)).symm y))
      (childAxis i)) (childAxis j))

lemma sourceChildTensorPush_quadratic (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (y v : Fin 3 → ℝ) :
    v ⬝ᵥ (sourceChildTensorPush k A y*ᵥv)=
      sourceScale⁻¹*((fun i => v (childAxis i)) ⬝ᵥ
        (A ((sourceChildHomeomorph (actualChildSign k)).symm y)*ᵥ
          (fun i => v (childAxis i)))) := by
  simp only [sourceChildTensorPush,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  simp [childAxis]
  ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalEndRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceSmallBand_bounds {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand (-centralThickness) 0) :
    |y 0|≤1602/1000 ∧ |y 1|≤1001/1000 ∧ |y 2|≤1002/1000 := by
  have hh := (sourceCollarTime_ge_iff y (-centralThickness)).mp hy.1
  have hx := (le_max_left (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  have hy' := (le_max_right (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  norm_num [centralThickness,sourceRadialWidth,sourceHole,sourceLength] at hx hy' hh ⊢
  exact ⟨by linarith,by linarith,by linarith [hh.1]⟩

lemma physicalEndRegion_children_disjoint :
    Disjoint (physicalEndRegion 1) (physicalEndRegion 2) := by
  apply disjoint_left.mpr
  intro y h₀ h₁
  have ha := (sourceSmallBand_bounds h₀).2.1
  have hb := (sourceSmallBand_bounds h₁).2.1
  change |(y 0 - actualChildSign 0 * sourceOffset)/sourceScale| ≤ _ at ha
  change |(y 0 - actualChildSign 1 * sourceOffset)/sourceScale| ≤ _ at hb
  norm_num [actualChildSign] at ha hb
  rw [abs_div,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])] at ha hb
  have ha' := abs_le.mp ((div_le_iff₀ (show 0 < sourceScale by norm_num [sourceScale])).mp ha)
  have hb' := abs_le.mp ((div_le_iff₀ (show 0 < sourceScale by norm_num [sourceScale])).mp hb)
  norm_num [sourceScale,sourceOffset] at ha' hb'
  linarith [ha'.1,hb'.2]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalBlockTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceChildTensorPush_norm_bound (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hA : ∀ y,‖A y‖ ≤ B) (y : Fin 3 → ℝ) :
    ‖sourceChildTensorPush k A y‖ ≤ |sourceScale⁻¹| * B := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (abs_nonneg _) hB)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (abs_nonneg _) hB)).mpr
  intro j
  change ‖sourceScale⁻¹*A _ (childAxis i) (childAxis j)‖ ≤ _
  rw [norm_mul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact ((norm_le_pi_norm _ (childAxis j)).trans
    (norm_le_pi_norm _ (childAxis i))).trans (hA _)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FacePasting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix

variable {E : Type*}

def sourceFacePasteList (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (y : Coord3) : E := by
  classical
  exact ks.foldr (fun k z => if y∈sourceFlatPatch k.1 k.2 then B k.1 k.2 y else z) v

lemma sourceFacePasteList_cons (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (k : Fin 4 × Fin 4) (ks : List (Fin 4 × Fin 4)) (y : Coord3) :
    sourceFacePasteList B v (k::ks) y=
      (by classical exact if y∈sourceFlatPatch k.1 k.2 then B k.1 k.2 y else sourceFacePasteList B v ks y) := rfl

lemma sourceFacePasteList_measurable [MeasurableSpace E]
    {B : Fin 4 → Fin 4 → Coord3 → E} (hB : ∀ i j,Measurable (B i j))
    (v : E) (ks : List (Fin 4 × Fin 4)) : Measurable (sourceFacePasteList B v ks) := by
  induction ks with
  | nil => exact measurable_const
  | cons k ks ih =>
    exact Measurable.ite (isCompact_sourceFlatPatch k.1 k.2).measurableSet (hB k.1 k.2) ih

def sourceFacePaste (B : Fin 4 → Fin 4 → Coord3 → E) (v : E) : Coord3 → E :=
  sourceFacePasteList B v (Finset.univ : Finset (Fin 4 × Fin 4)).toList

lemma sourceFacePaste_measurable [MeasurableSpace E]
    {B : Fin 4 → Fin 4 → Coord3 → E} (hB : ∀ i j,Measurable (B i j)) (v : E) :
    Measurable (sourceFacePaste B v) := sourceFacePasteList_measurable hB v _

lemma measurable_sourceCollarInverse (i j : Fin 4) : Measurable (sourceCollarInverse i j) := by
  unfold sourceCollarInverse squareFaceParameter sourceCollarTime sourceCrossCoordinates sourceRadial
  fun_prop

def flatEndCoordinates (a b : ℝ) (x : Coord3) : Coord3 := ![a*(x 0-b),x 1,x 2]

lemma contDiff_flatEndCoordinates (a b : ℝ) : ContDiff ℝ (↑(⊤:ℕ∞)) (flatEndCoordinates a b) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [flatEndCoordinates] <;> fun_prop

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SymmetricQuadraticBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Matrix
open scoped Matrix.Norms.Elementwise

lemma symmetric_matrix_bounded_of_quadratic (A : Mat3) (hA : A.IsSymm)
    {C : ℝ} (hC : 0≤C)
    (hb : ∀ v : Coord3,0≤v ⬝ᵥ(A*ᵥv) ∧ v ⬝ᵥ(A*ᵥv)≤C*‖v‖^2) :
    ‖A‖≤3*C := by
  have hn (i : Fin 3) : ‖(Pi.single i 1 : Coord3)‖=1 := by rw [Pi.norm_single]; norm_num
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤3*C)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤3*C)).mpr
  intro j
  have hi := hb (Pi.single i 1)
  have hj := hb (Pi.single j 1)
  have hij := hb (Pi.single i 1+Pi.single j 1)
  have hnij : ‖(Pi.single i 1+Pi.single j 1 : Coord3)‖≤2 := by
    calc
      _ ≤ ‖(Pi.single i 1 : Coord3)‖+‖(Pi.single j 1 : Coord3)‖ := norm_add_le _ _
      _ = 2 := by rw [hn,hn]; norm_num
  have hnsq : ‖(Pi.single i 1+Pi.single j 1 : Coord3)‖^2≤4 := by
    nlinarith [norm_nonneg (Pi.single i 1+Pi.single j 1 : Coord3)]
  have hsq := mul_le_mul_of_nonneg_left hnsq hC
  have hs : A j i=A i j := congrFun (congrFun hA i) j
  simp only [Matrix.mulVec_add,dotProduct_add,add_dotProduct,
    Matrix.mulVec_single,single_dotProduct,one_mul,
    hn,one_pow,mul_one,Matrix.col_apply,
    show MulOpposite.op (1:ℝ)=(1:ℝᵐᵒᵖ) from rfl,one_smul] at hi hj hij
  rw [hs] at hij
  rw [Real.norm_eq_abs,abs_le]
  constructor <;> nlinarith

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_VariableCollarTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise
local instance variableCollarTensorMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

def variableFaceTensor (K : Coord3 → Mat3) (a b : ℝ) (i j : Fin 4) : Coord3 → Mat3 :=
  fun y => attachedVariableTensor
    (fun x => K (flatEndCoordinates a b (sourceFaceAngles i j x))) a i j
      (sourceCollarInverse i j y)

def variableCollarTensor (K : Coord3 → Mat3) (a b : ℝ) : Coord3 → Mat3 :=
  sourceFacePaste (variableFaceTensor K a b) 1

local instance variableCollarTensorBorelSpace_r19559c_1 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
lemma variableFaceTensor_measurable {K : Coord3 → Mat3} (hK : Measurable K)
    (a b : ℝ) (i j : Fin 4) : Measurable (variableFaceTensor K a b i j) := by
  apply (attachedVariableTensor_measurable
    (hK.comp ((contDiff_flatEndCoordinates a b).continuous.measurable.comp
      (show Differentiable ℝ (sourceFaceAngles i j) from
        fun x => (sourceFaceAngles_hasFDeriv i j x).differentiableAt).continuous.measurable)) a i j).comp
    (measurable_sourceCollarInverse i j)

lemma variableCollarTensor_measurable {K : Coord3 → Mat3} (hK : Measurable K)
    (a b : ℝ) : Measurable (variableCollarTensor K a b) :=
  sourceFacePaste_measurable (variableFaceTensor_measurable hK a b) 1

lemma variableFaceTensor_symm {K : Coord3 → Mat3} (hK : ∀ x,(K x).IsSymm)
    (a b : ℝ) (i j : Fin 4) (y : Coord3) :
    (variableFaceTensor K a b i j y).IsSymm :=
  attachedVariableTensor_symmetric (fun _ => hK _) a i j _

lemma sourceFacePasteList_symm {B : Fin 4 → Fin 4 → Coord3 → Mat3}
    (hB : ∀ i j y,(B i j y).IsSymm) (ks : List (Fin 4 × Fin 4)) (y : Coord3) :
    (sourceFacePasteList B 1 ks y).IsSymm := by
  induction ks with
  | nil => exact Matrix.transpose_one
  | cons k ks ih =>
    rw [sourceFacePasteList_cons]
    split_ifs
    · exact hB _ _ _
    · exact ih

lemma variableCollarTensor_symm {K : Coord3 → Mat3} (hK : ∀ x,(K x).IsSymm)
    (a b : ℝ) (y : Coord3) : (variableCollarTensor K a b y).IsSymm :=
  sourceFacePasteList_symm (variableFaceTensor_symm hK a b) _ y

lemma sourceFacePasteList_elliptic {B : Fin 4 → Fin 4 → Coord3 → Mat3}
    (hB : ∀ i j,∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ y∈sourceFlatPatch i j,∀ v : Coord3,
      c*‖v‖^2≤v ⬝ᵥ(B i j y*ᵥv) ∧ v ⬝ᵥ(B i j y*ᵥv)≤C*‖v‖^2)
    (ks : List (Fin 4 × Fin 4)) :
    ∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ y (v : Coord3),
      c*‖v‖^2≤v ⬝ᵥ(sourceFacePasteList B 1 ks y*ᵥv) ∧
        v ⬝ᵥ(sourceFacePasteList B 1 ks y*ᵥv)≤C*‖v‖^2 := by
  induction ks with
  | nil =>
    obtain ⟨c,C,hc,hcC,h⟩ := identity_matrix_energy_bounds
    exact ⟨c,C,hc,hcC,fun _ => h⟩
  | cons k ks ih =>
    obtain ⟨c,C,hc,hcC,h⟩ := ih
    obtain ⟨d,D,hd,hdD,hk⟩ := hB k.1 k.2
    refine ⟨min c d,max C D,lt_min hc hd,
      lt_of_le_of_lt (min_le_left _ _) (hcC.trans_le (le_max_left _ _)),?_⟩
    intro y v
    rw [sourceFacePasteList_cons]
    split_ifs with hy
    · exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans (hk y hy v).1,
        (hk y hy v).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))⟩
    · exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans (h y v).1,
        (h y v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩

lemma variableCollarTensor_elliptic {K : Coord3 → Mat3} {c C : ℝ}
    (hc : 0 < c) (hcC : c≤C)
    (hK : ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K x*ᵥv) ∧ v ⬝ᵥ(K x*ᵥv)≤C*(v ⬝ᵥ v))
    {a : ℝ} (ha : a≠0) (b : ℝ) :
    ∃ l L : ℝ,0<l ∧ l<L ∧ ∀ y (v : Coord3),
      l*‖v‖^2≤v ⬝ᵥ(variableCollarTensor K a b y*ᵥv) ∧
        v ⬝ᵥ(variableCollarTensor K a b y*ᵥv)≤L*‖v‖^2 := by
  apply sourceFacePasteList_elliptic
  intro i j
  obtain ⟨l,L,hl,hlL,h⟩ := attachedVariableTensor_elliptic hc hcC
    (fun x v => hK (flatEndCoordinates a b (sourceFaceAngles i j x)) v) ha i j
  refine ⟨l,L,hl,hlL,?_⟩
  rintro _ ⟨x,hx,rfl⟩ v
  simpa only [variableFaceTensor,sourceCollarInverse_extended i j (le_refl _) (le_refl _) hx]
    using h x hx v

lemma variableCollarTensor_bounded {K : Coord3 → Mat3} (hS : ∀ x,(K x).IsSymm)
    {c C : ℝ} (hc : 0 < c) (hcC : c≤C)
    (hK : ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K x*ᵥv) ∧ v ⬝ᵥ(K x*ᵥv)≤C*(v ⬝ᵥ v))
    {a : ℝ} (ha : a≠0) (b : ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ y,‖variableCollarTensor K a b y‖≤B := by
  obtain ⟨l,L,hl,hlL,h⟩ := variableCollarTensor_elliptic hc hcC hK ha b
  refine ⟨3*L,mul_pos (by norm_num) (hl.trans hlL),fun y => ?_⟩
  exact symmetric_matrix_bounded_of_quadratic _ (variableCollarTensor_symm hS a b y)
    (hl.trans hlL).le (fun v => ⟨(mul_nonneg hl.le (sq_nonneg _)).trans (h y v).1,(h y v).2⟩)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTraceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma sourcePhysicalEnergy_jet_le (φ : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) :
    sourcePhysicalEnergy φ y ≤ 192*‖piSmoothJet φ y‖^2 := by
  have hb := linear_three_bound (fderiv ℝ φ y)
  have hsingle (i : Fin 3) : (Pi.single i (1:ℝ) : Fin 3 → ℝ)=
      ![![1,0,0],![0,1,0],![0,0,1]] i := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp
  rw [piSmoothJet,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succ,Fin.sum_univ_three]
  simp only [Fin.cases_zero,Fin.cases_succ,Real.norm_eq_abs,sq_abs,
    hsingle,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  dsimp [sourcePhysicalEnergy]
  change 64*‖fderiv ℝ φ y‖^2+2*(φ y)^2 ≤
    192*((φ y)^2+((fderiv ℝ φ y ![1,0,0])^2+
      (fderiv ℝ φ y ![0,1,0])^2+(fderiv ℝ φ y ![0,0,1])^2))
  nlinarith [sq_nonneg (φ y)]

lemma physical_smooth_energy_bound {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) {D : Set (Fin 3 → ℝ)}
    (hD : IsCompact D) (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) :
    (∫ y in D,sourcePhysicalEnergy φ y) ≤
      (192*‖physicalRestrictedJetCLM D‖^2)*‖piSmoothH1 hφ‖^2 := by
  let z := physicalRestrictedJetCLM D (piSmoothH1 hφ)
  have he : (∫ y in D,‖piSmoothJet φ y‖^2)=‖z‖^2 := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [physicalRestrictedJet_smooth_ae hφ hD.measurableSet hb] with y hy
    rw [hy,real_inner_self_eq_norm_sq]
  have hi : Integrable (fun y => ‖piSmoothJet φ y‖^2) (volume.restrict D) := by
    apply Integrable.congr (L2.integrable_inner z z)
    filter_upwards [physicalRestrictedJet_smooth_ae hφ hD.measurableSet hb] with y hy
    rw [hy,real_inner_self_eq_norm_sq]
  have hh := integral_mono
    ((continuous_sourcePhysicalEnergy hφ).continuousOn.integrableOn_compact hD)
    (hi.const_mul 192) (sourcePhysicalEnergy_jet_le φ)
  rw [integral_const_mul,he] at hh
  have hn := (physicalRestrictedJetCLM D).le_opNorm (piSmoothH1 hφ)
  exact hh.trans (by nlinarith [sq_nonneg (‖physicalRestrictedJetCLM D‖*‖piSmoothH1 hφ‖-‖z‖),
    mul_self_le_mul_self (norm_nonneg z) hn])

end ScalarConductivity

end


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

lemma physicalOuter_smooth_sq_bound (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (φ : (Fin 3 → ℝ) → ℝ)
      (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ),
      (∫ θ : UnitAddTorus (Fin 2), (φ (physicalOuterBoundary i θ))^2)≤C*‖piSmoothH1 hφ‖^2 := by
  let A : ℝ := (1+1/centralThickness)*physicalRayConstant
  have hA : 0≤A := by have := physicalRayConstant_pos; dsimp [A,centralThickness]; positivity
  refine Fin.cases ?_ (fun k => ?_) i
  · refine ⟨A*(192*‖physicalRestrictedJetCLM (physicalEndRegion 0)‖^2),by positivity,fun φ hφ => ?_⟩
    have ht := sourceAngular_physical_trace_forward hφ (physicalEndRegion_compact 0) 0
      (η:=centralThickness) (by norm_num [centralThickness]) (by norm_num)
      (by norm_num [centralThickness]) (fun i j => by
        simpa only [zero_add, physicalEndRegion, Fin.cases_zero] using sourceCollarClosedPiece_subset
          (by norm_num : -(1:ℝ)/100≤0) (by norm_num [centralThickness] : centralThickness≤1/100) i j)
    have he := physical_smooth_energy_bound hφ (physicalEndRegion_compact 0)
      (fun _ => physicalEndRegion_subset_ball 0)
    change (∫ θ : UnitAddTorus (Fin 2), (φ (sourceAngularCollar 0 θ))^2) ≤ _
    calc
      _ ≤ A * (∫ y in physicalEndRegion 0, sourcePhysicalEnergy φ y) := ht
      _ ≤ A * (192*‖physicalRestrictedJetCLM (physicalEndRegion 0)‖^2*‖piSmoothH1 hφ‖^2) :=
        mul_le_mul_of_nonneg_left he hA
      _ = _ := by ring
  · let σ := actualChildSign k
    let D := sourceClosedCollarBand (-centralThickness) 0
    have hD : IsCompact D := isCompact_sourceClosedCollarBand
      (by norm_num [centralThickness]) (by norm_num)
    have hσ : 0 < sourceScale^3 := by norm_num [sourceScale]
    refine ⟨A*((sourceScale^3)⁻¹*(192*‖physicalRestrictedJetCLM (physicalEndRegion k.succ)‖^2)),
      by positivity,fun φ hφ => ?_⟩
    have hfc := hφ.comp (sourceChildCoordinates_contDiff σ)
    have ht := sourceAngular_physical_trace_backward hfc hD 0
      (η:=centralThickness) (by norm_num [centralThickness])
      (by norm_num [centralThickness]) (by norm_num) (fun i j => by
        simpa only [zero_sub] using sourceCollarClosedPiece_subset
          (by norm_num [centralThickness] : -(1:ℝ)/100≤ -centralThickness)
          (by norm_num : (0:ℝ)≤1/100) i j)
    have hm : (∫ y in D, sourcePhysicalEnergy (φ ∘ sourceChildCoordinates σ) y)≤
        ∫ y in D,sourcePhysicalEnergy φ (sourceChildCoordinates σ y) := by
      apply integral_mono
        ((continuous_sourcePhysicalEnergy hfc).continuousOn.integrableOn_compact hD)
        (((continuous_sourcePhysicalEnergy hφ).comp (sourceChildCoordinates_contDiff σ).continuous).continuousOn.integrableOn_compact hD)
        (sourceChild_energy hφ σ)
    have hp : sourceChildCoordinates σ ⁻¹' physicalEndRegion k.succ=D := by
      ext y
      change ((sourceChildHomeomorph σ).symm (sourceChildHomeomorph σ y)∈D)↔y∈D
      rw [Homeomorph.symm_apply_apply]
    have hh := integral_sourceChild_preimage σ (physicalEndRegion_compact k.succ) (sourcePhysicalEnergy φ)
    rw [hp] at hh
    rw [hh] at hm
    have he := physical_smooth_energy_bound hφ (physicalEndRegion_compact k.succ)
      (fun _ => physicalEndRegion_subset_ball k.succ)
    have he' := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hσ.le)
    change (∫ θ : UnitAddTorus (Fin 2), ((φ ∘ sourceChildCoordinates σ) (sourceAngularCollar 0 θ))^2) ≤ _
    calc
      _ ≤ A * (∫ y in D, sourcePhysicalEnergy (φ ∘ sourceChildCoordinates σ) y) := ht
      _ ≤ A * ((sourceScale^3)⁻¹*(192*‖physicalRestrictedJetCLM (physicalEndRegion k.succ)‖^2*‖piSmoothH1 hφ‖^2)) :=
        mul_le_mul_of_nonneg_left (hm.trans he') hA
      _ = _ := by ring

def smoothPiH1L : SmoothScalar (Fin 3 → ℝ) →ₗ[ℝ] H1 where
  toFun f := piSmoothH1 (smoothScalar_contDiff f)
  map_add' f g := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [piSmoothH1_jet (smoothScalar_contDiff (f+g)),
      piSmoothH1_jet (smoothScalar_contDiff f),piSmoothH1_jet (smoothScalar_contDiff g),
      Lp.coeFn_add (piSmoothH1 (smoothScalar_contDiff f)).val (piSmoothH1 (smoothScalar_contDiff g)).val]
      with x hfg hf hg ha
    change (piSmoothH1 (smoothScalar_contDiff (f+g))).val x =
      ((piSmoothH1 (smoothScalar_contDiff f)).val + (piSmoothH1 (smoothScalar_contDiff g)).val) x
    rw [ha,hfg]
    simp only [Pi.add_apply]
    rw [hf,hg]
    ext i
    refine Fin.cases rfl (fun j => ?_) i
    change fderiv ℝ (f.val+g.val) _ (Pi.single j 1)=_
    rw [fderiv_add ((smoothScalar_contDiff f).differentiable (by simp) _)
      ((smoothScalar_contDiff g).differentiable (by simp) _)]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [piSmoothH1_jet (smoothScalar_contDiff (c•f)),
      piSmoothH1_jet (smoothScalar_contDiff f),
      Lp.coeFn_smul c (piSmoothH1 (smoothScalar_contDiff f)).val] with x hcf hf ha
    change (piSmoothH1 (smoothScalar_contDiff (c•f))).val x =
      (c • (piSmoothH1 (smoothScalar_contDiff f)).val) x
    rw [ha,hcf]
    simp only [Pi.smul_apply]
    rw [hf]
    ext i
    refine Fin.cases rfl (fun j => ?_) i
    change fderiv ℝ (c•f.val) _ (Pi.single j 1)=_
    rw [fderiv_const_smul ((smoothScalar_contDiff f).differentiable (by simp) _) c]
    rfl

lemma smoothPiH1L_dense : DenseRange smoothPiH1L := by
  apply smoothH1_dense.mono
  rintro u ⟨f,hf,hm,he⟩
  let q : SmoothScalar (Fin 3 → ℝ) := ⟨f ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm,
    hf.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff⟩
  refine ⟨q,?_⟩
  apply Subtype.ext
  change (smoothJet_memLp ((smoothScalar_contDiff q).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff)).toLp _=u.val
  rw [he]
  apply Lp.ext
  filter_upwards [(smoothJet_memLp ((smoothScalar_contDiff q).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff)).coeFn_toLp,hm.coeFn_toLp] with x hq hf'
  rw [hq,hf']
  congr 1

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalOuterTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_9
attribute [local instance] OAI.ScalarConductivity.instIsProbabilityMeasureUnitAddCircleVolume_solutions_9
lemma smoothOuterFourierL_sq (i : Fin 3) (φ : SmoothScalar (Fin 3 → ℝ)) :
    ‖smoothOuterFourierL i φ‖^2=∫ θ : UnitAddTorus (Fin 2),(φ.val (physicalOuterBoundary i θ))^2 := by
  change ‖(mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ (smoothOuterContinuousL i φ))‖^2=_
  rw [LinearIsometryEquiv.norm_map,←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (smoothOuterContinuousL i φ) (p:=2) (μ:=volume) (𝕜:=ℂ)] with θ hθ
  rw [hθ,real_inner_self_eq_norm_sq]
  simp [smoothOuterContinuousL,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma smoothOuterFourierL_bound (i : Fin 3) :
    ∃ C : ℝ,∀ φ,‖smoothOuterFourierL i φ‖≤C*‖smoothPiH1L φ‖ := by
  obtain ⟨C,hC,hb⟩ := physicalOuter_smooth_sq_bound i
  refine ⟨Real.sqrt C,fun φ => ?_⟩
  have hh := hb φ.val (smoothScalar_contDiff φ)
  simp only [volume_pi,unitCircle_volume_eq_haar] at hh
  have hh' : ‖smoothOuterFourierL i φ‖^2≤C*‖smoothPiH1L φ‖^2 := by
    rw [smoothOuterFourierL_sq]
    exact hh
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
  simpa only [mul_pow,Real.sq_sqrt hC] using hh'

def physicalOuterTraceCLM (i : Fin 3) : H1 →L[ℝ] SpectralL2 TorusModes :=
  (dense_linear_observable_extension smoothPiH1L (smoothOuterFourierL i)
    smoothPiH1L_dense (smoothOuterFourierL_bound i)).choose

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalFiniteEndingData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

structure PhysicalFiniteEndingData (s : Fin 3 → ℝ) where
  p : Fin 2 → centralEnergySpace s
  mean_zero : ∀ j,centralM s (p j)=0
  variational : ∀ j,CentralVariationalEquation s (centralBasisSlopes j) (p j)
  harmonic : ∀ j,WeaklyHarmonicOn
    (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) centralHarmonicRegion
  ending : ∀ i : Fin 3,TorusEndingData s
    (branchNormalize i (fun j => torusSpectralSynthesis s (centralT s i (p j))))

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

def compression (i : Fin 3) : ℝ :=
  if i=0 then -((z.ending i).R+1)/centralThickness else ((z.ending i).R+1)/centralThickness

lemma ending_R_pos (i : Fin 3) : 0<(z.ending i).R := by
  linarith [(z.ending i).d_pos,(z.ending i).e_pos,(z.ending i).overlap_lt]

lemma compression_parent : z.compression 0<0 := by
  rw [compression,ite_eq_left rfl]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by linarith [z.ending_R_pos 0]))
    (by norm_num [centralThickness])

lemma compression_child (k : Fin 2) : 0<z.compression k.succ := by
  rw [compression,ite_eq_right (Fin.succ_ne_zero k)]
  exact div_pos (by linarith [z.ending_R_pos k.succ]) (by norm_num [centralThickness])

lemma compression_ne (i : Fin 3) : z.compression i≠0 :=
  Fin.cases z.compression_parent.ne (fun k => (z.compression_child k).ne') i

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalOpenBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceChild_toLp (σ : ℝ) (y : Fin 3 → ℝ) :
    WithLp.toLp 2 (sourceChildCoordinates σ y)=sourceSimilarity σ (WithLp.toLp 2 y) := by
  ext i
  fin_cases i
  · exact (sourceSimilarity_coord σ (WithLp.toLp 2 y)).1.symm
  · exact (sourceSimilarity_coord σ (WithLp.toLp 2 y)).2.1.symm
  · exact (sourceSimilarity_coord σ (WithLp.toLp 2 y)).2.2.symm

def sourceOpenBlock : Set R3 := sourceDomain \ ⋃ k : Fin 2,
  sourceSimilarity (actualChildSign k) '' closure sourceDomain

lemma sourceOpenBlock_isOpen : IsOpen sourceOpenBlock := by
  apply sourceDomain_isOpen.sdiff
  apply isClosed_iUnion_of_finite
  intro k
  exact ((sourceSimilarity (actualChildSign k)).isClosedMap _ isClosed_closure)

end ScalarConductivity



end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_VariableBlockTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal
local instance variableBlockTensorMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance variableBlockTensorBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

def variableEndTensor (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (i : Fin 3) : Coord3 → Mat3 :=
  Fin.cases (variableCollarTensor (K 0) (a 0) centralThickness)
    (fun k => sourceChildTensorPush k
      (variableCollarTensor (K k.succ) (a k.succ) (-centralThickness))) i

lemma variableEndTensor_properties (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0 < c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) (i : Fin 3) :
    Measurable (variableEndTensor K a i) ∧
      (∀ y,(variableEndTensor K a i y).IsSymm) ∧
      (∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ y (v : Coord3),
        c*‖v‖^2≤v ⬝ᵥ(variableEndTensor K a i y*ᵥv) ∧
          v ⬝ᵥ(variableEndTensor K a i y*ᵥv)≤C*‖v‖^2) ∧
      (∃ B : ℝ,0<B ∧ ∀ y,‖variableEndTensor K a i y‖≤B) := by
  have hp (i : Fin 3) (b : ℝ) :
      Measurable (variableCollarTensor (K i) (a i) b) ∧
      (∀ y,(variableCollarTensor (K i) (a i) b y).IsSymm) ∧
      (∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ y (v : Coord3),
        c*‖v‖^2≤v ⬝ᵥ(variableCollarTensor (K i) (a i) b y*ᵥv) ∧
          v ⬝ᵥ(variableCollarTensor (K i) (a i) b y*ᵥv)≤C*‖v‖^2) ∧
      (∃ B : ℝ,0<B ∧ ∀ y,‖variableCollarTensor (K i) (a i) b y‖≤B) := by
    obtain ⟨c,C,hc,hcC,hb⟩ := (hK i).2.2
    exact ⟨variableCollarTensor_measurable (hK i).1 _ _,variableCollarTensor_symm (hK i).2.1 _ _,
      variableCollarTensor_elliptic hc hcC hb (ha i) b,
      variableCollarTensor_bounded (hK i).2.1 hc hcC hb (ha i) b⟩
  refine Fin.cases (hp 0 centralThickness) (fun k => ?_) i
  have hk := hp k.succ (-centralThickness)
  obtain ⟨c,C,hc,hcC,h⟩ := hk.2.2.1
  obtain ⟨B,hB,hbound⟩ := hk.2.2.2
  have hspos : 0 < sourceScale⁻¹ := by norm_num [sourceScale]
  have hmeas : Measurable (variableEndTensor K a k.succ) := by
    change Measurable (sourceChildTensorPush k _)
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact measurable_const.mul (((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp hk.1)).comp
      (sourceChildHomeomorph (actualChildSign k)).symm.continuous.measurable)
  refine ⟨hmeas,
    sourceChildTensorPush_symmetric k _ hk.2.1,
    ⟨sourceScale⁻¹*c,sourceScale⁻¹*C,mul_pos hspos hc,
      mul_lt_mul_of_pos_left hcC hspos,?_⟩,
    ⟨|sourceScale⁻¹| * B,mul_pos (abs_pos.mpr hspos.ne') hB,
      sourceChildTensorPush_norm_bound k _ hB.le hbound⟩⟩
  intro y v
  change (sourceScale⁻¹*c)*‖v‖^2≤v ⬝ᵥ(sourceChildTensorPush k _ y*ᵥv) ∧
    v ⬝ᵥ(sourceChildTensorPush k _ y*ᵥv)≤(sourceScale⁻¹*C)*‖v‖^2
  rw [sourceChildTensorPush_quadratic]
  have hh := h ((sourceChildHomeomorph (actualChildSign k)).symm y)
    (fun j => v (childAxis j))
  rw [childAxis_pi_norm] at hh
  exact ⟨by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.1 hspos.le,
    by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.2 hspos.le⟩

def variableBlockTensorList (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (is : List (Fin 3))
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := by
  classical
  exact is.foldr (fun i A => if y∈physicalEndRegion i then variableEndTensor K a i y else A) 1

lemma variableBlockTensorList_cons (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (i : Fin 3) (is : List (Fin 3))
    (y : Fin 3 → ℝ) : variableBlockTensorList K a (i::is) y=
      (by classical exact if y∈physicalEndRegion i then variableEndTensor K a i y
        else variableBlockTensorList K a is y) := rfl

lemma variableBlockTensorList_properties (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0 < c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) (is : List (Fin 3)) :
    Measurable (variableBlockTensorList K a is) ∧
      (∀ y,(variableBlockTensorList K a is y).IsSymm) ∧
      (∃ c C : ℝ,0 < c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
        c*‖v‖^2 ≤ v ⬝ᵥ (variableBlockTensorList K a is y*ᵥv) ∧
          v ⬝ᵥ (variableBlockTensorList K a is y*ᵥv) ≤ C*‖v‖^2) ∧
      (∃ B : ℝ,0<B ∧ ∀ y,‖variableBlockTensorList K a is y‖ ≤ B) := by
  classical
  induction is with
  | nil =>
    obtain ⟨c,C,hc,hcC,h⟩ := identity_matrix_energy_bounds
    exact ⟨measurable_const,fun _ => Matrix.transpose_one,
      ⟨c,C,hc,hcC,fun _ => h⟩,
      ⟨‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖+1,by positivity,fun _ => by
        change ‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖ ≤ _; linarith⟩⟩
  | cons i is ih =>
    have hi := variableEndTensor_properties K a hK ha i
    obtain ⟨c,C,hc,hcC,h⟩ := ih.2.2.1
    obtain ⟨d,D,hd,hdD,hlocal⟩ := hi.2.2.1
    obtain ⟨B,hB,hbound⟩ := ih.2.2.2
    obtain ⟨E,hE,hend⟩ := hi.2.2.2
    refine ⟨Measurable.ite (physicalEndRegion_compact i).measurableSet hi.1 ih.1,?_,
      ⟨min c d,max C D,lt_min hc hd,
        lt_of_le_of_lt (min_le_left _ _) (hcC.trans_le (le_max_left _ _)),?_⟩,
      ⟨max B E,hB.trans_le (le_max_left _ _),?_⟩⟩
    · intro y
      rw [variableBlockTensorList_cons]
      split_ifs
      · exact hi.2.1 y
      · exact ih.2.1 y
    · intro y v
      rw [variableBlockTensorList_cons]
      split_ifs with hy
      · exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
          (hlocal y v).1,(hlocal y v).2.trans
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))⟩
      · exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
          (h y v).1,(h y v).2.trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩
    · intro y
      rw [variableBlockTensorList_cons]
      split_ifs
      · exact (hend y).trans (le_max_right _ _)
      · exact (hbound y).trans (le_max_left _ _)

def variableBlockTensor (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) :
    (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  variableBlockTensorList K a (Finset.univ : Finset (Fin 3)).toList

lemma variableBlockTensorList_outside (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (is : List (Fin 3))
    {y : Fin 3 → ℝ} (hy : ∀ i∈is,y∉physicalEndRegion i) :
    variableBlockTensorList K a is y=1 := by
  classical
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [variableBlockTensorList_cons,ite_eq_right (hy i List.mem_cons_self)]
    exact ih (fun j hj => hy j (List.mem_cons_of_mem i hj))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalSplicedGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

def flatTensor (i : Fin 3) : Coord3 → Mat3 := branchSplicedTensor i (z.ending i)

end PhysicalFiniteEndingData
end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
local instance physicalSplicedGreenMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))

def constantTerminalFluxCLM (κ : Fin 3 → ℝ) : H1 →L[ℝ] ℝ :=
  angularArea • ∑ i : Fin 3,κ i •
    (Complex.reCLM.comp ((lp.evalCLM ℂ (fun _ : TorusModes => ℂ) 2 0).restrictScalars ℝ)).comp
      (physicalOuterTraceCLM i)

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

local instance physicalSplicedGreenBorelSpace_r19559c_1 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
lemma flatTensor_properties
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (i : Fin 3) :
    Measurable (z.flatTensor i) ∧ (∀ x,(z.flatTensor i x).IsSymm) ∧
      ∃ c C : ℝ,0 < c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(z.flatTensor i x*ᵥv) ∧
        v ⬝ᵥ(z.flatTensor i x*ᵥv)≤C*(v ⬝ᵥ v) :=
  ⟨branchSplicedTensor_measurable i (z.ending i),branchSplicedTensor_symm i (z.ending i),
    branchSplicedTensor_elliptic i (z.ending i) hs⟩

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_WordGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceChildEuclidean_eq_similarity (σ : ℝ) : sourceChildEuclidean σ=sourceSimilarity σ := by
  apply Homeomorph.ext
  intro x
  exact sourceChild_toLp σ (WithLp.ofLp x)

lemma source_child_closed_subset (k : Fin 2) :
    sourceChildEuclidean (actualChildSign k) '' closure sourceDomain⊆sourceDomain := by
  rw [sourceChildEuclidean_eq_similarity]
  fin_cases k
  · exact source_children_compact_inside.2.2.1
  · exact source_children_compact_inside.2.2.2.1

lemma source_child_closed_disjoint {k l : Fin 2} (h : k≠l) :
    Disjoint (sourceChildEuclidean (actualChildSign k) '' closure sourceDomain)
      (sourceChildEuclidean (actualChildSign l) '' closure sourceDomain) := by
  rw [sourceChildEuclidean_eq_similarity,sourceChildEuclidean_eq_similarity]
  fin_cases k <;> fin_cases l
  · exact (h rfl).elim
  · exact source_children_compact_inside.2.2.2.2
  · exact source_children_compact_inside.2.2.2.2.symm
  · exact (h rfl).elim

def sourceWordMap : SourceWord → R3 ≃ₜ R3
  | [] => Homeomorph.refl R3
  | k::ν => (sourceWordMap ν).trans (sourceChildEuclidean (actualChildSign k))

@[simp] lemma sourceWordMap_nil (x : R3) : sourceWordMap [] x=x := rfl
@[simp] lemma sourceWordMap_cons (k : Fin 2) (ν : SourceWord) (x : R3) :
    sourceWordMap (k::ν) x=sourceChildEuclidean (actualChildSign k) (sourceWordMap ν x) := rfl

lemma sourceWordMap_closed_subset (ν : SourceWord) : sourceWordMap ν '' closure sourceDomain⊆closure sourceDomain := by
  induction ν with
  | nil =>
    rintro _ ⟨x,hx,rfl⟩
    exact hx
  | cons k ν ih =>
    rintro _ ⟨x,hx,rfl⟩
    exact subset_closure (source_child_closed_subset k ⟨sourceWordMap ν x,ih ⟨x,hx,rfl⟩,rfl⟩)

def sourceWordCell (ν : SourceWord) : Set R3 := sourceWordMap ν '' closure sourceDomain

def sourceWordBlock (ν : SourceWord) : Set R3 := sourceWordMap ν '' sourceOpenBlock

lemma sourceWordBlock_subset_cell (ν : SourceWord) : sourceWordBlock ν⊆sourceWordCell ν :=
  image_mono (fun _ h => subset_closure h.1)

lemma sourceWordBlock_isOpen (ν : SourceWord) : IsOpen (sourceWordBlock ν) :=
  (sourceWordMap ν).isOpenMap _ sourceOpenBlock_isOpen

lemma sourceWordCell_cons_subset (k : Fin 2) (ν : SourceWord) :
    sourceWordCell (k::ν)⊆sourceChildEuclidean (actualChildSign k) '' closure sourceDomain := by
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨sourceWordMap ν x,sourceWordMap_closed_subset ν ⟨x,hx,rfl⟩,rfl⟩

lemma sourceWordBlock_cons (k : Fin 2) (ν : SourceWord) :
    sourceWordBlock (k::ν)=sourceChildEuclidean (actualChildSign k) '' sourceWordBlock ν := by
  change (fun x => sourceChildEuclidean (actualChildSign k) (sourceWordMap ν x)) '' sourceOpenBlock =
    sourceChildEuclidean (actualChildSign k) '' (sourceWordMap ν '' sourceOpenBlock)
  exact (image_image _ _ _).symm

lemma sourceWordBlock_nil_cons_disjoint (k : Fin 2) (ν : SourceWord) :
    Disjoint (sourceWordBlock []) (sourceWordBlock (k::ν)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' : x∈sourceOpenBlock := by
    rcases hx with ⟨y,hey,rfl⟩
    exact hey
  apply hx'.2
  apply mem_iUnion.mpr
  refine ⟨k,?_⟩
  rw [←sourceChildEuclidean_eq_similarity]
  exact sourceWordCell_cons_subset k ν (sourceWordBlock_subset_cell _ hy)

lemma sourceWordBlock_disjoint {ν ω : SourceWord} (h : ν≠ω) :
    Disjoint (sourceWordBlock ν) (sourceWordBlock ω) := by
  induction ν generalizing ω with
  | nil =>
    cases ω with
    | nil => exact (h rfl).elim
    | cons k ω => exact sourceWordBlock_nil_cons_disjoint k ω
  | cons k ν ih =>
    cases ω with
    | nil => exact (sourceWordBlock_nil_cons_disjoint k ν).symm
    | cons l ω =>
      by_cases hkl : k=l
      · subst l
        have hn : ν≠ω := fun hn => h (congrArg (List.cons k) hn)
        rw [sourceWordBlock_cons,sourceWordBlock_cons]
        apply Set.disjoint_left.mpr
        rintro x ⟨y,hy,he⟩ ⟨z,hz,hf⟩
        have hez : y=z := (sourceChildEuclidean (actualChildSign k)).injective (he.trans hf.symm)
        subst z
        exact Set.disjoint_left.mp (ih hn) hy hz
      · exact (source_child_closed_disjoint hkl).mono
          ((sourceWordBlock_subset_cell _).trans (sourceWordCell_cons_subset k ν))
          ((sourceWordBlock_subset_cell _).trans (sourceWordCell_cons_subset l ω))

lemma sourceWordBlock_unique {x : R3} {ν ω : SourceWord}
    (hν : x∈sourceWordBlock ν) (hω : x∈sourceWordBlock ω) : ν=ω := by
  by_contra hn
  exact Set.disjoint_left.mp (sourceWordBlock_disjoint hn) hν hω

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalOpenVoltage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

def physicalOpenBlock : Set Coord3 := (WithLp.toLp 2) ⁻¹' sourceOpenBlock

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_CopiedScalarCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

def copiedScalarCoefficient (b : Coord3 → ℝ) (x : R3) : ℝ :=
  1+∑' ν : SourceWord,(sourceWordBlock ν).indicator
    (fun x => b (WithLp.ofLp ((sourceWordMap ν).symm x))-1) x

lemma copiedScalarCoefficient_on (b : Coord3 → ℝ) {ν : SourceWord} {x : R3}
    (hx : x∈sourceWordBlock ν) :
    copiedScalarCoefficient b x=b (WithLp.ofLp ((sourceWordMap ν).symm x)) := by
  rw [copiedScalarCoefficient,tsum_eq_single ν]
  · rw [indicator_of_mem hx]; ring
  · intro ω hω
    apply indicator_of_notMem
    exact fun h => hω (sourceWordBlock_unique h hx)

lemma copiedScalarCoefficient_outside (b : Coord3 → ℝ) {x : R3}
    (hx : ∀ ν : SourceWord,x∉sourceWordBlock ν) : copiedScalarCoefficient b x=1 := by
  simp only [copiedScalarCoefficient,indicator_of_notMem (hx _),tsum_zero,add_zero]

lemma copiedScalarCoefficient_measurable {b : Coord3 → ℝ} (hb : Measurable b) :
    Measurable (copiedScalarCoefficient b) := by
  apply measurable_const.add
  apply Measurable.tsum
  intro ν
  exact ((hb.comp ((PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp
    (sourceWordMap ν).symm.continuous).measurable).sub measurable_const).indicator
      (sourceWordBlock_isOpen ν).measurableSet

lemma copiedScalarCoefficient_bounds {b : Coord3 → ℝ} {c C : ℝ}
    (hb : ∀ y,b y∈Icc c C) (x : R3) :
    copiedScalarCoefficient b x∈Icc (min c 1) (max C 1) := by
  by_cases hx : ∃ ν : SourceWord,x∈sourceWordBlock ν
  · obtain ⟨ν,hν⟩ := hx
    rw [copiedScalarCoefficient_on b hν]
    exact ⟨(min_le_left _ _).trans (hb _).1,(hb _).2.trans (le_max_left _ _)⟩
  · rw [copiedScalarCoefficient_outside b (not_exists.mp hx)]
    exact ⟨min_le_right _ _,le_max_right _ _⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

def SourceSupported (u : H1) : Prop :=
  ∀ᵐ x∂ballMeasure,x∉closure sourceDomain → u.val x=0

def childZeroTransport (k : Fin 2) : H10 →L[ℝ] H10 :=
  (childH10Transport k).codRestrict H10 (childH10Transport_mem_H10 k)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_BranchCombine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

def sourceAveragePush : H10 →L[ℝ] H10 :=
  (2*sourceScale)⁻¹ • (childZeroTransport 0+childZeroTransport 1)

def sourceDifferencePush : H10 →L[ℝ] H10 :=
  sourceScale⁻¹ • (childZeroTransport 0-childZeroTransport 1)

def sourceRatio : ℝ := (2*sourceScale)⁻¹

end

open Set MeasureTheory Filter Topology

def sourceAverageIter (v : H10) : ℕ → H10
  | 0 => v
  | n+1 => sourceAveragePush (sourceAverageIter v n)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_PhysicalMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix UnitAddTorus
attribute [local instance] Classical.propDecidable

structure BoundedRootSources where
  b : Coord3 → ℝ
  measurable_b : Measurable b
  c : ℝ
  C : ℝ
  K : ℝ
  c_pos : 0 < c
  c_lt_C : c<C
  K_pos : 0<K
  bounds : ∀ y,b y∈Icc c C
  W : Fin 2 → H1
  W_H10 : ∀ j,W j∈H10
  W_bound : ∀ j,∀ᵐ x∂ballMeasure,|weakValue (W j) x|≤K
  W_energy : ∀ j,‖weakGradientL (W j)‖^2≤K
  W_support : ∀ j,∀ᵐ x∂ballMeasure,x∉closure sourceDomain →
    weakValue (W j) x=0 ∧ weakGradient (W j) x=0
  W_gradient : ∀ j,∀ᵐ x∂ballMeasure,WithLp.ofLp x∉physicalOpenBlock → weakGradient (W j) x=0
  green : ∀ (a : R3 → ℝ),(∀ᵐ y∂volume.restrict physicalOpenBlock,a (WithLp.toLp 2 y)=b y) →
    ∀ j (h : H1),(∫ x,a x*inner ℝ (weakGradient (W j) x) (weakGradient h x) ∂ballMeasure)=
      constantTerminalFluxCLM (centralBasisSlopes j) h

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_CopiedEnergyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

namespace BoundedRootSources
variable (r : BoundedRootSources)
def coefficient : R3 → ℝ := copiedScalarCoefficient r.b
lemma coefficient_measurable : Measurable r.coefficient := copiedScalarCoefficient_measurable r.measurable_b
lemma coefficient_bound : ∀ᵐ x∂ballMeasure,abs (r.coefficient x) ≤ max r.C 1 :=
  Eventually.of_forall (fun x => by
    change abs (copiedScalarCoefficient r.b x) ≤ max r.C 1
    rw [abs_of_pos ((lt_min r.c_pos (by norm_num)).trans_le (copiedScalarCoefficient_bounds r.bounds x).1)]
    exact (copiedScalarCoefficient_bounds r.bounds x).2)
def form : H1 →L[ℝ] H1 →L[ℝ] ℝ :=
  energyForm r.coefficient r.coefficient_measurable.aestronglyMeasurable (max r.C 1)
    ((by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)) r.coefficient_bound
def root (j : Fin 2) : H10 := ⟨r.W j,r.W_H10 j⟩

def sourceHarmonic (u : H1) : Prop := ∀ v : H10,SourceSupported v.val → r.form v.val u=0

end BoundedRootSources
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

namespace BoundedRootSources
variable (r : BoundedRootSources)

def seed : H10 := (1/(2*angularArea)) • (r.root 0+r.root 1)
def initial : H10 := angularArea⁻¹ • (r.root 0-r.root 1)

def finiteSource (N : ℕ) : H10 :=
  r.initial+sourceDifferencePush (∑ n∈Finset.range N,sourceAverageIter r.seed n)

end BoundedRootSources
end ScalarConductivity

end
end

end OAI
end


