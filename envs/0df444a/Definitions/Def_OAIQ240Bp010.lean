-- Prove2me | Definitions.Def_OAIQ240Bp010
-- name    : OAIQ240Bp010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:51:10.698578+00:00
-- url     : https://prove2.me/theorems/fb0763d2-d699-4c67-a8d1-089686999048
-- title:
--   Definitions bundle OAIQ240Bp010 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 236 declarations of OpenAI's Lean: 132 definitions, 3 inductive types or structures and 101 theorems. The definitions and types are `OAI.PackingSufficiencySupport.CubicModel.cubicBubbleResidual`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative`, `OAI.PackingSufficiencySupport.Hamiltonian.FitsPolar`, `OAI.PackingSufficiencySupport.Hamiltonian.HamiltonianDiskIsotopyFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.HamiltonianDiskIsotopyFamily.refl`, `OAI.PackingSufficiencySupport.Hamiltonian.IsPrimitiveFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.SurfaceMassTransferData`, `OAI.PackingSufficiencySupport.Hamiltonian.affineRectangle`, `OAI.PackingSufficiencySupport.Hamiltonian.affineSphereScale`, `OAI.PackingSufficiencySupport.Hamiltonian.angularReparam`, `OAI.PackingSufficiencySupport.Hamiltonian.angularUnitVector`, `OAI.PackingSufficiencySupport.Hamiltonian.annularCylinderScalar`, `OAI.PackingSufficiencySupport.Hamiltonian.annularMean`, `OAI.PackingSufficiencySupport.Hamiltonian.annularNormalized`, `OAI.PackingSufficiencySupport.Hamiltonian.annularPrimitive`, `OAI.PackingSufficiencySupport.Hamiltonian.annularRadialIntegral`, `OAI.PackingSufficiencySupport.Hamiltonian.annularScalarDescent`, `OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm`, `OAI.PackingSufficiencySupport.Hamiltonian.areaLayerCoordinate`, `OAI.PackingSufficiencySupport.Hamiltonian.baseCoefficient`, `OAI.PackingSufficiencySupport.Hamiltonian.baseShearPrimitiveCoefficient`, `OAI.PackingSufficiencySupport.Hamiltonian.box`, `OAI.PackingSufficiencySupport.Hamiltonian.boxCovectorOperator`, `OAI.PackingSufficiencySupport.Hamiltonian.chartAreaMeasure`, `OAI.PackingSufficiencySupport.Hamiltonian.chartInverseExtension`, `OAI.PackingSufficiencySupport.Hamiltonian.circleAngular`, `OAI.PackingSufficiencySupport.Hamiltonian.compactSurfaceBoxes`, `OAI.PackingSufficiencySupport.Hamiltonian.compactSurfaceFormIntegral`, `OAI.PackingSufficiencySupport.Hamiltonian.compactSurfacePartition`, `OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian`, `OAI.PackingSufficiencySupport.Hamiltonian.complexCartesianLinear`, `OAI.PackingSufficiencySupport.Hamiltonian.complexQuotientGauge`, `OAI.PackingSufficiencySupport.Hamiltonian.complexSphereLift`, `OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase`, `OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhaseLinear`, `OAI.PackingSufficiencySupport.Hamiltonian.coneDenominator`, `OAI.PackingSufficiencySupport.Hamiltonian.curveOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular`, `OAI.PackingSufficiencySupport.Hamiltonian.cylinderAreaForm` and 95 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `BallPacking_Annuli_AnnularCurvaturePrimitive`, `BallPacking_Annuli_AnnularMean`, `BallPacking_Annuli_BaseHorizontalForms`, `BallPacking_Annuli_CircleHandleBump`, `BallPacking_Annuli_CylinderAnnularNormalization`, `BallPacking_Annuli_LayerCoordinates`, `BallPacking_Annuli_QuadricCylinderChart`, `BallPacking_Annuli_SurfacePathPositivity`, `BallPacking_Annuli_SurfaceSuspensionCoefficients`, `BallPacking_BallMaps_SphereCartesianDescent`, `BallPacking_DiskMaps_CompactEmbeddingIsotopy`, `BallPacking_DiskMaps_CubicAreaExhaustion`, `BallPacking_DiskMaps_NormalizedRoundedBoxes`, `BallPacking_DiskMaps_ParameterRelativeDiskMoser`, `BallPacking_DiskMaps_SmoothConvexSelection`, `BallPacking_Forms_HorizontalCoupling`, `BallPacking_Forms_ManifoldExteriorAlgebra`, `BallPacking_Forms_QuadricInfinityPrimitive`, `BallPacking_Hopf_AffineHopfRestriction`, `BallPacking_Hopf_DegreeRelativeShell`, `BallPacking_Kahler_PhaseArea`, `BallPacking_Layers_ConstructedSurfaceLayers`, `BallPacking_Layers_LayerAreaForm`, `BallPacking_Layers_LayerBallEmbedding`, `BallPacking_Layers_PlanarRotation`, `BallPacking_Layers_SmoothFormTransport`, `BallPacking_Moments_PolytopeSlices`, `BallPacking_Moments_RearrangementBounds`, `BallPacking_Normal_TailLineCoordinates`, `BallPacking_Projective_AnnularChartHelpers`, `BallPacking_SurfaceArea_QuadricEndAnnuli`, `BallPacking_SurfaceArea_QuadricEndResidueMass`, `BallPacking_SurfaceArea_SurfaceCutoffDefect`, `BallPacking_SurfaceArea_SurfaceIntegralIndependence`, `BallPacking_SurfaceArea_SurfacePrimitiveOperator`, `BallPacking_Surfaces_DiagonalQuadric`, `BallPacking_Toric_CubicRadialFamilyExtension`, `BallPacking_Toric_RestrictedMassIndependence`.
--
--   **Imports.** It imports the bundles `OAIQ240Bp005`, `OAIQ240Bp006` and `OAIQ240Bp007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp013` and `OAIQ240Bp015`; the statements `OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_radial_exact_moser_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_final_surface_layer_packing_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_isotopy_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_thin_planar_embedding_bp240` and `OAI.PackingSufficiencySupport.Hamiltonian.horizontal_moser_endpoint_bp240`; the proofs of `OAI.PackingSufficiencySupport.Hamiltonian.exists_final_surface_layer_packing_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_isotopy_bp240` and `OAI.PackingSufficiencySupport.Hamiltonian.exists_thin_planar_embedding_bp240`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ240Bp005
import Definitions.Def_OAIQ240Bp006
import Definitions.Def_OAIQ240Bp007

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_DiagonalQuadric
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function

variable {m : ℕ}

namespace NormalChart
variable {a : Fin m → ℂ} (e : NormalChart a)

theorem sliceChart_symm_eq (x : locus a) {t : ℂ} (ht : t∈(e.sliceChart x).target) :
    ((e.sliceChart x).symm t : Affine m)=e.ambient.symm (t,0) := e.sliceInverse_eq x ht

theorem sliceChart_inverse_smooth (x : locus a) :
    ContDiffOn ℂ ∞ (fun t => ((e.sliceChart x).symm t : Affine m)) (e.sliceChart x).target := by
  have hs : ContDiff ℂ ∞ (fun t : ℂ => (t,(0 : Fin m → ℂ))) :=
    contDiff_id.prodMk contDiff_const
  have hc := e.smooth_inverse.comp hs.contDiffOn (mapsTo_preimage _ _)
  exact hc.congr (fun t ht => e.sliceChart_symm_eq x ht)

theorem transition_smooth (x : locus a) (f : NormalChart a) (y : locus a) :
    ContDiffOn ℂ ∞ ((e.sliceChart x).symm.trans (f.sliceChart y))
      ((e.sliceChart x).symm.trans (f.sliceChart y)).source := by
  have hc := (curveCoordinate f.coordinate).contDiff.comp_contDiffOn (e.sliceChart_inverse_smooth x)
  exact hc.mono inter_subset_left

end NormalChart

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Kahler_PhaseArea
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function
open Hamiltonian

 def affinePhase (m : ℕ) : Affine m →L[ℝ] PlanePhase (Option (Fin m)) :=
  ContinuousLinearMap.pi fun j => match j with
    | none => Complex.equivRealProdCLM.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ ℂ (Fin m → ℂ))
    | some j => Complex.equivRealProdCLM.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℂ (Fin m → ℂ)))

@[simp] theorem affinePhase_none (m : ℕ) (z : Affine m) :
    affinePhase m z none=(z.1.re,z.1.im) := rfl
@[simp] theorem affinePhase_some (m : ℕ) (z : Affine m) (j : Fin m) :
    affinePhase m z (some j)=((z.2 j).re,(z.2 j).im) := rfl

 def realPhaseDerivative {m : ℕ} (L : ℂ →L[ℂ] Affine m) :
    (ℝ × ℝ) →L[ℝ] PlanePhase (Option (Fin m)) :=
  (affinePhase m).comp ((L.restrictScalars ℝ).comp Complex.equivRealProdCLM.symm.toContinuousLinearMap)

@[simp] theorem realPhaseDerivative_one {m : ℕ} (L : ℂ →L[ℂ] Affine m) :
    realPhaseDerivative L (1,0)=affinePhase m (L 1) := rfl

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_QuadricInfinityPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_vertical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {ι : Type*} [Fintype ι]

def complexCartesianLinear : (ι → ℂ) ≃ₗ[ℝ] PlanePhase ι where
  toFun z i := ((z i).re,(z i).im)
  invFun z i := ⟨(z i).1,(z i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a z := by ext i <;> simp [Pi.smul_apply]

def complexCartesian : (ι → ℂ) ≃L[ℝ] PlanePhase ι :=
  complexCartesianLinear.toContinuousLinearEquiv

@[simp] theorem complexCartesian_apply (z : ι → ℂ) (i : ι) :
    complexCartesian z i=((z i).re,(z i).im) := rfl

theorem complexCartesian_sq (z : ι → ℂ) :
    phaseSq (complexCartesian z)=∑ i,Complex.normSq (z i) := by
  simp only [phaseSq,phaseDot_apply,complexCartesian_apply,Complex.normSq_apply]

omit [Fintype ι] in
@[simp] theorem complexDiagonal_apply (u z : ι → ℂ) (i : ι) :
    complexDiagonal u z i=u i*z i := rfl

def phaseDiagonal (u : ι → ℂ) : PlanePhase ι →L[ℝ] PlanePhase ι :=
  complexCartesian.toContinuousLinearMap.comp
    ((complexDiagonal u).comp complexCartesian.symm.toContinuousLinearMap)

@[simp] theorem phaseDiagonal_cartesian (u z : ι → ℂ) :
    phaseDiagonal u (complexCartesian z)=complexCartesian (complexDiagonal u z) := by
  simp only [phaseDiagonal,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]

def phaseUnitDiagonal (u : ι → ℂ) (hu : ∀ i,Complex.normSq (u i)=1) :
    PlanePhase ι ≃L[ℝ] PlanePhase ι where
  toLinearEquiv :=
    { toLinearMap := (phaseDiagonal u).toLinearMap
      invFun := phaseDiagonal (fun i => star (u i))
      left_inv := by
        intro z
        obtain ⟨z,rfl⟩ := complexCartesian.surjective z
        change phaseDiagonal (fun i => star (u i)) (phaseDiagonal u (complexCartesian z))=complexCartesian z
        simp only [phaseDiagonal_cartesian]
        congr 1
        ext i
        simp only [complexDiagonal_apply,←mul_assoc,←Complex.normSq_eq_conj_mul_self,hu,
          Complex.ofReal_one,one_mul,Complex.star_def]
      right_inv := by
        intro z
        obtain ⟨z,rfl⟩ := complexCartesian.surjective z
        change phaseDiagonal u (phaseDiagonal (fun i => star (u i)) (complexCartesian z))=complexCartesian z
        simp only [phaseDiagonal_cartesian]
        congr 1
        ext i
        simp only [complexDiagonal_apply,←mul_assoc,Complex.star_def]
        rw [mul_comm (u i),←Complex.normSq_eq_conj_mul_self,hu]
        simp only [Complex.ofReal_one,one_mul] }
  continuous_toFun := (phaseDiagonal u).continuous
  continuous_invFun := (phaseDiagonal (fun i => star (u i))).continuous

@[simp] theorem phaseUnitDiagonal_apply (u : ι → ℂ) (hu : ∀ i,Complex.normSq (u i)=1)
    (z : PlanePhase ι) : phaseUnitDiagonal u hu z=phaseDiagonal u z := rfl

def affineSphereScale (z : ι → ℂ) : ℝ := (Real.sqrt (1+phaseSq (complexCartesian z)))⁻¹

def complexSphereLift (z : ι → ℂ) : Option ι → ℂ := affineSphereScale z • complexAffineLift z

omit [Fintype ι] in
@[simp] theorem complexAffineLift_none (z : ι → ℂ) : complexAffineLift z none=1 := rfl
omit [Fintype ι] in
@[simp] theorem complexAffineLift_some (z : ι → ℂ) (i : ι) : complexAffineLift z (some i)=z i := rfl

omit [Fintype ι] in
@[simp] theorem complexAffineQuotient_lift (z : ι → ℂ) :
    complexAffineQuotient (complexAffineLift z)=z := by ext i; simp [complexAffineQuotient]

end

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem extendManifoldOneForm_inside {U : Set M} {α : ManifoldOneForm E M}
    {x : M} (hx : x ∈ U) : extendManifoldOneForm U α x=α x := by
  classical
  exact Set.indicator_of_mem hx α

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem extendManifoldOneForm_outside {U : Set M} {α : ManifoldOneForm E M}
    {x : M} (hx : x ∉ U) : extendManifoldOneForm U α x=0 := by
  classical
  exact Set.indicator_of_notMem hx α

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_HorizontalCoupling
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {F E V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def globalHorizontalCoupling (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    (Γ : V → ManifoldOneForm E M) : ManifoldTwoForm (E × V) (M × V) := fun x =>
  Ω.bilinearComp (ContinuousLinearMap.snd ℝ E V) (ContinuousLinearMap.snd ℝ E V)+
    manifoldExteriorOneForm (productHorizontalLift Γ) x


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

structure IsPrimitiveFamily (Ω : P → ManifoldTwoForm E M) (α : P → ManifoldOneForm E M) : Prop where
  smooth : SmoothOneFormFamily α
  exterior : ∀ p c y, y ∈ (extChartAt 𝓘(ℝ,E) c).target →
    euclideanExteriorOneForm (chartOneForm (α p) c) y = chartTwoForm (Ω p) c y

end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def manifoldTimePrimitive (Γ : ℝ → ManifoldOneForm E M) (t : ℝ) : ManifoldOneForm E M :=
  fun x => deriv (fun s => Γ s x) t


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

def manifoldWedge (α β : ManifoldOneForm E M) : ManifoldTwoForm E M :=
  fun z => (α z).smulRight (β z)-(β z).smulRight (α z)

@[simp] theorem manifoldWedge_apply (α β : ManifoldOneForm E M) (z : M) (v w : E) :
    manifoldWedge α β z v w=α z v*β z w-β z v*α z w := rfl


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def manifoldScalarDifferential (f : M → ℝ) : ManifoldOneForm E M :=
  mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem chartOneForm_sub (α β : ManifoldOneForm E M) (c : M) (y : E) :
    chartOneForm (α-β) c y=chartOneForm α c y-chartOneForm β c y := by
  apply ContinuousLinearMap.ext
  intro v
  rfl



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldExteriorAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]




def normalizedManifoldPrimitive (Γ : P → ManifoldOneForm E M)
    (β : ManifoldOneForm E M) (a : P → ℝ) (G : P × M → ℝ) (p : P) :
    ManifoldOneForm E M := Γ p-a p • β-manifoldScalarDifferential (fun y => G (p,y))


end


open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def handlePushforwardOneForm (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    (α : ManifoldOneForm E M) : ManifoldOneForm F N :=
  extendManifoldOneForm e.target (manifoldPullbackOneForm (fun _ => α) e.symm 0)



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_AnnularChartHelpers
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators

section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def productVerticalLiouville (Ω : V →L[ℝ] V →L[ℝ] ℝ) : ManifoldOneForm (E × V) (M × V) :=
  manifoldPullbackOneForm (fun _ => linearLiouville Ω) (Prod.snd : M × V → V) 0

def productCouplingPrimitive (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    (Γ : V → ManifoldOneForm E M) : ManifoldOneForm (E × V) (M × V) :=
  productVerticalLiouville Ω+productHorizontalLift Γ

end

section
variable {ι : Type*} [Fintype ι]

def standardLiouville (z : PlanePhase ι) : PlanePhase ι →L[ℝ] ℝ :=
  (1/2:ℝ) • phaseArea z

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def verticalLiouville : ManifoldOneForm (E × PlanePhase ι) (M × PlanePhase ι) :=
  manifoldPullbackOneForm (fun _ => standardLiouville) Prod.snd 0

end

variable {ι : Type*} [Fintype ι]

 def hopfPrimitive (c : ℝ) (z : PlanePhase ι) : PlanePhase ι →L[ℝ] ℝ :=
  (c/(2*phaseSq z)) • phaseArea z

 def hopfForm (c : ℝ) := euclideanExteriorOneForm (hopfPrimitive (ι := ι) c)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfaceIntegralIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory Classical
open scoped ContDiff Manifold Topology ENNReal

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [MeasurableSpace M] [BorelSpace M]

def chartInverseExtension (c : M) (y : Plane) : M :=
  if y ∈ (extChartAt 𝓘(ℝ,Plane) c).target then (extChartAt 𝓘(ℝ,Plane) c).symm y else c

def chartAreaMeasure (c : M) (w : Plane → ℝ) : Measure M :=
  Measure.map (chartInverseExtension c) (volume.withDensity (fun y => ENNReal.ofReal (w y)))

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {I : Type*} {K : Set M}

def partitionChartDensity (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Λ : ManifoldTwoForm Plane M) (i : I) (y : Plane) : ℝ :=
  extendedChartCoefficient (B i).center (fun _ : ℝ => fun x => ρ i x • Λ x) (0,y)

variable [IsManifold 𝓘(ℝ,Plane) ∞ M]

variable [Fintype I] [MeasurableSpace M] [BorelSpace M]

def partitionAreaMeasure (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (Λ : ManifoldTwoForm Plane M) : Measure M :=
  ∑ i, chartAreaMeasure (B i).center (partitionChartDensity B ρ Λ i)

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [MeasurableSpace M] [BorelSpace M]

variable {I : Type*} [Fintype I] {K : Set M}

def restrictedPartitionFormMass (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (C : Set M)
    (Ω : ManifoldTwoForm Plane M) : ℝ :=
  ∑ i, ∫ y in (extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
    (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' C,
    partitionChartDensity B ρ Ω i y

end

end PackingSufficiencySupport.Hamiltonian
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

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open scoped BigOperators
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]

 def compactSurfaceBoxes {D : Set M} (hD : IsCompact D) : Finset (SurfaceCoordinateBox M) :=
  Classical.choose (SurfaceCoordinateBox.finite_partition hD)

 def compactSurfacePartition {D : Set M} (hD : IsCompact D) :
    SmoothPartitionOfUnity (compactSurfaceBoxes hD) 𝓘(ℝ,Plane) M D :=
  Classical.choose (Classical.choose_spec (SurfaceCoordinateBox.finite_partition hD))

 def compactSurfaceFormIntegral {D : Set M} (hD : IsCompact D)
    (Ω : ManifoldTwoForm Plane M) : ℝ :=
  restrictedPartitionFormMass (fun B : compactSurfaceBoxes hD => B.1)
    (compactSurfacePartition hD) D Ω

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialFamilyExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold Filter

def radialAnnulus (r R : ℝ) : Set Plane := {z | r ≤ radiusSq z ∧ radiusSq z≤R}

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricEndAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
  {I : Type*}

structure SurfaceMassTransferData (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M) where
  bump : ∀ i, BoxUnitBump (B i)
  common : BoxUnitBump B₀
  primitive : I → ManifoldOneForm Plane M
  supportSet : I → Set M
  compact_supportSet : ∀ i, IsCompact (supportSet i)
  zero_off : ∀ i x, x ∉ supportSet i → primitive i x=0
  primitive_spec : ∀ i, IsPrimitiveFamily (fun _ : ℝ => (bump i).form-common.form)
    (fun _ : ℝ => primitive i)

end

def fixedCovectorOperator (A : ℝ) (hA : 0<A) (f : Plane → ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  planarCovector (planarPrimitiveX A f (primitiveLineBump A hA) z)
    (planarPrimitiveY A f (primitiveLineBump A hA) z)

def translatedCovectorOperator (A : ℝ) (hA : 0<A) (a : Plane) (f : Plane → ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  fixedCovectorOperator A hA (fun w => f (w+a)) (z-a)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

def boxCovectorOperator (B : SurfaceCoordinateBox M) (Ω : ManifoldTwoForm Plane M) :
    ManifoldOneForm Plane M :=
  chartSupportedOneForm B.center (translatedCovectorOperator B.radius B.radius_pos B.point
    (fun y => extendedChartCoefficient B.center (fun _ : ℝ => Ω) (0,y)))

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfacePrimitiveOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory
open scoped ContDiff Manifold Topology

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
  {I : Type*} [Fintype I] {K : Set M}

def surfaceCovectorOperator (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (D : SurfaceMassTransferData B B₀)
    (Ω : ManifoldTwoForm Plane M) : ManifoldOneForm Plane M :=
  ∑ i, (boxCovectorOperator (B i) ((fun x => ρ i x • Ω x) -
      chartMass (B i).center (fun x => ρ i x • Ω x) • (D.bump i).form) +
    chartMass (B i).center (fun x => ρ i x • Ω x) • D.primitive i)

def surfaceCovectorSupport (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (D : SurfaceMassTransferData B B₀) : Set M :=
  ⋃ i, (B i).compactCarrier ∪ D.supportSet i

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {I : Type*} {K : Set M}

def partitionPiece (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Ω : ManifoldTwoForm Plane M) (i : I) : ManifoldTwoForm Plane M := fun x => ρ i x • Ω x

theorem partitionPiece_smooth [IsManifold 𝓘(ℝ,Plane) ∞ M] (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (i : I) : SmoothTwoForm (partitionPiece ρ Ω i) :=
  ((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ρ i).contMDiff).eval 0

theorem partitionPiece_add (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Ω Λ : ManifoldTwoForm Plane M) (i : I) :
    partitionPiece ρ (Ω+Λ) i = partitionPiece ρ Ω i + partitionPiece ρ Λ i := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact mul_add (ρ i x) (Ω x u v) (Λ x u v)

theorem partitionPiece_smul (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (a : ℝ) (Ω : ManifoldTwoForm Plane M) (i : I) :
    partitionPiece ρ (a • Ω) i = a • partitionPiece ρ Ω i := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change ρ i x * (a * Ω x u v) = a * (ρ i x * Ω x u v)
  ring

theorem partitionPiece_zero (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Ω : ManifoldTwoForm Plane M} (hz : ∀ x, x ∉ K → Ω x=0) (i : I) (x : M)
    (hx : x ∉ K ∩ tsupport (ρ i)) : partitionPiece ρ Ω i x=0 :=
  partitionTwoForm_zero (P := ℝ) ρ (fun _ => hz) i 0 x hx

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {I : Type*} [Fintype I] {K : Set M}

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem partitionFormMass_smul (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (a : ℝ) (Ω : ManifoldTwoForm Plane M) :
    partitionFormMass B ρ (a • Ω) = a * partitionFormMass B ρ Ω := by
  change (∑ i, chartMass (B i).center (partitionPiece ρ (a • Ω) i)) = _
  simp_rw [partitionPiece_smul,chartMass_smul]
  exact (Finset.mul_sum ..).symm

theorem partitionFormMass_add (hK : IsCompact K) (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω Λ : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (hΛ : SmoothTwoForm Λ)
    (hzΩ : ∀ x, x ∉ K → Ω x=0) (hzΛ : ∀ x, x ∉ K → Λ x=0) :
    partitionFormMass B ρ (Ω+Λ) = partitionFormMass B ρ Ω + partitionFormMass B ρ Λ := by
  change (∑ i, chartMass (B i).center (partitionPiece ρ (Ω+Λ) i)) = _
  unfold partitionFormMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [partitionPiece_add]
  exact chartMass_add
    ((partitionPiece_smooth ρ hΩ i).coefficient_integrable (B i).center
      (hK.inter_right (isClosed_tsupport (ρ i))) (fun _ hx => (hρ i hx.2).1) (partitionPiece_zero ρ hzΩ i))
    ((partitionPiece_smooth ρ hΛ i).coefficient_integrable (B i).center
      (hK.inter_right (isClosed_tsupport (ρ i))) (fun _ hx => (hρ i hx.2).1) (partitionPiece_zero ρ hzΛ i))

def surfaceIntegralLinearMap (hK : IsCompact K) (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) :
    smoothSupportedTwoForms (E := Plane) K →ₗ[ℝ] ℝ where
  toFun Ω := partitionFormMass B ρ Ω
  map_add' Ω Λ := partitionFormMass_add hK B ρ hρ (smoothSupportedTwoForms.smooth Ω) (smoothSupportedTwoForms.smooth Λ) (smoothSupportedTwoForms.zero_off Ω) (smoothSupportedTwoForms.zero_off Λ)
  map_smul' a Ω := partitionFormMass_smul B ρ a Ω

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfaceCutoffDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def spatialCutoffDefect (κ : M → ℝ) (α : ManifoldOneForm Plane M) : ManifoldTwoForm Plane M :=
  manifoldExteriorOneForm (fun x => κ x • α x)-(fun x => κ x • manifoldExteriorOneForm α x)

end

end PackingSufficiencySupport.Hamiltonian

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

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

 def partitionOnSubset {I : Type*} {K D : Set M}
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (hDK : D⊆K) :
    SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M D where
  toFun := ρ.toFun
  locallyFinite' := ρ.locallyFinite
  nonneg' := ρ.nonneg
  sum_eq_one' := fun _ hx => ρ.sum_eq_one (hDK hx)
  sum_le_one' := ρ.sum_le_one

variable [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

def surfaceCutoffMass {κ : M → ℝ} (hκc : HasCompactSupport κ)
    (Ω : ManifoldTwoForm Plane M) : ℝ :=
  partitionFormMass (fun b : compactSurfaceBoxes hκc => b.1)
    (compactSurfacePartition hκc) (fun x => κ x • Ω x)

end PackingSufficiencySupport.Hamiltonian

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

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory
open Filter

def squareSqueeze (k : ℝ) (x : Plane) : Plane :=
  (Real.tanh (k*x.1),Real.tanh (k*x.2))

def squeezedDisk (k : ℝ) : Set Plane := squareSqueeze k '' closedRoundDisk 1

def squeezedArea (k : ℝ) : ℝ := (volume (squeezedDisk k)).toReal

def diagonalScale (a b : ℝ) : Plane →L[ℝ] Plane :=
  (a • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (b • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem diagonalScale_apply (a b : ℝ) (x : Plane) :
    diagonalScale a b x = (a*x.1,b*x.2) := rfl

def affineRectangle (c : Plane) (a b : ℝ) (x : Plane) : Plane := c + diagonalScale a b x

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_SmoothConvexSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory

def box (c : Plane) (a b : ℝ) : Set Plane :=
  Icc (c.1-a) (c.1+a) ×ˢ Icc (c.2-b) (c.2+b)

def openBox (c : Plane) (a b : ℝ) : Set Plane :=
  Ioo (c.1-a) (c.1+a) ×ˢ Ioo (c.2-b) (c.2+b)

def roundedMap (k : ℝ) (c : Plane) (a b : ℝ) (x : Plane) : Plane :=
  affineRectangle c a b (squareSqueeze k x)

def roundedBox (k : ℝ) (c : Plane) (a b : ℝ) : Set Plane :=
  roundedMap k c a b '' closedRoundDisk 1


end

open scoped ContDiff Topology
open Set Function MeasureTheory

def FitsPolar (c : Plane) (a b : ℝ) : Prop :=
  0 < c.1-a ∧ c.1+a < 1 ∧ 0 < c.2-b ∧ c.2+b < 1

def polarRoundedMap (k : ℝ) (c : Plane) (a b : ℝ) (x : Plane) : Plane :=
  areaPolar (roundedMap k c a b x)

def polarRoundedDisk (k : ℝ) (c : Plane) (a b : ℝ) : Set Plane :=
  polarRoundedMap k c a b '' closedRoundDisk 1



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CompactEmbeddingIsotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory

def radialArea (x : Plane) : ℝ := Real.pi * radiusSq x

def normalizedPolarMap (k : ℝ) (c : Plane) (a b r : ℝ) : Plane → Plane :=
  polarRoundedMap k c a b ∘ diagonalScale r⁻¹ r⁻¹

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_NormalizedRoundedBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory

def normalizedRoundedMap (k : ℝ) (c : Plane) (a b r : ℝ) : Plane → Plane :=
  roundedMap k c a b ∘ diagonalScale r⁻¹ r⁻¹


end

open scoped ContDiff Topology NNReal
open Set Function MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_ParameterRelativeDiskMoser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def planarHamiltonianField (α : Plane →L[ℝ] ℝ) : Plane := (-α (0,1),α (1,0))

@[simp] theorem planarHamiltonianField_neg_area (v : Plane) :
    planarHamiltonianField (-planarArea v) = v := by
  ext <;> simp [planarHamiltonianField,planarArea_apply]

structure HamiltonianDiskIsotopyFamily (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (R : ℝ) where
  isotopy : SupportedSmoothIsotopyFamily P Plane (roundDisk R)
  symplectic : ∀ y t x v w, planarArea (fderiv ℝ (isotopy.map y t) x v)
    (fderiv ℝ (isotopy.map y t) x w) = planarArea v w
  hamiltonian : (P × ℝ) × Plane → ℝ
  smooth : ContDiff ℝ ∞ hamiltonian
  compact : HasCompactSupport hamiltonian
  support : tsupport hamiltonian ⊆ univ ×ˢ roundDisk R
  flow : ∀ y t x, HasDerivAt (fun s => isotopy.map y s x)
    (planarHamiltonianField (fderiv ℝ (fun z => hamiltonian ((y,t),z))
      (isotopy.map y t x))) t


end

open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_PlanarRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function

def planeRotate (θ : ℝ) (v : Plane) : Plane :=
  (Real.cos θ*v.1-Real.sin θ*v.2,Real.sin θ*v.1+Real.cos θ*v.2)

@[fun_prop] theorem planeRotate_smooth : ContDiff ℝ ∞ (fun p : ℝ × Plane => planeRotate p.1 p.2) := by
  unfold planeRotate
  fun_prop

@[simp] theorem planeRotate_zero (v : Plane) : planeRotate 0 v = v := by
  ext <;> simp [planeRotate]

@[simp] theorem radiusSq_planeRotate (θ : ℝ) (v : Plane) :
    radiusSq (planeRotate θ v) = radiusSq v := by
  unfold radiusSq planeRotate
  nlinarith only [Real.sin_sq_add_cos_sq θ]

@[simp] theorem radialArea_planeRotate (θ : ℝ) (v : Plane) :
    radialArea (planeRotate θ v) = radialArea v := by
  simp [radialArea]

@[fun_prop] theorem radialArea_smooth : ContDiff ℝ ∞ radialArea :=
  contDiff_const.mul radiusSq_smooth


end

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def productForm (A : E →L[ℝ] E →L[ℝ] ℝ) :
    (Plane × E) →L[ℝ] (Plane × E) →L[ℝ] ℝ :=
  planarArea.bilinearComp (ContinuousLinearMap.fst ℝ Plane E) (ContinuousLinearMap.fst ℝ Plane E) +
    A.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E)

@[simp] theorem productForm_apply (A : E →L[ℝ] E →L[ℝ] ℝ) (v w : Plane × E) :
    productForm A v w = planarArea v.1 w.1 + A v.2 w.2 := by simp [productForm]

def oneCovectorForm (A : E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ) (η : E →L[ℝ] ℝ) :
    (Plane × E) →L[ℝ] (Plane × E) →L[ℝ] ℝ :=
  let ds := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane E)
  let dt := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane E)
  let α := η.comp (ContinuousLinearMap.snd ℝ Plane E)
  A.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E) +
    c • (ds.smulRight dt - dt.smulRight ds) + α.smulRight dt - dt.smulRight α

@[simp] theorem oneCovectorForm_apply (A : E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ)
    (η : E →L[ℝ] ℝ) (v w : Plane × E) :
    oneCovectorForm A c η v w = A v.2 w.2 + c*(v.1.1*w.1.2-v.1.2*w.1.1) +
      η v.2*w.1.2-v.1.2*η w.2 := by
  simp [oneCovectorForm,ContinuousLinearMap.smulRight_apply,smul_eq_mul]


end

section
open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def planarProduct (q : Plane ≃ₜ Plane) : (Plane × E) ≃ₜ (Plane × E) :=
  q.prodCongr (Homeomorph.refl E)

@[fun_prop] theorem planarProduct_smooth {q : Plane ≃ₜ Plane} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (planarProduct (E := E) q) :=
  (hq.comp contDiff_fst).prodMk contDiff_snd


end

open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_PolytopeSlices
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical

namespace PackingSufficiencySupport.MomentPolytope
open Comparison
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
variable [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

def coordRearrange (F : C(region b c, ℝ)) : C(region b c, ℝ) :=
  (rearrange (baseRegion b c j) (length b c j) (continuous_length b c j).continuousOn
    (onSlice b c j hb F)).comp ⟨sliceEquiv b c j hb, (sliceEquiv b c j hb).continuous⟩

theorem coordRearrange_convex (F : ConvexMaps (region b c) (convex_region b c)) :
    coordRearrange b c j hb F.val ∈ convexFunctionSet _ (convex_region b c) := by
  let Fs : ConvexMaps (sliceDomain (baseRegion b c j) (length b c j))
      (convex_sliceDomain _ _ (concave_length b c j)) :=
    ⟨onSlice b c j hb F.val, onSlice_convex b c j hb F⟩
  have h := rearrange_convex (baseRegion b c j) (length b c j)
    (continuous_length b c j).continuousOn (concave_length b c j) Fs
  intro x y a d ha hd had
  exact h ((sliceEquiv b c j hb) x) ((sliceEquiv b c j hb) y) a d ha hd had

def coordOperator (F : ConvexMaps (region b c) (convex_region b c)) :
    ConvexMaps (region b c) (convex_region b c) :=
  ⟨coordRearrange b c j hb F.val, coordRearrange_convex b c j hb F⟩

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope
open Comparison MeasureTheory
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
variable [∀ j, Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

def successive : List (Fin m) → ConvexMaps (region b c) (convex_region b c) →
    ConvexMaps (region b c) (convex_region b c)
  | [], F => F
  | j::js, F => successive js (coordOperator b c j hb F)

end PackingSufficiencySupport.MomentPolytope
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RearrangementBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff ENNReal Pointwise Classical
open Comparison MeasureTheory
section
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
variable [∀ j, Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

def fullRearrangement (F : ConvexMaps (region b c) (convex_region b c)) :=
  successive b c hb (List.finRange m) F

end

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function
section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def outerMoments (j : ι) (z : PlanePhase ι) : ι → ℝ :=
  fun i => if i=j then 0 else radialArea (z i)

omit [Fintype ι] in
@[simp] theorem outerMoments_self (j : ι) (z : PlanePhase ι) : outerMoments j z j = 0 := by
  simp [outerMoments]

omit [Fintype ι] in
@[simp] theorem outerMoments_other (j : ι) (z : PlanePhase ι) {i : ι} (hi : i ≠ j) :
    outerMoments j z i = radialArea (z i) := by simp [outerMoments,hi]

@[fun_prop] theorem outerMoments_smooth (j : ι) : ContDiff ℝ ∞ (outerMoments j) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i=j
  · simp only [outerMoments,hi,ite_true, if_true]
    exact contDiff_const
  · simp only [outerMoments,hi,ite_false, if_false]
    exact radialArea_smooth.comp (contDiff_apply ℝ Plane i)

def outerDifferential (j : ι) (z : PlanePhase ι) : PlanePhase ι →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => if i=j then 0 else
    (fderiv ℝ radialArea (z i)).comp (ContinuousLinearMap.proj i))

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

namespace HamiltonianDiskIsotopyFamily

def refl (R : ℝ) : HamiltonianDiskIsotopyFamily P R where
  isotopy := SupportedSmoothIsotopyFamily.refl _
  symplectic := by
    intro y t x v w
    change planarArea (fderiv ℝ id x v) (fderiv ℝ id x w) = planarArea v w
    simp
  hamiltonian := fun _ => 0
  smooth := contDiff_const
  compact := HasCompactSupport.zero
  support := by simp
  flow := by
    intro y t x
    change HasDerivAt (fun _ : ℝ => x) (planarHamiltonianField (fderiv ℝ (fun _ : Plane => (0:ℝ)) x)) t
    have hz : fderiv ℝ (fun _ : Plane => (0:ℝ)) x = 0 :=
      (hasFDerivAt_const (c := (0:ℝ)) x).fderiv
    rw [hz]
    have he : planarHamiltonianField (0 : Plane →L[ℝ] ℝ) = 0 := by ext <;> simp [planarHamiltonianField]
    rw [he]
    exact hasDerivAt_const t x

end HamiltonianDiskIsotopyFamily

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def planeMoments (z : PlanePhase ι) : ι → ℝ := fun i => radialArea (z i)

omit [DecidableEq ι] in
@[fun_prop] theorem planeMoments_smooth : ContDiff ℝ ∞ (planeMoments (ι := ι)) := by
  apply contDiff_pi.mpr
  intro i
  exact radialArea_smooth.comp (contDiff_apply ℝ Plane i)

def momentDifferential (z : PlanePhase ι) : PlanePhase ι →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => (fderiv ℝ radialArea (z i)).comp (ContinuousLinearMap.proj i))

def toricHamiltonian (F : (ι → ℝ) → ℝ) (p : ℝ × PlanePhase ι) : ℝ := F (planeMoments p.2)

omit [DecidableEq ι] in
@[fun_prop] theorem toricHamiltonian_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (toricHamiltonian F) := hF.comp (planeMoments_smooth.comp contDiff_snd)

def toricAngularSpeed (F : (ι → ℝ) → ℝ) (z : PlanePhase ι) (i : ι) : ℝ :=
  2*Real.pi*fderiv ℝ F (planeMoments z) (Pi.single i 1)

@[fun_prop] theorem toricAngularSpeed_smooth {F : (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (i : ι) : ContDiff ℝ ∞ (fun z => toricAngularSpeed F z i) :=
  contDiff_const.mul (((hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp planeMoments_smooth).clm_apply contDiff_const)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_SmoothFormTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff BigOperators
open Set Function

@[simp] theorem planeRotate_comp (s t : ℝ) (z : Plane) :
    planeRotate s (planeRotate t z) = planeRotate (s+t) z := by
  apply Prod.ext <;> dsimp [planeRotate] <;> rw [Real.cos_add,Real.sin_add] <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def toricFlow (F : (ι → ℝ) → ℝ) (t : ℝ) (z : PlanePhase ι) : PlanePhase ι :=
  fun i => planeRotate (t*toricAngularSpeed F z i) (z i)

omit [Fintype ι] in
@[simp] theorem toricFlow_zero (F : (ι → ℝ) → ℝ) (z : PlanePhase ι) : toricFlow F 0 z = z := by
  funext i
  simp [toricFlow]

omit [Fintype ι] in
@[simp] theorem toricFlow_moments (F : (ι → ℝ) → ℝ) (t : ℝ) (z : PlanePhase ι) :
    planeMoments (toricFlow F t z) = planeMoments z := by
  funext i
  exact radialArea_planeRotate _ _

omit [Fintype ι] in
@[simp] theorem toricAngularSpeed_flow (F : (ι → ℝ) → ℝ) (t : ℝ) (z : PlanePhase ι) (i : ι) :
    toricAngularSpeed F (toricFlow F t z) i = toricAngularSpeed F z i := by
  simp [toricAngularSpeed]

omit [Fintype ι] in
theorem toricFlow_add (F : (ι → ℝ) → ℝ) (s t : ℝ) (z : PlanePhase ι) :
    toricFlow F s (toricFlow F t z) = toricFlow F (s+t) z := by
  funext i
  change planeRotate (s*toricAngularSpeed F (toricFlow F t z) i)
    (planeRotate (t*toricAngularSpeed F z i) (z i)) = _
  rw [toricAngularSpeed_flow,planeRotate_comp]
  simp only [toricFlow,add_mul]

omit [DecidableEq ι] in

theorem phase_rotation_smooth {a : ℝ × PlanePhase ι → (ι → ℝ)}
    (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => fun i => planeRotate (a p i) (p.2 i)) := by
  apply contDiff_pi.mpr
  intro i
  have hi : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => a p i) :=
    (contDiff_apply ℝ ℝ i).comp ha
  have hz : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => p.2 i) :=
    (contDiff_apply ℝ Plane i).comp contDiff_snd
  convert! planeRotate_smooth.comp (hi.prodMk hz) using 1
  all_goals try with_reducible_and_instances rfl

theorem toric_flow_angles_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => fun i => p.1*toricAngularSpeed F p.2 i) := by
  apply contDiff_pi.mpr
  intro i
  have ha : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => toricAngularSpeed F p.2 i) :=
    (toricAngularSpeed_smooth hF i).comp contDiff_snd
  exact contDiff_fst.mul ha

@[fun_prop] theorem toricFlow_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => toricFlow F p.1 p.2) := by
  exact phase_rotation_smooth (toric_flow_angles_smooth hF)


end

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def toricFunction (F : (ι → ℝ) → ℝ) (z : PlanePhase ι) : ℝ := F (planeMoments z)

omit [DecidableEq ι] in
@[fun_prop] theorem toricFunction_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (toricFunction F) := hF.comp planeMoments_smooth

def toricSuspension (F : (ι → ℝ) → ℝ) (p : Plane × PlanePhase ι) : Plane × PlanePhase ι :=
  (p.1,toricFlow F p.1.2 p.2)

@[fun_prop] theorem toricSuspension_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (toricSuspension F) := by
  have ht : ContDiff ℝ ∞ (fun p : Plane × PlanePhase ι => p.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hz : ContDiff ℝ ∞ (fun p : Plane × PlanePhase ι => toricFlow F p.1.2 p.2) := by
    convert! (toricFlow_smooth hF).comp (ht.prodMk contDiff_snd) using 1
    all_goals try with_reducible_and_instances rfl
  exact contDiff_fst.prodMk hz


end

section
open scoped ContDiff
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def toricSuspensionInverse (F : (ι → ℝ) → ℝ) (p : Plane × PlanePhase ι) : Plane × PlanePhase ι :=
  (p.1,toricFlow F (-p.1.2) p.2)

@[fun_prop] theorem toricSuspensionInverse_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (toricSuspensionInverse F) := by
  have ht : ContDiff ℝ ∞ (fun p : Plane × PlanePhase ι => -p.1.2) :=
    (contDiff_snd.comp contDiff_fst).neg
  have hz : ContDiff ℝ ∞ (fun p : Plane × PlanePhase ι => toricFlow F (-p.1.2) p.2) := by
    convert! (toricFlow_smooth hF).comp (ht.prodMk contDiff_snd) using 1
    all_goals try with_reducible_and_instances rfl
  exact contDiff_fst.prodMk hz

omit [Fintype ι] in
@[simp] theorem toricSuspensionInverse_left (F : (ι → ℝ) → ℝ) (p : Plane × PlanePhase ι) :
    toricSuspensionInverse F (toricSuspension F p) = p := by
  simp only [toricSuspensionInverse,toricSuspension,toricFlow_add,neg_add_cancel,toricFlow_zero]

omit [Fintype ι] in
@[simp] theorem toricSuspensionInverse_right (F : (ι → ℝ) → ℝ) (p : Plane × PlanePhase ι) :
    toricSuspension F (toricSuspensionInverse F p) = p := by
  simp only [toricSuspensionInverse,toricSuspension,toricFlow_add,add_neg_cancel,toricFlow_zero]

def toricSuspensionHomeomorph {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    (Plane × PlanePhase ι) ≃ₜ (Plane × PlanePhase ι) where
  toFun := toricSuspension F
  invFun := toricSuspensionInverse F
  left_inv := toricSuspensionInverse_left F
  right_inv := toricSuspensionInverse_right F
  continuous_toFun := (toricSuspension_smooth hF).continuous
  continuous_invFun := (toricSuspensionInverse_smooth hF).continuous

omit [Fintype ι] in
@[simp] theorem toricSuspension_moments (F : (ι → ℝ) → ℝ) (p : Plane × PlanePhase ι) :
    planeMoments (toricSuspension F p).2 = planeMoments p.2 := toricFlow_moments F _ _

omit [Fintype ι] in
@[simp] theorem toricSuspensionInverse_moments (F : (ι → ℝ) → ℝ) (p : Plane × PlanePhase ι) :
    planeMoments (toricSuspensionInverse F p).2 = planeMoments p.2 := toricFlow_moments F _ _


end

section
open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def layerOrder : (Plane × E) ≃L[ℝ] ((ℝ × E) × ℝ) :=
  (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ E).trans (ContinuousLinearEquiv.prodComm ℝ ℝ (ℝ × E))

omit [CompleteSpace E] in
@[simp] theorem layerOrder_apply (p : Plane × E) : layerOrder p = ((p.1.2,p.2),p.1.1) := rfl
omit [CompleteSpace E] in
@[simp] theorem layerOrder_symm_apply (p : (ℝ × E) × ℝ) : layerOrder.symm p = ((p.2,p.1.1),p.1.2) := rfl

def stripChart (f : Plane × E → ℝ) (p : Plane × E) : Plane × E := ((f p,p.1.2),p.2)

omit [CompleteSpace E] in
@[fun_prop] theorem stripChart_smooth {f : Plane × E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (stripChart f) := (hf.prodMk (contDiff_snd.comp contDiff_fst)).prodMk contDiff_snd


end

open scoped ContDiff Topology
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def layerChart (F : (ι → ℝ) → ℝ) (f : Plane × PlanePhase ι → ℝ) :
    Plane × PlanePhase ι → Plane × PlanePhase ι := toricSuspension F ∘ stripChart f

@[fun_prop] theorem layerChart_smooth {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (layerChart F f) :=
  (toricSuspension_smooth hF).comp (stripChart_smooth hf)

def layerForm (F : (ι → ℝ) → ℝ) (f : Plane × PlanePhase ι → ℝ)
    (p : Plane × PlanePhase ι) :
    (Plane × PlanePhase ι) →L[ℝ] (Plane × PlanePhase ι) →L[ℝ] ℝ :=
  let dt := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane (PlanePhase ι))
  let β := fderiv ℝ f p + (fderiv ℝ (toricFunction F) p.2).comp (ContinuousLinearMap.snd ℝ Plane (PlanePhase ι))
  phaseArea.bilinearComp (ContinuousLinearMap.snd ℝ Plane (PlanePhase ι))
    (ContinuousLinearMap.snd ℝ Plane (PlanePhase ι)) + β.smulRight dt - dt.smulRight β



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_LayerBallEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology BigOperators
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def splitCapacityBall (r : ℝ) : Set (Plane × PlanePhase ι) :=
  {z | radialArea z.1 + ∑ i, planeMoments z.2 i ≤ r}


end

section
open scoped ContDiff Topology BigOperators
open Set Function

def complexSplitPhaseLinear (m : ℕ) : Ambient (m+1) ≃ₗ[ℝ] Plane × PlanePhase (Fin m) where
  toFun z := (((z 0).re,(z 0).im),fun j => ((z j.succ).re,(z j.succ).im))
  invFun p := Fin.cons (⟨p.1.1,p.1.2⟩ : ℂ) (fun j => (⟨(p.2 j).1,(p.2 j).2⟩ : ℂ))
  left_inv z := by funext i; exact Fin.cases rfl (fun j => rfl) i
  right_inv p := rfl
  map_add' _ _ := rfl
  map_smul' a z := by
    ext <;> simp [Pi.smul_apply]

def complexSplitPhase (m : ℕ) : Ambient (m+1) ≃L[ℝ] Plane × PlanePhase (Fin m) :=
  (complexSplitPhaseLinear m).toContinuousLinearEquiv

@[simp] theorem complexSplitPhase_apply (m : ℕ) (z : Ambient (m+1)) :
    complexSplitPhase m z=(((z 0).re,(z 0).im),fun j => ((z j.succ).re,(z j.succ).im)) := rfl


end

open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_LayerCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory

def layerAreaIntegral (ℓ : Plane → ℝ) (a : ℝ) (q : Plane) : ℝ :=
  ∫ s in a..q.1,ℓ (s,q.2)

variable {ι : Type*} [Fintype ι]

def areaLayerCoordinate (ℓ : Plane → ℝ) (a : ℝ) (ρ : ℝ → ℝ) (H : (ι → ℝ) → ℝ)
    (p : Plane × PlanePhase ι) : ℝ :=
  layerAreaIntegral ℓ a p.1+ρ p.1.1*H (planeMoments p.2)


end

open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def twoCovectorForm (A : E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ)
    (η ζ : E →L[ℝ] ℝ) : (Plane × E) →L[ℝ] (Plane × E) →L[ℝ] ℝ :=
  let ds := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane E)
  let α := η.comp (ContinuousLinearMap.snd ℝ Plane E)
  oneCovectorForm A c ζ + α.smulRight ds - ds.smulRight α

@[simp] theorem twoCovectorForm_apply (A : E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ)
    (η ζ : E →L[ℝ] ℝ) (v w : Plane × E) :
    twoCovectorForm A c η ζ v w = A v.2 w.2 + c*(v.1.1*w.1.2-v.1.2*w.1.1) +
      ζ v.2*w.1.2-v.1.2*ζ w.2 + η v.2*w.1.1-v.1.1*η w.2 := by
  simp [twoCovectorForm,ContinuousLinearMap.smulRight_apply,smul_eq_mul]



def horizontalOneForm (A B : Plane × E → ℝ) (x : Plane × E) :
    (Plane × E) →L[ℝ] ℝ :=
  A x • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane E) +
  B x • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane E)

@[simp] theorem horizontalOneForm_apply (A B : Plane × E → ℝ) (x v : Plane × E) :
    horizontalOneForm A B x v = A x*v.1.1+B x*v.1.2 := by
  simp [horizontalOneForm,smul_eq_mul]

@[fun_prop] theorem horizontalOneForm_smooth {A B : Plane × E → ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (horizontalOneForm A B) :=
  (hA.smul contDiff_const).add (hB.smul contDiff_const)

def horizontalCoupling (Ω : E →L[ℝ] E →L[ℝ] ℝ) (A B : Plane × E → ℝ)
    (x : Plane × E) : (Plane × E) →L[ℝ] (Plane × E) →L[ℝ] ℝ :=
  Ω.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E) +
    euclideanExteriorOneForm (horizontalOneForm A B) x



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_BaseHorizontalForms
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_manifold _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_manifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory
open scoped ContDiff Manifold Topology

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def firstBaseCoefficient (a : ℝ × E → ℝ) (p : Plane × E) : ℝ := a (p.1.1,p.2)

@[fun_prop] theorem firstBaseCoefficient_smooth {a : ℝ × E → ℝ}
    (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (firstBaseCoefficient a) :=
  ha.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)

def baseCoefficient (a : Plane → ℝ) (p : Plane × E) : ℝ := a p.1

@[fun_prop] theorem baseCoefficient_smooth {a : Plane → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (baseCoefficient (E := E) a) := ha.comp contDiff_fst

def weightedSecondCoefficient (b w : Plane → ℝ) (G : ℝ × E → ℝ) (p : Plane × E) : ℝ :=
  b p.1+w p.1*G (p.1.1,p.2)

@[fun_prop] theorem weightedSecondCoefficient_smooth {b w : Plane → ℝ} {G : ℝ × E → ℝ}
    (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (weightedSecondCoefficient b w G) :=
  (baseCoefficient_smooth hb).add ((baseCoefficient_smooth hw).mul (firstBaseCoefficient_smooth hG))

end

def circleAngular : ManifoldOneForm CircleModel Circle :=
  manifoldPullbackOneForm (fun _ => ambientAngular) circleInclusion 0

theorem circleAngular_unit_pullback (t v : ℝ) :
    circleAngular (circleTurn t)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn t v)=v := by
  have hc := mfderiv_comp t
    ((circle_coe_smooth.mdifferentiable (by simp)) (circleTurn t))
    ((circleTurn_smooth.mdifferentiable (by simp)) t)
  simp only [circleAngular,manifoldPullbackOneForm,manifoldMapDifferential]
  change ambientAngular (circleInclusion (circleTurn t))
    (((mfderiv 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℂ) circleInclusion (circleTurn t)).comp
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn t)) v)=v
  rw [← hc,mfderiv_eq_fderiv]
  change ambientAngular (circleTurn t : ℂ)
    (fderiv ℝ (fun s : ℝ => (circleTurn s : ℂ)) t v)=v
  rw [(circleTurn_deriv t).hasFDerivAt.fderiv,ambientAngular_apply]
  have hu : starRingEnd ℂ (circleTurn t : ℂ)*(circleTurn t : ℂ)=1 := by
    rw [← Circle.coe_inv_eq_conj,← Circle.coe_mul,inv_mul_cancel,Circle.coe_one]
  have he : starRingEnd ℂ (circleTurn t : ℂ)*
      (v • ((circleTurn t : ℂ)*((2*Real.pi : ℝ):ℂ)*Complex.I)) =
      (v:ℂ)*((2*Real.pi : ℝ):ℂ)*Complex.I := by
    rw [Complex.real_smul]
    calc
      _ = (v:ℂ)*(starRingEnd ℂ (circleTurn t : ℂ)*(circleTurn t : ℂ))*
          ((2*Real.pi : ℝ):ℂ)*Complex.I := by ring
      _ = _ := by rw [hu,mul_one]
  change (1/(2*Real.pi))*(starRingEnd ℂ (circleTurn t : ℂ)*
    (v • ((circleTurn t : ℂ)*((2*Real.pi : ℝ):ℂ)*Complex.I))).im=v
  rw [he]
  simp only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,mul_one]
  field_simp

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_CircleHandleBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold

def cylinderAngular : ManifoldOneForm CylinderModel HandleCylinder :=
  manifoldPullbackOneForm (fun _ => circleAngular) Prod.snd 0

@[simp] theorem cylinderAngular_apply (z : HandleCylinder) (v : CylinderModel) :
    cylinderAngular z v=circleAngular z.2 v.2 := by
  simp only [cylinderAngular,manifoldPullbackOneForm,manifoldMapDifferential]
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod,mfderiv_snd]
  rfl

def cylinderCover (q : Plane) : HandleCylinder := (q.1,circleTurn q.2)

theorem cylinderCover_smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) ∞ cylinderCover := by
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Plane → ℝ)).contMDiff.prodMk
    (circleTurn_smooth.comp (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Plane → ℝ)).contMDiff)

theorem cylinderCover_derivative (q v : Plane) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v=
      (v.1,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn q.2 v.2) := by
  have hf := (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Plane → ℝ)).contMDiff
  have hs := (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Plane → ℝ)).contMDiff
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  have hd := mfderiv_prodMk (I := 𝓘(ℝ,Plane)) (I' := 𝓘(ℝ,ℝ))
    (I'' := 𝓘(ℝ,CircleModel)) (f := (Prod.fst : Plane → ℝ))
    (g := fun z : Plane => circleTurn z.2) (x := q)
    (hf.mdifferentiableAt (by simp))
    ((circleTurn_smooth.comp hs).mdifferentiableAt (by simp))
  change (mfderiv 𝓘(ℝ,Plane) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel))
    (fun z : Plane => (z.1,circleTurn z.2)) q v)=_
  rw [hd]
  have hc := mfderiv_comp q (circleTurn_smooth.mdifferentiableAt (by simp))
    (I := 𝓘(ℝ,Plane)) (I' := 𝓘(ℝ,ℝ)) (I'' := 𝓘(ℝ,CircleModel))
    (f := (Prod.snd : Plane → ℝ)) (hs.mdifferentiableAt (by simp))
  change ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) Prod.fst q) v,
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CircleModel) (circleTurn ∘ Prod.snd) q) v)=_
  rw [hc,mfderiv_eq_fderiv,mfderiv_eq_fderiv,fderiv_fst,fderiv_snd]
  rfl

@[simp] theorem cylinderAngular_cover (q v : Plane) :
    cylinderAngular (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v)=v.2 := by
  erw [cylinderCover_derivative,cylinderAngular_apply]
  exact circleAngular_unit_pullback q.2 v.2

def weightedCylinderAngular (f : HandleCylinder → ℝ) (z : HandleCylinder) :
    CylinderModel →L[ℝ] ℝ := f z • cylinderAngular z


end

open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def stripPrimitive (a : ℝ) (A B : Plane → ℝ) (q : Plane) : ℝ :=
  (∫ s in a..q.1, A (s,0)) + ∫ t in (0:ℝ)..q.2, B (q.1,t)

def annularPrimitive (a : ℝ) (A B : P × Plane → ℝ) (q : P × Plane) : ℝ :=
  stripPrimitive a (fun z => A (q.1,z)) (fun z => B (q.1,z)) q.2



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def annularMean (a : ℝ) (B : P × Plane → ℝ) (p : P) : ℝ :=
  ∫ t in (0:ℝ)..1, B (p,(a,t))

def annularNormalized (a : ℝ) (B : P × Plane → ℝ) (β : ℝ → ℝ)
    (q : P × Plane) : ℝ := B q-annularMean a B q.1*β q.2.2


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def normalizedAnnularPrimitive (a : ℝ) (A B : P × Plane → ℝ)
    (β : ℝ → ℝ) : P × Plane → ℝ :=
  annularPrimitive a A (annularNormalized a B β)


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def annularScalarDescent (F : P × Plane → ℝ) : (P × ℝ) × Circle → ℝ :=
  circleFamilyDescent (fun q => F (q.1.1,(q.1.2,q.2)))



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularCurvaturePrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def annularRadialIntegral (a : ℝ) (κ : P × Plane → ℝ) (q : P × Plane) : ℝ :=
  ∫ s in a..q.2.1,κ (q.1,(s,q.2.2))


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

theorem torus_fst_smooth : ContMDiff 𝓘(ℝ,TorusModel) 𝓘(ℝ,CircleModel) ∞
    (Prod.fst : HandleTorus → Circle) := by
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact contMDiff_fst

def torusTurns (z : Plane) : HandleTorus := (circleTurn z.1,circleTurn z.2)

theorem flatPlane_fst_smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (Prod.fst : Plane → ℝ) :=
  (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Plane → ℝ)).contMDiff

theorem flatPlane_snd_smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (Prod.snd : Plane → ℝ) :=
  (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Plane → ℝ)).contMDiff

theorem torusTurns_smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,TorusModel) ∞ torusTurns := by
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact (circleTurn_smooth.comp flatPlane_fst_smooth).prodMk
    (circleTurn_smooth.comp flatPlane_snd_smooth)





def angularUnitVector (z : Circle) : CircleModel :=
  mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn (shortCircleArgument z) 1

theorem angularUnitVector_value (z : Circle) : circleAngular z (angularUnitVector z)=1 := by
  have h := circleAngular_unit_pullback (shortCircleArgument z) 1
  rwa [circleTurn_shortCircleArgument] at h

theorem circleAngular_injective (z : Circle) : Injective (circleAngular z) := by
  let e : CircleModel := EuclideanSpace.single 0 1
  have he (v : CircleModel) : v=(v 0) • e := by
    ext i
    fin_cases i
    simp [e]
  have hz : circleAngular z e≠0 := by
    intro hzero
    have hv := angularUnitVector_value z
    rw [he (angularUnitVector z),map_smul,hzero,smul_zero] at hv
    norm_num at hv
  intro v w hvw
  have hce : v 0 * circleAngular z e=w 0 * circleAngular z e := by
    rwa [he v,he w,map_smul,map_smul,smul_eq_mul,smul_eq_mul] at hvw
  have hcoords := mul_right_cancel₀ hz hce
  rw [he v,he w,hcoords]


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def annularCylinderScalar (F : P × Plane → ℝ) (p : P) (z : HandleCylinder) : ℝ :=
  annularScalarDescent F ((p,z.1),z.2)

variable [FiniteDimensional ℝ P]

def cylinderCurvaturePrimitive (a : ℝ) (κ : P × Plane → ℝ) (p : P) :
    ManifoldOneForm CylinderModel HandleCylinder :=
  weightedCylinderAngular (annularCylinderScalar (annularRadialIntegral a κ) p)


end


open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem circleTurn_derivative_right_inverse (t : ℝ) (v : CircleModel) :
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn t (circleAngular (circleTurn t) v)=v :=
  circleAngular_injective (circleTurn t) (circleAngular_unit_pullback t _)

theorem cylinderCover_derivative_right_inverse (q : Plane) (v : CylinderModel) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q
      (v.1,circleAngular (circleTurn q.2) v.2)=v := by
  rw [cylinderCover_derivative,circleTurn_derivative_right_inverse]
  rfl

def cylinderAreaForm : ManifoldTwoForm CylinderModel HandleCylinder :=
  manifoldWedge (fun _ => ContinuousLinearMap.fst ℝ ℝ CircleModel) cylinderAngular

@[simp] theorem cylinderAreaForm_apply (z : HandleCylinder) (v w : CylinderModel) :
    cylinderAreaForm z v w=v.1*circleAngular z.2 w.2-circleAngular z.2 v.2*w.1 := by
  simp only [cylinderAreaForm,manifoldWedge_apply,cylinderAngular_apply]
  rfl



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_CylinderAnnularNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def cylinderFormA (α : P → ManifoldOneForm CylinderModel HandleCylinder) (q : P × Plane) : ℝ :=
  parameterEuclideanPullbackOneForm α cylinderCover q (1,0)

def cylinderFormB (α : P → ManifoldOneForm CylinderModel HandleCylinder) (q : P × Plane) : ℝ :=
  parameterEuclideanPullbackOneForm α cylinderCover q (0,1)

def cylinderFormPeriod (a : ℝ) (α : P → ManifoldOneForm CylinderModel HandleCylinder) (p : P) : ℝ :=
  annularMean a (cylinderFormB α) p


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def handleAnnularChart
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) HandleCylinder M ∞ :=
  restrictHandleDiffeomorph (torusAnnulus.trans e) (Ioo (-a) a ×ˢ univ)
    (isOpen_Ioo.prod isOpen_univ)

@[simp] theorem handleAnnularChart_apply
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) (z : HandleCylinder) : handleAnnularChart e a z=e (torusAnnulusMap z) := rfl

end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem positiveCircleArgument_smooth {s : ℝ} (hs : s∈Ioo (0:ℝ) 1) :
    ContMDiffAt 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ positiveCircleArgument (circleTurn s) := by
  have hi : ContMDiffAt 𝓘(ℝ,CircleModel) 𝓘(ℝ,CircleModel) ∞
      (fun z : Circle => z/circleTurn (1/2)) (circleTurn s) :=
    contMDiffAt_id.div contMDiffAt_const
  have hslit : ((circleTurn s/circleTurn (1/2) : Circle) : ℂ)∈Complex.slitPlane := by
    rw [← circleTurn_sub]
    apply circleTurn_short_slit
    constructor <;> linarith [hs.1,hs.2]
  exact ((shortCircleArgument_smooth_at hslit).comp (circleTurn s) hi).add contMDiffAt_const

def positiveCircleCoordinate : PartialDiffeomorph 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) ℝ Circle ∞ where
  toFun := circleTurn
  invFun := positiveCircleArgument
  source := Ioo (0:ℝ) 1
  target := circleTurn '' Ioo (0:ℝ) 1
  map_source' s hs := ⟨s,hs,rfl⟩
  map_target' := by
    rintro z ⟨s,hs,rfl⟩
    rwa [positiveCircleArgument_turn hs]
  left_inv' := fun _ hs => positiveCircleArgument_turn hs
  right_inv' := fun _ _ => circleTurn_positiveCircleArgument _
  open_source := isOpen_Ioo
  open_target := circleTurn_isOpenMap _ isOpen_Ioo
  contMDiffOn_toFun := circleTurn_smooth.contMDiffOn
  contMDiffOn_invFun := by
    rintro z ⟨s,hs,rfl⟩
    exact (positiveCircleArgument_smooth hs).contMDiffWithinAt

def torusRectangleInverse (z : HandleTorus) : Plane :=
  (shortCircleArgument z.1,positiveCircleArgument z.2)

theorem torusRectangleInverse_smooth {z : HandleTorus}
    (hz : z∈circleBandCoordinate.target ×ˢ positiveCircleCoordinate.target) :
    ContMDiffAt 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) ∞ torusRectangleInverse z := by
  have hf := circleBandCoordinate.contMDiffOn_invFun.contMDiffAt
    (circleBandCoordinate.open_target.mem_nhds hz.1)
  have hg := positiveCircleCoordinate.contMDiffOn_invFun.contMDiffAt
    (positiveCircleCoordinate.open_target.mem_nhds hz.2)
  have hp : ContMDiffAt 𝓘(ℝ,TorusModel) 𝓘(ℝ,CircleModel) ∞
      (Prod.fst : HandleTorus → Circle) z := torus_fst_smooth.contMDiffAt
  have hq : ContMDiffAt 𝓘(ℝ,TorusModel) 𝓘(ℝ,CircleModel) ∞
      (Prod.snd : HandleTorus → Circle) z := torus_snd_smooth.contMDiffAt
  exact (contMDiffAt_prod_module_iff _).2 ⟨hf.comp z hp,hg.comp z hq⟩

def torusRectangle : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,TorusModel) Plane HandleTorus ∞ where
  toFun := torusTurns
  invFun := torusRectangleInverse
  source := circleBandCoordinate.source ×ˢ positiveCircleCoordinate.source
  target := circleBandCoordinate.target ×ˢ positiveCircleCoordinate.target
  map_source' _z hz := ⟨circleBandCoordinate.map_source hz.1,positiveCircleCoordinate.map_source hz.2⟩
  map_target' _z hz := ⟨circleBandCoordinate.map_target hz.1,positiveCircleCoordinate.map_target hz.2⟩
  left_inv' _z hz := Prod.ext (circleBandCoordinate.left_inv hz.1) (positiveCircleCoordinate.left_inv hz.2)
  right_inv' _z hz := Prod.ext (circleBandCoordinate.right_inv hz.1) (positiveCircleCoordinate.right_inv hz.2)
  open_source := circleBandCoordinate.open_source.prod positiveCircleCoordinate.open_source
  open_target := circleBandCoordinate.open_target.prod positiveCircleCoordinate.open_target
  contMDiffOn_toFun := torusTurns_smooth.contMDiffOn
  contMDiffOn_invFun := fun _ hz => (torusRectangleInverse_smooth hz).contMDiffWithinAt


end


open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def angularReparam (g : ℝ → ℝ) (p : Plane × E) : Plane × E :=
  ((p.1.1,g p.1.2),p.2)

def normalizedAreaDensity (A B : Plane → ℝ) (g : ℝ → ℝ) (q : Plane) : ℝ :=
  (fderiv ℝ B (q.1,g q.2) (1,0)-fderiv ℝ A (q.1,g q.2) (0,1))*deriv g q.2



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_LayerAreaForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Topology
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def layerHamiltonian (F H : (ι → ℝ) → ℝ) (ρ : ℝ → ℝ) (p : ℝ × PlanePhase ι) : ℝ :=
  F (planeMoments p.2)+ρ p.1*H (planeMoments p.2)

omit [DecidableEq ι] in
@[fun_prop] theorem layerHamiltonian_smooth {F H : (ι → ℝ) → ℝ} {ρ : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H) (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (layerHamiltonian F H ρ) :=
  (hF.comp (planeMoments_smooth.comp contDiff_snd)).add
    ((hρ.comp contDiff_fst).mul (hH.comp (planeMoments_smooth.comp contDiff_snd)))


end

section

open scoped ContDiff Topology BigOperators
open Set Function

def areaHamiltonianForm {m : ℕ} (ℓ : Plane → ℝ) (G : ℝ × PlanePhase (Fin m) → ℝ)
    (p : Plane × PlanePhase (Fin m)) :
    (Plane × PlanePhase (Fin m)) →L[ℝ] (Plane × PlanePhase (Fin m)) →L[ℝ] ℝ :=
  let ds := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane (PlanePhase (Fin m)))
  let dt := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane (PlanePhase (Fin m)))
  let c := ds.prod (ContinuousLinearMap.snd ℝ Plane (PlanePhase (Fin m)))
  let β := (fderiv ℝ G (p.1.1,p.2)).comp c
  phaseArea.bilinearComp (ContinuousLinearMap.snd ℝ Plane (PlanePhase (Fin m)))
      (ContinuousLinearMap.snd ℝ Plane (PlanePhase (Fin m)))+
    ℓ p.1 • (ds.smulRight dt-dt.smulRight ds)+β.smulRight dt-dt.smulRight β

@[simp] theorem areaHamiltonianForm_apply {m : ℕ} (ℓ : Plane → ℝ)
    (G : ℝ × PlanePhase (Fin m) → ℝ) (p v w : Plane × PlanePhase (Fin m)) :
    areaHamiltonianForm ℓ G p v w=phaseArea v.2 w.2+ℓ p.1*(v.1.1*w.1.2-v.1.2*w.1.1)+
      fderiv ℝ G (p.1.1,p.2) (v.1.1,v.2)*w.1.2-v.1.2*fderiv ℝ G (p.1.1,p.2) (w.1.1,w.2) := by
  simp [areaHamiltonianForm,ContinuousLinearMap.smulRight_apply,smul_eq_mul]


end

open scoped ContDiff
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_ConstructedSurfaceLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : E →L[ℝ] E →L[ℝ] ℝ}

def hamiltonianBaseShear (Φ : CompactHamiltonianIsotopy Ω) (θ : ℝ → ℝ)
    (hθ : ContDiff ℝ ∞ θ) : (Plane × E) ≃ₜ (Plane × E) where
  toFun p := (p.1,Φ.map (θ p.1.1) p.2)
  invFun p := (p.1,(Φ.map (θ p.1.1)).symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk
    (Φ.smooth.continuous.comp ((hθ.continuous.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    (Φ.inverse_smooth.continuous.comp ((hθ.continuous.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd))

@[fun_prop] theorem hamiltonianBaseShear_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) : ContDiff ℝ ∞ (hamiltonianBaseShear Φ θ hθ) :=
  contDiff_fst.prodMk (Φ.smooth.comp
    ((hθ.comp (contDiff_fst.comp contDiff_fst)).prodMk contDiff_snd))

@[fun_prop] theorem hamiltonianBaseShear_inverse_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) : ContDiff ℝ ∞ (hamiltonianBaseShear Φ θ hθ).symm :=
  contDiff_fst.prodMk (Φ.inverse_smooth.comp
    ((hθ.comp (contDiff_fst.comp contDiff_fst)).prodMk contDiff_snd))

def baseShearPrimitiveCoefficient (Φ : CompactHamiltonianIsotopy Ω) (θ : ℝ → ℝ)
    (p : ℝ × E) : ℝ := deriv θ p.1 * Φ.hamiltonian (θ p.1,Φ.map (θ p.1) p.2)

@[fun_prop] theorem baseShearPrimitiveCoefficient_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) : ContDiff ℝ ∞ (baseShearPrimitiveCoefficient Φ θ) := by
  exact ((hθ.deriv').comp contDiff_fst).mul
    (Φ.hamiltonian_smooth.comp ((hθ.comp contDiff_fst).prodMk
      (Φ.smooth.comp ((hθ.comp contDiff_fst).prodMk contDiff_snd))))


end

open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : E →L[ℝ] E →L[ℝ] ℝ}

def surfaceFirstPrimitive (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (H : E → ℝ) (a b w : Plane → ℝ) (p : ℝ × (Plane × E)) : (Plane × E) →L[ℝ] ℝ :=
  horizontalOneForm
    (fun x => a x.1 + p.1*deriv S x.1.1 *
      Φ.hamiltonian (p.1*S x.1.1,Φ.map (p.1*S x.1.1) x.2))
    (fun x => b x.1 + w x.1 * S x.1.1 * H ((Φ.map p.1).symm
      (Φ.map (p.1*S x.1.1) x.2))) p.2

@[fun_prop] theorem surfaceFirstPrimitive_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} {H : E → ℝ} {a b w : Plane → ℝ}
    (hS : ContDiff ℝ ∞ S) (hH : ContDiff ℝ ∞ H)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (surfaceFirstPrimitive Φ S H a b w) := by
  have ht : ContDiff ℝ ∞ (fun p : ℝ × (Plane × E) => p.1*S p.2.1.1) :=
    contDiff_fst.mul (hS.comp ((contDiff_fst.comp contDiff_fst).comp contDiff_snd))
  have hq : ContDiff ℝ ∞ (fun p : ℝ × (Plane × E) => Φ.map (p.1*S p.2.1.1) p.2.2) :=
    Φ.smooth.comp (ht.prodMk (contDiff_snd.comp contDiff_snd))
  have hA : ContDiff ℝ ∞ (fun p : ℝ × (Plane × E) => a p.2.1 +
      p.1*deriv S p.2.1.1*Φ.hamiltonian (p.1*S p.2.1.1,Φ.map (p.1*S p.2.1.1) p.2.2)) :=
    (ha.comp (contDiff_fst.comp contDiff_snd)).add
      ((contDiff_fst.mul ((hS.deriv').comp ((contDiff_fst.comp contDiff_fst).comp contDiff_snd))).mul
        (Φ.hamiltonian_smooth.comp (ht.prodMk hq)))
  have hB : ContDiff ℝ ∞ (fun p : ℝ × (Plane × E) => b p.2.1 + w p.2.1*S p.2.1.1*
      H ((Φ.map p.1).symm (Φ.map (p.1*S p.2.1.1) p.2.2))) :=
    (hb.comp (contDiff_fst.comp contDiff_snd)).add
      (((hw.comp (contDiff_fst.comp contDiff_snd)).mul
        (hS.comp ((contDiff_fst.comp contDiff_fst).comp contDiff_snd))).mul
        (hH.comp (Φ.inverse_smooth.comp (contDiff_fst.prodMk hq))))
  exact (hA.smul contDiff_const).add (hB.smul contDiff_const)



end PackingSufficiencySupport.Hamiltonian
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

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : E →L[ℝ] E →L[ℝ] ℝ}

variable {ι : Type*} [Fintype ι]


def surfaceSecondPrimitive (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (K H : E → ℝ) (h : ι → E → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (a b w : Plane → ℝ) (p : ℝ × (Plane × E)) : (Plane × E) →L[ℝ] ℝ :=
  horizontalOneForm
    (fun x => a x.1 + deriv S x.1.1 * Φ.hamiltonian (S x.1.1,Φ.map (S x.1.1) x.2))
    (fun x => b x.1 + w x.1 * surfaceInterpolatedLayer S K H h (Φ.map 1).symm ρ ρ₀ p.1
      (x.1.1,Φ.map (S x.1.1) x.2)) p.2

end

theorem complexUnitDirection_smoothAt {z : ℂ} (hz : z≠0) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,CircleModel) ∞ complexUnitDirection z := by
  let U : TopologicalSpace.Opens ℂ := ⟨{z : ℂ | z≠0},isOpen_compl_singleton⟩
  let f : U → ℂ := fun w => ((‖w.val‖⁻¹:ℝ):ℂ)*w.val
  have hf : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f := by
    intro w
    apply (contMDiffAt_subtype_iff (U := U)
      (f := fun w : ℂ => ((‖w‖⁻¹:ℝ):ℂ)*w)).mpr
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp w.val
      ((contDiffAt_norm ℝ w.property).inv (norm_ne_zero_iff.mpr w.property))).mul
        contDiffAt_id).contMDiffAt
  have hm : ∀ w : U,f w∈Metric.sphere (0:ℂ) 1 := by
    intro w
    rw [show f w=(complexUnitDirection w.val : ℂ) from (complexUnitDirection_coe w.property).symm]
    exact (complexUnitDirection w.val).property
  let := finrank_real_complex_fact'
  have hd : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,CircleModel) ∞ (fun w : U => complexUnitDirection w.val) := by
    have hh := hf.codRestrict_sphere (n := 1) hm
    apply hh.congr
    intro w
    apply Subtype.ext
    exact complexUnitDirection_coe w.property
  exact contMDiffAt_subtype_iff.mp (hd ⟨z,hz⟩)

def cylinderComplexMap (q : HandleCylinder) : ℂ := (Real.exp q.1 : ℂ)*(q.2 : ℂ)

def cylinderComplexInverse (z : ℂ) : HandleCylinder := (Real.log ‖z‖,complexUnitDirection z)

theorem cylinderComplexMap_smooth :
    ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℂ) ∞ cylinderComplexMap := by
  rw [show 𝓘(ℝ,CylinderModel)=(𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod]
  have hf := ((Complex.ofRealCLM.contDiff.contMDiff.comp Real.contDiff_exp.contMDiff).comp
    (contMDiff_fst : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞ (@Prod.fst ℝ Circle)))
  have hg := circle_coe_smooth.comp
    (contMDiff_snd : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,CircleModel) ∞ (@Prod.snd ℝ Circle))
  have hm : ContMDiff ((𝓘(ℝ,ℂ)).prod 𝓘(ℝ,ℂ)) 𝓘(ℝ,ℂ) ∞ (fun z : ℂ × ℂ => z.1*z.2) := by
    rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod]
    exact (show ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1*z.2) from contDiff_fst.mul contDiff_snd).contMDiff
  exact hm.comp (hf.prodMk hg)

theorem cylinderComplexInverse_smoothAt {z : ℂ} (hz : z≠0) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,CylinderModel) ∞ cylinderComplexInverse z := by
  rw [show 𝓘(ℝ,CylinderModel)=(𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod]
  exact (((contDiffAt_norm ℝ hz).log (norm_ne_zero_iff.mpr hz)).contMDiffAt).prodMk
    (complexUnitDirection_smoothAt hz)

@[simp] theorem cylinderComplexMap_norm (q : HandleCylinder) :
    ‖cylinderComplexMap q‖=Real.exp q.1 := by
  rw [cylinderComplexMap,norm_mul,Circle.norm_coe,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

theorem cylinderComplexMap_ne_zero (q : HandleCylinder) : cylinderComplexMap q≠0 := by
  rw [← norm_ne_zero_iff,cylinderComplexMap_norm]
  exact (Real.exp_pos _).ne'

theorem cylinderComplex_left_inv (q : HandleCylinder) :
    cylinderComplexInverse (cylinderComplexMap q)=q := by
  apply Prod.ext
  · simp [cylinderComplexInverse]
  · apply Subtype.ext
    rw [show (cylinderComplexInverse (cylinderComplexMap q)).2=complexUnitDirection (cylinderComplexMap q) from rfl,
      complexUnitDirection_coe (cylinderComplexMap_ne_zero q),cylinderComplexMap_norm]
    simp only [cylinderComplexMap,← mul_assoc,← Complex.ofReal_mul,
      inv_mul_cancel₀ (Real.exp_pos q.1).ne',Complex.ofReal_one,one_mul]

theorem cylinderComplex_right_inv {z : ℂ} (hz : z≠0) :
    cylinderComplexMap (cylinderComplexInverse z)=z := by
  simp only [cylinderComplexMap,cylinderComplexInverse,
    Real.exp_log (norm_pos_iff.mpr hz),complexUnitDirection_coe hz,← mul_assoc,
    ← Complex.ofReal_mul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),Complex.ofReal_one,one_mul]

def cylinderComplexDiffeomorph : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℂ)
    HandleCylinder ℂ ∞ where
  toFun := cylinderComplexMap
  invFun := cylinderComplexInverse
  source := univ
  target := {z | z≠0}
  map_source' q _ := cylinderComplexMap_ne_zero q
  map_target' _ _ := mem_univ _
  left_inv' q _ := cylinderComplex_left_inv q
  right_inv' _ hz := cylinderComplex_right_inv hz
  open_source := isOpen_univ
  open_target := isOpen_compl_singleton
  contMDiffOn_toFun := cylinderComplexMap_smooth.contMDiffOn
  contMDiffOn_invFun := fun _ hz => (cylinderComplexInverse_smoothAt hz).contMDiffWithinAt

end PackingSufficiencySupport.Hamiltonian

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

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def curveOneForm (α : ManifoldOneForm E M) (q : ℝ → M) (t : ℝ) : ℝ :=
  α (q t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) q t 1)

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

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

def surfaceSuspensionCoefficient (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (p : (ℝ × V) × ℝ) : ℝ :=
  p.1.1 * Φ.hamiltonian (p.1.1*S p.2,Φ.map (p.1.1*S p.2) p.1.2)

def surfaceFirstCorrectionCoefficient (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (H : V → ℝ) (p : (ℝ × V) × ℝ) : ℝ :=
  S p.2 * (H ((Φ.map p.1.1).symm (Φ.map (p.1.1*S p.2) p.1.2))-H p.1.2)

@[fun_prop] theorem surfaceSuspensionCoefficient_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (surfaceSuspensionCoefficient Φ S) := by
  have ht : ContDiff ℝ ∞ (fun p : (ℝ × V) × ℝ => p.1.1*S p.2) :=
    (contDiff_fst.comp contDiff_fst).mul (hS.comp contDiff_snd)
  have hq := Φ.smooth.comp (ht.prodMk (contDiff_snd.comp contDiff_fst))
  exact (contDiff_fst.comp contDiff_fst).mul (Φ.hamiltonian_smooth.comp (ht.prodMk hq))

@[fun_prop] theorem surfaceFirstCorrectionCoefficient_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} {H : V → ℝ} (hS : ContDiff ℝ ∞ S) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (surfaceFirstCorrectionCoefficient Φ S H) := by
  have ht : ContDiff ℝ ∞ (fun p : (ℝ × V) × ℝ => p.1.1*S p.2) :=
    (contDiff_fst.comp contDiff_fst).mul (hS.comp contDiff_snd)
  have hq := Φ.smooth.comp (ht.prodMk (contDiff_snd.comp contDiff_fst))
  exact (hS.comp contDiff_snd).mul
    ((hH.comp (Φ.inverse_smooth.comp ((contDiff_fst.comp contDiff_fst).prodMk hq))).sub
      (hH.comp (contDiff_snd.comp contDiff_fst)))

@[simp] theorem surfaceSuspensionCoefficient_zero (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (v : V) (s : ℝ) : surfaceSuspensionCoefficient Φ S ((0,v),s)=0 := by
  simp [surfaceSuspensionCoefficient]

@[simp] theorem surfaceFirstCorrectionCoefficient_zero (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (H : V → ℝ) (v : V) (s : ℝ) :
    surfaceFirstCorrectionCoefficient Φ S H ((0,v),s)=0 := by
  simp [surfaceFirstCorrectionCoefficient,Φ.zero]

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_AffineHopfRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff BigOperators
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def cubicBubbleResidual {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ)
     (ε : ℂ) (z : Fin 3 → ℂ) :
     ((TrapezoidWeight A B × WeightedHomogeneousIndex) ⊕
       ((Fin m → Option (Fin 3)) ⊕ (Fin L → Option (Fin 3)))) → ℂ :=
   Sum.elim (distinguishedResidualPolynomial p L S t δ ε z)
     (Sum.elim (homogeneousVeronese m (complexAffineLift z))
       (fun j => ε^(N-p)*homogeneousVeronese L (complexAffineLift (ε•z)) j))

end PackingSufficiencySupport.CubicModel

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def complexQuotientGauge (y : Option ι → ℂ) : ℂ :=
  (affineSphereScale (complexAffineQuotient y) : ℂ)*(y none)⁻¹

end

section
variable {ι : Type*} [Fintype ι]

def sphereAffineDescend (f : (Option ι → ℂ) → (Option ι → ℂ)) (z : ι → ℂ) : ι → ℂ :=
  complexAffineQuotient (f (complexSphereLift z))

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

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
section

def optionComplexAmbient (m : ℕ) : (Option (Fin m) → ℂ) ≃L[ℝ] Ambient (m+1) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => Fin.cons (z none) (fun j => z (some j))
      invFun := fun z j => match j with | none => z 0 | some j => z j.succ
      left_inv := by intro z; funext j; cases j <;> rfl
      right_inv := by intro z; funext j; exact Fin.cases rfl (fun _ => rfl) j
      map_add' := by intros; funext j; exact Fin.cases rfl (fun _ => rfl) j
      map_smul' := by intros; funext j; exact Fin.cases rfl (fun _ => rfl) j }

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_TailLineCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open scoped BigOperators
section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def coneDenominator (p : PlanePhase ι × PlanePhase κ) : ℝ :=
  (1+phaseSq p.1)^2+phaseSq p.2

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end


