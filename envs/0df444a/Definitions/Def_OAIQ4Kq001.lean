-- Prove2me | Definitions.Def_OAIQ4Kq001
-- name    : OAIQ4Kq001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T08:30:52.058028+00:00
-- url     : https://prove2.me/theorems/8df396b7-f9b1-49d2-b211-e452195511e9
-- title:
--   Definitions bundle OAIQ4Kq001 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kaplansky.kaplansky_quasitrace_counterexample`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 214 declarations of OpenAI's Lean: 53 definitions, 1 inductive type or structure, 3 instances and 157 theorems. The definitions and types are `OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceMatrixFinHAddNatOfNatComplex_solutions`, `OAI.Kaplansky.ComplexGrassmann.matrixColumnLinear`, `OAI.Kaplansky.Expanding`, `OAI.Kaplansky.ExpandingThrough`, `OAI.Kaplansky.HermitianMatrices`, `OAI.Kaplansky.Incidence.MatrixTuple`, `OAI.Kaplansky.Incidence.OpenRankBad`, `OAI.Kaplansky.Incidence.RankBad`, `OAI.Kaplansky.RepeatedLineModel`, `OAI.Kaplansky.SmoothKernel.KernelModel`, `OAI.Kaplansky.SmoothKernel.SurjectiveFamily`, `OAI.Kaplansky.SmoothKernel.SurjectiveFamily.baseSet`, `OAI.Kaplansky.SmoothKernel.SurjectiveFamily.fromModel`, `OAI.Kaplansky.SmoothKernel.SurjectiveFamily.kernelParameterization`, `OAI.Kaplansky.SmoothKernel.SurjectiveFamily.modelEquiv`, `OAI.Kaplansky.SmoothKernel.SurjectiveFamily.rightInverse`, `OAI.Kaplansky.SmoothKernel.SurjectiveFamily.toModel`, `OAI.Kaplansky.SmoothKernel.kernelProjection`, `OAI.Kaplansky.SmoothKernel.kernelRetraction`, `OAI.Kaplansky.SmoothKernel.localRightInverse`, `OAI.Kaplansky.SmoothKernel.splitDomain`, `OAI.Kaplansky.blockDiagonal`, `OAI.Kaplansky.collectiveMatrix`, `OAI.Kaplansky.complexCoreReal`, `OAI.Kaplansky.complexHomCoordinates`, `OAI.Kaplansky.complexOfCommuteI`, `OAI.Kaplansky.complexPart`, `OAI.Kaplansky.complexProjection`, `OAI.Kaplansky.complexProjectionLinear`, `OAI.Kaplansky.decreasingEigenvalues`, `OAI.Kaplansky.expMoment`, `OAI.Kaplansky.frameTuple`, `OAI.Kaplansky.frameTupleCLM`, `OAI.Kaplansky.frameTupleLinear`, `OAI.Kaplansky.gramCoefficient`, `OAI.Kaplansky.homEvaluationCoordinates`, `OAI.Kaplansky.homFrameLinear`, `OAI.Kaplansky.localChartDomain`, `OAI.Kaplansky.matrixHomCore`, `OAI.Kaplansky.normalizedTuple` and 14 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: `ComplexBundle_Avoidance`, `ComplexBundle_BundleIncidence`, `ComplexBundle_Evaluation`, `ComplexBundle_Hom`, `ComplexBundle_Kernel`, `ComplexBundle_Maps`, `ComplexBundle_OpenIncidence`, `ComplexBundle_PointExpansion`, `ComplexBundle_RealModel`, `ComplexBundle_Replacement`, `ComplexBundle_Sections`, `ComplexBundle_SmoothLine`, `MatrixScaling_Bounds`, `MatrixScaling_Canonical`, `MatrixScaling_Continuous`, `MatrixScaling_Critical`, `MatrixScaling_Determinant`, `MatrixScaling_Expansion`, `MatrixScaling_Geodesic`, `MatrixScaling_Gram`, `MatrixScaling_Minimizer`, `MatrixScaling_Spectrum`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ4Kq005`, `OAIQ4Kq006` and `OAIQ4Kq008`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ4_Kq.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Kernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Smooth splittings, kernel charts, and realization of kernel bundles. -/

section
open scoped ContDiff
namespace Kaplansky.SmoothKernel

section
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Right inverse on the open neighborhood where A R is invertible. -/
def localRightInverse (R : W →L[ℂ] V) (A : V →L[ℂ] W) : W →L[ℂ] V :=
  R.comp (Ring.inverse (A.comp R))

def kernelProjection (R : W →L[ℂ] V) (A : V →L[ℂ] W) : V →L[ℂ] V :=
  ContinuousLinearMap.id ℂ V - (localRightInverse R A).comp A

def splitDomain (R : W →L[ℂ] V) : Set (V →L[ℂ] W) := {A | IsUnit (A.comp R)}

theorem splitDomain_open [CompleteSpace W] (R : W →L[ℂ] V) : IsOpen (splitDomain R) := by
  change IsOpen ((fun A : V →L[ℂ] W => A.comp R) ⁻¹' {B : W →L[ℂ] W | IsUnit B})
  exact Units.isOpen.preimage (continuous_id.clm_comp continuous_const)

theorem localRightInverse_right (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) (w : W) : A (localRightInverse R A w)=w := by
  exact congrArg (fun T : W →L[ℂ] W => T w) (Ring.mul_inverse_cancel (A.comp R) hA)

theorem localRightInverse_on_range (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) (w : W) : localRightInverse R A (A (R w))=R w := by
  have h := congrArg (fun T : W →L[ℂ] W => T w) (Ring.inverse_mul_cancel (A.comp R) hA)
  exact congrArg R h

theorem kernelProjection_mem (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) (v : V) : A (kernelProjection R A v)=0 := by
  change A (v-localRightInverse R A (A v))=0
  rw [map_sub,localRightInverse_right R A hA,sub_self]

theorem kernelProjection_fix (R : W →L[ℂ] V) (A : V →L[ℂ] W) (v : V)
    (hv : A v=0) : kernelProjection R A v=v := by
  change v-localRightInverse R A (A v)=v
  rw [hv,map_zero,sub_zero]

theorem kernelProjection_kill (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) (w : W) : kernelProjection R A (R w)=0 := by
  change R w-localRightInverse R A (A (R w))=0
  rw [localRightInverse_on_range R A hA,sub_self]

theorem kernelProjection_absorb (R : W →L[ℂ] V) (A B : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) (v : V) :
    kernelProjection R A (kernelProjection R B v)=kernelProjection R A v := by
  change kernelProjection R A (v-R (Ring.inverse (B.comp R) (B v)))=_
  rw [map_sub,kernelProjection_kill R A hA,sub_zero]

variable [CompleteSpace W]

theorem localRightInverse_smooth (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) : ContDiffAt ℂ ∞ (localRightInverse R) A := by
  obtain ⟨u,hu⟩ := hA
  have hi : ContDiffAt ℂ ∞ Ring.inverse (A.comp R) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℂ u
  exact contDiffAt_const.clm_comp (hi.comp A (contDiffAt_id.clm_comp contDiffAt_const))

theorem kernelProjection_smooth (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) : ContDiffAt ℂ ∞ (kernelProjection R) A :=
  contDiffAt_const.sub ((localRightInverse_smooth R A hA).clm_comp contDiffAt_id)

end

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

def kernelRetraction (R : W →L[ℂ] V) (L : V →L[ℂ] W) (hL : L ∈ splitDomain R) :
    V →L[ℂ] LinearMap.ker L.toLinearMap :=
  (kernelProjection R L).codRestrict _ (kernelProjection_mem R L hL)

end Kaplansky.SmoothKernel

end

namespace Kaplansky.SmoothKernel
variable {B V W : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

abbrev KernelModel (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] :=
  Fin (Module.finrank ℂ V-Module.finrank ℂ W) → ℂ

/-- Ordinary continuous, surjective linear families. No kernel bundle is part
of the input: the following construction supplies it. -/
structure SurjectiveFamily (B V W : Type*) [TopologicalSpace B]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] where
  map : B → V →L[ℂ] W
  continuous : Continuous map
  surjective : ∀ b, Function.Surjective (map b)

local instance instCompleteSpace_solutions : CompleteSpace W := FiniteDimensional.complete ℂ W

namespace SurjectiveFamily
variable (A : SurjectiveFamily B V W)

def rightInverse (b : B) : W →L[ℂ] V :=
  ((A.map b).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (A.surjective b))).choose.toContinuousLinearMap

omit [FiniteDimensional ℂ V] in
theorem rightInverse_spec (b : B) : (A.map b).comp (A.rightInverse b)=1 := by
  apply ContinuousLinearMap.ext
  intro w
  exact congrArg (fun T : W →ₗ[ℂ] W => T w)
    ((A.map b).toLinearMap.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (A.surjective b))).choose_spec

omit [FiniteDimensional ℂ V] in
theorem center_mem (b : B) : A.map b ∈ splitDomain (A.rightInverse b) := by
  change IsUnit ((A.map b).comp (A.rightInverse b))
  rw [A.rightInverse_spec]
  exact isUnit_one

omit [FiniteDimensional ℂ W] in
theorem kernel_finrank (b : B) : Module.finrank ℂ (LinearMap.ker (A.map b).toLinearMap)=
    Module.finrank ℂ V-Module.finrank ℂ W := by
  have h := (A.map b).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (A.surjective b),finrank_top] at h
  omega

def modelEquiv (b : B) : KernelModel V W ≃L[ℂ] LinearMap.ker (A.map b).toLinearMap :=
  ((FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
    (R := ℂ) (M := KernelModel V W) (M' := LinearMap.ker (A.map b).toLinearMap)).mpr
      (by simp [KernelModel,A.kernel_finrank])).some.toContinuousLinearEquiv

def baseSet (i : B) : Set B := {b | A.map b ∈ splitDomain (A.rightInverse i)}

omit [FiniteDimensional ℂ V] in
theorem baseSet_open (i : B) : IsOpen (A.baseSet i) :=
  (splitDomain_open (A.rightInverse i)).preimage A.continuous

def toModel (i : B) : V →L[ℂ] KernelModel V W :=
  (A.modelEquiv i).symm.toContinuousLinearMap.comp
    (kernelRetraction (A.rightInverse i) (A.map i) (A.center_mem i))

def fromModel (i b : B) : KernelModel V W →L[ℂ] V :=
  (kernelProjection (A.rightInverse i) (A.map b)).comp
    (((LinearMap.ker (A.map i).toLinearMap).subtypeL).comp (A.modelEquiv i).toContinuousLinearMap)

theorem fromModel_toModel (i b : B) (hb : b ∈ A.baseSet i) (v : V)
    (hv : A.map b v=0) : A.fromModel i b (A.toModel i v)=v := by
  change kernelProjection (A.rightInverse i) (A.map b)
    (A.modelEquiv i ((A.modelEquiv i).symm (kernelRetraction _ _ _ v))).val=v
  rw [(A.modelEquiv i).apply_symm_apply]
  exact (kernelProjection_absorb (A.rightInverse i) (A.map b) (A.map i) hb v).trans
    (kernelProjection_fix _ _ v hv)

end SurjectiveFamily
end Kaplansky.SmoothKernel

section
open scoped ContDiff Manifold
namespace Kaplansky.SmoothKernel.SurjectiveFamily
variable {B V W : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
variable (A : SurjectiveFamily B V W)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem kernel_model_real_finrank : Module.finrank ℝ (KernelModel V W)=
    2*(Module.finrank ℂ V-Module.finrank ℂ W) := by
  rw [finrank_real_of_complex]
  simp [KernelModel]

end Kaplansky.SmoothKernel.SurjectiveFamily

end

open Topology Bundle

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Avoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Avoidance of lower-dimensional incidence images in local manifold charts. -/

section
open scoped MeasureTheory ENNReal NNReal Topology
open Set MeasureTheory MeasureTheory.Measure Module
namespace Kaplansky.Incidence

/-- Local smoothness on an open coordinate domain suffices; convexity and
compactness of the whole coordinate domain are not assumptions. -/
theorem smoothOn_open_dimH_image_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s) :
    dimH (f '' s) ≤ finrank ℝ E := by
  apply le_trans (dimH_image_le_of_locally_lipschitzOn ?_)
    ((dimH_mono (subset_univ s)).trans_eq (Real.dimH_univ_eq_finrank E))
  intro x hx
  obtain ⟨C,t,ht,hL⟩ := ((hf x hx).contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨C,t,nhdsWithin_le_nhds ht,hL⟩

/-- The lower-dimensional smooth image is null for top-dimensional Hausdorff
measure, which is an additive Haar measure on the target. -/
theorem smoothOn_open_image_null {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s)
    (hd : finrank ℝ E < finrank ℝ F) : μH[finrank ℝ F] (f '' s)=0 := by
  have h : dimH (f '' s) < (finrank ℝ F : ℝ≥0∞) :=
    (smoothOn_open_dimH_image_le hs hf).trans_lt (Nat.cast_lt.mpr hd)
  simpa only [NNReal.coe_natCast] using
    (hausdorffMeasure_of_dimH_lt (d := (finrank ℝ F : ℝ≥0)) h)

end Kaplansky.Incidence

end

section
open Set
open scoped Topology Manifold ContDiff
namespace Kaplansky
variable {X B Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace B] [ChartedSpace X B] [IsManifold 𝓘(ℝ,X) ∞ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The actual chart domain restricted to a bundle trivializing open set. -/
def localChartDomain (U : B → Set B) (x : B) : Set X :=
  (chartAt X x).target ∩ (chartAt X x).symm ⁻¹' U x

omit [NormedSpace ℝ X] [IsManifold 𝓘(ℝ, X) ∞ B] in
theorem localChartDomain_open (U : B → Set B) (hU : ∀ x, IsOpen (U x)) (x : B) :
    IsOpen (localChartDomain (X := X) U x) :=
  (chartAt X x).continuousOn_symm.isOpen_inter_preimage (chartAt X x).open_target (hU x)

theorem localChartDomain_smooth (U : B → Set B) (f : B → Z) (x : B)
    (hf : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Z) ∞ f (U x)) :
    ContDiffOn ℝ ∞ (fun z => f ((chartAt X x).symm z)) (localChartDomain U x) := by
  apply ContMDiffOn.contDiffOn
  exact hf.comp ((contMDiffOn_chart_symm (I := 𝓘(ℝ,X)) (x := x)).mono inter_subset_left)
    (fun _ hz => hz.2)

omit [NormedSpace ℝ X] [IsManifold 𝓘(ℝ, X) ∞ B] in
/-- A countable choice of actual base charts covers the manifold while also
respecting the prescribed open neighborhoods. -/
theorem exists_countable_local_chart_cover [LindelofSpace B]
    (U : B → Set B) (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x) :
    ∃ c : Set B, c.Countable ∧ ∀ y, ∃ x ∈ c,
      y ∈ U x ∧ y ∈ (chartAt X x).source ∧
      (chartAt X x) y ∈ localChartDomain U x ∧
      (chartAt X x).symm ((chartAt X x) y)=y := by
  let O x := U x ∩ (chartAt X x).source
  have ho : ∀ x, IsOpen (O x) := fun x => (hU x).inter (chartAt X x).open_source
  have hcov : (univ : Set B) ⊆ ⋃ x, O x := by
    intro y _
    exact mem_iUnion.mpr ⟨y,hxU y,mem_chart_source X y⟩
  obtain ⟨c,hc,hcov⟩ := isLindelof_univ.elim_countable_subcover O ho hcov
  refine ⟨c,hc,fun y => ?_⟩
  obtain ⟨x,hxc,hxy⟩ : ∃ x ∈ c, y ∈ O x := by
    simpa only [mem_iUnion,exists_prop] using hcov (mem_univ y)
  have he := (chartAt X x).left_inv hxy.2
  refine ⟨x,hxc,hxy.1,hxy.2,⟨(chartAt X x).mapsTo hxy.2,?_⟩,he⟩
  simpa only [mem_preimage,he] using hxy.1

end Kaplansky

end

section
open scoped ContDiff Topology MeasureTheory
open Set MeasureTheory MeasureTheory.Measure Module
namespace Kaplansky.SmoothKernel.SurjectiveFamily
variable {X V W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
local instance instCompleteSpace_2 : CompleteSpace W := FiniteDimensional.complete ℂ W
variable (A : SurjectiveFamily X V W)

def kernelParameterization (i : X) (p : X × KernelModel V W) : V := A.fromModel i p.1 p.2

end Kaplansky.SmoothKernel.SurjectiveFamily

end

open scoped ContDiff MeasureTheory
open Module MeasureTheory MeasureTheory.Measure

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Evaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Smooth generating sections, evaluation maps, and complex-linear bundle maps. -/

section
open scoped ContDiff
namespace Kaplansky

section
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {q : ℕ}

def tupleEvaluation (L : V →L[ℂ] W) : (Fin q → V) →L[ℂ] (Fin q → W) :=
  ContinuousLinearMap.pi (fun i => L.comp (ContinuousLinearMap.proj i))

@[simp] theorem tupleEvaluation_apply (L : V →L[ℂ] W) (v : Fin q → V) (i : Fin q) :
    tupleEvaluation L v i=L (v i) := rfl

theorem tupleEvaluation_surjective (L : V →L[ℂ] W) (hL : Function.Surjective L) :
    Function.Surjective (tupleEvaluation (q := q) L) := by
  intro w
  choose v hv using fun i => hL (w i)
  exact ⟨v,funext hv⟩

def tupleEvaluationLinear : (V →L[ℂ] W) →ₗ[ℂ] ((Fin q → V) →L[ℂ] (Fin q → W)) where
  toFun := tupleEvaluation
  map_add' L K := by ext v i; rfl
  map_smul' c L := by ext v i; rfl

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

def tupleEvaluationMap : (V →L[ℂ] W) →L[ℂ] ((Fin q → V) →L[ℂ] (Fin q → W)) :=
  tupleEvaluationLinear.toContinuousLinearMap

theorem tupleEvaluation_smooth : ContDiff ℝ ∞ (tupleEvaluation (V := V) (W := W) (q := q)) :=
  ((tupleEvaluationMap (V := V) (W := W) (q := q)).restrictScalars ℝ).contDiff

end

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem complex_smul_decomposition (c : ℂ) (v : E) :
    c • v=c.re • v+c.im • (Complex.I • v) := by
  calc
    c • v=((c.re : ℂ)+(c.im : ℂ)*Complex.I) • v := by rw [Complex.re_add_im]
    _ = _ := by rw [add_smul,mul_smul,Complex.coe_smul,Complex.coe_smul]

/-- Upgrade a real-linear map commuting with the complex structure. -/
def complexOfCommuteI (f : E →ₗ[ℝ] F) (hI : ∀ v, f (Complex.I • v)=Complex.I • f v) :
    E →ₗ[ℂ] F where
  toFun := f
  map_add' := f.map_add
  map_smul' c v := by
    rw [complex_smul_decomposition, map_add, map_smul, map_smul,hI]
    exact (complex_smul_decomposition c (f v)).symm

/-- The canonical projection from real-linear maps to complex-linear maps. -/
def realComplexPart (f : E →ₗ[ℝ] F) : E →ₗ[ℝ] F where
  toFun v := (1/2 : ℂ) • (f v-Complex.I • f (Complex.I • v))
  map_add' v w := by simp only [smul_add,map_add]; module
  map_smul' c v := by
    change (1/2 : ℂ) • (f (c • v)-Complex.I • f (Complex.I • (c • v))) = c • ((1/2 : ℂ) • (f v-Complex.I • f (Complex.I • v)))
    simp only [smul_comm Complex.I c,map_smul,← smul_sub,smul_comm (1/2 : ℂ) c]

theorem realComplexPart_commute_I (f : E →ₗ[ℝ] F) (v : E) :
    realComplexPart f (Complex.I • v)=Complex.I • realComplexPart f v := by
  change (1/2 : ℂ) • (f (Complex.I • v)-Complex.I • f (Complex.I • (Complex.I • v))) = Complex.I • ((1/2 : ℂ) • (f v-Complex.I • f (Complex.I • v)))
  rw [smul_comm Complex.I (1/2 : ℂ)]
  simp only [smul_sub,smul_smul,Complex.I_mul_I,neg_one_smul,map_neg,smul_neg,sub_neg_eq_add]
  rw [add_comm]

def complexPart (f : E →L[ℝ] F) : E →L[ℂ] F :=
  { complexOfCommuteI (realComplexPart f.toLinearMap) (realComplexPart_commute_I f.toLinearMap) with
    cont := continuous_const.smul (f.continuous.sub
      (continuous_const.smul (f.continuous.comp (continuous_const.smul continuous_id)))) }

@[simp] theorem complexPart_apply (f : E →L[ℝ] F) (v : E) :
    complexPart f v=(1/2 : ℂ) • (f v-Complex.I • f (Complex.I • v)) := rfl

theorem complexPart_restrict (f : E →L[ℂ] F) : complexPart (f.restrictScalars ℝ)=f := by
  ext v
  change (1/2 : ℂ) • (f v-Complex.I • f (Complex.I • v))=f v
  rw [map_smul,smul_smul,Complex.I_mul_I,neg_one_smul]
  module

def complexProjectionLinear : (E →L[ℝ] F) →ₗ[ℝ] (E →L[ℂ] F) where
  toFun := complexPart
  map_add' f g := by ext v; simp only [complexPart_apply,add_apply]; module
  map_smul' c f := by
    ext v
    change (1/2 : ℂ) • (c • f v-Complex.I • (c • f (Complex.I • v))) = c • ((1/2 : ℂ) • (f v-Complex.I • f (Complex.I • v)))
    simp only [smul_comm Complex.I c,← smul_sub,smul_comm (1/2 : ℂ) c]

theorem complexPart_natural
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (g : G →L[ℂ] E) (f : E →L[ℝ] F) (h : F →L[ℂ] H) :
    complexPart ((h.restrictScalars ℝ).comp (f.comp (g.restrictScalars ℝ))) =
      h.comp ((complexPart f).comp g) := by
  ext v
  change (1/2 : ℂ) • (h (f (g v))-Complex.I • h (f (g (Complex.I • v)))) =
    h ((1/2 : ℂ) • (f (g v)-Complex.I • f (Complex.I • g v)))
  simp only [map_smul,map_sub]

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

def complexProjection : (E →L[ℝ] F) →L[ℝ] (E →L[ℂ] F) :=
  complexProjectionLinear.toContinuousLinearMap

end Kaplansky

end

section
open Bundle Function Set Module
open scoped Topology Manifold ContDiff
namespace Kaplansky

section
variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] (I : ModelWithCorners ℝ X H)
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℝ F E] [ContMDiffVectorBundle ∞ F E I]

/-- A finite family of actual global smooth sections spanning every fiber.
The sections are local frame vectors multiplied by a constructed subordinate
partition of unity, so no global generation hypothesis is used. -/
theorem exists_finite_smooth_spanning_sections :
    ∃ (n : ℕ) (s : Fin n → ∀ x, E x),
      (∀ i, ContMDiff I (I.prod 𝓘(ℝ,F)) ∞ (fun x => TotalSpace.mk' F x (s i x))) ∧
      ∀ x, Submodule.span ℝ (Set.range (fun i => s i x)) = ⊤ := by
  classical
  let U (x : B) := (trivializationAt F E x).baseSet
  obtain ⟨ι, f, hf⟩ := SmoothBumpCovering.exists_isSubordinate I isClosed_univ
    (U := U) (fun x _ => (trivializationAt F E x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F E x))
  let : Fintype ι := f.fintype
  let ρ := f.toSmoothPartitionOfUnity
  have hρ := hf.toSmoothPartitionOfUnity
  let b := finBasis ℝ F
  let e (i : ι) := trivializationAt F E (f.c i)
  let s (i : ι × Fin (finrank ℝ F)) (x : B) : E x :=
    ρ i.1 x • (e i.1).symm x (b i.2)
  have hs : ∀ i, ContMDiff I (I.prod 𝓘(ℝ,F)) ∞
      (fun x => TotalSpace.mk' F x (s i x)) := by
    intro i
    apply ContMDiffOn.smul_section_of_tsupport (ρ i.1).contMDiff.contMDiffOn
      (e i.1).open_baseSet (hρ i.1)
    apply ((e i.1).contMDiffOn_section_baseSet_iff).mpr
    apply (contMDiffOn_const (c := b i.2)).congr
    intro x hx
    simp only [(e i.1).apply_mk_symm hx]
  have hspan : ∀ x, Submodule.span ℝ (Set.range (fun i => s i x)) = ⊤ := by
    intro x
    obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem (mem_univ x)
    have hx : x ∈ (e i).baseSet := hρ i (subset_closure (show x ∈ support (ρ i) from ne_of_gt hi))
    let W := Submodule.span ℝ (Set.range (fun i => s i x))
    have hb : ∀ j, (e i).symm x (b j) ∈ W := by
      intro j
      have hm : s (i,j) x ∈ W := Submodule.subset_span ⟨(i,j),rfl⟩
      have := W.smul_mem ((ρ i x)⁻¹) hm
      simpa only [s, smul_smul, inv_mul_cancel₀ (ne_of_gt hi), one_smul] using this
    rw [Submodule.eq_top_iff']
    intro v
    have heq : v = ∑ j, (b.repr ((e i) ⟨x,v⟩).2 j) • (e i).symm x (b j) := by
      have h := b.sum_repr ((e i) ⟨x,v⟩).2
      have hh := congrArg ((e i).symm x) h
      rw [(e i).symm_apply_apply_mk hx] at hh
      simpa only [← (e i).symmL_apply (R := ℝ) hx, map_sum, map_smul] using hh.symm
    rw [heq]
    exact W.sum_mem (fun j _ => W.smul_mem _ (hb j))
  let a := Fintype.equivFin (ι × Fin (finrank ℝ F))
  refine ⟨Fintype.card (ι × Fin (finrank ℝ F)),fun j => s (a.symm j),fun j => hs _,?_⟩
  intro x
  have hr : Set.range (fun j => s (a.symm j) x) = Set.range (fun i => s i x) := by
    ext v
    constructor
    · rintro ⟨j,rfl⟩; exact ⟨a.symm j,rfl⟩
    · rintro ⟨i,rfl⟩; exact ⟨a i,by simp⟩
  rw [hr]
  exact hspan x

end

section Algebra
variable {B : Type*} {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  {n : ℕ}
/-- Evaluation of the complex coefficients of a finite family of sections. -/
def sectionEvaluation (s : Fin n → ∀ x, E x) (x : B) : (Fin n → ℂ) →ₗ[ℂ] E x where
  toFun c := ∑ i, c i • s i x
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

@[simp] theorem sectionEvaluation_single (s : Fin n → ∀ x, E x) (x : B) (i : Fin n) :
    sectionEvaluation s x (Pi.single i 1) = s i x := by
  classical
  simp [sectionEvaluation, Pi.single_apply]

/-- Real spanning suffices for surjectivity of the complex-linear evaluation. -/
theorem sectionEvaluation_surjective [∀ x, Module ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
    (s : Fin n → ∀ x, E x)
    (hs : ∀ x, Submodule.span ℝ (Set.range (fun i => s i x)) = ⊤) (x : B) :
    Function.Surjective (sectionEvaluation s x) := by
  have h : Submodule.span ℝ (Set.range (fun i => s i x)) ≤
      (LinearMap.range (sectionEvaluation s x)).restrictScalars ℝ := by
    apply Submodule.span_le.mpr
    rintro v ⟨i,rfl⟩
    exact ⟨Pi.single i 1,sectionEvaluation_single s x i⟩
  rw [hs x] at h
  intro v
  exact h (Submodule.mem_top : v ∈ (⊤ : Submodule ℝ (E x)))
end Algebra

end Kaplansky

end

section
open Bundle Module Set
open scoped Topology Manifold ContDiff
namespace Kaplansky

section
variable {X H B F₁ F₂ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] (I : ModelWithCorners ℝ X H)
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [FiniteDimensional ℂ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [FiniteDimensional ℂ F₂]
  (E₁ E₂ : B → Type*)
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [∀ x, NormedAddCommGroup (E₂ x)] [∀ x, NormedSpace ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]
  [VectorBundle ℝ F₁ E₁] [VectorBundle ℂ F₁ E₁]
  [VectorBundle ℝ F₂ E₂] [VectorBundle ℂ F₂ E₂]
  [ContMDiffVectorBundle ∞ F₁ E₁ I] [ContMDiffVectorBundle ∞ F₂ E₂ I]

def complexHomCoordinates
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    (s : ∀ x, E₁ x →L[ℂ] E₂ x) (x : B) : F₁ →L[ℂ] F₂ :=
  (e₂.continuousLinearMapAt ℂ x).comp ((s x).comp (e₁.symmL ℂ x))

omit [T2Space B] [CompactSpace B] [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂] in
theorem complexHomCoordinates_projected
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    (s : ∀ x, E₁ x →L[ℝ] E₂ x) (x : B) (hx : x ∈ e₁.baseSet ∩ e₂.baseSet) :
    complexHomCoordinates E₁ E₂ e₁ e₂ (fun x => complexPart (s x)) x =
      complexPart (((e₁.continuousLinearMap (RingHom.id ℝ) e₂) ⟨x,s x⟩).2) := by
  have h₁ : (e₁.symmL ℂ x).restrictScalars ℝ=e₁.symmL ℝ x := by
    ext v
    change e₁.symmL ℂ x v=e₁.symmL ℝ x v
    rw [e₁.symmL_apply hx.1,e₁.symmL_apply hx.1]
  have h₂ : (e₂.continuousLinearMapAt ℂ x).restrictScalars ℝ=e₂.continuousLinearMapAt ℝ x := by
    ext v
    change e₂.continuousLinearMapAt ℂ x v=e₂.continuousLinearMapAt ℝ x v
    simp only [Trivialization.continuousLinearMapAt_apply,e₂.coe_linearMapAt_of_mem hx.2]
  have hn := complexPart_natural (e₁.symmL ℂ x) (s x) (e₂.continuousLinearMapAt ℂ x)
  rw [h₁,h₂] at hn
  exact hn.symm

omit [FiniteDimensional ℝ X] [IsManifold I ∞ B] [T2Space B] [CompactSpace B] in
theorem complexHomCoordinates_projected_smooth
    (s : ∀ x, E₁ x →L[ℝ] E₂ x)
    (hs : ContMDiff I (I.prod 𝓘(ℝ,F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (s x)))
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] :
    ContMDiffOn I 𝓘(ℝ,F₁ →L[ℂ] F₂) ∞
      (complexHomCoordinates E₁ E₂ e₁ e₂ (fun x => complexPart (s x)))
      (e₁.baseSet ∩ e₂.baseSet) := by
  let e := e₁.continuousLinearMap (RingHom.id ℝ) e₂
  have hc := (e.contMDiffOn_section_baseSet_iff).mp hs.contMDiffOn
  have hp := (complexProjection (E := F₁) (F := F₂)).contMDiff.comp_contMDiffOn hc
  apply hp.congr
  intro x hx
  exact complexHomCoordinates_projected E₁ E₂ e₁ e₂ s x hx

/-- Finite global Hom sections are constructed using the ordinary smooth
real Hom bundle and the canonical complex-linear projection. Evaluation is
surjective onto actual complex-linear fiber maps, and the projected sections
are real-smooth in every pair of actual complex bundle frames. -/
theorem exists_finite_smooth_complex_hom_generators :
    ∃ (n : ℕ) (s : Fin n → ∀ x, E₁ x →L[ℂ] E₂ x),
      (∀ x, Function.Surjective (sectionEvaluation s x)) ∧
      ∀ i (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
        [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂],
        ContMDiffOn I 𝓘(ℝ,F₁ →L[ℂ] F₂) ∞ (complexHomCoordinates E₁ E₂ e₁ e₂ (s i))
          (e₁.baseSet ∩ e₂.baseSet) := by
  obtain ⟨n,s,hs,hspan⟩ := exists_finite_smooth_spanning_sections
    (F := F₁ →L[ℝ] F₂) I (fun x => E₁ x →L[ℝ] E₂ x)
  let t (i : Fin n) (x : B) := complexPart (s i x)
  have ht : ∀ x, Submodule.span ℝ (Set.range (fun i => t i x))=⊤ := by
    intro x
    let P : (E₁ x →L[ℝ] E₂ x) →ₗ[ℝ] (E₁ x →L[ℂ] E₂ x) := complexProjectionLinear
    have hp : Function.Surjective P := fun f => ⟨f.restrictScalars ℝ,complexPart_restrict f⟩
    have hh := congrArg (Submodule.map P) (hspan x)
    rw [Submodule.map_span,Submodule.map_top,LinearMap.range_eq_top.mpr hp] at hh
    have he : P '' Set.range (fun i => s i x)=Set.range (fun i => t i x) := by
      ext v
      constructor
      · rintro ⟨_,⟨i,rfl⟩,rfl⟩; exact ⟨i,rfl⟩
      · rintro ⟨i,rfl⟩; exact ⟨s i x,⟨i,rfl⟩,rfl⟩
    rw [he] at hh
    exact hh
  exact ⟨n,t,sectionEvaluation_surjective t ht,fun i e₁ e₂ _ _ =>
    complexHomCoordinates_projected_smooth I E₁ E₂ (s i) (hs i) e₁ e₂⟩

end

variable {X H B F₁ F₂ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] (I : ModelWithCorners ℝ X H)
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [FiniteDimensional ℂ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [FiniteDimensional ℂ F₂]
  (E₁ E₂ : B → Type*)
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [∀ x, NormedAddCommGroup (E₂ x)] [∀ x, NormedSpace ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]
  [VectorBundle ℝ F₁ E₁] [VectorBundle ℂ F₁ E₁]
  [VectorBundle ℝ F₂ E₂] [VectorBundle ℂ F₂ E₂]
  [ContMDiffVectorBundle ∞ F₁ E₁ I] [ContMDiffVectorBundle ∞ F₂ E₂ I]

omit [T2Space B] [CompactSpace B] [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂] in
theorem realHomCoordinates_restrict
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    (s : ∀ x, E₁ x →L[ℂ] E₂ x) (x : B) (hx : x ∈ e₁.baseSet ∩ e₂.baseSet) :
    (((e₁.continuousLinearMap (RingHom.id ℝ) e₂) ⟨x,(s x).restrictScalars ℝ⟩).2) =
      (complexHomCoordinates E₁ E₂ e₁ e₂ s x).restrictScalars ℝ := by
  ext v
  change e₂.continuousLinearMapAt ℝ x (s x (e₁.symmL ℝ x v)) =
    e₂.continuousLinearMapAt ℂ x (s x (e₁.symmL ℂ x v))
  simp only [e₁.symmL_apply hx.1,Trivialization.continuousLinearMapAt_apply,
    e₂.coe_linearMapAt_of_mem hx.2]

omit [FiniteDimensional ℝ X] [IsManifold I ∞ B] [T2Space B] [CompactSpace B]
  [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂] in
/-- Complex frame-coordinate smoothness implies genuine smoothness of the
section of the ordinary real Hom bundle. It is not merely a named predicate. -/
theorem smooth_realHom_of_complex_coordinates
    (s : ∀ x, E₁ x →L[ℂ] E₂ x)
    (hs : ∀ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂],
      ContMDiffOn I 𝓘(ℝ,F₁ →L[ℂ] F₂) ∞ (complexHomCoordinates E₁ E₂ e₁ e₂ s)
        (e₁.baseSet ∩ e₂.baseSet)) :
    ContMDiff I (I.prod 𝓘(ℝ,F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x ((s x).restrictScalars ℝ)) := by
  intro x
  let e₁ := trivializationAt F₁ E₁ x
  let e₂ := trivializationAt F₂ E₂ x
  let e := e₁.continuousLinearMap (RingHom.id ℝ) e₂
  have hx : x ∈ e₁.baseSet ∩ e₂.baseSet :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x,mem_baseSet_trivializationAt F₂ E₂ x⟩
  apply (e.contMDiffAt_section_iff hx).mpr
  have ho := e₁.open_baseSet.inter e₂.open_baseSet
  have hc := ((hs e₁ e₂) x hx).contMDiffAt (ho.mem_nhds hx)
  have hh := (ContinuousLinearMap.restrictScalarsL ℂ F₁ F₂ ℝ ℝ).contDiff.contDiffAt.contMDiffAt.comp x hc
  apply hh.congr_of_eventuallyEq
  filter_upwards [ho.mem_nhds hx] with y hy
  exact realHomCoordinates_restrict E₁ E₂ e₁ e₂ s y hy

end Kaplansky

end

open Bundle Module Set
open scoped Topology Manifold ContDiff
namespace Kaplansky
variable {X H B F₁ F₂ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] (I : ModelWithCorners ℝ X H)
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [FiniteDimensional ℂ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [FiniteDimensional ℂ F₂]
  (E₁ E₂ : B → Type*)
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [∀ x, NormedAddCommGroup (E₂ x)] [∀ x, NormedSpace ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]
  [VectorBundle ℝ F₁ E₁] [VectorBundle ℂ F₁ E₁]
  [VectorBundle ℝ F₂ E₂] [VectorBundle ℂ F₂ E₂]
  [ContMDiffVectorBundle ∞ F₁ E₁ I] [ContMDiffVectorBundle ∞ F₂ E₂ I]

def homFrameLinear
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] (x : B) :
    (E₁ x →L[ℂ] E₂ x) →ₗ[ℂ] (F₁ →L[ℂ] F₂) where
  toFun T := (e₂.continuousLinearMapAt ℂ x).comp (T.comp (e₁.symmL ℂ x))
  map_add' T S := by ext v; simp
  map_smul' c T := by ext v; simp

omit [T2Space B] [CompactSpace B] [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂]
  [VectorBundle ℝ F₁ E₁] [VectorBundle ℝ F₂ E₂] in
theorem homFrameLinear_surjective
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] (x : B)
    (hx : x ∈ e₁.baseSet ∩ e₂.baseSet) :
    Function.Surjective (homFrameLinear E₁ E₂ e₁ e₂ x) := by
  intro T
  refine ⟨(e₂.symmL ℂ x).comp (T.comp (e₁.continuousLinearMapAt ℂ x)),?_⟩
  ext v
  change e₂.continuousLinearMapAt ℂ x (e₂.symmL ℂ x
    (T (e₁.continuousLinearMapAt ℂ x (e₁.symmL ℂ x v))))=T v
  simp only [Trivialization.continuousLinearMapAt_apply,e₁.coe_linearMapAt_of_mem hx.1,
    e₂.coe_linearMapAt_of_mem hx.2,e₁.symmL_apply hx.1,e₂.symmL_apply hx.2,
    e₁.apply_mk_symm hx.1,e₂.apply_mk_symm hx.2]

omit [T2Space B] [CompactSpace B] [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂]
  [VectorBundle ℝ F₁ E₁] [VectorBundle ℝ F₂ E₂] in
theorem homFrameLinear_commutes
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] (x : B)
    (hx : x ∈ e₁.baseSet ∩ e₂.baseSet) (T : E₁ x →L[ℂ] E₂ x) (v : E₁ x) :
    (e₂.toPretrivialization.linearEquivAt ℂ x hx.2) (T v)=
      homFrameLinear E₁ E₂ e₁ e₂ x T ((e₁.toPretrivialization.linearEquivAt ℂ x hx.1) v) := by
  change (e₂ ⟨x,T v⟩).2=e₂.continuousLinearMapAt ℂ x (T (e₁.symmL ℂ x ((e₁ ⟨x,v⟩).2)))
  simp only [e₁.symmL_apply hx.1,e₁.symm_apply_apply_mk hx.1,
    Trivialization.continuousLinearMapAt_apply,e₂.coe_linearMapAt_of_mem hx.2]

def homEvaluationCoordinates {n : ℕ} (s : Fin n → ∀ x, E₁ x →L[ℂ] E₂ x)
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] (x : B) :
    (Fin n → ℂ) →L[ℂ] (F₁ →L[ℂ] F₂) :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (complexHomCoordinates E₁ E₂ e₁ e₂ (s i) x)

omit [T2Space B] [CompactSpace B] [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂]
  [VectorBundle ℝ F₁ E₁] [VectorBundle ℝ F₂ E₂] in
theorem homEvaluationCoordinates_apply {n : ℕ} (s : Fin n → ∀ x, E₁ x →L[ℂ] E₂ x)
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] (x : B) (c : Fin n → ℂ) :
    homEvaluationCoordinates E₁ E₂ s e₁ e₂ x c=
      homFrameLinear E₁ E₂ e₁ e₂ x (sectionEvaluation s x c) := by
  change (∑ i, (ContinuousLinearMap.proj i).smulRight (complexHomCoordinates E₁ E₂ e₁ e₂ (s i) x)) c =
    homFrameLinear E₁ E₂ e₁ e₂ x (∑ i, c i • s i x)
  simp only [sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,map_sum,map_smul]
  rfl

omit [FiniteDimensional ℝ X] [IsManifold I ∞ B] [T2Space B] [CompactSpace B]
  [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂] [VectorBundle ℝ F₁ E₁]
  [VectorBundle ℝ F₂ E₂] [ContMDiffVectorBundle ∞ F₁ E₁ I]
  [ContMDiffVectorBundle ∞ F₂ E₂ I] in
theorem homEvaluationCoordinates_smooth {n : ℕ} (s : Fin n → ∀ x, E₁ x →L[ℂ] E₂ x)
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    (hs : ∀ i, ContMDiffOn I 𝓘(ℝ,F₁ →L[ℂ] F₂) ∞
      (complexHomCoordinates E₁ E₂ e₁ e₂ (s i)) (e₁.baseSet ∩ e₂.baseSet)) :
    ContMDiffOn I 𝓘(ℝ,(Fin n → ℂ) →L[ℂ] (F₁ →L[ℂ] F₂)) ∞
      (homEvaluationCoordinates E₁ E₂ s e₁ e₂) (e₁.baseSet ∩ e₂.baseSet) := by
  apply contMDiffOn_finsetSum
  intro i _
  have hh : ContDiff ℂ ∞ (fun A : F₁ →L[ℂ] F₂ => (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).smulRight A) :=
    contDiff_clm_apply_iff.mpr (fun c => contDiff_const.smul contDiff_id)
  exact (hh.restrict_scalars ℝ).contMDiff.comp_contMDiffOn (hs i)

theorem exists_finite_smooth_hom_evaluation :
    ∃ (n : ℕ) (s : Fin n → ∀ x, E₁ x →L[ℂ] E₂ x),
      (∀ x, Function.Surjective (sectionEvaluation s x)) ∧
      ∀ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
        [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂],
        ContMDiffOn I 𝓘(ℝ,(Fin n → ℂ) →L[ℂ] (F₁ →L[ℂ] F₂)) ∞
          (homEvaluationCoordinates E₁ E₂ s e₁ e₂) (e₁.baseSet ∩ e₂.baseSet) ∧
        ∀ x ∈ e₁.baseSet ∩ e₂.baseSet,
          Function.Surjective (homEvaluationCoordinates E₁ E₂ s e₁ e₂ x) := by
  obtain ⟨n,s,hs,hsm⟩ := exists_finite_smooth_complex_hom_generators (F₁ := F₁) (F₂ := F₂) I E₁ E₂
  refine ⟨n,s,hs,fun e₁ e₂ _ _ => ⟨homEvaluationCoordinates_smooth I E₁ E₂ s e₁ e₂
    (fun i => hsm i e₁ e₂),fun x hx T => ?_⟩⟩
  obtain ⟨R,hR⟩ := homFrameLinear_surjective E₁ E₂ e₁ e₂ x hx T
  obtain ⟨c,hc⟩ := hs x R
  refine ⟨c,?_⟩
  rw [homEvaluationCoordinates_apply E₁ E₂ s e₁ e₂ x c,hc,hR]

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_PointExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-point incidence avoidance and expansion inequalities. -/

section
open Set Module
namespace Kaplansky.Incidence

/-- Extend any subspace to a prescribed intermediate dimension. -/
theorem exists_super_finrank {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (S : Submodule ℂ E) {n : ℕ}
    (hSn : finrank ℂ S≤n) (hn : n≤finrank ℂ E) :
    ∃ U : Submodule ℂ E, S≤U ∧ finrank ℂ U=n := by
  have aux : ∀ j : ℕ, finrank ℂ S+j≤finrank ℂ E →
      ∃ U : Submodule ℂ E, S≤U ∧ finrank ℂ U=finrank ℂ S+j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨S,le_rfl,by omega⟩
    | succ j ih =>
      intro hj
      obtain ⟨U,hSU,hU⟩ := ih (by omega)
      have hu : finrank ℂ U<finrank ℂ E := by omega
      obtain ⟨v,hv⟩ := U.exists_of_finrank_lt hu
      have hv' : v ∉ U := by simpa using hv 1 one_ne_zero
      refine ⟨U ⊔ Submodule.span ℂ {v},hSU.trans le_sup_left,?_⟩
      rw [Submodule.finrank_sup_span_singleton hv',hU]
      omega
  obtain ⟨U,hSU,hU⟩ := aux (n-finrank ℂ S) (by omega)
  exact ⟨U,hSU,by omega⟩

end Kaplansky.Incidence

end

open scoped MeasureTheory
open Set Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence

abbrev MatrixTuple (q d r : ℕ) := Fin q → (Fin d → ℂ) →L[ℂ] (Fin r → ℂ)

def RankBad {q d r : ℕ} (s t : ℕ) : Set (MatrixTuple q d r) :=
  {T | ∃ S : Submodule ℂ (Fin d → ℂ), finrank ℂ S=s ∧
    ∃ U : Submodule ℂ (Fin r → ℂ), finrank ℂ U=t ∧ ∀ i, ∀ x ∈ S, T i x ∈ U}

end Kaplansky.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_OpenIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Openness of kernel, graph, frame, and rank incidence conditions. -/

section
open scoped ContDiff Topology MeasureTheory
open Set MeasureTheory MeasureTheory.Measure Module
namespace Kaplansky.SmoothKernel
variable {X V W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
local instance instCompleteSpace_solutions_1 : CompleteSpace W := FiniteDimensional.complete ℂ W

/-- Nullity for a surjective family defined smoothly only on an open domain.
Values outside that domain need not be smooth, continuous or surjective. -/
theorem open_kernel_incidence_image_null [MeasurableSpace V] [BorelSpace V]
    (a : X → V →L[ℂ] W) (U : Set X) (hU : IsOpen U)
    (ha : ContDiffOn ℝ ∞ a U) (hs : ∀ x ∈ U, Function.Surjective (a x))
    (hd : finrank ℝ (X × KernelModel V W)<finrank ℝ V) :
    μH[finrank ℝ V] {v : V | ∃ x ∈ U, a x v=0}=0 := by
  let A : SurjectiveFamily U V W := ⟨fun x => a x,ha.continuousOn.domRestrict,fun x => hs x x.property⟩
  let D (i : U) : Set X := U ∩ a ⁻¹' splitDomain (A.rightInverse i)
  have hD : ∀ i, IsOpen (D i) := fun i =>
    ha.continuousOn.isOpen_inter_preimage hU (splitDomain_open (A.rightInverse i))
  have hcov : U ⊆ ⋃ i, D i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hx,A.center_mem ⟨x,hx⟩⟩
  obtain ⟨c,hc,hcov⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover D hD hcov
  let := hc.toEncodable
  let f (i : U) (p : X × KernelModel V W) : V :=
    kernelProjection (A.rightInverse i) (a p.1)
      (((LinearMap.ker (A.map i).toLinearMap).subtypeL).comp
        (A.modelEquiv i).toContinuousLinearMap p.2)
  have hf (i : U) : ContDiffOn ℝ ∞ (f i) (D i ×ˢ univ) := by
    intro p hp
    have hk := ((kernelProjection_smooth (A.rightInverse i) (a p.1) hp.1.2).restrict_scalars ℝ).comp p.1
      ((ha p.1 hp.1.1).contDiffAt (hU.mem_nhds hp.1.1))
    have hc := ((ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).contDiff.contDiffAt.comp p.1 hk).comp p contDiffAt_fst
    have hz : ContDiffAt ℝ ∞ (fun p : X × KernelModel V W =>
        (((LinearMap.ker (A.map i).toLinearMap).subtypeL).comp
          (A.modelEquiv i).toContinuousLinearMap) p.2) p :=
      ((((LinearMap.ker (A.map i).toLinearMap).subtypeL).comp
        (A.modelEquiv i).toContinuousLinearMap).restrictScalars ℝ).contDiff.contDiffAt.comp p contDiffAt_snd
    exact (hc.clm_apply hz).contDiffWithinAt
  have hn (i : c) : μH[finrank ℝ V] (f i.val '' (D i.val ×ˢ univ))=0 :=
    Kaplansky.Incidence.smoothOn_open_image_null ((hD i.val).prod isOpen_univ)
      ((hf i.val).of_le (by simp)) hd
  apply measure_mono_null (t := ⋃ i : c, f i.val '' (D i.val ×ˢ univ)) ?_
    (measure_iUnion_null hn)
  rintro v ⟨x,hx,hv⟩
  obtain ⟨i,hi,hxi⟩ : ∃ i ∈ c, x ∈ D i := by
    simpa only [mem_iUnion,exists_prop] using hcov hx
  refine mem_iUnion.mpr ⟨⟨i,hi⟩,(x,A.toModel i v),⟨hxi,mem_univ _⟩,?_⟩
  exact A.fromModel_toModel i ⟨x,hx⟩ hxi.2 v hv

end Kaplansky.SmoothKernel

end

open scoped ContDiff MeasureTheory
open Set Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
variable {q d r : ℕ}
variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def OpenRankBad (ev : Y → V →L[ℂ] MatrixTuple q d r) (U : Set Y) (s t : ℕ) : Set V :=
  {v | ∃ y ∈ U, ev y v ∈ RankBad s t}

end Kaplansky.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_BundleIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Rank transport and smooth bundle-incidence families. -/

section
open Module
namespace Kaplansky.Incidence
variable {𝕜 E F D R ι : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [AddCommGroup D] [Module 𝕜 D] [AddCommGroup R] [Module 𝕜 R]

/-- Strict collective-image rank bounds are invariant under actual fiber
coordinate equivalences. -/
theorem rank_expansion_of_coordinates (T : ι → E →ₗ[𝕜] F) (C : ι → D →ₗ[𝕜] R)
    (e : E ≃ₗ[𝕜] D) (f : F ≃ₗ[𝕜] R)
    (hcomm : ∀ i x, f (T i x)=C i (e x)) {s t : ℕ}
    (hC : ∀ S : Submodule 𝕜 D, finrank 𝕜 S=s →
      t<finrank 𝕜 (⨆ i, S.map (C i) : Submodule 𝕜 R)) :
    ∀ S : Submodule 𝕜 E, finrank 𝕜 S=s →
      t<finrank 𝕜 (⨆ i, S.map (T i) : Submodule 𝕜 F) := by
  intro S hS
  have h := hC (S.map e.toLinearMap) (by simpa only [e.finrank_map_eq] using hS)
  have he : (⨆ i, (S.map e.toLinearMap).map (C i) : Submodule 𝕜 R)=
      (⨆ i, S.map (T i) : Submodule 𝕜 F).map f.toLinearMap := by
    rw [Submodule.map_iSup]
    apply iSup_congr
    intro i
    rw [← Submodule.map_comp,← Submodule.map_comp]
    congr 1
    ext x
    exact (hcomm i x).symm
  rw [he,f.finrank_map_eq] at h
  exact h

end Kaplansky.Incidence

end

open Bundle Module Set
open scoped Topology Manifold ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Determinant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coercivity, determinants, and positive matrix scaling maps. -/

section

noncomputable section
namespace Kaplansky

def scalingScalar (ε t : ℝ) : ℝ := 2*Real.log (1+ε*t) - (3/2)*Real.log t

/-- The endpoint lower bound which controls t approaching zero. -/
theorem scalingScalar_lower_small {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    -(3/2)*Real.log t ≤ scalingScalar ε t := by
  have h : 0 ≤ Real.log (1+ε*t) := Real.log_nonneg (by nlinarith [mul_pos hε ht])
  dsimp [scalingScalar]
  linarith

/-- The endpoint lower bound which controls t approaching infinity. -/
theorem scalingScalar_lower_large {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    2*Real.log ε + (1/2)*Real.log t ≤ scalingScalar ε t := by
  have h : Real.log (ε*t) ≤ Real.log (1+ε*t) :=
    Real.log_le_log (mul_pos hε ht) (by linarith)
  rw [Real.log_mul (ne_of_gt hε) (ne_of_gt ht)] at h
  dsimp [scalingScalar]
  linarith

/-- A uniform lower bound, without importing a minimizer assumption. -/
theorem scalingScalar_bounded_below {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    (3/2)*Real.log ε ≤ scalingScalar ε t := by
  have h1 := scalingScalar_lower_small hε ht
  have h2 := scalingScalar_lower_large hε ht
  linarith

theorem scalingScalar_sublevel {ε t C : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (hf : scalingScalar ε t ≤ C) :
    Real.exp (-2*C/3) ≤ t ∧ t ≤ Real.exp (2*C-4*Real.log ε) := by
  have h1 := scalingScalar_lower_small hε ht
  have h2 := scalingScalar_lower_large hε ht
  have hlo : -2*C/3 ≤ Real.log t := by linarith
  have hhi : Real.log t ≤ 2*C-4*Real.log ε := by linarith
  constructor
  · simpa only [Real.exp_log ht] using Real.exp_le_exp.mpr hlo
  · simpa only [Real.exp_log ht] using Real.exp_le_exp.mpr hhi

open scoped BigOperators

theorem scaling_eigenvalue_bounds {d : ℕ} {ε C : ℝ} (hε : 0 < ε)
    (eigs : Fin d → ℝ) (heigs : ∀ i, 0 < eigs i)
    (hsum : ∑ i, scalingScalar ε (eigs i) ≤ C) (i : Fin d) :
    let B := C - (d-1) * ((3/2)*Real.log ε)
    Real.exp (-2*B/3) ≤ eigs i ∧ eigs i ≤ Real.exp (2*B-4*Real.log ε) := by
  let b := (3/2)*Real.log ε
  have hb (j : Fin d) : b ≤ scalingScalar ε (eigs j) := scalingScalar_bounded_below hε (heigs j)
  have hi := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => scalingScalar ε (eigs j) - b)
    (fun j _ => sub_nonneg.mpr (hb j)) (Finset.mem_univ i)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hi
  apply scalingScalar_sublevel hε (heigs i)
  change scalingScalar ε (eigs i) ≤ C - (d-1)*b
  linarith

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky

/-- The ordered spectrum, with the matrix cardinality reduced to its size. -/
def decreasingEigenvalues {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.IsHermitian) : Fin r → ℝ :=
  fun i => hA.eigenvalues₀ (Fin.cast (Fintype.card_fin r).symm i)

theorem decreasingEigenvalues_antitone {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.IsHermitian) : Antitone (decreasingEigenvalues hA) := by
  intro i j hij
  exact hA.eigenvalues₀_antitone hij

theorem det_one_add_eq_prod {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.IsHermitian) :
    (1 + A).det = ∏ i, ((1 + decreasingEigenvalues hA i : ℝ) : ℂ) := by
  have h : (1 + A).det = ∏ i, ((1 + hA.eigenvalues i : ℝ) : ℂ) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_one (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary), ← map_add]
    rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul_comm, ← mul_assoc,
      Unitary.coe_star_mul_self, one_mul]
    simp only [← Matrix.diagonal_one,
      Matrix.diagonal_add, Matrix.det_diagonal, Function.comp_apply, Complex.ofReal_add, Complex.ofReal_one]
    rfl
  rw [h]
  let e : Fin (Fintype.card (Fin r)) ≃ Fin r :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let f := fun i => ((1 + hA.eigenvalues₀ i : ℝ) : ℂ)
  change (∏ i, f (e.symm i)) = ∏ i, f ((finCongr (Fintype.card_fin r).symm) i)
  exact (e.symm.prod_comp f).trans ((finCongr (Fintype.card_fin r).symm).prod_comp f).symm

theorem decreasingEigenvalues_nonneg {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.PosSemidef) (i : Fin r) : 0 ≤ decreasingEigenvalues hA.1 i := by
  let e : Fin (Fintype.card (Fin r)) ≃ Fin r :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  change 0 ≤ hA.1.eigenvalues₀ (Fin.cast (Fintype.card_fin r).symm i)
  have h := hA.eigenvalues_nonneg (e (Fin.cast (Fintype.card_fin r).symm i))
  change 0 ≤ hA.1.eigenvalues₀ (e.symm (e (Fin.cast (Fintype.card_fin r).symm i))) at h
  simpa only [Equiv.symm_apply_apply] using h

/-- Real logarithm of the positive determinant, not the complex logarithm. -/
theorem log_det_one_add {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.PosSemidef) :
    Real.log ((1 + A).det.re) = ∑ i, Real.log (1 + decreasingEigenvalues hA.1 i) := by
  rw [det_one_add_eq_prod hA.1, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Real.log_prod (fun i _ => ne_of_gt (by linarith [decreasingEigenvalues_nonneg hA i]))

theorem paired_log_sum {d r : ℕ} (hdr : 2*d ≤ r)
    (μ : Fin r → ℝ) (hμ : Antitone μ) (hμ0 : ∀ i, 0 ≤ μ i)
    (lam : Fin d → ℝ) (hlam : ∀ i, 0 < lam i) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ s : Fin d, ε * lam s ≤ μ ⟨2*s.val+1, by omega⟩) :
    2 * ∑ s, Real.log (1+ε*lam s) ≤ ∑ j, Real.log (1+μ j) := by
  let f : Fin d × Fin 2 → Fin r := fun p => ⟨2*p.1.val+p.2.val, by omega⟩
  have hf : Function.Injective f := by
    intro ⟨i,a⟩ ⟨j,b⟩ h
    have hv := congrArg Fin.val h
    dsimp [f] at hv
    have hab : a = b := Fin.ext (by omega)
    have hij : i = j := Fin.ext (by omega)
    simp [hab, hij]
  have hpair : ∀ p : Fin d × Fin 2,
      Real.log (1+ε*lam p.1) ≤ Real.log (1+μ (f p)) := by
    intro p
    apply Real.log_le_log (by nlinarith [mul_pos hε (hlam p.1)])
    have hm := hμ (show f p ≤ ⟨2*p.1.val+1, by omega⟩ from by
      change 2*p.1.val+p.2.val ≤ 2*p.1.val+1; omega)
    linarith [hbound p.1]
  calc
    2 * ∑ s, Real.log (1+ε*lam s) =
        ∑ p : Fin d × Fin 2, Real.log (1+ε*lam p.1) := by
      simp [Fintype.sum_prod_type, ← Finset.sum_add_distrib, two_mul]
    _ ≤ ∑ p : Fin d × Fin 2, Real.log (1+μ (f p)) :=
      Finset.sum_le_sum (fun p _ => hpair p)
    _ ≤ ∑ j, Real.log (1+μ j) :=
      by
        have he := Finset.sum_image (f := fun j : Fin r => Real.log (1+μ j))
          (s := (Finset.univ : Finset (Fin d × Fin 2))) (g := f)
          (fun _ _ _ _ h => hf h)
        rw [← he]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => Real.log_nonneg (by linarith [hμ0 j]))

theorem scaling_log_det_of_spectral_bound {d r : ℕ} (hdr : 2*d ≤ r)
    {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef)
    (lam : Fin d → ℝ) (hlam : ∀ i, 0 < lam i) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ s : Fin d,
      ε * lam s ≤ decreasingEigenvalues hA.1 ⟨2*s.val+1, by omega⟩) :
    2 * ∑ s, Real.log (1+ε*lam s) ≤ Real.log ((1+A).det.re) := by
  rw [log_det_one_add hA]
  exact paired_log_sum hdr _ (decreasingEigenvalues_antitone hA.1)
    (decreasingEigenvalues_nonneg hA) lam hlam hε hbound

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

def scalingMap (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  ∑ i, T i * P * (T i)ᴴ

theorem scalingMap_positive (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef) :
    (scalingMap T P).PosSemidef :=
  Matrix.posSemidef_sum _ (fun i _ => hP.mul_mul_conjTranspose_same (T i))

theorem scalingMap_sub (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (P Q : Matrix (Fin d) (Fin d) ℂ) :
    scalingMap T (P-Q) = scalingMap T P - scalingMap T Q := by
  simp [scalingMap, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem scalingMap_smul (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (c : ℝ) :
    scalingMap T (c • P) = c • scalingMap T P := by
  simp [scalingMap, Finset.smul_sum]

theorem scalingMap_comparison (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {P p : Matrix (Fin d) (Fin d) ℂ} (c : ℝ)
    (h : (P-c • p).PosSemidef) :
    (scalingMap T P - c • scalingMap T p).PosSemidef := by
  simpa only [scalingMap_sub, scalingMap_smul] using scalingMap_positive T h

theorem decreasingEigenvalues_pos_of_lt_rank {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.PosSemidef) (k : Fin r) (hk : k.val < A.rank) :
    0 < decreasingEigenvalues hA.1 k := by
  let e : Fin (Fintype.card (Fin r)) ≃ Fin r :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let e' : Fin r ≃ Fin r := (finCongr (Fintype.card_fin r).symm).trans e
  have he (i : Fin r) : hA.1.eigenvalues (e' i) = decreasingEigenvalues hA.1 i := by
    change hA.1.eigenvalues₀ (e.symm (e (Fin.cast (Fintype.card_fin r).symm i))) = _
    simp only [Equiv.symm_apply_apply, decreasingEigenvalues]
  have hrank : A.rank = Fintype.card {i // decreasingEigenvalues hA.1 i ≠ 0} := by
    rw [hA.1.rank_eq_card_non_zero_eigs]
    exact (Fintype.card_congr (Equiv.subtypeEquiv e' (fun i => by rw [he]))).symm
  by_contra h
  have hk0 : decreasingEigenvalues hA.1 k = 0 :=
    le_antisymm (le_of_not_gt h) (decreasingEigenvalues_nonneg hA k)
  have hi : ∀ i, decreasingEigenvalues hA.1 i ≠ 0 → i.val < k.val := by
    intro i hne
    by_contra hlt
    have hm := decreasingEigenvalues_antitone hA.1 (show k ≤ i from Nat.le_of_not_gt hlt)
    exact hne (le_antisymm (hk0 ▸ hm) (decreasingEigenvalues_nonneg hA i))
  let f : {i // decreasingEigenvalues hA.1 i ≠ 0} → Fin k.val :=
    fun i => ⟨i.val.val, hi i.val i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Subtype.ext (Fin.ext (congrArg (fun z : Fin k.val => z.val) hij))
  have hc := Fintype.card_le_of_injective f hf
  rw [← hrank, Fintype.card_fin] at hc
  omega

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

/-- Concatenation of all projected maps, whose range is their collective image. -/
def collectiveMatrix (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (p : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin r) (Fin n × Fin d) ℂ :=
  fun a j => (T j.1 * p) a j.2

theorem collectiveMatrix_mulVec (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (p : Matrix (Fin d) (Fin d) ℂ) (v : Fin n × Fin d → ℂ) :
    collectiveMatrix T p *ᵥ v = ∑ i, (T i * p) *ᵥ (fun b => v (i,b)) := by
  ext a
  simp [collectiveMatrix, mulVec, dotProduct, Fintype.sum_prod_type]

theorem collectiveMatrix_range (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (p : Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.range (collectiveMatrix T p).mulVecLin =
      ⨆ i, LinearMap.range (T i * p).mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change collectiveMatrix T p *ᵥ v ∈ _
    rw [collectiveMatrix_mulVec]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup (fun i => LinearMap.range (T i * p).mulVecLin) i)
      ⟨fun b => v (i,b), rfl⟩
  · apply iSup_le
    intro i v hv
    obtain ⟨w,rfl⟩ := hv
    refine ⟨fun j => if j.1 = i then w j.2 else 0, ?_⟩
    change collectiveMatrix T p *ᵥ _ = (T i * p) *ᵥ w
    rw [collectiveMatrix_mulVec]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hz : (fun b => if j=i then w b else 0) = (0 : Fin d → ℂ) := by
        funext b; simp [hji]
      rw [hz, Matrix.mulVec_zero]
    · simp

theorem scalingMap_eq_collective_gram (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {p : Matrix (Fin d) (Fin d) ℂ} (hp : p.IsHermitian) (hpp : p*p=p) :
    scalingMap T p = collectiveMatrix T p * (collectiveMatrix T p)ᴴ := by
  have hi (i : Fin n) : T i * p * (T i)ᴴ = (T i * p) * (T i * p)ᴴ := by
    simp only [conjTranspose_mul, hp.eq]
    simp only [← Matrix.mul_assoc, Matrix.mul_assoc (T i) p p, hpp]
  ext a b
  simp only [scalingMap, Matrix.sum_apply, hi, Matrix.mul_apply,
    collectiveMatrix, conjTranspose_apply, Fintype.sum_prod_type]

theorem scalingMap_projection_rank (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ),
      2 * Module.finrank ℂ S ≤ Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    {p : Matrix (Fin d) (Fin d) ℂ} (hp : p.IsHermitian) (hpp : p*p=p) :
    2*p.rank ≤ (scalingMap T p).rank := by
  rw [scalingMap_eq_collective_gram T hp hpp, Matrix.rank_self_mul_conjTranspose]
  change 2 * Module.finrank ℂ (LinearMap.range p.mulVecLin) ≤
    Module.finrank ℂ (LinearMap.range (collectiveMatrix T p).mulVecLin)
  rw [collectiveMatrix_range]
  have h := hexpand (LinearMap.range p.mulVecLin)
  have he (i : Fin n) : LinearMap.range (T i * p).mulVecLin =
      (LinearMap.range p.mulVecLin).map (T i).mulVecLin := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
  rw [show (⨆ i, LinearMap.range (T i * p).mulVecLin) =
      (⨆ i, (LinearMap.range p.mulVecLin).map (T i).mulVecLin) from iSup_congr he]
  exact h

theorem scalingMap_projection_positive (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {p : Matrix (Fin d) (Fin d) ℂ} (hp : p.IsHermitian) (hpp : p*p=p) :
    (scalingMap T p).PosSemidef := by
  rw [scalingMap_eq_collective_gram T hp hpp]
  exact posSemidef_self_mul_conjTranspose _

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Spectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral min-max bounds, continuity, and compactness of projections. -/

section

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def spectralForm (b : OrthonormalBasis (Fin r) ℂ E) (e : Fin r → ℝ) (x : E) : ℝ :=
  ∑ i, e i * ‖b.repr x i‖^2

theorem basis_norm_sq (b : OrthonormalBasis (Fin r) ℂ E) (x : E) :
    ‖x‖^2 = ∑ i, ‖b.repr x i‖^2 := by
  rw [← b.repr.norm_map x]
  exact EuclideanSpace.norm_sq_eq _

/-- Two full bases have a nonzero vector in the first k+1 coordinates of
one basis and in the last r-k coordinates of the other. -/
theorem basis_intersection_vector (a b : OrthonormalBasis (Fin r) ℂ E) (k : Fin r) :
    ∃ x : E, x ≠ 0 ∧ (∀ i : Fin r, k < i → a.repr x i = 0) ∧
      (∀ i : Fin r, i < k → b.repr x i = 0) := by
  let emb : Fin (k.val+1) → Fin r := fun i => ⟨i.val, by omega⟩
  have hemb : Function.Injective emb := fun i j h => Fin.ext (congrArg (fun z : Fin r => z.val) h)
  let L : (Fin (k.val+1) → ℂ) →ₗ[ℂ] E :=
    ∑ i, (LinearMap.proj i).smulRight (a (emb i))
  have hL (v : Fin (k.val+1) → ℂ) : L v = ∑ i, v i • a (emb i) := by
    simp [L]
  have hcoord (v : Fin (k.val+1) → ℂ) (j : Fin r) :
      a.repr (L v) j = ∑ i, if emb i = j then v i else 0 := by
    rw [hL]
    simp [map_sum, map_smul, OrthonormalBasis.repr_self, Pi.single_apply, mul_ite, eq_comm]
  have hinj : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    funext i
    have h := hcoord v (emb i)
    rw [hv, map_zero] at h
    simpa only [PiLp.zero_apply, hemb.eq_iff, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Pi.zero_apply] using h.symm
  let C : (Fin (k.val+1) → ℂ) →ₗ[ℂ] (Fin k.val → ℂ) :=
    LinearMap.pi (fun i => (b.toBasis.coord ⟨i.val, by omega⟩).comp L)
  have hnot : ¬ Function.Injective C := by
    intro h
    have hc := LinearMap.finrank_le_finrank_of_injective h
    simp only [Module.finrank_pi, Fintype.card_fin] at hc
    omega
  obtain ⟨v, hv, hv0⟩ : ∃ v, C v = 0 ∧ v ≠ 0 := by
    by_contra h
    apply hnot
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    exact h ⟨v, hv, hv0⟩
  refine ⟨L v, fun h => hv0 (hinj (h.trans L.map_zero.symm)), ?_, ?_⟩
  · intro i hi
    rw [hcoord]
    apply Finset.sum_eq_zero
    intro j _
    have hne : emb j ≠ i := by intro h; have := congrArg Fin.val h; dsimp [emb] at this; omega
    simp [hne]
  · intro i hi
    have h := congrFun hv (⟨i.val, hi⟩ : Fin k.val)
    exact h

/-- The min--max comparison, proved by a dimension intersection and
quadratic-form bounds in two orthonormal bases. -/
theorem spectralForm_eigenvalue_mono
    (a b : OrthonormalBasis (Fin r) ℂ E) (e f : Fin r → ℝ)
    (he : Antitone e) (hf : Antitone f)
    (horder : ∀ x, spectralForm a e x ≤ spectralForm b f x) (k : Fin r) : e k ≤ f k := by
  obtain ⟨x,hx,ha,hb⟩ := basis_intersection_vector a b k
  have hlo : e k * ‖x‖^2 ≤ spectralForm a e x := by
    rw [basis_norm_sq a x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i ≤ k
    · exact mul_le_mul_of_nonneg_right (he hi) (sq_nonneg _)
    · simp [ha i (lt_of_not_ge hi)]
  have hhi : spectralForm b f x ≤ f k * ‖x‖^2 := by
    rw [basis_norm_sq b x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : k ≤ i
    · exact mul_le_mul_of_nonneg_right (hf hi) (sq_nonneg _)
    · simp [hb i (lt_of_not_ge hi)]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mp
    (hlo.trans ((horder x).trans hhi))

theorem symmetric_spectralForm [FiniteDimensional ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = r) (x : E) :
    spectralForm (hT.eigenvectorBasis hn) (hT.eigenvalues hn) x =
      (inner ℂ x (T x)).re := by
  let b := hT.eigenvectorBasis hn
  rw [← b.repr.inner_map_map x (T x), EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change (∑ i, hT.eigenvalues hn i * ‖b.repr x i‖^2) =
    (∑ i, star (b.repr x i) * b.repr (T x) i).re
  have hsum := map_sum Complex.reAddGroupHom
    (fun i : Fin r => star (b.repr x i) * b.repr (T x) i) Finset.univ
  change (∑ i, star (b.repr x i) * b.repr (T x) i).re =
    ∑ i, (star (b.repr x i) * b.repr (T x) i).re at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hT.eigenvectorBasis_apply_self_apply hn x i]
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im, star]
  ring

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem symmetric_eigenvalues_smul_le [FiniteDimensional ℂ E]
    {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : Module.finrank ℂ E = r) (c : ℝ) (hc : 0 ≤ c)
    (horder : ∀ x, c * (inner ℂ x (T x)).re ≤ (inner ℂ x (S x)).re) (k : Fin r) :
    c * hT.eigenvalues hn k ≤ hS.eigenvalues hn k := by
  apply spectralForm_eigenvalue_mono (hT.eigenvectorBasis hn) (hS.eigenvectorBasis hn)
    (fun i => c * hT.eigenvalues hn i) (hS.eigenvalues hn)
    (fun i j hij => mul_le_mul_of_nonneg_left (hT.eigenvalues_antitone hn hij) hc)
    (hS.eigenvalues_antitone hn)
  intro x
  have he : spectralForm (hT.eigenvectorBasis hn) (fun i => c * hT.eigenvalues hn i) x =
      c * spectralForm (hT.eigenvectorBasis hn) (hT.eigenvalues hn) x := by
    simp only [spectralForm, Finset.mul_sum, mul_assoc]
  rw [he, symmetric_spectralForm, symmetric_spectralForm]
  exact horder x

theorem decreasingEigenvalues_smul_le {A B : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (c : ℝ) (hc : 0 ≤ c)
    (hBA : (B-c • A).PosSemidef) (k : Fin r) :
    c * decreasingEigenvalues hA k ≤ decreasingEigenvalues hB k := by
  apply symmetric_eigenvalues_smul_le (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace c hc
  intro x
  have h := hBA.re_dotProduct_nonneg (WithLp.ofLp x)
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul] at h
  simpa only [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp, dotProduct_comm, Complex.smul_re, smul_eq_mul] using sub_nonneg.mp h

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem quadraticForm_norm_bound (T : E →L[ℂ] E) (x : E) :
    (inner ℂ x (T x)).re ≤ ‖T‖ * ‖x‖^2 := by
  calc
    (inner ℂ x (T x)).re ≤ ‖inner ℂ x (T x)‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg _)
    _ = ‖T‖ * ‖x‖^2 := by ring

theorem spectralForm_add_const (b : OrthonormalBasis (Fin r) ℂ E)
    (e : Fin r → ℝ) (c : ℝ) (x : E) :
    spectralForm b (fun i => e i+c) x = spectralForm b e x + c*‖x‖^2 := by
  simp only [spectralForm, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← basis_norm_sq]

theorem symmetric_eigenvalue_le_add_norm [FiniteDimensional ℂ E]
    {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : Module.finrank ℂ E = r) (k : Fin r) :
    hT.eigenvalues hn k ≤ hS.eigenvalues hn k + ‖(T-S).toContinuousLinearMap‖ := by
  apply spectralForm_eigenvalue_mono (hT.eigenvectorBasis hn) (hS.eigenvectorBasis hn)
    (hT.eigenvalues hn) (fun i => hS.eigenvalues hn i + ‖(T-S).toContinuousLinearMap‖)
    (hT.eigenvalues_antitone hn) (fun i j hij => add_le_add (hS.eigenvalues_antitone hn hij) le_rfl)
  intro x
  rw [spectralForm_add_const, symmetric_spectralForm, symmetric_spectralForm]
  have h := quadraticForm_norm_bound (T-S).toContinuousLinearMap x
  change (inner ℂ x (T x - S x)).re ≤ _ at h
  rw [inner_sub_right, Complex.sub_re] at h
  linarith

/-- Ordered eigenvalues are 1-Lipschitz in the actual operator norm. -/
theorem decreasingEigenvalues_sub_le_norm {A B : Matrix (Fin r) (Fin r) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : Fin r) :
    |decreasingEigenvalues hA k - decreasingEigenvalues hB k| ≤ ‖A-B‖ := by
  have hab := symmetric_eigenvalue_le_add_norm
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace
    (Fin.cast (Fintype.card_fin r).symm k)
  have hba := symmetric_eigenvalue_le_add_norm
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) finrank_euclideanSpace
    (Fin.cast (Fintype.card_fin r).symm k)
  rw [← map_sub] at hab hba
  change decreasingEigenvalues hA k ≤ decreasingEigenvalues hB k + ‖A-B‖ at hab
  change decreasingEigenvalues hB k ≤ decreasingEigenvalues hA k + ‖B-A‖ at hba
  rw [norm_sub_rev] at hba
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem lipschitz_decreasingEigenvalues (k : Fin r) :
    LipschitzWith 1 (fun A : {A : Matrix (Fin r) (Fin r) ℂ // A.IsHermitian} =>
      decreasingEigenvalues A.property k) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq, Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
    decreasingEigenvalues_sub_le_norm A.property B.property k

theorem continuous_decreasingEigenvalues (k : Fin r) :
    Continuous (fun A : {A : Matrix (Fin r) (Fin r) ℂ // A.IsHermitian} =>
      decreasingEigenvalues A.property k) :=
  (lipschitz_decreasingEigenvalues k).continuous

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Top spectral projections, uniform scaling bounds, and compact sublevels. -/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky

def spectralIndex (d : ℕ) : Fin d ≃ Fin d :=
  (finCongr (Fintype.card_fin d).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin _))

theorem eigenvalues_spectralIndex {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (i : Fin d) :
    hA.eigenvalues (spectralIndex d i) = decreasingEigenvalues hA i := by
  unfold spectralIndex Matrix.IsHermitian.eigenvalues
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, decreasingEigenvalues]
  rfl

theorem decreasingEigenvalues_pos {d : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosDef) (i : Fin d) : 0 < decreasingEigenvalues hP.1 i := by
  rw [← eigenvalues_spectralIndex]
  exact hP.eigenvalues_pos _

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem continuous_scalingMap {Y : Type*} [TopologicalSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hT : Continuous T) (P : Y → Matrix (Fin d) (Fin d) ℂ) (hP : Continuous P) :
    Continuous (fun y => scalingMap (T y) (P y)) := by
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i |>.comp hT).matrix_mul hP).matrix_mul
    ((continuous_apply i |>.comp hT).matrix_conjTranspose)

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem expansion_dimension (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ),
      2 * Module.finrank ℂ S ≤
        Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ))) :
    2*d ≤ r := by
  have h := hexpand ⊤
  have hb := Submodule.finrank_le (⨆ i,
    (⊤ : Submodule ℂ (Fin d → ℂ)).map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ))
  simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at h hb
  omega

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem det_eq_prod_decreasing {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian) :
    P.det = ∏ i, (decreasingEigenvalues hP i : ℂ) := by
  rw [hP.det_eq_prod_eigenvalues]
  calc
    ∏ i, (hP.eigenvalues i : ℂ) = ∏ i, (hP.eigenvalues (spectralIndex d i) : ℂ) :=
      ((spectralIndex d).prod_comp (fun i => (hP.eigenvalues i : ℂ))).symm
    _ = _ := by simp only [eigenvalues_spectralIndex]

theorem log_det_posDef {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) :
    Real.log P.det.re = ∑ i, Real.log (decreasingEigenvalues hP.1 i) := by
  rw [det_eq_prod_decreasing hP.1, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Real.log_prod (fun i _ => ne_of_gt (decreasingEigenvalues_pos hP i))

def scalingPotential (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.log (1+scalingMap T P).det.re - (3/2)*Real.log P.det.re

theorem scalingScalar_sum_le_potential
    (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) (ε : ℝ)
    (hdet : 2 * ∑ s, Real.log (1+ε*decreasingEigenvalues hP.1 s) ≤
      Real.log ((1+scalingMap T P).det.re)) :
    ∑ s, scalingScalar ε (decreasingEigenvalues hP.1 s) ≤ scalingPotential T P := by
  simp only [scalingScalar, Finset.sum_sub_distrib, ← Finset.mul_sum,
    scalingPotential, log_det_posDef hP]
  linarith

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {d : ℕ}

abbrev HermitianMatrices (d : ℕ) := {P : Matrix (Fin d) (Fin d) ℂ // P.IsHermitian}

instance instProperSpaceHermitianMatrices : ProperSpace (HermitianMatrices d) :=
  ProperSpace.of_isClosed (isClosed_eq continuous_star continuous_id)

def spectralWindow (d : ℕ) (a b : ℝ) : Set (HermitianMatrices d) :=
  {P | ∀ i, a ≤ decreasingEigenvalues P.property i ∧ decreasingEigenvalues P.property i ≤ b}

theorem isClosed_spectralWindow (a b : ℝ) : IsClosed (spectralWindow d a b) := by
  simp only [spectralWindow, Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  exact (isClosed_le continuous_const (continuous_decreasingEigenvalues i)).inter
    (isClosed_le (continuous_decreasingEigenvalues i) continuous_const)

theorem norm_le_of_decreasingEigenvalues {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.IsHermitian) {b : ℝ} (hb : 0 ≤ b)
    (he : ∀ i, 0 ≤ decreasingEigenvalues hP i ∧ decreasingEigenvalues hP i ≤ b) :
    ‖P‖ ≤ b := by
  conv_lhs => rw [hP.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro i
  have he' := he ((spectralIndex d).symm i)
  rw [← eigenvalues_spectralIndex, Equiv.apply_symm_apply] at he'
  simpa only [Function.comp_apply, RCLike.norm_ofReal, Real.norm_eq_abs, abs_of_nonneg he'.1]
    using he'.2

theorem isCompact_spectralWindow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsCompact (spectralWindow d a b) := by
  let z : HermitianMatrices d := ⟨0, isHermitian_zero⟩
  apply (isCompact_closedBall z b).of_isClosed_subset (isClosed_spectralWindow a b)
  intro P hP
  rw [Metric.mem_closedBall, Subtype.dist_eq]
  change dist P.val 0 ≤ b
  rw [dist_zero_right]
  exact norm_le_of_decreasingEigenvalues P.property hb (fun i => ⟨ha.trans (hP i).1, (hP i).2⟩)

theorem spectralWindow_posDef {a b : ℝ} (ha : 0 < a) {P : HermitianMatrices d}
    (hP : P ∈ spectralWindow d a b) : P.val.PosDef := by
  apply P.property.posDef_iff_eigenvalues_pos.mpr
  intro i
  have h := lt_of_lt_of_le ha (hP ((spectralIndex d).symm i)).1
  rwa [← eigenvalues_spectralIndex, Equiv.apply_symm_apply] at h

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram determinant expansions and exponential convexity. -/

noncomputable section
open scoped BigOperators
namespace Kaplansky
variable {ι : Type*} [Fintype ι]

/-- Strict positivity of the unnormalized weighted variance. -/
theorem weighted_variance_pos (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (i j : ι) (hi : 0 < w i) (hj : 0 < w j) (hij : a i ≠ a j) :
    0 < (∑ k, w k) * (∑ k, w k * (a k)^2) - (∑ k, w k * a k)^2 := by
  let S := ∑ k, w k
  let M := ∑ k, w k * a k
  let m := M/S
  have hS : 0 < S := lt_of_lt_of_le hi
    (Finset.single_le_sum (fun k _ => hw k) (Finset.mem_univ i))
  have he : ∑ k, w k * (a k-m)^2 =
      (∑ k, w k*(a k)^2) - 2*m*M + m^2*S := by
    calc
      ∑ k, w k * (a k-m)^2 =
          ∑ k, (w k*(a k)^2 - 2*m*(w k*a k) + m^2*w k) := by
        apply Finset.sum_congr rfl; intro k _; ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  have hn : ∀ k, 0 ≤ w k * (a k-m)^2 := fun k => mul_nonneg (hw k) (sq_nonneg _)
  have hpos : 0 < ∑ k, w k * (a k-m)^2 := by
    by_cases him : a i = m
    · have hjm : a j ≠ m := fun h => hij (him.trans h.symm)
      exact lt_of_lt_of_le (mul_pos hj (sq_pos_of_ne_zero (sub_ne_zero.mpr hjm)))
        (Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ j))
    · exact lt_of_lt_of_le (mul_pos hi (sq_pos_of_ne_zero (sub_ne_zero.mpr him)))
        (Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ i))
  have hid : S * (∑ k, w k*(a k)^2) - M^2 = S * (∑ k, w k*(a k-m)^2) := by
    rw [he]
    dsimp [m]
    field_simp
    ring
  change 0 < S * (∑ k, w k*(a k)^2) - M^2
  rw [hid]
  exact mul_pos hS hpos

def expMoment (c a : ι → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∑ i, c i * (a i)^k * Real.exp (a i*u)

theorem hasDerivAt_expMoment (c a : ι → ℝ) (k : ℕ) (u : ℝ) :
    HasDerivAt (expMoment c a k) (expMoment c a (k+1) u) u := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((hasDerivAt_id u).const_mul (a i)).exp).const_mul (c i * (a i)^k))
  have hf : expMoment c a k = ∑ i, fun y => c i*(a i)^k*Real.exp (a i*id y) := by
    funext y
    simp [expMoment]
  have hv : expMoment c a (k+1) u =
      ∑ i, c i*(a i)^k*(Real.exp (a i*id u)*(a i*1)) := by
    simp [expMoment, pow_succ, mul_assoc, mul_comm, mul_left_comm]
  rw [hf, hv]
  exact h

theorem expMoment_zero_pos (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (i : ι) (hi : 0 < c i) (u : ℝ) : 0 < expMoment c a 0 u := by
  simp only [expMoment, pow_zero, mul_one]
  exact lt_of_lt_of_le (mul_pos hi (Real.exp_pos _))
    (Finset.single_le_sum (fun j _ => mul_nonneg (hc j) (Real.exp_pos _).le) (Finset.mem_univ i))

theorem strictConvexOn_log_expSum (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (i j : ι) (hi : 0 < c i) (hj : 0 < c j) (hij : a i ≠ a j) :
    StrictConvexOn ℝ Set.univ (fun u => Real.log (∑ k, c k * Real.exp (a k*u))) := by
  have hz (u : ℝ) := expMoment_zero_pos c a hc i hi u
  have hd (u : ℝ) : HasDerivAt (fun u => Real.log (expMoment c a 0 u))
      (expMoment c a 1 u / expMoment c a 0 u) u :=
    (hasDerivAt_expMoment c a 0 u).log (ne_of_gt (hz u))
  have hd' : deriv (fun u => Real.log (expMoment c a 0 u)) =
      fun u => expMoment c a 1 u / expMoment c a 0 u := funext (fun u => (hd u).deriv)
  have hc' : StrictConvexOn ℝ Set.univ (fun u => Real.log (expMoment c a 0 u)) := by
    apply strictConvexOn_of_deriv2_pos convex_univ
    · exact (continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)).continuousOn
    · intro u _
      change 0 < deriv (deriv (fun u => Real.log (expMoment c a 0 u))) u
      rw [hd']
      change 0 < deriv (expMoment c a 1 / expMoment c a 0) u
      rw [((hasDerivAt_expMoment c a 1 u).div
        (hasDerivAt_expMoment c a 0 u) (ne_of_gt (hz u))).deriv]
      apply div_pos _ (sq_pos_of_pos (hz u))
      have hv := weighted_variance_pos (fun k => c k*Real.exp (a k*u)) a
        (fun k => mul_nonneg (hc k) (Real.exp_pos _).le) i j
        (mul_pos hi (Real.exp_pos _)) (mul_pos hj (Real.exp_pos _)) hij
      simpa only [expMoment, Nat.reduceAdd, pow_zero, pow_one, mul_one, mul_comm, mul_left_comm,
        mul_assoc, pow_two] using hv
  simpa only [expMoment, pow_zero, mul_one] using hc'

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Multivariate principal-minor expansion, with one scalar for each row. -/
theorem det_one_add_diagonal_mul {R : Type*} [CommRing R]
    (G : Matrix n n R) (t : n → R) :
    (1 + Matrix.diagonal t * G).det =
      ∑ s : Finset n, (∏ i ∈ s, t i) *
        (G.submatrix (Subtype.val : s → n) Subtype.val).det := by
  let D := (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
  rw [add_comm]
  have hg : Matrix.diagonal t * G = Matrix.of (fun i => t i • G i) := by
    ext i j
    simp [Matrix.diagonal_mul]
  rw [hg]
  change D ((fun i => t i • G i) + (fun i => (1 : Matrix n n R) i)) = _
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  have hsmul : s.piecewise (fun i => t i • G i) (1 : Matrix n n R) =
      fun i => (if i ∈ s then t i else 1) • s.piecewise G (1 : Matrix n n R) i := by
    funext i j
    simp only [Finset.piecewise, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hsmul, D.map_smul_univ]
  rw [smul_eq_mul]
  change (∏ i, if i ∈ s then t i else 1) *
    (Matrix.of (s.piecewise G (1 : Matrix n n R))).det = _
  have hd := Matrix.det_piecewise_one_eq_submatrix_det G s
  change (Matrix.of (s.piecewise G (1 : Matrix n n R))).det = _ at hd
  rw [hd]
  simp only [Finset.prod_ite_mem, Finset.univ_inter]

theorem gram_determinant_expansion (W : Matrix m n ℂ) (t : n → ℂ) :
    (1 + W * Matrix.diagonal t * W.conjTranspose).det =
      ∑ s : Finset n, (∏ i ∈ s, t i) *
        ((W.conjTranspose * W).submatrix (Subtype.val : s → n) Subtype.val).det := by
  rw [Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc]
  exact det_one_add_diagonal_mul _ _

omit [DecidableEq m] in
theorem gram_minor_nonneg (W : Matrix m n ℂ) (s : Finset n) :
    0 ≤ ((W.conjTranspose * W).submatrix (Subtype.val : s → n) Subtype.val).det := by
  exact (Matrix.posSemidef_conjTranspose_mul_self W).submatrix _ |>.det_nonneg

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def gramCoefficient (W : Matrix m n ℂ) (s : Finset n) : ℝ :=
  ((W.conjTranspose * W).submatrix (Subtype.val : s → n) Subtype.val).det.re

omit [DecidableEq m] in
theorem gramCoefficient_nonneg (W : Matrix m n ℂ) (s : Finset n) :
    0 ≤ gramCoefficient W s := (gram_minor_nonneg W s).1

omit [Fintype n] [DecidableEq m] in
@[simp] theorem gramCoefficient_empty (W : Matrix m n ℂ) :
    gramCoefficient W ∅ = 1 := by simp [gramCoefficient]

omit [Fintype n] [DecidableEq m] in
theorem gramCoefficient_singleton (W : Matrix m n ℂ) (j : n) :
    gramCoefficient W {j} = ∑ i, Complex.normSq (W i j) := by
  unfold gramCoefficient
  rw [Matrix.det_eq_elem_of_subsingleton _ ⟨j,Finset.mem_singleton_self j⟩]
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have he := map_sum Complex.reAddGroupHom (fun i => star (W i j) * W i j) Finset.univ
  change (∑ i, star (W i j) * W i j).re = ∑ i, (star (W i j) * W i j).re at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

omit [Fintype n] [DecidableEq m] in
theorem gramCoefficient_singleton_pos (W : Matrix m n ℂ) (i : m) (j : n)
    (h : W i j ≠ 0) : 0 < gramCoefficient W {j} := by
  rw [gramCoefficient_singleton]
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr h)
    (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (W k j)) (Finset.mem_univ i))

theorem gram_determinant_expSum (W : Matrix m n ℂ) (a : n → ℝ) (u : ℝ) :
    (1 + W * Matrix.diagonal (fun i => (Real.exp (a i*u) : ℂ)) * W.conjTranspose).det.re =
      ∑ s : Finset n, gramCoefficient W s * Real.exp ((∑ i ∈ s, a i)*u) := by
  rw [gram_determinant_expansion]
  have he := map_sum Complex.reAddGroupHom
    (fun s : Finset n => (∏ i ∈ s, (Real.exp (a i*u) : ℂ)) *
      ((W.conjTranspose * W).submatrix (Subtype.val : s → n) Subtype.val).det) Finset.univ
  change Complex.re (∑ s : Finset n, _) = ∑ s : Finset n, Complex.re _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.sum_mul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    gramCoefficient, mul_comm]

theorem strictConvexOn_log_gram (W : Matrix m n ℂ) (a : n → ℝ)
    (i : m) (j : n) (hW : W i j ≠ 0) (ha : a j ≠ 0) :
    StrictConvexOn ℝ Set.univ (fun u => Real.log
      (1 + W * Matrix.diagonal (fun k => (Real.exp (a k*u) : ℂ)) * W.conjTranspose).det.re) := by
  have hc := strictConvexOn_log_expSum (gramCoefficient W)
    (fun s : Finset n => ∑ k ∈ s, a k) (gramCoefficient_nonneg W)
    ∅ {j} (by simp) (gramCoefficient_singleton_pos W i j hW) (by simpa using ha.symm)
  simpa only [← gram_determinant_expSum] using hc

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Geodesic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral curves, strict convexity, and geodesic connections. -/

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {d : ℕ}

/-- A positive-definite geodesic in an eigenbasis for its Hermitian direction. -/
def spectralCurve (L : Matrix (Fin d) (Fin d) ℂ) (h : Fin d → ℝ) (u : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  L * Matrix.diagonal (fun j => (Real.exp (h j*u) : ℂ)) * L.conjTranspose

theorem spectralCurve_posDef (L : Matrix (Fin d) (Fin d) ℂ) (hL : IsUnit L)
    (h : Fin d → ℝ) (u : ℝ) : (spectralCurve L h u).PosDef := by
  have hd : (Matrix.diagonal (fun j => (Real.exp (h j*u) : ℂ))).PosDef :=
    Matrix.PosDef.diagonal (fun j => by exact_mod_cast Real.exp_pos (h j*u))
  exact hL.posDef_star_right_conjugate_iff.mpr hd

theorem spectralCurve_det (L : Matrix (Fin d) (Fin d) ℂ) (h : Fin d → ℝ) (u : ℝ) :
    (spectralCurve L h u).det.re =
      Complex.normSq L.det * Real.exp ((∑ j, h j)*u) := by
  unfold spectralCurve
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose]
  have hp : (∏ j, (Real.exp (h j*u) : ℂ)) = (Real.exp ((∑ j, h j)*u) : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.sum_mul]
  rw [hp]
  have he : L.det * (Real.exp ((∑ j, h j)*u) : ℂ) * star L.det =
      (Complex.normSq L.det : ℂ) * (Real.exp ((∑ j, h j)*u) : ℂ) := by
    rw [Complex.star_def, ← Complex.mul_conj]
    ring
  rw [he, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem spectralCurve_log_det (L : Matrix (Fin d) (Fin d) ℂ) (hL : IsUnit L)
    (h : Fin d → ℝ) (u : ℝ) :
    Real.log (spectralCurve L h u).det.re =
      Real.log (Complex.normSq L.det) + (∑ j, h j)*u := by
  rw [spectralCurve_det, Real.log_mul _ (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  exact ne_of_gt (Complex.normSq_pos.mpr (hL.map Matrix.detMonoidHom).ne_zero)

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {d : ℕ}

/-- A positive definite matrix has an invertible Gram factor, constructed
from its eigenbasis and positive eigenvalues. -/
theorem posDef_gram_factor {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) :
    ∃ L : Matrix (Fin d) (Fin d) ℂ, IsUnit L ∧ L * L.conjTranspose = P := by
  let U := hP.1.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) ℂ := diagonal (fun j => (Real.sqrt (hP.1.eigenvalues j) : ℂ))
  have hD : IsUnit D := by
    apply (D.isUnit_iff_isUnit_det).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hP.eigenvalues_pos j)))
  have hdstar : D.conjTranspose = D := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [D, Matrix.conjTranspose_apply]
    · simp [D, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  have hdsq : D*D = diagonal (fun j => (hP.1.eigenvalues j : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    change (Real.sqrt (hP.1.eigenvalues j) : ℂ) * (Real.sqrt (hP.1.eigenvalues j) : ℂ) = _
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hP.eigenvalues_pos j).le]
  refine ⟨(U : Matrix (Fin d) (Fin d) ℂ)*D, (Unitary.isUnit_coe (U := U)).mul hD, ?_⟩
  rw [Matrix.conjTranspose_mul, hdstar, ← Matrix.mul_assoc,
    Matrix.mul_assoc (U : Matrix (Fin d) (Fin d) ℂ) D D, hdsq]
  exact hP.1.spectral_theorem.symm

theorem exists_spectralCurve_between {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) :
    ∃ (L : Matrix (Fin d) (Fin d) ℂ) (h : Fin d → ℝ), IsUnit L ∧
      spectralCurve L h 0 = P ∧ spectralCurve L h 1 = Q := by
  obtain ⟨A,hA,hAA⟩ := posDef_gram_factor hP
  let B := A⁻¹ * Q * (A⁻¹).conjTranspose
  have hAi : IsUnit A⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hA
  have hB : B.PosDef := hAi.posDef_star_right_conjugate_iff.mpr hQ
  let U := hB.1.eigenvectorUnitary
  let L := A * (U : Matrix (Fin d) (Fin d) ℂ)
  let h := fun j => Real.log (hB.1.eigenvalues j)
  have hAU : IsUnit L := hA.mul (Unitary.isUnit_coe (U := U))
  have hzero : spectralCurve L h 0 = P := by
    simp only [spectralCurve, mul_zero, Real.exp_zero, Complex.ofReal_one, diagonal_one,
      Matrix.mul_one, L, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have hu : (U : Matrix (Fin d) (Fin d) ℂ) *
        (U : Matrix (Fin d) (Fin d) ℂ).conjTranspose = 1 := Unitary.coe_mul_star_self U
    rw [← Matrix.mul_assoc (U : Matrix (Fin d) (Fin d) ℂ), hu, Matrix.one_mul]
    exact hAA
  have hone : spectralCurve L h 1 = Q := by
    have hd : diagonal (fun j => (Real.exp (h j*1) : ℂ)) =
        diagonal (fun j => (hB.1.eigenvalues j : ℂ)) := by
      congr 1
      funext j
      simp only [h, mul_one, Real.exp_log (hB.eigenvalues_pos j)]
    have hspec : (U : Matrix (Fin d) (Fin d) ℂ) *
        diagonal (fun j => (hB.1.eigenvalues j : ℂ)) *
        (U : Matrix (Fin d) (Fin d) ℂ).conjTranspose = B := hB.1.spectral_theorem.symm
    have hc : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp hA)
    have hcstar : (A⁻¹).conjTranspose * A.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, hc, Matrix.conjTranspose_one]
    unfold spectralCurve
    rw [hd]
    change (A*(U : Matrix (Fin d) (Fin d) ℂ))*_ *
      (A*(U : Matrix (Fin d) (Fin d) ℂ)).conjTranspose = Q
    rw [Matrix.conjTranspose_mul]
    calc
      (A*(U : Matrix (Fin d) (Fin d) ℂ))*
          diagonal (fun j => (hB.1.eigenvalues j : ℂ))*
          ((U : Matrix (Fin d) (Fin d) ℂ).conjTranspose*A.conjTranspose) = A*B*A.conjTranspose := by
        have he := congrArg (fun X : Matrix (Fin d) (Fin d) ℂ => A*X*A.conjTranspose) hspec
        simpa only [Matrix.mul_assoc] using he
      _ = Q := by
        dsimp [B]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc, Matrix.one_mul,
          Matrix.mul_assoc, hcstar, Matrix.mul_one]
  exact ⟨L,h,hAU,hzero,hone⟩

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem expansion_common_kernel (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    (v : Fin d → ℂ) (hv : ∀ i, T i *ᵥ v = 0) : v = 0 := by
  let S : Submodule ℂ (Fin d → ℂ) := ⨅ i, LinearMap.ker (T i).mulVecLin
  have hm (i : Fin n) : S.map (T i).mulVecLin = ⊥ := by
    apply le_antisymm _ bot_le
    rintro w ⟨z,hz,rfl⟩
    exact (iInf_le (fun i => LinearMap.ker (T i).mulVecLin) i) hz
  have hsup : (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)) = ⊥ :=
    iSup_eq_bot.mpr hm
  have hdim := congrArg (fun V : Submodule ℂ (Fin r → ℂ) => Module.finrank ℂ V) hsup
  have hd := (hexpand S).trans_eq hdim
  rw [finrank_bot] at hd
  have hz : Module.finrank ℂ S = 0 := by omega
  have he : S = ⊥ := Submodule.finrank_eq_zero.mp hz
  have hmem : v ∈ S := by
    simp only [S, Submodule.mem_iInf, LinearMap.mem_ker]
    exact hv
  simpa [he] using hmem

theorem collectiveMatrix_column_nonzero (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    (L : Matrix (Fin d) (Fin d) ℂ) (hL : IsUnit L) (j : Fin d) :
    ∃ (i : Fin n) (b : Fin r), collectiveMatrix T L b (i,j) ≠ 0 := by
  by_contra h
  push Not at h
  have hz : (fun a => L a j) = (0 : Fin d → ℂ) := by
    apply expansion_common_kernel T hexpand
    intro i
    ext b
    exact h i b
  have hcol : L *ᵥ (Pi.single j 1) = 0 := by
    ext a
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hz] using congrFun hz a
  have he := Matrix.mulVec_injective_of_isUnit hL (hcol.trans (Matrix.mulVec_zero L).symm)
  have hj := congrFun he j
  simp at hj

theorem scalingMap_spectralCurve (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (L : Matrix (Fin d) (Fin d) ℂ) (h : Fin d → ℝ) (u : ℝ) :
    scalingMap T (spectralCurve L h u) =
      collectiveMatrix T L * Matrix.diagonal (fun k : Fin n × Fin d =>
        (Real.exp (h k.2*u) : ℂ)) * (collectiveMatrix T L).conjTranspose := by
  have hi (i : Fin n) : T i * spectralCurve L h u * (T i).conjTranspose =
      (T i * L) * Matrix.diagonal (fun j => (Real.exp (h j*u) : ℂ)) *
        (T i * L).conjTranspose := by
    simp only [spectralCurve, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  ext a b
  simp only [scalingMap, Matrix.sum_apply, hi, Matrix.mul_apply,
    collectiveMatrix, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Prod.mk.injEq, ite_and]
  simp

theorem scalingPotential_strictConvex_spectralCurve
    (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    (L : Matrix (Fin d) (Fin d) ℂ) (hL : IsUnit L) (h : Fin d → ℝ)
    (j : Fin d) (hj : h j ≠ 0) :
    StrictConvexOn ℝ Set.univ (fun u => scalingPotential T (spectralCurve L h u)) := by
  obtain ⟨i,b,hib⟩ := collectiveMatrix_column_nonzero T hexpand L hL j
  have hs := strictConvexOn_log_gram (collectiveMatrix T L) (fun k => h k.2) b (i,j) hib hj
  let c := (3/2 : ℝ)*Real.log (Complex.normSq L.det)
  let s := (3/2 : ℝ)*(∑ j, h j)
  have haff : ConcaveOn ℝ Set.univ (fun u : ℝ => c+s*u) := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ x y hx hy hxy
    simp only [smul_eq_mul]
    nlinarith [congrArg (fun z => c*z) hxy]
  have hc := hs.sub_concaveOn haff
  have he : (fun u => scalingPotential T (spectralCurve L h u)) =
      (fun u => Real.log (1 + collectiveMatrix T L * Matrix.diagonal
        (fun k : Fin n × Fin d => (Real.exp (h k.2*u) : ℂ)) * (collectiveMatrix T L).conjTranspose).det.re) -
      (fun u => c+s*u) := by
    funext u
    simp only [scalingPotential, scalingMap_spectralCurve, spectralCurve_log_det L hL,
      Pi.sub_apply, c, s]
    ring
  rw [he]
  exact hc

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Minimizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Existence and uniqueness of scaling minimizers. -/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem posDef_det_re_pos {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) :
    0 < P.det.re := by
  exact (RCLike.pos_iff.mp hP.det_pos).1

theorem continuousOn_scalingPotential (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun P : HermitianMatrices d => scalingPotential T P.val)
      (spectralWindow d a b) := by
  have hP : Continuous (fun P : HermitianMatrices d => P.val.det.re) :=
    Complex.continuous_re.comp continuous_subtype_val.matrix_det
  have hD : Continuous (fun P : HermitianMatrices d => scalingMap T P.val) :=
    continuous_scalingMap (fun _ : HermitianMatrices d => T) continuous_const
      (fun P : HermitianMatrices d => P.val) continuous_subtype_val
  have hQ : Continuous (fun P : HermitianMatrices d => (1+scalingMap T P.val).det.re) :=
    Complex.continuous_re.comp (continuous_const.add hD).matrix_det
  have hp : ContinuousOn (fun P : HermitianMatrices d => Real.log P.val.det.re)
      (spectralWindow d a b) := hP.continuousOn.log (fun P h => ne_of_gt
    (posDef_det_re_pos (spectralWindow_posDef ha h)))
  have hq : ContinuousOn (fun P : HermitianMatrices d => Real.log (1+scalingMap T P.val).det.re)
      (spectralWindow d a b) := hQ.continuousOn.log (fun P h => ne_of_gt (posDef_det_re_pos
    (Matrix.PosDef.one.add_posSemidef (scalingMap_positive T (spectralWindow_posDef ha h).posSemidef))))
  exact hq.sub (hp.const_mul (3/2))

/-- Minimizing on a spectral window gives a global minimum when all
points below the comparison value lie in the window. -/
theorem scaling_minimum_of_sublevel_bound
    (T : Fin n → Matrix (Fin r) (Fin d) ℂ) {a b C : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hbound : ∀ (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosDef),
      scalingPotential T P ≤ C → (⟨P,hP.1⟩ : HermitianMatrices d) ∈ spectralWindow d a b)
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.PosDef) (hQC : scalingPotential T Q ≤ C) :
    ∃ P : Matrix (Fin d) (Fin d) ℂ, P.PosDef ∧
      ∀ R : Matrix (Fin d) (Fin d) ℂ, R.PosDef → scalingPotential T P ≤ scalingPotential T R := by
  obtain ⟨P,hP,hmin⟩ := (isCompact_spectralWindow ha.le hb).exists_isMinOn
    ⟨⟨Q,hQ.1⟩, hbound Q hQ hQC⟩ (continuousOn_scalingPotential T ha)
  refine ⟨P.val, spectralWindow_posDef ha hP, ?_⟩
  intro R hR
  by_cases hRC : scalingPotential T R ≤ C
  · have hm := hmin (hbound R hR hRC)
    exact hm
  · have hm := hmin (hbound Q hQ hQC)
    exact hm.trans (hQC.trans (le_of_lt (lt_of_not_ge hRC)))

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem scaling_minimizer_unique (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    {P Q : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (hminP : ∀ R : Matrix (Fin d) (Fin d) ℂ, R.PosDef → scalingPotential T P ≤ scalingPotential T R)
    (hminQ : ∀ R : Matrix (Fin d) (Fin d) ℂ, R.PosDef → scalingPotential T Q ≤ scalingPotential T R) :
    P = Q := by
  by_contra hneq
  obtain ⟨L,h,hL,hzero,hone⟩ := exists_spectralCurve_between hP hQ
  have hnonzero : ∃ j, h j ≠ 0 := by
    by_contra hn
    push Not at hn
    have he : spectralCurve L h 0 = spectralCurve L h 1 := by
      simp only [spectralCurve, hn, zero_mul]
    exact hneq (hzero.symm.trans (he.trans hone))
  obtain ⟨j,hj⟩ := hnonzero
  have hs := scalingPotential_strictConvex_spectralCurve T hexpand L hL h j hj
  have hstrict := hs.2
  have hmid := hstrict (x := 0) (y := 1) (a := (1/2 : ℝ)) (b := (1/2 : ℝ))
    (Set.mem_univ _) (Set.mem_univ _) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, hzero, hone] at hmid
  have hpq := hminP Q hQ
  have hqp := hminQ P hP
  have hpm := hminP (spectralCurve L h (1/2)) (spectralCurve_posDef L hL h _)
  linarith

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Critical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Log-determinant derivatives, critical points, and normalized tuple relations. -/

noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {d : ℕ}

theorem posDef_iff_decreasing_pos {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian) :
    P.PosDef ↔ ∀ i, 0 < decreasingEigenvalues hP i := by
  constructor
  · intro h i; exact decreasingEigenvalues_pos h i
  · intro h
    apply hP.posDef_iff_eigenvalues_pos.mpr
    intro i
    have hi := h ((spectralIndex d).symm i)
    rw [← eigenvalues_spectralIndex, Equiv.apply_symm_apply] at hi
    exact hi

theorem isOpen_posDef_hermitian : IsOpen {P : HermitianMatrices d | P.val.PosDef} := by
  have he : {P : HermitianMatrices d | P.val.PosDef} =
      ⋂ i : Fin d, {P : HermitianMatrices d | 0 < decreasingEigenvalues P.property i} := by
    ext P
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, posDef_iff_decreasing_pos P.property]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (continuous_decreasingEigenvalues i)

/-- A Hermitian direction remains in the positive cone near a positive
point, providing the open domain needed for the critical-point argument. -/
theorem eventually_posDef_add_smul {P K : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosDef) (hK : K.IsHermitian) :
    ∀ᶠ u : ℝ in 𝓝 0, (P+(u : ℂ) • K).PosDef := by
  have hline (u : ℝ) : (P+(u : ℂ) • K).IsHermitian := by
    change (P+(u : ℂ) • K).conjTranspose = P+(u : ℂ) • K
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hP.1.eq, hK.eq]
    congr 1
    simp
  let f : ℝ → HermitianMatrices d := fun u => ⟨P+(u : ℂ) • K, hline u⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hm : f 0 ∈ {P : HermitianMatrices d | P.val.PosDef} := by simpa [f] using hP
  exact hf.continuousAt (isOpen_posDef_hermitian.mem_nhds hm)

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix Polynomial
namespace Kaplansky
variable {d : ℕ}

/-- Jacobi's directional formula, derived from the polynomial determinant
expansion at the identity and an actual inverse factorization. -/
theorem hasDerivAt_det_add_smul (P K : Matrix (Fin d) (Fin d) ℂ) (hP : IsUnit P) :
    HasDerivAt (fun z : ℂ => (P+z • K).det) (P.det * (P⁻¹*K).trace) 0 := by
  let M := P⁻¹*K
  let p : ℂ[X] := (1 + (X : ℂ[X]) • M.map C).det
  have hd := p.hasDerivAt (0 : ℂ)
  have hp : p.derivative.eval 0 = M.trace := Matrix.derivative_det_one_add_X_smul M
  rw [hp] at hd
  have hev (z : ℂ) : p.eval z = (1+z • M).det := by
    simp only [p, eval_det]
    congr 1
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, mul_comm]
  have hi : P*P⁻¹=1 := Matrix.mul_nonsing_inv P (P.isUnit_iff_isUnit_det.mp hP)
  have hf : (fun z : ℂ => (P+z • K).det) = fun z => P.det * p.eval z := by
    funext z
    rw [hev, ← Matrix.det_mul]
    congr 1
    dsimp [M]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hi, Matrix.one_mul]
  rw [hf]
  exact hd.const_mul P.det

theorem hasDerivAt_log_det_add_smul {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosDef) (K : Matrix (Fin d) (Fin d) ℂ) :
    HasDerivAt (fun u : ℝ => Real.log (P+(u : ℂ) • K).det.re)
      (P⁻¹*K).trace.re 0 := by
  have hd := (hasDerivAt_det_add_smul P K hP.isUnit).real_of_complex
  have hn : (P+(↑(0 : ℝ) : ℂ) • K).det.re ≠ 0 := by
    simpa using ne_of_gt (posDef_det_re_pos hP)
  have hlog := hd.log hn
  have him : P.det.im = 0 := hP.posSemidef.det_nonneg.2.symm
  have hv : (P.det * (P⁻¹*K).trace).re / (P+(↑(0 : ℝ) : ℂ) • K).det.re =
      (P⁻¹*K).trace.re := by
    simp only [Complex.ofReal_zero, zero_smul, add_zero, Complex.mul_re, him, zero_mul, sub_zero]
    exact mul_div_cancel_left₀ _ (ne_of_gt (posDef_det_re_pos hP))
  rw [hv] at hlog
  exact hlog

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

def scalingAdjoint (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (Q : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i, (T i).conjTranspose * Q * T i

theorem scalingAdjoint_trace (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (Q : Matrix (Fin r) (Fin r) ℂ) (K : Matrix (Fin d) (Fin d) ℂ) :
    (scalingAdjoint T Q * K).trace = (Q * scalingMap T K).trace := by
  simp only [scalingAdjoint, scalingMap, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem scalingAdjoint_positive (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {Q : Matrix (Fin r) (Fin r) ℂ} (hQ : Q.PosSemidef) :
    (scalingAdjoint T Q).PosSemidef :=
  Matrix.posSemidef_sum _ (fun i _ => hQ.conjTranspose_mul_mul_same (T i))

theorem hasDerivAt_scalingPotential {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef)
    (T : Fin n → Matrix (Fin r) (Fin d) ℂ) (K : Matrix (Fin d) (Fin d) ℂ) :
    HasDerivAt (fun u : ℝ => scalingPotential T (P+(u : ℂ) • K))
      (((1+scalingMap T P)⁻¹ * scalingMap T K).trace.re - (3/2)*(P⁻¹*K).trace.re) 0 := by
  have hQ : (1+scalingMap T P).PosDef :=
    Matrix.PosDef.one.add_posSemidef (scalingMap_positive T hP.posSemidef)
  have hd := (hasDerivAt_log_det_add_smul hQ (scalingMap T K)).sub
    ((hasDerivAt_log_det_add_smul hP K).const_mul (3/2))
  have he : (fun u : ℝ => scalingPotential T (P+(u : ℂ) • K)) =
      (fun u : ℝ => Real.log (1+scalingMap T P+(u : ℂ) • scalingMap T K).det.re) -
      (fun u : ℝ => (3/2)*Real.log (P+(u : ℂ) • K).det.re) := by
    funext u
    simp only [scalingPotential, Pi.sub_apply]
    congr 3
    simp [scalingMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib,
      Finset.smul_sum, add_assoc]
  rw [he]
  exact hd

theorem scaling_minimizer_critical (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef)
    (hmin : ∀ R : Matrix (Fin d) (Fin d) ℂ, R.PosDef → scalingPotential T P ≤ scalingPotential T R) :
    scalingAdjoint T (1+scalingMap T P)⁻¹ = (3/2 : ℂ) • P⁻¹ := by
  let Q := 1+scalingMap T P
  let C := scalingAdjoint T Q⁻¹ - (3/2 : ℂ) • P⁻¹
  have hQ : Q.PosDef := Matrix.PosDef.one.add_posSemidef (scalingMap_positive T hP.posSemidef)
  have hC : C.IsHermitian := by
    change (scalingAdjoint T Q⁻¹ - (3/2 : ℂ) • P⁻¹).conjTranspose = _
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      (scalingAdjoint_positive T hQ.inv.posSemidef).1.eq, hP.inv.1.eq]
    norm_num
    rfl
  have hdirection (K : Matrix (Fin d) (Fin d) ℂ) (hK : K.IsHermitian) :
      ((C*K).trace).re = 0 := by
    have hlocal : IsLocalMin (fun u : ℝ => scalingPotential T (P+(u : ℂ) • K)) 0 := by
      filter_upwards [eventually_posDef_add_smul hP hK] with u hu
      simpa only [Complex.ofReal_zero, zero_smul, add_zero] using hmin _ hu
    have hd := hlocal.hasDerivAt_eq_zero (hasDerivAt_scalingPotential hP T K)
    have he : (C*K).trace = (Q⁻¹*scalingMap T K).trace - (3/2 : ℂ)*(P⁻¹*K).trace := by
      simp only [C, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
        scalingAdjoint_trace, smul_eq_mul]
    rw [he]
    norm_num [Complex.sub_re, Complex.mul_re]
    exact hd
  have hr := hdirection C hC
  have hpos : (C.conjTranspose*C).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  have him : (C*C).trace.im = 0 := by
    have ht := hpos.trace_nonneg
    rw [hC.eq] at ht
    exact ht.2.symm
  have hz : (C.conjTranspose*C).trace = 0 := by
    rw [hC.eq]
    apply Complex.ext
    · exact hr
    · exact him
  have hzero : C = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz
  exact sub_eq_zero.mp hzero

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

def normalizedTuple (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (J : Matrix (Fin r) (Fin r) ℂ) :
    Fin n → Matrix (Fin r) (Fin d) ℂ :=
  fun i => (Real.sqrt (2/3 : ℝ) : ℂ) • (J*T i*A)

theorem normalizedTuple_column (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (J : Matrix (Fin r) (Fin r) ℂ) :
    (∑ i, (normalizedTuple T A J i).conjTranspose * normalizedTuple T A J i) =
      (2/3 : ℂ) • (A.conjTranspose * scalingAdjoint T (J.conjTranspose*J) * A) := by
  have hs : (Real.sqrt (2/3 : ℝ) : ℂ) * star (Real.sqrt (2/3 : ℝ) : ℂ) = (2/3 : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [normalizedTuple, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hs, scalingAdjoint, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem normalizedTuple_row (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (J : Matrix (Fin r) (Fin r) ℂ) :
    (∑ i, normalizedTuple T A J i * (normalizedTuple T A J i).conjTranspose) =
      (2/3 : ℂ) • (J * scalingMap T (A*A.conjTranspose) * J.conjTranspose) := by
  have hs : star (Real.sqrt (2/3 : ℝ) : ℂ) * (Real.sqrt (2/3 : ℝ) : ℂ) = (2/3 : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [normalizedTuple, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hs, scalingMap, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Continuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous dependence of the unique normalized scaling. -/

namespace Kaplansky

theorem continuous_unique_minimizer {X K : Type*}
    [TopologicalSpace X] [TopologicalSpace K] [CompactSpace K]
    (g : X × K → ℝ) (hg : Continuous g) (m : X → K)
    (hmin : ∀ x z, g (x,m x) ≤ g (x,z))
    (hunique : ∀ x y, (∀ z, g (x,y) ≤ g (x,z)) → y = m x) :
    Continuous m := by
  let G : Set (X × K) := {p | ∀ z, g p ≤ g (p.1,z)}
  have hG : IsClosed G := by
    simp only [G, Set.ofPred_forall]
    apply isClosed_iInter
    intro z
    exact isClosed_le hg (hg.comp (continuous_fst.prodMk continuous_const))
  rw [continuous_iff_isClosed]
  intro s hs
  have heq : m ⁻¹' s = Prod.fst '' (G ∩ Prod.snd ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x,m x), ⟨hmin x, hx⟩, rfl⟩
    · rintro ⟨⟨x',y⟩,⟨hy,hys⟩,hxy⟩
      change x' = x at hxy
      subst x'
      have he := hunique x y hy
      simpa only [Set.mem_preimage, he] using hys
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ (hG.inter (hs.preimage continuous_snd))

end Kaplansky

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

theorem continuous_scalingPotential {Y : Type*} [TopologicalSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (P : Y → Matrix (Fin d) (Fin d) ℂ) (hP : Continuous P) (hpos : ∀ y, (P y).PosDef) :
    Continuous (fun y => scalingPotential (T y) (P y)) := by
  have hp : Continuous (fun y => (P y).det.re) := Complex.continuous_re.comp hP.matrix_det
  have hd := continuous_scalingMap T hT P hP
  have hq : Continuous (fun y => (1+scalingMap (T y) (P y)).det.re) :=
    Complex.continuous_re.comp (continuous_const.add hd).matrix_det
  exact (hq.log (fun y => ne_of_gt (posDef_det_re_pos
    (Matrix.PosDef.one.add_posSemidef (scalingMap_positive (T y) (hpos y).posSemidef))))).sub
    ((hp.log (fun y => ne_of_gt (posDef_det_re_pos (hpos y)))).const_mul (3/2))

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem gramFactor_inverse_identity (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A) :
    A.conjTranspose * (A*A.conjTranspose)⁻¹ * A = 1 := by
  have hi : A⁻¹*A=1 := Matrix.nonsing_inv_mul A (A.isUnit_iff_isUnit_det.mp hA)
  have his : A.conjTranspose * (A⁻¹).conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, hi, Matrix.conjTranspose_one]
  rw [Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv,
    ← Matrix.mul_assoc, his, Matrix.one_mul, hi]

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

/-- The normalization relations for any invertible Gram factors of a
minimizer and its target matrix. -/
theorem normalizedTuple_of_minimizer (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef)
    (hmin : ∀ R : Matrix (Fin d) (Fin d) ℂ, R.PosDef → scalingPotential T P ≤ scalingPotential T R)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A) (hAA : A*A.conjTranspose=P)
    (B : Matrix (Fin r) (Fin r) ℂ) (hB : IsUnit B) (hBB : B*B.conjTranspose=1+scalingMap T P) :
    (∑ i, (normalizedTuple T A B⁻¹ i).conjTranspose * normalizedTuple T A B⁻¹ i) = 1 ∧
      ((2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
        ∑ i, normalizedTuple T A B⁻¹ i * (normalizedTuple T A B⁻¹ i).conjTranspose).PosSemidef := by
  have hcrit := scaling_minimizer_critical T hP hmin
  let Q := 1+scalingMap T P
  let J := B⁻¹
  change B*B.conjTranspose=Q at hBB
  have hJ : J.conjTranspose*J = Q⁻¹ := by
    rw [← hBB, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv]
  have hAP : A.conjTranspose*P⁻¹*A = 1 := by
    rw [← hAA]
    exact gramFactor_inverse_identity A hA
  have hJB : J*B=1 := Matrix.nonsing_inv_mul B (B.isUnit_iff_isUnit_det.mp hB)
  have hJQ : J*Q*J.conjTranspose=1 := by
    rw [← hBB]
    have hs : B.conjTranspose*J.conjTranspose=1 := by
      rw [← Matrix.conjTranspose_mul, hJB, Matrix.conjTranspose_one]
    rw [← Matrix.mul_assoc, hJB, Matrix.one_mul, hs]
  refine ⟨?_, ?_⟩
  · rw [normalizedTuple_column, hJ, hcrit, Matrix.mul_smul, Matrix.smul_mul, hAP, smul_smul]
    norm_num
  · rw [normalizedTuple_row, hAA]
    have hD : scalingMap T P = Q-1 := by dsimp [Q]; abel
    rw [hD, Matrix.mul_sub, Matrix.sub_mul, hJQ, Matrix.mul_one, smul_sub]
    have he : (2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
        ((2/3 : ℂ) • 1 - (2/3 : ℂ) • (J*J.conjTranspose)) =
        (2/3 : ℂ) • (J*J.conjTranspose) := by abel
    rw [he]
    exact (Matrix.posSemidef_self_mul_conjTranspose J).smul (by constructor <;> norm_num)

theorem continuous_matrix_sqrt {Y : Type*} [TopologicalSpace Y]
    (P : Y → Matrix (Fin d) (Fin d) ℂ) (hP : Continuous P) (hpos : ∀ y, (P y).PosDef) :
    Continuous (fun y => CFC.sqrt (P y)) :=
  CFC.continuousOn_sqrt.comp_continuous hP (fun y => (hpos y).posSemidef.nonneg)

theorem continuous_matrix_inverse {Y : Type*} [TopologicalSpace Y]
    (P : Y → Matrix (Fin d) (Fin d) ℂ) (hP : Continuous P) (hunit : ∀ y, IsUnit (P y)) :
    Continuous (fun y => (P y)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hi : ContinuousAt Ring.inverse (P y).det := by
    rw [show (Ring.inverse : ℂ → ℂ) = Inv.inv from funext Ring.inverse_eq_inv]
    exact continuousAt_inv₀
      ((P y).isUnit_iff_isUnit_det.mp (hunit y)).ne_zero
  exact (continuousAt_matrix_inv (P y) hi).comp hP.continuousAt

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Sections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Gluing, homotopy, and operations on vector bundle sections. -/

section
open Bundle Topology
namespace Kaplansky

variable {𝕜 Y F I : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace Y] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Gluing compatible local coordinate functions produces a continuous
section of the ordinary, potentially nontrivial vector bundle. -/
theorem glue_core_section (H : VectorBundleCore 𝕜 Y F I)
    (L : I → Y → F) (hL : ∀ a, ContinuousOn (L a) (H.baseSet a))
    (hcompat : ∀ a b y, y ∈ H.baseSet a → y ∈ H.baseSet b →
      H.coordChange a b y (L a y) = L b y) :
    ∃ s : ∀ y, H.Fiber y,
      Continuous (fun y => TotalSpace.mk' F y (s y)) ∧
      ∀ a y, y ∈ H.baseSet a → (H.localTriv a ⟨y,s y⟩).2 = L a y := by
  let s : ∀ y, H.Fiber y := fun y => L (H.indexAt y) y
  have he (a : I) (y : Y) (hy : y ∈ H.baseSet a) :
      (H.localTriv a ⟨y,s y⟩).2 = L a y :=
    hcompat (H.indexAt y) a y (H.mem_baseSet_at y) hy
  refine ⟨s, ?_, he⟩
  rw [continuous_iff_continuousAt]
  intro y
  rw [FiberBundle.continuousAt_section]
  have hn := (H.isOpen_baseSet (H.indexAt y)).mem_nhds (H.mem_baseSet_at y)
  have hc := (hL (H.indexAt y) y (H.mem_baseSet_at y)).continuousAt hn
  apply hc.congr_of_eventuallyEq
  filter_upwards [hn] with z hz
  exact he (H.indexAt y) z hz

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
variable {𝕜 Y V : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace Y]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module 𝕜 (E y)]
variable [∀ y, TopologicalSpace (E y)] [TopologicalSpace (TotalSpace V E)]
variable [FiberBundle V E] [VectorBundle 𝕜 V E]

include 𝕜 in
/-- Finite sums of continuous local sections in an ordinary vector bundle. -/
theorem continuousOn_bundle_sum {ι : Type*} (u : Finset ι) (v : ι → ∀ y, E y) {s : Set Y}
    (hv : ∀ i ∈ u, ContinuousOn (fun y => TotalSpace.mk' V y (v i y)) s) :
    ContinuousOn (fun y => TotalSpace.mk' V y (∑ i ∈ u, v i y)) s := by
  intro y hy
  rw [FiberBundle.continuousWithinAt_section]
  have hc : ContinuousWithinAt
      (fun z => ∑ i ∈ u, ((trivializationAt V E y) ⟨z,v i z⟩).2) s y :=
    tendsto_finsetSum u (fun i hi =>
    ((FiberBundle.continuousWithinAt_section V).mp (hv i hi y hy)))
  apply hc.congr_of_eventuallyEq
  ·
    have hn := (trivializationAt V E y).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt V E y)
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn] with z hz
    exact (map_sum (((trivializationAt V E y).linear 𝕜 hz).mk' _) (fun i => v i z) u)
  · exact map_sum (((trivializationAt V E y).linear 𝕜 (mem_baseSet_trivializationAt V E y)).mk' _) (fun i => v i y) u

/-- Scalar multiplication of continuous local sections. -/
theorem continuousOn_bundle_smul (f : Y → 𝕜) (v : ∀ y, E y) {s : Set Y}
    (hf : ContinuousOn f s) (hv : ContinuousOn (fun y => TotalSpace.mk' V y (v y)) s) :
    ContinuousOn (fun y => TotalSpace.mk' V y (f y • v y)) s := by
  intro y hy
  rw [FiberBundle.continuousWithinAt_section]
  have hc := (hf y hy).smul ((FiberBundle.continuousWithinAt_section V).mp (hv y hy))
  apply hc.congr_of_eventuallyEq
  ·
    have hn := (trivializationAt V E y).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt V E y)
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn] with z hz
    exact (((trivializationAt V E y).linear 𝕜 hz).map_smul (f z) (v z))
  · exact ((trivializationAt V E y).linear 𝕜 (mem_baseSet_trivializationAt V E y)).map_smul (f y) (v y)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unitary naturality and canonical local matrix scaling. -/

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

def frameTuple (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ) :=
  fun i => V * T i * Uᴴ

theorem scalingMap_frame (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ)
    (hU : Uᴴ * U = 1) (P : Matrix (Fin d) (Fin d) ℂ) :
    scalingMap (frameTuple T U V) (U * P * Uᴴ) = V * scalingMap T P * Vᴴ := by
  simp only [scalingMap, frameTuple, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]

theorem det_unitary_conjugate (U P : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) : (U * P * Uᴴ).det = P.det := by
  have hdet := congrArg Matrix.det hU
  simp only [Matrix.det_mul, Matrix.det_one] at hdet
  simp only [Matrix.det_mul]
  calc
    U.det * P.det * Uᴴ.det = P.det * (Uᴴ.det * U.det) := by ring
    _ = P.det := by rw [hdet, mul_one]

theorem scalingPotential_frame (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    (P : Matrix (Fin d) (Fin d) ℂ) :
    scalingPotential (frameTuple T U V) (U * P * Uᴴ) = scalingPotential T P := by
  have hQ : 1 + V * scalingMap T P * Vᴴ = V * (1 + scalingMap T P) * Vᴴ := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hV']
  simp only [scalingPotential, scalingMap_frame T U V hU, hQ,
    det_unitary_conjugate U P hU, det_unitary_conjugate V _ hV]

theorem posDef_unitary_conjugate (U P : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (hP : P.PosDef) : (U * P * Uᴴ).PosDef := by
  have hu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr (by
    have hd := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact isUnit_iff_ne_zero.mpr (by intro hz; simp [hz] at hd))
  exact hu.posDef_star_right_conjugate_iff.mpr hP

/-- A minimizer transports to any other unitary frame. -/
theorem scaling_minimizer_frame (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosDef)
    (hmin : ∀ R, R.PosDef → scalingPotential T P ≤ scalingPotential T R) :
    (U * P * Uᴴ).PosDef ∧ ∀ R, R.PosDef →
      scalingPotential (frameTuple T U V) (U * P * Uᴴ) ≤
        scalingPotential (frameTuple T U V) R := by
  refine ⟨posDef_unitary_conjugate U P hU hP, ?_⟩
  intro R hR
  have hR' := posDef_unitary_conjugate Uᴴ R (by simpa using hU') hR
  have he : U * (Uᴴ * R * U) * Uᴴ = R := by
    simp only [← Matrix.mul_assoc, hU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hU', Matrix.mul_one]
  have hi := scalingPotential_frame T U V hU hV hV' (Uᴴ * R * U)
  rw [he] at hi
  rw [scalingPotential_frame T U V hU hV hV' P, hi]
  exact hmin _ (by simpa using hR')

/-- The positive square root, not an arbitrary Gram factor, is equivariant. -/
theorem sqrt_unitary_conjugate (U P : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (hP : P.PosSemidef) :
    CFC.sqrt (U * P * Uᴴ) = U * CFC.sqrt P * Uᴴ := by
  apply CFC.sqrt_unique
  · calc
      (U * CFC.sqrt P * Uᴴ) * (U * CFC.sqrt P * Uᴴ) =
          U * (CFC.sqrt P * CFC.sqrt P) * Uᴴ := by
            simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
      _ = U * P * Uᴴ := by rw [CFC.sqrt_mul_sqrt_self P hP.nonneg]
  · exact ((CFC.sqrt_nonneg P).posSemidef.mul_mul_conjTranspose_same U).nonneg

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

def Expanding (T : Fin n → Matrix (Fin r) (Fin d) ℂ) : Prop :=
  ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
    Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ))

theorem inverse_unitary_conjugate (U P : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) :
    (U * P * Uᴴ)⁻¹ = U * P⁻¹ * Uᴴ := by
  have hi : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hU
  have hi' : (Uᴴ)⁻¹ = U := Matrix.inv_eq_left_inv hU'
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hi, hi']
  simp only [Matrix.mul_assoc]

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Descent of canonical scaling and Hermitian bundle homomorphisms. -/

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky

variable {n d r : ℕ}

def frameTupleLinear (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ) :
    (Fin n → Matrix (Fin r) (Fin d) ℂ) →ₗ[ℂ] (Fin n → Matrix (Fin r) (Fin d) ℂ) where
  toFun T := frameTuple T U V
  map_add' T S := by ext i; simp [frameTuple, Matrix.mul_add, Matrix.add_mul]
  map_smul' z T := by ext i; simp [frameTuple, Matrix.mul_smul, Matrix.smul_mul]

def frameTupleCLM (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ) :
    (Fin n → Matrix (Fin r) (Fin d) ℂ) →L[ℂ] (Fin n → Matrix (Fin r) (Fin d) ℂ) :=
  ⟨frameTupleLinear U V, (frameTupleLinear U V).continuous_of_finiteDimensional⟩

theorem frameTupleCLM_apply (U : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin r) (Fin r) ℂ) (T : Fin n → Matrix (Fin r) (Fin d) ℂ) :
    frameTupleCLM U V T = frameTuple T U V := rfl

theorem frameTuple_comp (U₁ U₂ : Matrix (Fin d) (Fin d) ℂ)
    (V₁ V₂ : Matrix (Fin r) (Fin r) ℂ) (T : Fin n → Matrix (Fin r) (Fin d) ℂ) :
    frameTuple (frameTuple T U₁ V₁) U₂ V₂ = frameTuple T (U₂ * U₁) (V₂ * V₁) := by
  funext i
  simp only [frameTuple, conjTranspose_mul, Matrix.mul_assoc]

theorem continuousOn_frameTupleCLM {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (U : Y → Matrix (Fin d) (Fin d) ℂ) (V : Y → Matrix (Fin r) (Fin r) ℂ)
    (hU : ContinuousOn U s) (hV : ContinuousOn V s) :
    ContinuousOn (fun y => frameTupleCLM (n := n) (U y) (V y)) s := by
  apply continuousOn_clm_apply.mpr
  intro T
  apply continuousOn_pi.mpr
  intro i
  rw [continuousOn_iff_continuous_domRestrict]
  have hu := continuousOn_iff_continuous_domRestrict.mp hU
  have hv := continuousOn_iff_continuous_domRestrict.mp hV
  exact (hv.matrix_mul continuous_const).matrix_mul hu.matrix_conjTranspose

/-- Construct the actual Hom-tuple vector bundle from transition matrices
and their verified cocycle. There is no bundle-realization hypothesis. -/
def matrixHomCore {Y I : Type*} [TopologicalSpace Y]
    (O : I → Set Y) (hO : ∀ i, IsOpen (O i)) (idx : Y → I) (hat : ∀ y, y ∈ O (idx y))
    (U : I → I → Y → Matrix (Fin d) (Fin d) ℂ)
    (V : I → I → Y → Matrix (Fin r) (Fin r) ℂ)
    (hUc : ∀ i j, ContinuousOn (U i j) (O i ∩ O j))
    (hVc : ∀ i j, ContinuousOn (V i j) (O i ∩ O j))
    (hUs : ∀ i y, y ∈ O i → U i i y = 1)
    (hVs : ∀ i y, y ∈ O i → V i i y = 1)
    (hUm : ∀ i j k y, y ∈ O i → y ∈ O j → y ∈ O k → U j k y * U i j y = U i k y)
    (hVm : ∀ i j k y, y ∈ O i → y ∈ O j → y ∈ O k → V j k y * V i j y = V i k y) :
    VectorBundleCore ℂ Y (Fin n → Matrix (Fin r) (Fin d) ℂ) I where
  baseSet := O
  isOpen_baseSet := hO
  indexAt := idx
  mem_baseSet_at := hat
  coordChange i j y := frameTupleCLM (U i j y) (V i j y)
  coordChange_self i y hy T := by
    change frameTuple T (U i i y) (V i i y) = T
    rw [hUs i y hy, hVs i y hy]
    funext k
    simp [frameTuple]
  continuousOn_coordChange i j := continuousOn_frameTupleCLM _ _ (hUc i j) (hVc i j)
  coordChange_comp i j k y hy T := by
    simp only [frameTupleCLM_apply, frameTuple_comp, hUm i j k y hy.1.1 hy.1.2 hy.2,
      hVm i j k y hy.1.1 hy.1.2 hy.2]

end Kaplansky

end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Expansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic and finite-block expansion inequalities. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace Kaplansky
variable {n d r : ℕ} {E F D R : Type*}
variable [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
variable [AddCommGroup D] [Module ℂ D] [AddCommGroup R] [Module ℂ R]

theorem basis_matrix_action (b : Module.Basis (Fin d) ℂ E) (c : Module.Basis (Fin r) ℂ F)
    (T : E →ₗ[ℂ] F) :
    (LinearMap.toMatrix b c T).mulVecLin =
      c.equivFun.toLinearMap.comp (T.comp b.equivFun.symm.toLinearMap) := by
  apply LinearMap.ext
  intro x
  have he := LinearMap.toMatrix_mulVec_repr b c T (b.equivFun.symm x)
  change (LinearMap.toMatrix b c T) *ᵥ b.equivFun (b.equivFun.symm x) =
    c.equivFun (T (b.equivFun.symm x)) at he
  rw [LinearEquiv.apply_symm_apply] at he
  exact he

end Kaplansky

end

noncomputable section
open scoped BigOperators
open LinearMap
namespace Kaplansky
variable {n : ℕ} {E F G H : Type*}
variable [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
variable [AddCommGroup G] [Module ℂ G] [AddCommGroup H] [Module ℂ H]

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

/-- Expansion restricted to the dimensions used by the sixteen small-subspace maps. -/
def ExpandingThrough (m : ℕ) (T : Fin n → E →ₗ[ℂ] G) : Prop :=
  ∀ S : Submodule ℂ E, Module.finrank ℂ S ≤ m →
    2 * Module.finrank ℂ S ≤ Module.finrank ℂ (⨆ i, S.map (T i) : Submodule ℂ G)

end Kaplansky

end

noncomputable section
namespace Kaplansky
variable {n : ℕ}

def blockDiagonal {k : ℕ} {E : Fin k → Type*} {F : Fin k → Type*}
    [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)]
    [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)]
    (T : ∀ j, Fin n → E j →ₗ[ℂ] F j) (i : Fin n) : (∀ j, E j) →ₗ[ℂ] (∀ j, F j) where
  toFun v j := T j i (v j)
  map_add' v w := by funext j; exact map_add (T j i) _ _
  map_smul' z v := by funext j; exact map_smul (T j i) _ _

end Kaplansky

end

noncomputable section
namespace Kaplansky
variable {E F G H : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
  [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ H]

theorem image_iSup_finrank_le {n N : ℕ} (T : Fin n → E →ₗ[ℂ] F)
    (U : Fin N → E →ₗ[ℂ] H) (f : F →ₗ[ℂ] H) (hf : Function.Injective f)
    (a : Fin n → Fin N) (ha : ∀ i, U (a i)=f.comp (T i)) (S : Submodule ℂ E) :
    Module.finrank ℂ (⨆ i, S.map (T i) : Submodule ℂ F) ≤ Module.finrank ℂ (⨆ i, S.map (U i) : Submodule ℂ H) := by
  have he := (Submodule.equivMapOfInjective f hf (⨆ i, S.map (T i) : Submodule ℂ F)).finrank_eq
  rw [he]
  apply Submodule.finrank_mono
  rw [Submodule.map_iSup]
  apply iSup_le
  intro i
  rw [← Submodule.map_comp,← ha i]
  exact le_iSup (fun q : Fin N => S.map (U q)) (a i)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Maps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Continuous bundle maps, adjoints, and normalized Hermitian scaling. -/

section
open Bundle Topology
namespace Kaplansky
variable {𝕜 Y V X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace Y] [TopologicalSpace X]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module 𝕜 (E y)]
variable [∀ y, TopologicalSpace (E y)] [TopologicalSpace (TotalSpace V E)]
variable [FiberBundle V E] [VectorBundle 𝕜 V E]

include 𝕜 in
theorem continuousOn_bundle_sum_over {ι : Type*} (b : X → Y) {s : Set X}
    (hb : ContinuousOn b s) (u : Finset ι) (v : ι → ∀ x, E (b x))
    (hv : ∀ i ∈ u, ContinuousOn (fun x => TotalSpace.mk' V (b x) (v i x)) s) :
    ContinuousOn (fun x => TotalSpace.mk' V (b x) (∑ i ∈ u, v i x)) s := by
  intro x hx
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨hb x hx, ?_⟩
  have hc : ContinuousWithinAt
      (fun z => ∑ i ∈ u, ((trivializationAt V E (b x)) ⟨b z,v i z⟩).2) s x :=
    tendsto_finsetSum u (fun i hi =>
      ((FiberBundle.continuousWithinAt_totalSpace V _).mp (hv i hi x hx)).2)
  apply hc.congr_of_eventuallyEq
  · have hn := (trivializationAt V E (b x)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt V E (b x))
    filter_upwards [(hb x hx) hn] with z hz
    exact map_sum (((trivializationAt V E (b x)).linear 𝕜 hz).mk' _) (fun i => v i z) u
  · exact map_sum (((trivializationAt V E (b x)).linear 𝕜
      (mem_baseSet_trivializationAt V E (b x))).mk' _) (fun i => v i x) u

end Kaplansky

end

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix
namespace Kaplansky
variable {n d r : ℕ} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ E] in
theorem inner_toMatrix (b : OrthonormalBasis (Fin d) ℂ E) (A : E →ₗ[ℂ] E) (v : E) :
    inner ℂ v (A v) = star (b.toBasis.repr v) ⬝ᵥ
      (LinearMap.toMatrix b.toBasis b.toBasis A) *ᵥ b.toBasis.repr v := by
  rw [LinearMap.toMatrix_mulVec_repr]
  calc
    inner ℂ v (A v) = ∑ i, star (b.repr v i) * b.repr (A v) i := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, mul_comm] using
        (b.repr.inner_map_map v (A v)).symm
    _ = _ := by simp only [dotProduct, Pi.star_apply, OrthonormalBasis.coe_toBasis_repr_apply]

/-- Transfer the normalized matrix relations to actual adjoints on the
original finite-dimensional Hermitian fibers. -/
theorem intrinsic_relations_of_matrix
    (b : OrthonormalBasis (Fin d) ℂ E) (c : OrthonormalBasis (Fin r) ℂ F)
    (X : Fin n → E →ₗ[ℂ] F)
    (hcol : (∑ i, (LinearMap.toMatrix b.toBasis c.toBasis (X i))ᴴ *
      LinearMap.toMatrix b.toBasis c.toBasis (X i)) = 1)
    (hrow : ((2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
      ∑ i, LinearMap.toMatrix b.toBasis c.toBasis (X i) *
        (LinearMap.toMatrix b.toBasis c.toBasis (X i))ᴴ).PosSemidef) :
    (∑ i, (LinearMap.adjoint (X i)).comp (X i)) = LinearMap.id ∧
      ∀ v : F, 0 ≤ inner ℂ v (((2/3 : ℂ) • (LinearMap.id : F →ₗ[ℂ] F) -
        ∑ i, (X i).comp (LinearMap.adjoint (X i))) v) := by
  constructor
  · apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
    simpa only [map_sum, LinearMap.toMatrix_comp b.toBasis c.toBasis b.toBasis,
      LinearMap.toMatrix_adjoint, LinearMap.toMatrix_id] using hcol
  · intro v
    rw [inner_toMatrix c]
    have he : LinearMap.toMatrix c.toBasis c.toBasis
        ((2/3 : ℂ) • (LinearMap.id : F →ₗ[ℂ] F) - ∑ i, (X i).comp (LinearMap.adjoint (X i))) =
        (2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
          ∑ i, LinearMap.toMatrix b.toBasis c.toBasis (X i) *
            (LinearMap.toMatrix b.toBasis c.toBasis (X i))ᴴ := by
      simp only [map_sub, map_smul, map_sum, LinearMap.toMatrix_id,
        LinearMap.toMatrix_comp c.toBasis b.toBasis c.toBasis, LinearMap.toMatrix_adjoint]
    rw [he]
    exact hrow.dotProduct_mulVec_nonneg _

end Kaplansky

end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_RealModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Real models of complex bundles and smooth finite line sums. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky

section
variable {B F J : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] (C : VectorBundleCore ℂ B F J)

/-- Restrict scalars while retaining the original complex transition maps
as functions, and hence the original bundle atlas and topology. -/
def complexCoreReal : VectorBundleCore ℝ B F J where
  baseSet := C.baseSet
  isOpen_baseSet := C.isOpen_baseSet
  indexAt := C.indexAt
  mem_baseSet_at := C.mem_baseSet_at
  coordChange i j x := (C.coordChange i j x).restrictScalars ℝ
  coordChange_self := C.coordChange_self
  continuousOn_coordChange i j :=
    (ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ).continuous.comp_continuousOn
      (C.continuousOn_coordChange i j)
  coordChange_comp := C.coordChange_comp

instance complexCoreFiberRealModule (x : B) : Module ℝ (C.Fiber x) := inferInstanceAs (Module ℝ F)

instance complexCoreFiberRealVectorBundle : VectorBundle ℝ F C.Fiber :=
  inferInstanceAs (VectorBundle ℝ F (complexCoreReal C).Fiber)

end

end Kaplansky

end

open Bundle Topology
open scoped Manifold ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Replacement
attribute [-instance] _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Quantitative bundle rank margins and repeated-line replacement maps. -/

namespace Kaplansky

theorem large_incidence (m s d η : ℝ) (hm : 0 ≤ m) (hd : 0 < d)
    (hms : m < s) (hsd : s ≤ d) (hη : η < (20/3)*m*d) :
    2*s < (15/4)*d ∧ η < (8*s-2*s)*(15*d/4-2*s)-s*(d-s) := by
  have hs : 0 < s := lt_of_le_of_lt hm hms
  have h1 := mul_le_mul_of_nonneg_right hsd hs.le
  have h2 := mul_lt_mul_of_pos_right hms hd
  have h3 := mul_nonneg hm hd.le
  constructor <;> nlinarith

end Kaplansky

namespace Kaplansky.Incidence

theorem fresh_incidence_dimension (m d r N s : ℕ) (hd : 0<d)
    (hr : 4*r=15*d) (hN : 3*N<40*m*d) (hms : m < s) (hsd : s≤d) :
    2*s ≤ r ∧ N+2*s*(d-s)+2*(2*s)*(r-2*s)<2*8*s*(r-2*s) := by
  have hrr : (r : ℝ)=15*(d : ℝ)/4 := by
    have hh : (4 : ℝ)*r=15*d := by exact_mod_cast hr
    linarith
  have hn : (N : ℝ)/2 < (20/3)*(m : ℝ)*d := by
    have hh : (3 : ℝ)*N<40*(m : ℝ)*d := by exact_mod_cast hN
    linarith
  obtain ⟨hep,hgap⟩ := Kaplansky.large_incidence (m : ℝ) (s : ℝ) (d : ℝ) ((N : ℝ)/2)
    (by positivity) (by exact_mod_cast hd) (by exact_mod_cast hms) (by exact_mod_cast hsd) hn
  have htr : 2*s ≤ r := by
    have hh : (2 : ℝ)*s<(r : ℝ) := by rw [hrr]; linarith
    exact le_of_lt (by exact_mod_cast hh)
  refine ⟨htr,?_⟩
  apply (Nat.cast_lt (α := ℝ)).mp
  push_cast [Nat.cast_sub hsd,Nat.cast_sub htr]
  rw [hrr]
  nlinarith

end Kaplansky.Incidence

section
open scoped BigOperators
namespace Kaplansky
variable {d r n : ℕ} {L : Type*} [AddCommGroup L] [Module ℂ L]

/-- A scalar matrix tensored with the identity of a line fiber. This formula
uses only scalar multiplication, not a choice of a vector in that line. -/
def scalarTensor (T : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ)) :
    (Fin d → L) →ₗ[ℂ] (Fin r → L) where
  toFun v a := ∑ j, (T (Pi.single j 1) a) • v j
  map_add' v w := by funext a; simp [smul_add,Finset.sum_add_distrib]
  map_smul' c v := by
    funext a
    simp [Finset.smul_sum,smul_smul,mul_comm]

end Kaplansky

end

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky
variable {B : Type*} [TopologicalSpace B] {k : ℕ}
  {J : Fin k → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

abbrev RepeatedLineModel (D : Fin k → ℕ) := EuclideanSpace ℂ (Σ s, Fin (D s))

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
variable {B : Type*} [TopologicalSpace B] {k : ℕ}
  {J : Fin k → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

local instance instFiniteDimensionalComplexFiber_solutions (s : Fin k) (x : B) : FiniteDimensional ℂ ((C s).Fiber x) :=
  inferInstanceAs (FiniteDimensional ℂ ℂ)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_SmoothLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Smooth projective lines, product lines, finite sums, and restrictions. -/

section
open Matrix Topology
open scoped Manifold ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

-- Use the topology of the chosen matrix norm for both manifold models.
local instance instTopologicalSpaceMatrixFinHAddNatOfNatComplex_solutions : TopologicalSpace (Matrix (Fin (1+k)) (Fin (1+k)) ℂ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin (1+k)) (Fin (1+k)) ℂ)).toUniformSpace.toTopologicalSpace

end Kaplansky.ComplexGrassmann

end

section
open Bundle Topology NormedSpace
open scoped Manifold ContDiff Matrix.Norms.Elementwise
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

def matrixColumnLinear {d : ℕ} (i : Fin d) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin d) where
  toFun A := WithLp.toLp 2 (fun j => A j i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem contDiffAt_normalize {d : ℕ} {v : EuclideanSpace ℂ (Fin d)} (hv : v≠0) :
    ContDiffAt ℝ ∞ (normalize (V := EuclideanSpace ℂ (Fin d))) v := by
  exact ((contDiffAt_id.norm ℂ hv).inv (norm_ne_zero_iff.mpr hv)).smul contDiffAt_id

end Kaplansky.ComplexGrassmann

end

open Bundle Topology

end

end OAI
end


