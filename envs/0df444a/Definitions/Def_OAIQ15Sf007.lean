-- Prove2me | Definitions.Def_OAIQ15Sf007
-- name    : OAIQ15Sf007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:25:13.343113+00:00
-- url     : https://prove2.me/theorems/fd4c89b9-320c-4b91-bdfe-41d5d46752d8
-- title:
--   Definitions bundle OAIQ15Sf007 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 215 declarations of OpenAI's Lean: 68 definitions, 3 inductive types or structures, 9 instances and 135 theorems. The definitions and types are `OAI.Kaplansky.BundleTestBase`, `OAI.Kaplansky.BundleWordValue.identity`, `OAI.Kaplansky.ComplexGrassmann.ProjectivePuncture`, `OAI.Kaplansky.ComplexGrassmann.PunctureHyperplane`, `OAI.Kaplansky.ComplexGrassmann.graphDenominatorConstant`, `OAI.Kaplansky.ComplexGrassmann.graphDenominatorLinear`, `OAI.Kaplansky.ComplexGrassmann.graphLineFrame`, `OAI.Kaplansky.ComplexGrassmann.graphVerticalFunctional`, `OAI.Kaplansky.ComplexGrassmann.hyperplaneEmbed`, `OAI.Kaplansky.ComplexGrassmann.hyperplaneEmbedLinear`, `OAI.Kaplansky.ComplexGrassmann.hyperplaneEmbedPoint`, `OAI.Kaplansky.ComplexGrassmann.hyperplaneProject`, `OAI.Kaplansky.ComplexGrassmann.hyperplaneProjectLinear`, `OAI.Kaplansky.ComplexGrassmann.productGraphDenominatorConstant`, `OAI.Kaplansky.ComplexGrassmann.projectiveCoordinatePuncture`, `OAI.Kaplansky.ComplexGrassmann.projectiveHyperplaneHomeomorph`, `OAI.Kaplansky.ComplexGrassmann.projectiveLinearImage`, `OAI.Kaplansky.ComplexGrassmann.projectivePointPunctureLowerHomotopyEquiv`, `OAI.Kaplansky.ComplexGrassmann.projectivePunctureLowerHomotopyEquiv`, `OAI.Kaplansky.ComplexGrassmann.punctureCollapse`, `OAI.Kaplansky.ComplexGrassmann.punctureCollapseLinear`, `OAI.Kaplansky.ComplexGrassmann.punctureDeformation`, `OAI.Kaplansky.ComplexGrassmann.punctureHyperplaneHomotopyEquiv`, `OAI.Kaplansky.ComplexGrassmann.punctureHyperplaneInclusion`, `OAI.Kaplansky.ComplexGrassmann.punctureHyperplaneRetraction`, `OAI.Kaplansky.ComplexGrassmann.slopeEvaluationOneEquiv`, `OAI.Kaplansky.ComplexGrassmann.standardLineGraphFrame`, `OAI.Kaplansky.ComplexGrassmann.verticalAmbientEquiv`, `OAI.Kaplansky.ContinuousIndependentStageFrame`, `OAI.Kaplansky.ContinuousIndependentStageFrame.normalize`, `OAI.Kaplansky.ContinuousOrthonormalStageFrame`, `OAI.Kaplansky.ContinuousStageMap`, `OAI.Kaplansky.ContinuousStageMap.comp`, `OAI.Kaplansky.ContinuousStageMap.inj`, `OAI.Kaplansky.ContinuousStageMap.proj`, `OAI.Kaplansky.ContinuousStageMap.smul`, `OAI.Kaplansky.ContinuousStageMap.sum`, `OAI.Kaplansky.CuntzDimensionState.baseValue`, `OAI.Kaplansky.CuntzDimensionState.commutativeValueLinearMap`, `OAI.Kaplansky.CuntzDimensionState.complexValueLinearMap` and 31 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: `BundleTests_Assembly`, `BundleTests_Base`, `BundleTests_Multiplicities`, `BundleTests_Normalized`, `BundleTests_Retained`, `BundleTests_Sequence`, `BundleTests_Smooth`, `ComplexBundle_Avoidance`, `ComplexBundle_CoordinatesMetric`, `ComplexBundle_DirectSum`, `ComplexBundle_Hyperplane`, `ComplexBundle_LineStage`, `ComplexBundle_Orthonormal`, `ComplexBundle_ProjectionBundle`, `ComplexBundle_Replacement`, `ComplexBundle_SmoothLine`, `ComplexBundle_StageMaps`, `Cuntz_Commutative`, `Cuntz_Content`, `Cuntz_Distribution`, `Cuntz_Measure`, `Cuntz_Quasitrace`, `Cuntz_Regularization`, `Cuntz_Spectral`, `Cuntz_SquareCutoff`, `IntegralHomology_GraphCover`, `IntegralHomology_ProjectiveClass`, `IntegralHomology_ProjectiveLocal`, `IntegralHomology_ProjectivePuncture`, `Kaplansky_BundlePolynomials`, `Kaplansky_BundleWords`, `Kaplansky_Products`, `Kaplansky_Shift`, `Kaplansky_TestAlgebra`, `Kaplansky_Words`, `MatrixScaling_Expansion`, `OrderedStates_Semigroup`.
--
--   **Imports.** It imports the published bundle `Def_KaplanskyStableFiniteness`; the bundles `OAIQ15Sf000`, `OAIQ15Sf001`, `OAIQ15Sf002` and `OAIQ15Sf003` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ15Sf010`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf000
import Definitions.Def_OAIQ15Sf001
import Definitions.Def_OAIQ15Sf002
import Definitions.Def_OAIQ15Sf003

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Avoidance
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Avoidance of lower-dimensional incidence images in local manifold charts. -/

section
open scoped ContDiff Topology MeasureTheory
open Set MeasureTheory MeasureTheory.Measure Module
namespace Kaplansky.SmoothKernel.SurjectiveFamily
variable {X V W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
variable (A : SurjectiveFamily X V W)

attribute [local instance] OAI.Kaplansky.SmoothKernel.SurjectiveFamily.instCompleteSpace_2
theorem fromModel_contDiffAt (hA : ContDiff ℝ ∞ A.map) (i x : X) (hx : x ∈ A.baseSet i) :
    ContDiffAt ℝ ∞ (A.fromModel i) x := by
  have hc : ContDiff ℂ ∞ (fun P : V →L[ℂ] V =>
      P.comp (((LinearMap.ker (A.map i).toLinearMap).subtypeL).comp
        (A.modelEquiv i).toContinuousLinearMap)) := contDiff_id.clm_comp contDiff_const
  exact (hc.restrict_scalars ℝ).contDiffAt.comp x
    (((kernelProjection_smooth (A.rightInverse i) (A.map x) hx).restrict_scalars ℝ).comp x hA.contDiffAt)

def kernelParameterization (i : X) (p : X × KernelModel V W) : V := A.fromModel i p.1 p.2

theorem kernelParameterization_smooth (hA : ContDiff ℝ ∞ A.map) (i : X) :
    ContDiffOn ℝ ∞ (A.kernelParameterization i) (A.baseSet i ×ˢ univ) := by
  intro p hp
  have hc := (ContinuousLinearMap.restrictScalarsL ℂ (KernelModel V W) V ℝ ℝ).contDiff.contDiffAt.comp p.1
    (A.fromModel_contDiffAt hA i p.1 hp.1)
  exact ((hc.comp p contDiffAt_fst).clm_apply contDiffAt_snd).contDiffWithinAt

variable [FiniteDimensional ℝ X]

/-- The image of the ACTUAL kernel incidence subset is null. The proof uses a
countable cover of the constructed kernel charts, not a null-image premise. -/
theorem kernel_incidence_image_null [MeasurableSpace V] [BorelSpace V]
    (hA : ContDiff ℝ ∞ A.map)
    (hd : finrank ℝ (X × KernelModel V W)<finrank ℝ V) :
    μH[finrank ℝ V] {v : V | ∃ x, A.map x v=0}=0 := by
  obtain ⟨c,hc,hcov⟩ := A.exists_countable_baseSet_cover
  let := hc.toEncodable
  have hi (i : c) : μH[finrank ℝ V]
      (A.kernelParameterization i.val '' (A.baseSet i.val ×ˢ univ))=0 :=
    Kaplansky.Incidence.smoothOn_open_image_null ((A.baseSet_open i.val).prod isOpen_univ)
      ((A.kernelParameterization_smooth hA i.val).of_le (by simp)) hd
  apply measure_mono_null (t := ⋃ i : c, A.kernelParameterization i.val '' (A.baseSet i.val ×ˢ univ))
    ?_ (measure_iUnion_null hi)
  rintro v ⟨x,hx⟩
  obtain ⟨i,hi,hxi⟩ := hcov x
  apply mem_iUnion.mpr
  refine ⟨⟨i,hi⟩,(x,A.toModel i v),⟨hxi,mem_univ _⟩,?_⟩
  exact A.fromModel_toModel i x hxi v hx

end Kaplansky.SmoothKernel.SurjectiveFamily

end

open scoped ContDiff MeasureTheory
open Module MeasureTheory MeasureTheory.Measure

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_DirectSum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite direct sums of line bundles, metrics, inclusions, and projections. -/

section
open Bundle Topology

open Bundle Topology
open scoped BigOperators InnerProductSpace
namespace Kaplansky
variable {B S : Type*} [TopologicalSpace B] [Fintype S]
  {J : S → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

theorem finiteLineSumTransition_inner (hC : LineCoreIsUnitary C)
    (a b : ∀ s, J s) (x : B) (ha : x ∈ lineSumBaseSet C a)
    (hb : x ∈ lineSumBaseSet C b) (v w : EuclideanSpace ℂ S) :
    inner ℂ (lineSumTransition C a b x v) (lineSumTransition C a b x w) = inner ℂ v w := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro s _
  exact hC s (a s) (b s) x (ha s) (hb s) (v s) (w s)

theorem finiteLineSum_chart_inner (hC : LineCoreIsUnitary C)
    (a : ∀ s, J s) (x : B) (ha : x ∈ lineSumBaseSet C a)
    (v w : (finiteLineSumCore C).Fiber x) :
    inner ℂ (((finiteLineSumCore C).localTriv a) ⟨x,v⟩).2
      (((finiteLineSumCore C).localTriv a) ⟨x,w⟩).2 = inner ℂ v w :=
  finiteLineSumTransition_inner C hC _ a x ((finiteLineSumCore C).mem_baseSet_at x) ha v w

/-- The fiberwise Hilbert metrics are continuous on the constructed bundle,
proved in local charts. This is the continuous Hermitian metric condition
for arbitrary continuous local sections. -/
theorem finiteLineSum_inner_continuousOn (hC : LineCoreIsUnitary C)
    (A : Set B) (v w : ∀ x, (finiteLineSumCore C).Fiber x)
    (hv : ContinuousOn (fun x => TotalSpace.mk' (EuclideanSpace ℂ S) x (v x)) A)
    (hw : ContinuousOn (fun x => TotalSpace.mk' (EuclideanSpace ℂ S) x (w x)) A) :
    ContinuousOn (fun x => inner ℂ (v x) (w x)) A := by
  intro x hx
  let a := (finiteLineSumCore C).indexAt x
  have hax : x ∈ lineSumBaseSet C a := (finiteLineSumCore C).mem_baseSet_at x
  have hcv := ((FiberBundle.continuousWithinAt_totalSpace (EuclideanSpace ℂ S) _).mp (hv x hx)).2
  have hcw := ((FiberBundle.continuousWithinAt_totalSpace (EuclideanSpace ℂ S) _).mp (hw x hx)).2
  apply (hcv.inner hcw).congr_of_eventuallyEq
  · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        ((isOpen_lineSumBaseSet C a).mem_nhds hax)] with y hy
    exact (finiteLineSum_chart_inner C hC a y hy (v y) (w y)).symm
  · exact (finiteLineSum_chart_inner C hC a x hax (v x) (w x)).symm

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
variable {B S T : Type*} [TopologicalSpace B] [Fintype S] [Fintype T]
  {J : S⊕T → Type*} (L : ∀ u, VectorBundleCore ℂ B ℂ (J u))

theorem lineSumInl_injective (x : B) : Function.Injective (lineSumInl L x) := by
  intro v w h
  apply (EuclideanSpace.equiv S ℂ).injective
  funext s
  exact congrArg (fun u : EuclideanSpace ℂ (S⊕T) => u (Sum.inl s)) h

theorem lineSumInr_injective (x : B) : Function.Injective (lineSumInr L x) := by
  intro v w h
  apply (EuclideanSpace.equiv T ℂ).injective
  funext t
  exact congrArg (fun u : EuclideanSpace ℂ (S⊕T) => u (Sum.inr t)) h

end Kaplansky

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
variable {B S T : Type*} [TopologicalSpace B] [Fintype S] [Fintype T]
  {J : S → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s)) (e : T ≃ S)

def lineSumReindex (x : B) : (finiteLineSumCore (fun t => C (e t))).Fiber x ≃ₗ[ℂ]
    (finiteLineSumCore C).Fiber x where
  toFun v := WithLp.toLp 2 (fun s => (show EuclideanSpace ℂ T from v) (e.symm s))
  invFun v := WithLp.toLp 2 (fun t => (show EuclideanSpace ℂ S from v) (e t))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    apply (EuclideanSpace.equiv T ℂ).injective
    funext t
    exact congrArg (fun t => (show EuclideanSpace ℂ T from v) t) (e.symm_apply_apply t)
  right_inv v := by
    apply (EuclideanSpace.equiv S ℂ).injective
    funext s
    exact congrArg (fun s => (show EuclideanSpace ℂ S from v) s) (e.apply_symm_apply s)

def lineSumReindexTotalHomeomorph :
    TotalSpace (EuclideanSpace ℂ T) (finiteLineSumCore (fun t => C (e t))).Fiber ≃ₜ
      TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore C).Fiber where
  toFun z := ⟨z.proj,lineSumReindex C e z.proj z.2⟩
  invFun z := ⟨z.proj,(lineSumReindex C e z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp
  continuous_toFun := by
    apply (continuous_finiteLineSum_iff _ _).mpr
    refine ⟨FiberBundle.continuous_proj _ _,?_⟩
    intro s
    obtain ⟨t,rfl⟩ := e.surjective s
    change Continuous (fun z : TotalSpace (EuclideanSpace ℂ T) (finiteLineSumCore (fun t => C (e t))).Fiber =>
      TotalSpace.mk' ℂ (E := (C (e t)).Fiber) z.proj ((show EuclideanSpace ℂ T from z.2) (e.symm (e t))))
    simp only [Equiv.symm_apply_apply]
    exact continuous_finiteLineSumComponent (fun t => C (e t)) t
  continuous_invFun := by
    apply (continuous_finiteLineSum_iff _ _).mpr
    refine ⟨FiberBundle.continuous_proj _ _,?_⟩
    intro t
    exact continuous_finiteLineSumComponent C (e t)

theorem lineSumReindex_inner (x : B)
    (v w : (finiteLineSumCore (fun t => C (e t))).Fiber x) :
    inner ℂ (lineSumReindex C e x v) (lineSumReindex C e x w) = inner ℂ v w := by
  change (∑ s : S, inner ℂ ((show EuclideanSpace ℂ T from v) (e.symm s))
    ((show EuclideanSpace ℂ T from w) (e.symm s))) =
    ∑ t : T, inner ℂ ((show EuclideanSpace ℂ T from v) t) ((show EuclideanSpace ℂ T from w) t)
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

end Kaplansky

end

open Bundle Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.MatrixScaling_Expansion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic and finite-block expansion inequalities. -/

noncomputable section
open scoped BigOperators
open LinearMap
namespace Kaplansky
variable {n : ℕ} {E F G H : Type*}
variable [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
variable [AddCommGroup G] [Module ℂ G] [AddCommGroup H] [Module ℂ H]

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

variable [FiniteDimensional ℂ G] [FiniteDimensional ℂ H]

theorem expandingThrough_prod (m : ℕ) (T : Fin n → E →ₗ[ℂ] G) (U : Fin n → F →ₗ[ℂ] H)
    (hT : ExpandingThrough m T) (hU : ExpandingThrough m U) :
    ExpandingThrough m (fun i => (T i).prodMap (U i)) := by
  intro S hS
  let W : Submodule ℂ (G × H) := ⨆ i, S.map ((T i).prodMap (U i))
  let L := S.comap (LinearMap.inl ℂ E F)
  let R := S.map (LinearMap.snd ℂ E F)
  have hdim := prod_submodule_finrank S
  have hL := hT L (by dsimp [L]; omega)
  have hR := hU R (by dsimp [R]; omega)
  have hright : W.map (LinearMap.snd ℂ G H) =
      ⨆ i, R.map (U i) := by
    dsimp [W,R]
    rw [Submodule.map_iSup]
    apply iSup_congr
    intro i
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
  have hleft : (⨆ i, L.map (T i) : Submodule ℂ G) ≤ W.comap (LinearMap.inl ℂ G H) := by
    apply iSup_le
    intro i
    rintro _ ⟨v,hv,rfl⟩
    change (T i v,0) ∈ W
    apply (le_iSup (fun j => S.map ((T j).prodMap (U j))) i)
    refine ⟨(v,0),hv,?_⟩
    simp
  have hw := prod_submodule_finrank W
  have hlrank := Submodule.finrank_mono hleft
  rw [hright] at hw
  change 2 * Module.finrank ℂ S ≤ Module.finrank ℂ W
  dsimp [L,R] at hL hR hlrank hw
  omega

end Kaplansky

end

noncomputable section
namespace Kaplansky
variable {n : ℕ}

theorem expandingThrough_equiv {E F D R : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup D] [Module ℂ D] [AddCommGroup R] [Module ℂ R]
    (m : ℕ) (T : Fin n → E →ₗ[ℂ] F) (e : E ≃ₗ[ℂ] D) (f : F ≃ₗ[ℂ] R)
    (hT : ExpandingThrough m T) :
    ExpandingThrough m (fun i => f.toLinearMap.comp ((T i).comp e.symm.toLinearMap)) := by
  intro S hS
  have h := hT (S.map e.symm.toLinearMap) (by simpa only [e.symm.finrank_map_eq] using hS)
  rw [e.symm.finrank_map_eq] at h
  have he : (⨆ i, S.map (f.toLinearMap.comp ((T i).comp e.symm.toLinearMap)) : Submodule ℂ R) =
      (⨆ i, (S.map e.symm.toLinearMap).map (T i) : Submodule ℂ F).map f.toLinearMap := by
    rw [Submodule.map_iSup]
    apply iSup_congr
    intro i
    rw [Submodule.map_comp, Submodule.map_comp]
  rw [he, f.finrank_map_eq]
  exact h

theorem expandingThrough_blocks (k m : ℕ)
    (E : Fin k → Type*) (F : Fin k → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)] [∀ j, FiniteDimensional ℂ (E j)]
    [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] [∀ j, FiniteDimensional ℂ (F j)]
    (T : ∀ j, Fin n → E j →ₗ[ℂ] F j) (hT : ∀ j, ExpandingThrough m (T j)) :
    ExpandingThrough m (blockDiagonal T) := by
  induction k with
  | zero =>
      intro S _
      have hz : Module.finrank ℂ S = 0 := Module.finrank_zero_of_subsingleton
      simp [hz]
  | succ k ih =>
      have ht := ih (fun j => E j.succ) (fun j => F j.succ)
        (fun j => T j.succ) (fun j => hT j.succ)
      have hp := expandingThrough_prod m (T 0) (blockDiagonal (fun j : Fin k => T j.succ)) (hT 0) ht
      have he := expandingThrough_equiv m _ (piSuccLinearEquiv E).symm (piSuccLinearEquiv F).symm hp
      convert he using 1
      all_goals try with_reducible_and_instances rfl
      funext i
      apply LinearMap.ext
      intro v
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> rfl

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Replacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Quantitative bundle rank margins and repeated-line replacement maps. -/

section
open scoped BigOperators
namespace Kaplansky
variable {d r n : ℕ} {L : Type*} [AddCommGroup L] [Module ℂ L]

theorem scalarTensor_coordinates (T : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (e : L ≃ₗ[ℂ] ℂ) (v : Fin d → L) :
    lineCoordinates e r (scalarTensor T v)=T (lineCoordinates e d v) := by
  classical
  have hv : lineCoordinates e d v = ∑ j, e (v j) • Pi.single j 1 := by
    funext j
    simp [lineCoordinates,Pi.single_apply]
  rw [hv,map_sum]
  funext a
  simp [scalarTensor,lineCoordinates,map_sum,map_smul,Finset.sum_apply,mul_comm]

theorem scalarTensor_eq_conjugate (T : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (e : L ≃ₗ[ℂ] ℂ) :
    scalarTensor T=(lineCoordinates e r).symm.toLinearMap.comp
      (T.comp (lineCoordinates e d).toLinearMap) := by
  apply LinearMap.ext
  intro v
  apply (lineCoordinates e r).injective
  simpa using scalarTensor_coordinates T e v

/-- Tensoring an expanding scalar family with a line preserves expansion for
all subspaces, and the tensor maps themselves are independent of the frame. -/
theorem scalarTensor_expanding (m : ℕ) (T : Fin n → (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (e : L ≃ₗ[ℂ] ℂ) (hT : ExpandingThrough m T) :
    ExpandingThrough m (fun i => scalarTensor (L := L) (T i)) := by
  have h := expandingThrough_equiv m T (lineCoordinates e d).symm (lineCoordinates e r).symm hT
  simpa only [LinearEquiv.symm_symm,← scalarTensor_eq_conjugate] using h

/-- Rank one is enough; the line coordinate equivalence is constructed. -/
theorem scalarTensor_expanding_rank_one [FiniteDimensional ℂ L]
    (hL : Module.finrank ℂ L=1) (m : ℕ)
    (T : Fin n → (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ)) (hT : ExpandingThrough m T) :
    ExpandingThrough m (fun i => scalarTensor (L := L) (T i)) := by
  obtain ⟨e⟩ := (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
    (R := ℂ) (M := L) (M' := ℂ)).mpr (by simpa using hL)
  exact scalarTensor_expanding m T e hT

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Multiplicities
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplicity sequences and their arithmetic identities. -/


namespace Kaplansky
open scoped BigOperators

theorem testMultiplicity_lower_bound {m R j : ℕ} (hj : j<R) (i : Fin (j+1)) :
    256*m ≤ testMultiplicity m R j i := by
  rw [← testMultiplicity_quarter hj i]
  have h : 64*m ≤ testMultiplicity m R (j+1) i.castSucc := by
    unfold testMultiplicity
    split
    · have hp : 1≤4^(R-(j+1)) := Nat.one_le_pow _ _ (by omega)
      nlinarith
    · have hp : 1≤4^(R+2*(i.castSucc).val-(j+1)-2) := Nat.one_le_pow _ _ (by omega)
      nlinarith
  omega

end Kaplansky

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_ProjectionBundle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The projection line bundle and its dual. -/

section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Topology Bundle
namespace Kaplansky
variable {d : ℕ}

theorem projectionLineTransition_star (i j : Fin d) (p : projectionSpace d 1) :
    star (projectionLineTransition i j p) = projectionLineTransition j i p :=
  inner_conj_symm _ _

theorem projectionLineTransition_unitary (i j : Fin d) (p : projectionSpace d 1)
    (hi : p ∈ projectionChartSet i) (hj : p ∈ projectionChartSet j) :
    star (projectionLineTransition i j p) * projectionLineTransition i j p = 1 := by
  rw [projectionLineTransition_star, projectionLineTransition_comp i j i p hj,
    projectionLineTransition_self i p hi]

/-- Identify each constructed fiber with the actual projected line in
Euclidean space. -/
def projectionLineFiberEquiv (p : projectionSpace d 1) :
    (projectionLineCore d).Fiber p ≃ₗ[ℂ] projectionLine p where
  toFun z := ⟨(show ℂ from z) • unitProjectionColumn p ((projectionLineCore d).indexAt p),
    (projectionLine p).smul_mem (show ℂ from z) (unitProjectionColumn_mem p _)⟩
  invFun v := inner ℂ (unitProjectionColumn p ((projectionLineCore d).indexAt p)) v.val
  left_inv z := by
    change ℂ at z
    change inner ℂ (unitProjectionColumn p _) ((show ℂ from z) • unitProjectionColumn p _) = (show ℂ from z)
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K,
      unitProjectionColumn_norm p _ ((projectionLineCore d).mem_baseSet_at p)]
    simp
  right_inv v := Subtype.ext (unitProjectionColumn_reconstruct p _
    ((projectionLineCore d).mem_baseSet_at p) v.val v.property)
  map_add' z w := by apply Subtype.ext; exact add_smul _ _ _
  map_smul' z w := by apply Subtype.ext; exact mul_smul _ _ _

theorem projectionLine_realization_chart (p : projectionSpace d 1)
    (z : (projectionLineCore d).Fiber p) (i : Fin d) (hi : p ∈ projectionChartSet i) :
    (projectionLineFiberEquiv p z).val =
      ((projectionLineCore d).localTriv i ⟨p,z⟩).2 • unitProjectionColumn p i := by
  change (show ℂ from z) • unitProjectionColumn p ((projectionLineCore d).indexAt p) =
    (projectionLineTransition ((projectionLineCore d).indexAt p) i p * (show ℂ from z)) • unitProjectionColumn p i
  rw [mul_comm, mul_smul, projectionLineTransition,
    unitProjectionColumn_reconstruct p i hi _ (unitProjectionColumn_mem p _)]

end Kaplansky

end

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Topology Bundle
namespace Kaplansky
variable {d : ℕ}

/-- The constructed dual fiber is the full algebraic dual of the actual line. -/
def projectionDualLineFiberEquiv (p : projectionSpace d 1) :
    (projectionDualLineCore d).Fiber p ≃ₗ[ℂ] (projectionLine p →ₗ[ℂ] ℂ) where
  toFun z := (show ℂ from z) • (projectionLineFiberEquiv p).symm.toLinearMap
  invFun f := f (projectionLineFiberEquiv p (show (projectionLineCore d).Fiber p from (1 : ℂ)))
  left_inv z := by
    change ℂ at z
    let e : ℂ ≃ₗ[ℂ] projectionLine p := projectionLineFiberEquiv p
    change z * e.symm (e 1) = z
    rw [LinearEquiv.symm_apply_apply, mul_one]
  right_inv f := by
    let e : ℂ ≃ₗ[ℂ] projectionLine p := projectionLineFiberEquiv p
    apply LinearMap.ext
    intro v
    change f (e 1) * e.symm v = f v
    have hv : v = e.symm v • e 1 := by
      rw [← map_smul]
      simp
    conv_rhs => rw [hv, map_smul]
    exact mul_comm _ _
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := mul_smul _ _ _

/-- Evaluation of the dual on the line is independent of the local chart. -/
theorem projectionDualLine_pairing_chart (p : projectionSpace d 1)
    (z : (projectionDualLineCore d).Fiber p) (w : (projectionLineCore d).Fiber p)
    (i : Fin d) (hi : p ∈ projectionChartSet i) :
    ((projectionDualLineCore d).localTriv i ⟨p,z⟩).2 *
      ((projectionLineCore d).localTriv i ⟨p,w⟩).2 = (show ℂ from z) * (show ℂ from w) := by
  let j := (projectionLineCore d).indexAt p
  change (star (projectionLineTransition j i p) * (show ℂ from z)) *
    (projectionLineTransition j i p * (show ℂ from w)) = _
  calc
    _ = (star (projectionLineTransition j i p) * projectionLineTransition j i p) *
      ((show ℂ from z) * (show ℂ from w)) := by ring
    _ = _ := by rw [projectionLineTransition_unitary j i p ((projectionLineCore d).mem_baseSet_at p) hi, one_mul]

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Base
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact bundle-test base, prefix dimensions, and retained multiplicities. -/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky

abbrev BundleTestBase (m R : ℕ) := ∀ i : Fin R,
  projectionSpace (testProjectiveDimension m R i + 1) 1

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_SmoothLine
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Smooth projective lines, product lines, finite sums, and restrictions. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky.ComplexGrassmann

section
variable {ι : Type*} [Fintype ι] (K : ι → ℕ)

omit [Fintype ι] in
theorem productLineCore_unitary (i : Option ι)
    (a b : productLineChartIndex K i) (P : ProjectiveProduct K)
    (ha : P ∈ (productLineCore K i).baseSet a)
    (hb : P ∈ (productLineCore K i).baseSet b) (z w : ℂ) :
    inner ℂ ((productLineCore K i).coordChange a b P z)
      ((productLineCore K i).coordChange a b P w) = inner ℂ z w := by
  cases i with
  | none => rfl
  | some i =>
    apply complex_unit_mul_inner
    simpa only [star_star,mul_comm,ContinuousMap.coe_mk] using
      projectionLineTransition_unitary a b (projectiveProjectionMap (K i) (P i)) ha hb

end

variable {ι S : Type*} [Fintype ι] [Fintype S] (K : ι → ℕ) (label : S → Option ι)

omit [Fintype ι] in
theorem smoothLineSum_inner_continuousOn (A : Set (ProjectiveProduct K))
    (v w : ∀ P, SmoothLineSumBundle K label P)
    (hv : ContinuousOn (fun P => TotalSpace.mk' (EuclideanSpace ℂ S) P (v P)) A)
    (hw : ContinuousOn (fun P => TotalSpace.mk' (EuclideanSpace ℂ S) P (w P)) A) :
    ContinuousOn (fun P => inner ℂ (v P) (w P)) A :=
  finiteLineSum_inner_continuousOn _ (fun s => productLineCore_unitary K (label s)) A v w hv hw

end Kaplansky.ComplexGrassmann

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Smooth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Smooth bases and test bundles with replacement maps. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann

/-- The fresh block on Y_{j+1}, consisting of exactly a_{j+1,j+1}
occurrences of the hyperplane line of its last factor. -/
def smoothFreshCore (m R j : ℕ) (hj : j<R) :=
  smoothLineSumCore (stageProjectiveDimensions m R (j+1) hj)
    (fun _ : Fin (testMultiplicity m R (j+1) (Fin.last (j+1))) => some (Fin.last j))

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_CoordinatesMetric
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-coordinate smooth bundles and their metrics. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {S ι : Type*} [Fintype S] [Fintype ι]
  (K : ι → ℕ) (label : S → Option ι) (d : ℕ) (hd : Fintype.card S=d)

omit [Fintype ι] in
/-- The actual sum metric is continuous in the finite-coordinate presentation. -/
theorem finiteCoordinate_continuousHermitianMetric :
    ContinuousHermitianMetric (d := d) (E := FiniteCoordinateBundle K label d hd) := by
  intro A v w hv hw
  let H := finiteCoordinateTotalHomeomorph K label d hd
  have hv' := H.symm.continuous.comp_continuousOn hv
  have hw' := H.symm.continuous.comp_continuousOn hw
  exact smoothLineSum_inner_continuousOn K label A
    (fun P => (finiteCoordinateEquiv d hd).symm (v P))
    (fun P => (finiteCoordinateEquiv d hd).symm (w P)) hv' hw'

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Assembly
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Fresh bundle maps and assembly of the test-bundle step. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

/-- E_{j+1} presented as the direct sum of its replacement and fresh blocks. -/
def smoothNextCore (m R j : ℕ) (hj : j<R) :=
  smoothLineSumCore (stageProjectiveDimensions m R (j+1) hj) (testNextLabel m R j)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Normalized
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Normalized test maps, slot regrouping, and unitary coordinate changes. -/

section
open Bundle
namespace Kaplansky
open ComplexGrassmann

def testNextSlotEquiv (m R j : ℕ) : TestNextSlot m R j ≃ TestBundleSlot m R (j+1) where
  toFun := Sum.elim (fun s => ⟨s.1.castSucc,s.2⟩) (fun k => ⟨Fin.last (j+1),k⟩)
  invFun s := Fin.lastCases (fun k => Sum.inr k) (fun i k => Sum.inl ⟨i,k⟩) s.1 s.2
  left_inv s := by cases s <;> simp
  right_inv s := by
    obtain ⟨i,k⟩ := s
    induction i using Fin.lastCases <;> simp

theorem testNextLabel_eq (m R j : ℕ) (s : TestNextSlot m R j) :
    testNextLabel m R j s = testSummandLineIndex (Nat.le_refl (j+1)) (testNextSlotEquiv m R j s).1 := by
  cases s with
  | inl s =>
    obtain ⟨i,k⟩ := s
    simp only [testNextLabel,Sum.elim_inl,testNextSlotEquiv,Equiv.coe_fn_mk]
    simp [testSummandLineIndex]
  | inr k =>
    simp only [testNextLabel,Sum.elim_inr,testNextSlotEquiv,Equiv.coe_fn_mk]
    simp [testSummandLineIndex]
    rfl

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

/-- Reindexing an orthogonal line sum is unitary on fibers and continuous
in both directions on the actual total space. -/
def lineSumReindexUnitary {B S T : Type*} [TopologicalSpace B] [Fintype S] [Fintype T]
    {J : S → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s)) (e : T ≃ S) :
    UnitaryBundleEquiv (EuclideanSpace ℂ T) (EuclideanSpace ℂ S)
      (finiteLineSumCore (fun t => C (e t))).Fiber (finiteLineSumCore C).Fiber where
  fiber x :=
    { toLinearEquiv := lineSumReindex C e x
      norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (lineSumReindex_inner C e x) }
  continuous_forward := (lineSumReindexTotalHomeomorph C e).continuous
  continuous_reverse := (lineSumReindexTotalHomeomorph C e).symm.continuous

instance smoothNext_norm (m R j : ℕ) (hj : j<R)
    (x : ProjectiveProduct (stageProjectiveDimensions m R (j+1) hj)) :
    NormedAddCommGroup ((smoothNextCore m R j hj).Fiber x) := smoothLineSum_norm _ _ x

instance smoothNext_inner (m R j : ℕ) (hj : j<R)
    (x : ProjectiveProduct (stageProjectiveDimensions m R (j+1) hj)) :
    InnerProductSpace ℂ ((smoothNextCore m R j hj).Fiber x) := smoothLineSum_inner _ _ x

/-- The replacement-plus-fresh target is the standard next stage as an
ordinary Hermitian bundle, so normalization survives this regrouping. -/
def testNextStageUnitary (m R j : ℕ) (hj : j<R) :
    UnitaryBundleEquiv (EuclideanSpace ℂ (TestNextSlot m R j))
      (EuclideanSpace ℂ (TestBundleSlot m R (j+1)))
      (smoothNextCore m R j hj).Fiber
      (SmoothTestBundle m R (j+1) (j+1) hj (Nat.le_refl (j+1))) := by
  let K := stageProjectiveDimensions m R (j+1) hj
  let e := testNextSlotEquiv m R j
  let P : (TestNextSlot m R j → Option (Fin (j+1))) → Type := fun label =>
    UnitaryBundleEquiv (EuclideanSpace ℂ (TestNextSlot m R j))
      (EuclideanSpace ℂ (TestBundleSlot m R (j+1)))
      (SmoothLineSumBundle K label)
      (SmoothTestBundle m R (j+1) (j+1) hj (Nat.le_refl (j+1)))
  have he : testNextLabel m R j = fun u => testSummandLineIndex (Nat.le_refl (j+1)) (e u).1 :=
    funext (testNextLabel_eq m R j)
  have h : P (fun u => testSummandLineIndex (Nat.le_refl (j+1)) (e u).1) :=
    lineSumReindexUnitary
      (fun s : TestBundleSlot m R (j+1) => productLineCore K (testSummandLineIndex (Nat.le_refl (j+1)) s.1)) e
  exact Eq.mp (congrArg P he.symm) h

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Retained
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Retained bundle labels, positive multiplicities, regrouping, and complement rank. -/

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann

abbrev RetainedSlot (m R : ℕ) := Fin m × (Σ j : Fin (R+1), TestBundleSlot m R j.val)

end Kaplansky

end

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_LineStage
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Doubling stages of line bundles and their Hilbert direct sums. -/

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

attribute [instance] LineStage.finiteSlot

end Kaplansky

end

section
open Bundle Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Kaplansky
open ComplexGrassmann
namespace LineStage
variable {ι : Type*} {J : Type} [Fintype J] {K : ι → ℕ}

theorem continuous_sumProj (a : J → LineStage K) (j : J) :
    Continuous (fun z : TotalSpace (sum a).Model (sum a).Fiber =>
      TotalSpace.mk' (a j).Model z.proj (sumProj a j z.proj z.2)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  exact ⟨FiberBundle.continuous_proj _ _, fun s => continuous_finiteLineSumComponent (fun (t : Σ j : J, (a j).Slot) => productLineCore K ((a t.1).label t.2)) ⟨j,s⟩⟩

theorem continuous_sumInj (a : J → LineStage K) (j : J) :
    Continuous (fun z : TotalSpace (a j).Model (a j).Fiber =>
      TotalSpace.mk' (sum a).Model z.proj (sumInj a j z.proj z.2)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  refine ⟨FiberBundle.continuous_proj _ _, ?_⟩
  rintro ⟨k,s⟩
  by_cases h : k=j
  · subst k
    have hc : Continuous (fun z : TotalSpace (a j).Model (a j).Fiber =>
        TotalSpace.mk' ℂ (E := (productLineCore K ((a j).label s)).Fiber)
          z.proj ((show (a j).Model from z.2) s)) :=
      continuous_finiteLineSumComponent (fun t => productLineCore K ((a j).label t)) s
    apply hc.congr
    intro z
    apply congrArg (TotalSpace.mk' ℂ z.proj)
    let v : (a j).Model := z.2
    change @Eq ℂ (v s) (if h : j = j then v (h ▸ s) else 0)
    symm
    exact dite_eq_left rfl
  · have hc : Continuous (fun z : TotalSpace (a j).Model (a j).Fiber =>
        TotalSpace.mk' ℂ (E := (productLineCore K ((a k).label s)).Fiber) z.proj 0) :=
      (Trivialization.continuous_zeroSection ℂ (F := ℂ) (E := (productLineCore K ((a k).label s)).Fiber)).comp
        (FiberBundle.continuous_proj _ _)
    apply hc.congr
    intro z
    apply congrArg (TotalSpace.mk' ℂ z.proj)
    let v : (a j).Model := z.2
    change @Eq ℂ 0 (if h : k = j then v (h ▸ s) else 0)
    symm
    exact dite_eq_right h

end LineStage
end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} [Fintype ι] {K : ι → ℕ}

omit [Fintype ι] in
/-- The actual Hermitian metric is continuous when evaluated on two bundle
vectors over the same varying base, including vectors in the total space. -/
theorem continuous_lineStage_inner_over (a : LineStage K) {X : Type*} [TopologicalSpace X]
    (b : X → ProjectiveProduct K) (hb : Continuous b)
    (v w : ∀ x, a.Fiber (b x))
    (hv : Continuous (fun x => TotalSpace.mk' a.Model (b x) (v x)))
    (hw : Continuous (fun x => TotalSpace.mk' a.Model (b x) (w x))) :
    Continuous (fun x => inner ℂ (v x) (w x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let C := fun s => productLineCore K (a.label s)
  let chart := (smoothLineSumCore K a.label).indexAt (b x)
  have hcv := (FiberBundle.continuousAt_totalSpace a.Model _ (x₀ := x)).mp hv.continuousAt |>.2
  have hcw := (FiberBundle.continuousAt_totalSpace a.Model _ (x₀ := x)).mp hw.continuousAt |>.2
  apply (hcv.inner hcw).congr_of_eventuallyEq
  · have hn := (hb.continuousAt (x := x)) ((isOpen_lineSumBaseSet C chart).mem_nhds
      ((smoothLineSumCore K a.label).mem_baseSet_at (b x)))
    filter_upwards [hn] with z hz
    exact (finiteLineSum_chart_inner C (fun s => productLineCore_unitary K (a.label s))
      chart (b z) hz (v z) (w z)).symm

end Kaplansky

end

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Sequence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Prefix and full test steps, pullbacks, and the infinite test sequence. -/

section
open Bundle Topology
namespace Kaplansky

open ComplexGrassmann

theorem testSummandLineIndex_map {n b R : ℕ} (hn : n≤b) (hb : b≤R) (s : Fin (n+1)) :
    (testSummandLineIndex hn s).map (fun i => i.castLE hb) = testSummandLineIndex (hn.trans hb) s := by
  unfold testSummandLineIndex
  split <;> simp_all

theorem testSequenceStage_prefix {m R j : ℕ} (hj : j≤R) :
    testSequenceStage m R j = testLineStage m R j hj := by simp [testSequenceStage,hj]

theorem testSequenceStage_tail {m R j : ℕ} (hj : R≤j) :
    testSequenceStage m R j = (testLineStage m R R (Nat.le_refl R)).tail (j-R) := by
  by_cases h : j≤R
  · have he : j=R := Nat.le_antisymm h hj
    subst j
    simp [testSequenceStage,LineStage.tail]
  · simp [testSequenceStage,h]

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Hyperplane
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Hyperplane sections, dual evaluation, graph coordinates, and their zero. -/

section
open Bundle Topology
namespace Kaplansky

def firstCoordinateProjection (k : ℕ) : projectionSpace (1+k) 1 :=
  nonzeroVectorProjection (firstCoordinateVector k) (firstCoordinateVector_ne_zero k)

theorem firstCoordinateProjection_line (k : ℕ) :
    projectionLine (firstCoordinateProjection k)=Submodule.span ℂ {firstCoordinateVector k} :=
  nonzeroVectorProjection_line _ _

end Kaplansky

open Bundle Topology
open scoped InnerProductSpace
namespace Kaplansky
variable {d : ℕ}

/-- Evaluation at any nonzero vector is a genuine coordinate on the dual
of its one-dimensional line. -/
def hyperplaneEvaluationEquiv (p : projectionSpace d 1) (v : projectionLine p) (hv : v≠0) :
    (projectionDualLineCore d).Fiber p ≃ₗ[ℂ] ℂ := by
  let c : ℂ := (projectionLineFiberEquiv p).symm v
  have hc : c≠0 := by
    intro h
    apply hv
    exact (projectionLineFiberEquiv p).symm.injective (h.trans (map_zero _).symm)
  exact {
    toFun := fun z => (show ℂ from z)*c
    invFun := fun z => (show (projectionDualLineCore d).Fiber p from z/c)
    left_inv := fun z => mul_div_cancel_right₀ (show ℂ from z) hc
    right_inv := fun z => div_mul_cancel₀ z hc
    map_add' := fun z w => add_mul (show ℂ from z) (show ℂ from w) c
    map_smul' := fun t z => by change (t*(show ℂ from z))*c=t*((show ℂ from z)*c); ring }

@[simp] theorem hyperplaneEvaluationEquiv_apply (p : projectionSpace d 1)
    (v : projectionLine p) (hv : v≠0) (z : (projectionDualLineCore d).Fiber p) :
    hyperplaneEvaluationEquiv p v hv z = projectionDualLineFiberEquiv p z v := rfl

/-- In every chart the actual pairing is chart coefficient times the
coordinate of v in the unit local line frame. -/
theorem hyperplaneEvaluation_chart (p : projectionSpace d 1) (v : projectionLine p)
    (z : (projectionDualLineCore d).Fiber p) (i : Fin d) (hi : p ∈ projectionChartSet i) :
    projectionDualLineFiberEquiv p z v =
      ((projectionDualLineCore d).localTriv i ⟨p,z⟩).2 * inner ℂ (unitProjectionColumn p i) v.val := by
  let w := (projectionLineFiberEquiv p).symm v
  have h := projectionDualLine_pairing_chart p z w i hi
  have hw : ((projectionLineCore d).localTriv i ⟨p,w⟩).2 =
      inner ℂ (unitProjectionColumn p i) v.val := by
    have he := projectionLine_realization_chart p w i hi
    rw [LinearEquiv.apply_symm_apply] at he
    have hh := congrArg (inner ℂ (unitProjectionColumn p i)) he
    rw [inner_smul_right,inner_self_eq_norm_sq_to_K,unitProjectionColumn_norm p i hi] at hh
    simpa using hh.symm
  rw [hw] at h
  exact h.symm

/-- Pairing is continuous for actual continuously varying dual fibers and
line vectors. The line-membership premise only identifies its genuine domain. -/
theorem continuous_hyperplaneEvaluation {X : Type*} [TopologicalSpace X]
    (p : X → projectionSpace d 1) (hp : Continuous p)
    (v : X → EuclideanSpace ℂ (Fin d)) (hvm : ∀ x, v x ∈ projectionLine (p x))
    (hv : Continuous v) (z : ∀ x, (projectionDualLineCore d).Fiber (p x))
    (hz : Continuous (fun x => TotalSpace.mk' ℂ (p x) (z x))) :
    Continuous (fun x => projectionDualLineFiberEquiv (p x) (z x) ⟨v x,hvm x⟩) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let i := (projectionLineCore d).indexAt (p x)
  have hi : p x ∈ projectionChartSet i := (projectionLineCore d).mem_baseSet_at (p x)
  have hc := (FiberBundle.continuousAt_totalSpace ℂ _ (x₀ := x)).mp hz.continuousAt |>.2
  have hu := ((continuousOn_unitProjectionColumn i (p x) hi).continuousAt
    ((isOpen_projectionChartSet i).mem_nhds hi)).comp hp.continuousAt
  apply (hc.mul (hu.inner hv.continuousAt)).congr_of_eventuallyEq
  filter_upwards [hp.continuousAt ((isOpen_projectionChartSet i).mem_nhds hi)] with y hy
  exact hyperplaneEvaluation_chart (p y) ⟨v y,hvm y⟩ (z y) i hy

end Kaplansky

end

section
open Bundle Topology
open scoped InnerProductSpace
namespace Kaplansky
variable {X : Type*} [TopologicalSpace X] {d : ℕ}
variable (p : C(X,projectionSpace d 1)) (v : X → EuclideanSpace ℂ (Fin d))
variable (hvm : ∀ x, v x ∈ projectionLine (p x)) (hvn : ∀ x, v x≠0)

abbrev evaluationPullbackCore := pullbackLineCore (projectionDualLineCore d) p

def pullbackEvaluationEquiv (x : X) : (evaluationPullbackCore p).Fiber x ≃ₗ[ℂ] ℂ :=
  hyperplaneEvaluationEquiv (p x) ⟨v x,hvm x⟩ (fun h => hvn x (congrArg Subtype.val h))

include hvm hvn in
theorem evaluation_inner_ne_zero (x : X) (i : Fin d) (hi : p x ∈ projectionChartSet i) :
    inner ℂ (unitProjectionColumn (p x) i) (v x)≠0 := by
  intro h
  have he := unitProjectionColumn_reconstruct (p x) i hi (v x) (hvm x)
  rw [h,zero_smul] at he
  exact hvn x he.symm

theorem pullbackEvaluation_inverse_chart (x : X) (c : ℂ) (i : Fin d)
    (hi : p x ∈ projectionChartSet i) :
    ((evaluationPullbackCore p).localTriv i ⟨x,(pullbackEvaluationEquiv p v hvm hvn x).symm c⟩).2 =
      c / inner ℂ (unitProjectionColumn (p x) i) (v x) := by
  apply (eq_div_iff (evaluation_inner_ne_zero p v hvm hvn x i hi)).mpr
  change ((projectionDualLineCore d).localTriv i
    ⟨p x,(pullbackEvaluationEquiv p v hvm hvn x).symm c⟩).2 *
      inner ℂ (unitProjectionColumn (p x) i) (v x)=c
  exact (hyperplaneEvaluation_chart (p x) ⟨v x,hvm x⟩
    ((pullbackEvaluationEquiv p v hvm hvn x).symm c) i hi).symm.trans
      ((pullbackEvaluationEquiv p v hvm hvn x).apply_symm_apply c)

theorem continuous_evaluationPullback_toOriginal :
    Continuous (fun z : TotalSpace ℂ (evaluationPullbackCore p).Fiber =>
      TotalSpace.mk' ℂ (p z.proj) (show (projectionDualLineCore d).Fiber (p z.proj) from z.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(p.continuous.comp (FiberBundle.continuous_proj _ _)).continuousAt,?_⟩
  exact ((FiberBundle.continuousAt_totalSpace ℂ _ (x₀ := z)).mp
    (continuous_id (X := TotalSpace ℂ (evaluationPullbackCore p).Fiber)).continuousAt).2

variable (hv : Continuous v)

/-- Evaluation at a nonvanishing continuous line vector trivializes the
actual pullback hyperplane bundle, with its ordinary bundle topology. -/
def hyperplaneEvaluationHomeomorph : TotalSpace ℂ (evaluationPullbackCore p).Fiber ≃ₜ X × ℂ where
  toFun z := (z.proj,pullbackEvaluationEquiv p v hvm hvn z.proj z.2)
  invFun z := ⟨z.1,(pullbackEvaluationEquiv p v hvm hvn z.1).symm z.2⟩
  left_inv z := by
    obtain ⟨x,c⟩ := z
    exact congrArg (TotalSpace.mk' ℂ x) ((pullbackEvaluationEquiv p v hvm hvn x).symm_apply_apply c)
  right_inv z := Prod.ext rfl ((pullbackEvaluationEquiv p v hvm hvn z.1).apply_symm_apply z.2)
  continuous_toFun := by
    have hp := FiberBundle.continuous_proj ℂ (evaluationPullbackCore p).Fiber
    exact hp.prodMk (continuous_hyperplaneEvaluation (fun z : TotalSpace ℂ (evaluationPullbackCore p).Fiber => p z.proj) (p.continuous.comp hp)
      (fun z => v z.proj) (fun z => hvm z.proj) (hv.comp hp)
      (fun z : TotalSpace ℂ (evaluationPullbackCore p).Fiber =>
        (show (projectionDualLineCore d).Fiber (p z.proj) from z.2))
      (continuous_evaluationPullback_toOriginal p))
  continuous_invFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨continuous_fst.continuousAt,?_⟩
    let i := (projectionLineCore d).indexAt (p z.1)
    have hi : p z.1 ∈ projectionChartSet i := (projectionLineCore d).mem_baseSet_at (p z.1)
    have hu : ContinuousAt (fun w : X × ℂ => unitProjectionColumn (p w.1) i) z := ((continuousOn_unitProjectionColumn i (p z.1) hi).continuousAt
      ((isOpen_projectionChartSet i).mem_nhds hi)).comp p.continuous.continuousAt |>.comp continuous_fst.continuousAt
    have hc : ContinuousAt (fun w : X × ℂ => w.2 / inner ℂ (unitProjectionColumn (p w.1) i) (v w.1)) z := continuous_snd.continuousAt.div (hu.inner (hv.comp continuous_fst).continuousAt)
      (evaluation_inner_ne_zero p v hvm hvn z.1 i hi)
    apply hc.congr_of_eventuallyEq
    filter_upwards [(p.continuous.comp continuous_fst).continuousAt
      ((isOpen_projectionChartSet i).mem_nhds hi)] with w hw
    exact pullbackEvaluation_inverse_chart p v hvm hvn w.1 w.2 i hw

@[simp] theorem hyperplaneEvaluationHomeomorph_base
    (z : TotalSpace ℂ (evaluationPullbackCore p).Fiber) :
    (hyperplaneEvaluationHomeomorph p v hvm hvn hv z).1=z.proj := rfl

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

def graphVerticalFunctional (F : GraphFrame 1 k) (j : Fin k) :
    EuclideanSpace ℂ (Fin (1+k)) →ₗ[ℂ] ℂ :=
  (LinearMap.proj j).comp ((LinearMap.snd ℂ (GraphHorizontal 1) (GraphVertical k)).comp
    (F.toLinearMap.comp (EuclideanSpace.equiv (Fin (1+k)) ℂ).toLinearEquiv.toLinearMap))

theorem graphLineVector_mem (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    graphLineVector F A ∈ projectionLine (graphLineProjection F A) := by
  rw [graphLineProjection,nonzeroVectorProjection_line]
  exact Submodule.subset_span (Set.mem_singleton _)

def slopeEvaluationOneEquiv (k : ℕ) : GraphSlope 1 k ≃L[ℂ] GraphVertical k :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun A => A (fun _ => 1)
    invFun := fun z => (ContinuousLinearMap.proj (0 : Fin 1)).smulRight z
    left_inv := by
      intro A
      apply ContinuousLinearMap.ext
      intro v
      have hv : v=v 0 • (fun _ : Fin 1 => (1 : ℂ)) := by
        funext i
        have hi : i=0 := Subsingleton.elim _ _
        simp [hi]
      change v 0 • A (fun _ => 1)=A v
      rw [← map_smul,← hv]
    right_inv := by intro z; simp
    map_add' := by intro A B; rfl
    map_smul' := by intro c A; rfl }

end Kaplansky.ComplexGrassmann

end

open Bundle Topology
namespace Kaplansky.ComplexGrassmann

def standardLineGraphFrame (k : ℕ) : GraphFrame 1 k :=
  (LinearEquiv.piCongrLeft' ℂ (fun _ : Fin (1+k) => ℂ) finSumFinEquiv.symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin k) ℂ ℂ)

@[simp] theorem standardLineGraphFrame_vertical (k : ℕ) (v : Components 1 k) (i : Fin k) :
    (standardLineGraphFrame k v).2 i=v (positiveCoordinate k i) := by
  change v (Fin.natAdd 1 i)=v (positiveCoordinate k i)
  congr 1
  apply Fin.ext
  simp [positiveCoordinate,Nat.add_comm]

@[simp] theorem standardLineGraphFrame_horizontal (k : ℕ) (v : Components 1 k) (i : Fin 1) :
    (standardLineGraphFrame k v).1 i=v 0 := by
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  rfl

theorem standard_graphVector_zero (k : ℕ) :
    graphLineVector (standardLineGraphFrame k) 0=firstCoordinateVector k := by
  apply (EuclideanSpace.equiv (Fin (1+k)) ℂ).injective
  apply (standardLineGraphFrame k).injective
  rw [graphLineVector_coordinates,LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · funext i
    simp [firstCoordinateVector]
  · funext i
    have hi : positiveCoordinate k i≠0 := by
      intro h
      have := congrArg Fin.val h
      simp [positiveCoordinate] at this
    simp [firstCoordinateVector,hi]

/-- The graph-chart origin is exactly the unique zero previously identified
in the canonical coordinate sections of the actual hyperplane bundle. -/
theorem standard_graphProjection_zero (k : ℕ) :
    graphLineProjection (standardLineGraphFrame k) 0=firstCoordinateProjection k := by
  apply projectionLine_injective
  rw [graphLineProjection,nonzeroVectorProjection_line,standard_graphVector_zero,firstCoordinateProjection_line]

end Kaplansky.ComplexGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Orthonormal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Continuous orthonormal frames and orthogonal complements. -/

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky

section
open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ} {d : ℕ}

structure ContinuousIndependentStageFrame (a : LineStage K) (d : ℕ) where
  vector : ∀ y, Fin d → a.Fiber y
  continuous_vector : ∀ i, Continuous (fun y => TotalSpace.mk' a.Model y (vector y i))
  independent : ∀ y, LinearIndependent ℂ (vector y)

structure ContinuousOrthonormalStageFrame (a : LineStage K) (d : ℕ) where
  vector : ∀ y, Fin d → a.Fiber y
  continuous_vector : ∀ i, Continuous (fun y => TotalSpace.mk' a.Model y (vector y i))
  orthonormal : ∀ y, Orthonormal ℂ (vector y)

namespace ContinuousIndependentStageFrame
variable {a : LineStage K}

theorem continuous_gram (f : ContinuousIndependentStageFrame a d) :
    Continuous (fun y => Matrix.gram ℂ (f.vector y)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_lineStage_inner_over a id continuous_id (fun y => f.vector y i)
    (fun y => f.vector y j) (f.continuous_vector i) (f.continuous_vector j)

def normalize (f : ContinuousIndependentStageFrame a d) : ContinuousOrthonormalStageFrame a d where
  vector y := metricFrame (f.vector y)
  orthonormal y := metricFrame_orthonormal _ (f.independent y)
  continuous_vector j := by
    have hc := continuous_metricFrame_coefficients _ f.continuous_gram
      (fun y => Matrix.posDef_gram_of_linearIndependent (f.independent y))
    apply continuousOn_univ.mp
    unfold metricFrame frameMul
    apply continuousOn_bundle_sum (𝕜 := ℂ)
    intro i _
    apply continuousOn_bundle_smul
    · exact ((continuous_apply j).comp ((continuous_apply i).comp hc)).continuousOn
    · exact (f.continuous_vector i).continuousOn

end ContinuousIndependentStageFrame
end

open ComplexGrassmann
end Kaplansky

end

open Bundle Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_StageMaps
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Continuous stage maps and trivial input stages. -/

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ}

/-- A sum consisting entirely of trivial projective-product lines has a
global chart, for the existing bundle topology. -/
def lineStageTrivialTotalHomeomorph (a : LineStage K)
    (h : ∀ s, a.label s=none) (y₀ : ProjectiveProduct K) :
    TotalSpace a.Model a.Fiber ≃ₜ ProjectiveProduct K × a.Model := by
  let C := smoothLineSumCore K a.label
  let chart := C.indexAt y₀
  have hb : (C.localTriv chart).baseSet = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      change ∀ s, y ∈ (productLineCore K (a.label s)).baseSet (chart s)
      intro s
      have hz (l : Option ι) (hl : l=none) (c : productLineChartIndex K l) :
          y ∈ (productLineCore K l).baseSet c := by
        subst l
        exact Set.mem_univ _
      exact hz (a.label s) (h s) (chart s)

  exact (C.localTriv chart).toOpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv
    (by rw [(C.localTriv chart).source_eq,hb]; simp)
    (by rw [(C.localTriv chart).target_eq,hb]; simp)

@[simp] theorem lineStageTrivialTotalHomeomorph_apply (a : LineStage K)
    (h : ∀ s, a.label s=none) (y₀ : ProjectiveProduct K)
    (z : TotalSpace a.Model a.Fiber) :
    lineStageTrivialTotalHomeomorph a h y₀ z = (z.proj,(show a.Model from z.2)) := by
  apply Prod.ext
  · rfl
  · ext s
    change (productLineCore K (a.label s)).coordChange _ _ z.proj
      ((show a.Model from z.2) s) = _
    have hz (l : Option ι) (hl : l=none) (c e : productLineChartIndex K l) (v : ℂ) :
        (productLineCore K l).coordChange c e z.proj v=v := by
      subst l
      rfl
    exact hz (a.label s) (h s) _ _ _

end Kaplansky

end

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} [Fintype ι] {K : ι → ℕ}

/-- A linear map between the actual bundles, continuous on total spaces. -/
structure ContinuousStageMap (a b : LineStage K) where
  map : ∀ y, a.Fiber y →ₗ[ℂ] b.Fiber y
  continuous_map : Continuous (fun z : TotalSpace a.Model a.Fiber =>
    TotalSpace.mk' b.Model z.proj (map z.proj z.2))

namespace ContinuousStageMap
variable {a b c : LineStage K}

def comp (g : ContinuousStageMap b c) (f : ContinuousStageMap a b) :
    ContinuousStageMap a c :=
  ⟨fun y => (g.map y).comp (f.map y),g.continuous_map.comp f.continuous_map⟩

def smul (z : ℂ) (f : ContinuousStageMap a b) : ContinuousStageMap a b where
  map y := z • f.map y
  continuous_map := by
    apply continuousOn_univ.mp
    exact continuousOn_bundle_smul_over (𝕜 := ℂ) _
      (FiberBundle.continuous_proj _ _).continuousOn (fun _ => z) _
      continuousOn_const f.continuous_map.continuousOn

def sum {T : Type*} (s : Finset T) (f : T → ContinuousStageMap a b) :
    ContinuousStageMap a b where
  map y := ∑ t ∈ s, (f t).map y
  continuous_map := by
    simp only [LinearMap.sum_apply]
    apply continuousOn_univ.mp
    exact continuousOn_bundle_sum_over (𝕜 := ℂ) _
      (FiberBundle.continuous_proj _ _).continuousOn s
      (fun t z => (f t).map z.proj z.2) (fun t _ => (f t).continuous_map.continuousOn)

def proj {J : Type} [Fintype J] (a : J → LineStage K) (j : J) :
    ContinuousStageMap (LineStage.sum a) (a j) :=
  ⟨LineStage.sumProj a j,LineStage.continuous_sumProj a j⟩

def inj {J : Type} [Fintype J] (a : J → LineStage K) (j : J) :
    ContinuousStageMap (a j) (LineStage.sum a) :=
  ⟨LineStage.sumInj a j,LineStage.continuous_sumInj a j⟩

end ContinuousStageMap
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Content
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact dimension contents, their finite measures, and positive support. -/

section

noncomputable section
open Set TopologicalSpace
namespace Kaplansky

namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] (D : PositiveDimensionFunctional X)

theorem compactValue_le_one (K : Compacts X) : D.compactValue K ≤ D.toFun 1 :=
  D.compactValue_le K ⟨zero_le_one, fun _ _ => le_rfl⟩

end PositiveDimensionFunctional
end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal
namespace Kaplansky
namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] [NormalSpace X] [R1Space X]
    [MeasurableSpace X] [BorelSpace X] (D : PositiveDimensionFunctional X)

theorem measure_open (U : Opens X) :
    D.measure (U : Set X) = D.content.innerContent U := by
  rw [measure, Content.measure_apply _ U.isOpen.measurableSet, Content.outerMeasure_opens]

theorem measure_open_eq_sup (U : Opens X) :
    D.measure (U : Set X) = ⨆ (K : Compacts X) (_ : (K : Set X) ⊆ U), D.content K :=
  D.measure_open U

omit [R1Space X] [MeasurableSpace X] [BorelSpace X] in
theorem content_le_one (K : Compacts X) : D.content K ≤ ENNReal.ofReal (D.toFun 1) := by
  rw [← ENNReal.ofReal_toReal (show D.content K ≠ ∞ from ENNReal.coe_ne_top)]
  rw [D.content_toReal K]
  exact ENNReal.ofReal_le_ofReal (D.compactValue_le_one K)

theorem measure_univ_le : D.measure Set.univ ≤ ENNReal.ofReal (D.toFun 1) := by
  change D.measure ((⊤ : Opens X) : Set X) ≤ _
  rw [D.measure_open_eq_sup]
  exact iSup₂_le fun K _ => D.content_le_one K

instance measure_isFiniteMeasure : IsFiniteMeasure D.measure :=
  ⟨D.measure_univ_le.trans_lt ENNReal.ofReal_lt_top⟩

end PositiveDimensionFunctional
end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace
namespace Kaplansky
namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] (D : PositiveDimensionFunctional X)

theorem zero_value : D.toFun 0 = 0 := by
  have h := D.orthogonal 0 0 le_rfl le_rfl (mul_zero _)
  rw [add_zero] at h
  linarith

theorem compactValue_empty : D.compactValue ⊥ = 0 := by
  apply le_antisymm _ (D.compactValue_nonneg _)
  rw [← D.zero_value]
  exact D.compactValue_le _ ⟨le_rfl, fun _ hx => False.elim hx⟩

/-- Positive scalar invariance is a dimension property, not spectral homogeneity. -/
def ScaleInvariant : Prop := ∀ (f : C(X, ℝ)), 0 ≤ f → ∀ r : ℝ, 0 < r →
  D.toFun (r • f) = D.toFun f

theorem compactValue_le_of_pos (hscale : D.ScaleInvariant) (K : Compacts X)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (hK : ∀ x ∈ K, 0 < f x) :
    D.compactValue K ≤ D.toFun f := by
  by_cases hne : (K : Set X).Nonempty
  · obtain ⟨x, hx, hmin⟩ := K.isCompact.exists_isMinOn hne f.continuous.continuousOn
    have hp := hK x hx
    rw [← hscale f hf ((f x)⁻¹) (inv_pos.mpr hp)]
    apply D.compactValue_le
    refine ⟨fun y => mul_nonneg (inv_nonneg.mpr hp.le) (hf y), ?_⟩
    intro y hy
    change 1 ≤ (f x)⁻¹ * f y
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hp).mpr (by simpa using hmin hy)
  · have h : K = ⊥ := by
      ext x
      change (x ∈ K) ↔ False
      exact ⟨fun hx => hne ⟨x, hx⟩, False.elim⟩
    rw [h, D.compactValue_empty]
    exact D.nonneg f hf

variable [CompactSpace X]

/-- A function vanishing off K has dimension at most the compact content of K. -/
theorem value_le_compactValue_of_support (hscale : D.ScaleInvariant) (K : Compacts X)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (hs : ∀ x, x ∉ K → f x=0) :
    D.toFun f ≤ D.compactValue K := by
  apply D.le_compactValue
  intro g hg
  have hp : 0 < ‖f‖+1 := by linarith [norm_nonneg f]
  have hle : f ≤ (‖f‖+1) • g := by
    intro x
    change f x ≤ (‖f‖+1)*g x
    by_cases hx : x ∈ K
    · have hb : f x ≤ ‖f‖+1 := (f.apply_le_norm x).trans (by linarith)
      exact hb.trans (le_mul_of_one_le_right hp.le (hg.2 x hx))
    · rw [hs x hx]
      exact mul_nonneg hp.le (hg.1 x)
  calc
    D.toFun f ≤ D.toFun ((‖f‖+1) • g) := D.mono _ _ hf hle
    _ = D.toFun g := hscale g hg.1 _ hp

end PositiveDimensionFunctional
end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal Topology
namespace Kaplansky

namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] (D : PositiveDimensionFunctional X)

/-- Lower semicontinuity is required only on the nonnegative cone. -/
def ConeLowerSemicontinuous : Prop :=
  LowerSemicontinuous (fun f : {f : C(X, ℝ) // 0 ≤ f} => D.toFun f.val)

theorem exists_positive_cutoff (hsc : D.ConeLowerSemicontinuous)
    (f : C(X, ℝ)) (hf : 0 ≤ f) {r : ℝ} (hr : r < D.toFun f) :
    ∃ t : ℝ, 0 < t ∧ r < D.toFun (continuousDimensionCutoff f t) := by
  let g : ℝ → {f : C(X, ℝ) // 0 ≤ f} :=
    fun t => ⟨continuousDimensionCutoff f t, continuousDimensionCutoff_nonneg f t⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℝ × X => max (f p.2-p.1) 0)
    fun_prop
  have h0 : r < D.toFun (g 0).val := by
    simpa only [g, continuousDimensionCutoff_zero f hf] using hr
  have he := (hsc.comp hg) 0 r h0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ/2, half_pos hδ, hball ?_⟩
  change dist (δ/2) (0 : ℝ) < δ
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
  linarith

variable [CompactSpace X] [NormalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]

/-- The finite measure represents dimension on every positive support.
The proof uses genuine compact contents and lower semicontinuity, not an
assumed measure representation or finite-spectrum approximation. -/
theorem measure_positive_support (hscale : D.ScaleInvariant) (hsc : D.ConeLowerSemicontinuous)
    (f : C(X, ℝ)) (hf : 0 ≤ f) :
    D.measure {x | 0 < f x} = ENNReal.ofReal (D.toFun f) := by
  let U : Opens X := ⟨{x | 0 < f x}, isOpen_lt continuous_const f.continuous⟩
  change D.measure (U : Set X) = _
  apply le_antisymm
  · rw [D.measure_open_eq_sup]
    refine iSup₂_le fun K hK => ?_
    rw [← ENNReal.ofReal_toReal (show D.content K ≠ ∞ from ENNReal.coe_ne_top), D.content_toReal]
    exact ENNReal.ofReal_le_ofReal (D.compactValue_le_of_pos hscale K f hf (fun x hx => hK hx))
  · have hl : D.toFun f ≤ (D.measure (U : Set X)).toReal := by
      apply le_of_forall_lt
      intro r hr
      obtain ⟨t, ht, hrt⟩ := D.exists_positive_cutoff hsc f hf hr
      let K : Compacts X := ⟨{x | t ≤ f x}, (isClosed_le continuous_const f.continuous).isCompact⟩
      have hKU : (K : Set X) ⊆ U := fun x hx => ht.trans_le hx
      have hs : ∀ x, x ∉ K → continuousDimensionCutoff f t x = 0 := by
        intro x hx
        change max (f x-t) 0=0
        apply max_eq_right
        have hx' : ¬t ≤ f x := hx
        linarith
      have hle := D.value_le_compactValue_of_support hscale K
        (continuousDimensionCutoff f t) (continuousDimensionCutoff_nonneg f t) hs
      have hm : D.compactValue K ≤ (D.measure (U : Set X)).toReal := by
        rw [← D.content_toReal K, D.measure_open]
        apply ENNReal.toReal_mono
        · rw [← D.measure_open]
          exact measure_ne_top _ _
        · exact D.content.le_innerContent K U hKU
      exact hrt.trans_le (hle.trans hm)
    calc
      ENNReal.ofReal (D.toFun f) ≤ ENNReal.ofReal (D.measure (U : Set X)).toReal :=
        ENNReal.ofReal_le_ofReal hl
      _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)

end PositiveDimensionFunctional
end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.OrderedStates_Semigroup
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Catalytic orders, ordered group completion, and normalized semigroup states. -/

namespace Kaplansky

section
variable (S : Type*) [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

variable {S}

/-- The stabilizing summand records the cancellation which is unavailable
in the original monoid. -/
def SemigroupDifference.Rel (a b : SemigroupDifference S) : Prop :=
  ∃ c : S, a.1 + b.2 + c ≤ b.1 + a.2 + c

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Regularization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Regularized dimensions, cutoff calculus, and topological regularization. -/

open scoped Matrix CStarAlgebra Topology

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
namespace CuntzDimensionState

/-- Every number strictly below the supremum is exceeded by one actual cutoff value. -/
theorem exists_lt_cutoff_value (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {r : ℝ} (h : r < d.regularized a) : ∃ ε : ℝ, 0 < ε ∧ r < d.value (a.cutoff ε) := by
  by_contra! hn
  exact (not_le_of_gt h) (d.regularized_le a hn)

end CuntzDimensionState


/-- A norm neighborhood controls one fixed cutoff by the regularized value. -/
theorem CuntzDimensionState.cutoff_value_le_regularized_of_norm {n : ℕ}
    (d : CuntzDimensionState A) {a b : CStarMatrix (Fin n) (Fin n) A}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) (hab : ‖a-b‖ < ε/2) :
    d.value ((⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ : CuntzPositiveMatrix A).cutoff ε) ≤
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ := by
  have hn : ‖a - cuntzCutoff b (ε/2)‖ < ε := by
    have ht : ‖a - cuntzCutoff b (ε/2)‖ ≤ ‖a-b‖ + ‖b - cuntzCutoff b (ε/2)‖ := by
      simpa only [dist_eq_norm] using dist_triangle a b (cuntzCutoff b (ε/2))
    have he := norm_sub_cuntzCutoff_le hb (half_pos hε).le
    linarith
  have hc := cuntzLE_cutoff_of_norm_sub_lt ha (cuntzCutoff_nonneg b (ε/2)).isSelfAdjoint hn
  exact (d.value_mono (a := (⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ : CuntzPositiveMatrix A).cutoff ε)
    (b := (⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ : CuntzPositiveMatrix A).cutoff (ε/2)) hc).trans
    (d.cutoff_value_le_regularized _ (half_pos hε))

/-- Lower semicontinuity on the full positive cone in each actual matrix norm. -/
theorem CuntzDimensionState.regularized_lowerSemicontinuous (d : CuntzDimensionState A)
    (n : ℕ) : LowerSemicontinuous (fun a : {a : CStarMatrix (Fin n) (Fin n) A // 0 ≤ a} =>
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm a.val, a.property⟩) := by
  intro a r hr
  obtain ⟨ε, hε, he⟩ := d.exists_lt_cutoff_value _ hr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ε/2, half_pos hε, ?_⟩
  intro b hb
  have hdist : ‖a.val-b.val‖ < ε/2 := by
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hb
  exact he.trans_le (d.cutoff_value_le_regularized_of_norm a.property b.property hε hdist)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Commutative
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Commutative dimension contents and continuous positive functions. -/

section
open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A X : Type*} [CStarAlgebra A] [TopologicalSpace X]

/-- Transport the existing regularized dimension through a real star algebra
homomorphism. On negative functions the auxiliary value is zero and is unused. -/
def CuntzDimensionState.continuousDimension (d : CuntzDimensionState A) {n : ℕ}
    (φ : C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A) : PositiveDimensionFunctional X where
  toFun f := if hf : 0 ≤ f then d.regularized ⟨n, CStarMatrix.ofMatrix.symm (φ f), map_nonneg φ hf⟩ else 0
  nonneg f hf := by simp only [dite_eq_left hf]; exact d.regularized_nonneg _
  mono f g hf hfg := by
    simp only [dite_eq_left hf, dite_eq_left (hf.trans hfg)]
    exact d.regularized_mono (cuntzLE_of_nonneg_le (map_nonneg φ hf) (OrderHomClass.mono φ hfg))
  subadd f g hf hg := by
    simp only [dite_eq_left hf, dite_eq_left hg, dite_eq_left (add_nonneg hf hg), map_add]
    exact d.regularized_sum_le _ _ (map_nonneg φ hf) (map_nonneg φ hg)
  orthogonal f g hf hg hfg := by
    simp only [dite_eq_left hf, dite_eq_left hg, dite_eq_left (add_nonneg hf hg), map_add]
    apply d.regularized_orthogonal_add _ _ (map_nonneg φ hf) (map_nonneg φ hg)
    rw [← map_mul, hfg, map_zero]

@[simp] theorem CuntzDimensionState.continuousDimension_apply (d : CuntzDimensionState A) {n : ℕ}
    (φ : C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A) (f : C(X, ℝ)) (hf : 0 ≤ f) :
    (d.continuousDimension φ).toFun f =
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm (φ f), map_nonneg φ hf⟩ := by
  simp [continuousDimension, hf]

end Kaplansky

end

open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A X : Type*} [CStarAlgebra A] [TopologicalSpace X]
namespace CuntzDimensionState

theorem continuousDimension_scaleInvariant (d : CuntzDimensionState A) {n : ℕ}
    (φ : C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A) :
    (d.continuousDimension φ).ScaleInvariant := by
  intro f hf r hr
  rw [d.continuousDimension_apply φ f hf,
    d.continuousDimension_apply φ (r • f) (fun x => mul_nonneg hr.le (hf x))]
  apply d.regularized_eq
  change CuntzEquivalent (CStarMatrix.ofMatrix.symm (φ (r • f))) _
  rw [map_smul]
  exact cuntzEquivalent_pos_smul (φ f) hr

theorem continuousDimension_lowerSemicontinuous (d : CuntzDimensionState A) {n : ℕ}
    (φ : C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A) (hφ : Continuous φ) :
    (d.continuousDimension φ).ConeLowerSemicontinuous := by
  let g : {f : C(X, ℝ) // 0 ≤ f} → {a : CStarMatrix (Fin n) (Fin n) A // 0 ≤ a} :=
    fun f => ⟨φ f.val, map_nonneg φ f.property⟩
  have hg : Continuous g := (hφ.comp continuous_subtype_val).subtype_mk _
  have h := (d.regularized_lowerSemicontinuous n).comp hg
  change LowerSemicontinuous (fun f : {f : C(X, ℝ) // 0 ≤ f} => (d.continuousDimension φ).toFun f.val)
  have he : (fun f : {f : C(X, ℝ) // 0 ≤ f} => (d.continuousDimension φ).toFun f.val) =
      (fun f : {f : C(X, ℝ) // 0 ≤ f} => d.regularized ⟨n, CStarMatrix.ofMatrix.symm (φ f.val), map_nonneg φ f.property⟩) := by
    funext f
    exact d.continuousDimension_apply φ f.val f.property
  rw [he]
  exact h

variable [CompactSpace X] [NormalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]

/-- The measure of a positive support is the actual regularized ambient
Cuntz dimension of its image, with no functional or measure-existence premise. -/
theorem continuousDimension_measure_positive_support (d : CuntzDimensionState A) {n : ℕ}
    (φ : C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A) (hφ : Continuous φ)
    (f : C(X, ℝ)) (hf : 0 ≤ f) :
    (d.continuousDimension φ).measure {x | 0 < f x} =
      ENNReal.ofReal (d.regularized ⟨n, CStarMatrix.ofMatrix.symm (φ f), map_nonneg φ hf⟩) := by
  rw [← d.continuousDimension_apply φ f hf]
  exact (d.continuousDimension φ).measure_positive_support
    (d.continuousDimension_scaleInvariant φ) (d.continuousDimension_lowerSemicontinuous φ hφ) f hf

end CuntzDimensionState
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Distribution
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Spectral distributions, integrals, and scalar covariance. -/

open scoped Matrix CStarAlgebra
open MeasureTheory

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

theorem cuntzCutoff_one_of_lt {t : ℝ} (ht : t < 1) :
    cuntzCutoff (1 : A) t = (1 - t) • (1 : A) := by
  have h := cfc_algebraMap (A := A) (1 : ℝ) (fun x : ℝ => max (x - t) 0)
  simpa only [cuntzCutoff, map_one, max_eq_left (sub_nonneg.mpr ht.le),
    Algebra.algebraMap_eq_smul_one] using h

namespace CuntzDimensionState

theorem distribution_add (d : CuntzDimensionState A) (a b : CuntzPositiveMatrix A) (t : ℝ) :
    d.distribution (a.add b) t = d.distribution a t + d.distribution b t := by
  simp only [distribution, CuntzPositiveMatrix.cutoff_add, d.regularized_add]

/-- Block addition is preserved by the finite spectral integral. -/
theorem spectralValue_add (d : CuntzDimensionState A) (a b : CuntzPositiveMatrix A) :
    d.spectralValue (a.add b) = d.spectralValue a + d.spectralValue b := by
  let R := ‖CStarMatrix.ofMatrix (a.add b).matrix‖ +
    ‖CStarMatrix.ofMatrix a.matrix‖ + ‖CStarMatrix.ofMatrix b.matrix‖
  have ha : ‖CStarMatrix.ofMatrix a.matrix‖ ≤ R := by
    dsimp [R]
    linarith [norm_nonneg (CStarMatrix.ofMatrix (a.add b).matrix),
      norm_nonneg (CStarMatrix.ofMatrix a.matrix), norm_nonneg (CStarMatrix.ofMatrix b.matrix)]
  have hb : ‖CStarMatrix.ofMatrix b.matrix‖ ≤ R := by
    dsimp [R]
    linarith [norm_nonneg (CStarMatrix.ofMatrix (a.add b).matrix),
      norm_nonneg (CStarMatrix.ofMatrix a.matrix), norm_nonneg (CStarMatrix.ofMatrix b.matrix)]
  have hab : ‖CStarMatrix.ofMatrix (a.add b).matrix‖ ≤ R := by
    dsimp [R]
    linarith [norm_nonneg (CStarMatrix.ofMatrix (a.add b).matrix),
      norm_nonneg (CStarMatrix.ofMatrix a.matrix), norm_nonneg (CStarMatrix.ofMatrix b.matrix)]
  rw [d.spectralValue_eq_integral _ hab, d.spectralValue_eq_integral _ ha,
    d.spectralValue_eq_integral _ hb]
  simp_rw [d.distribution_add]
  exact intervalIntegral.integral_add (d.distribution_intervalIntegrable a 0 R)
    (d.distribution_intervalIntegrable b 0 R)

/-- A normalized dimension state forces the underlying algebra to be nonzero. -/
theorem nontrivial (d : CuntzDimensionState A) : Nontrivial A := by
  rcases subsingleton_or_nontrivial A with h | h
  · let := h
    have he := d.regularized_of_matrix_eq_zero (.unit 1) (Subsingleton.elim _ _)
    rw [d.regularized_unit] at he
    norm_num at he
  · exact h

theorem distribution_unit_of_lt (d : CuntzDimensionState A) (n : ℕ) {t : ℝ} (ht : t < 1) :
    d.distribution (.unit n) t = (n : ℝ) := by
  have hp : 0 < 1-t := sub_pos.mpr ht
  have he := cuntzCutoff_one_of_lt (A := CStarMatrix (Fin n) (Fin n) A) ht
  rw [← d.regularized_unit n]
  apply d.regularized_eq
  change CuntzEquivalent (CStarMatrix.ofMatrix.symm
    (cuntzCutoff (1 : CStarMatrix (Fin n) (Fin n) A) t)) (1 : Matrix (Fin n) (Fin n) A)
  rw [he]
  exact cuntzEquivalent_pos_smul 1 hp

end CuntzDimensionState

/-- Scaling the element rescales the spectral threshold. -/
theorem cuntzCutoff_pos_smul {a : A} (ha : 0 ≤ a) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    cuntzCutoff (r • a) t = r • cuntzCutoff a (t/r) := by
  unfold cuntzCutoff
  rw [← cfc_comp_const_mul r (fun s : ℝ => max (s-t) 0) a (ha := ha.isSelfAdjoint),
    ← cfc_const_mul r (fun s : ℝ => max (s-t/r) 0) a]
  apply cfc_congr
  intro s hs
  dsimp only
  rw [mul_max_of_nonneg _ _ hr.le, mul_zero, mul_sub, mul_div_cancel₀ _ hr.ne']

/-- Nonnegative scalar multiplication of a positive finite matrix. -/
def CuntzPositiveMatrix.scale (a : CuntzPositiveMatrix A) (r : ℝ) (hr : 0 ≤ r) :
    CuntzPositiveMatrix A :=
  ⟨a.size, CStarMatrix.ofMatrix.symm (r • CStarMatrix.ofMatrix a.matrix),
    smul_nonneg hr a.nonneg⟩

namespace CuntzDimensionState

theorem distribution_pos_scale (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    d.distribution (a.scale r hr.le) t = d.distribution a (t/r) := by
  apply d.regularized_eq
  have he := cuntzCutoff_pos_smul a.nonneg hr t
  have hc := cuntzEquivalent_pos_smul
    (cuntzCutoff (CStarMatrix.ofMatrix a.matrix) (t / r)) hr
  exact Eq.mpr (congrArg (fun c => CuntzEquivalent (CStarMatrix.ofMatrix.symm c)
    (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix a.matrix) (t / r)))) he) hc

/-- The integral scales with the positive scalar, including zero. -/
theorem spectralValue_scale (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    (r : ℝ) (hr : 0 ≤ r) :
    d.spectralValue (a.scale r hr) = r * d.spectralValue a := by
  rcases eq_or_lt_of_le hr with h | h
  · subst r
    have hn : ‖CStarMatrix.ofMatrix (a.scale 0 hr).matrix‖ = 0 := by
      change ‖(0 : ℝ) • CStarMatrix.ofMatrix a.matrix‖ = 0
      rw [zero_smul, norm_zero]
    simp only [spectralValue, hn, intervalIntegral.integral_same, zero_mul]
  · let : NormedSpace ℝ (CStarMatrix (Fin a.size) (Fin a.size) A) :=
      NormedSpace.restrictScalars ℝ ℂ _
    let : NormSMulClass ℝ (CStarMatrix (Fin a.size) (Fin a.size) A) :=
      NormedSpace.toNormSMulClass
    change (∫ t in (0 : ℝ)..‖r • CStarMatrix.ofMatrix a.matrix‖,
        d.distribution (a.scale r hr) t) = _
    simp_rw [d.distribution_pos_scale a h]
    rw [norm_smul, Real.norm_of_nonneg hr, intervalIntegral.integral_comp_div _ h.ne']
    simp only [zero_div, mul_div_cancel_left₀ _ h.ne', smul_eq_mul, spectralValue]

end CuntzDimensionState
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_SquareCutoff
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Intertwining functional calculus and cutoffs of adjoint squares. -/

open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] matrixRealFunctionalCalculus productMatrixRealFunctionalCalculus

/-- Matching positive cutoffs of unequal rectangular Gram matrices are
Cuntz equivalent, proved by an exact rectangular factorization. -/
theorem cuntzEquivalent_cutoff_rectangular_gram {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (x : Matrix ι κ A) (ha : 0 ≤ CStarMatrix.ofMatrix (x*x.conjTranspose))
    (hb : 0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x)) {ε : ℝ} (hε : 0 < ε) :
    CuntzEquivalent
      (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix (x*x.conjTranspose)) ε))
      (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix (x.conjTranspose*x)) ε)) := by
  classical
  let a := CStarMatrix.ofMatrix (x*x.conjTranspose)
  let b := CStarMatrix.ofMatrix (x.conjTranspose*x)
  let L := cfc (cutoffSquareFactor ε) a
  let R := cfc (cutoffSquareFactor ε) b
  have hL : star L = L := (cfc_predicate _ _ : IsSelfAdjoint L).star_eq
  have hR : star R = R := (cfc_predicate _ _ : IsSelfAdjoint R).star_eq
  have hx : CStarMatrix.ofMatrix.symm L * x = x * CStarMatrix.ofMatrix.symm R :=
    cfc_matrix_intertwine a b x ha hb (Matrix.mul_assoc _ _ _) _
      (cutoffSquareFactor_continuous hε)
  let y := CStarMatrix.ofMatrix.symm L * x
  have hy : y = x * CStarMatrix.ofMatrix.symm R := hx
  have hl : y*y.conjTranspose = CStarMatrix.ofMatrix.symm (cuntzCutoff a ε) := by
    dsimp only [y]
    rw [Matrix.conjTranspose_mul]
    change CStarMatrix.ofMatrix.symm L * x * (x.conjTranspose * CStarMatrix.ofMatrix.symm (star L)) = _
    rw [hL]
    have he := cutoffSquareFactor_cfc ha hε
    change L * a * L = _ at he
    have he' := congrArg CStarMatrix.ofMatrix.symm he
    change CStarMatrix.ofMatrix.symm L * (x*x.conjTranspose) * CStarMatrix.ofMatrix.symm L = _ at he'
    simpa only [Matrix.mul_assoc] using he'
  have hr : y.conjTranspose*y = CStarMatrix.ofMatrix.symm (cuntzCutoff b ε) := by
    rw [hy, Matrix.conjTranspose_mul]
    change CStarMatrix.ofMatrix.symm (star R) * x.conjTranspose * (x * CStarMatrix.ofMatrix.symm R) = _
    rw [hR]
    have he := cutoffSquareFactor_cfc hb hε
    change R * b * R = _ at he
    have he' := congrArg CStarMatrix.ofMatrix.symm he
    change CStarMatrix.ofMatrix.symm R * (x.conjTranspose*x) * CStarMatrix.ofMatrix.symm R = _ at he'
    simpa only [Matrix.mul_assoc] using he'
  rw [← hl, ← hr]
  exact cuntzEquivalent_rectangular_gram y

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Spectral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Spectral candidates on squares, orthogonal elements, and complex elements. -/

open scoped Matrix CStarAlgebra ComplexStarModule ComplexOrder
open MeasureTheory

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

namespace CuntzDimensionState

/-- The spectral distributions of rectangular Gram matrices agree at
all strictly positive thresholds, not just on the uncut matrices. -/
theorem distribution_rectangular_gram (d : CuntzDimensionState A) {n m : ℕ}
    (x : Matrix (Fin n) (Fin m) A) (ha : 0 ≤ CStarMatrix.ofMatrix (x*x.conjTranspose))
    (hb : 0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x)) {t : ℝ} (ht : 0 < t) :
    d.distribution ⟨n, x*x.conjTranspose, ha⟩ t =
      d.distribution ⟨m, x.conjTranspose*x, hb⟩ t :=
  d.regularized_eq (cuntzEquivalent_cutoff_rectangular_gram x ha hb ht)

/-- The spectral integral satisfies square swapping in unequal sizes. -/
theorem spectralValue_rectangular_gram (d : CuntzDimensionState A) {n m : ℕ}
    (x : Matrix (Fin n) (Fin m) A) (ha : 0 ≤ CStarMatrix.ofMatrix (x*x.conjTranspose))
    (hb : 0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x)) :
    d.spectralValue ⟨n, x*x.conjTranspose, ha⟩ =
      d.spectralValue ⟨m, x.conjTranspose*x, hb⟩ := by
  let a : CuntzPositiveMatrix A := ⟨n, x*x.conjTranspose, ha⟩
  let b : CuntzPositiveMatrix A := ⟨m, x.conjTranspose*x, hb⟩
  let R := ‖CStarMatrix.ofMatrix a.matrix‖ + ‖CStarMatrix.ofMatrix b.matrix‖
  have hR : ‖CStarMatrix.ofMatrix a.matrix‖ ≤ R := le_add_of_nonneg_right (norm_nonneg _)
  have hR' : ‖CStarMatrix.ofMatrix b.matrix‖ ≤ R := le_add_of_nonneg_left (norm_nonneg _)
  rw [d.spectralValue_eq_integral a hR, d.spectralValue_eq_integral b hR']
  apply intervalIntegral.integral_congr_Ioo_of_le (le_trans (norm_nonneg _) hR)
  intro t ht
  exact d.distribution_rectangular_gram x ha hb ht.1

/-- In particular, the original square-swap axiom holds on the positive squares. -/
theorem spectralValue_square_swap (d : CuntzDimensionState A) {n : ℕ}
    (x : CStarMatrix (Fin n) (Fin n) A) :
    d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm (x*star x), mul_star_self_nonneg x⟩ =
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm (star x*x), star_mul_self_nonneg x⟩ :=
  d.spectralValue_rectangular_gram (CStarMatrix.ofMatrix.symm x) _ _

end CuntzDimensionState

namespace CuntzDimensionState

attribute [local instance] OAI.Kaplansky.matrixNonUnitalRealFunctionalCalculus
/-- Real scalar homogeneity holds for the signed construction. -/
theorem signedValue_smul (d : CuntzDimensionState A) {n : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) (r : ℝ) : d.signedValue (r • a) = r*d.signedValue a := by
  have hp (b : CStarMatrix (Fin n) (Fin n) A) (hb : 0 ≤ b) (s : ℝ) (hs : 0 ≤ s) :
      d.positiveValue (s • b) (smul_nonneg hs hb) = s*d.positiveValue b hb :=
    d.spectralValue_scale ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ s hs
  rcases le_total 0 r with hr | hr
  · simp only [signedValue, CFC.posPart_smul_of_nonneg hr, CFC.negPart_smul_of_nonneg hr,
      hp a⁺ (CFC.posPart_nonneg a) r hr, hp a⁻ (CFC.negPart_nonneg a) r hr,
      mul_sub]
  · simp only [signedValue, CFC.posPart_smul_of_nonpos hr, CFC.negPart_smul_of_nonpos hr,
      hp a⁺ (CFC.posPart_nonneg a) (-r) (neg_nonneg.mpr hr),
      hp a⁻ (CFC.negPart_nonneg a) (-r) (neg_nonneg.mpr hr)]
    ring

/-- Square swapping for the same whole-matrix construction. -/
theorem complexValue_square_swap (d : CuntzDimensionState A) {n : ℕ}
    (x : CStarMatrix (Fin n) (Fin n) A) :
    d.complexValue (star x*x) = d.complexValue (x*star x) := by
  rw [d.complexValue_of_nonneg (star_mul_self_nonneg x), d.complexValue_of_nonneg (mul_star_self_nonneg x)]
  exact congrArg (fun r : ℝ => (r : ℂ)) (d.spectralValue_square_swap x).symm

end CuntzDimensionState
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Measure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Real functional calculus and signed and complex spectral measures. -/

open scoped Matrix CStarAlgebra ComplexOrder
open Set MeasureTheory TopologicalSpace

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance] matrixRealFunctionalCalculus matrixNonUnitalRealFunctionalCalculus matrixNonnegSpectrum
variable {X : Type*} [TopologicalSpace X]

variable [CompactSpace X]

theorem continuous_continuousRealInclusion : Continuous (continuousRealInclusion (X := X)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : C(X, ℝ) × X => (p.1 p.2 : ℂ))
  fun_prop

attribute [local instance] OAI.Kaplansky.continuousMapRealFunctionalCalculus
theorem continuousRealInclusion_cutoff (f : C(X, ℝ)) (hf : 0 ≤ f) (t : ℝ) :
    cuntzCutoff (continuousRealInclusion f) t =
      continuousRealInclusion (continuousDimensionCutoff f t) := by
  ext x
  have hsa : IsSelfAdjoint (continuousRealInclusion f) := (map_nonneg continuousRealInclusion hf).isSelfAdjoint
  have hsax : IsSelfAdjoint (continuousRealInclusion f x) := by
    change star (f x : ℂ) = (f x : ℂ)
    simp
  have h := (ContinuousMap.evalStarAlgHom ℂ ℂ x).map_cfc
    (fun s : ℝ => max (s-t) 0) (continuousRealInclusion f) (ha := hsa) (hφa := hsax)
  change (cfc (fun s : ℝ => max (s-t) 0) (continuousRealInclusion f)) x = _ at h
  change (cfc (fun s : ℝ => max (s-t) 0) (continuousRealInclusion f)) x = _
  rw [h]
  exact cfc_algebraMap (A := ℂ) (f x) (fun s : ℝ => max (s-t) 0)

variable {A : Type*} [CStarAlgebra A] {n : ℕ}

theorem realFunctionHom_continuous (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) :
    Continuous (realFunctionHom ψ) := by
  have hψ : Continuous ψ := by fun_prop
  exact hψ.comp continuous_continuousRealInclusion

/-- Genuine CFC naturality identifies the image of a scalar cutoff. -/
theorem realFunctionHom_cutoff (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (t : ℝ) :
    realFunctionHom ψ (continuousDimensionCutoff f t) = cuntzCutoff (realFunctionHom ψ f) t := by
  change ψ (continuousRealInclusion (continuousDimensionCutoff f t)) = _
  rw [← continuousRealInclusion_cutoff f hf t]
  exact ψ.map_cfc (fun s : ℝ => max (s-t) 0) (continuousRealInclusion f)
    (ha := (map_nonneg continuousRealInclusion hf).isSelfAdjoint)
    (hφa := (map_nonneg ψ (map_nonneg continuousRealInclusion hf)).isSelfAdjoint)

section Measures
variable [NormalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
namespace CuntzDimensionState

/-- The single finite Borel measure associated with a commutative representation. -/
def spectralMeasure (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) : Measure X :=
  (d.continuousDimension (realFunctionHom ψ)).measure

instance spectralMeasure_finite (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) : IsFiniteMeasure (d.spectralMeasure ψ) :=
  inferInstanceAs (IsFiniteMeasure (d.continuousDimension (realFunctionHom ψ)).measure)

theorem spectralMeasure_lt (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (t : ℝ) :
    d.spectralMeasure ψ {x | t < f x} = ENNReal.ofReal
      (d.distribution ⟨n, CStarMatrix.ofMatrix.symm (realFunctionHom ψ f), map_nonneg (realFunctionHom ψ) hf⟩ t) := by
  have he : {x | t < f x} = {x | 0 < continuousDimensionCutoff f t x} := by
    ext x
    simp only [continuousDimensionCutoff, ContinuousMap.coe_mk, lt_max_iff, lt_self_iff_false, or_false]
    exact (sub_pos : 0 < f x-t ↔ t < f x).symm
  rw [he]
  change (d.continuousDimension (realFunctionHom ψ)).measure _ = _
  rw [d.continuousDimension_measure_positive_support _ (realFunctionHom_continuous ψ)
    _ (continuousDimensionCutoff_nonneg f t)]
  congr 1
  apply d.regularized_eq
  change CuntzEquivalent (CStarMatrix.ofMatrix.symm (realFunctionHom ψ (continuousDimensionCutoff f t)))
    (CStarMatrix.ofMatrix.symm (cuntzCutoff (realFunctionHom ψ f) t))
  rw [realFunctionHom_cutoff ψ f hf]
  exact .refl _

theorem spectralMeasure_real_lt (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (t : ℝ) :
    (d.spectralMeasure ψ).real {x | t < f x} =
      d.distribution ⟨n, CStarMatrix.ofMatrix.symm (realFunctionHom ψ f), map_nonneg (realFunctionHom ψ) hf⟩ t := by
  rw [measureReal_def, d.spectralMeasure_lt ψ f hf, ENNReal.toReal_ofReal (d.distribution_nonneg _ _)]

/-- The original finite spectral integral equals the integral against the
constructed measure. No new choice of positive functional is made. -/
theorem spectralValue_eq_measure_integral (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) (hf : 0 ≤ f) :
    d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm (realFunctionHom ψ f), map_nonneg (realFunctionHom ψ) hf⟩ =
      ∫ x, f x ∂(d.spectralMeasure ψ) := by
  let p : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm (realFunctionHom ψ f), map_nonneg (realFunctionHom ψ) hf⟩
  have hi : Integrable f (d.spectralMeasure ψ) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  rw [hi.integral_eq_integral_meas_lt (Filter.Eventually.of_forall hf)]
  simp_rw [d.spectralMeasure_real_lt ψ f hf]
  change d.spectralValue p = ∫ t in Ioi 0, d.distribution p t
  rw [spectralValue, intervalIntegral.integral_of_le (norm_nonneg _)]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
  intro t ht
  apply d.distribution_eq_zero
  have h : ¬t ≤ ‖CStarMatrix.ofMatrix p.matrix‖ := by
    intro hle
    exact ht.2 ⟨ht.1, hle⟩
  exact (lt_of_not_ge h).le

end CuntzDimensionState
end Measures

omit [CompactSpace X] in
/-- All real-valued functions give self-adjoint elements, regardless of sign. -/
theorem continuousRealInclusion_selfAdjoint (f : C(X, ℝ)) :
    IsSelfAdjoint (continuousRealInclusion f) := by
  change star (continuousRealInclusion f) = continuousRealInclusion f
  ext x
  simp

theorem continuousRealInclusion_posPart (f : C(X, ℝ)) :
    (continuousRealInclusion f)⁺ = continuousRealInclusion (continuousDimensionCutoff f 0) := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  ext x
  have hs := continuousRealInclusion_selfAdjoint f
  have hsx : IsSelfAdjoint (continuousRealInclusion f x) := by
    change star (f x : ℂ) = (f x : ℂ)
    simp
  have h := (ContinuousMap.evalStarAlgHom ℂ ℂ x).map_cfc (fun s : ℝ => s⁺)
    (continuousRealInclusion f) (ha := hs) (hφa := hsx)
  change (cfc (fun s : ℝ => s⁺) (continuousRealInclusion f)) x = _
  change (cfc (fun s : ℝ => s⁺) (continuousRealInclusion f)) x = _ at h
  rw [h]
  have he := cfc_algebraMap (A := ℂ) (f x) (fun s : ℝ => s⁺)
  change cfc (fun s : ℝ => s⁺) (f x : ℂ) = ((max (f x-0) 0 : ℝ) : ℂ)
  rw [sub_zero]
  exact he


theorem realFunctionHom_selfAdjoint (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) : IsSelfAdjoint (realFunctionHom ψ f) :=
  (continuousRealInclusion_selfAdjoint f).map ψ

theorem realFunctionHom_posPart (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) :
    (realFunctionHom ψ f)⁺ = realFunctionHom ψ (continuousDimensionCutoff f 0) := by
  change (ψ (continuousRealInclusion f))⁺ = ψ (continuousRealInclusion (continuousDimensionCutoff f 0))
  rw [← continuousRealInclusion_posPart f]
  exact (ψ.toNonUnitalStarAlgHom.map_cfcₙ (fun s : ℝ => s⁺) (continuousRealInclusion f)
    (ha := continuousRealInclusion_selfAdjoint f) (hφa := realFunctionHom_selfAdjoint ψ f)).symm

theorem realFunctionHom_negPart (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) :
    (realFunctionHom ψ f)⁻ = realFunctionHom ψ (continuousDimensionCutoff (-f) 0) := by
  rw [← CFC.posPart_neg, ← map_neg, realFunctionHom_posPart]

section Measures
variable [NormalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
namespace CuntzDimensionState

/-- The canonical signed extension agrees with the same measure on all real
continuous functions, including those of mixed sign. -/
theorem signedValue_eq_measure_integral (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) (f : C(X, ℝ)) :
    d.signedValue (realFunctionHom ψ f) = ∫ x, f x ∂(d.spectralMeasure ψ) := by
  unfold signedValue
  simp only [realFunctionHom_posPart, realFunctionHom_negPart, positiveValue]
  rw [d.spectralValue_eq_measure_integral ψ _ (continuousDimensionCutoff_nonneg f 0),
    d.spectralValue_eq_measure_integral ψ _ (continuousDimensionCutoff_nonneg (-f) 0)]
  rw [← integral_sub
    ((continuousDimensionCutoff f 0).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((continuousDimensionCutoff (-f) 0).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => congrArg (fun g : C(X, ℝ) => g x) (continuousDimensionCutoff_sub f))


/-- The globally fixed complex spectral value agrees with the same finite
measure on EVERY complex continuous function in the representation. -/
theorem complexValue_eq_measure_integral (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) (f : C(X, ℂ)) :
    d.complexValue (ψ f) = ∫ x, f x ∂(d.spectralMeasure ψ) := by
  let fr : C(X, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
  let fi : C(X, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩
  have he : f = continuousRealInclusion fr + Complex.I • continuousRealInclusion fi := by
    ext x
    apply Complex.ext <;> simp [fr, fi]
  have hψ : ψ f = realFunctionHom ψ fr + Complex.I • realFunctionHom ψ fi := by
    conv_lhs => rw [he, map_add, map_smul]
    rfl
  rw [hψ, d.complexValue_real_imag _ _ (realFunctionHom_selfAdjoint ψ fr)
    (realFunctionHom_selfAdjoint ψ fi),
    d.complexValue_selfAdjoint (realFunctionHom_selfAdjoint ψ fr),
    d.complexValue_selfAdjoint (realFunctionHom_selfAdjoint ψ fi),
    d.signedValue_eq_measure_integral ψ fr, d.signedValue_eq_measure_integral ψ fi]
  have hi : Integrable f (d.spectralMeasure ψ) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  rw [mul_comm Complex.I]
  exact integral_re_add_im hi

/-- Complex linearity for the original spectral value composed with a
commutative representation. Agreement is pointwise, ensuring overlap consistency. -/
def complexValueLinearMap (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) : C(X, ℂ) →ₗ[ℂ] ℂ where
  toFun f := d.complexValue (ψ f)
  map_add' f g := by
    rw [d.complexValue_eq_measure_integral ψ (f+g),
      d.complexValue_eq_measure_integral ψ f, d.complexValue_eq_measure_integral ψ g]
    exact integral_add
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))
  map_smul' r f := by
    rw [d.complexValue_eq_measure_integral ψ (r • f), d.complexValue_eq_measure_integral ψ f]
    exact integral_smul r _

end CuntzDimensionState
end Measures
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Quasitrace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Corner-compatible spectral quasitraces and nonunital abelian complex linearity. -/

open scoped Matrix CStarAlgebra ComplexStarModule ComplexOrder

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance] matrixRealFunctionalCalculus matrixNonUnitalRealFunctionalCalculus matrixNonnegSpectrum
variable {A : Type*} [CStarAlgebra A]

namespace CuntzDimensionState

/-- The same spectral construction on the original coefficient algebra. -/
def baseValue (d : CuntzDimensionState A) (a : A) : ℂ :=
  d.complexValue (corner (0 : Fin 1) a)

theorem baseValue_square_nonneg (d : CuntzDimensionState A) (x : A) :
    0 ≤ d.baseValue (star x*x) := by
  simpa only [baseValue, ← corner_mul, ← corner_star] using
    d.complexValue_square_nonneg (corner (0 : Fin 1) x)

theorem baseValue_square_swap (d : CuntzDimensionState A) (x : A) :
    d.baseValue (star x*x) = d.baseValue (x*star x) := by
  simpa only [baseValue, ← corner_mul, ← corner_star] using
    d.complexValue_square_swap (corner (0 : Fin 1) x)

theorem baseValue_real_imag (d : CuntzDimensionState A) (h k : A)
    (hh : IsSelfAdjoint h) (hk : IsSelfAdjoint k) :
    d.baseValue (h+Complex.I • k) = d.baseValue h + Complex.I*d.baseValue k := by
  simpa only [baseValue, corner_add, corner_smul] using d.complexValue_real_imag
    (corner (0 : Fin 1) h) (corner (0 : Fin 1) k)
    (corner_selfAdjoint _ hh) (corner_selfAdjoint _ hk)

/-- A single compatible base/M2 candidate, built from one dimension state.
Only the abelian linearity constraints are still missing. -/
def spectralCandidate (d : CuntzDimensionState A) : QuasitraceCandidate A :=
  (d.baseValue, d.complexValue)

def oneQuasitraceOfSpectralCandidate (d : CuntzDimensionState A)
    (hlin : ∀ S : NonUnitalStarSubalgebra ℂ A, IsClosed (S : Set A) →
      (∀ x y : S, x*y=y*x) → ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.baseValue x) :
    OneQuasitrace A where
  toFun := d.baseValue
  square_nonneg := d.baseValue_square_nonneg
  square_swap := d.baseValue_square_swap
  real_imag := d.baseValue_real_imag
  abelian_linear := hlin

/-- Gelfand duality transfers the proved integral linearity to any unital
commutative C*-algebra represented in a finite matrix algebra over A. -/
def commutativeValueLinearMap (d : CuntzDimensionState A)
    {B : Type*} [CommCStarAlgebra B] {n : ℕ}
    (φ : B →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) : B →ₗ[ℂ] ℂ := by
  letI := borel (WeakDual.characterSpace ℂ B)
  letI : BorelSpace (WeakDual.characterSpace ℂ B) := ⟨rfl⟩
  let ψ := φ.comp (gelfandStarTransform B).symm.toStarAlgHom
  exact (d.complexValueLinearMap ψ).comp (gelfandStarTransform B).toAlgEquiv.toLinearEquiv.toLinearMap

@[simp] theorem commutativeValueLinearMap_apply (d : CuntzDimensionState A)
    {B : Type*} [CommCStarAlgebra B] {n : ℕ}
    (φ : B →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) (b : B) :
    d.commutativeValueLinearMap φ b = d.complexValue (φ b) := by
  change d.complexValue (φ ((gelfandStarTransform B).symm ((gelfandStarTransform B) b))) = _
  rw [StarAlgEquiv.symm_apply_apply]

def nonunitalCommutativeValueLinearMap (d : CuntzDimensionState A)
    {B : Type*} [NonUnitalCommCStarAlgebra B] {n : ℕ}
    (φ : B →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) : B →ₗ[ℂ] ℂ :=
  (d.commutativeValueLinearMap (Unitization.starLift φ)).comp
    (Unitization.inrHom ℂ ℂ B)

@[simp] theorem nonunitalCommutativeValueLinearMap_apply (d : CuntzDimensionState A)
    {B : Type*} [NonUnitalCommCStarAlgebra B] {n : ℕ}
    (φ : B →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) (b : B) :
    d.nonunitalCommutativeValueLinearMap φ b = d.complexValue (φ b) := by
  have he : (Unitization.starLift φ) (b : Unitization ℂ B) = φ b :=
    congrArg (fun ψ : B →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A => ψ b)
      (Equiv.symm_apply_apply Unitization.starLift φ)
  have hc := d.commutativeValueLinearMap_apply (Unitization.starLift φ)
    (b : Unitization ℂ B)
  exact hc.trans (congrArg d.complexValue he)

/-- The exact abelian-linearity axiom for the fixed matrix spectral candidate. -/
theorem complexValue_abelian_linear (d : CuntzDimensionState A) (n : ℕ)
    (S : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin n) (Fin n) A))
    (hS : IsClosed (S : Set (CStarMatrix (Fin n) (Fin n) A)))
    (hcomm : ∀ x y : S, x*y=y*x) :
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.complexValue (x : CStarMatrix (Fin n) (Fin n) A) := by
  let : IsClosed (S : Set (CStarMatrix (Fin n) (Fin n) A)) := hS
  let : NonUnitalCommCStarAlgebra S := { (inferInstance : NonUnitalCStarAlgebra S) with mul_comm := hcomm }
  exact ⟨d.nonunitalCommutativeValueLinearMap (NonUnitalStarSubalgebraClass.subtype S),
    fun x => d.nonunitalCommutativeValueLinearMap_apply _ x⟩

end CuntzDimensionState
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_ProjectivePuncture
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.projectiveGrassmannT2 _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Punctures, collapse, and hyperplane retraction in projective space. -/

section
open Set Topology
namespace ComplexGrassmann

section
variable {k l : ℕ}

/-- The actual image line, when the linear map is injective on that line. -/
def projectiveLinearImage (L : Components 1 k →L[ℂ] Components 1 l)
    (P : Grassmann 1 k) (h : Function.Injective (L.toLinearMap.comp P.val.subtype)) :
    Grassmann 1 l :=
  ⟨P.val.map L.toLinearMap, by
    rw [← Submodule.range_subtype P.val, ← LinearMap.range_comp,
      LinearMap.finrank_range_of_inj h]
    exact P.property⟩

/-- A continuously varying independent frame for a graph-chart line. -/
def graphLineFrame (F : GraphFrame 1 k) (A : GraphSlope 1 k) : PlaneFrameMap 1 k :=
  F.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℂ _).prod A)

theorem graphLineFrame_injective (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    Function.Injective (graphLineFrame F A) := by
  intro x y h
  exact congrArg Prod.fst (F.symm.injective h)

theorem graphLineFrame_point (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    framePoint ⟨graphLineFrame F A, graphLineFrame_injective F A⟩ = slopePoint F A := by
  apply Subtype.ext
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change (F (F.symm (x, A x))).2 = A (F (F.symm (x, A x))).1
    simp
  · intro hz
    refine ⟨(F z).1, ?_⟩
    change F.symm ((F z).1, A (F z).1) = z
    apply F.injective
    simp only [LinearEquiv.apply_symm_apply]
    exact Prod.ext rfl hz.symm

theorem continuous_graphLineFrame (F : GraphFrame 1 k) : Continuous (graphLineFrame F) := by
  apply continuous_clm_apply.mpr
  intro v
  exact F.symm.toContinuousLinearEquiv.continuous.comp
    (continuous_const.prodMk (continuous_id.clm_apply continuous_const))

/-- Linear images vary continuously even if the ambient map is singular;
only injectivity on the input line is needed. -/
theorem continuous_projectiveLinearImage {X : Type*} [TopologicalSpace X]
    (L : X → Components 1 k →L[ℂ] Components 1 l) (P : X → Grassmann 1 k)
    (h : ∀ x, Function.Injective ((L x).toLinearMap.comp (P x).val.subtype))
    (hL : Continuous L) (hP : Continuous P) :
    Continuous (fun x => projectiveLinearImage (L x) (P x) (h x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨F, hF⟩ := grassmann_atlas_covers (P x)
  let U := P ⁻¹' (grassmannChart F).source
  have hU : IsOpen U := (grassmannChart F).open_source.preimage hP
  have hc : Continuous (fun y : U => slopeCoordinate F (P y.val)) :=
    (grassmannChart F).continuousOn.comp_continuous
      (hP.comp continuous_subtype_val) (fun y => y.property)
  let B : U → PlaneFrameMap 1 l := fun y =>
    (L y.val).comp (graphLineFrame F (slopeCoordinate F (P y.val)))
  have hB : ∀ y, Function.Injective (B y) := by
    intro y u v huv
    have hg := graphLineFrame_point F (slopeCoordinate F (P y.val))
    rw [slopePoint_coordinate F (P y.val) y.property] at hg
    have hm (w) : graphLineFrame F (slopeCoordinate F (P y.val)) w ∈ (P y.val).val := by
      have he := congrArg Subtype.val hg
      exact he ▸ (show graphLineFrame F (slopeCoordinate F (P y.val)) w ∈
        LinearMap.range (graphLineFrame F (slopeCoordinate F (P y.val))).toLinearMap from ⟨w, rfl⟩)
    have he := h y.val (a₁ := ⟨_, hm u⟩) (a₂ := ⟨_, hm v⟩) huv
    exact graphLineFrame_injective F _ (congrArg Subtype.val he)
  have he (y : U) : framePoint ⟨B y, hB y⟩ =
      projectiveLinearImage (L y.val) (P y.val) (h y.val) := by
    apply Subtype.ext
    change LinearMap.range ((L y.val).toLinearMap.comp
      (graphLineFrame F (slopeCoordinate F (P y.val))).toLinearMap) = _
    rw [LinearMap.range_comp]
    have hg := congrArg Subtype.val (graphLineFrame_point F (slopeCoordinate F (P y.val)))
    rw [slopePoint_coordinate F (P y.val) y.property] at hg
    exact congrArg (Submodule.map (L y.val).toLinearMap) hg
  have hb : Continuous B := (hL.comp continuous_subtype_val).clm_comp
    ((continuous_graphLineFrame F).comp hc)
  have hi : Continuous (fun y : U => projectiveLinearImage (L y.val) (P y.val) (h y.val)) :=
    (framePoint_continuous.comp (hb.subtype_mk hB)).congr he
  exact ((continuousOn_iff_continuous_domRestrict.mpr hi) x hF).continuousAt
    (hU.mem_nhds hF)

end

variable {k : ℕ}

/-- Projection along the removed line is injective on every other line. -/
theorem verticalProjection_injective_iff (F : GraphFrame 1 k) (P : Grassmann 1 k) :
    Function.Injective (fun z : P.val => (F z.val).2) ↔ P ≠ graphPoint F 0 := by
  constructor
  · intro hi he
    subst P
    let x : GraphHorizontal 1 := fun _ => 1
    have h := hi (a₁ := graphPlaneEquiv F 0 x) (a₂ := 0) (by
      simp [graphPlaneEquiv, graphPoint])
    have hx0 : x = 0 := (graphPlaneEquiv F 0).injective
      (h.trans (graphPlaneEquiv F 0).map_zero.symm)
    have hx1 := congrFun hx0 0
    simp [x] at hx1
  · intro hne
    let L := (LinearMap.snd ℂ (GraphHorizontal 1) (GraphVertical k)).comp
      (F.toLinearMap.comp P.val.subtype)
    change Function.Injective L
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro z hz
    apply Subtype.ext
    change z.val = 0
    by_contra hz0
    have hv : (F z.val).2 = 0 := hz
    have hm : z.val ∈ graphPlane F 0 := by simpa using hv
    have hp := eq_span_singleton_of_mem_of_finrank_eq_one P.property z.property hz0
    have hq := eq_span_singleton_of_mem_of_finrank_eq_one (graphPlane_finrank F 0) hm hz0
    exact hne (Subtype.ext (hp.trans hq.symm))

/-- Scale the removed-line coordinate and leave the complementary coordinates fixed. -/
def punctureCollapseLinear (F : GraphFrame 1 k) (c : ℂ) :
    Components 1 k →L[ℂ] Components 1 k :=
  F.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((c • ContinuousLinearMap.fst ℂ (GraphHorizontal 1) (GraphVertical k)).prod
      (ContinuousLinearMap.snd ℂ (GraphHorizontal 1) (GraphVertical k))).comp
      F.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem punctureCollapseLinear_coordinates (F : GraphFrame 1 k) (c : ℂ)
    (v : Components 1 k) :
    F (punctureCollapseLinear F c v) = (c • (F v).1, (F v).2) :=
  F.apply_symm_apply _

theorem continuous_punctureCollapseLinear (F : GraphFrame 1 k) :
    Continuous (punctureCollapseLinear F) := by
  apply continuous_clm_apply.mpr
  intro v
  exact F.symm.toContinuousLinearEquiv.continuous.comp
    ((continuous_id.smul continuous_const).prodMk continuous_const)

theorem punctureCollapseLinear_injective (F : GraphFrame 1 k) (c : ℂ)
    (P : Grassmann 1 k) (hP : P ≠ graphPoint F 0) :
    Function.Injective ((punctureCollapseLinear F c).toLinearMap.comp P.val.subtype) := by
  intro x y h
  apply (verticalProjection_injective_iff F P).mpr hP
  have he := congrArg (fun z => (F z).2) h
  simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    Submodule.subtype_apply, punctureCollapseLinear_coordinates] using he

/-- Collapse within the punctured projective space, including at c=0. -/
def punctureCollapse (F : GraphFrame 1 k) (c : ℂ)
    (P : ({graphPoint F 0}ᶜ : Set (Grassmann 1 k))) : Grassmann 1 k :=
  projectiveLinearImage (punctureCollapseLinear F c) P.val
    (punctureCollapseLinear_injective F c P.val P.property)

theorem punctureCollapse_ne_center (F : GraphFrame 1 k) (c : ℂ)
    (P : ({graphPoint F 0}ᶜ : Set (Grassmann 1 k))) :
    punctureCollapse F c P ≠ graphPoint F 0 := by
  apply (verticalProjection_injective_iff F _).mp
  intro x y h
  obtain ⟨u, hu, hux⟩ := x.property
  obtain ⟨v, hv, hvy⟩ := y.property
  apply Subtype.ext
  have he : (F u).2 = (F v).2 := by
    change (F x.val).2 = (F y.val).2 at h
    rw [← hux, ← hvy] at h
    simpa only [ContinuousLinearMap.coe_coe, punctureCollapseLinear_coordinates] using h
  have huv := (verticalProjection_injective_iff F P.val).mpr P.property
    (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) he
  exact hux.symm.trans ((congrArg (punctureCollapseLinear F c)
    (congrArg Subtype.val huv)).trans hvy)

theorem continuous_punctureCollapse (F : GraphFrame 1 k) :
    Continuous (fun z : ℂ × ({graphPoint F 0}ᶜ : Set (Grassmann 1 k)) =>
      punctureCollapse F z.1 z.2) :=
  continuous_projectiveLinearImage _ _ _
    ((continuous_punctureCollapseLinear F).comp continuous_fst)
    (continuous_subtype_val.comp continuous_snd)

theorem punctureCollapse_one (F : GraphFrame 1 k)
    (P : ({graphPoint F 0}ᶜ : Set (Grassmann 1 k))) : punctureCollapse F 1 P = P.val := by
  apply Subtype.ext
  have hL : (punctureCollapseLinear F 1).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro z
    apply F.injective
    simp
  change P.val.val.map (punctureCollapseLinear F 1).toLinearMap = P.val.val
  rw [hL, Submodule.map_id]

/-- The endpoint lies entirely in the complementary projective hyperplane. -/
theorem punctureCollapse_zero_horizontal (F : GraphFrame 1 k)
    (P : ({graphPoint F 0}ᶜ : Set (Grassmann 1 k)))
    (z : (punctureCollapse F 0 P).val) : (F z.val).1 = 0 := by
  obtain ⟨u, hu, huz⟩ := z.property
  rw [← huz]
  simp

/-- Every point already in the complementary hyperplane stays fixed. -/
theorem punctureCollapse_fixed (F : GraphFrame 1 k) (c : ℂ)
    (P : ({graphPoint F 0}ᶜ : Set (Grassmann 1 k)))
    (hP : ∀ z : P.val.val, (F z.val).1 = 0) : punctureCollapse F c P = P.val := by
  apply Subtype.ext
  have he (u : P.val.val) : punctureCollapseLinear F c u.val = u.val := by
    apply F.injective
    rw [punctureCollapseLinear_coordinates]
    exact Prod.ext (by simp [hP u]) rfl
  change P.val.val.map (punctureCollapseLinear F c).toLinearMap = P.val.val
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    change punctureCollapseLinear F c u ∈ P.val.val
    rw [he ⟨u, hu⟩]
    exact hu
  · intro hz
    exact ⟨z, hz, he ⟨z, hz⟩⟩

end ComplexGrassmann

end

section
open Set Topology ContinuousMap
namespace ComplexGrassmann
variable {k : ℕ}

abbrev ProjectivePuncture (F : GraphFrame 1 k) :=
  ({graphPoint F 0}ᶜ : Set (Grassmann 1 k))

/-- The actual complementary projective hyperplane, as a subspace of the puncture. -/
def PunctureHyperplane (F : GraphFrame 1 k) :=
  {P : ProjectivePuncture F // ∀ z : P.val.val, (F z.val).1 = 0}

instance instTopologicalSpacePunctureHyperplane (F : GraphFrame 1 k) : TopologicalSpace (PunctureHyperplane F) :=
  inferInstanceAs (TopologicalSpace {P : ProjectivePuncture F //
    ∀ z : P.val.val, (F z.val).1 = 0})

def punctureHyperplaneInclusion (F : GraphFrame 1 k) :
    C(PunctureHyperplane F, ProjectivePuncture F) := ⟨Subtype.val, continuous_subtype_val⟩

def punctureHyperplaneRetraction (F : GraphFrame 1 k) :
    C(ProjectivePuncture F, PunctureHyperplane F) where
  toFun P := ⟨⟨punctureCollapse F 0 P, punctureCollapse_ne_center F 0 P⟩,
    punctureCollapse_zero_horizontal F P⟩
  continuous_toFun := ((continuous_punctureCollapse F).comp
    (continuous_const.prodMk continuous_id)).subtype_mk _ |>.subtype_mk _

theorem punctureHyperplaneRetraction_inclusion (F : GraphFrame 1 k)
    (P : PunctureHyperplane F) :
    punctureHyperplaneRetraction F (punctureHyperplaneInclusion F P) = P := by
  apply Subtype.ext
  apply Subtype.ext
  exact punctureCollapse_fixed F 0 P.val P.property

/-- The deformation scales [a:v] to [(1-t)a:v]; it stays outside the
removed point and fixes the entire complementary hyperplane. -/
def punctureDeformation (F : GraphFrame 1 k) :
    (ContinuousMap.id (ProjectivePuncture F)).Homotopy
      ((punctureHyperplaneInclusion F).comp (punctureHyperplaneRetraction F)) where
  toFun z := ⟨punctureCollapse F (1 - (z.1.val : ℂ)) z.2,
    punctureCollapse_ne_center F _ z.2⟩
  continuous_toFun := ((continuous_punctureCollapse F).comp
    ((continuous_const.sub (Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd)).subtype_mk _
  map_zero_left P := by
    apply Subtype.ext
    change punctureCollapse F (1 - ((0 : ℝ) : ℂ)) P = P.val
    simpa using punctureCollapse_one F P
  map_one_left P := by
    apply Subtype.ext
    change punctureCollapse F (1 - ((1 : ℝ) : ℂ)) P = punctureCollapse F 0 P
    simp

/-- A proved homotopy equivalence, not a deformation-retraction premise. -/
def punctureHyperplaneHomotopyEquiv (F : GraphFrame 1 k) :
    ProjectivePuncture F ≃ₕ PunctureHyperplane F where
  toFun := punctureHyperplaneRetraction F
  invFun := punctureHyperplaneInclusion F
  left_inv := ⟨(punctureDeformation F).symm⟩
  right_inv := by
    have he : (punctureHyperplaneRetraction F).comp (punctureHyperplaneInclusion F) =
        ContinuousMap.id _ := ContinuousMap.ext (punctureHyperplaneRetraction_inclusion F)
    rw [he]

end ComplexGrassmann

end

open Set Topology ContinuousMap
namespace ComplexGrassmann
variable {k : ℕ}

def verticalAmbientEquiv (k : ℕ) : Components 1 k ≃L[ℂ] GraphVertical (k+1) :=
  (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (k+1) => ℂ)
    (finCongr (Nat.add_comm 1 k))).toContinuousLinearEquiv

def hyperplaneEmbedLinear (F : GraphFrame 1 (k+1)) :
    Components 1 k →L[ℂ] Components 1 (k+1) :=
  F.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((0 : Components 1 k →L[ℂ] GraphHorizontal 1).prod
      (verticalAmbientEquiv k).toContinuousLinearMap)

def hyperplaneProjectLinear (F : GraphFrame 1 (k+1)) :
    Components 1 (k+1) →L[ℂ] Components 1 k :=
  (verticalAmbientEquiv k).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.snd ℂ (GraphHorizontal 1) (GraphVertical (k+1))).comp
      F.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem hyperplaneEmbedLinear_coordinates (F : GraphFrame 1 (k+1))
    (v : Components 1 k) : F (hyperplaneEmbedLinear F v) = (0, verticalAmbientEquiv k v) :=
  F.apply_symm_apply _

@[simp] theorem hyperplaneProjectLinear_embed (F : GraphFrame 1 (k+1))
    (v : Components 1 k) : hyperplaneProjectLinear F (hyperplaneEmbedLinear F v) = v := by
  change (verticalAmbientEquiv k).symm (F (hyperplaneEmbedLinear F v)).2 = v
  simp

theorem hyperplaneEmbedLinear_project (F : GraphFrame 1 (k+1))
    (v : Components 1 (k+1)) (hv : (F v).1 = 0) :
    hyperplaneEmbedLinear F (hyperplaneProjectLinear F v) = v := by
  apply F.injective
  rw [hyperplaneEmbedLinear_coordinates]
  change (0, verticalAmbientEquiv k ((verticalAmbientEquiv k).symm (F v).2)) = F v
  exact Prod.ext hv.symm ((verticalAmbientEquiv k).apply_symm_apply _)

theorem hyperplaneEmbedLinear_injective (F : GraphFrame 1 (k+1)) :
    Function.Injective (hyperplaneEmbedLinear F) :=
  Function.LeftInverse.injective (hyperplaneProjectLinear_embed F)

def hyperplaneEmbedPoint (F : GraphFrame 1 (k+1)) (P : Grassmann 1 k) :
    Grassmann 1 (k+1) :=
  projectiveLinearImage (hyperplaneEmbedLinear F) P
    ((hyperplaneEmbedLinear_injective F).comp Subtype.val_injective)

theorem hyperplaneEmbedPoint_ne_center (F : GraphFrame 1 (k+1)) (P : Grassmann 1 k) :
    hyperplaneEmbedPoint F P ≠ graphPoint F 0 := by
  apply (verticalProjection_injective_iff F _).mp
  intro x y h
  obtain ⟨u, hu, hux⟩ := x.property
  obtain ⟨v, hv, hvy⟩ := y.property
  apply Subtype.ext
  change (F x.val).2 = (F y.val).2 at h
  rw [← hux, ← hvy] at h
  have huv : u = v := (verticalAmbientEquiv k).injective (by
    simpa only [ContinuousLinearMap.coe_coe, hyperplaneEmbedLinear_coordinates] using h)
  exact hux.symm.trans ((congrArg (hyperplaneEmbedLinear F) huv).trans hvy)

theorem hyperplaneEmbedPoint_horizontal (F : GraphFrame 1 (k+1)) (P : Grassmann 1 k)
    (z : (hyperplaneEmbedPoint F P).val) : (F z.val).1 = 0 := by
  obtain ⟨u, hu, huz⟩ := z.property
  rw [← huz]
  exact congrArg Prod.fst (hyperplaneEmbedLinear_coordinates F u)

def hyperplaneEmbed (F : GraphFrame 1 (k+1)) :
    C(Grassmann 1 k, PunctureHyperplane F) where
  toFun P := ⟨⟨hyperplaneEmbedPoint F P, hyperplaneEmbedPoint_ne_center F P⟩,
    hyperplaneEmbedPoint_horizontal F P⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_projectiveLinearImage (fun _ => hyperplaneEmbedLinear F)
      (fun P : Grassmann 1 k => P) _ continuous_const continuous_id

theorem hyperplaneProjectLinear_injective (F : GraphFrame 1 (k+1))
    (P : PunctureHyperplane F) :
    Function.Injective ((hyperplaneProjectLinear F).toLinearMap.comp P.val.val.val.subtype) := by
  intro x y h
  apply (verticalProjection_injective_iff F P.val.val).mpr P.val.property
  exact (verticalAmbientEquiv k).symm.injective h

def hyperplaneProject (F : GraphFrame 1 (k+1)) :
    C(PunctureHyperplane F, Grassmann 1 k) where
  toFun P := projectiveLinearImage (hyperplaneProjectLinear F) P.val.val
    (hyperplaneProjectLinear_injective F P)
  continuous_toFun := continuous_projectiveLinearImage _ _ _ continuous_const
    (continuous_subtype_val.comp continuous_subtype_val)

theorem hyperplaneProject_embed (F : GraphFrame 1 (k+1)) (P : Grassmann 1 k) :
    hyperplaneProject F (hyperplaneEmbed F P) = P := by
  apply Subtype.ext
  change (P.val.map (hyperplaneEmbedLinear F).toLinearMap).map
    (hyperplaneProjectLinear F).toLinearMap = P.val
  rw [← Submodule.map_comp]
  have he : (hyperplaneProjectLinear F).toLinearMap.comp
      (hyperplaneEmbedLinear F).toLinearMap = LinearMap.id :=
    LinearMap.ext (hyperplaneProjectLinear_embed F)
  rw [he, Submodule.map_id]

theorem hyperplaneEmbed_project (F : GraphFrame 1 (k+1)) (P : PunctureHyperplane F) :
    hyperplaneEmbed F (hyperplaneProject F P) = P := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change (P.val.val.val.map (hyperplaneProjectLinear F).toLinearMap).map
    (hyperplaneEmbedLinear F).toLinearMap = P.val.val.val
  rw [← Submodule.map_comp]
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    change hyperplaneEmbedLinear F (hyperplaneProjectLinear F v) ∈ P.val.val.val
    rw [hyperplaneEmbedLinear_project F v (P.property ⟨v, hv⟩)]
    exact hv
  · intro hz
    exact ⟨z, hz, hyperplaneEmbedLinear_project F z (P.property ⟨z, hz⟩)⟩

/-- The complementary hyperplane carries exactly the topology of CP^k. -/
def projectiveHyperplaneHomeomorph (F : GraphFrame 1 (k+1)) :
    PunctureHyperplane F ≃ₜ Grassmann 1 k where
  toFun := hyperplaneProject F
  invFun := hyperplaneEmbed F
  left_inv := hyperplaneEmbed_project F
  right_inv := hyperplaneProject_embed F
  continuous_toFun := (hyperplaneProject F).continuous
  continuous_invFun := (hyperplaneEmbed F).continuous

/-- CP^(k+1) minus a chart center is homotopy equivalent to CP^k. -/
def projectivePunctureLowerHomotopyEquiv (F : GraphFrame 1 (k+1)) :
    ProjectivePuncture F ≃ₕ Grassmann 1 k :=
  (punctureHyperplaneHomotopyEquiv F).trans (projectiveHyperplaneHomeomorph F).toHomotopyEquiv

/-- The puncture retraction theorem holds at any actual projective point. -/
def projectivePointPunctureLowerHomotopyEquiv (P : Grassmann 1 (k+1)) :
    ({P}ᶜ : Set (Grassmann 1 (k+1))) ≃ₕ Grassmann 1 k := by
  let F := (graph_charts_cover P.val P.property).choose
  have hF := (graph_charts_cover P.val P.property).choose_spec
  have hp : graphPoint F 0 = P := Subtype.ext hF
  exact (Homeomorph.setCongr (congrArg (fun Q => ({Q}ᶜ : Set (Grassmann 1 (k+1)))) hp.symm)).toHomotopyEquiv.trans
    (projectivePunctureLowerHomotopyEquiv F)

end ComplexGrassmann

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_ProjectiveLocal
attribute [-instance] _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Nonzero local classes and local homology of projective spaces and products. -/

section
open Set
namespace ComplexGrassmann

instance grassmannZero_subsingleton : Subsingleton (Grassmann 1 0) := by
  constructor
  intro P Q
  apply Subtype.ext
  have hp : P.val = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using P.property)
  have hq : Q.val = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using Q.property)
  exact hp.trans hq.symm

end ComplexGrassmann

end

open CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_ProjectiveClass
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Localization, top homology, and the fundamental class of projective products. -/

section
open Set Topology ContinuousMap
namespace ComplexGrassmann
variable {ι : Type} (K : ι → ℕ)

/-- The coordinate puncture is open in the actual compact projective product. -/
def projectiveCoordinatePuncture (P : ProjectiveProduct K) (i : ι) : Set (ProjectiveProduct K) :=
  {Q | Q i ≠ P i}

theorem projectiveCoordinatePuncture_open (P : ProjectiveProduct K) (i : ι) :
    IsOpen (projectiveCoordinatePuncture K P i) :=
  isClosed_singleton.isOpen_compl.preimage (continuous_apply i)

variable [Fintype ι]

theorem coordinatePunctureDimensions_sum (T : Finset ι) (hT : ∀ i ∈ T, 0 < K i) :
    (∑ i, coordinatePunctureDimensions K T i) + T.card = ∑ i, K i := by
  classical
  have he : ∑ i, (coordinatePunctureDimensions K T i + if i ∈ T then 1 else 0) = ∑ i, K i := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ T
    · have := hT i hi
      simp only [coordinatePunctureDimensions, ite_eq_left hi]
      omega
    · simp [coordinatePunctureDimensions, hi]
  have hcount : (∑ i, if i ∈ T then 1 else 0 : ℕ) = T.card := by
    rw [Finset.sum_boole]
    have hf : Finset.univ.filter (fun i => i ∈ T) = T := by ext i; simp
    simp only [hf, Nat.cast_id]
  rwa [Finset.sum_add_distrib, hcount] at he

/-- Positive-dimensional coordinate punctures cover the complement of any point. -/
theorem projectiveCoordinatePunctures_cover (P : ProjectiveProduct K) :
    (⋃ i ∈ Finset.univ.filter (fun i => 0 < K i), projectiveCoordinatePuncture K P i) = {P}ᶜ := by
  classical
  ext Q
  simp only [mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    projectiveCoordinatePuncture, mem_ofPred_eq, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, hne⟩ he
    exact hne (congrFun he i)
  · intro hne
    have hd : ∃ i, Q i ≠ P i := by
      by_contra h
      push Not at h
      exact hne (funext h)
    obtain ⟨i, hi⟩ := hd
    refine ⟨i, ?_, hi⟩
    by_contra hk
    have hz : K i = 0 := by omega
    have hs : Subsingleton (Grassmann 1 (K i)) := by rw [hz]; infer_instance
    exact hi (hs.elim _ _)

end ComplexGrassmann

end

open CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_GraphCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Projective graph denominators, intersections, and finite graph covers. -/

section
open Set
namespace ComplexGrassmann

theorem horizontalOne_eq_smul (v : GraphHorizontal 1) :
    v = v 0 • (fun _ => (1 : ℂ)) := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simp [hi]

/-- An actual complex endomorphism of a one-dimensional horizontal
space is invertible exactly when its scalar coefficient is nonzero. -/
theorem horizontalOne_isUnit_iff (L : GraphHorizontal 1 →L[ℂ] GraphHorizontal 1) :
    IsUnit L ↔ L (fun _ => 1) 0 ≠ 0 := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have happ (v : GraphHorizontal 1) (i : Fin 1) :
      L v i = v 0 * L (fun _ => 1) 0 := by
    have h := congrArg (fun v : GraphHorizontal 1 => L v i) (horizontalOne_eq_smul v)
    rw [map_smul] at h
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using h
  constructor
  · intro h hz
    have he : L (fun _ => 1) = L 0 := by
      ext i
      rw [happ, hz]
      simp
    have he' := congrFun (h.1 he) 0
    exact one_ne_zero he'
  · intro hz
    constructor
    · intro v w h
      have he := congrFun h 0
      rw [happ v 0, happ w 0] at he
      have he' := mul_right_cancel₀ hz he
      rw [horizontalOne_eq_smul v, horizontalOne_eq_smul w, he']
    · intro w
      refine ⟨fun _ => w 0 / L (fun _ => 1) 0, ?_⟩
      ext i
      rw [happ, div_mul_cancel₀ _ hz]
      exact congrArg w (Subsingleton.elim _ _)

variable {k : ℕ}

/-- The variable part of the graph-overlap denominator. -/
def graphDenominatorLinear (F G : GraphFrame 1 k) : GraphSlope 1 k →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A => (G (F.symm (0,A (fun _ => 1)))).1 0
    map_add' := by
      intro A B
      have h : ((0 : GraphHorizontal 1),(A+B) (fun _ => 1)) =
          (0,A (fun _ => 1)) + (0,B (fun _ => 1)) := by ext <;> simp
      rw [h, map_add, map_add]
      rfl
    map_smul' := by
      intro c A
      have h : ((0 : GraphHorizontal 1),(c • A) (fun _ => 1)) =
          c • (0,A (fun _ => 1)) := by ext <;> simp
      rw [h, map_smul, map_smul]
      rfl }

def graphDenominatorConstant (F G : GraphFrame 1 k) : ℂ :=
  (G (F.symm ((fun _ => 1),0))).1 0

theorem graphDenominator_eq (F G : GraphFrame 1 k) (A : GraphSlope 1 k) :
    graphTop F G A (fun _ => 1) 0 =
      graphDenominatorLinear F G A + graphDenominatorConstant F G := by
  rw [graphTop_apply]
  have h : ((fun _ : Fin 1 => (1 : ℂ)),A (fun _ => 1)) =
      (0,A (fun _ => 1)) + ((fun _ => 1),0) := by ext <;> simp
  rw [h, map_add, map_add]
  rfl

/-- The actual projective overlap is precisely the complement of an
affine scalar zero set, for arbitrary complex graph frames. -/
theorem projective_inGraphChart_iff_denominator (F G : GraphFrame 1 k) (A : GraphSlope 1 k) :
    InGraphChart G (slopePoint F A).val ↔
      graphDenominatorLinear F G A + graphDenominatorConstant F G ≠ 0 := by
  change InGraphChart G (graphPlane F A.toLinearMap) ↔ _
  rw [inGraphChart_iff_unit, horizontalOne_isUnit_iff, graphDenominator_eq]

end ComplexGrassmann

end

section
open Set Topology
namespace ComplexGrassmann
variable {ι J : Type} [Fintype ι] [Fintype J] (K : ι → ℕ)

def productGraphDenominatorConstant (F : ∀ i, GraphFrame 1 (K i))
    (G : J → ∀ i, GraphFrame 1 (K i)) (ji : J × ι) : ℂ :=
  graphDenominatorConstant (F ji.2) (G ji.1 ji.2)

end ComplexGrassmann

end

open Set

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Shift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert shifts, their relations, and block operator bounds. -/

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)]

theorem successor_orthogonal : OrthogonalFamily ℂ (fun j => E (j+1))
    (fun j => levelInclusion (j+1)) := by
  intro i j hij v w
  change inner ℂ (lp.single 2 (i+1) v) (lp.single 2 (j+1) w) = 0
  rw [lp.inner_single_left]
  simp [Pi.single_eq_of_ne (show i+1 ≠ j+1 by omega)]

variable [∀ j, CompleteSpace (E j)]

/-- Isometric insertion of a zero level at the start of the sum. -/
def successorInclusion : lp (fun j => E (j+1)) 2 →ₗᵢ[ℂ] FiberHilbertSum E :=
  successor_orthogonal.linearIsometry

def forwardShift (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1) :
    FiberHilbertSum E →L[ℂ] FiberHilbertSum E :=
  successorInclusion.toContinuousLinearMap.comp (lp.mapCLM 2 T zero_le_one hT)

theorem forwardShift_norm_le (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1) :
    ‖forwardShift T hT‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖successorInclusion (lp.mapCLM 2 T zero_le_one hT f)‖ ≤ 1 * ‖f‖
  rw [successorInclusion.norm_map]
  exact (lp.mapCLM 2 T zero_le_one hT).le_of_opNorm_le (lp.norm_mapCLM_le ..) f

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Words
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word propagation through Hilbert shifts and normalized tuple operators. -/

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky.NormalizedHermitianTuple
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

local instance instCompleteSpace_r6cdab6_1 : CompleteSpace E := FiniteDimensional.complete ℂ E
attribute [local instance] OAI.Kaplansky.NormalizedHermitianTuple.instCompleteSpace_1
theorem operator_adjoint (T : NormalizedHermitianTuple E F) (i : Fin 24) :
    (T.operator i).adjoint = (T.reverse i).toContinuousLinearMap := by
  ext w
  apply ext_inner_right ℂ
  intro v
  exact (ContinuousLinearMap.adjoint_inner_left (T.operator i) v w).trans (T.adjoint_inner i v w).symm

theorem operator_column (T : NormalizedHermitianTuple E F) :
    ∑ i, (T.operator i).adjoint.comp (T.operator i) = ContinuousLinearMap.id ℂ E := by
  simp_rw [operator_adjoint]
  ext v
  exact congrArg (fun a : E →ₗ[ℂ] E => a v) T.column

theorem operator_norm_le (T : NormalizedHermitianTuple E F) (i : Fin 24) : ‖T.operator i‖ ≤ 1 :=
  Kaplansky.block_norm_le_of_column T.operator T.operator_column i

end Kaplansky.NormalizedHermitianTuple

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_BundleWords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Continuous bundle words and their finite-tower Hilbert realization. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ}

section WordValues

namespace BundleWordValue
variable {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))

def identity : BundleWordValue a := ⟨0,fun _ => LinearMap.id,continuous_id⟩

end BundleWordValue

end WordValues

open scoped BigOperators

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Products
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded C-star products and the generated separable unital algebra. -/

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

instance boundedProductCStarAlgebra : CStarAlgebra (BoundedProduct A) where

def boundedProductLift (x : ∀ i, A i) (hx : ∀ i, ‖x i‖ ≤ 1) : BoundedProduct A :=
  ⟨x, memℓp_infty ⟨1, by rintro _ ⟨i,rfl⟩; exact hx i⟩⟩

omit [∀ i, Nontrivial (A i)] in
@[simp] theorem boundedProductLift_apply (x : ∀ i, A i) (hx : ∀ i, ‖x i‖ ≤ 1) (i : I) :
    boundedProductLift x hx i = x i := rfl

def boundedProductEval (i : I) : BoundedProduct A →+ A i where
  toFun f := f i
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem boundedProduct_sum_apply {N : ℕ} (f : Fin N → BoundedProduct A) (i : I) :
    (∑ k, f k) i = ∑ k, f k i :=
  map_sum (boundedProductEval i) f Finset.univ

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_BundlePolynomials
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Bundle matrix polynomial evaluation, Hilbert isometries, and polynomial action. -/

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann

variable {ι : Type*} {K : ι → ℕ}

variable {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))

abbrev MatrixTowerHilbert (a : ℕ → LineStage K) (n : ℕ) (y : ProjectiveProduct K) :=
  PiLp 2 (fun _ : Fin n => lp (fun j => (a j).Fiber y) 2)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_TestAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete test operators, their C-star algebra, and its faithful representation. -/

open Bundle Topology
open scoped BigOperators ComplexOrder
namespace Kaplansky
open ComplexGrassmann

instance actualTestFiber_zero_nontrivial (z : ActualTestIndex) : Nontrivial (ActualTestFiber z 0) := by
  change Nontrivial (EuclideanSpace ℂ (testSequenceStage z.1.val z.2.1.val 0).Slot)
  rw [testSequenceStage_prefix (Nat.zero_le _)]
  let : Nonempty (TestBundleSlot z.1.val z.2.1.val 0) := ⟨⟨0,⟨0,by
    change 0 < 64*z.1.val*4^(z.2.1.val-0)
    positivity⟩⟩⟩
  exact inferInstanceAs (Nontrivial (EuclideanSpace ℂ (TestBundleSlot z.1.val z.2.1.val 0)))

open scoped BigOperators

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2000] closedSubalgebraLE closedSubalgebraPreorder

instance actualHilbert_nontrivial (z : ActualTestIndex) : Nontrivial (FiberHilbertSum (ActualTestFiber z)) :=
  fiberHilbertSum_nontrivial

end Kaplansky

end

end OAI
end


