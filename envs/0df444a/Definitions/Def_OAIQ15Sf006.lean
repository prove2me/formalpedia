-- Prove2me | Definitions.Def_OAIQ15Sf006
-- name    : OAIQ15Sf006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:24:24.648747+00:00
-- url     : https://prove2.me/theorems/6866762e-08fc-4267-bc06-c7317d955801
-- title:
--   Definitions bundle OAIQ15Sf006 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 151 declarations of OpenAI's Lean: 31 definitions, 12 instances and 108 theorems. The definitions and types are `OAI.Kaplansky.ComplexGrassmann.ProjectiveProductModel`, `OAI.Kaplansky.ComplexGrassmann.coordinatePunctureFactor`, `OAI.Kaplansky.Incidence.OpenFrameBad`, `OAI.Kaplansky.Incidence.TupleAmbient`, `OAI.Kaplansky.Incidence.TupleOperators`, `OAI.Kaplansky.Incidence.TupleTarget`, `OAI.Kaplansky.Incidence.frameEvaluation`, `OAI.Kaplansky.Incidence.frameEvaluationLinear`, `OAI.Kaplansky.Incidence.graphEvaluation`, `OAI.Kaplansky.Incidence.graphQuotient`, `OAI.Kaplansky.Incidence.graphRestriction`, `OAI.Kaplansky.Incidence.tupleGraphRestriction`, `OAI.Kaplansky.SmoothPrefixModel`, `OAI.Kaplansky.TestFreshCoordinates`, `OAI.Kaplansky.TestReplacementModel`, `OAI.Kaplansky.bundleMapCoordinates`, `OAI.Kaplansky.bundleOrthonormalBasis`, `OAI.Kaplansky.bundleOrthonormalFrame`, `OAI.Kaplansky.bundleUnitaryTransition`, `OAI.Kaplansky.canonicalMinimizer`, `OAI.Kaplansky.canonicalScaling`, `OAI.Kaplansky.chartScaling`, `OAI.Kaplansky.hermitianHomCore`, `OAI.Kaplansky.hermitianSourceTransition`, `OAI.Kaplansky.hermitianTargetTransition`, `OAI.Kaplansky.realizeHomSection`, `OAI.Kaplansky.repeatedLineCore`, `OAI.Kaplansky.repeatedLineFiberEquiv`, `OAI.Kaplansky.repeatedLineMap`, `OAI.Kaplansky.spectralWindow`, `OAI.Kaplansky.testPrefixDimension`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: `BundleTests_Assembly`, `BundleTests_Base`, `BundleTests_Smooth`, `ComplexBundle_Avoidance`, `ComplexBundle_BundleIncidence`, `ComplexBundle_Coordinates`, `ComplexBundle_Frames`, `ComplexBundle_Grassmann`, `ComplexBundle_GrassmannManifold`, `ComplexBundle_Hom`, `ComplexBundle_Incidence`, `ComplexBundle_Maps`, `ComplexBundle_OpenIncidence`, `ComplexBundle_Projective`, `ComplexBundle_RealModel`, `ComplexBundle_Replacement`, `ComplexBundle_SmoothLine`, `IntegralHomology_ProjectiveClass`, `MatrixScaling_Bounds`, `MatrixScaling_Canonical`, `MatrixScaling_Continuous`, `MatrixScaling_Critical`, `MatrixScaling_Expansion`, `MatrixScaling_Minimizer`, `MatrixScaling_Spectrum`.
--
--   **Imports.** It imports the bundles `OAIQ15Sf000` and `OAIQ15Sf001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ15Sf010`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ15Sf000
import Definitions.Def_OAIQ15Sf001

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Grassmann
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.projectiveGrassmannT2 _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Graph charts and atlas of the complex Grassmannian. -/

section
open scoped BigOperators
namespace Kaplansky.ComplexGrassmann

variable {s k : ℕ}

theorem graph_model_finrank : Module.finrank ℂ (GraphMap s k)=s*k := by
  simp [GraphMap,GraphHorizontal,GraphVertical,Module.finrank_linearMap]

end Kaplansky.ComplexGrassmann

end

open scoped ContDiff
open Set
namespace Kaplansky.ComplexGrassmann
variable {s k : ℕ}

theorem grassmann_chart_transition (F G : (GraphFrame s k)) (A : (GraphSlope s k))
    (hA : IsUnit (graphTop F G A)) :
    grassmannChart G ((grassmannChart F).symm A)=graphTransition F G A := by
  apply slopePoint_injective G
  rw [grassmannChart_apply,grassmannChart_symm_apply,
    slopePoint_coordinate G _ ((inGraphChart_iff_unit F G A).mpr hA)]
  apply Subtype.ext
  exact (graphTransition_plane F G A hA).symm

/-- Smoothness on every actual chart overlap, with no assumed transition law. -/
theorem grassmann_chart_transition_smooth (F G : (GraphFrame s k)) :
    ContDiffOn ℂ ∞ (fun A => grassmannChart G ((grassmannChart F).symm A))
      {A | IsUnit (graphTop F G A)} := by
  apply (show ContDiffOn ℂ ∞ (graphTransition F G) {A | IsUnit (graphTop F G A)} from
    fun A hA => (graphTransition_contDiffAt F G A hA).contDiffWithinAt).congr
  intro A hA
  exact grassmann_chart_transition F G A hA

end Kaplansky.ComplexGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_GrassmannManifold
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.projectiveGrassmannT2 _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Grassmannian frames, smooth manifold structure, and countability. -/

section
open scoped ContDiff Manifold
open Set
namespace Kaplansky.ComplexGrassmann
variable {s k : ℕ}

instance grassmannChartedSpace : ChartedSpace (GraphSlope s k) (Grassmann s k) where
  atlas := Set.range grassmannChart
  chartAt P := grassmannChart (grassmann_atlas_covers P).choose
  mem_chart_source P := (grassmann_atlas_covers P).choose_spec
  chart_mem_atlas P := Set.mem_range_self (grassmann_atlas_covers P).choose

theorem grassmann_overlap_source (F G : GraphFrame s k) :
    ((grassmannChart F).symm.trans (grassmannChart G)).source=
      {A | IsUnit (graphTop F G A)} := by
  ext A
  change (A ∈ (grassmannChart F).target ∧
    (grassmannChart F).symm A ∈ (grassmannChart G).source) ↔ _
  simp only [grassmannChart_target,mem_univ,true_and,grassmannChart_source,
    grassmannChart_symm_apply,mem_ofPred_eq,slopePoint,graphPoint]
  exact inGraphChart_iff_unit F G A

instance grassmannRealManifold : IsManifold 𝓘(ℝ, GraphSlope s k) ∞ (Grassmann s k) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨F,rfl⟩ ⟨G,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, Set.range_id,Set.inter_univ,Set.preimage_id,
    grassmann_overlap_source,OpenPartialHomeomorph.trans_apply] using
    (grassmann_chart_transition_smooth F G).restrict_scalars ℝ

theorem graph_slope_complex_finrank : Module.finrank ℂ (GraphSlope s k)=s*k := by
  rw [← (LinearMap.toContinuousLinearMap : (GraphMap s k) ≃ₗ[ℂ] GraphSlope s k).finrank_eq]
  exact graph_model_finrank

theorem graph_slope_real_finrank : Module.finrank ℝ (GraphSlope s k)=2*s*k := by
  rw [finrank_real_of_complex,graph_slope_complex_finrank,Nat.mul_assoc]

end Kaplansky.ComplexGrassmann

end

open Set Topology
namespace Kaplansky.ComplexGrassmann
variable {s k : ℕ}

/-- Every actual plane is the span of an independent frame. -/
theorem framePoint_surjective : Function.Surjective (framePoint (s := s) (k := k)) := by
  intro P
  obtain ⟨F,hF⟩ := graph_charts_cover P.val P.property
  let B : PlaneFrameMap s k :=
    F.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (graphInclusion 0)
  have hB : Function.Injective B := by
    intro u v h
    have he := congrArg (fun z : Components s k => (F z).1) h
    simpa [B] using he
  refine ⟨⟨B,hB⟩,?_⟩
  apply Subtype.ext
  change LinearMap.range B.toLinearMap=P.val
  rw [← hF]
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    simp [B]
  · intro hz
    refine ⟨(F z).1,?_⟩
    apply F.injective
    have he : ((F z).1,(0 : GraphVertical k))=F z := Prod.ext rfl hz.symm
    simpa [B] using he

instance independentFrameLocallyCompact : LocallyCompactSpace (IndependentFrame s k) :=
  (ContinuousLinearMap.isOpen_injective (𝕜 := ℂ) (E := GraphHorizontal s)
    (F := Components s k)).locallyCompactSpace

instance grassmannSigmaCompact : SigmaCompactSpace (Grassmann s k) := by
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr (framePoint_surjective (s := s) (k := k))]
  exact isSigmaCompact_range framePoint_continuous

instance grassmannSecondCountable : SecondCountableTopology (Grassmann s k) :=
  ChartedSpace.secondCountable_of_sigmaCompact (GraphSlope s k) (Grassmann s k)

/-- The graph atlas has a countable subcover of actual planes, providing the
countability needed for the lower-dimensional image argument. -/
theorem exists_countable_graph_cover : ∃ c : Set (GraphFrame s k), c.Countable ∧
    ∀ P : Grassmann s k, ∃ F ∈ c, InGraphChart F P.val := by
  have hcover : (univ : Set (Grassmann s k)) ⊆ ⋃ F : GraphFrame s k, (grassmannChart F).source := by
    intro P _
    obtain ⟨F,hF⟩ := grassmann_atlas_covers P
    exact mem_iUnion.mpr ⟨F,hF⟩
  obtain ⟨c,hc,hcov⟩ := isLindelof_univ.elim_countable_subcover
    (fun F : GraphFrame s k => (grassmannChart F).source) (fun F => (grassmannChart F).open_source) hcover
  refine ⟨c,hc,fun P => ?_⟩
  simpa only [Set.mem_iUnion,exists_prop,grassmannChart_source,Set.mem_ofPred_eq] using hcov (mem_univ P)

end Kaplansky.ComplexGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Incidence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Linear incidence equations and their graph-coordinate kernel bundles. -/

section
open scoped ContDiff
namespace Kaplansky.Incidence
variable {s k t l : ℕ}
open ComplexGrassmann

/-- The quotient coordinate of a graph t-plane, (u,v) ↦ v-bu. -/
def graphQuotient (b : GraphSlope t l) : GraphAmbient t l →L[ℂ] GraphVertical l :=
  ContinuousLinearMap.snd ℂ _ _ - b.comp (ContinuousLinearMap.fst ℂ _ _)

@[simp] theorem graphQuotient_apply (b : GraphSlope t l) (v : GraphAmbient t l) :
    graphQuotient b v=v.2-b v.1 := rfl

theorem graphQuotient_zero_iff (b : GraphSlope t l) (v : GraphAmbient t l) :
    graphQuotient b v=0 ↔ v ∈ b.toLinearMap.graph := sub_eq_zero

def graphRestriction (a : GraphSlope s k) (b : GraphSlope t l) :
    (GraphAmbient s k →L[ℂ] GraphAmbient t l) →L[ℂ]
      (GraphHorizontal s →L[ℂ] GraphVertical l) :=
  ((ContinuousLinearMap.compL ℂ (GraphHorizontal s) (GraphAmbient t l) (GraphVertical l))
    (graphQuotient b)).comp
      ((ContinuousLinearMap.compL ℂ (GraphHorizontal s) (GraphAmbient s k) (GraphAmbient t l)).flip
        (graphInclusion a))

@[simp] theorem graphRestriction_apply (a : GraphSlope s k) (b : GraphSlope t l)
    (T : GraphAmbient s k →L[ℂ] GraphAmbient t l) (v : GraphHorizontal s) :
    graphRestriction a b T v=graphQuotient b (T (v,a v)) := by
  simp [graphRestriction]

/-- The zero equation for these smooth coordinates is exactly preservation of
S into U, with S and U the actual graph subspaces. -/
theorem graphRestriction_zero_iff (a : GraphSlope s k) (b : GraphSlope t l)
    (T : GraphAmbient s k →L[ℂ] GraphAmbient t l) :
    graphRestriction a b T=0 ↔ ∀ v ∈ a.toLinearMap.graph, T v ∈ b.toLinearMap.graph := by
  constructor
  · intro h v hv
    have he := congrArg (fun Q : GraphHorizontal s →L[ℂ] GraphVertical l => Q v.1) h
    have hv' : v.2=a v.1 := hv
    have hvv : (v.1,a v.1)=v := Prod.ext rfl hv'.symm
    rw [graphRestriction_apply,hvv] at he
    exact (graphQuotient_zero_iff b (T v)).mp he
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    simpa only [graphRestriction_apply,zero_apply] using
      (graphQuotient_zero_iff b (T (v,a v))).mpr (h _ rfl)

/-- A concrete right inverse: place the requested quotient map in the lower
left block and set all other blocks to zero. -/
theorem graphRestriction_surjective (a : GraphSlope s k) (b : GraphSlope t l) :
    Function.Surjective (graphRestriction a b) := by
  intro C
  refine ⟨(ContinuousLinearMap.inr ℂ _ _).comp
    (C.comp (ContinuousLinearMap.fst ℂ _ _)),?_⟩
  ext v
  simp [graphRestriction_apply]

theorem graphQuotient_smooth : ContDiff ℂ ∞ (graphQuotient (t := t) (l := l)) :=
  contDiff_const.sub (contDiff_id.clm_comp contDiff_const)

theorem graphInclusion_smooth : ContDiff ℂ ∞ (graphInclusion (s := s) (k := k)) :=
  contDiff_const.add (contDiff_const.clm_comp contDiff_id)

theorem graphRestriction_smooth : ContDiff ℂ ∞
    (fun p : GraphSlope s k × GraphSlope t l => graphRestriction p.1 p.2) := by
  have hq : ContDiff ℂ ∞ (fun p : GraphSlope s k × GraphSlope t l => graphQuotient p.2) :=
    graphQuotient_smooth.comp contDiff_snd
  have hi : ContDiff ℂ ∞ (fun p : GraphSlope s k × GraphSlope t l => graphInclusion p.1) :=
    graphInclusion_smooth.comp contDiff_fst
  exact (((ContinuousLinearMap.compL ℂ (GraphHorizontal s) (GraphAmbient t l)
    (GraphVertical l)).contDiff.comp hq)).clm_comp
    (((ContinuousLinearMap.compL ℂ (GraphHorizontal s) (GraphAmbient s k)
      (GraphAmbient t l)).flip.contDiff).comp hi)

end Kaplansky.Incidence

end

open scoped ContDiff Manifold
namespace Kaplansky.Incidence
open ComplexGrassmann SmoothKernel
variable {s k t l q : ℕ}

abbrev TupleAmbient (q s k t l : ℕ) :=
  Fin q → GraphAmbient s k →L[ℂ] GraphAmbient t l
abbrev TupleTarget (q s l : ℕ) := Fin q → GraphHorizontal s →L[ℂ] GraphVertical l

def tupleGraphRestriction (a : GraphSlope s k) (b : GraphSlope t l) :
    TupleAmbient q s k t l →L[ℂ] TupleTarget q s l :=
  ContinuousLinearMap.pi (fun i => (graphRestriction a b).comp (ContinuousLinearMap.proj i))

theorem tupleGraphRestriction_surjective (a : GraphSlope s k) (b : GraphSlope t l) :
    Function.Surjective (tupleGraphRestriction (q := q) a b) := by
  intro C
  choose T hT using fun i => graphRestriction_surjective a b (C i)
  exact ⟨T,funext hT⟩

theorem tupleGraphRestriction_smooth : ContDiff ℂ ∞
    (fun p : GraphSlope s k × GraphSlope t l => tupleGraphRestriction (q := q) p.1 p.2) := by
  apply contDiff_clm_apply_iff.mpr
  intro T
  apply contDiff_pi.mpr
  intro i
  exact graphRestriction_smooth.clm_apply contDiff_const

theorem tupleTarget_finrank : Module.finrank ℂ (TupleTarget q s l)=q*s*l := by
  have h : Module.finrank ℂ (GraphHorizontal s →L[ℂ] GraphVertical l)=s*l :=
    graph_slope_complex_finrank
  simp [TupleTarget,Module.finrank_pi_fintype,h,Nat.mul_assoc]

variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable (ev : Y → V →L[ℂ] TupleAmbient q s k t l)

/-- The actual linear family whose zero set is the local incidence locus. -/
def graphEvaluation (p : Y × (GraphSlope s k × GraphSlope t l)) : V →L[ℂ] TupleTarget q s l :=
  (tupleGraphRestriction p.2.1 p.2.2).comp (ev p.1)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
theorem graphEvaluation_zero_iff (p : Y × (GraphSlope s k × GraphSlope t l)) (v : V) :
    graphEvaluation ev p v=0 ↔ ∀ i, ∀ x ∈ p.2.1.toLinearMap.graph,
      ev p.1 v i x ∈ p.2.2.toLinearMap.graph := by
  constructor
  · intro h i
    have hi := congrArg (fun T : TupleTarget q s l => T i) h
    exact (graphRestriction_zero_iff p.2.1 p.2.2 (ev p.1 v i)).mp hi
  · intro h
    funext i
    exact (graphRestriction_zero_iff p.2.1 p.2.2 (ev p.1 v i)).mpr (h i)

variable [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem incidence_model_finrank [FiniteDimensional ℝ Y] : Module.finrank ℝ
    ((Y × (GraphSlope s k × GraphSlope t l)) × KernelModel V (TupleTarget q s l))=
      Module.finrank ℝ Y+2*s*k+2*t*l+2*(Module.finrank ℂ V-q*s*l) := by
  simp only [Module.finrank_prod,graph_slope_real_finrank,
    SurjectiveFamily.kernel_model_real_finrank,tupleTarget_finrank]
  omega

end Kaplansky.Incidence

end

end OAI
end

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

open scoped ContDiff MeasureTheory
open Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann
variable {s k t l q : ℕ}

abbrev TupleOperators (q s k t l : ℕ) := Fin q → Components s k →L[ℂ] Components t l

def frameEvaluationLinear (F : GraphFrame s k) (G : GraphFrame t l) :
    TupleOperators q s k t l →ₗ[ℂ] TupleAmbient q s k t l where
  toFun T i := G.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((T i).comp F.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  map_add' T U := by
    funext i
    apply ContinuousLinearMap.ext
    intro x
    change G (T i (F.symm x)+U i (F.symm x))=G (T i (F.symm x))+G (U i (F.symm x))
    exact G.map_add _ _
  map_smul' c T := by
    funext i
    apply ContinuousLinearMap.ext
    intro x
    change G (c • T i (F.symm x))=c • G (T i (F.symm x))
    exact G.map_smul c _

def frameEvaluation (F : GraphFrame s k) (G : GraphFrame t l) :
    TupleOperators q s k t l →L[ℂ] TupleAmbient q s k t l :=
  (frameEvaluationLinear F G).toContinuousLinearMap

@[simp] theorem frameEvaluation_apply (F : GraphFrame s k) (G : GraphFrame t l)
    (T : TupleOperators q s k t l) (i : Fin q) (x : GraphAmbient s k) :
    frameEvaluation F G T i x=G (T i (F.symm x)) := rfl

theorem frameEvaluation_surjective (F : GraphFrame s k) (G : GraphFrame t l) :
    Function.Surjective (frameEvaluation (q := q) F G) := by
  intro C
  refine ⟨fun i => G.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((C i).comp F.toContinuousLinearEquiv.toContinuousLinearMap),?_⟩
  funext i
  apply ContinuousLinearMap.ext
  intro x
  change G (G.symm (C i (F (F.symm x))))=C i x
  simp

theorem frame_incidence_iff (F : GraphFrame s k) (G : GraphFrame t l)
    (T : TupleOperators q s k t l) (a : GraphSlope s k) (b : GraphSlope t l) :
    (∀ i, ∀ x ∈ graphPlane F a.toLinearMap, T i x ∈ graphPlane G b.toLinearMap) ↔
      ∀ i, ∀ x ∈ a.toLinearMap.graph, frameEvaluation F G T i x ∈ b.toLinearMap.graph := by
  constructor
  · intro h i x hx
    have hi : F.symm x ∈ graphPlane F a.toLinearMap := by simpa using hx
    exact h i (F.symm x) hi
  · intro h i x hx
    have hi : F x ∈ a.toLinearMap.graph := hx
    have hh := h i (F x) hi
    change G (T i x) ∈ b.toLinearMap.graph
    simpa only [frameEvaluation_apply,LinearEquiv.symm_apply_apply] using hh

end Kaplansky.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_OpenIncidence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.projectiveGrassmannT2 _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Openness of kernel, graph, frame, and rank incidence conditions. -/

section
open scoped ContDiff MeasureTheory
open Module Set MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann SmoothKernel
variable {s k t l q : ℕ}
variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable (ev : Y → V →L[ℂ] TupleAmbient q s k t l) (U : Set Y)

set_option synthInstance.maxHeartbeats 200000 in
omit [FiniteDimensional ℝ Y] [FiniteDimensional ℂ V] in
theorem graphEvaluation_smoothOn (hU : IsOpen U) (he : ContDiffOn ℝ ∞ ev U) :
    ContDiffOn ℝ ∞ (graphEvaluation ev) (U ×ˢ univ) := by
  intro p hp
  have hc : ContDiff ℂ ∞ (fun z :
      (TupleAmbient q s k t l →L[ℂ] TupleTarget q s l) × (V →L[ℂ] TupleAmbient q s k t l) =>
      z.1.comp z.2) := contDiff_fst.clm_comp contDiff_snd
  have h1 := ((tupleGraphRestriction_smooth (q := q) (s := s) (k := k) (t := t) (l := l)).restrict_scalars ℝ).contDiffAt.comp p contDiffAt_snd
  have h2 := ((he p.1 hp.1).contDiffAt (hU.mem_nhds hp.1)).comp p contDiffAt_fst
  exact ((hc.restrict_scalars ℝ).contDiffAt.comp p (h1.prodMk h2)).contDiffWithinAt

/-- Actual graph incidence over an open base chart is null under the real
dimension gap; no extension of its evaluation map off the chart is assumed. -/
theorem open_graph_incidence_image_null [MeasurableSpace V] [BorelSpace V]
    (hU : IsOpen U) (he : ContDiffOn ℝ ∞ ev U)
    (hs : ∀ y ∈ U, Function.Surjective (ev y))
    (hgap : finrank ℝ Y+2*s*k+2*t*l<2*q*s*l) :
    μH[finrank ℝ V] {v : V | ∃ y ∈ U, ∃ (a : GraphSlope s k) (b : GraphSlope t l),
      ∀ i, ∀ x ∈ a.toLinearMap.graph, ev y v i x ∈ b.toLinearMap.graph}=0 := by
  by_cases hu : U.Nonempty
  · obtain ⟨y,hy⟩ := hu
    have hsur : ∀ p ∈ U ×ˢ (univ : Set (GraphSlope s k × GraphSlope t l)),
        Function.Surjective (graphEvaluation ev p) := fun p hp =>
      (tupleGraphRestriction_surjective p.2.1 p.2.2).comp (hs p.1 hp.1)
    have hr := (graphEvaluation ev (y,(0,0))).toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (hsur _ ⟨hy,mem_univ _⟩),finrank_top,tupleTarget_finrank] at hr
    have hd : finrank ℝ ((Y × (GraphSlope s k × GraphSlope t l)) × KernelModel V (TupleTarget q s l)) < finrank ℝ V := by
      rw [incidence_model_finrank,finrank_real_of_complex]
      simp only [Nat.mul_assoc] at *
      omega
    have hn := open_kernel_incidence_image_null (graphEvaluation ev) (U ×ˢ univ)
      (hU.prod isOpen_univ) (graphEvaluation_smoothOn ev U hU he) hsur hd
    have heq : {v : V | ∃ p ∈ U ×ˢ (univ : Set (GraphSlope s k × GraphSlope t l)), graphEvaluation ev p v=0} =
        {v : V | ∃ y ∈ U, ∃ (a : GraphSlope s k) (b : GraphSlope t l), ∀ i, ∀ x ∈ a.toLinearMap.graph, ev y v i x ∈ b.toLinearMap.graph} := by
      ext v
      simp only [mem_ofPred_eq,Prod.exists,mem_prod,mem_univ,and_true,graphEvaluation_zero_iff]
      constructor
      · rintro ⟨y,a,b,hy,h⟩; exact ⟨y,hy,a,b,h⟩
      · rintro ⟨y,hy,a,b,h⟩; exact ⟨y,a,b,hy,h⟩
    rw [heq] at hn
    exact hn
  · have hempty : U=∅ := Set.not_nonempty_iff_eq_empty.mp hu
    simp [hempty]

end Kaplansky.Incidence

end

section
open scoped ContDiff MeasureTheory
open Set Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann
variable {q s k t l : ℕ}
variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable (ev : Y → V →L[ℂ] TupleOperators q s k t l) (U : Set Y)

def OpenFrameBad : Set V :=
  {v | ∃ y ∈ U, ∃ (P : Grassmann s k) (Q : Grassmann t l),
    ∀ i, ∀ x ∈ P.val, ev y v i x ∈ Q.val}

theorem openFrameBad_null [MeasurableSpace V] [BorelSpace V]
    (hU : IsOpen U) (he : ContDiffOn ℝ ∞ ev U)
    (hs : ∀ y ∈ U, Function.Surjective (ev y))
    (hgap : finrank ℝ Y+2*s*k+2*t*l<2*q*s*l) :
    μH[finrank ℝ V] (OpenFrameBad ev U)=0 := by
  obtain ⟨c,hc,hcover⟩ := exists_countable_graph_cover (s := s) (k := k)
  obtain ⟨d,hd,hcover'⟩ := exists_countable_graph_cover (s := t) (k := l)
  let := hc.toEncodable
  let := hd.toEncodable
  let bad (i : c × d) : Set V := {v | ∃ y ∈ U, ∃ (a : GraphSlope s k) (b : GraphSlope t l),
    ∀ j, ∀ x ∈ a.toLinearMap.graph,
      frameEvaluation i.1.val i.2.val (ev y v) j x ∈ b.toLinearMap.graph}
  have hn (i : c × d) : μH[finrank ℝ V] (bad i)=0 := by
    let ef : Y → V →L[ℂ] TupleAmbient q s k t l := fun y =>
      (frameEvaluation i.1.val i.2.val).comp (ev y)
    have hf : ContDiffOn ℝ ∞ ef U := by
      have hh : ContDiff ℂ ∞ (fun L : V →L[ℂ] TupleOperators q s k t l =>
        (frameEvaluation i.1.val i.2.val).comp L) := contDiff_const.clm_comp contDiff_id
      exact (hh.restrict_scalars ℝ).comp_contDiffOn he
    exact open_graph_incidence_image_null ef U hU hf
      (fun y hy => (frameEvaluation_surjective i.1.val i.2.val).comp (hs y hy)) hgap
  apply measure_mono_null (t := ⋃ i : c × d, bad i) ?_ (measure_iUnion_null hn)
  rintro v ⟨y,hy,P,Q,hPQ⟩
  obtain ⟨F,hFc,hF⟩ := hcover P
  obtain ⟨G,hGd,hG⟩ := hcover' Q
  refine mem_iUnion.mpr ⟨(⟨F,hFc⟩,⟨G,hGd⟩),y,hy,slopeCoordinate F P,slopeCoordinate G Q,?_⟩
  apply (frame_incidence_iff F G (ev y v) _ _).mp
  have hp : graphPlane F (slopeCoordinate F P).toLinearMap=P.val :=
    congrArg Subtype.val (slopePoint_coordinate F P hF)
  have hq : graphPlane G (slopeCoordinate G Q).toLinearMap=Q.val :=
    congrArg Subtype.val (slopePoint_coordinate G Q hG)
  rw [hp,hq]
  exact hPQ

end Kaplansky.Incidence

end

open scoped ContDiff MeasureTheory
open Set Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
variable {q d r : ℕ}
variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem openRankBad_null [MeasurableSpace V] [BorelSpace V]
    (ev : Y → V →L[ℂ] MatrixTuple q d r) (U : Set Y)
    (hU : IsOpen U) (he : ContDiffOn ℝ ∞ ev U)
    (hs : ∀ y ∈ U, Function.Surjective (ev y)) {s t : ℕ}
    (hsd : s≤d) (htr : t ≤ r)
    (hgap : finrank ℝ Y+2*s*(d-s)+2*t*(r-t)<2*q*s*(r-t)) :
    μH[finrank ℝ V] (OpenRankBad ev U s t)=0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hsd
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le htr
  have heq : OpenRankBad ev U s t=OpenFrameBad ev U := by
    ext v
    constructor
    · rintro ⟨y,hy,S,hS,T,hT,h⟩
      exact ⟨y,hy,⟨S,hS⟩,⟨T,hT⟩,h⟩
    · rintro ⟨y,hy,⟨S,hS⟩,⟨T,hT⟩,h⟩
      exact ⟨y,hy,S,hS,T,hT,h⟩
  rw [heq]
  exact openFrameBad_null ev U hU he hs (by simpa using hgap)

/-- A single parameter avoids every forbidden rank pair on every chart of a
countable family. The maps, kernels, graph coverage and nullity are actual;
only the smooth surjective coordinate evaluation data enter as hypotheses. -/
theorem exists_countable_chart_incidence_parameter {ι : Type*} [Countable ι]
    (ev : ι → Y → V →L[ℂ] MatrixTuple q d r) (U : ι → Set Y)
    (hU : ∀ j, IsOpen (U j)) (he : ∀ j, ContDiffOn ℝ ∞ (ev j) (U j))
    (hs : ∀ j y, y ∈ U j → Function.Surjective (ev j y))
    (pairs : Finset (ℕ × ℕ))
    (hpairs : ∀ p ∈ pairs, p.1≤d ∧ p.2 ≤ r ∧
      finrank ℝ Y+2*p.1*(d-p.1)+2*p.2*(r-p.2)<2*q*p.1*(r-p.2)) :
    ∃ v : V, ∀ j y, y ∈ U j → ∀ p ∈ pairs, ∀ S : Submodule ℂ (Fin d → ℂ),
      finrank ℂ S=p.1 → p.2<finrank ℂ
        (⨆ i, S.map (ev j y v i).toLinearMap : Submodule ℂ (Fin r → ℂ)) := by
  borelize V
  have hn : μH[finrank ℝ V] (⋃ j, ⋃ p ∈ pairs, OpenRankBad (ev j) (U j) p.1 p.2)=0 :=
    measure_iUnion_null (fun j => measure_iUnion_null (fun p => measure_iUnion_null (fun hp =>
      openRankBad_null (ev j) (U j) (hU j) (he j) (hs j)
        (hpairs p hp).1 (hpairs p hp).2.1 (hpairs p hp).2.2)))
  have hev : ∃ v : V, v ∉ ⋃ j, ⋃ p ∈ pairs, OpenRankBad (ev j) (U j) p.1 p.2 := by
    by_contra h
    push Not at h
    have hu : (⋃ j, ⋃ p ∈ pairs, OpenRankBad (ev j) (U j) p.1 p.2)=univ := Set.eq_univ_of_forall h
    rw [hu] at hn
    exact (ne_of_gt (isOpen_univ.measure_pos (μH[finrank ℝ V]) Set.univ_nonempty)) hn
  obtain ⟨v,hv⟩ := hev
  refine ⟨v,fun j y hy p hp S hS => ?_⟩
  by_contra h
  have hd : finrank ℂ (⨆ i, S.map (ev j y v i).toLinearMap : Submodule ℂ (Fin r → ℂ))≤p.2 := by omega
  obtain ⟨T,hWT,hT⟩ := exists_super_finrank
    (⨆ i, S.map (ev j y v i).toLinearMap : Submodule ℂ (Fin r → ℂ)) hd
      (by simpa using (hpairs p hp).2.1)
  apply hv
  refine mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,y,hy,S,hS,T,hT,?_⟩⟩⟩
  intro i x hx
  exact hWT ((le_iSup (fun i => S.map (ev j y v i).toLinearMap) i)
    (Submodule.mem_map.mpr ⟨x,hx,rfl⟩))

end Kaplansky.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_BundleIncidence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Rank transport and smooth bundle-incidence families. -/

section
open Bundle Module Set
open scoped Topology Manifold ContDiff
namespace Kaplansky.Incidence
variable {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace B] [ChartedSpace X B]
  [IsManifold 𝓘(ℝ,X) ∞ B] [T2Space B] [CompactSpace B]
  {q d r : ℕ} (E F : B → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (Fin d → ℂ) E)] [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
  [FiberBundle (Fin d → ℂ) E] [FiberBundle (Fin r → ℂ) F]
  [VectorBundle ℝ (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
  [VectorBundle ℝ (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]
  [ContMDiffVectorBundle ∞ (Fin d → ℂ) E 𝓘(ℝ,X)]
  [ContMDiffVectorBundle ∞ (Fin r → ℂ) F 𝓘(ℝ,X)]

/-- The bundle incidence construction on a compact smooth manifold without
boundary. The conclusion gives actual fiber maps, smooth in every frame,
and strict image-rank bounds for every subspace of each original fiber.
Global generation, incidence nullity and the good tuple are all constructed. -/
theorem exists_bundle_incidence_maps (pairs : Finset (ℕ × ℕ))
    (hpairs : ∀ p ∈ pairs, p.1≤d ∧ p.2 ≤ r ∧
      finrank ℝ X+2*p.1*(d-p.1)+2*p.2*(r-p.2)<2*q*p.1*(r-p.2)) :
    ∃ T : Fin q → ∀ y, E y →L[ℂ] F y,
      (∀ i (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
        (f : Trivialization (Fin r → ℂ) (π (Fin r → ℂ) F))
        [MemTrivializationAtlas e] [MemTrivializationAtlas f],
        ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,(Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) ∞
          (complexHomCoordinates E F e f (T i)) (e.baseSet ∩ f.baseSet)) ∧
      ∀ y p, p ∈ pairs → ∀ S : Submodule ℂ (E y), finrank ℂ S=p.1 →
        p.2<finrank ℂ (⨆ i, S.map (T i y).toLinearMap : Submodule ℂ (F y)) := by
  classical
  obtain ⟨n,s,hs,hsm⟩ := exists_finite_smooth_hom_evaluation
    (F₁ := Fin d → ℂ) (F₂ := Fin r → ℂ) 𝓘(ℝ,X) E F
  let e (x : B) := trivializationAt (Fin d → ℂ) E x
  let f (x : B) := trivializationAt (Fin r → ℂ) F x
  let U (x : B) := (e x).baseSet ∩ (f x).baseSet
  have hU : ∀ x, IsOpen (U x) := fun x => (e x).open_baseSet.inter (f x).open_baseSet
  have hxU : ∀ x, x ∈ U x := fun x =>
    ⟨mem_baseSet_trivializationAt (Fin d → ℂ) E x,mem_baseSet_trivializationAt (Fin r → ℂ) F x⟩
  obtain ⟨c,hc,hcover⟩ := exists_countable_local_chart_cover (X := X) U hU hxU
  let := hc.toEncodable
  let V := Fin q → Fin n → ℂ
  let evB (x y : B) : V →L[ℂ] MatrixTuple q d r :=
    tupleEvaluation (homEvaluationCoordinates E F s (e x) (f x) y)
  have heB (x : B) : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,V →L[ℂ] MatrixTuple q d r) ∞ (evB x) (U x) :=
    tupleEvaluation_smooth.contMDiff.comp_contMDiffOn (hsm (e x) (f x)).1
  let ev (x : c) (z : X) := evB x.val ((chartAt X x.val).symm z)
  have hev (x : c) : ContDiffOn ℝ ∞ (ev x) (localChartDomain U x.val) :=
    localChartDomain_smooth U (evB x.val) x.val (heB x.val)
  have hsur (x : c) (z : X) (hz : z ∈ localChartDomain U x.val) :
      Function.Surjective (ev x z) :=
    tupleEvaluation_surjective _ ((hsm (e x.val) (f x.val)).2 _ hz.2)
  obtain ⟨v,hv⟩ := exists_countable_chart_incidence_parameter ev
    (fun x : c => localChartDomain U x.val)
    (fun x => localChartDomain_open U hU x.val) hev hsur pairs hpairs
  let T (i : Fin q) (y : B) := sectionEvaluation s y (v i)
  refine ⟨T,?_,?_⟩
  · intro i e' f' _ _
    have happ : ContDiff ℂ ∞ (fun L : (Fin n → ℂ) →L[ℂ] ((Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) => L (v i)) :=
      contDiff_id.clm_apply contDiff_const
    have hh := (happ.restrict_scalars ℝ).contMDiff.comp_contMDiffOn (hsm e' f').1
    apply hh.congr
    intro y hy
    exact (homEvaluationCoordinates_apply E F s e' f' y (v i)).symm
  · intro y p hp S hS
    obtain ⟨x,hxc,hyU,hyc,hz,hyz⟩ := hcover y
    let x' : c := ⟨x,hxc⟩
    let z := (chartAt X x) y
    have hh := hv x' z hz p hp
    apply rank_expansion_of_coordinates (fun i => (T i y).toLinearMap)
      (fun i => (ev x' z v i).toLinearMap)
      ((e x).toPretrivialization.linearEquivAt ℂ y hyU.1)
      ((f x).toPretrivialization.linearEquivAt ℂ y hyU.2) ?_ hh S hS
    intro i w
    change ((f x).toPretrivialization.linearEquivAt ℂ y hyU.2) (T i y w)=
      (tupleEvaluation (homEvaluationCoordinates E F s (e x) (f x)
        ((chartAt X x).symm ((chartAt X x) y))) v i)
        (((e x).toPretrivialization.linearEquivAt ℂ y hyU.1) w)
    rw [hyz,tupleEvaluation_apply,homEvaluationCoordinates_apply E F s (e x) (f x) y (v i)]
    exact homFrameLinear_commutes E F (e x) (f x) y hyU (T i y) w

end Kaplansky.Incidence

end

open Bundle Module Set
open scoped Topology Manifold ContDiff
namespace Kaplansky.Incidence
variable {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace B] [ChartedSpace X B]
  [IsManifold 𝓘(ℝ,X) ∞ B] [T2Space B] [CompactSpace B]
  {q d r : ℕ} (E F : B → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (Fin d → ℂ) E)] [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
  [FiberBundle (Fin d → ℂ) E] [FiberBundle (Fin r → ℂ) F]
  [VectorBundle ℝ (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
  [VectorBundle ℝ (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]
  [ContMDiffVectorBundle ∞ (Fin d → ℂ) E 𝓘(ℝ,X)]
  [ContMDiffVectorBundle ∞ (Fin r → ℂ) F 𝓘(ℝ,X)]

theorem exists_smooth_bundle_incidence_maps (pairs : Finset (ℕ × ℕ))
    (hpairs : ∀ p ∈ pairs, p.1≤d ∧ p.2 ≤ r ∧
      finrank ℝ X+2*p.1*(d-p.1)+2*p.2*(r-p.2)<2*q*p.1*(r-p.2)) :
    ∃ T : Fin q → ∀ y, E y →L[ℂ] F y,
      (∀ i, ContMDiff 𝓘(ℝ,X) (𝓘(ℝ,X).prod 𝓘(ℝ,(Fin d → ℂ) →L[ℝ] (Fin r → ℂ))) ∞
        (fun y => TotalSpace.mk' ((Fin d → ℂ) →L[ℝ] (Fin r → ℂ)) y ((T i y).restrictScalars ℝ))) ∧
      ∀ y p, p ∈ pairs → ∀ S : Submodule ℂ (E y), finrank ℂ S=p.1 →
        p.2<finrank ℂ (⨆ i, S.map (T i y).toLinearMap : Submodule ℂ (F y)) := by
  obtain ⟨T,hT,hExp⟩ := exists_bundle_incidence_maps E F pairs hpairs
  exact ⟨T,fun i => smooth_realHom_of_complex_coordinates 𝓘(ℝ,X) E F (T i) (hT i),hExp⟩

end Kaplansky.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.MatrixScaling_Spectrum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral min-max bounds, continuity, and compactness of projections. -/

section

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {d : ℕ}

instance instCompactSpaceProjectionSpace (s : ℕ) : CompactSpace (projectionSpace d s) :=
  isCompact_iff_compactSpace.mp (isCompact_projectionSpace s)

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.MatrixScaling_Bounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
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

theorem exists_top_spectral_projection {d : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosDef) (k : Fin d) :
    ∃ p : projectionSpace d (k.val+1),
      (P - decreasingEigenvalues hP.1 k • p.val).PosSemidef := by
  let e := spectralIndex d
  let f : Fin d → ℂ := fun i => if e.symm i ≤ k then 1 else 0
  let U := Unitary.conjStarAlgAut ℂ _ hP.1.eigenvectorUnitary
  let p := U (diagonal f)
  have hf : IsSelfAdjoint (diagonal f) := by
    apply isHermitian_diagonal_of_self_adjoint
    funext i
    simp [f]
  have hp : p.IsHermitian := by
    change star (U (diagonal f)) = U (diagonal f)
    rw [← map_star, hf.star_eq]
  have hpp : p*p=p := by
    change U (diagonal f) * U (diagonal f) = U (diagonal f)
    rw [← map_mul, diagonal_mul_diagonal]
    congr 2
    funext i
    simp [f]
  have ht : p.trace = ((k.val+1 : ℕ) : ℂ) := by
    change (U (diagonal f)).trace = _
    dsimp [U]
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
      one_mul, Matrix.trace_diagonal]
    change (∑ i, (fun j : Fin d => if j ≤ k then (1 : ℂ) else 0) (e.symm i)) = _
    rw [e.symm.sum_comp (fun j : Fin d => if j ≤ k then (1 : ℂ) else 0), Finset.sum_boole]
    have heq : Finset.univ.filter (fun i : Fin d => i ≤ k) = Finset.Iic k := by
      ext i; simp
    rw [heq, Fin.card_Iic]
  refine ⟨⟨p, hp, hpp, ?_⟩, ?_⟩
  · simpa only [Complex.natCast_re] using congrArg Complex.re ht
  · have hd : (diagonal (fun i => (hP.1.eigenvalues i : ℂ)) -
        (decreasingEigenvalues hP.1 k : ℂ) • diagonal f).PosSemidef := by
      rw [← diagonal_smul, diagonal_sub, posSemidef_diagonal_iff]
      intro i
      have he : hP.1.eigenvalues i = decreasingEigenvalues hP.1 (e.symm i) := by
        simpa only [e, Equiv.apply_symm_apply] using eigenvalues_spectralIndex hP.1 (e.symm i)
      by_cases hi : e.symm i ≤ k
      · have hm := decreasingEigenvalues_antitone hP.1 hi
        simp only [Pi.smul_apply, f, ite_eq_left hi, smul_eq_mul, mul_one]
        rw [he, ← Complex.ofReal_sub]
        exact_mod_cast sub_nonneg.mpr hm
      · simp only [Pi.smul_apply, f, ite_eq_right hi, smul_eq_mul, mul_zero, sub_zero]
        exact_mod_cast (hP.eigenvalues_pos i).le
    have hu := hd.mul_mul_conjTranspose_same (hP.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
    change (U (diagonal (fun i => (hP.1.eigenvalues i : ℂ)) -
      (decreasingEigenvalues hP.1 k : ℂ) • diagonal f)).PosSemidef at hu
    rw [map_sub, map_smul] at hu
    have hspec : U (diagonal (fun i => (hP.1.eigenvalues i : ℂ))) = P :=
      hP.1.spectral_theorem.symm
    rw [hspec, Complex.coe_smul] at hu
    exact hu

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem uniform_projection_spectral_bound {Y : Type*}
    [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)),
      2 * Module.finrank ℂ S ≤
        Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    (hdr : 2*d ≤ r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y (s : Fin d) (p : projectionSpace d (s.val+1)),
      ε ≤ decreasingEigenvalues
        (scalingMap_projection_positive (T y) p.property.1 p.property.2.1).1
        ⟨2*s.val+1, by omega⟩ := by
  let X := Σ s : Fin d, Y × projectionSpace d (s.val+1)
  let f : X → ℝ := fun x => decreasingEigenvalues
    (scalingMap_projection_positive (T x.2.1) x.2.2.property.1 x.2.2.property.2.1).1
    ⟨2*x.1.val+1, by omega⟩
  have hf : Continuous f := by
    apply continuous_sigma
    intro s
    let D : Y × projectionSpace d (s.val+1) → Matrix (Fin r) (Fin r) ℂ :=
      fun x => scalingMap (T x.1) x.2.val
    have hD : Continuous D := continuous_scalingMap
      (fun x : Y × projectionSpace d (s.val+1) => T x.1)
      (hT.comp continuous_fst) (fun x => x.2.val) (continuous_subtype_val.comp continuous_snd)
    have hDh (x : Y × projectionSpace d (s.val+1)) : (D x).IsHermitian :=
      (scalingMap_projection_positive (T x.1) x.2.property.1 x.2.property.2.1).1
    let k : Fin r := ⟨2*s.val+1, by omega⟩
    have hc := (continuous_decreasingEigenvalues k).comp (hD.subtype_mk hDh)
    change Continuous (fun x : Y × projectionSpace d (s.val+1) =>
      decreasingEigenvalues (hDh x) k)
    exact hc
  have hpos (x : X) : 0 < f x := by
    have hr := scalingMap_projection_rank (T x.2.1) (hexpand x.2.1)
      x.2.2.property.1 x.2.2.property.2.1
    rw [projectionSpace_rank] at hr
    exact decreasingEigenvalues_pos_of_lt_rank
      (scalingMap_projection_positive (T x.2.1) x.2.2.property.1 x.2.2.property.2.1)
      ⟨2*x.1.val+1, by omega⟩ (by change 2*x.1.val+1 < _; omega)
  cases isEmpty_or_nonempty X with
  | inl h =>
    let := h
    refine ⟨1, zero_lt_one, ?_⟩
    intro y s p
    exact isEmptyElim (⟨s,y,p⟩ : X)
  | inr h =>
    let := h
    obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (Set.univ : Set X).Nonempty)
      hf.continuousOn
    exact ⟨f x, hpos x, fun y s p => hx (Set.mem_univ (⟨s,y,p⟩ : X))⟩

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem scaling_spectral_bound (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hdr : 2*d ≤ r) (ε : ℝ)
    (hmin : ∀ (s : Fin d) (p : projectionSpace d (s.val+1)),
      ε ≤ decreasingEigenvalues (scalingMap_projection_positive T p.property.1 p.property.2.1).1
        ⟨2*s.val+1, by omega⟩)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) (s : Fin d) :
    ε * decreasingEigenvalues hP.1 s ≤
      decreasingEigenvalues (scalingMap_positive T hP.posSemidef).1 ⟨2*s.val+1, by omega⟩ := by
  obtain ⟨p,hp⟩ := exists_top_spectral_projection hP s
  have hc := scalingMap_comparison T (decreasingEigenvalues hP.1 s) hp
  have hLam := decreasingEigenvalues_pos hP s
  have hs := decreasingEigenvalues_smul_le
    (scalingMap_projection_positive T p.property.1 p.property.2.1).1
    (scalingMap_positive T hP.posSemidef).1 _ hLam.le hc
    (⟨2*s.val+1, by omega⟩ : Fin r)
  calc
    ε * decreasingEigenvalues hP.1 s = decreasingEigenvalues hP.1 s * ε := mul_comm _ _
    _ ≤ decreasingEigenvalues hP.1 s *
        decreasingEigenvalues (scalingMap_projection_positive T p.property.1 p.property.2.1).1
          ⟨2*s.val+1, by omega⟩ := mul_le_mul_of_nonneg_left (hmin s p) hLam.le
    _ ≤ _ := hs

theorem uniform_scaling_estimate {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)),
      2 * Module.finrank ℂ S ≤
        Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    (hdr : 2*d ≤ r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosDef),
      (∀ s : Fin d, ε * decreasingEigenvalues hP.1 s ≤
        decreasingEigenvalues (scalingMap_positive (T y) hP.posSemidef).1
          ⟨2*s.val+1, by omega⟩) ∧
      2 * ∑ s, Real.log (1+ε*decreasingEigenvalues hP.1 s) ≤
        Real.log ((1+scalingMap (T y) P).det.re) := by
  obtain ⟨ε,hε,hm⟩ := uniform_projection_spectral_bound T hT hexpand hdr
  refine ⟨ε,hε,?_⟩
  intro y P hP
  have hs := scaling_spectral_bound (T y) hdr ε (hm y) hP
  refine ⟨hs, ?_⟩
  exact scaling_log_det_of_spectral_bound hdr (scalingMap_positive (T y) hP.posSemidef)
    (decreasingEigenvalues hP.1) (decreasingEigenvalues_pos hP) hε hs

/-- The uniform determinant bound with no extra dimension or nonempty-base
hypothesis. The dimension inequality is deduced from expansion when needed. -/
theorem uniform_scaling_log_det {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)),
      2 * Module.finrank ℂ S ≤
        Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosDef),
      2 * ∑ s, Real.log (1+ε*decreasingEigenvalues hP.1 s) ≤
        Real.log ((1+scalingMap (T y) P).det.re) := by
  cases isEmpty_or_nonempty Y with
  | inl h =>
    let := h
    exact ⟨1, zero_lt_one, fun y => isEmptyElim y⟩
  | inr h =>
    let := h
    let y := Classical.arbitrary Y
    obtain ⟨ε,hε,he⟩ := uniform_scaling_estimate T hT hexpand
      (expansion_dimension (T y) (hexpand y))
    exact ⟨ε,hε,fun y P hP => (he y P hP).2⟩

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem uniform_scaling_sublevels {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)),
      2 * Module.finrank ℂ S ≤
        Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (C : ℝ) y (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosDef),
      scalingPotential (T y) P ≤ C → ∀ i : Fin d,
        let B := C - (d-1)*((3/2)*Real.log ε)
        Real.exp (-2*B/3) ≤ decreasingEigenvalues hP.1 i ∧
          decreasingEigenvalues hP.1 i ≤ Real.exp (2*B-4*Real.log ε) := by
  obtain ⟨ε,hε,he⟩ := uniform_scaling_log_det T hT hexpand
  refine ⟨ε,hε,?_⟩
  intro C y P hP hC i
  exact scaling_eigenvalue_bounds hε (decreasingEigenvalues hP.1)
    (decreasingEigenvalues_pos hP)
    ((scalingScalar_sum_le_potential (T y) hP ε (he y P hP)).trans hC) i

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {d : ℕ}

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
-- module Solutions.OAIQ15_Sf.MatrixScaling_Minimizer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
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

theorem scaling_minimizer_exists {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)),
      2 * Module.finrank ℂ S ≤
        Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ))) (y : Y) :
    ∃ P : Matrix (Fin d) (Fin d) ℂ, P.PosDef ∧
      ∀ R : Matrix (Fin d) (Fin d) ℂ, R.PosDef →
        scalingPotential (T y) P ≤ scalingPotential (T y) R := by
  obtain ⟨ε,hε,hbound⟩ := uniform_scaling_sublevels T hT hexpand
  let C := scalingPotential (T y) 1
  let B := C - (d-1)*((3/2)*Real.log ε)
  apply scaling_minimum_of_sublevel_bound (T y)
    (a := Real.exp (-2*B/3)) (b := Real.exp (2*B-4*Real.log ε)) (C := C)
    (Real.exp_pos _) (Real.exp_pos _).le
  · intro P hP hC
    exact hbound C y P hP hC
  · exact Matrix.PosDef.one
  · exact le_rfl

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem existsUnique_scaling_minimizer (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ))) :
    ∃! P : Matrix (Fin d) (Fin d) ℂ, P.PosDef ∧
      ∀ Q : Matrix (Fin d) (Fin d) ℂ, Q.PosDef → scalingPotential T P ≤ scalingPotential T Q := by
  obtain ⟨P,hP,hmin⟩ := scaling_minimizer_exists (fun _ : Unit => T)
    continuous_const (fun _ => hexpand) ()
  refine ⟨P,⟨hP,hmin⟩,?_⟩
  intro Q hQ
  exact scaling_minimizer_unique T hexpand hQ.1 hP hQ.2 hmin

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.MatrixScaling_Critical
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
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
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

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

end OAI
end

section
-- module Solutions.OAIQ15_Sf.MatrixScaling_Continuous
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous dependence of the unique normalized scaling. -/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

theorem exists_continuous_scaling_minimizer {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ))) :
    ∃ P : Y → Matrix (Fin d) (Fin d) ℂ, Continuous P ∧ ∀ y, (P y).PosDef ∧
      ∀ Q : Matrix (Fin d) (Fin d) ℂ, Q.PosDef → scalingPotential (T y) (P y) ≤ scalingPotential (T y) Q := by
  choose P hP using fun y => (existsUnique_scaling_minimizer (T y) (hexpand y)).exists
  have hidentity := continuous_scalingPotential T hT (fun _ => 1) continuous_const
    (fun _ => Matrix.PosDef.one)
  obtain ⟨C,hC⟩ := (isCompact_range hidentity).bddAbove
  obtain ⟨ε,hε,hbound⟩ := uniform_scaling_sublevels T hT hexpand
  let B := C-(d-1)*((3/2)*Real.log ε)
  let a := Real.exp (-2*B/3)
  let b := Real.exp (2*B-4*Real.log ε)
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 ≤ b := (Real.exp_pos _).le
  let K := spectralWindow d a b
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_spectralWindow (d := d) ha.le hb)
  have hmem (y : Y) : (⟨P y,(hP y).1.1⟩ : HermitianMatrices d) ∈ K := by
    apply hbound C y (P y) (hP y).1
    exact ((hP y).2 1 Matrix.PosDef.one).trans (hC ⟨y,rfl⟩)
  let m : Y → K := fun y => ⟨⟨P y,(hP y).1.1⟩,hmem y⟩
  let g : Y × K → ℝ := fun z => scalingPotential (T z.1) z.2.val.val
  have hg : Continuous g :=
    continuous_scalingPotential (fun z : Y × K => T z.1) (hT.comp continuous_fst)
      (fun z : Y × K => z.2.val.val)
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
      (fun z => spectralWindow_posDef ha z.2.property)
  have hm : Continuous m := by
    apply continuous_unique_minimizer g hg m
    · intro y z
      exact (hP y).2 z.val.val (spectralWindow_posDef ha z.property)
    · intro y z hz
      have hglob : ∀ Q : Matrix (Fin d) (Fin d) ℂ, Q.PosDef →
          scalingPotential (T y) z.val.val ≤ scalingPotential (T y) Q := by
        intro Q hQ
        exact (hz (m y)).trans ((hP y).2 Q hQ)
      have he := scaling_minimizer_unique (T y) (hexpand y)
        (spectralWindow_posDef ha z.property) (hP y).1 hglob (hP y).2
      apply Subtype.ext
      exact Subtype.ext he
  refine ⟨P,?_,hP⟩
  exact continuous_subtype_val.comp (continuous_subtype_val.comp hm)

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

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.MatrixScaling_Canonical
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unitary naturality and canonical local matrix scaling. -/

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

def canonicalMinimizer (T : Fin n → Matrix (Fin r) (Fin d) ℂ) (h : Expanding T) :
    Matrix (Fin d) (Fin d) ℂ := (existsUnique_scaling_minimizer T h).choose

theorem canonicalMinimizer_spec (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (h : Expanding T) : (canonicalMinimizer T h).PosDef ∧ ∀ R, R.PosDef →
      scalingPotential T (canonicalMinimizer T h) ≤ scalingPotential T R :=
  (existsUnique_scaling_minimizer T h).choose_spec.1

theorem canonicalMinimizer_frame (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    (h : Expanding T) (h' : Expanding (frameTuple T U V)) :
    canonicalMinimizer (frameTuple T U V) h' = U * canonicalMinimizer T h * Uᴴ := by
  have hp := canonicalMinimizer_spec T h
  have ht := scaling_minimizer_frame T U V hU hU' hV hV' _ hp.1 hp.2
  have hq := canonicalMinimizer_spec (frameTuple T U V) h'
  exact scaling_minimizer_unique _ h' hq.1 ht.1 hq.2 ht.2

def canonicalScaling (T : Fin n → Matrix (Fin r) (Fin d) ℂ) (h : Expanding T) :=
  normalizedTuple T (CFC.sqrt (canonicalMinimizer T h))
    (CFC.sqrt (1 + scalingMap T (canonicalMinimizer T h)))⁻¹

theorem canonicalScaling_relations (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (h : Expanding T) :
    (∑ i, (canonicalScaling T h i)ᴴ * canonicalScaling T h i) = 1 ∧
    ((2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
      ∑ i, canonicalScaling T h i * (canonicalScaling T h i)ᴴ).PosSemidef := by
  have hp := canonicalMinimizer_spec T h
  have hq := Matrix.PosDef.one.add_posSemidef (scalingMap_positive T hp.1.posSemidef)
  exact normalizedTuple_of_minimizer T hp.1 hp.2 _ (matrix_sqrt_factor hp.1).1
    (matrix_sqrt_factor hp.1).2 _ (matrix_sqrt_factor hq).1 (matrix_sqrt_factor hq).2

/-- The normalized maps obey precisely the bundle transition law. -/
theorem canonicalScaling_frame (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    (h : Expanding T) (h' : Expanding (frameTuple T U V)) :
    canonicalScaling (frameTuple T U V) h' = frameTuple (canonicalScaling T h) U V := by
  have hp := (canonicalMinimizer_spec T h).1
  have hq := Matrix.PosDef.one.add_posSemidef (scalingMap_positive T hp.posSemidef)
  have he : 1 + V * scalingMap T (canonicalMinimizer T h) * Vᴴ =
      V * (1 + scalingMap T (canonicalMinimizer T h)) * Vᴴ := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hV']
  simp only [canonicalScaling, canonicalMinimizer_frame T U V hU hU' hV hV' h h',
    scalingMap_frame T U V hU, he, sqrt_unitary_conjugate U _ hU hp.posSemidef,
    sqrt_unitary_conjugate V _ hV hq.posSemidef, inverse_unitary_conjugate V _ hV hV']
  funext i
  simp only [normalizedTuple, frameTuple, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul,
    ← Matrix.mul_assoc Uᴴ U, hU]

/-- Continuity of the canonical, hence frame-compatible, choice. -/
theorem continuous_canonicalMinimizer {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (h : ∀ y, Expanding (T y)) : Continuous (fun y => canonicalMinimizer (T y) (h y)) := by
  obtain ⟨P,hP,hmin⟩ := exists_continuous_scaling_minimizer T hT h
  have he (y : Y) : canonicalMinimizer (T y) (h y) = P y := by
    have hp := canonicalMinimizer_spec (T y) (h y)
    exact scaling_minimizer_unique _ (h y) hp.1 (hmin y).1 hp.2 (hmin y).2
  simpa only [he] using hP

theorem continuous_canonicalScaling {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (h : ∀ y, Expanding (T y)) : Continuous (fun y => canonicalScaling (T y) (h y)) := by
  let P := fun y => canonicalMinimizer (T y) (h y)
  have hp := continuous_canonicalMinimizer T hT h
  have hp' := fun y => (canonicalMinimizer_spec (T y) (h y)).1
  let Q := fun y => 1 + scalingMap (T y) (P y)
  have hq : Continuous Q := continuous_const.add (continuous_scalingMap T hT P hp)
  have hq' : ∀ y, (Q y).PosDef := fun y =>
    Matrix.PosDef.one.add_posSemidef (scalingMap_positive (T y) (hp' y).posSemidef)
  have ha := continuous_matrix_sqrt P hp hp'
  have hb := continuous_matrix_sqrt Q hq hq'
  have hi := continuous_matrix_inverse _ hb (fun y => (matrix_sqrt_factor (hq' y)).1)
  apply continuous_pi
  intro i
  exact (continuous_const : Continuous (fun _ : Y => (Real.sqrt (2/3 : ℝ) : ℂ))).smul ((hi.matrix_mul ((continuous_apply i).comp hT)).matrix_mul ha)

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

theorem continuous_canonicalScaling_local {Y : Type*} [TopologicalSpace Y]
    [WeaklyLocallyCompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (h : ∀ y, Expanding (T y)) : Continuous (fun y => canonicalScaling (T y) (h y)) := by
  rw [continuous_iff_continuousAt]
  intro y
  obtain ⟨K,hK,hy⟩ := exists_compact_mem_nhds y
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc := continuous_canonicalScaling (fun z : K => T z.val)
    (hT.comp continuous_subtype_val) (fun z => h z.val)
  have hon : ContinuousOn (fun y => canonicalScaling (T y) (h y)) K :=
    continuousOn_iff_continuous_domRestrict.mpr hc
  exact (hon y (mem_of_mem_nhds hy)).continuousAt hy

end Kaplansky

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
open Matrix
namespace Kaplansky
variable {n d r : ℕ} {E F D R : Type*}
variable [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
variable [AddCommGroup D] [Module ℂ D] [AddCommGroup R] [Module ℂ R]

theorem intrinsicExpanding_equiv (T : Fin n → E →ₗ[ℂ] F)
    (e : E ≃ₗ[ℂ] D) (f : F ≃ₗ[ℂ] R) (hT : IntrinsicExpanding T) :
    IntrinsicExpanding (fun i => f.toLinearMap.comp ((T i).comp e.symm.toLinearMap)) := by
  intro S
  have h := hT (S.map e.symm.toLinearMap)
  rw [e.symm.finrank_map_eq] at h
  have he : (⨆ i, S.map (f.toLinearMap.comp ((T i).comp e.symm.toLinearMap)) : Submodule ℂ R) =
      (⨆ i, (S.map e.symm.toLinearMap).map (T i) : Submodule ℂ F).map f.toLinearMap := by
    rw [Submodule.map_iSup]
    apply iSup_congr
    intro i
    rw [Submodule.map_comp, Submodule.map_comp]
  rw [he, f.finrank_map_eq]
  exact h

theorem expanding_in_basis (T : Fin n → E →ₗ[ℂ] F)
    (b : Module.Basis (Fin d) ℂ E) (c : Module.Basis (Fin r) ℂ F)
    (hT : IntrinsicExpanding T) : Expanding (fun i => LinearMap.toMatrix b c (T i)) := by
  have h := intrinsicExpanding_equiv T b.equivFun c.equivFun hT
  have he : (fun i => (LinearMap.toMatrix b c (T i)).mulVecLin) =
      (fun i => c.equivFun.toLinearMap.comp ((T i).comp b.equivFun.symm.toLinearMap)) :=
    funext (fun i => basis_matrix_action b c (T i))
  change IntrinsicExpanding (fun i => (LinearMap.toMatrix b c (T i)).mulVecLin)
  rw [he]
  exact h

end Kaplansky

end

noncomputable section
namespace Kaplansky
variable {E F G H : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
  [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ H]

theorem combined_expanding (m : ℕ) (A : Fin 16 → E →ₗ[ℂ] F)
    (B : Fin 8 → E →ₗ[ℂ] G) (f : F →ₗ[ℂ] H) (g : G →ₗ[ℂ] H)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hA : ExpandingThrough m A)
    (hB : ∀ S : Submodule ℂ E, m<Module.finrank ℂ S →
      2*Module.finrank ℂ S≤Module.finrank ℂ (⨆ i, S.map (B i) : Submodule ℂ G)) :
    IntrinsicExpanding (Fin.addCases (fun i => f.comp (A i)) (fun i => g.comp (B i))) := by
  intro S
  by_cases hs : Module.finrank ℂ S ≤ m
  · exact (hA S hs).trans (image_iSup_finrank_le A _ f hf (Fin.castAdd 8) (by intro i; simp) S)
  · exact (hB S (by omega)).trans (image_iSup_finrank_le B _ g hg (Fin.natAdd 16) (by intro i; simp) S)

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
open Bundle Module Set
open scoped Topology Manifold ContDiff
namespace Kaplansky.Incidence
variable {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace B] [ChartedSpace X B]
  [IsManifold 𝓘(ℝ,X) ∞ B] [T2Space B] [CompactSpace B]
  {d r : ℕ} (E F : B → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (Fin d → ℂ) E)] [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
  [FiberBundle (Fin d → ℂ) E] [FiberBundle (Fin r → ℂ) F]
  [VectorBundle ℝ (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
  [VectorBundle ℝ (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]
  [ContMDiffVectorBundle ∞ (Fin d → ℂ) E 𝓘(ℝ,X)]
  [ContMDiffVectorBundle ∞ (Fin r → ℂ) F 𝓘(ℝ,X)]

theorem exists_eight_fresh_bundle_maps (m : ℕ) (hd : 0<d)
    (hr : 4*r=15*d) (hbase : 3*finrank ℝ X<40*m*d) :
    ∃ T : Fin 8 → ∀ y, E y →L[ℂ] F y,
      (∀ i, ContMDiff 𝓘(ℝ,X) (𝓘(ℝ,X).prod 𝓘(ℝ,(Fin d → ℂ) →L[ℝ] (Fin r → ℂ))) ∞
        (fun y => TotalSpace.mk' ((Fin d → ℂ) →L[ℝ] (Fin r → ℂ)) y ((T i y).restrictScalars ℝ))) ∧
      ∀ y (S : Submodule ℂ (E y)), m<finrank ℂ S →
        2*finrank ℂ S≤finrank ℂ (⨆ i, S.map (T i y).toLinearMap : Submodule ℂ (F y)) := by
  classical
  let pairs : Finset (ℕ × ℕ) := (Finset.Icc (m+1) d).image (fun s => (s,2*s))
  have hpairs : ∀ p ∈ pairs, p.1≤d ∧ p.2 ≤ r ∧
      finrank ℝ X+2*p.1*(d-p.1)+2*p.2*(r-p.2)<2*8*p.1*(r-p.2) := by
    intro p hp
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hms,hsd⟩ := Finset.mem_Icc.mp hs
    obtain ⟨htr,hgap⟩ := fresh_incidence_dimension m d r (finrank ℝ X) s hd hr hbase (by omega) hsd
    exact ⟨hsd,htr,hgap⟩
  obtain ⟨T,hT,hExp⟩ := exists_smooth_bundle_incidence_maps E F pairs hpairs
  refine ⟨T,hT,fun y S hS => ?_⟩
  let e := trivializationAt (Fin d → ℂ) E y
  let a := e.toPretrivialization.linearEquivAt ℂ y (mem_baseSet_trivializationAt (Fin d → ℂ) E y)
  have hsd : finrank ℂ S≤d := by
    have hh := (S.map a.toLinearMap).finrank_le
    simpa [a.finrank_map_eq,Module.finrank_pi_fintype] using hh
  have hp : (finrank ℂ S,2*finrank ℂ S) ∈ pairs :=
    Finset.mem_image.mpr ⟨finrank ℂ S,Finset.mem_Icc.mpr ⟨by omega,hsd⟩,rfl⟩
  exact (hExp y _ hp S rfl).le

end Kaplansky.Incidence

end

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky
variable {B : Type*} [TopologicalSpace B] {k : ℕ}
  {J : Fin k → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

def repeatedLineCore (D : Fin k → ℕ) := finiteLineSumCore (fun a : Σ s, Fin (D s) => C a.1)

def repeatedLineFiberEquiv (D : Fin k → ℕ) (x : B) :
    (repeatedLineCore C D).Fiber x ≃ₗ[ℂ] (∀ s, Fin (D s) → (C s).Fiber x) where
  toFun v s a := (show RepeatedLineModel D from v) ⟨s,a⟩
  invFun v := WithLp.toLp 2 (fun a => v a.1 a.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual bundle map obtained by tensoring each scalar block with its
line identity, expressed in the finite-sum core fibers. -/
def repeatedLineMap (D E : Fin k → ℕ)
    (T : ∀ s, (Fin (D s) → ℂ) →ₗ[ℂ] (Fin (E s) → ℂ)) (x : B) :
    (repeatedLineCore C D).Fiber x →ₗ[ℂ] (repeatedLineCore C E).Fiber x :=
  (repeatedLineFiberEquiv C E x).symm.toLinearMap.comp
    ((blockDiagonal (n := 1) (fun s _ => scalarTensor (L := (C s).Fiber x) (T s)) 0).comp
      (repeatedLineFiberEquiv C D x).toLinearMap)

@[simp] theorem repeatedLineMap_apply (D E : Fin k → ℕ)
    (T : ∀ s, (Fin (D s) → ℂ) →ₗ[ℂ] (Fin (E s) → ℂ)) (x : B)
    (v : (repeatedLineCore C D).Fiber x) (s : Fin k) (b : Fin (E s)) :
    (show RepeatedLineModel E from repeatedLineMap C D E T x v) ⟨s,b⟩ = ∑ a, T s (Pi.single a 1) b * (show RepeatedLineModel D from v) ⟨s,a⟩ := rfl

end Kaplansky

end

open Bundle Topology

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

namespace Kaplansky
open scoped BigOperators

theorem testProjectiveDimension_bound (m R : ℕ) (i : Fin R) :
    testProjectiveDimension m R i ≤ 5*m*testRank m R 0*4^i.val := by
  have h := Nat.mul_le_mul_left (320*m^2*4^(2*i.val)) (Nat.sub_le (4^(R-i.val)) 1)
  change testProjectiveDimension m R i ≤ _ at h
  have he : 2*i.val+(R-i.val)=R+i.val := by omega
  calc
    _ ≤ 320*m^2*4^(2*i.val)*4^(R-i.val) := h
    _ = 320*m^2*4^(R+i.val) := by rw [mul_assoc,← pow_add,he]
    _ = _ := by rw [testRank_eq]; simp only [Nat.add_zero,pow_add]; ring

/-- Exact prefix dimensions, retaining every later occurrence through R. -/
def testPrefixDimension (m R j : ℕ) (hj : j<R) : ℕ :=
  ∑ i : Fin (j+1), testProjectiveDimension m R (i.castLE hj)

end Kaplansky

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Projective
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.smoothLineSum_inner _root_.OAI.Kaplansky.ComplexGrassmann.smoothLineSum_norm _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Projection models of complex projective space and products. -/

section
open Topology Set
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

instance projectiveGrassmannCompact : CompactSpace (Grassmann 1 k) :=
  (projectiveProjectionHomeomorph k).compactSpace

end Kaplansky.ComplexGrassmann

open Topology Set
open scoped Manifold ContDiff BigOperators
namespace Kaplansky.ComplexGrassmann
variable {ι : Type*} [Fintype ι] (K : ι → ℕ)

abbrev ProjectiveProductModel := ∀ i, GraphSlope 1 (K i)

instance projectiveProductChartedSpace :
    ChartedSpace (ProjectiveProductModel K) (ProjectiveProduct K) :=
  inferInstanceAs (ChartedSpace (ModelPi (fun i => GraphSlope 1 (K i))) (ProjectiveProduct K))

instance projectiveProductRealManifold :
    IsManifold 𝓘(ℝ,ProjectiveProductModel K) ∞ (ProjectiveProduct K) := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨e,he,rfl⟩ ⟨f,hf,rfl⟩
  have he' : ∀ i, ∃ F : GraphFrame 1 (K i), grassmannChart F = e i := fun i => he i (mem_univ i)
  have hf' : ∀ i, ∃ F : GraphFrame 1 (K i), grassmannChart F = f i := fun i => hf i (mem_univ i)
  choose F hF using he'
  choose G hG using hf'
  have hfe : e = fun i => grassmannChart (F i) := funext (fun i => (hF i).symm)
  have hge : f = fun i => grassmannChart (G i) := funext (fun i => (hG i).symm)
  subst e; subst f
  simp only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.comp_def,id_eq,
    Set.range_id,Set.inter_univ,Set.preimage_id]
  apply contDiffOn_pi.mpr
  intro i
  have h := (grassmann_chart_transition_smooth (F i) (G i)).restrict_scalars ℝ
  apply h.comp ((ContinuousLinearMap.proj i : ProjectiveProductModel K →L[ℝ] GraphSlope 1 (K i)).contDiff.contDiffOn)
  intro A hA
  change A ∈ (OpenPartialHomeomorph.pi (fun i => grassmannChart (F i))).target ∧
    (OpenPartialHomeomorph.pi (fun i => grassmannChart (F i))).symm A ∈
      (OpenPartialHomeomorph.pi (fun i => grassmannChart (G i))).source at hA
  exact (inGraphChart_iff_unit (F i) (G i) (A i)).mp (hA.2 i (mem_univ i))

instance projectiveProductCompact : CompactSpace (ProjectiveProduct K) := inferInstance
instance projectiveProductT2 : T2Space (ProjectiveProduct K) := inferInstance

theorem projectiveProduct_real_finrank :
    Module.finrank ℝ (ProjectiveProductModel K) = 2*∑ i, K i := by
  rw [Module.finrank_pi_fintype]
  simp only [graph_slope_real_finrank,mul_one]
  exact (Finset.mul_sum ..).symm

end Kaplansky.ComplexGrassmann

end

open Topology Set
open scoped Manifold ContDiff
namespace Kaplansky.ComplexGrassmann
variable {ι : Type*} [Fintype ι] (K : ι → ℕ)

/-- Coordinate projections of the actual finite projective product are smooth. -/
theorem contMDiff_projectiveProduct_apply (i : ι) :
    ContMDiff 𝓘(ℝ,ProjectiveProductModel K) 𝓘(ℝ,GraphSlope 1 (K i)) ∞
      (fun P : ProjectiveProduct K => P i) := by
  intro P
  choose F hF using fun j => grassmann_atlas_covers (P j)
  let e := OpenPartialHomeomorph.pi (fun j => grassmannChart (F j))
  have he : e ∈ atlas (ProjectiveProductModel K) (ProjectiveProduct K) :=
    ⟨_,(fun j _ => Set.mem_range_self (F j)),rfl⟩
  have hP : P ∈ e.source := fun j _ => hF j
  have hchart : ContMDiffAt 𝓘(ℝ,ProjectiveProductModel K) 𝓘(ℝ,ProjectiveProductModel K) ∞ e P :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hP
  have hc := (ContinuousLinearMap.proj i : ProjectiveProductModel K →L[ℝ] GraphSlope 1 (K i)).contDiff.contDiffAt.contMDiffAt.comp P hchart
  have hi : grassmannChart (F i) ∈ IsManifold.maximalAtlas 𝓘(ℝ,GraphSlope 1 (K i)) ∞ (Grassmann 1 (K i)) :=
    IsManifold.subset_maximalAtlas (Set.mem_range_self (F i))
  have hs := contMDiffAt_symm_of_mem_maximalAtlas hi
    (show e P i ∈ (grassmannChart (F i)).target by simp)
  apply (hs.comp P hc).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hP] with Q hQ
  exact ((grassmannChart (F i)).left_inv (hQ i (mem_univ i))).symm

end Kaplansky.ComplexGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_RealModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

variable {S : Type*} [Fintype S]

variable {B : Type*} [TopologicalSpace B] {J : S → Type*}
  (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

omit [Fintype S] in
theorem lineSumTransition_eq_diagonal (a b : ∀ s, J s) (x : B) :
    lineSumTransition C a b x = lineDiagonal (fun s => (C s).coordChange (a s) (b s) x 1) := by
  ext v s
  change (C s).coordChange (a s) (b s) x (v s) =
    ((C s).coordChange (a s) (b s) x 1)*(v s)
  have h := map_smul ((C s).coordChange (a s) (b s) x) (v s) (1 : ℂ)
  simpa only [smul_eq_mul,mul_one,one_mul,mul_comm] using h

end Kaplansky

end

open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
variable {B F G J : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  (C : VectorBundleCore ℂ B F J) (e : F ≃L[ℂ] G)

theorem changeModelCore_transition_smooth
    {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace H]
    (I : ModelWithCorners ℝ X H) [ChartedSpace H B]
    (hC : ∀ a b, ContMDiffOn I 𝓘(ℝ,F →L[ℂ] F) ∞ (C.coordChange a b)
      (C.baseSet a ∩ C.baseSet b)) (a b : J) :
    ContMDiffOn I 𝓘(ℝ,G →L[ℂ] G) ∞ ((changeModelCore C e).coordChange a b)
      ((changeModelCore C e).baseSet a ∩ (changeModelCore C e).baseSet b) := by
  let L : (F →L[ℂ] F) →L[ℂ] (G →L[ℂ] G) :=
    (ContinuousLinearMap.compL ℂ G F G e.toContinuousLinearMap).comp
      ((ContinuousLinearMap.compL ℂ G F F).flip e.symm.toContinuousLinearMap)
  intro x hx
  exact (L.restrictScalars ℝ).contDiff.contDiffAt.contMDiffAt.comp_contMDiffWithinAt x (hC a b x hx)

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
open Matrix Topology
open scoped Manifold ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

theorem contDiff_graphLineVector (F : GraphFrame 1 k) : ContDiff ℝ ∞ (graphLineVector F) := by
  have h : ContDiff ℂ ∞ (graphLineVector F) := by
    apply (EuclideanSpace.equiv (Fin (1+k)) ℂ).symm.contDiff.comp
    apply F.symm.toContinuousLinearEquiv.contDiff.comp
    exact contDiff_const.prodMk (contDiff_id.clm_apply contDiff_const)
  exact h.restrict_scalars ℝ

theorem contDiff_vectorOuter {d : ℕ} : ContDiff ℝ ∞ (vectorOuter (d := d)) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have hi : ContDiff ℝ ∞ (fun v : EuclideanSpace ℂ (Fin d) => v i) :=
    ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  have hj : ContDiff ℝ ∞ (fun v : EuclideanSpace ℂ (Fin d) => v j) :=
    ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  exact hi.mul (Complex.conjCLE.contDiff.comp hj)

theorem contDiff_graphLineProjection_val (F : GraphFrame 1 k) :
    ContDiff ℝ ∞ (fun A => (graphLineProjection F A).val) := by
  apply contDiff_vectorOuter.comp
  exact (((contDiff_graphLineVector F).norm ℂ (graphLineVector_ne_zero F)).inv
    (fun A => norm_ne_zero_iff.mpr (graphLineVector_ne_zero F A))).smul (contDiff_graphLineVector F)

attribute [local instance] OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceMatrixFinHAddNatOfNatComplex_solutions
/-- The actual projector matrix of a line is a smooth function on complex
projective space, viewed as a real manifold. -/
theorem contMDiff_projectiveProjection_matrix :
    ContMDiff 𝓘(ℝ,GraphSlope 1 k) 𝓘(ℝ,Matrix (Fin (1+k)) (Fin (1+k)) ℂ) ∞
      (fun P : Grassmann 1 k => ((projectiveProjectionEquiv k).symm P).val) := by
  intro P
  obtain ⟨F,hF⟩ := grassmann_atlas_covers P
  have hchart : ContMDiffAt 𝓘(ℝ,GraphSlope 1 k) 𝓘(ℝ,GraphSlope 1 k) ∞ (grassmannChart F) P :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (Set.mem_range_self F)) hF
  have hc := (contDiff_graphLineProjection_val F).contDiffAt.contMDiffAt.comp P hchart
  apply hc.congr_of_eventuallyEq
  filter_upwards [(grassmannChart F).open_source.mem_nhds hF] with Q hQ
  have he : (projectiveProjectionEquiv k).symm Q = graphLineProjection F (grassmannChart F Q) := by
    apply (projectiveProjectionEquiv k).injective
    rw [Equiv.apply_symm_apply]
    exact ((graphLineProjection_point F _).trans (slopePoint_coordinate F Q hQ)).symm
  exact congrArg Subtype.val he

end Kaplansky.ComplexGrassmann

end

section
open Bundle Topology NormedSpace
open scoped Manifold ContDiff Matrix.Norms.Elementwise
namespace Kaplansky.ComplexGrassmann
variable {k : ℕ}

theorem contMDiff_projectiveColumn (i : Fin (1+k)) :
    ContMDiff 𝓘(ℝ,GraphSlope 1 k) 𝓘(ℝ,EuclideanSpace ℂ (Fin (1+k))) ∞
      (fun P => projectionColumn (projectiveProjectionMap k P) i) := by
  intro P
  exact ((matrixColumnLinear i).toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.contMDiffAt.comp P
    (contMDiff_projectiveProjection_matrix P)

theorem contMDiffOn_projectiveUnitColumn (i : Fin (1+k)) :
    ContMDiffOn 𝓘(ℝ,GraphSlope 1 k) 𝓘(ℝ,EuclideanSpace ℂ (Fin (1+k))) ∞
      (fun P => unitProjectionColumn (projectiveProjectionMap k P) i)
      ((projectiveHyperplaneCore k).baseSet i) := by
  intro P hP
  exact ((contDiffAt_normalize hP).contMDiffAt.comp P (contMDiff_projectiveColumn i P)).contMDiffWithinAt

/-- The actual dual tautological-line transitions are real smooth. -/
theorem projectiveHyperplaneCore_transition_smooth (a b : Fin (1+k)) :
    ContMDiffOn 𝓘(ℝ,GraphSlope 1 k) 𝓘(ℝ,ℂ →L[ℂ] ℂ) ∞
      ((projectiveHyperplaneCore k).coordChange a b)
      ((projectiveHyperplaneCore k).baseSet a ∩ (projectiveHyperplaneCore k).baseSet b) := by
  intro P hP
  have ha := ((contMDiffOn_projectiveUnitColumn a).mono Set.inter_subset_left) P hP
  have hb := ((contMDiffOn_projectiveUnitColumn b).mono Set.inter_subset_right) P hP
  have hi := (contDiff_inner (𝕜 := ℂ)).contDiffAt.contMDiffAt.comp_contMDiffWithinAt P (hb.prodMk_space ha)
  have hs := Complex.conjCLE.contDiff.contDiffAt.contMDiffAt.comp_contMDiffWithinAt P hi
  let g : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (ContinuousLinearMap.id ℂ ℂ)
  exact (g.restrictScalars ℝ).contDiff.contDiffAt.contMDiffAt.comp_contMDiffWithinAt P hs

end Kaplansky.ComplexGrassmann

end

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky.ComplexGrassmann

section
variable {ι : Type*} [Fintype ι] (K : ι → ℕ)

theorem productLineCore_transition_smooth (i : Option ι)
    (a b : productLineChartIndex K i) :
    ContMDiffOn 𝓘(ℝ,ProjectiveProductModel K) 𝓘(ℝ,ℂ →L[ℂ] ℂ) ∞
      ((productLineCore K i).coordChange a b)
      ((productLineCore K i).baseSet a ∩ (productLineCore K i).baseSet b) := by
  cases i with
  | none => exact contMDiffOn_const
  | some i =>
    exact (projectiveHyperplaneCore_transition_smooth a b).comp
      (contMDiff_projectiveProduct_apply K i).contMDiffOn (fun _ hx => hx)

end

end Kaplansky.ComplexGrassmann

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Smooth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Smooth bases and test bundles with replacement maps. -/

section
open Topology
open scoped Manifold ContDiff BigOperators
namespace Kaplansky
open ComplexGrassmann

abbrev SmoothPrefixModel (m R j : ℕ) (hj : j<R) :=
  ProjectiveProductModel (fun i : Fin (j+1) => testProjectiveDimension m R (i.castLE hj))

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky

abbrev TestReplacementModel (m R j : ℕ) := RepeatedLineModel (testReplacementMultiplicity m R j)

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Frames
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Hermitian frames, synthesis, and unitary transition functions. -/

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Bundle Topology
namespace Kaplansky
variable {d : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E : Y → Type*} [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]

theorem bundleChartBasis_apply (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
    [e.IsLinear ℂ] (y : Y) (hy : y ∈ e.baseSet) (i : Fin d) :
    bundleChartBasis e y hy i = bundleChartFrame e y i := by
  simp [bundleChartBasis, bundleChartFrame, hy]

theorem bundleChartFrame_independent (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
    [e.IsLinear ℂ] (y : Y) (hy : y ∈ e.baseSet) :
    LinearIndependent ℂ (bundleChartFrame e y) := by
  have he : (bundleChartBasis e y hy : Fin d → E y) = bundleChartFrame e y :=
    funext (bundleChartBasis_apply e y hy)
  rw [← he]
  exact (bundleChartBasis e y hy).linearIndependent

theorem continuousOn_bundleChartFrame
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ] (i : Fin d) :
    ContinuousOn (fun y => TotalSpace.mk' (Fin d → ℂ) y (bundleChartFrame e y i)) e.baseSet := by
  have hc := e.continuousOn_symm.comp (continuousOn_id.prodMk continuousOn_const)
    (show Set.MapsTo (fun y : Y => (y, (Pi.single i (1 : ℂ) : Fin d → ℂ))) e.baseSet
      (e.baseSet ×ˢ Set.univ) from fun y hy => ⟨hy, Set.mem_univ _⟩)
  apply hc.congr
  intro y hy
  simp [bundleChartFrame, hy, Trivialization.mk_symm]

theorem continuousOn_bundleGram
    (hm : ContinuousHermitianMetric (d := d) (E := E))
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ] :
    ContinuousOn (fun y => gram ℂ (bundleChartFrame e y)) e.baseSet := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact hm e.baseSet (fun y => bundleChartFrame e y i) (fun y => bundleChartFrame e y j)
    (continuousOn_bundleChartFrame e i) (continuousOn_bundleChartFrame e j)

/-- The actual orthonormal frame on the chart, extended by zero outside. -/
def bundleOrthonormalFrame
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ] (y : Y) : Fin d → E y :=
  metricFrame (bundleChartFrame e y)

theorem bundleOrthonormalFrame_eq
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ] (y : Y) (j : Fin d) :
    bundleOrthonormalFrame e y j =
      e.symmₗ ℂ y (fun i => (CFC.sqrt (gram ℂ (bundleChartFrame e y)))⁻¹ i j) := by
  unfold bundleOrthonormalFrame metricFrame frameMul bundleChartFrame
  simp only [← map_smul, ← map_sum]
  congr 1
  classical
  ext k
  simp [Pi.single_apply]

def bundleOrthonormalBasis
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ]
    (y : Y) (hy : y ∈ e.baseSet) : OrthonormalBasis (Fin d) ℂ (E y) :=
  metricBasis (bundleChartBasis e y hy)

theorem bundleOrthonormalBasis_apply
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ]
    (y : Y) (hy : y ∈ e.baseSet) (i : Fin d) :
    bundleOrthonormalBasis e y hy i = bundleOrthonormalFrame e y i := by
  rw [bundleOrthonormalBasis, metricBasis_apply]
  congr 2
  funext j
  exact bundleChartBasis_apply e y hy j

theorem continuousOn_bundleOrthonormalFrame
    (hm : ContinuousHermitianMetric (d := d) (E := E))
    (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [e.IsLinear ℂ] (j : Fin d) :
    ContinuousOn (fun y => TotalSpace.mk' (Fin d → ℂ) y (bundleOrthonormalFrame e y j))
      e.baseSet := by
  have hG := continuousOn_bundleGram hm e
  have hc : ContinuousOn (fun y => (CFC.sqrt (gram ℂ (bundleChartFrame e y)))⁻¹) e.baseSet := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_metricFrame_coefficients _
      (continuousOn_iff_continuous_domRestrict.mp hG)
      (fun y => Matrix.posDef_gram_of_linearIndependent (bundleChartFrame_independent e y y.property))
  have hv : ContinuousOn (fun y i => (CFC.sqrt (gram ℂ (bundleChartFrame e y)))⁻¹ i j)
      e.baseSet := by
    apply continuousOn_pi.mpr
    intro i
    exact (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc)
  have hh := e.continuousOn_symm.comp (continuousOn_id.prodMk hv)
    (show Set.MapsTo (fun y => (y, fun i => (CFC.sqrt (gram ℂ (bundleChartFrame e y)))⁻¹ i j))
      e.baseSet (e.baseSet ×ˢ Set.univ) from fun y hy => ⟨hy, Set.mem_univ _⟩)
  apply hh.congr
  intro y hy
  simp [bundleOrthonormalFrame_eq, hy]

end Kaplansky

end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Bundle Topology
namespace Kaplansky
variable {d : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E : Y → Type*} [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]

/-- Transition from the orthonormalization of chart a to that of chart b. -/
def bundleUnitaryTransition
    (a b : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [a.IsLinear ℂ] [b.IsLinear ℂ]
    (y : Y) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => inner ℂ (bundleOrthonormalFrame b y i) (bundleOrthonormalFrame a y j)

theorem bundleUnitaryTransition_eq
    (a b : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [a.IsLinear ℂ] [b.IsLinear ℂ]
    (y : Y) (ha : y ∈ a.baseSet) (hb : y ∈ b.baseSet) :
    bundleUnitaryTransition a b y =
      (bundleOrthonormalBasis b y hb).toBasis.toMatrix (bundleOrthonormalBasis a y ha) := by
  ext i j
  simp only [bundleUnitaryTransition, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    bundleOrthonormalBasis_apply]

theorem bundleUnitaryTransition_unitary
    (a b : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [a.IsLinear ℂ] [b.IsLinear ℂ]
    (y : Y) (ha : y ∈ a.baseSet) (hb : y ∈ b.baseSet) :
    (bundleUnitaryTransition a b y)ᴴ * bundleUnitaryTransition a b y = 1 ∧
      bundleUnitaryTransition a b y * (bundleUnitaryTransition a b y)ᴴ = 1 := by
  rw [bundleUnitaryTransition_eq a b y ha hb]
  exact ⟨OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self _ _,
    OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose _ _⟩

theorem bundleUnitaryTransition_self
    (a : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [a.IsLinear ℂ]
    (y : Y) (ha : y ∈ a.baseSet) : bundleUnitaryTransition a a y = 1 := by
  rw [bundleUnitaryTransition_eq a a y ha ha]
  exact (bundleOrthonormalBasis a y ha).toBasis.toMatrix_self

theorem bundleUnitaryTransition_comp
    (a b c : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
    [a.IsLinear ℂ] [b.IsLinear ℂ] [c.IsLinear ℂ]
    (y : Y) (ha : y ∈ a.baseSet) (hb : y ∈ b.baseSet) (hc : y ∈ c.baseSet) :
    bundleUnitaryTransition b c y * bundleUnitaryTransition a b y =
      bundleUnitaryTransition a c y := by
  rw [bundleUnitaryTransition_eq b c y hb hc, bundleUnitaryTransition_eq a b y ha hb,
    bundleUnitaryTransition_eq a c y ha hc]
  exact Module.Basis.toMatrix_mul_toMatrix
    (bundleOrthonormalBasis c y hc).toBasis (bundleOrthonormalBasis b y hb).toBasis
    (bundleOrthonormalBasis a y ha)

theorem continuousOn_bundleUnitaryTransition
    (hm : ContinuousHermitianMetric (d := d) (E := E))
    (a b : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E)) [a.IsLinear ℂ] [b.IsLinear ℂ] :
    ContinuousOn (bundleUnitaryTransition a b) (a.baseSet ∩ b.baseSet) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact hm _ (fun y => bundleOrthonormalFrame b y i) (fun y => bundleOrthonormalFrame a y j)
    ((continuousOn_bundleOrthonormalFrame hm b i).mono Set.inter_subset_right)
    ((continuousOn_bundleOrthonormalFrame hm a j).mono Set.inter_subset_left)

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

section
open Bundle Topology Module
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann

abbrev TestFreshCoordinates (m R j : ℕ) (hj : j<R) :=
  FiniteCoordinateBundle (stageProjectiveDimensions m R (j+1) hj)
    (fun _ : Fin (TestFreshRank m R j) => some (Fin.last j))
    (TestFreshRank m R j) (Fintype.card_fin _)

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Hom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
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

section
variable {n d r : ℕ} {Y I : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y]

theorem canonicalScaling_congr {T S : Fin n → Matrix (Fin r) (Fin d) ℂ}
    (he : T = S) (hT : Expanding T) (hS : Expanding S) :
    canonicalScaling T hT = canonicalScaling S hS := by
  cases he
  rfl

/-- Local normalization with harmless zero values outside a chart. -/
def chartScaling (H : VectorBundleCore ℂ Y (Fin n → Matrix (Fin r) (Fin d) ℂ) I)
    (T : I → Y → Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexp : ∀ a y, y ∈ H.baseSet a → Expanding (T a y)) (a : I) (y : Y) := by
  classical
  exact if hy : y ∈ H.baseSet a then canonicalScaling (T a y) (hexp a y hy) else 0

theorem continuousOn_chartScaling
    (H : VectorBundleCore ℂ Y (Fin n → Matrix (Fin r) (Fin d) ℂ) I)
    (T : I → Y → Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hT : ∀ a, ContinuousOn (T a) (H.baseSet a))
    (hexp : ∀ a y, y ∈ H.baseSet a → Expanding (T a y)) (a : I) :
    ContinuousOn (chartScaling H T hexp a) (H.baseSet a) := by
  classical
  let : LocallyCompactSpace (H.baseSet a) := (H.isOpen_baseSet a).locallyCompactSpace
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := continuous_canonicalScaling_local (fun z : H.baseSet a => T a z.val)
    (continuousOn_iff_continuous_domRestrict.mp (hT a)) (fun z => hexp a z.val z.property)
  apply hc.congr
  intro z
  change canonicalScaling (T a z.val) _ = chartScaling H T hexp a z.val
  rw [chartScaling, dite_eq_left z.property]

theorem exists_scaled_core_section
    (H : VectorBundleCore ℂ Y (Fin n → Matrix (Fin r) (Fin d) ℂ) I)
    (T : I → Y → Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hT : ∀ a, ContinuousOn (T a) (H.baseSet a))
    (hexp : ∀ a y, y ∈ H.baseSet a → Expanding (T a y))
    (U : I → I → Y → Matrix (Fin d) (Fin d) ℂ)
    (V : I → I → Y → Matrix (Fin r) (Fin r) ℂ)
    (hunit : ∀ a b y, y ∈ H.baseSet a → y ∈ H.baseSet b →
      (U a b y)ᴴ * U a b y = 1 ∧ U a b y * (U a b y)ᴴ = 1 ∧
      (V a b y)ᴴ * V a b y = 1 ∧ V a b y * (V a b y)ᴴ = 1)
    (hcore : ∀ a b y, y ∈ H.baseSet a → y ∈ H.baseSet b → ∀ M,
      H.coordChange a b y M = frameTuple M (U a b y) (V a b y))
    (hcompat : ∀ a b y, y ∈ H.baseSet a → y ∈ H.baseSet b →
      T b y = frameTuple (T a y) (U a b y) (V a b y)) :
    ∃ s : ∀ y, H.Fiber y,
      Continuous (fun y => TotalSpace.mk' (Fin n → Matrix (Fin r) (Fin d) ℂ) y (s y)) ∧
      ∀ a y, y ∈ H.baseSet a →
        let X := (H.localTriv a ⟨y,s y⟩).2
        (∑ i, (X i)ᴴ * X i) = 1 ∧
        ((2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - ∑ i, X i * (X i)ᴴ).PosSemidef := by
  classical
  have hg : ∀ a b y, y ∈ H.baseSet a → y ∈ H.baseSet b →
      H.coordChange a b y (chartScaling H T hexp a y) = chartScaling H T hexp b y := by
    intro a b y ha hb
    rw [chartScaling, dite_eq_left ha, chartScaling, dite_eq_left hb, hcore a b y ha hb]
    obtain ⟨hu,hu',hv,hv'⟩ := hunit a b y ha hb
    have ht := hcompat a b y ha hb
    have he := canonicalScaling_frame (T a y) (U a b y) (V a b y) hu hu' hv hv'
      (hexp a y ha) (ht ▸ hexp b y hb)
    exact he.symm.trans (canonicalScaling_congr ht.symm _ _)
  obtain ⟨s,hs,he⟩ := glue_core_section H (chartScaling H T hexp)
    (continuousOn_chartScaling H T hT hexp) hg
  refine ⟨s,hs,?_⟩
  intro a y hy
  rw [he a y hy]
  simpa only [chartScaling, dite_eq_left hy] using canonicalScaling_relations (T a y) (hexp a y hy)

end

end Kaplansky

end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky
variable {n d r : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E F : Y → Type*}
variable [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℂ (F y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]
variable [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
variable [FiberBundle (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
variable [FiberBundle (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]

def hermitianSourceTransition (a b : Y) :=
  bundleUnitaryTransition (trivializationAt (Fin d → ℂ) E a) (trivializationAt (Fin d → ℂ) E b)

def hermitianTargetTransition (a b : Y) :=
  bundleUnitaryTransition (trivializationAt (Fin r → ℂ) F a) (trivializationAt (Fin r → ℂ) F b)

/-- The Hom-tuple core is constructed from ordinary Hermitian bundles.
The charts, orthonormalizations, transition matrices, and cocycle proofs
are derived here; no unitary core is an input. -/
def hermitianHomCore
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F)) :
    VectorBundleCore ℂ Y (Fin n → Matrix (Fin r) (Fin d) ℂ) Y :=
  matrixHomCore (hermitianChartSet (d := d) (r := r) (E := E) (F := F))
    (fun a => (trivializationAt (Fin d → ℂ) E a).open_baseSet.inter
      (trivializationAt (Fin r → ℂ) F a).open_baseSet)
    id (fun y => ⟨mem_baseSet_trivializationAt (Fin d → ℂ) E y,
      mem_baseSet_trivializationAt (Fin r → ℂ) F y⟩)
    (hermitianSourceTransition (d := d) (E := E)) (hermitianTargetTransition (r := r) (F := F))
    (fun _ _ => (continuousOn_bundleUnitaryTransition hE _ _).mono
      (fun _ h => ⟨h.1.1,h.2.1⟩))
    (fun _ _ => (continuousOn_bundleUnitaryTransition hF _ _).mono
      (fun _ h => ⟨h.1.2,h.2.2⟩))
    (fun _ y h => bundleUnitaryTransition_self _ y h.1)
    (fun _ y h => bundleUnitaryTransition_self _ y h.2)
    (fun _ _ _ y ha hb hc => bundleUnitaryTransition_comp _ _ _ y ha.1 hb.1 hc.1)
    (fun _ _ _ y ha hb hc => bundleUnitaryTransition_comp _ _ _ y ha.2 hb.2 hc.2)

theorem hermitianHomCore_coordChange
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F)) (a b y : Y)
    (T : Fin n → Matrix (Fin r) (Fin d) ℂ) :
    (hermitianHomCore hE hF).coordChange a b y T =
      frameTuple T (hermitianSourceTransition (d := d) (E := E) a b y)
        (hermitianTargetTransition (r := r) (F := F) a b y) := rfl

theorem hermitianHomCore_unitary (a b y : Y)
    (ha : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a)
    (hb : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) b) :
    let U := hermitianSourceTransition (d := d) (E := E) a b y
    let V := hermitianTargetTransition (r := r) (F := F) a b y
    Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ Vᴴ * V = 1 ∧ V * Vᴴ = 1 := by
  obtain ⟨hu,hu'⟩ := bundleUnitaryTransition_unitary
    (trivializationAt (Fin d → ℂ) E a) (trivializationAt (Fin d → ℂ) E b) y ha.1 hb.1
  obtain ⟨hv,hv'⟩ := bundleUnitaryTransition_unitary
    (trivializationAt (Fin r → ℂ) F a) (trivializationAt (Fin r → ℂ) F b) y ha.2 hb.2
  exact ⟨hu,hu',hv,hv'⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Coordinates
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Coordinates and realization of Hermitian scaling sections. -/

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky
variable {n d r : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E F : Y → Type*}
variable [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℂ (F y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]
variable [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
variable [FiberBundle (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
variable [FiberBundle (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]

/-- Coordinates of genuine fiber maps in the constructed orthonormal frames. -/
def bundleMapCoordinates (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a y : Y) :
    Fin n → Matrix (Fin r) (Fin d) ℂ :=
  fun i k j => inner ℂ
    (bundleOrthonormalFrame (trivializationAt (Fin r → ℂ) F a) y k)
    (T y i (bundleOrthonormalFrame (trivializationAt (Fin d → ℂ) E a) y j))

theorem bundleMapCoordinates_eq (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a y : Y)
    (hy : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a) (i : Fin n) :
    bundleMapCoordinates (d := d) (r := r) T a y i = LinearMap.toMatrix
      (bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E a) y hy.1).toBasis
      (bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F a) y hy.2).toBasis (T y i) := by
  ext k j
  simp only [bundleMapCoordinates, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.coe_toBasis, bundleOrthonormalBasis_apply]

theorem continuousOn_bundleMapCoordinates
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y)
    (hT : ∀ i, Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (T z.proj i z.2))) (a : Y) :
    ContinuousOn (bundleMapCoordinates (d := d) (r := r) T a) (hermitianChartSet (d := d) (r := r) (E := E) (F := F) a) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro k
  apply continuousOn_pi.mpr
  intro j
  apply hF
  · exact (continuousOn_bundleOrthonormalFrame hF _ k).mono Set.inter_subset_right
  · exact (hT i).comp_continuousOn
      ((continuousOn_bundleOrthonormalFrame hE _ j).mono Set.inter_subset_left)

theorem bundleMapCoordinates_expanding
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (hT : ∀ y, IntrinsicExpanding (T y))
    (a y : Y) (hy : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a) :
    Expanding (bundleMapCoordinates (d := d) (r := r) T a y) := by
  have he : bundleMapCoordinates (d := d) (r := r) T a y = fun i => LinearMap.toMatrix
      (bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E a) y hy.1).toBasis
      (bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F a) y hy.2).toBasis (T y i) :=
    funext (bundleMapCoordinates_eq T a y hy)
  rw [he]
  exact expanding_in_basis _ _ _ (hT y)

theorem bundleUnitaryTransition_star
    {k : ℕ} {V : Y → Type*} [∀ y, NormedAddCommGroup (V y)] [∀ y, InnerProductSpace ℂ (V y)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) V)]
    [FiberBundle (Fin k → ℂ) V] [VectorBundle ℂ (Fin k → ℂ) V]
    (a b : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) V)) [a.IsLinear ℂ] [b.IsLinear ℂ]
    (y : Y) : (bundleUnitaryTransition a b y)ᴴ = bundleUnitaryTransition b a y := by
  apply Matrix.ext
  intro i j
  exact inner_conj_symm _ _

theorem bundleMapCoordinates_compatible
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a b y : Y)
    (ha : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a)
    (hb : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) b) :
    bundleMapCoordinates (d := d) (r := r) T b y = frameTuple (bundleMapCoordinates (d := d) (r := r) T a y)
      (hermitianSourceTransition (d := d) (E := E) a b y)
      (hermitianTargetTransition (r := r) (F := F) a b y) := by
  funext i
  dsimp only [frameTuple, hermitianSourceTransition, hermitianTargetTransition]
  rw [bundleUnitaryTransition_star, bundleMapCoordinates_eq T a y ha i,
    bundleMapCoordinates_eq T b y hb i,
    bundleUnitaryTransition_eq _ _ y hb.1 ha.1,
    bundleUnitaryTransition_eq _ _ y ha.2 hb.2]
  symm
  exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    (bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E b) y hb.1).toBasis
    (bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E a) y ha.1).toBasis
    (bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F b) y hb.2).toBasis
    (bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F a) y ha.2).toBasis (T y i)

/-- Interpret a section of the constructed core as linear maps between
its original bundles, using the core's selected chart in each fiber. -/
def realizeHomSection
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (s : ∀ y, (hermitianHomCore (n := n) hE hF).Fiber y) (y : Y) (i : Fin n) :
    E y →ₗ[ℂ] F y :=
  Matrix.toLin
    (bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E y) y
      (mem_baseSet_trivializationAt (Fin d → ℂ) E y)).toBasis
    (bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F y) y
      (mem_baseSet_trivializationAt (Fin r → ℂ) F y)).toBasis (s y i)

theorem realizeHomSection_at
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (s : ∀ y, (hermitianHomCore (n := n) hE hF).Fiber y) (y : Y) :
    bundleMapCoordinates (d := d) (r := r) (realizeHomSection hE hF s) y y = s y := by
  funext i
  rw [bundleMapCoordinates_eq _ y y (mem_hermitianChartSet (d := d) (r := r) y) i]
  exact LinearMap.toMatrix_toLin _ _ (s y i)

theorem realizeHomSection_coordinates
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (s : ∀ y, (hermitianHomCore (n := n) hE hF).Fiber y) (a y : Y)
    (hy : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a) :
    bundleMapCoordinates (d := d) (r := r) (realizeHomSection hE hF s) a y =
      ((hermitianHomCore hE hF).localTriv a ⟨y,s y⟩).2 := by
  rw [bundleMapCoordinates_compatible _ y a y
    (mem_hermitianChartSet (d := d) (r := r) y) hy, realizeHomSection_at]
  rfl

theorem continuousOn_realizeHomSection_coordinates
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (s : ∀ y, (hermitianHomCore (n := n) hE hF).Fiber y)
    (hs : Continuous (fun y => TotalSpace.mk' (Fin n → Matrix (Fin r) (Fin d) ℂ) y (s y)))
    (a : Y) :
    ContinuousOn (bundleMapCoordinates (d := d) (r := r) (realizeHomSection hE hF s) a)
      (hermitianChartSet (d := d) (r := r) (E := E) (F := F) a) := by
  have hc := ((hermitianHomCore hE hF).localTriv a).continuousOn.comp hs.continuousOn
    (show Set.MapsTo (fun y => TotalSpace.mk' (Fin n → Matrix (Fin r) (Fin d) ℂ) y (s y))
      (hermitianChartSet (d := d) (r := r) (E := E) (F := F) a)
      ((hermitianHomCore hE hF).localTriv a).source from fun y hy =>
        ((hermitianHomCore hE hF).localTriv a).mem_source.mpr hy)
  exact hc.snd.congr (fun y hy => realizeHomSection_coordinates hE hF s a y hy)

end Kaplansky

end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky
variable {n d r : ℕ} {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y]
variable {E F : Y → Type*}
variable [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℂ (F y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]
variable [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
variable [FiberBundle (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
variable [FiberBundle (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]

/-- Normalization of intrinsic expanding maps descends in the constructed
Hom-tuple bundle. The ordinary input bundles may be nontrivial. -/
theorem exists_hermitian_scaled_section
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y)
    (hT : ∀ i, Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (T z.proj i z.2)))
    (hexp : ∀ y, IntrinsicExpanding (T y)) :
    ∃ s : ∀ y, (hermitianHomCore (n := n) hE hF).Fiber y,
      Continuous (fun y => TotalSpace.mk' (Fin n → Matrix (Fin r) (Fin d) ℂ) y (s y)) ∧
      ∀ a y, y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a →
        let X := ((hermitianHomCore hE hF).localTriv a ⟨y,s y⟩).2
        (∑ i, (X i)ᴴ * X i) = 1 ∧
        ((2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - ∑ i, X i * (X i)ᴴ).PosSemidef := by
  exact exists_scaled_core_section (hermitianHomCore hE hF)
    (bundleMapCoordinates (d := d) (r := r) T)
    (continuousOn_bundleMapCoordinates hE hF T hT)
    (bundleMapCoordinates_expanding T hexp)
    (hermitianSourceTransition (d := d) (E := E))
    (hermitianTargetTransition (r := r) (F := F))
    (hermitianHomCore_unitary (d := d) (r := r))
    (fun a b y _ _ M => hermitianHomCore_coordChange hE hF a b y M)
    (bundleMapCoordinates_compatible T)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Maps
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Continuous bundle maps, adjoints, and normalized Hermitian scaling. -/

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky
variable {n d r : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E F : Y → Type*}
variable [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℂ (F y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]
variable [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
variable [FiberBundle (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
variable [FiberBundle (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]

theorem bundleMap_apply_eq
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a y : Y)
    (hy : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a)
    (i : Fin n) (v : E y) :
    T y i v = ∑ k, (∑ j, bundleMapCoordinates (d := d) (r := r) T a y i k j *
      inner ℂ (bundleOrthonormalFrame (trivializationAt (Fin d → ℂ) E a) y j) v) •
      bundleOrthonormalFrame (trivializationAt (Fin r → ℂ) F a) y k := by
  simp only [bundleMapCoordinates_eq T a y hy i]
  let b := bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E a) y hy.1
  let c := bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F a) y hy.2
  have he := congrArg (fun L : E y →ₗ[ℂ] F y => L v)
    (Matrix.toLin_toMatrix b.toBasis c.toBasis (T y i))
  rw [Matrix.toLin_apply] at he
  symm
  simpa only [Matrix.mulVec, dotProduct, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, b, c,
    bundleOrthonormalBasis_apply] using he

/-- Continuous coordinate matrices act continuously on local sections of
the original bundles. -/
theorem continuousOn_bundleMap_apply_section
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a : Y) {s : Set Y}
    (hsub : s ⊆ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a)
    (hT : ContinuousOn (bundleMapCoordinates (d := d) (r := r) T a) s)
    (v : ∀ y, E y) (hv : ContinuousOn (fun y => TotalSpace.mk' (Fin d → ℂ) y (v y)) s)
    (i : Fin n) :
    ContinuousOn (fun y => TotalSpace.mk' (Fin r → ℂ) y (T y i (v y))) s := by
  have hc : ContinuousOn (fun y => TotalSpace.mk' (Fin r → ℂ) y
      (∑ k, (∑ j, bundleMapCoordinates (d := d) (r := r) T a y i k j *
        inner ℂ (bundleOrthonormalFrame (trivializationAt (Fin d → ℂ) E a) y j) (v y)) •
        bundleOrthonormalFrame (trivializationAt (Fin r → ℂ) F a) y k)) s := by
    apply continuousOn_bundle_sum (𝕜 := ℂ)
    intro k _
    apply continuousOn_bundle_smul
    · apply continuousOn_finsetSum
      intro j _
      have hm := (continuous_apply j).comp_continuousOn
        ((continuous_apply k).comp_continuousOn ((continuous_apply i).comp_continuousOn hT))
      exact hm.mul (hE s _ v
        ((continuousOn_bundleOrthonormalFrame hE _ j).mono (fun _ hy => (hsub hy).1)) hv)
    · exact (continuousOn_bundleOrthonormalFrame hF _ k).mono (fun _ hy => (hsub hy).2)
  apply hc.congr
  intro y hy
  exact congrArg (TotalSpace.mk' (Fin r → ℂ) y) (bundleMap_apply_eq T a y (hsub hy) i (v y))

theorem bundleChartFrame_sum (a : Y) (y : Y)
    (hy : y ∈ (trivializationAt (Fin d → ℂ) E a).baseSet) (v : E y) :
    (∑ j, ((trivializationAt (Fin d → ℂ) E a) ⟨y,v⟩).2 j •
      bundleChartFrame (trivializationAt (Fin d → ℂ) E a) y j) = v := by
  let b := bundleChartBasis (trivializationAt (Fin d → ℂ) E a) y hy
  have he := b.sum_repr v
  simpa [b, bundleChartBasis, bundleChartFrame, hy] using he

/-- Continuity on the actual total spaces follows from the constructed
coordinate matrices. No simultaneous trivialization is assumed. -/
theorem continuous_bundleMap_of_coordinates
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y)
    (hT : ∀ a, ContinuousOn (bundleMapCoordinates (d := d) (r := r) T a)
      (hermitianChartSet (d := d) (r := r) (E := E) (F := F) a)) (i : Fin n) :
    Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (T z.proj i z.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let a := z₀.proj
  let e := trivializationAt (Fin d → ℂ) E a
  let O := hermitianChartSet (d := d) (r := r) (E := E) (F := F) a
  let S : Set (TotalSpace (Fin d → ℂ) E) := π (Fin d → ℂ) E ⁻¹' O
  have hp : Continuous (π (Fin d → ℂ) E) := FiberBundle.continuous_proj (Fin d → ℂ) E
  have hO : IsOpen O := e.open_baseSet.inter (trivializationAt (Fin r → ℂ) F a).open_baseSet
  have hz₀ : z₀ ∈ S := mem_hermitianChartSet (d := d) (r := r) a
  have hec : ContinuousOn e S := e.continuousOn.mono
    (fun z hz => e.mem_source.mpr hz.1)
  have hsec (j : Fin d) : ContinuousOn
      (fun y => TotalSpace.mk' (Fin r → ℂ) y (T y i (bundleChartFrame e y j))) O :=
    continuousOn_bundleMap_apply_section hE hF T a (Set.Subset.refl _) (hT a)
      (fun y => bundleChartFrame e y j)
      ((continuousOn_bundleChartFrame e j).mono Set.inter_subset_left) i
  have hc : ContinuousOn (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj
        (∑ j, (e z).2 j • T z.proj i (bundleChartFrame e z.proj j))) S := by
    apply continuousOn_bundle_sum_over (𝕜 := ℂ) _ hp.continuousOn
    intro j _
    apply continuousOn_bundle_smul_over _ hp.continuousOn
    · exact (continuous_apply j).comp_continuousOn hec.snd
    · exact (hsec j).comp hp.continuousOn (fun _ hz => hz)
  have hc' : ContinuousOn (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (T z.proj i z.2)) S := by
    apply hc.congr
    intro z hz
    apply congrArg (TotalSpace.mk' (Fin r → ℂ) z.proj)
    simp only [← map_smul, ← map_sum]
    exact congrArg (T z.proj i) (bundleChartFrame_sum a z.proj hz.1 z.2).symm
  exact (hc' z₀ hz₀).continuousAt ((hO.preimage hp).mem_nhds hz₀)

theorem continuous_realizeHomSection
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (s : ∀ y, (hermitianHomCore (n := n) hE hF).Fiber y)
    (hs : Continuous (fun y => TotalSpace.mk' (Fin n → Matrix (Fin r) (Fin d) ℂ) y (s y)))
    (i : Fin n) :
    Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (realizeHomSection hE hF s z.proj i z.2)) :=
  continuous_bundleMap_of_coordinates hE hF _ (continuousOn_realizeHomSection_coordinates hE hF s hs) i

theorem bundleAdjoint_coordinates (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a y : Y)
    (hy : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a) (i : Fin n) :
    bundleMapCoordinates (d := r) (r := d) (bundleAdjoint (d := d) (r := r) T) a y i =
      (bundleMapCoordinates (d := d) (r := r) T a y i)ᴴ := by
  let := bundleFiberFiniteDimensional (d := d) (E := E) y
  let := bundleFiberFiniteDimensional (d := r) (E := F) y
  rw [bundleMapCoordinates_eq _ a y ⟨hy.2,hy.1⟩ i, bundleMapCoordinates_eq _ a y hy i]
  exact LinearMap.toMatrix_adjoint
    (bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E a) y hy.1)
    (bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F a) y hy.2) (T y i)

theorem continuous_bundleAdjoint
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y)
    (hT : ∀ i, Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (T z.proj i z.2))) (i : Fin n) :
    Continuous (fun z : TotalSpace (Fin r → ℂ) F =>
      TotalSpace.mk' (Fin d → ℂ) z.proj (bundleAdjoint (d := d) (r := r) T z.proj i z.2)) := by
  apply continuous_bundleMap_of_coordinates hF hE _ _ i
  intro a
  apply continuousOn_pi.mpr
  intro k
  have hc := (continuousOn_bundleMapCoordinates hE hF T hT a).mono
    (show hermitianChartSet (d := r) (r := d) (E := F) (F := E) a ⊆
      hermitianChartSet (d := d) (r := r) (E := E) (F := F) a from fun _ h => ⟨h.2,h.1⟩)
  have hh : ContinuousOn (fun y => (bundleMapCoordinates (d := d) (r := r) T a y k)ᴴ)
      (hermitianChartSet (d := r) (r := d) (E := F) (F := E) a) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (((continuous_apply k).comp (continuousOn_iff_continuous_domRestrict.mp hc))).matrix_conjTranspose
  exact hh.congr (fun y hy => bundleAdjoint_coordinates T a y ⟨hy.2,hy.1⟩ k)

end Kaplansky

end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky
variable {n d r : ℕ} {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y]
variable {E F : Y → Type*}
variable [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℂ (F y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]
variable [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
variable [FiberBundle (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
variable [FiberBundle (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]

theorem exists_continuous_normalized_bundle_maps
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y)
    (hT : ∀ i, Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (T z.proj i z.2)))
    (hexp : ∀ y, IntrinsicExpanding (T y)) :
    ∃ X : ∀ y, Fin n → E y →ₗ[ℂ] F y,
      (∀ i, Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
        TotalSpace.mk' (Fin r → ℂ) z.proj (X z.proj i z.2))) ∧
      (∀ i, Continuous (fun z : TotalSpace (Fin r → ℂ) F =>
        TotalSpace.mk' (Fin d → ℂ) z.proj (bundleAdjoint (d := d) (r := r) X z.proj i z.2))) ∧
      ∀ y, (∑ i, (bundleAdjoint (d := d) (r := r) X y i).comp (X y i)) = LinearMap.id ∧
        ∀ v : F y, 0 ≤ inner ℂ v (((2/3 : ℂ) • (LinearMap.id : F y →ₗ[ℂ] F y) -
          ∑ i, (X y i).comp (bundleAdjoint (d := d) (r := r) X y i)) v) := by
  obtain ⟨s,hs,hr⟩ := exists_hermitian_scaled_section hE hF T hT hexp
  let X := realizeHomSection hE hF s
  have hX := continuous_realizeHomSection hE hF s hs
  refine ⟨X,hX,continuous_bundleAdjoint hE hF X hX,?_⟩
  intro y
  let := bundleFiberFiniteDimensional (d := d) (E := E) y
  let := bundleFiberFiniteDimensional (d := r) (E := F) y
  have hy := mem_hermitianChartSet (d := d) (r := r) (E := E) (F := F) y
  let b := bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E y) y hy.1
  let c := bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F y) y hy.2
  have he : ((hermitianHomCore hE hF).localTriv y ⟨y,s y⟩).2 =
      fun i => LinearMap.toMatrix b.toBasis c.toBasis (X y i) := by
    rw [← realizeHomSection_coordinates hE hF s y y hy]
    exact funext (bundleMapCoordinates_eq X y y hy)
  have hm := hr y y hy
  dsimp only at hm
  rw [he] at hm
  exact intrinsic_relations_of_matrix b c (X y) hm.1 hm.2

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_ProjectiveClass
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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

def coordinatePunctureFactor (P : ProjectiveProduct K) (T : Finset ι) (i : ι) :=
  {Q : Grassmann 1 (K i) // i ∈ T → Q ≠ P i}

end ComplexGrassmann

end

open CategoryTheory Limits

end Kaplansky

end

end OAI
end


