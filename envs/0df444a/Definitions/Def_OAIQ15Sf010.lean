-- Prove2me | Definitions.Def_OAIQ15Sf010
-- name    : OAIQ15Sf010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:29:58.141255+00:00
-- url     : https://prove2.me/theorems/c3f2ea3e-e797-421f-b64c-1b583011dd30
-- title:
--   Definitions bundle OAIQ15Sf010 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 218 declarations of OpenAI's Lean: 103 definitions, 20 instances and 95 theorems. The definitions and types are `OAI.Kaplansky.ActualAlgebra`, `OAI.Kaplansky.ComplexGrassmann.coordinatePunctureFactorHomotopyEquiv`, `OAI.Kaplansky.ComplexGrassmann.coordinatePunctureIntersectionHomeomorph`, `OAI.Kaplansky.ComplexGrassmann.coordinatePunctureIntersectionHomotopyEquiv`, `OAI.Kaplansky.ComplexGrassmann.productGraphDenominatorLinear`, `OAI.Kaplansky.ComplexGrassmann.projectiveProductGraphChart`, `OAI.Kaplansky.ComplexGrassmann.projectiveProductGraphHomeomorph`, `OAI.Kaplansky.ComplexGrassmann.projectiveProductGraphIntersection`, `OAI.Kaplansky.ComplexGrassmann.projectiveProductGraphIntersectionHomeomorph`, `OAI.Kaplansky.ContinuousOrthonormalStageFrame.congr`, `OAI.Kaplansky.Incidence.ChartBad`, `OAI.Kaplansky.Incidence.PointBad`, `OAI.Kaplansky.Incidence.graphFamily`, `OAI.Kaplansky.RetainedBundle`, `OAI.Kaplansky.SemigroupOrderedGroup`, `OAI.Kaplansky.actualBoundedGenerator`, `OAI.Kaplansky.actualMatrixRestriction`, `OAI.Kaplansky.actualMatrixStageMap`, `OAI.Kaplansky.actualRepresentation`, `OAI.Kaplansky.actualRetainedUnitary`, `OAI.Kaplansky.actualTestOperator`, `OAI.Kaplansky.bundleMatrixPolynomial`, `OAI.Kaplansky.bundleMatrixTerm`, `OAI.Kaplansky.bundleTestBasePoint`, `OAI.Kaplansky.bundleWordValue`, `OAI.Kaplansky.canonicalChartExcisionIso`, `OAI.Kaplansky.canonicalChartRelativeInclusion`, `OAI.Kaplansky.canonicalChartSmallRelativeIso`, `OAI.Kaplansky.canonicalChartSphereHomologyIso`, `OAI.Kaplansky.canonicalLocalRelativeHomologyIso`, `OAI.Kaplansky.canonicalLocalSectionHomeomorph`, `OAI.Kaplansky.canonicalProductChartHomeomorph`, `OAI.Kaplansky.canonicalProductGraphChart`, `OAI.Kaplansky.canonicalProductGraphPoint`, `OAI.Kaplansky.canonicalProductLocalGenerator`, `OAI.Kaplansky.canonicalProductLocalHomologyIso`, `OAI.Kaplansky.firstCoordinateProduct`, `OAI.Kaplansky.inputMatrixHilbertIsometry`, `OAI.Kaplansky.inputMatrixHilbertMap`, `OAI.Kaplansky.lineSumRelabelUnitary` and 63 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: `BundleTests_Assembly`, `BundleTests_Base`, `BundleTests_Complement`, `BundleTests_Normalization`, `BundleTests_Normalized`, `BundleTests_Obstruction`, `BundleTests_Retained`, `BundleTests_Sequence`, `BundleTests_Smooth`, `BundleTests_Twisted`, `ComplexBundle_Avoidance`, `ComplexBundle_CoordinatesMetric`, `ComplexBundle_GrassmannManifold`, `ComplexBundle_Hyperplane`, `ComplexBundle_HyperplaneProduct`, `ComplexBundle_Incidence`, `ComplexBundle_PointExpansion`, `ComplexBundle_RealModel`, `ComplexBundle_Replacement`, `ComplexBundle_SmoothLine`, `ComplexBundle_StageMaps`, `ComplexBundle_ZeroSign`, `Cuntz_Distribution`, `IntegralHomology_Excision`, `IntegralHomology_GraphCover`, `IntegralHomology_HyperplaneLocal`, `IntegralHomology_ProjectiveClass`, `IntegralHomology_ProjectiveLocal`, `IntegralHomology_Sphere`, `IntegralHomology_Thom`, `Kaplansky_BundlePolynomials`, `Kaplansky_BundleWords`, `Kaplansky_MatrixImage`, `Kaplansky_Products`, `Kaplansky_StableFiniteness_FaithfulRepresentation`, `Kaplansky_TestAlgebra`, `Kaplansky_Ultrapower_Construction`, `Kaplansky_Words`, `OrderedStates_Semigroup`.
--
--   **Imports.** It imports the bundles `OAIQ15Sf006`, `OAIQ15Sf007` and `OAIQ15Sf008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ15Sf012`; the statements `OAI.KaplanskyConsequences.actualAlgebra_no_tracialState`, `OAI.Kaplansky.actualAlgebra_matrix_not_properlyInfinite` and `OAI.Kaplansky.retainedGrouped_no_test_frame`; the proofs of `OAI.KaplanskyConsequences.actualAlgebra_no_tracialState`, `OAI.KaplanskyConsequences.separable_extraction`, `OAI.Kaplansky.actualAlgebra_matrix_not_properlyInfinite` and `OAI.Kaplansky.retainedGrouped_no_test_frame`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ15Sf006
import Definitions.Def_OAIQ15Sf007
import Definitions.Def_OAIQ15Sf008

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_GrassmannManifold
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpacePunctureHyperplane _root_.OAI.Kaplansky.ComplexGrassmann.projectiveGrassmannCompact _root_.OAI.Kaplansky.ComplexGrassmann.projectiveGrassmannT2 _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductChartedSpace _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductCompact _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductRealManifold _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductT2 _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.lineStage_finite _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
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

instance grassmannComplexManifold : IsManifold 𝓘(ℂ, GraphSlope s k) ∞ (Grassmann s k) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨F,rfl⟩ ⟨G,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, Set.range_id,Set.inter_univ,Set.preimage_id,
    grassmann_overlap_source,OpenPartialHomeomorph.trans_apply] using
    grassmann_chart_transition_smooth F G

end Kaplansky.ComplexGrassmann

end

open Set Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Incidence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductChartedSpace _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductRealManifold _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Linear incidence equations and their graph-coordinate kernel bundles. -/

open scoped ContDiff Manifold
namespace Kaplansky.Incidence
open ComplexGrassmann SmoothKernel
variable {s k t l q : ℕ}

variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable (ev : Y → V →L[ℂ] TupleAmbient q s k t l)

set_option synthInstance.maxHeartbeats 200000 in
theorem graphEvaluation_smooth (he : ContDiff ℝ ∞ ev) : ContDiff ℝ ∞ (graphEvaluation ev) := by
  have hc : ContDiff ℂ ∞ (fun p :
      (TupleAmbient q s k t l →L[ℂ] TupleTarget q s l) × (V →L[ℂ] TupleAmbient q s k t l) =>
      p.1.comp p.2) := contDiff_fst.clm_comp contDiff_snd
  exact (hc.restrict_scalars ℝ).comp
    (((tupleGraphRestriction_smooth (q := q) (s := s) (k := k) (t := t) (l := l)).restrict_scalars ℝ).comp
      contDiff_snd |>.prodMk (he.comp contDiff_fst))

def graphFamily (he : ContDiff ℝ ∞ ev) (hs : ∀ y, Function.Surjective (ev y)) :
    SurjectiveFamily (Y × (GraphSlope s k × GraphSlope t l)) V (TupleTarget q s l) where
  map := graphEvaluation ev
  continuous := (graphEvaluation_smooth ev he).continuous
  surjective p := (tupleGraphRestriction_surjective p.2.1 p.2.2).comp (hs p.1)

end Kaplansky.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Avoidance
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpacePunctureHyperplane _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductChartedSpace _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductRealManifold _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Avoidance of lower-dimensional incidence images in local manifold charts. -/

section
open scoped ContDiff MeasureTheory
open Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann SmoothKernel
variable {s k t l q h : ℕ}
variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable (ev : Y → V →L[ℂ] TupleAmbient q s k t l)

omit [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] in
theorem evaluation_target_rank_le (hs : ∀ y, Function.Surjective (ev y)) :
    q*s*l ≤ finrank ℂ V := by
  let A := graphEvaluation ev (0,(0,0))
  have ha : Function.Surjective A :=
    (tupleGraphRestriction_surjective 0 0).comp (hs 0)
  have hr := A.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr ha,finrank_top,tupleTarget_finrank] at hr
  omega

theorem graph_incidence_dimension_gap (hs : ∀ y, Function.Surjective (ev y))
    (hY : finrank ℝ Y=2*h) (hgap : h+s*k+t*l<q*s*l) :
    finrank ℝ ((Y × (GraphSlope s k × GraphSlope t l)) × KernelModel V (TupleTarget q s l))<
      finrank ℝ V := by
  rw [incidence_model_finrank,hY,finrank_real_of_complex]
  have hm := evaluation_target_rank_le ev hs
  simp only [Nat.mul_assoc] at *
  omega

/-- On one pair of Grassmann graph charts, the actual bad-parameter locus is
null under exactly the incidence dimension gap. -/
theorem graph_incidence_image_null [MeasurableSpace V] [BorelSpace V]
    (he : ContDiff ℝ ∞ ev) (hs : ∀ y, Function.Surjective (ev y))
    (hY : finrank ℝ Y=2*h) (hgap : h+s*k+t*l<q*s*l) :
    μH[finrank ℝ V] {v : V | ∃ (y : Y) (a : GraphSlope s k) (b : GraphSlope t l), ∀ i, ∀ x ∈ a.toLinearMap.graph,
      ev y v i x ∈ b.toLinearMap.graph}=0 := by
  have hn := (graphFamily ev he hs).kernel_incidence_image_null
    (graphEvaluation_smooth ev he) (graph_incidence_dimension_gap ev hs hY hgap)
  have heq : {v : V | ∃ p, (graphFamily ev he hs).map p v=0}=
      {v : V | ∃ (y : Y) (a : GraphSlope s k) (b : GraphSlope t l), ∀ i, ∀ x ∈ a.toLinearMap.graph, ev y v i x ∈ b.toLinearMap.graph} := by
    ext v
    simp only [Set.mem_ofPred_eq,graphFamily,graphEvaluation_zero_iff,Prod.exists]
  rw [heq] at hn
  exact hn

end Kaplansky.Incidence

end

open scoped ContDiff MeasureTheory
open Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann
variable {s k t l q : ℕ}

def ChartBad (F : GraphFrame s k) (G : GraphFrame t l) : Set (TupleOperators q s k t l) :=
  {T | ∃ (a : GraphSlope s k) (b : GraphSlope t l),
    ∀ i, ∀ x ∈ graphPlane F a.toLinearMap, T i x ∈ graphPlane G b.toLinearMap}

/-- The actual bad tuples in any pair of graph charts form a null set over a
point; no restriction is placed on the positions of the two charts. -/
theorem chartBad_null (F : GraphFrame s k) (G : GraphFrame t l)
    [MeasurableSpace (TupleOperators q s k t l)] [BorelSpace (TupleOperators q s k t l)]
    (hgap : s*k+t*l<q*s*l) : μH[finrank ℝ (TupleOperators q s k t l)] (ChartBad (q := q) F G)=0 := by
  let ev : (Fin 0 → ℝ) → TupleOperators q s k t l →L[ℂ] TupleAmbient q s k t l :=
    fun _ => frameEvaluation F G
  have hn := graph_incidence_image_null (h := 0) ev contDiff_const
    (fun _ => frameEvaluation_surjective F G) (by simp) (by simpa using hgap)
  have he : {T : TupleOperators q s k t l | ∃ (y : Fin 0 → ℝ)
      (a : GraphSlope s k) (b : GraphSlope t l), ∀ i, ∀ x ∈ a.toLinearMap.graph,
      ev y T i x ∈ b.toLinearMap.graph}=ChartBad F G := by
    ext T
    constructor
    · rintro ⟨_,a,b,hab⟩
      exact ⟨a,b,(frame_incidence_iff F G T a b).mpr hab⟩
    · rintro ⟨a,b,hab⟩
      exact ⟨0,a,b,(frame_incidence_iff F G T a b).mp hab⟩
  rw [he] at hn
  exact hn

end Kaplansky.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_PointExpansion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpacePunctureHyperplane _root_.OAI.Kaplansky.ComplexGrassmann.projectiveGrassmannCompact _root_.OAI.Kaplansky.ComplexGrassmann.projectiveGrassmannT2 _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductChartedSpace _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductCompact _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductRealManifold _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductT2 _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.lineStage_finite _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-point incidence avoidance and expansion inequalities. -/

section
open scoped MeasureTheory
open Set Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann
variable {q s k t l : ℕ}

def PointBad : Set (TupleOperators q s k t l) :=
  {T | ∃ (P : Grassmann s k) (Q : Grassmann t l), ∀ i, ∀ x ∈ P.val, T i x ∈ Q.val}

/-- The full bad locus over a point is null, across ALL s-planes and t-planes.
The countable graph cover is constructed from the actual Grassmann spaces. -/
theorem pointBad_null [MeasurableSpace (TupleOperators q s k t l)]
    [BorelSpace (TupleOperators q s k t l)] (hgap : s*k+t*l<q*s*l) :
    μH[finrank ℝ (TupleOperators q s k t l)] (PointBad (q := q) (s := s) (k := k) (t := t) (l := l))=0 := by
  obtain ⟨c,hc,hcover⟩ := exists_countable_graph_cover (s := s) (k := k)
  obtain ⟨d,hd,hcover'⟩ := exists_countable_graph_cover (s := t) (k := l)
  let := hc.toEncodable
  let := hd.toEncodable
  have hn (i : c × d) : μH[finrank ℝ (TupleOperators q s k t l)] (ChartBad i.1.val i.2.val)=0 :=
    chartBad_null i.1.val i.2.val hgap
  apply measure_mono_null (t := ⋃ i : c × d, ChartBad i.1.val i.2.val) ?_ (measure_iUnion_null hn)
  rintro T ⟨P,Q,hPQ⟩
  obtain ⟨F,hFc,hF⟩ := hcover P
  obtain ⟨G,hGd,hG⟩ := hcover' Q
  apply mem_iUnion.mpr
  refine ⟨(⟨F,hFc⟩,⟨G,hGd⟩),slopeCoordinate F P,slopeCoordinate G Q,?_⟩
  have hp : graphPlane F (slopeCoordinate F P).toLinearMap=P.val :=
    congrArg Subtype.val (slopePoint_coordinate F P hF)
  have hq : graphPlane G (slopeCoordinate G Q).toLinearMap=Q.val :=
    congrArg Subtype.val (slopePoint_coordinate G Q hG)
  rw [hp,hq]
  exact hPQ

end Kaplansky.Incidence

end

open scoped MeasureTheory
open Set Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann

theorem rankBad_null {q d r s t : ℕ} [MeasurableSpace (MatrixTuple q d r)]
    [BorelSpace (MatrixTuple q d r)] (hsd : s≤d) (htr : t ≤ r)
    (hgap : s*(d-s)+t*(r-t)<q*s*(r-t)) :
    μH[finrank ℝ (MatrixTuple q d r)] (RankBad (q := q) (d := d) (r := r) s t)=0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hsd
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le htr
  have he : RankBad (q := q) (d := s+k) (r := t+l) s t=
      PointBad (q := q) (s := s) (k := k) (t := t) (l := l) := by
    ext T
    constructor
    · rintro ⟨S,hS,U,hU,h⟩
      exact ⟨⟨S,hS⟩,⟨U,hU⟩,h⟩
    · rintro ⟨⟨S,hS⟩,⟨U,hU⟩,h⟩
      exact ⟨S,hS,U,hU,h⟩
  rw [he]
  exact pointBad_null (by simpa using hgap)

theorem exists_point_incidence_tuple {q d r : ℕ} (pairs : Finset (ℕ × ℕ))
    (hpairs : ∀ p ∈ pairs, p.1≤d ∧ p.2 ≤ r ∧
      p.1*(d-p.1)+p.2*(r-p.2)<q*p.1*(r-p.2)) :
    ∃ T : MatrixTuple q d r, ∀ p ∈ pairs, ∀ S : Submodule ℂ (Fin d → ℂ),
      finrank ℂ S=p.1 → p.2<finrank ℂ (⨆ i, S.map (T i).toLinearMap : Submodule ℂ (Fin r → ℂ)) := by
  borelize (MatrixTuple q d r)
  have hn : μH[finrank ℝ (MatrixTuple q d r)] (⋃ p ∈ pairs, RankBad (q := q) (d := d) (r := r) p.1 p.2)=0 :=
    measure_iUnion_null (fun p => measure_iUnion_null (fun hp =>
      rankBad_null (hpairs p hp).1 (hpairs p hp).2.1 (hpairs p hp).2.2))
  have hev : ∃ T : MatrixTuple q d r, T ∉ ⋃ p ∈ pairs, RankBad (q := q) (d := d) (r := r) p.1 p.2 := by
    by_contra h
    push Not at h
    have hu : (⋃ p ∈ pairs, RankBad (q := q) (d := d) (r := r) p.1 p.2)=univ := Set.eq_univ_of_forall h
    rw [hu] at hn
    have hp : 0<μH[finrank ℝ (MatrixTuple q d r)] (univ : Set (MatrixTuple q d r)) :=
      isOpen_univ.measure_pos _ Set.univ_nonempty
    exact (ne_of_gt hp) hn
  obtain ⟨T,hT⟩ := hev
  refine ⟨T,fun p hp S hS => ?_⟩
  by_contra h
  have hd : finrank ℂ (⨆ i, S.map (T i).toLinearMap : Submodule ℂ (Fin r → ℂ))≤p.2 := by omega
  obtain ⟨U,hWU,hU⟩ := exists_super_finrank
    (⨆ i, S.map (T i).toLinearMap : Submodule ℂ (Fin r → ℂ)) hd
      (by simpa using (hpairs p hp).2.1)
  apply hT
  refine Set.mem_iUnion.mpr ⟨p,Set.mem_iUnion.mpr ⟨hp,S,hS,U,hU,?_⟩⟩
  intro i x hx
  apply hWU
  apply (le_iSup (fun i => S.map (T i).toLinearMap) i)
  exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

end Kaplansky.Incidence

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
open Module
namespace Kaplansky.Incidence

theorem exists_sixteen_replacement_maps (m r : ℕ) (hm : 0 < m) (hr : 16*m ≤ r) :
    ∃ T : MatrixTuple 16 (4*r) r, ∀ S : Submodule ℂ (Fin (4*r) → ℂ),
      finrank ℂ S ≤ m → 2*finrank ℂ S≤
        finrank ℂ (⨆ i, S.map (T i).toLinearMap : Submodule ℂ (Fin r → ℂ)) := by
  let pairs : Finset (ℕ × ℕ) := (Finset.Icc 1 m).image (fun s => (s,2*s))
  have hpairs : ∀ p ∈ pairs, p.1≤4*r ∧ p.2 ≤ r ∧
      p.1*(4*r-p.1)+p.2*(r-p.2)<16*p.1*(r-p.2) := by
    intro p hp
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hp
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hsm : s ≤ m := (Finset.mem_Icc.mp hs).2
    have hsd : s≤4*r := by omega
    have htr : 2*s ≤ r := by omega
    refine ⟨hsd,htr,?_⟩
    apply (point_dimension_inequality_iff (q := 16) hsd htr).mp
    have hi := (Kaplansky.small_incidence (m : ℝ) (s : ℝ) (4*(r : ℝ))
      (by exact_mod_cast hm) (by exact_mod_cast (show 0 < s by omega)) (by exact_mod_cast hsm)
      (by exact_mod_cast (show 64*m≤4*r by omega))).1
    have hi' : 0<((16 : ℝ)*s-2*s)*(r-2*s)-(s : ℝ)*(4*r-s) := by
      convert hi using 1 <;> first | rfl | ring
    exact_mod_cast hi'
  obtain ⟨T,hT⟩ := exists_point_incidence_tuple pairs hpairs
  refine ⟨T,fun S hS => ?_⟩
  by_cases hz : finrank ℂ S=0
  · simp [hz]
  · have hs1 : 1≤finrank ℂ S := by omega
    have hp : (finrank ℂ S,2*finrank ℂ S) ∈ pairs :=
      Finset.mem_image.mpr ⟨finrank ℂ S,Finset.mem_Icc.mpr ⟨hs1,hS⟩,rfl⟩
    exact (hT _ hp S rfl).le

end Kaplansky.Incidence

end

section
open Bundle Module
open scoped Topology Manifold ContDiff
namespace Kaplansky

/-- The same scalar choices work simultaneously over every base point,
including for nontrivial line bundles; fiber coordinates are not input. -/
theorem exists_uniform_line_block_replacements {B : Type*}
    (k m : ℕ) (hm : 0 < m) (r : Fin k → ℕ) (hr : ∀ j, 16*m ≤ r j)
    (L : Fin k → B → Type*)
    [∀ j x, AddCommGroup (L j x)] [∀ j x, Module ℂ (L j x)]
    [∀ j x, FiniteDimensional ℂ (L j x)]
    (hL : ∀ j x, finrank ℂ (L j x)=1) :
    ∃ T : ∀ j, Incidence.MatrixTuple 16 (4*r j) (r j),
      ∀ x, ExpandingThrough m
        (blockDiagonal (fun j i => scalarTensor (L := L j x) (T j i).toLinearMap)) := by
  choose T hT using fun j => Incidence.exists_sixteen_replacement_maps m (r j) hm (hr j)
  exact ⟨T,fun x => expandingThrough_blocks k m (fun j => Fin (4*r j) → L j x)
    (fun j => Fin (r j) → L j x) _
    (fun j => scalarTensor_expanding_rank_one (hL j x) m (fun i => (T j i).toLinearMap) (hT j))⟩

end Kaplansky

end

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky
variable {B : Type*} [TopologicalSpace B] {k : ℕ}
  {J : Fin k → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

/-- The local chart formula is exactly the same scalar tensor expression.
In particular it contains no arbitrary choice of line frame. -/
theorem repeatedLineMap_chart (D E : Fin k → ℕ)
    (T : ∀ s, (Fin (D s) → ℂ) →ₗ[ℂ] (Fin (E s) → ℂ)) (x y : B)
    (v : (repeatedLineCore C D).Fiber y) (s : Fin k) (b : Fin (E s)) :
    ((trivializationAt (RepeatedLineModel E) (repeatedLineCore C E).Fiber x)
      ⟨y,repeatedLineMap C D E T y v⟩).2 ⟨s,b⟩ =
    ∑ a, T s (Pi.single a 1) b *
      ((trivializationAt (RepeatedLineModel D) (repeatedLineCore C D).Fiber x) ⟨y,v⟩).2 ⟨s,a⟩ := by
  change (C s).coordChange ((C s).indexAt y) ((C s).indexAt x) y
    (∑ a, T s (Pi.single a 1) b • (show RepeatedLineModel D from v) ⟨s,a⟩) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact map_smul _ _ _

/-- Componentwise smooth-section formulas alone do not establish this
claim: the map on the actual finite-sum total spaces is continuous. -/
theorem continuous_repeatedLineMap (D E : Fin k → ℕ)
    (T : ∀ s, (Fin (D s) → ℂ) →ₗ[ℂ] (Fin (E s) → ℂ)) :
    Continuous (fun z : TotalSpace (RepeatedLineModel D) (repeatedLineCore C D).Fiber =>
      TotalSpace.mk' (RepeatedLineModel E) z.proj (repeatedLineMap C D E T z.proj z.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
  have hc := ((trivializationAt (RepeatedLineModel D) (repeatedLineCore C D).Fiber z.proj).continuousAt
    FiberBundle.mem_trivializationAt_proj_source).snd
  have hpi := (EuclideanSpace.equiv (Σ s, Fin (D s)) ℂ).continuous.continuousAt.comp hc
  apply (EuclideanSpace.equiv (Σ s, Fin (E s)) ℂ).symm.continuous.continuousAt.comp
  apply continuousAt_pi.mpr
  rintro ⟨s,b⟩
  have h : ContinuousAt (fun w : TotalSpace (RepeatedLineModel D) (repeatedLineCore C D).Fiber =>
      ∑ a, T s (Pi.single a 1) b *
        ((trivializationAt (RepeatedLineModel D) (repeatedLineCore C D).Fiber z.proj) w).2 ⟨s,a⟩) z :=
    tendsto_finsetSum Finset.univ (fun a _ =>
    continuousAt_const.mul ((continuous_apply (⟨s,a⟩ : Σ s, Fin (D s))).continuousAt.comp hpi))
  exact h.congr (Filter.Eventually.of_forall (fun w =>
    (repeatedLineMap_chart C D E T z.proj w.proj w.2 s b).symm))

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
variable {B : Type*} [TopologicalSpace B] {k : ℕ}
  {J : Fin k → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

attribute [local instance] OAI.Kaplansky.instFiniteDimensionalComplexFiber_solutions
/-- The constructed uniform scalar choices give continuous total-space
maps on the actual bundles and expand every small fiber subspace. -/
theorem exists_continuous_repeatedLine_replacements
    (m : ℕ) (hm : 0 < m) (r : Fin k → ℕ) (hr : ∀ s, 16*m ≤ r s) :
    ∃ A : ∀ x, Fin 16 →
      (repeatedLineCore C (fun s => 4*r s)).Fiber x →ₗ[ℂ] (repeatedLineCore C r).Fiber x,
      (∀ i, Continuous (fun z : TotalSpace (RepeatedLineModel (fun s => 4*r s))
        (repeatedLineCore C (fun s => 4*r s)).Fiber =>
        TotalSpace.mk' (RepeatedLineModel r) z.proj (A z.proj i z.2))) ∧
      ∀ x, ExpandingThrough m (A x) := by
  obtain ⟨T,hT⟩ := exists_uniform_line_block_replacements k m hm r hr
    (fun s x => (C s).Fiber x) (fun _ _ => Module.finrank_self ℂ)
  let A := fun x i => repeatedLineMap C (fun s => 4*r s) r
    (fun s => (T s i).toLinearMap) x
  refine ⟨A,fun i => continuous_repeatedLineMap C _ _ _,?_⟩
  intro x
  have h := expandingThrough_equiv m _
    (repeatedLineFiberEquiv C (fun s => 4*r s) x).symm
    (repeatedLineFiberEquiv C r x).symm (hT x)
  exact h

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Base
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.complexCoreFiberRealModule
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

instance instCompactSpaceBundleTestBase (m R : ℕ) : CompactSpace (BundleTestBase m R) := inferInstance

def bundleTestBasePoint (m R : ℕ) : BundleTestBase m R :=
  fun i => coordinateLineProjection (testProjectiveDimension m R i)

instance instNonemptyBundleTestBase (m R : ℕ) : Nonempty (BundleTestBase m R) := ⟨bundleTestBasePoint m R⟩

end Kaplansky

end

namespace Kaplansky
open scoped BigOperators

theorem testPrefixDimension_margin {m R j : ℕ} (hm : 0 < m) (hj : j<R) :
    3*testPrefixDimension m R j hj < 20*m*testRank m R j := by
  have h : testPrefixDimension m R j hj ≤
      5*m*testRank m R 0*(∑ i : Fin (j+1),4^i.val) := by
    unfold testPrefixDimension
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => testProjectiveDimension_bound m R (i.castLE hj))
  have hg := three_sum_pow_four (j+1)
  have hd : 0<testRank m R 0 := by unfold testRank; positivity
  have he : testRank m R j = testRank m R 0*4^j := by
    simp only [testRank,pow_zero,one_mul]
    ring
  rw [pow_succ] at hg
  rw [he]
  nlinarith [Nat.mul_le_mul_left 3 h,
    congrArg (fun n : ℕ => 5*m*testRank m R 0*n) hg]

end Kaplansky

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

theorem finiteLineSumCore_transition_smooth
    {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace H]
    (I : ModelWithCorners ℝ X H) [ChartedSpace H B]
    (hC : ∀ s a b, ContMDiffOn I 𝓘(ℝ,ℂ →L[ℂ] ℂ) ∞ ((C s).coordChange a b)
      ((C s).baseSet a ∩ (C s).baseSet b)) (a b : ∀ s, J s) :
    ContMDiffOn I 𝓘(ℝ,EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) ∞
      ((finiteLineSumCore C).coordChange a b)
      ((finiteLineSumCore C).baseSet a ∩ (finiteLineSumCore C).baseSet b) := by
  have hc : ContMDiffOn I 𝓘(ℝ,S → ℂ) ∞
      (fun x s => (C s).coordChange (a s) (b s) x 1)
      ((finiteLineSumCore C).baseSet a ∩ (finiteLineSumCore C).baseSet b) := by
    apply contMDiffOn_pi_space.mpr
    intro s x hx
    exact ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).restrictScalars ℝ).contDiff.contDiffAt.contMDiffAt.comp_contMDiffWithinAt x
      ((hC s (a s) (b s)).mono (fun y (hy : y ∈ (finiteLineSumCore C).baseSet a ∩ (finiteLineSumCore C).baseSet b) => ⟨hy.1 s,hy.2 s⟩) x hx)
  let hd := (lineDiagonalLinear (S := S)).toContinuousLinearMap.restrictScalars ℝ
  intro x hx
  have h := hd.contDiff.contDiffAt.contMDiffAt.comp_contMDiffWithinAt x (hc x hx)
  exact h.congr (fun y _ => by simpa [hd, finiteLineSumCore, lineDiagonalLinear] using lineSumTransition_eq_diagonal C a b y) (by simpa [hd, finiteLineSumCore, lineDiagonalLinear] using lineSumTransition_eq_diagonal C a b x)

end Kaplansky

end

open Bundle Topology
open scoped Manifold ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_SmoothLine
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.lineStage_complete _root_.OAI.Kaplansky.lineStage_finite _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
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

instance productLineCore_contMDiffVectorBundle (i : Option ι) :
    ContMDiffVectorBundle ∞ ℂ (productLineCore K i).Fiber 𝓘(ℝ,ProjectiveProductModel K) :=
  complexCore_contMDiffVectorBundle _ _ (productLineCore_transition_smooth K i)

end

variable {ι S : Type*} [Fintype ι] [Fintype S] (K : ι → ℕ) (label : S → Option ι)

instance smoothLineSum_contMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (EuclideanSpace ℂ S) (SmoothLineSumBundle K label)
      𝓘(ℝ,ProjectiveProductModel K) :=
  complexCore_contMDiffVectorBundle _ _
    (finiteLineSumCore_transition_smooth _ _ (fun s => productLineCore_transition_smooth K (label s)))

end Kaplansky.ComplexGrassmann

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Smooth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.lineStage_complete _root_.OAI.Kaplansky.lineStage_finite _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
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

def testBaseProjectiveHomeomorph (m R : ℕ) : BundleTestBase m R ≃ₜ SmoothTestBase m R :=
  Homeomorph.piCongrRight (testFactorProjectiveHomeomorph m R)

instance instCompactSpaceSmoothTestBase (m R : ℕ) : CompactSpace (SmoothTestBase m R) := inferInstance
instance instT2SpaceSmoothTestBase (m R : ℕ) : T2Space (SmoothTestBase m R) := inferInstance

theorem smoothPrefix_incidence_margin {m R j : ℕ} (hm : 0 < m) (hj : j<R) :
    3*Module.finrank ℝ (SmoothPrefixModel m R j hj) < 40*m*testRank m R j := by
  rw [projectiveProduct_real_finrank]
  have h := testPrefixDimension_margin hm hj
  change 3*testPrefixDimension m R j hj < _ at h
  change 3*(2*testPrefixDimension m R j hj)<_
  nlinarith

end Kaplansky

end

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann

instance smoothTestBundle_smooth (m R b n : ℕ) (hb : b≤R) (hn : n≤b) :
    ContMDiffVectorBundle ∞ (EuclideanSpace ℂ (TestBundleSlot m R n))
      (SmoothTestBundle m R b n hb hn)
      𝓘(ℝ,ProjectiveProductModel (stageProjectiveDimensions m R b hb)) :=
  smoothLineSum_contMDiffVectorBundle _ _

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

def smoothReplacementCore (m R j : ℕ) (hj : j<R) :=
  repeatedLineCore (fun i : Fin (j+1) =>
    productLineCore (stageProjectiveDimensions m R (j+1) hj)
      (testSummandLineIndex (Nat.le_succ j) i)) (testReplacementMultiplicity m R j)

theorem exists_smoothTest_replacements {m R j : ℕ} (hm : 0 < m) (hj : j<R) :
    ∃ A : ∀ y, Fin 16 → SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y →ₗ[ℂ]
      (smoothReplacementCore m R j hj).Fiber y,
      (∀ i, Continuous (fun z : TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R j))
        (SmoothTestBundle m R (j+1) j hj (Nat.le_succ j)) =>
        TotalSpace.mk' (TestReplacementModel m R j) z.proj (A z.proj i z.2))) ∧
      ∀ y, ExpandingThrough m (A y) := by
  let C := fun i : Fin (j+1) => productLineCore (stageProjectiveDimensions m R (j+1) hj)
    (testSummandLineIndex (Nat.le_succ j) i)
  let r := testReplacementMultiplicity m R j
  have hr : ∀ i,16*m ≤ r i := by
    intro i
    have hq := testMultiplicity_quarter (m := m) hj i
    have hl := testMultiplicity_lower_bound (m := m) hj i
    change 16*m≤testMultiplicity m R (j+1) i.castSucc
    omega
  have he : (fun i : Fin (j+1) => 4*r i) = testMultiplicity m R j := by
    funext i
    exact testMultiplicity_quarter hj i
  let P : (Fin (j+1) → ℕ) → Prop := fun D =>
    ∃ A : ∀ y, Fin 16 → (repeatedLineCore C D).Fiber y →ₗ[ℂ] (repeatedLineCore C r).Fiber y,
      (∀ i, Continuous (fun z : TotalSpace (RepeatedLineModel D) (repeatedLineCore C D).Fiber =>
        TotalSpace.mk' (RepeatedLineModel r) z.proj (A z.proj i z.2))) ∧
      ∀ y, ExpandingThrough m (A y)
  have h : P (fun i => 4*r i) := exists_continuous_repeatedLine_replacements C m hm r hr
  exact Eq.mp (congrArg P he) h

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_CoordinatesMetric
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.lineStage_complete _root_.OAI.Kaplansky.lineStage_finite _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-coordinate smooth bundles and their metrics. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann
variable {S ι : Type*} [Fintype S] [Fintype ι]

variable (K : ι → ℕ) (label : S → Option ι) (d : ℕ) (hd : Fintype.card S=d)

instance finiteCoordinateBundle_smooth : ContMDiffVectorBundle ∞ (Fin d → ℂ)
    (FiniteCoordinateBundle K label d hd) 𝓘(ℝ,ProjectiveProductModel K) :=
  complexCore_contMDiffVectorBundle _ _ (changeModelCore_transition_smooth _ _ _
    (finiteLineSumCore_transition_smooth _ _ (fun s => productLineCore_transition_smooth K (label s))))

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Assembly
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.lineStage_complete _root_.OAI.Kaplansky.lineStage_finite _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
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

theorem exists_test_eight_fresh_bundle_maps {m R j : ℕ} (hm : 0 < m) (hj : j<R) :
    ∃ T : Fin 8 → ∀ y, TestSourceCoordinates m R j hj y →L[ℂ] TestFreshCoordinates m R j hj y,
      (∀ i, ContMDiff 𝓘(ℝ,SmoothPrefixModel m R j hj)
        (𝓘(ℝ,SmoothPrefixModel m R j hj).prod
          𝓘(ℝ,(Fin (testRank m R j) → ℂ) →L[ℝ] (Fin (TestFreshRank m R j) → ℂ))) ∞
        (fun y => TotalSpace.mk' ((Fin (testRank m R j) → ℂ) →L[ℝ]
          (Fin (TestFreshRank m R j) → ℂ)) y ((T i y).restrictScalars ℝ))) ∧
      ∀ y (S : Submodule ℂ (TestSourceCoordinates m R j hj y)), m<finrank ℂ S →
        2*finrank ℂ S≤finrank ℂ (⨆ i, S.map (T i y).toLinearMap :
          Submodule ℂ (TestFreshCoordinates m R j hj y)) := by
  apply Incidence.exists_eight_fresh_bundle_maps
  · unfold testRank
    positivity
  · exact testMultiplicity_fresh hj
  · exact smoothPrefix_incidence_margin hm hj

end Kaplansky

end

section
open Bundle Topology Module
namespace Kaplansky
open ComplexGrassmann

/-- The finite-coordinate incidence maps give genuine continuous maps on
the original Hilbert-sum presentation of E_j and its fresh block. -/
theorem exists_smoothTest_freshMaps {m R j : ℕ} (hm : 0 < m) (hj : j<R) :
    ∃ A : ∀ y, Fin 8 → SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y →ₗ[ℂ]
      (smoothFreshCore m R j hj).Fiber y,
      (∀ i, Continuous (fun z : TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R j))
        (SmoothTestBundle m R (j+1) j hj (Nat.le_succ j)) =>
        TotalSpace.mk' (EuclideanSpace ℂ (Fin (TestFreshRank m R j))) z.proj (A z.proj i z.2))) ∧
      ∀ y (S : Submodule ℂ (SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y)),
        m<finrank ℂ S → 2*finrank ℂ S≤finrank ℂ
          (⨆ i, S.map (A y i) : Submodule ℂ ((smoothFreshCore m R j hj).Fiber y)) := by
  obtain ⟨T,hT,hExp⟩ := exists_test_eight_fresh_bundle_maps hm hj
  let e := finiteCoordinateEquiv (testRank m R j) (testBundleSlot_card (Nat.le_of_lt hj) (m := m))
  let f := finiteCoordinateEquiv (TestFreshRank m R j) (Fintype.card_fin (TestFreshRank m R j))
  let a := fun y => (show SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y ≃ₗ[ℂ]
    TestSourceCoordinates m R j hj y from e.toLinearEquiv)
  let b := fun y => (show (smoothFreshCore m R j hj).Fiber y ≃ₗ[ℂ]
    TestFreshCoordinates m R j hj y from f.toLinearEquiv)
  let A := fun y i => (b y).symm.toLinearMap.comp ((T i y).toLinearMap.comp (a y).toLinearMap)
  refine ⟨A,?_,?_⟩
  · intro i
    have hc : Continuous (fun z : TotalSpace (Fin (testRank m R j) → ℂ) (TestSourceCoordinates m R j hj) =>
        TotalSpace.mk' (Fin (TestFreshRank m R j) → ℂ) z.proj (T i z.proj z.2)) :=
      ((hT i).continuous.comp (FiberBundle.continuous_proj _ _)).clm_bundle_apply continuous_id
    let H := finiteCoordinateTotalHomeomorph (stageProjectiveDimensions m R (j+1) hj)
      (fun s : TestBundleSlot m R j => testSummandLineIndex (Nat.le_succ j) s.1)
      (testRank m R j) (testBundleSlot_card (Nat.le_of_lt hj))
    let G := finiteCoordinateTotalHomeomorph (stageProjectiveDimensions m R (j+1) hj)
      (fun _ : Fin (TestFreshRank m R j) => some (Fin.last j))
      (TestFreshRank m R j) (Fintype.card_fin _)
    exact G.symm.continuous.comp (hc.comp H.continuous)
  · intro y S hS
    have h := hExp y (S.map (a y).toLinearMap) (by simpa only [(a y).finrank_map_eq] using hS)
    rw [(a y).finrank_map_eq] at h
    have he : (⨆ i, S.map (A y i)) =
        (⨆ i, (S.map (a y).toLinearMap).map (T i y).toLinearMap).map (b y).symm.toLinearMap := by
      rw [Submodule.map_iSup]
      apply iSup_congr
      intro i
      rw [Submodule.map_comp,Submodule.map_comp]
    rw [he,(b y).symm.finrank_map_eq]
    exact h

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

theorem exists_test_twentyFour_expanding_maps {m R j : ℕ} (hm : 0 < m) (hj : j<R) :
    ∃ T : ∀ y, Fin 24 → SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y →ₗ[ℂ]
      (smoothNextCore m R j hj).Fiber y,
      (∀ i, Continuous (fun z : TotalSpace (EuclideanSpace ℂ (TestBundleSlot m R j))
        (SmoothTestBundle m R (j+1) j hj (Nat.le_succ j)) =>
        TotalSpace.mk' (EuclideanSpace ℂ (TestNextSlot m R j)) z.proj (T z.proj i z.2))) ∧
      ∀ y, IntrinsicExpanding (T y) := by
  obtain ⟨A,hA,heA⟩ := exists_smoothTest_replacements hm hj
  obtain ⟨B,hB,heB⟩ := exists_smoothTest_freshMaps hm hj
  let L := fun u : TestNextSlot m R j =>
    productLineCore (stageProjectiveDimensions m R (j+1) hj) (testNextLabel m R j u)
  let T : ∀ y, Fin 24 → SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y →ₗ[ℂ]
      (smoothNextCore m R j hj).Fiber y := fun y q => Fin.addCases
    (motive := fun _ : Fin (16+8) => SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y →ₗ[ℂ] (smoothNextCore m R j hj).Fiber y)
    (fun i => (lineSumInl L y).comp (A y i))
    (fun i => (lineSumInr L y).comp (B y i)) q
  refine ⟨T,?_,?_⟩
  · intro i
    refine Fin.addCases (m := 16) (n := 8) ?_ ?_ i
    · intro a
      have ht (y) : T y (Fin.castAdd 8 a) = (lineSumInl L y).comp (A y a) :=
        Fin.addCases_left a
      apply ((continuous_lineSumInl L).comp (hA a)).congr
      intro z
      apply congrArg (TotalSpace.mk' _ z.proj)
      exact (congrArg (fun F => F z.2) (ht z.proj)).symm
    · intro b
      have ht (y) : T y (Fin.natAdd 16 b) = (lineSumInr L y).comp (B y b) :=
        Fin.addCases_right b
      apply ((continuous_lineSumInr L).comp (hB b)).congr
      intro z
      apply congrArg (TotalSpace.mk' _ z.proj)
      exact (congrArg (fun F => F z.2) (ht z.proj)).symm
  · intro y
    let : FiniteDimensional ℂ ((finiteLineSumCore L).Fiber y) :=
      inferInstanceAs (FiniteDimensional ℂ (EuclideanSpace ℂ (TestNextSlot m R j)))
    exact combined_expanding m (A y) (B y) (lineSumInl L y) (lineSumInr L y)
      (lineSumInl_injective L y) (lineSumInr_injective L y) (heA y) (heB y)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Normalized
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.lineStage_complete _root_.OAI.Kaplansky.lineStage_finite _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Normalized test maps, slot regrouping, and unitary coordinate changes. -/

section
open Bundle Topology
open scoped BigOperators ComplexOrder
namespace Kaplansky
open ComplexGrassmann

/-- The actual 24-map expansion transported into the same concrete
Hermitian coordinate bundles used by ordinary bundle normalization. -/
theorem exists_test_coordinate_expanding_maps {m R j : ℕ} (hm : 0 < m) (hj : j<R) :
    ∃ T : ∀ y, Fin 24 → TestSourceCoordinates m R j hj y →ₗ[ℂ] TestNextCoordinates m R j hj y,
      (∀ i, Continuous (fun z : TotalSpace (Fin (testRank m R j) → ℂ) (TestSourceCoordinates m R j hj) =>
        TotalSpace.mk' (Fin (testRank m R (j+1)) → ℂ) z.proj (T z.proj i z.2))) ∧
      ∀ y, IntrinsicExpanding (T y) := by
  obtain ⟨T,hT,hExp⟩ := exists_test_twentyFour_expanding_maps hm hj
  let e := finiteCoordinateEquiv (testRank m R j) (testBundleSlot_card (Nat.le_of_lt hj) (m := m))
  let f := finiteCoordinateEquiv (testRank m R (j+1)) (testNextSlot_card hj (m := m))
  let a := fun y => (show SmoothTestBundle m R (j+1) j hj (Nat.le_succ j) y ≃ₗ[ℂ]
    TestSourceCoordinates m R j hj y from e.toLinearEquiv)
  let b := fun y => (show (smoothNextCore m R j hj).Fiber y ≃ₗ[ℂ]
    TestNextCoordinates m R j hj y from f.toLinearEquiv)
  refine ⟨fun y i => (b y).toLinearMap.comp ((T y i).comp (a y).symm.toLinearMap),?_,?_⟩
  · intro i
    let H := finiteCoordinateTotalHomeomorph (stageProjectiveDimensions m R (j+1) hj)
      (fun s : TestBundleSlot m R j => testSummandLineIndex (Nat.le_succ j) s.1)
      (testRank m R j) (testBundleSlot_card (Nat.le_of_lt hj))
    let G := finiteCoordinateTotalHomeomorph (stageProjectiveDimensions m R (j+1) hj)
      (testNextLabel m R j) (testRank m R (j+1)) (testNextSlot_card hj)
    exact G.continuous.comp ((hT i).comp H.symm.continuous)
  · intro y
    exact intrinsicExpanding_equiv (T y) (a y) (b y) (hExp y)

theorem exists_test_normalized_maps {m R j : ℕ} (hm : 0 < m) (hj : j<R) :
    ∃ X : ∀ y, Fin 24 → TestSourceCoordinates m R j hj y →ₗ[ℂ] TestNextCoordinates m R j hj y,
      (∀ i, Continuous (fun z : TotalSpace (Fin (testRank m R j) → ℂ) (TestSourceCoordinates m R j hj) =>
        TotalSpace.mk' (Fin (testRank m R (j+1)) → ℂ) z.proj (X z.proj i z.2))) ∧
      (∀ i, Continuous (fun z : TotalSpace (Fin (testRank m R (j+1)) → ℂ) (TestNextCoordinates m R j hj) =>
        TotalSpace.mk' (Fin (testRank m R j) → ℂ) z.proj
          (bundleAdjoint (d := testRank m R j) (r := testRank m R (j+1)) X z.proj i z.2))) ∧
      ∀ y, (∑ i, (bundleAdjoint (d := testRank m R j) (r := testRank m R (j+1)) X y i).comp (X y i)) = LinearMap.id ∧
        ∀ v : TestNextCoordinates m R j hj y, 0 ≤ inner ℂ v
          (((2/3 : ℂ) • (LinearMap.id : TestNextCoordinates m R j hj y →ₗ[ℂ] TestNextCoordinates m R j hj y) -
            ∑ i, (X y i).comp (bundleAdjoint (d := testRank m R j) (r := testRank m R (j+1)) X y i)) v) := by
  obtain ⟨T,hT,hExp⟩ := exists_test_coordinate_expanding_maps hm hj
  exact exists_continuous_normalized_bundle_maps
    (finiteCoordinate_continuousHermitianMetric _ _ _ _)
    (finiteCoordinate_continuousHermitianMetric _ _ _ _) T hT hExp

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Retained
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.lineStage_complete _root_.OAI.Kaplansky.lineStage_finite _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
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

def retainedLabel (m R : ℕ) (s : RetainedSlot m R) : Option (Fin R) :=
  testSummandLineIndex (Nat.le_of_lt_succ s.2.1.isLt) s.2.2.1

def retainedBundleCore (m R : ℕ) :=
  smoothLineSumCore (testProjectiveDimension m R) (retainedLabel m R)
abbrev RetainedBundle (m R : ℕ) := (retainedBundleCore m R).Fiber

instance retainedBundle_norm (m R : ℕ) (P : SmoothTestBase m R) :
    NormedAddCommGroup (RetainedBundle m R P) := smoothLineSum_norm _ _ P
instance retainedBundle_inner (m R : ℕ) (P : SmoothTestBase m R) :
    InnerProductSpace ℂ (RetainedBundle m R P) := smoothLineSum_inner _ _ P

end Kaplansky

end

section
open scoped BigOperators
namespace Kaplansky

theorem retainedLabel_card_sum (m R : ℕ) (i : Option (Fin R)) :
    Fintype.card {s : RetainedSlot m R // retainedLabel m R s=i} =
      m * ∑ j : Fin (R+1), ∑ a : Fin (j.val+1),
        if testSummandLineIndex (Nat.le_of_lt_succ j.isLt) a=i
        then testMultiplicity m R j.val a else 0 := by
  change Fintype.card {s : Fin m × (Σ j : Fin (R+1), TestBundleSlot m R j.val) //
    testSummandLineIndex (Nat.le_of_lt_succ s.2.1.isLt) s.2.2.1=i} = _
  rw [labelFiberProd_card (A := Fin m)
    (fun s : Σ j : Fin (R+1), TestBundleSlot m R j.val =>
      testSummandLineIndex (Nat.le_of_lt_succ s.1.isLt) s.2.1) i,Fintype.card_fin,
    labelFiberSigma_card (A := fun j : Fin (R+1) => TestBundleSlot m R j.val) (fun (j : Fin (R+1)) (s : TestBundleSlot m R j.val) =>
      testSummandLineIndex (Nat.le_of_lt_succ j.isLt) s.1) i]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [labelFiberSigma_card (fun a (_ : Fin (testMultiplicity m R j.val a)) =>
    testSummandLineIndex (Nat.le_of_lt_succ j.isLt) a) i]
  apply Finset.sum_congr rfl
  intro a _
  rw [constantLabelFiber_card,Fintype.card_fin]

theorem retainedLabel_none_card (m R : ℕ) :
    Fintype.card {s : RetainedSlot m R // retainedLabel m R s=none} = retainedTrivialMultiplicity m R := by
  rw [retainedLabel_card_sum]
  simp_rw [testSummandLineIndex_eq_none]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold retainedTrivialMultiplicity
  congr 1
  let e : Fin (R+1) ≃ Fin (R+1) := ⟨Fin.rev,Fin.rev,Fin.rev_involutive,Fin.rev_involutive⟩
  apply Fintype.sum_equiv e
  intro j
  have he : R-(e j).val=j.val := by
    change R-((R+1)-(j.val+1))=j.val
    have hj := j.isLt
    omega
  change 64*m*4^(R-j.val) = 64*m*4^(R-(R-(e j).val))
  rw [he]

/-- Each K_i is the count of actual occurrences of its hyperplane line in
G, including all m copies and every retained stage. -/
theorem retainedLabel_some_card (m R : ℕ) (i : Fin R) :
    Fintype.card {s : RetainedSlot m R // retainedLabel m R s=some i} = testProjectiveDimension m R i := by
  rw [retainedLabel_card_sum]
  simp_rw [retainedLabel_some_stage_sum]
  rw [sum_suffix_reverse]
  exact retainedHyperplaneMultiplicity_eq m R i

end Kaplansky

end

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann

theorem retainedLabel_card (m R : ℕ) (i : Option (Fin R)) :
    Fintype.card {s : RetainedSlot m R // retainedLabel m R s=i}=retainedLineRank m R i := by
  cases i with
  | none => exact retainedLabel_none_card m R
  | some i => exact retainedLabel_some_card m R i

/-- Every retained line occurrence is accounted for exactly once. -/
def retainedGroupingEquiv (m R : ℕ) : RetainedSlot m R ≃ RetainedGroupedSlot m R :=
  (groupingByLabel (retainedLabel m R)).trans (Equiv.sigmaCongrRight (fun i =>
    (Fintype.equivFin {s : RetainedSlot m R // retainedLabel m R s=i}).trans
      (finCongr (retainedLabel_card m R i))))

theorem retainedGrouping_label (m R : ℕ) (s : RetainedSlot m R) :
    (retainedGroupingEquiv m R s).1=retainedLabel m R s := rfl

/-- Relabeling justified by an exact slot bijection preserves topology and
metric, as well as the fiber linear structure. -/
def lineSumRelabelUnitary {S T ι : Type*} [Fintype S] [Fintype T] [Fintype ι]
    (K : ι → ℕ) (a : T → Option ι) (b : S → Option ι) (e : T ≃ S)
    (h : ∀ t, a t=b (e t)) :
    UnitaryBundleEquiv (EuclideanSpace ℂ T) (EuclideanSpace ℂ S)
      (SmoothLineSumBundle K a) (SmoothLineSumBundle K b) := by
  have he : a = fun t => b (e t) := funext h
  subst a
  exact lineSumReindexUnitary (fun s => productLineCore K (b s)) e

def retainedRegroupingUnitary (m R : ℕ) :
    UnitaryBundleEquiv (EuclideanSpace ℂ (RetainedSlot m R))
      (EuclideanSpace ℂ (RetainedGroupedSlot m R)) (RetainedBundle m R)
      (SmoothLineSumBundle (testProjectiveDimension m R) (fun s : RetainedGroupedSlot m R => s.1)) :=
  lineSumRelabelUnitary (testProjectiveDimension m R) (retainedLabel m R) (fun s : RetainedGroupedSlot m R => s.1)
    (retainedGroupingEquiv m R) (fun s => (retainedGrouping_label m R s).symm)

end Kaplansky

end

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_StageMaps
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
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

/-- Constant model vectors are genuine continuous sections of this trivial
bundle in its original topology. -/
theorem lineStageTrivial_section (a : LineStage K) (h : ∀ s, a.label s=none)
    (y₀ : ProjectiveProduct K) (v : a.Model) :
    Continuous (fun y => TotalSpace.mk' a.Model y (show a.Fiber y from v)) := by
  let e := lineStageTrivialTotalHomeomorph a h y₀
  have he : (fun y => TotalSpace.mk' a.Model y (show a.Fiber y from v)) =
      e.symm ∘ (fun y => (y,v)) := by
    funext y
    apply e.injective
    exact (lineStageTrivialTotalHomeomorph_apply a h y₀ _).trans (e.apply_symm_apply (y,v)).symm
  rw [he]
  exact e.symm.continuous.comp (continuous_id.prodMk continuous_const)

end Kaplansky

end

open Bundle Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Words
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word propagation through Hilbert shifts and normalized tuple operators. -/

noncomputable section
open scoped BigOperators
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)] [∀ j, CompleteSpace (E j)]

variable {n : ℕ} (T : Fin n → ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ i j, ‖T i j‖ ≤ 1)

/-- False letters are generators; true letters are their actual adjoints. -/
def shiftLetter (a : Bool × Fin n) : Module.End ℂ (FiberHilbertSum E) :=
  if a.1 then (forwardShift (T a.2) (hT a.2)).adjoint.toLinearMap
  else (forwardShift (T a.2) (hT a.2)).toLinearMap

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_BundleWords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
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

def bundleWordValue {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1))) :
    List (Bool × Fin 24) → BundleWordValue a
  | [] => BundleWordValue.identity
  | (false,i)::w => (bundleWordValue X w).raise X i
  | (true,i)::w => (bundleWordValue X w).lower X i

theorem bundleWordValue_level_le {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))
    (w : List (Bool × Fin 24)) : (bundleWordValue X w).level ≤ w.length := by
  induction w with
  | nil => exact Nat.zero_le _
  | cons l w ih =>
    obtain ⟨b,i⟩ := l
    cases b <;> simp only [bundleWordValue,BundleWordValue.raise_level,
      BundleWordValue.lower_level,List.length_cons] <;> omega

end WordValues

section Evaluation

variable {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))

theorem towerOperator_norm (i : Fin 24) (y : ProjectiveProduct K) (j : ℕ) :
    ‖towerOperator X i y j‖ ≤ 1 := by
  let T : NormalizedHermitianTuple (EuclideanSpace ℂ (a j).Slot)
      (EuclideanSpace ℂ (a (j+1)).Slot) := (X j).tuple y
  have h := T.operator_norm_le i
  exact h

end Evaluation

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
namespace Kaplansky

/-- A nonempty family of nontrivial coordinate algebras has a nontrivial
bounded product. Nonemptiness is explicit; an empty product is excluded. -/
theorem boundedProduct_nontrivial {I : Type*} [Nonempty I] {A : I → Type*}
    [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)] : Nontrivial (BoundedProduct A) := by
  let i : I := Classical.arbitrary I
  refine ⟨⟨0,1,?_⟩⟩
  intro h
  have he := congrArg (fun f : BoundedProduct A => f i) h
  exact zero_ne_one he

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_BundlePolynomials
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
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

/-- The finite direct sum of the retained stages, for each matrix row. -/
def towerRetainedStage (a : ℕ → LineStage K) (m R : ℕ) : LineStage K :=
  LineStage.sum (fun _ : Fin m => LineStage.sum (fun j : Fin (R+1) => a j.val))

/-- The bottom bundle repeated once per matrix column. -/
def towerInputStage (a : ℕ → LineStage K) (n : ℕ) : LineStage K :=
  LineStage.sum (fun _ : Fin n => a 0)

variable {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))

def bundleMatrixTerm {m n R : ℕ} (t : BoundedMatrixTerm m n R) :
    ContinuousStageMap (towerInputStage a n) (towerRetainedStage a m R) := by
  let W := bundleWordValue X t.word
  let j : Fin (R+1) := ⟨W.level,Nat.lt_succ_of_le ((bundleWordValue_level_le X t.word).trans t.degree_le)⟩
  let wordMap : ContinuousStageMap (a 0) (a j.val) := ⟨W.map,W.continuous_map⟩
  exact ((ContinuousStageMap.inj (fun _ : Fin m =>
    LineStage.sum (fun k : Fin (R+1) => a k.val)) t.row).comp
    ((ContinuousStageMap.inj (fun k : Fin (R+1) => a k.val) j).comp
      (wordMap.comp (ContinuousStageMap.proj (fun _ : Fin n => a 0) t.col)))).smul t.coeff

/-- The intrinsic finite matrix restriction. Its continuity is proved from
actual normalized bundle maps and adjoints, including the constant term. -/
def bundleMatrixPolynomial {m n R : ℕ} {T : Type*} (s : Finset T)
    (t : T → BoundedMatrixTerm m n R) :
    ContinuousStageMap (towerInputStage a n) (towerRetainedStage a m R) :=
  ContinuousStageMap.sum s (fun k => bundleMatrixTerm X (t k))

theorem bundleMatrixPolynomial_continuous {m n R : ℕ} {T : Type*} (s : Finset T)
    (t : T → BoundedMatrixTerm m n R) :
    Continuous (fun z : TotalSpace (towerInputStage a n).Model (towerInputStage a n).Fiber =>
      TotalSpace.mk' (towerRetainedStage a m R).Model z.proj
        ((bundleMatrixPolynomial X s t).map z.proj z.2)) :=
  (bundleMatrixPolynomial X s t).continuous_map

def retainedRowHilbert (a : ℕ → LineStage K) (m R : ℕ)
    (y : ProjectiveProduct K) (row : Fin m) :
    (towerRetainedStage a m R).Fiber y →ₗ[ℂ] lp (fun j => (a j).Fiber y) 2 :=
  (finiteTowerHilbert a R y).comp
    (LineStage.sumProj (fun _ : Fin m => LineStage.sum (fun j : Fin (R+1) => a j.val)) row y)

def retainedMatrixHilbertMap (a : ℕ → LineStage K) (m R : ℕ) (y : ProjectiveProduct K) :
    (towerRetainedStage a m R).Fiber y →ₗ[ℂ] MatrixTowerHilbert a m y where
  toFun v := WithLp.toLp 2 (fun row => retainedRowHilbert a m R y row v)
  map_add' v w := by
    apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => lp (fun j => (a j).Fiber y) 2)).injective
    funext row
    exact map_add (retainedRowHilbert a m R y row) v w
  map_smul' c v := by
    apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => lp (fun j => (a j).Fiber y) 2)).injective
    funext row
    exact map_smul (retainedRowHilbert a m R y row) c v

theorem retainedMatrixHilbert_inner (a : ℕ → LineStage K) (m R : ℕ) (y : ProjectiveProduct K)
    (v w : (towerRetainedStage a m R).Fiber y) :
    inner ℂ (retainedMatrixHilbertMap a m R y v) (retainedMatrixHilbertMap a m R y w)=inner ℂ v w := by
  change (∑ row : Fin m, inner ℂ (retainedRowHilbert a m R y row v)
    (retainedRowHilbert a m R y row w))=inner ℂ v w
  exact (Finset.sum_congr rfl (fun row _ => finiteTowerHilbert_inner a R y
    (LineStage.sumProj (fun _ : Fin m => LineStage.sum (fun j : Fin (R+1) => a j.val)) row y v)
    (LineStage.sumProj (fun _ : Fin m => LineStage.sum (fun j : Fin (R+1) => a j.val)) row y w))).trans
      (LineStage.sum_inner _ y v w).symm

def retainedMatrixHilbertIsometry (a : ℕ → LineStage K) (m R : ℕ) (y : ProjectiveProduct K) :
    (towerRetainedStage a m R).Fiber y →ₗᵢ[ℂ] MatrixTowerHilbert a m y where
  toLinearMap := retainedMatrixHilbertMap a m R y
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (retainedMatrixHilbert_inner a m R y)

def inputMatrixHilbertMap (a : ℕ → LineStage K) (n : ℕ) (y : ProjectiveProduct K) :
    (towerInputStage a n).Fiber y →ₗ[ℂ] MatrixTowerHilbert a n y where
  toFun v := WithLp.toLp 2 (fun col => lp.single 2 0
    (LineStage.sumProj (fun _ : Fin n => a 0) col y v))
  map_add' v w := by
    apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => lp (fun j => (a j).Fiber y) 2)).injective
    funext col
    exact (congrArg (lp.single (E := fun j => (a j).Fiber y) 2 0)
      (map_add (LineStage.sumProj (fun _ : Fin n => a 0) col y) v w)).trans
      (lp.single_add (E := fun j => (a j).Fiber y) 2 0 _ _)
  map_smul' c v := by
    apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => lp (fun j => (a j).Fiber y) 2)).injective
    funext col
    exact (congrArg (lp.single (E := fun j => (a j).Fiber y) 2 0)
      (map_smul (LineStage.sumProj (fun _ : Fin n => a 0) col y) c v)).trans
      (lp.single_smul (E := fun j => (a j).Fiber y) 2 0 c _)

theorem inputMatrixHilbert_inner (a : ℕ → LineStage K) (n : ℕ) (y : ProjectiveProduct K)
    (v w : (towerInputStage a n).Fiber y) :
    inner ℂ (inputMatrixHilbertMap a n y v) (inputMatrixHilbertMap a n y w)=inner ℂ v w := by
  change (∑ col : Fin n, inner ℂ
    (lp.single 2 0 (LineStage.sumProj (fun _ : Fin n => a 0) col y v) : lp (fun j => (a j).Fiber y) 2)
    (lp.single 2 0 (LineStage.sumProj (fun _ : Fin n => a 0) col y w) : lp (fun j => (a j).Fiber y) 2))=inner ℂ v w
  simp only [lp.inner_single_left,lp.single_apply_self]
  exact (LineStage.sum_inner _ y v w).symm

def inputMatrixHilbertIsometry (a : ℕ → LineStage K) (n : ℕ) (y : ProjectiveProduct K) :
    (towerInputStage a n).Fiber y →ₗᵢ[ℂ] MatrixTowerHilbert a n y where
  toLinearMap := inputMatrixHilbertMap a n y
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (inputMatrixHilbert_inner a n y)

/-- Direct evaluated matrix action on Hilbert vectors, with every term
placed in its specified row and applied to its specified input column. -/
def matrixPolynomialAction {m n R : ℕ} {T : Type*} (s : Finset T)
    (t : T → BoundedMatrixTerm m n R) (y : ProjectiveProduct K)
    (v : MatrixTowerHilbert a n y) : MatrixTowerHilbert a m y :=
  WithLp.toLp 2 (fun row => ∑ k ∈ s, if (t k).row=row then (t k).coeff •
    applyWord (shiftLetter (fun i j => towerOperator X i y j)
      (fun i j => towerOperator_norm X i y j)) (t k).word (v (t k).col) else 0)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Sequence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
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

section
open ComplexGrassmann

attribute [local irreducible] bundleAdjoint finiteCoordinateEquiv

/-- The previously constructed normalized tuple, including both directions
of continuity and the actual adjoint identity. -/
theorem testCoordinateStep_nonempty {m R j : ℕ} (hm : 0 < m) (hj : j<R) :
    Nonempty (TestCoordinateStepType m R j hj) := by
  obtain ⟨X,hX,hA,hN⟩ := exists_test_normalized_maps hm hj
  refine ⟨{
    tuple := fun y =>
      { forward := X y
        reverse := bundleAdjoint (d := testRank m R j) (r := testRank m R (j+1)) X y
        adjoint_inner := bundleAdjoint_inner (d := testRank m R j) (r := testRank m R (j+1)) X y
        column := (hN y).1
        row := (hN y).2 }
    continuous_forward := hX
    continuous_reverse := hA }⟩

def testCoordinateStep {m R j : ℕ} (hm : 0 < m) (hj : j<R) : TestCoordinateStepType m R j hj :=
  Classical.choice (testCoordinateStep_nonempty hm hj)

def testPrefixStep {m R j : ℕ} (hm : 0 < m) (hj : j<R) :
    ContinuousNormalizedStep (EuclideanSpace ℂ (TestBundleSlot m R j))
      (EuclideanSpace ℂ (TestBundleSlot m R (j+1)))
      (SmoothTestBundle m R (j+1) j hj (Nat.le_succ j))
      (SmoothTestBundle m R (j+1) (j+1) hj (Nat.le_refl (j+1))) :=
  (testCoordinateStep hm hj).congr
    (finiteCoordinateUnitary _ _ _ (testBundleSlot_card (Nat.le_of_lt hj))).symm
    ((finiteCoordinateUnitary _ _ _ (testNextSlot_card hj)).symm.trans (testNextStageUnitary m R j hj))

end

open ComplexGrassmann

def testFullStep {m R j : ℕ} (hm : 0 < m) (hj : j<R) :
    ContinuousNormalizedStep (EuclideanSpace ℂ (TestBundleSlot m R j))
      (EuclideanSpace ℂ (TestBundleSlot m R (j+1)))
      (FullTestBundle m R j (Nat.le_of_lt hj)) (FullTestBundle m R (j+1) hj) := by
  let X := lineSumPullbackStep (testProjectiveDimension m R) (fun i : Fin (j+1) => i.castLE hj)
    (fun s : TestBundleSlot m R j => testSummandLineIndex (Nat.le_succ j) s.1)
    (fun s : TestBundleSlot m R (j+1) => testSummandLineIndex (Nat.le_refl (j+1)) s.1)
    (testPrefixStep hm hj)
  have ha : (fun s : TestBundleSlot m R j =>
      (testSummandLineIndex (Nat.le_succ j) s.1).map (fun i => i.castLE hj)) =
      fun s => testSummandLineIndex (Nat.le_of_lt hj) s.1 :=
    funext (fun s => testSummandLineIndex_map (Nat.le_succ j) hj s.1)
  have hb : (fun s : TestBundleSlot m R (j+1) =>
      (testSummandLineIndex (Nat.le_refl (j+1)) s.1).map (fun i => i.castLE hj)) =
      fun s => testSummandLineIndex hj s.1 :=
    funext (fun s => testSummandLineIndex_map (Nat.le_refl (j+1)) hj s.1)
  rw [ha,hb] at X
  exact X

/-- All 24 normalized bundle maps for all levels, constructed solely from
m>0. Both forward maps and their genuine adjoints are continuous over the
single full projective product Y. -/
def testSequenceStep {m R : ℕ} (hm : 0 < m) (j : ℕ) :
    (testSequenceStage m R j).Step (testSequenceStage m R (j+1)) := by
  by_cases hj : j<R
  · rw [testSequenceStage_prefix (Nat.le_of_lt hj),testSequenceStage_prefix hj]
    exact testFullStep hm hj
  · have hR : R≤j := Nat.le_of_not_gt hj
    rw [testSequenceStage_tail hR,testSequenceStage_tail (hR.trans (Nat.le_succ j))]
    have hs : j+1-R=(j-R)+1 := by omega
    rw [hs]
    exact (testLineStage m R R (Nat.le_refl R)).tailStep (j-R)

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_TestAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.retainedBundle_inner _root_.OAI.Kaplansky.retainedBundle_norm _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
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

instance instNonemptyActualTestIndex : Nonempty ActualTestIndex :=
  ⟨⟨1,1,testBaseProjectiveHomeomorph 1 1 (bundleTestBasePoint 1 1)⟩⟩

/-- Actual bounded blocks of the normalized bundle test, at all levels. -/
def actualTestOperator (i : Fin 24) (z : ActualTestIndex) (j : ℕ) :
    ActualTestFiber z j →L[ℂ] ActualTestFiber z (j+1) := by
  let T : NormalizedHermitianTuple (ActualTestFiber z j) (ActualTestFiber z (j+1)) :=
    (testSequenceStep (R := z.2.1.val) z.1.property j).tuple z.2.2
  exact T.operator i

theorem actualTestOperator_norm (i : Fin 24) (z : ActualTestIndex) (j : ℕ) :
    ‖actualTestOperator i z j‖ ≤ 1 :=
  by
    let T : NormalizedHermitianTuple (ActualTestFiber z j) (ActualTestFiber z (j+1)) :=
      (testSequenceStep (R := z.2.1.val) z.1.property j).tuple z.2.2
    have h := T.operator_norm_le i
    exact h

open scoped BigOperators

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2000] closedSubalgebraLE closedSubalgebraPreorder

def actualBoundedGenerator (i : Fin 24) : BoundedProduct (fun z : ActualTestIndex => ActualHilbert z →L[ℂ] ActualHilbert z) :=
  boundedProductLift (fun z => forwardShift (actualTestOperator i z) (actualTestOperator_norm i z))
    (fun z => forwardShift_norm_le (actualTestOperator i z) (actualTestOperator_norm i z))

abbrev ActualAlgebra := generatedAlgebra (Set.range actualBoundedGenerator)


def actualRepresentation (z : ActualTestIndex) : ActualAlgebra →⋆ₐ[ℂ] (ActualHilbert z →L[ℂ] ActualHilbert z) where
  toFun b := b.val z
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp] theorem actualRepresentation_generator (z : ActualTestIndex) (i : Fin 24) :
    actualRepresentation z (generatedGenerator actualBoundedGenerator i) =
      forwardShift (actualTestOperator i z) (actualTestOperator_norm i z) := rfl

theorem actualRepresentation_norm (z : ActualTestIndex) (b : ActualAlgebra) :
    ‖actualRepresentation z b‖ ≤ ‖b‖ := by
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero b.val z

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_MatrixImage
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Matrix restriction, trivial input bundles, and matrix images. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ} {a b : LineStage K}

def stageModelBasis (a : LineStage K) :
    Module.Basis (Fin (Fintype.card a.Slot)) ℂ a.Model :=
  ((Pi.basisFun ℂ a.Slot).map (EuclideanSpace.equiv a.Slot ℂ).symm.toLinearEquiv).reindex
    (Fintype.equivFin a.Slot)

/-- Columns of a continuous injective map from a genuinely trivial stage
are a continuous independent frame of its image. -/
def trivialMapFrame (L : ContinuousStageMap a b) (ha : ∀ s, a.label s=none)
    (y₀ : ProjectiveProduct K) (hinj : ∀ y, Function.Injective (L.map y)) :
    ContinuousIndependentStageFrame b (Fintype.card a.Slot) where
  vector y i := L.map y (show a.Fiber y from stageModelBasis a i)
  continuous_vector i := L.continuous_map.comp
    (lineStageTrivial_section a ha y₀ (stageModelBasis a i))
  independent y := (stageModelBasis a).linearIndependent.map' (L.map y)
    (LinearMap.ker_eq_bot.mpr (hinj y))

open scoped BigOperators

def actualRetainedUnitary (m R : ℕ) :
    UnitaryBundleEquiv (towerRetainedStage (testSequenceStage m R) m R).Model
      (EuclideanSpace ℂ (RetainedSlot m R))
      (towerRetainedStage (testSequenceStage m R) m R).Fiber (RetainedBundle m R) := by
  have he : (fun j : Fin (R+1) => testSequenceStage m R j.val) =
      (fun j : Fin (R+1) => testLineStage m R j.val (Nat.le_of_lt_succ j.isLt)) := by
    funext j
    exact testSequenceStage_prefix (Nat.le_of_lt_succ j.isLt)
  unfold towerRetainedStage
  rw [he]
  let e : (Σ _ : Fin m, Σ j : Fin (R+1), TestBundleSlot m R j.val) ≃ RetainedSlot m R :=
    { toFun := fun s => (s.1,s.2)
      invFun := fun s => ⟨s.1,s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact lineSumRelabelUnitary (testProjectiveDimension m R) _ (retainedLabel m R) e
    (fun _ => rfl)

/-- The actual finite rectangular matrix map into G, constructed from all
its polynomial terms. This definition assumes no obstruction or lower bound. -/
def actualMatrixRestriction {m n R : ℕ} (hm : 0 < m) {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) (y : SmoothTestBase m R) :
    (towerInputStage (testSequenceStage m R) n).Fiber y →ₗ[ℂ] RetainedBundle m R y :=
  ((actualRetainedUnitary m R).fiber y).toLinearMap.comp
    ((bundleMatrixPolynomial (testSequenceStep (R := R) hm) s t).map y)

theorem actualMatrixRestriction_continuous {m n R : ℕ} (hm : 0 < m) {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) :
    Continuous (fun z : TotalSpace (towerInputStage (testSequenceStage m R) n).Model
        (towerInputStage (testSequenceStage m R) n).Fiber =>
      TotalSpace.mk' (EuclideanSpace ℂ (RetainedSlot m R)) z.proj
        (actualMatrixRestriction hm s t z.proj z.2)) :=
  (actualRetainedUnitary m R).continuous_forward.comp
    (bundleMatrixPolynomial_continuous (testSequenceStep (R := R) hm) s t)

def retainedLineStage (m R : ℕ) : LineStage (testProjectiveDimension m R) :=
  ⟨RetainedSlot m R,inferInstance,retainedLabel m R⟩

def actualMatrixStageMap {m n R : ℕ} (hm : 0 < m) {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) :
    ContinuousStageMap (towerInputStage (testSequenceStage m R) n) (retainedLineStage m R) :=
  ⟨actualMatrixRestriction hm s t,actualMatrixRestriction_continuous hm s t⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Complement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Regrouping retained frames and their complement bundles. -/

section
open Bundle
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

namespace ContinuousOrthonormalStageFrame
variable {ι : Type*} [Fintype ι] {K : ι → ℕ} {a b : LineStage K} {d : ℕ}

def congr (f : ContinuousOrthonormalStageFrame a d)
    (e : UnitaryBundleEquiv a.Model b.Model a.Fiber b.Fiber) :
    ContinuousOrthonormalStageFrame b d where
  vector y i := e.fiber y (f.vector y i)
  continuous_vector i := e.continuous_forward.comp (f.continuous_vector i)
  orthonormal y := ((e.fiber y).toLinearIsometry.orthonormal_comp_iff).mpr (f.orthonormal y)
end ContinuousOrthonormalStageFrame

def retainedGroupedStage (m R : ℕ) : LineStage (testProjectiveDimension m R) :=
  ⟨RetainedGroupedSlot m R,inferInstance,fun s => s.1⟩

end Kaplansky

end

open Bundle Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Hyperplane
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.instCompactSpaceBundleTestBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Hyperplane sections, dual evaluation, graph coordinates, and their zero. -/

section
open Bundle Topology
open scoped InnerProductSpace
namespace Kaplansky
variable {d : ℕ}

theorem hyperplaneFunctionalSection_chart (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ)
    (p : projectionSpace d 1) (i : Fin d) (hi : p ∈ projectionChartSet i) :
    ((projectionDualLineCore d).localTriv i ⟨p,hyperplaneFunctionalSection L p⟩).2 =
      L (unitProjectionColumn p i) := by
  let j := (projectionLineCore d).indexAt p
  have hj : p ∈ projectionChartSet j := (projectionLineCore d).mem_baseSet_at p
  have hv := unitProjectionColumn_reconstruct p i hi
    (unitProjectionColumn p j) (unitProjectionColumn_mem p j)
  have he : L (unitProjectionColumn p j) =
      projectionLineTransition j i p * L (unitProjectionColumn p i) := by
    rw [← hv,map_smul]
    rfl
  change star (projectionLineTransition j i p) * L (unitProjectionColumn p j) = _
  rw [he,← mul_assoc,projectionLineTransition_unitary j i p hj hi,one_mul]

theorem continuous_hyperplaneFunctionalSection (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ) :
    Continuous (fun p => TotalSpace.mk' ℂ p (hyperplaneFunctionalSection L p)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rw [FiberBundle.continuousAt_section]
  let i := (projectionLineCore d).indexAt p
  have hi : p ∈ projectionChartSet i := (projectionLineCore d).mem_baseSet_at p
  have hc := L.toContinuousLinearMap.continuous.continuousAt.comp
    ((continuousOn_unitProjectionColumn i p hi).continuousAt
      ((isOpen_projectionChartSet i).mem_nhds hi))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(isOpen_projectionChartSet i).mem_nhds hi] with q hq
  exact hyperplaneFunctionalSection_chart L q i hq

/-- The section's actual dual-line realization is exactly restriction of L. -/
theorem hyperplaneFunctionalSection_realization (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ)
    (p : projectionSpace d 1) (v : projectionLine p) :
    projectionDualLineFiberEquiv p (hyperplaneFunctionalSection L p) v = L v.val := by
  let i := (projectionLineCore d).indexAt p
  have hi : p ∈ projectionChartSet i := (projectionLineCore d).mem_baseSet_at p
  change L (unitProjectionColumn p i) * inner ℂ (unitProjectionColumn p i) v.val = L v.val
  conv_rhs => rw [← unitProjectionColumn_reconstruct p i hi v.val v.property,map_smul]
  exact mul_comm _ _

theorem hyperplaneFunctionalSection_eq_zero_iff (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ)
    (p : projectionSpace d 1) : hyperplaneFunctionalSection L p=0 ↔
      ∀ v ∈ projectionLine p, L v=0 := by
  constructor
  · intro h v hv
    have he := hyperplaneFunctionalSection_realization L p ⟨v,hv⟩
    rw [h,map_zero,LinearMap.zero_apply] at he
    exact he.symm
  · intro h
    exact h _ (unitProjectionColumn_mem p _)

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky

/-- The K coordinate sections of O(1) on CP^K have exactly one common zero,
the first coordinate line. This is an actual zero-set statement, not yet
an identification or nonvanishing theorem for the top Chern class. -/
theorem hyperplaneCoordinateSections_common_zero {k : ℕ} (p : projectionSpace (1+k) 1) :
    (∀ i : Fin k, hyperplaneFunctionalSection (coordinateFunctional (positiveCoordinate k i)) p=0) ↔
      p=firstCoordinateProjection k := by
  constructor
  · intro h
    have hle : projectionLine p ≤ Submodule.span ℂ {firstCoordinateVector k} := by
      intro v hv
      have hz (i : Fin k) : v (positiveCoordinate k i)=0 :=
        (hyperplaneFunctionalSection_eq_zero_iff _ p).mp (h i) v hv
      rw [vector_eq_firstCoordinate_of_positive_zero v hz]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    apply projectionLine_injective
    rw [firstCoordinateProjection_line]
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [projectionLine_finrank,finrank_span_singleton (firstCoordinateVector_ne_zero k)]
  · rintro rfl i
    rw [hyperplaneFunctionalSection_eq_zero_iff,firstCoordinateProjection_line]
    intro v hv
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hi : positiveCoordinate k i≠0 := by
      intro h
      have := congrArg Fin.val h
      simp [positiveCoordinate] at this
    simp [coordinateFunctional_apply,firstCoordinateVector,hi]

end Kaplansky

open Bundle Topology
open scoped InnerProductSpace

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_HyperplaneProduct
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Hyperplane product sections and regular zeros. -/

section
open Bundle Topology
namespace Kaplansky

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

def firstCoordinateProduct : ProjectiveProduct K :=
  fun i => projectiveProjectionEquiv (K i) (firstCoordinateProjection (K i))

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} (K : ι → ℕ)

def canonicalProductGraphPoint (A : ProjectiveProductModel K) : ProjectiveProduct K :=
  fun i => slopePoint (standardLineGraphFrame (K i)) (A i)

theorem canonicalProductGraphPoint_zero :
    canonicalProductGraphPoint K 0=firstCoordinateProduct K := by
  funext i
  apply (projectiveProjectionEquiv (K i)).symm.injective
  change (projectiveProjectionEquiv (K i)).symm (slopePoint (standardLineGraphFrame (K i)) 0)=
    (projectiveProjectionEquiv (K i)).symm (projectiveProjectionEquiv (K i) (firstCoordinateProjection (K i)))
  rw [projectiveProjectionEquiv_symm_slopePoint,standard_graphProjection_zero,Equiv.symm_apply_apply]

variable [Fintype ι]

def productSlopeEvaluationEquiv : ProjectiveProductModel K ≃L[ℂ] ((Σ i, Fin (K i)) → ℂ) :=
  ((LinearEquiv.piCongrRight (fun i => (slopeEvaluationOneEquiv (K i)).toLinearEquiv)).trans
    (LinearEquiv.piCurry ℂ (fun i (_ : Fin (K i)) => ℂ)).symm).toContinuousLinearEquiv

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_ZeroSign
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Real signs of complex derivatives and signed regular-zero coordinates. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- The genuine product graph chart used for the canonical zero. -/
def canonicalProductGraphChart :
    OpenPartialHomeomorph (ProjectiveProduct K) (ProjectiveProductModel K) :=
  OpenPartialHomeomorph.pi (fun i => grassmannChart (standardLineGraphFrame (K i)))

theorem canonicalProduct_zero_in_chart :
    firstCoordinateProduct K ∈ (canonicalProductGraphChart K).source := by
  rw [← canonicalProductGraphPoint_zero K]
  intro i hi
  exact graphPlane_inChart (standardLineGraphFrame (K i)) 0

theorem canonicalProductGraphChart_zero :
    canonicalProductGraphChart K (firstCoordinateProduct K) = 0 := by
  rw [← canonicalProductGraphPoint_zero K]
  funext i
  exact slopeCoordinate_point (standardLineGraphFrame (K i)) 0

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_HyperplaneLocal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Relative section classes and local homology at hyperplane product zeros. -/

open Bundle Topology CategoryTheory
section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

theorem canonicalProductGraphChart_target_univ :
    (canonicalProductGraphChart K).target = Set.univ := by
  ext A
  simp [canonicalProductGraphChart]

/-- The actual open neighborhood of the unique zero is homeomorphic to
the full complex graph model, with the inherited topology on the neighborhood. -/
def canonicalProductChartHomeomorph :
    (canonicalProductGraphChart K).source ≃ₜ ProjectiveProductModel K :=
  (canonicalProductGraphChart K).toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr (canonicalProductGraphChart_target_univ K)).trans
      (Homeomorph.Set.univ _))

theorem canonicalProductChartHomeomorph_zero :
    canonicalProductChartHomeomorph K
      ⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩ = 0 :=
  canonicalProductGraphChart_zero K

def canonicalLocalSectionHomeomorph :
    (canonicalProductGraphChart K).source ≃ₜ ((Σ i, Fin (K i)) → ℂ) :=
  (canonicalProductChartHomeomorph K).trans (productSlopeEvaluationEquiv K).toHomeomorph

theorem canonicalLocalSectionHomeomorph_zero :
    canonicalLocalSectionHomeomorph K
      ⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩ = 0 := by
  change productSlopeEvaluationEquiv K (canonicalProductChartHomeomorph K _) = 0
  rw [canonicalProductChartHomeomorph_zero]
  exact map_zero _

/-- Local section-coordinate isomorphism for the actual punctured chart,
not just an abstract vector-space model. Excision into the full base is separate. -/
def canonicalLocalRelativeHomologyIso (n : ℕ) :
    relativeSingularHomology (subspaceInclusion
      ({⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩}ᶜ :
        Set (canonicalProductGraphChart K).source)) n ≅
      relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set ((Σ i, Fin (K i)) → ℂ))) n :=
  relativeHomologyHomeomorphIso (canonicalLocalSectionHomeomorph K) _ _ (fun P => by
    change (P ≠ ⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩) ↔
      canonicalLocalSectionHomeomorph K P ≠ 0
    rw [← canonicalLocalSectionHomeomorph_zero K]
    exact (not_congr (canonicalLocalSectionHomeomorph K).injective.eq_iff).symm) n

/-- Inclusion of the punctured chart into the punctured whole base. Its
induced map is constructed; no excision isomorphism is asserted here. -/
def canonicalChartRelativeInclusion (n : ℕ) :=
  relativeHomologyMap
    (subspaceInclusion
      ({⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩}ᶜ :
        Set (canonicalProductGraphChart K).source))
    (subspaceInclusion ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K)))
    (subspaceMap _ _ ⟨Subtype.val, continuous_subtype_val⟩ (by
      intro P hP
      change (P : ProjectiveProduct K) ≠ firstCoordinateProduct K
      intro hz
      exact hP (Subtype.ext hz)))
    (subspaceInclusion (canonicalProductGraphChart K).source)
    (subspaceMap_square _ _ _ _) n

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Excision
attribute [-instance] _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Excision for chart-small chains, open covers, and open embeddings. -/

section
open CategoryTheory Limits
variable {X : Type} [TopologicalSpace X] (U : Set X) (x : X) (hx : x ∈ U)

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

def canonicalChartSmallRelativeIso (n : ℕ) :
    relativeSingularHomology (subspaceInclusion
      ({⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩}ᶜ :
        Set (canonicalProductGraphChart K).source)) n ≅
      (smallRelativeChains (canonicalProductGraphChart K).source
        ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))).homology n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (chartSmallRelativeChainsIso _ _ (canonicalProduct_zero_in_chart K))

/-- Exact factorization of the preserved projective-chart inclusion.
The first factor is proved invertible. The second still needs subdivision. -/
theorem canonicalChartRelativeInclusion_factor (n : ℕ) :
    canonicalChartRelativeInclusion K n =
    (canonicalChartSmallRelativeIso K n).hom ≫
        HomologicalComplex.homologyMap
          (smallRelativeComparison (canonicalProductGraphChart K).source
            ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) n := by
  change HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp]
  rw [chartSmallRelativeChainsIso_comparison]
  rfl

theorem canonicalChartRelativeInclusion_isIso_of_smallChains
    (h : QuasiIso (smallSingularChainInclusion (canonicalProductGraphChart K).source
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K)))) (n : ℕ) :
    IsIso (canonicalChartRelativeInclusion K n) := by
  have hq := smallRelativeComparison_quasiIso _ _ h
  have hi := (quasiIsoAt_iff_isIso_homologyMap _ n).mp ((quasiIso_iff _).mp hq n)
  rw [canonicalChartRelativeInclusion_factor]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (canonicalChartSmallRelativeIso K n).isIso_hom hi

theorem canonicalChart_punctured_open_cover :
    IsOpen (canonicalProductGraphChart K).source ∧
    IsOpen ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K)) ∧
    (canonicalProductGraphChart K).source ∪
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K)) = Set.univ :=
  ⟨(canonicalProductGraphChart K).open_source, isClosed_singleton.isOpen_compl,
    chart_punctured_cover _ _ (canonicalProduct_zero_in_chart K)⟩

end

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X] (U V : Set X)

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- The preserved canonical projective-chart relative inclusion is now
proved invertible, with no small-chain or excision premise. -/
theorem canonicalChartRelativeInclusion_isIso (n : ℕ) :
    IsIso (canonicalChartRelativeInclusion K n) := by
  obtain ⟨hU, hV, hUV⟩ := canonicalChart_punctured_open_cover K
  exact canonicalChartRelativeInclusion_isIso_of_smallChains K
    (smallSingularChainInclusion_quasiIso _ _ hU hV hUV) n

/-- Actual local singular homology equivalence for the canonical chart. -/
def canonicalChartExcisionIso (n : ℕ) :=
  @asIso _ _ _ _ (canonicalChartRelativeInclusion K n) (canonicalChartRelativeInclusion_isIso K n)

end

open CategoryTheory Limits HomologicalComplex

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Thom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Thom spaces of line stages, disk collapse, quotient maps, and homology. -/

section
open Bundle Topology Set OnePoint

open ComplexGrassmann
variable {ι : Type} [Fintype ι] {K : ι → ℕ}

instance lineStageTotal_locallyCompactSpace (a : LineStage K) :
    LocallyCompactSpace (TotalSpace a.Model a.Fiber) :=
  ChartedSpace.locallyCompactSpace (ProjectiveProduct K × a.Model) _

end

open Bundle Topology CategoryTheory OnePoint

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Sphere
attribute [-instance] _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Suspension homology and integral top generators of spheres. -/

section
open CategoryTheory ContinuousMap

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- The local relative homology of the actual projective chart at its
canonical zero is now compared with ordinary sphere homology. -/
def canonicalChartSphereHomologyIso (n : ℕ) (hn : n ≠ 0) :
    relativeSingularHomology (subspaceInclusion
      ({⟨firstCoordinateProduct K, canonicalProduct_zero_in_chart K⟩}ᶜ :
        Set (canonicalProductGraphChart K).source)) (n+1) ≅
      (integralSingularHomology n).obj
        (TopCat.of (Metric.sphere (0 : ((Σ i, Fin (K i)) → ℂ)) 1)) :=
  canonicalLocalRelativeHomologyIso K (n+1) ≪≫
    localVectorSphereHomologyIso _ n hn

end

open CategoryTheory Limits Metric

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_ProjectiveLocal
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Nonzero local classes and local homology of projective spaces and products. -/

section
open CategoryTheory Metric
open ComplexGrassmann

variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- Local relative integral homology at the canonical point of the full
projective product is ℤ in its real dimension. -/
def canonicalProductLocalHomologyIso (hp : 0 < ∑ i, K i) :
    relativeSingularHomology (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (2 * (∑ i, K i)) ≅
        ModuleCat.of ℤ ℤ := by
  let p := ∑ i, K i
  have hdim : Module.finrank ℝ ((Σ i, Fin (K i)) → ℂ) = (2*p-2)+2 := by
    rw [canonicalCoordinateSpace_real_finrank]
    dsimp [p]
    omega
  let e := (canonicalChartExcisionIso K ((2*p-2)+2)).symm ≪≫
    canonicalChartSphereHomologyIso K ((2*p-2)+1) (by dsimp [p]; omega) ≪≫
      finiteDimensionalSphereTopHomologyIso ((Σ i, Fin (K i)) → ℂ) (2*p-2) hdim
  have he : (2*p-2)+2 = 2*p := by dsimp [p]; omega
  rw [he] at e
  exact e

/-- A specific primitive integral local class, obtained from 1 under the
proved local homology isomorphism. Its orientation is the chosen recursive
coordinate orientation; comparison with the standard complex orientation is separate. -/
def canonicalProductLocalGenerator (hp : 0 < ∑ i, K i) :
    relativeSingularHomology (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (2 * (∑ i, K i)) :=
  (canonicalProductLocalHomologyIso K hp).inv (1 : ℤ)

end

section
open CategoryTheory Limits

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- An actual full product graph chart containing any specified projective point. -/
def projectivePointChart (P : ProjectiveProduct K) :
    OpenPartialHomeomorph (ProjectiveProduct K) (ProjectiveProductModel K) :=
  OpenPartialHomeomorph.pi (fun i =>
    grassmannChart (Classical.choose (grassmann_atlas_covers (P i))))

theorem projectivePointChart_mem (P : ProjectiveProduct K) :
    P ∈ (projectivePointChart K P).source :=
  fun i _ => Classical.choose_spec (grassmann_atlas_covers (P i))

theorem projectivePointChart_target (P : ProjectiveProduct K) :
    (projectivePointChart K P).target = Set.univ := by
  ext A
  simp [projectivePointChart]

def projectivePointChartHomeomorph (P : ProjectiveProduct K) :
    (projectivePointChart K P).source ≃ₜ ProjectiveProductModel K :=
  (projectivePointChart K P).toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr (projectivePointChart_target K P)).trans (Homeomorph.Set.univ _))

/-- Local homology at every point of the actual projective product, rather
than only at the canonical section zero, has the genuine coordinate comparison. -/
def projectivePointLocalCoordinateIso (P : ProjectiveProduct K) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K))) n ≅
      relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set (ProjectiveProductModel K))) n :=
  openChartCoordinateLocalHomologyIso _ (projectivePointChart K P).open_source P
    (projectivePointChart_mem K P) (projectivePointChartHomeomorph K P) n

/-- Every actual projective point has local integral homology concentrated
in the real dimension of the product. -/
theorem projectivePointLocalHomology_isZero (hp : 0 < ∑ i, K i)
    (P : ProjectiveProduct K) (n : ℕ) (hn : n ≠ 2*(∑ i, K i)) :
    IsZero (relativeSingularHomology
      (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K))) n) := by
  have hd : 2 ≤ Module.finrank ℝ (ProjectiveProductModel K) := by
    rw [projectiveProduct_real_finrank]
    omega
  have hne : n ≠ Module.finrank ℝ (ProjectiveProductModel K) := by
    rwa [projectiveProduct_real_finrank]
  exact (localVectorHomology_isZero (ProjectiveProductModel K) hd n hne).of_iso
    (projectivePointLocalCoordinateIso K P n)

end

open CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_ProjectiveClass
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Localization, top homology, and the fundamental class of projective products. -/

section
open CategoryTheory Limits
open ComplexGrassmann

instance projectiveSpaceZero_nonempty : Nonempty (Grassmann 1 0) :=
  ⟨graphPoint (standardLineGraphFrame 0) 0⟩

open ComplexGrassmann

end

section
open Set Topology ContinuousMap
namespace ComplexGrassmann
variable {ι : Type} (K : ι → ℕ)

instance instTopologicalSpaceCoordinatePunctureFactor (P : ProjectiveProduct K) (T : Finset ι) (i : ι) :
    TopologicalSpace (coordinatePunctureFactor K P T i) :=
  inferInstanceAs (TopologicalSpace {Q : Grassmann 1 (K i) // i ∈ T → Q ≠ P i})

def coordinatePunctureIntersectionHomeomorph (P : ProjectiveProduct K) (T : Finset ι) :
    (⋂ i ∈ T, projectiveCoordinatePuncture K P i) ≃ₜ
      (∀ i, coordinatePunctureFactor K P T i) where
  toFun Q i := ⟨Q.val i, fun hi => (mem_iInter.mp (mem_iInter.mp Q.property i) hi)⟩
  invFun Q := ⟨fun i => (Q i).val, mem_iInter.mpr (fun i => mem_iInter.mpr (Q i).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi (fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (continuous_pi (fun i => continuous_subtype_val.comp
    (continuous_apply i))).subtype_mk _

def coordinatePunctureFactorHomotopyEquiv (P : ProjectiveProduct K) (T : Finset ι)
    (hT : ∀ i ∈ T, 0 < K i) (i : ι) :
    coordinatePunctureFactor K P T i ≃ₕ Grassmann 1 (coordinatePunctureDimensions K T i) := by
  classical
  by_cases hi : i ∈ T
  · have he : ({Q : Grassmann 1 (K i) | i ∈ T → Q ≠ P i}) = {P i}ᶜ := by
      ext Q
      simp [hi]
    let e := (Homeomorph.setCongr he).toHomotopyEquiv
    have hk := hT i hi
    have hgen : ∀ k : ℕ, 0 < k → ∀ Q : Grassmann 1 k,
        ({Q}ᶜ : Set (Grassmann 1 k)) ≃ₕ Grassmann 1 (k-1) := by
      intro k hk Q
      cases k with
      | zero => omega
      | succ k => exact projectivePointPunctureLowerHomotopyEquiv Q
    have hd : coordinatePunctureDimensions K T i = K i - 1 := ite_eq_left hi
    rw [hd]
    exact e.trans (hgen (K i) hk (P i))
  · have he : ({Q : Grassmann 1 (K i) | i ∈ T → Q ≠ P i}) = univ := by
      ext Q
      simp [hi]
    have hd : coordinatePunctureDimensions K T i = K i := ite_eq_right hi
    rw [hd]
    exact ((Homeomorph.setCongr he).trans (Homeomorph.Set.univ _)).toHomotopyEquiv

/-- Every nonempty coordinate-puncture intersection retracts to the actual
projective product with one dimension removed in each punctured factor. -/
def coordinatePunctureIntersectionHomotopyEquiv (P : ProjectiveProduct K) (T : Finset ι)
    (hT : ∀ i ∈ T, 0 < K i) :
    (⋂ i ∈ T, projectiveCoordinatePuncture K P i) ≃ₕ
      ProjectiveProduct (coordinatePunctureDimensions K T) :=
  (coordinatePunctureIntersectionHomeomorph K P T).toHomotopyEquiv.trans
    (HomotopyEquiv.piCongrRight (coordinatePunctureFactorHomotopyEquiv K P T hT))

end ComplexGrassmann

end

section
open CategoryTheory Limits
open ComplexGrassmann
variable {ι : Type} [Fintype ι]

/-- A zero-dimensional projective product is a single point, including an
empty index type. -/
theorem projectiveProductZero_contractible (K : ι → ℕ) (hK : ∑ i, K i = 0) :
    ContractibleSpace (ProjectiveProduct K) := by
  have hzero (i) : K i = 0 := by
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (K j)) (Finset.mem_univ i)
    omega
  let : Subsingleton (ProjectiveProduct K) := ⟨fun P Q => funext (fun i => by
    have hs : Subsingleton (Grassmann 1 (K i)) := by rw [hzero i]; infer_instance
    exact hs.elim _ _)⟩
  let : Nonempty (ProjectiveProduct K) := ⟨firstCoordinateProduct K⟩
  infer_instance

/-- A coordinate-puncture cover converts already-proved lower-dimensional
absolute vanishing into puncture vanishing two degrees below the real dimension. -/
theorem projectiveProductPunctureHomology_from_lower (K : ι → ℕ)
    (hp : 0 < ∑ i, K i)
    (hlower : ∀ L : ι → ℕ, (∑ i, L i) < ∑ i, K i → ∀ q : ℕ, 2*(∑ i, L i) < q →
      IsZero ((integralSingularHomology q).obj (TopCat.of (ProjectiveProduct L))))
    (P : ProjectiveProduct K) (n : ℕ) (hn : 2*(∑ i, K i)-2 < n) :
    IsZero ((integralSingularHomology n).obj (TopCat.of ({P}ᶜ : Set (ProjectiveProduct K)))) := by
  classical
  let S := Finset.univ.filter (fun i => 0 < K i)
  have hs : S.Nonempty := by
    obtain ⟨i, hi, hKi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (by omega : ∑ i, K i ≠ 0)
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, by omega⟩⟩
  have hpos : ∀ i ∈ S, 0 < K i := fun i hi => (Finset.mem_filter.mp hi).2
  have hdim := coordinatePunctureDimensions_sum K S hpos
  have hcard : S.card ≤ n+1 := by omega
  have hz := finiteOpenUnionHomology_isZero S (projectiveCoordinatePuncture K P) hs
    (fun i _ => projectiveCoordinatePuncture_open K P i) n hcard (by
      intro T ht hts q hq
      have hT : ∀ i ∈ T, 0 < K i := fun i hi => hpos i (hts hi)
      have hd := coordinatePunctureDimensions_sum K T hT
      have hc := Finset.card_pos.mpr ht
      have hl := hlower (coordinatePunctureDimensions K T) (by omega) q (by omega)
      exact hl.of_iso (integralHomologyHomotopyIso
        (coordinatePunctureIntersectionHomotopyEquiv K P T hT) q))
  rw [projectiveCoordinatePunctures_cover K P] at hz
  exact hz

/-- Genuine integral homology of every finite projective product vanishes
above its real dimension. The strong induction uses the coordinate-puncture
cover, the proved puncture retractions, and the actual relative exact sequence. -/
theorem projectiveProductHomology_above_dimension (K : ι → ℕ)
    (n : ℕ) (hn : 2*(∑ i, K i) < n) :
    IsZero ((integralSingularHomology n).obj (TopCat.of (ProjectiveProduct K))) := by
  have hall : ∀ p : ℕ, ∀ L : ι → ℕ, (∑ i, L i) = p → ∀ q : ℕ, 2*p < q →
      IsZero ((integralSingularHomology q).obj (TopCat.of (ProjectiveProduct L))) := by
    intro p
    induction p using Nat.strong_induction_on with
    | h p ih =>
      intro L hL q hq
      by_cases hp : p = 0
      · have hzero : ∑ i, L i = 0 := hL.trans hp
        let := projectiveProductZero_contractible L hzero
        exact integralSingularHomology_isZero_contractible _ q (by omega)
      · let P := firstCoordinateProduct L
        have hpos : 0 < ∑ i, L i := by omega
        have hpuncture := projectiveProductPunctureHomology_from_lower L hpos
          (fun M hM r hr => ih (∑ i, M i) (by omega) M rfl r hr) P q (by omega)
        exact (relativeHomology_exact_at_absolute
          (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct L))) q).isZero_of_both_isZero
          hpuncture (projectivePointLocalHomology_isZero L hpos P q (by omega))
  exact hall (∑ i, K i) K rfl n hn

/-- Removing any point from any positive-dimensional projective product
kills homology above real dimension minus two. -/
theorem projectiveProductPunctureHomology_isZero (K : ι → ℕ) (hp : 0 < ∑ i, K i)
    (P : ProjectiveProduct K) (n : ℕ) (hn : 2*(∑ i, K i)-2 < n) :
    IsZero ((integralSingularHomology n).obj (TopCat.of ({P}ᶜ : Set (ProjectiveProduct K)))) :=
  projectiveProductPunctureHomology_from_lower K hp
    (fun L _ q hq => projectiveProductHomology_above_dimension L q hq) P n hn

theorem projectiveProductTopBoundary_zero (K : ι → ℕ) (hp : 0 < ∑ i, K i)
    (P : ProjectiveProduct K) :
    relativeHomologyBoundary (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K)))
      (2*(∑ i, K i)-1) = 0 :=
  (projectiveProductPunctureHomology_isZero K hp P _ (by omega)).eq_of_tgt _ _

end

open CategoryTheory Limits
section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- Top-degree localization is the actual absolute-to-relative map and is
invertible at every point of every positive-dimensional projective product. -/
def projectiveProductTopLocalizationIso (hp : 0 < ∑ i, K i) (P : ProjectiveProduct K) :
    (integralSingularHomology (2*(∑ i, K i))).obj (TopCat.of (ProjectiveProduct K)) ≅
      relativeSingularHomology (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K)))
        (2*(∑ i, K i)) := by
  let j := subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K))
  apply (LinearEquiv.ofBijective (absoluteToRelative j (2*(∑ i, K i))).hom ?_).toModuleIso
  constructor
  · apply (absoluteToRelative j (2*(∑ i, K i))).hom.ker_eq_bot.mp
    rw [← (relativeHomology_exact_at_absolute j (2*(∑ i, K i))).moduleCat_range_eq_ker]
    have hz : (integralSingularHomology (2*(∑ i, K i))).map j = 0 :=
      (projectiveProductPunctureHomology_isZero K hp P _ (by omega)).eq_of_src _ _
    change LinearMap.range ((integralSingularHomology (2*(∑ i, K i))).map j).hom = ⊥
    rw [hz]
    exact LinearMap.range_zero
  · have he : 2*(∑ i, K i) = (2*(∑ i, K i)-1)+1 := by omega
    rw [he]
    intro z
    apply (relativeClass_lifts_iff j (2*(∑ i, K i)-1) z).mp
    rw [projectiveProductTopBoundary_zero K hp P]
    rfl

/-- The unique actual global lift of the PRESERVED canonical local generator.
This construction is unconditional apart from positive total dimension. -/
def projectiveProductFundamentalClass (hp : 0 < ∑ i, K i) :
    (integralSingularHomology (2*(∑ i, K i))).obj (TopCat.of (ProjectiveProduct K)) :=
  (projectiveProductTopLocalizationIso K hp (firstCoordinateProduct K)).inv
    (canonicalProductLocalGenerator K hp)

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_GraphCover
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Projective graph denominators, intersections, and finite graph covers. -/

section
open Set Topology
namespace ComplexGrassmann
variable {ι J : Type} [Fintype ι] [Fintype J] (K : ι → ℕ)

def projectiveProductGraphChart (F : ∀ i, GraphFrame 1 (K i)) :
    OpenPartialHomeomorph (ProjectiveProduct K) (ProjectiveProductModel K) :=
  OpenPartialHomeomorph.pi (fun i => grassmannChart (F i))

theorem projectiveProductGraphChart_target (F : ∀ i, GraphFrame 1 (K i)) :
    (projectiveProductGraphChart K F).target = univ := by
  ext A
  simp [projectiveProductGraphChart]

def projectiveProductGraphHomeomorph (F : ∀ i, GraphFrame 1 (K i)) :
    (projectiveProductGraphChart K F).source ≃ₜ ProjectiveProductModel K :=
  (projectiveProductGraphChart K F).toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr (projectiveProductGraphChart_target K F)).trans (Homeomorph.Set.univ _))

def productGraphDenominatorLinear (F : ∀ i, GraphFrame 1 (K i))
    (G : J → ∀ i, GraphFrame 1 (K i)) (ji : J × ι) : ProjectiveProductModel K →L[ℝ] ℂ :=
  ((graphDenominatorLinear (F ji.2) (G ji.1 ji.2)).restrictScalars ℝ).comp
    (ContinuousLinearMap.proj ji.2)

omit [Fintype J] in
/-- Simultaneous membership in any finite family of actual graph charts
is exactly a finite affine nonvanishing condition in a fixed graph chart. -/
theorem productGraph_multi_overlap_iff (F : ∀ i, GraphFrame 1 (K i))
    (G : J → ∀ i, GraphFrame 1 (K i)) (A : ProjectiveProductModel K) :
    (∀ j, ((projectiveProductGraphHomeomorph K F).symm A).val ∈
      (projectiveProductGraphChart K (G j)).source) ↔
    A ∈ affineAvoidanceSet (productGraphDenominatorLinear K F G)
      (productGraphDenominatorConstant K F G) := by
  change (∀ j, ∀ i ∈ (univ : Set ι), InGraphChart (G j i)
      (slopePoint (F i) (A i)).val) ↔
    ∀ ji : J × ι, graphDenominatorLinear (F ji.2) (G ji.1 ji.2) (A ji.2) +
      graphDenominatorConstant (F ji.2) (G ji.1 ji.2) ≠ 0
  simp only [mem_univ, forall_true_left, projective_inGraphChart_iff_denominator]
  exact ⟨fun h ji => h ji.1 ji.2, fun h j i => h (j,i)⟩

def projectiveProductGraphIntersection (F : ∀ i, GraphFrame 1 (K i))
    (G : J → ∀ i, GraphFrame 1 (K i)) : Set (ProjectiveProduct K) :=
  (projectiveProductGraphChart K F).source ∩ ⋂ j, (projectiveProductGraphChart K (G j)).source

/-- Actual iterated graph-chart intersections, with their subspace
topology, have the explicit affine-complement coordinates. -/
def projectiveProductGraphIntersectionHomeomorph (F : ∀ i, GraphFrame 1 (K i))
    (G : J → ∀ i, GraphFrame 1 (K i)) :
    projectiveProductGraphIntersection K F G ≃ₜ
      affineAvoidanceSet (productGraphDenominatorLinear K F G)
        (productGraphDenominatorConstant K F G) :=
  (subspaceSubsetHomeomorph (projectiveProductGraphIntersection K F G)
    (projectiveProductGraphChart K F).source inter_subset_left).symm.trans
    ((projectiveProductGraphHomeomorph K F).subtype
      (q := fun A => A ∈ affineAvoidanceSet (productGraphDenominatorLinear K F G)
        (productGraphDenominatorConstant K F G)) (fun P => by
      have h := productGraph_multi_overlap_iff K F G (projectiveProductGraphHomeomorph K F P)
      rw [Homeomorph.symm_apply_apply] at h
      change (P.val ∈ (projectiveProductGraphChart K F).source ∧
        P.val ∈ ⋂ j, (projectiveProductGraphChart K (G j)).source) ↔ _
      simpa only [P.property, true_and, mem_iInter] using h))

end ComplexGrassmann

end

open Set

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Twisted
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Twisted hyperplane bundles, zeros, graph coordinates, and frame sections. -/

section
open Bundle Topology
namespace Kaplansky

section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedCoordinateSection (i : Option ι)
    (j : Fin (1 + twistedProjectiveDimensions K h i))
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (productLineCore (twistedProjectiveDimensions K h) (some i)).Fiber P :=
  hyperplaneFunctionalSection (coordinateFunctional j)
    (projectiveProjectionMap (twistedProjectiveDimensions K h i) (P i))

omit [Fintype ι] in
theorem continuous_twistedCoordinateSection (i : Option ι)
    (j : Fin (1 + twistedProjectiveDimensions K h i)) :
    Continuous (fun P => TotalSpace.mk' ℂ P (twistedCoordinateSection K h i j P)) := by
  have hsec := continuous_pullbackLineCore_section (projectionDualLineCore _)
    (projectiveProjectionMap (twistedProjectiveDimensions K h i))
    (hyperplaneFunctionalSection (coordinateFunctional j))
    (continuous_hyperplaneFunctionalSection _)
  exact continuous_pullbackLineCore_section (projectiveHyperplaneCore _)
    ⟨fun P : ProjectiveProduct (twistedProjectiveDimensions K h) => P i, continuous_apply i⟩ _ hsec

def twistedOldSection (s : TwistedHyperplaneSlot K h)
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s)).Fiber P :=
  match s with
  | .inl _ => (1 : ℂ)
  | .inr s => twistedCoordinateSection K h (some s.1) (positiveCoordinate (K s.1) s.2) P

def twistedNewSection (s : TwistedHyperplaneSlot K h)
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (productLineCore (twistedProjectiveDimensions K h) (some none)).Fiber P :=
  match s with
  | .inl j => twistedCoordinateSection K h none (positiveCoordinate h j) P
  | .inr _ => twistedCoordinateSection K h none 0 P

omit [Fintype ι] in
theorem continuous_twistedOldSection (s : TwistedHyperplaneSlot K h) :
    Continuous (fun P => TotalSpace.mk' ℂ P (twistedOldSection K h s P)) := by
  cases s with
  | inl j =>
    apply continuous_iff_continuousAt.mpr
    intro P
    rw [FiberBundle.continuousAt_section]
    exact continuousAt_const
  | inr s => exact continuous_twistedCoordinateSection K h _ _

omit [Fintype ι] in
theorem continuous_twistedNewSection (s : TwistedHyperplaneSlot K h) :
    Continuous (fun P => TotalSpace.mk' ℂ P (twistedNewSection K h s P)) := by
  cases s <;> exact continuous_twistedCoordinateSection K h _ _

/-- A concrete section: auxiliary positive coordinates on the h trivial
summands, and old positive coordinates multiplied by auxiliary coordinate 0
on the other summands. Its topological nonvanishing remains to be proved. -/
def twistedHyperplaneSection (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (twistedHyperplaneSumCore K h).Fiber P :=
  WithLp.toLp 2 (fun s => tensorLinePair _ _ P (twistedOldSection K h s P) (twistedNewSection K h s P))

theorem continuous_twistedHyperplaneSection :
    Continuous (fun P => TotalSpace.mk' (EuclideanSpace ℂ (TwistedHyperplaneSlot K h)) P
      (twistedHyperplaneSection K h P)) := by
  apply (continuous_finiteLineSum_iff (twistedHyperplaneLineCore K h) _).mpr
  exact ⟨continuous_id, fun s => continuous_tensorLinePair_section _ _
    (twistedOldSection K h s) (twistedNewSection K h s)
    (continuous_twistedOldSection K h s) (continuous_twistedNewSection K h s)⟩

end

open ComplexGrassmann

theorem hyperplaneFirstCoordinateSection_ne_zero (k : ℕ) :
    hyperplaneFunctionalSection (coordinateFunctional (0 : Fin (1+k)))
      (firstCoordinateProjection k) ≠ 0 := by
  let v : projectionLine (firstCoordinateProjection k) := ⟨firstCoordinateVector k, by
    rw [firstCoordinateProjection_line]
    exact Submodule.subset_span (Set.mem_singleton _)⟩
  intro hz
  have he := congrArg (fun z => projectionDualLineFiberEquiv (firstCoordinateProjection k) z v) hz
  rw [hyperplaneFunctionalSection_realization, map_zero] at he
  simp [v,coordinateFunctional,firstCoordinateVector] at he

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

omit [Fintype ι] in
theorem twistedCoordinateSection_positive_zero_iff
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) (i : Option ι) :
    (∀ j : Fin (twistedProjectiveDimensions K h i),
      twistedCoordinateSection K h i (positiveCoordinate _ j) P = 0) ↔
      P i = firstCoordinateProduct (twistedProjectiveDimensions K h) i := by
  change (∀ j, hyperplaneFunctionalSection (coordinateFunctional (positiveCoordinate _ j))
    (projectiveProjectionMap _ (P i)) = 0) ↔ _
  rw [hyperplaneCoordinateSections_common_zero]
  constructor
  · intro hp
    have he := congrArg (projectiveProjectionEquiv (twistedProjectiveDimensions K h i)) hp
    simpa [projectiveProjectionMap, firstCoordinateProduct] using he
  · intro hp
    rw [hp]
    exact (projectiveProjectionEquiv _).symm_apply_apply _

/-- The explicit twisted section has exactly one zero on the actual
augmented projective product. This is geometry, not a nonzero Euler map. -/
theorem twistedHyperplaneSection_eq_zero_iff
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    twistedHyperplaneSection K h P = 0 ↔
      P = firstCoordinateProduct (twistedProjectiveDimensions K h) := by
  constructor
  · intro hz
    have hnew : P none = firstCoordinateProduct (twistedProjectiveDimensions K h) none := by
      apply (twistedCoordinateSection_positive_zero_iff K h P none).mp
      intro j
      have he := congrArg (fun v : (twistedHyperplaneSumCore K h).Fiber P =>
        (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from v) (.inl j)) hz
      change (1 : ℂ) * (show ℂ from twistedCoordinateSection K h none (positiveCoordinate h j) P) = 0 at he
      change (show ℂ from twistedCoordinateSection K h none (positiveCoordinate h j) P) = 0
      exact (one_mul (show ℂ from twistedCoordinateSection K h none
        (positiveCoordinate h j) P)).symm.trans he
    have hnew0 : twistedCoordinateSection K h none 0 P ≠ 0 := by
      change hyperplaneFunctionalSection (coordinateFunctional (0 : Fin (1+h)))
        (projectiveProjectionMap h (P none)) ≠ 0
      rw [hnew]
      change hyperplaneFunctionalSection (coordinateFunctional (0 : Fin (1+h)))
        ((projectiveProjectionEquiv h).symm
          (projectiveProjectionEquiv h (firstCoordinateProjection h))) ≠ 0
      rw [Equiv.symm_apply_apply]
      exact hyperplaneFirstCoordinateSection_ne_zero h
    funext i
    cases i with
    | none => exact hnew
    | some i =>
      apply (twistedCoordinateSection_positive_zero_iff K h P (some i)).mp
      intro j
      have he := congrArg (fun v : (twistedHyperplaneSumCore K h).Fiber P =>
        (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from v) (.inr ⟨i,j⟩)) hz
      change (show ℂ from twistedCoordinateSection K h (some i) (positiveCoordinate (K i) j) P) *
        (show ℂ from twistedCoordinateSection K h none 0 P) = 0 at he
      exact (mul_eq_zero.mp he).resolve_right hnew0
  · rintro rfl
    change (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
      twistedHyperplaneSection K h (firstCoordinateProduct (twistedProjectiveDimensions K h))) = 0
    ext s
    cases s with
    | inl j =>
      have he := (twistedCoordinateSection_positive_zero_iff K h
        (firstCoordinateProduct (twistedProjectiveDimensions K h)) none).mpr rfl j
      change (1 : ℂ) * (show ℂ from twistedCoordinateSection K h none (positiveCoordinate h j)
        (firstCoordinateProduct (twistedProjectiveDimensions K h))) = 0
      change (show ℂ from twistedCoordinateSection K h none (positiveCoordinate h j)
        (firstCoordinateProduct (twistedProjectiveDimensions K h))) = 0 at he
      exact (congrArg (fun z : ℂ => 1*z) he).trans (mul_zero _)
    | inr s =>
      have he := (twistedCoordinateSection_positive_zero_iff K h
        (firstCoordinateProduct (twistedProjectiveDimensions K h)) (some s.1)).mpr rfl s.2
      change (show ℂ from twistedCoordinateSection K h (some s.1) (positiveCoordinate (K s.1) s.2)
        (firstCoordinateProduct (twistedProjectiveDimensions K h))) * _ = 0
      change (show ℂ from twistedCoordinateSection K h (some s.1) (positiveCoordinate (K s.1) s.2)
        (firstCoordinateProduct (twistedProjectiveDimensions K h))) = 0 at he
      exact (congrArg (fun z : ℂ => z * (show ℂ from twistedNewSection K h (.inr s)
        (firstCoordinateProduct (twistedProjectiveDimensions K h)))) he).trans (zero_mul _)

end Kaplansky

end

section
open Bundle Topology Set
namespace Kaplansky
open ComplexGrassmann
variable {ι A : Type} [Fintype ι] [TopologicalSpace A] (K : ι → ℕ)
  (U : Set (ProjectiveProduct K)) (e : U ≃ₜ A)
  (F : ∀ i, GraphFrame 1 (K i))
  (hF : U ⊆ (projectiveProductGraphChart K F).source)

def productGraphLineProjection (i : ι) : C(A,projectionSpace (1+K i) 1) :=
  (projectiveProjectionMap (K i)).comp
    ((⟨fun P : ProjectiveProduct K => P i,continuous_apply i⟩ :
      C(ProjectiveProduct K,Grassmann 1 (K i))).comp (chartBaseMap U e))

def productGraphLineVector (i : ι) (a : A) :=
  graphLineVector (F i) (slopeCoordinate (F i) ((chartBaseMap U e a) i))

omit [Fintype ι] in
theorem productGraphLineVector_mem [Fintype ι]
    (hF : U ⊆ (projectiveProductGraphChart K F).source) (i : ι) (a : A) :
    productGraphLineVector K U e F i a ∈ projectionLine (productGraphLineProjection K U e i a) := by
  have hp : InGraphChart (F i) ((chartBaseMap U e a) i).val :=
    hF (e.symm a).property i (mem_univ i)
  have he : productGraphLineProjection K U e i a =
      graphLineProjection (F i) (slopeCoordinate (F i) ((chartBaseMap U e a) i)) := by
    rw [← projectiveProjectionEquiv_symm_slopePoint,slopePoint_coordinate _ _ hp]
    rfl
  rw [he]
  exact graphLineVector_mem _ _

omit [Fintype ι] in
theorem productGraphLineVector_ne_zero (i : ι) (a : A) :
    productGraphLineVector K U e F i a ≠ 0 := graphLineVector_ne_zero _ _

omit [Fintype ι] in
theorem continuous_productGraphLineVector [Fintype ι]
    (hF : U ⊆ (projectiveProductGraphChart K F).source) (i : ι) :
    Continuous (productGraphLineVector K U e F i) := by
  apply (continuous_graphLineVector (F i)).comp
  exact (grassmannChart (F i)).continuousOn.comp_continuous
    ((continuous_apply i).comp (chartBaseMap U e).continuous)
    (fun a => hF (e.symm a).property i (mem_univ i))

def productGraphLineEvaluation (i : ι) (a : A) :
    (pullbackLineCore (productLineCore K (some i)) (chartBaseMap U e)).Fiber a ≃ₗ[ℂ] ℂ :=
  pullbackEvaluationEquiv (productGraphLineProjection K U e i)
    (productGraphLineVector K U e F i) (productGraphLineVector_mem K U e F hF i)
    (productGraphLineVector_ne_zero K U e F i) a

/-- The graph evaluation unit also covers zero-dimensional factors. -/
def productGraphLineUnit (i : Option ι) (a : A) :
    (pullbackLineCore (productLineCore K i) (chartBaseMap U e)).Fiber a :=
  match i with
  | none => (1 : ℂ)
  | some i => (productGraphLineEvaluation K U e F hF i a).symm 1

theorem productGraphLineUnit_ne_zero (i : Option ι) (a : A) :
    productGraphLineUnit K U e F hF i a ≠ 0 := by
  cases i with
  | none => exact (one_ne_zero : (1 : ℂ) ≠ 0)
  | some i => exact fun hz => one_ne_zero ((productGraphLineEvaluation K U e F hF i a).symm.map_eq_zero_iff.mp hz)

theorem continuous_productGraphLineUnit (i : Option ι) :
    Continuous (fun a => TotalSpace.mk' ℂ a (productGraphLineUnit K U e F hF i a)) := by
  cases i with
  | none =>
    apply continuous_iff_continuousAt.mpr
    intro a
    rw [FiberBundle.continuousAt_section]
    exact continuousAt_const
  | some i =>
    exact (hyperplaneEvaluationHomeomorph (productGraphLineProjection K U e i)
      (productGraphLineVector K U e F i) (productGraphLineVector_mem K U e F hF i)
      (productGraphLineVector_ne_zero K U e F i) (continuous_productGraphLineVector K U e F hF i)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)

end Kaplansky

end

section
open Bundle Topology Set CategoryTheory
namespace Kaplansky
open ComplexGrassmann
variable {ι A : Type} [Fintype ι] [TopologicalSpace A] (K : ι → ℕ) (h : ℕ)
  (U : Set (ProjectiveProduct (twistedProjectiveDimensions K h))) (e : U ≃ₜ A)
  (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
  (hF : U ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source)

def twistedGraphLineUnit (s : TwistedHyperplaneSlot K h) (a : A) :
    (pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U e)).Fiber a :=
  tensorLinePair
    (pullbackLineCore (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s)) (chartBaseMap U e))
    (pullbackLineCore (productLineCore (twistedProjectiveDimensions K h) (some none)) (chartBaseMap U e)) a
    (productGraphLineUnit (twistedProjectiveDimensions K h) U e F hF (twistedOldLabel K h s) a)
    (productGraphLineUnit (twistedProjectiveDimensions K h) U e F hF (some none) a)

theorem twistedGraphLineUnit_ne_zero (s : TwistedHyperplaneSlot K h) (a : A) :
    twistedGraphLineUnit K h U e F hF s a ≠ 0 :=
  tensorLinePair_ne_zero _ _ _ _ _
    (productGraphLineUnit_ne_zero _ _ _ _ _ _ _) (productGraphLineUnit_ne_zero _ _ _ _ _ _ _)

theorem continuous_twistedGraphLineUnit (s : TwistedHyperplaneSlot K h) :
    Continuous (fun a => TotalSpace.mk' ℂ a (twistedGraphLineUnit K h U e F hF s a)) := by
  exact continuous_tensorLinePair_section _ _ _ _
    (continuous_productGraphLineUnit _ _ _ _ _ _) (continuous_productGraphLineUnit _ _ _ _ _ _)

/-- Genuine linear coordinates for the original twisted bundle, over
any subset of any product graph chart. -/
def twistedGraphBundleCoordinates : twistedGraphBundleDomain K h U ≃ₜ
    A × (TwistedHyperplaneSlot K h → ℂ) :=
  (lineSumChartPullbackHomeomorph (twistedHyperplaneLineCore K h) U e).symm.trans
    (finiteLineFrameHomeomorph
      (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U e))
      (twistedGraphLineUnit K h U e F hF) (twistedGraphLineUnit_ne_zero K h U e F hF)
      (continuous_twistedGraphLineUnit K h U e F hF))

theorem twistedGraphBundleCoordinates_zero_iff (z : twistedGraphBundleDomain K h U) :
    (twistedGraphBundleCoordinates K h U e F hF z).2 = 0 ↔ z.1.2 = 0 :=
  (finiteLineFrameEquiv _ (twistedGraphLineUnit K h U e F hF)
    (twistedGraphLineUnit_ne_zero K h U e F hF) _).map_eq_zero_iff

def twistedGraphBundleRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso (twistedGraphBundleCoordinates K h U e F hF)
    (Subtype.val ⁻¹' nonzeroBundle) {z : A × (TwistedHyperplaneSlot K h → ℂ) | z.2 ≠ 0}
    (fun z => (mem_nonzeroBundle z.1).trans
      (not_congr (twistedGraphBundleCoordinates_zero_iff K h U e F hF z)).symm) n

def twistedGraphBundleNormalization (n : ℕ) :=
  (twistedGraphBundleRelativeIso K h U e F hF n).hom ≫
    productPairProjection (B := A) ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)) n

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedSlopeEvaluationEquiv : ProjectiveProductModel (twistedProjectiveDimensions K h) ≃L[ℂ]
    (TwistedHyperplaneSlot K h → ℂ) :=
  (productSlopeEvaluationEquiv (twistedProjectiveDimensions K h)).trans
    (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) (twistedSlotEquiv K h).symm).toContinuousLinearEquiv

def twistedStandardFrames (i : Option ι) := standardLineGraphFrame (twistedProjectiveDimensions K h i)

abbrev twistedStandardChart := canonicalProductGraphChart (twistedProjectiveDimensions K h)
abbrev twistedStandardChartHomeomorph := canonicalProductChartHomeomorph (twistedProjectiveDimensions K h)

def twistedStandardLineUnit (s : TwistedHyperplaneSlot K h)
    (A : ProjectiveProductModel (twistedProjectiveDimensions K h)) :=
  twistedGraphLineUnit K h (twistedStandardChart K h).source
    (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl s A

/-- Actual section coordinates in the proved tensor graph trivialization. -/
def twistedStandardSectionCoordinates
    (A : ProjectiveProductModel (twistedProjectiveDimensions K h)) : TwistedHyperplaneSlot K h → ℂ :=
  fun s => (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
    twistedHyperplaneSection K h (canonicalProductGraphPoint (twistedProjectiveDimensions K h) A)) s /
    (show ℂ from twistedStandardLineUnit K h s A)

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

/-- Tensor an arbitrary old section with a homogeneous auxiliary
coordinate, preserving the original bundle topologies. -/
def twistedSectionFromVector (v : ∀ y, (twistedSourceStage K h).Fiber y)
    (j : Fin (1+h)) (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (twistedHyperplaneSumCore K h).Fiber P :=
  WithLp.toLp 2 (fun s => tensorLinePair _ _ P
    (show (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s)).Fiber P from
      (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from v (twistedOldBase K h P)) s)
    (twistedCoordinateSection K h none j P))

variable {d : ℕ}

def twistedFrameSection (f : ContinuousOrthonormalStageFrame (twistedSourceStage K h) d)
    (hd : 1+h ≤ d) (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (twistedHyperplaneSumCore K h).Fiber P :=
  ∑ j : Fin (1+h), twistedSectionFromVector K h
    (fun y => f.vector y (Fin.castLE hd j)) j P

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Normalization
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Twisted bundle graph normalization and its naturality. -/

open Bundle Topology CategoryTheory Limits Set
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

abbrev twistedGraphBundleChartDomain (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) :=
  twistedGraphBundleDomain K h (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source

def twistedGraphBundleChartNormalization (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (n : ℕ) :=
  twistedGraphBundleNormalization K h (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source
    (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) F) F subset_rfl n

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Nonvanishing twisted section classes and the stable retained-bundle obstruction. -/

section
open Bundle Topology CategoryTheory Set
namespace Kaplansky
open ComplexGrassmann

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedRestrictedSection : C((twistedStandardChart K h).source,
    twistedGraphBundleDomain K h (twistedStandardChart K h).source) :=
  ⟨fun P => ⟨⟨P.1,twistedHyperplaneSection K h P.1⟩,P.2⟩,
    ((continuous_twistedHyperplaneSection K h).comp continuous_subtype_val).subtype_mk _⟩

def twistedLocalSectionHomeomorph : (twistedStandardChart K h).source ≃ₜ
    (TwistedHyperplaneSlot K h → ℂ) :=
  (twistedStandardChartHomeomorph K h).trans (twistedSlopeEvaluationEquiv K h).toHomeomorph

theorem twistedLocalSectionHomeomorph_zero :
    twistedLocalSectionHomeomorph K h
      ⟨firstCoordinateProduct (twistedProjectiveDimensions K h),
        canonicalProduct_zero_in_chart (twistedProjectiveDimensions K h)⟩ = 0 := by
  change twistedSlopeEvaluationEquiv K h (canonicalProductChartHomeomorph _ _) = 0
  rw [canonicalProductChartHomeomorph_zero,map_zero]

def twistedLocalSectionRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso (twistedLocalSectionHomeomorph K h)
    ({⟨firstCoordinateProduct (twistedProjectiveDimensions K h),
      canonicalProduct_zero_in_chart (twistedProjectiveDimensions K h)⟩}ᶜ :
      Set (twistedStandardChart K h).source)
    ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)) (fun P => by
      change P ≠ _ ↔ twistedLocalSectionHomeomorph K h P ≠ 0
      rw [← twistedLocalSectionHomeomorph_zero K h]
      exact (not_congr (twistedLocalSectionHomeomorph K h).injective.eq_iff).symm) n

def twistedRestrictedSectionRelativeMap (n : ℕ) :=
  relativeHomologyMap
    (subspaceInclusion ({⟨firstCoordinateProduct (twistedProjectiveDimensions K h),
      canonicalProduct_zero_in_chart (twistedProjectiveDimensions K h)⟩}ᶜ :
      Set (twistedStandardChart K h).source))
    (subspaceInclusion (Subtype.val ⁻¹' nonzeroBundle :
      Set (twistedGraphBundleDomain K h (twistedStandardChart K h).source)))
    (subspaceMap _ _ (twistedRestrictedSection K h) (by
      intro P hP
      exact (mem_nonzeroBundle _).mpr (fun hz => hP
        (Subtype.ext ((twistedHyperplaneSection_eq_zero_iff K h P.1).mp hz)))))
    (TopCat.ofHom (twistedRestrictedSection K h)) (by rfl) n

def twistedOrdinaryRelativeMap (n : ℕ) :=
  relativeHomologyMap
    (subspaceInclusion ({firstCoordinateProduct (twistedProjectiveDimensions K h)}ᶜ :
      Set (ProjectiveProduct (twistedProjectiveDimensions K h))))
    (subspaceInclusion (nonzeroBundle (V := EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
      (E := (twistedHyperplaneSumCore K h).Fiber)))
    (subspaceMap _ _ ⟨_,continuous_twistedHyperplaneSection K h⟩ (by
      intro P hP
      exact (mem_nonzeroBundle _).mpr
        (fun hz => hP ((twistedHyperplaneSection_eq_zero_iff K h P).mp hz))))
    (TopCat.ofHom ⟨_,continuous_twistedHyperplaneSection K h⟩) (by rfl) n

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

def retainedTwistedSlotEquiv (m R : ℕ) :
    TwistedHyperplaneSlot (testProjectiveDimension m R) (retainedTrivialMultiplicity m R) ≃
      RetainedGroupedSlot m R where
  toFun
    | .inl j => ⟨none,j⟩
    | .inr s => ⟨some s.1,s.2⟩
  invFun
    | ⟨none,j⟩ => .inl j
    | ⟨some i,j⟩ => .inr ⟨i,j⟩
  left_inv s := by cases s <;> rfl
  right_inv s := by obtain ⟨i,j⟩ := s; cases i <;> rfl

/-- Exact slot regrouping as an actual unitary bundle isomorphism. -/
def retainedTwistedSourceUnitary (m R : ℕ) :
    UnitaryBundleEquiv
      (twistedSourceStage (testProjectiveDimension m R) (retainedTrivialMultiplicity m R)).Model
      (retainedGroupedStage m R).Model
      (twistedSourceStage (testProjectiveDimension m R) (retainedTrivialMultiplicity m R)).Fiber
      (retainedGroupedStage m R).Fiber :=
  lineSumRelabelUnitary (testProjectiveDimension m R)
    (twistedSourceLabel (testProjectiveDimension m R) (retainedTrivialMultiplicity m R))
    (fun s : RetainedGroupedSlot m R => s.1) (retainedTwistedSlotEquiv m R)
    (fun s => by cases s <;> rfl)

end Kaplansky

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

omit [IsOrderedAddMonoid S] in
theorem SemigroupDifference.rel_refl (a : SemigroupDifference S) : Rel a a := ⟨0, le_rfl⟩

theorem SemigroupDifference.rel_trans {a b c : SemigroupDifference S}
    (hab : Rel a b) (hbc : Rel b c) : Rel a c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  refine ⟨x+y+b.1+b.2, ?_⟩
  convert add_le_add hx hy using 1 <;> ac_rfl

instance instPreorderSemigroupDifference : Preorder (SemigroupDifference S) where
  le := SemigroupDifference.Rel
  le_refl := SemigroupDifference.rel_refl
  le_trans _ _ _ := SemigroupDifference.rel_trans

theorem SemigroupDifference.add_le_add {a b c d : SemigroupDifference S}
    (hab : a ≤ b) (hcd : c ≤ d) : a+c ≤ b+d := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hcd
  refine ⟨x+y, ?_⟩
  change (a.1+c.1)+(b.2+d.2)+(x+y) ≤ (b.1+d.1)+(a.2+c.2)+(x+y)
  convert _root_.add_le_add hx hy using 1 <;> ac_rfl

theorem SemigroupDifference.flip_le_flip {a b : SemigroupDifference S} (h : a ≤ b) :
    flip b ≤ flip a := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x, ?_⟩
  change b.2+a.1+x ≤ a.2+b.1+x
  simpa only [add_comm] using hx

/-- Ordered group completion: order-equivalent differences are identified.
This need not embed the original noncancellative monoid injectively. -/
abbrev SemigroupOrderedGroup (S : Type*) [AddCommMonoid S] [PartialOrder S]
    [IsOrderedAddMonoid S] := Antisymmetrization (SemigroupDifference S) (· ≤ ·)

def semigroupDifferenceClass (a : SemigroupDifference S) : SemigroupOrderedGroup S :=
  toAntisymmetrization (· ≤ ·) a

instance instZeroSemigroupOrderedGroup : Zero (SemigroupOrderedGroup S) := ⟨semigroupDifferenceClass 0⟩

instance instAddSemigroupOrderedGroup : Add (SemigroupOrderedGroup S) where
  add := Quotient.map₂ (· + ·) (fun _ _ ha _ _ hb =>
    ⟨SemigroupDifference.add_le_add ha.1 hb.1,
      SemigroupDifference.add_le_add ha.2 hb.2⟩)

instance instNegSemigroupOrderedGroup : Neg (SemigroupOrderedGroup S) where
  neg := Quotient.map SemigroupDifference.flip (fun _ _ h =>
    ⟨SemigroupDifference.flip_le_flip h.2, SemigroupDifference.flip_le_flip h.1⟩)

@[simp] theorem semigroupDifferenceClass_add (a b : SemigroupDifference S) :
    semigroupDifferenceClass (a+b) = semigroupDifferenceClass a + semigroupDifferenceClass b := rfl

@[simp] theorem semigroupDifferenceClass_zero :
    semigroupDifferenceClass (0 : SemigroupDifference S) = 0 := rfl

@[simp] theorem semigroupDifferenceClass_flip (a : SemigroupDifference S) :
    semigroupDifferenceClass a.flip = -semigroupDifferenceClass a := rfl

instance instAddCommGroupSemigroupOrderedGroup : AddCommGroup (SemigroupOrderedGroup S) where
  add_assoc a b c := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    induction c using Quotient.inductionOn with | h c =>
    exact congrArg semigroupDifferenceClass (add_assoc a b c)
  zero_add a := by
    induction a using Quotient.inductionOn with | h a =>
    exact congrArg semigroupDifferenceClass (zero_add a)
  add_zero a := by
    induction a using Quotient.inductionOn with | h a =>
    exact congrArg semigroupDifferenceClass (add_zero a)
  add_comm a b := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    exact congrArg semigroupDifferenceClass (add_comm a b)
  neg_add_cancel a := by
    induction a using Quotient.inductionOn with | h a =>
    apply Quotient.sound
    constructor
    · refine ⟨0, ?_⟩
      change a.2+a.1+0+0 ≤ 0+(a.1+a.2)+0
      simp [add_comm]
    · refine ⟨0, ?_⟩
      change 0+(a.1+a.2)+0 ≤ a.2+a.1+0+0
      simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The actual additive map from the monoid into its ordered completion. -/
def semigroupToOrderedGroup : S →+ SemigroupOrderedGroup S where
  toFun a := semigroupDifferenceClass (a,0)
  map_zero' := rfl
  map_add' a b := by
    change semigroupDifferenceClass (a+b,0) = semigroupDifferenceClass ((a,0)+(b,0))
    congr 1
    exact Prod.ext rfl (zero_add 0).symm

end

section
variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

theorem semigroupDifference_value_mono (f : S →+ G) (hf : Monotone f)
    {a b : SemigroupDifference S} (h : a ≤ b) :
    f a.1 - f a.2 ≤ f b.1 - f b.2 := by
  obtain ⟨c,hc⟩ := h
  have hh := hf hc
  simp only [map_add] at hh
  have hh' := (add_le_add_iff_right (f c)).mp hh
  exact sub_le_sub_iff.mpr hh'

/-- Every monotone additive map to an ordered group descends to the
ordered completion. This constructs the map; it does not postulate a state. -/
def semigroupOrderedGroupLift (f : S →+ G) (hf : Monotone f) : SemigroupOrderedGroup S →+ G where
  toFun := Quotient.lift (fun a : SemigroupDifference S => f a.1-f a.2)
    (fun _ _ h => le_antisymm (semigroupDifference_value_mono f hf h.1)
      (semigroupDifference_value_mono f hf h.2))
  map_zero' := by change f 0-f 0=0; simp
  map_add' a b := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    change f (a.1+b.1)-f (a.2+b.2) = (f a.1-f a.2)+(f b.1-f b.2)
    simp only [map_add]
    abel

@[simp] theorem semigroupOrderedGroupLift_apply (f : S →+ G) (hf : Monotone f) (a b : S) :
    semigroupOrderedGroupLift f hf (semigroupDifferenceClass (a,b)) = f a-f b := rfl

@[simp] theorem semigroupOrderedGroupLift_unit (f : S →+ G) (hf : Monotone f) (a : S) :
    semigroupOrderedGroupLift f hf (semigroupToOrderedGroup a) = f a := by
  change f a-f 0=f a
  simp

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Distribution
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.CuntzDimensionState.spectralMeasure_finite _root_.OAI.Kaplansky.complexCoreFiberRealModule
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

namespace CuntzDimensionState

/-- The finite spectral integral has exactly the required matrix-unit values. -/
theorem spectralValue_unit (d : CuntzDimensionState A) (n : ℕ) :
    d.spectralValue (.unit n) = (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    have h := d.spectralValue_le_norm_mul_size (.unit 0)
    have hp := d.spectralValue_nonneg (.unit 0)
    change d.spectralValue (.unit 0) ≤ ‖CStarMatrix.ofMatrix (CuntzPositiveMatrix.unit (A := A) 0).matrix‖ * ((0 : ℕ) : ℝ) at h
    rw [Nat.cast_zero, mul_zero] at h
    simpa only [Nat.cast_zero] using le_antisymm h hp
  · let := d.nontrivial
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    change (∫ t in (0 : ℝ)..‖(1 : CStarMatrix (Fin n) (Fin n) A)‖,
      d.distribution (.unit n) t) = _
    rw [norm_one]
    have he := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (f := d.distribution (.unit n)) (g := fun _ : ℝ => (n : ℝ))
      (fun t ht => d.distribution_unit_of_lt n ht.2)
    simpa using he

end CuntzDimensionState

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_FaithfulRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped InnerProductSpace ENNReal
open Kaplansky

abbrev ActualRepresentationHilbert := lp (fun z : ActualTestIndex => ActualHilbert z) 2


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Construction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder ENNReal
open Filter Topology
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) {ι : Type*} (u : Ultrafilter ι)
abbrev Sequences := BoundedProduct (fun _ : ι => A)

omit [Nontrivial A] in
lemma seq_eval_selfAdjoint {a : Sequences (A:=A) (ι:=ι)} (ha : IsSelfAdjoint a) (i : ι) :
    IsSelfAdjoint (a i) := congrArg (fun x : Sequences (A:=A) (ι:=ι) => x i) ha.star_eq

omit [Nontrivial A] in
lemma seq_eval_commute {a b : Sequences (A:=A) (ι:=ι)} (h : Commute a b) (i : ι) :
    Commute (a i) (b i) := congrArg (fun x : Sequences (A:=A) (ι:=ι) => x i) h.eq

omit [Nontrivial A] in
lemma ultra_val_tendsto (a : Sequences (A:=A) (ι:=ι)) :
    Tendsto (fun i => V.val (a i)) u (𝓝 (limUnder u (fun i => V.val (a i)))) :=
  ultra_tendsto u _ ‖a‖ (fun i => (V.bound _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero a i))

def ultra : QuasiValue (Sequences (A:=A) (ι:=ι)) where
  val a := limUnder u (fun i => V.val (a i))
  zero := by
    apply tendsto_nhds_unique (V.ultra_val_tendsto u 0)
    change Tendsto (fun _ : ι => V.val 0) u (𝓝 0)
    rw [V.zero]; exact tendsto_const_nhds
  one := by
    apply tendsto_nhds_unique (V.ultra_val_tendsto u 1)
    change Tendsto (fun _ : ι => V.val 1) u (𝓝 1)
    rw [V.one]; exact tendsto_const_nhds
  nonneg := by
    intro a ha
    exact ge_of_tendsto (V.ultra_val_tendsto u a) (Filter.Eventually.of_forall fun i =>
      V.nonneg ((boundedProduct_nonneg_iff a).mp ha i))
  mono := by
    intro a b ha hab
    exact le_of_tendsto_of_tendsto (V.ultra_val_tendsto u a) (V.ultra_val_tendsto u b)
      (Filter.Eventually.of_forall fun i => V.mono ((boundedProduct_nonneg_iff a).mp ha i)
        ((boundedProduct_le_iff a b).mp hab i))
  smul := by
    intro r a
    apply tendsto_nhds_unique (V.ultra_val_tendsto u (r • a))
    change Tendsto (fun i => V.val (r • a i)) u _
    simpa only [V.smul] using (V.ultra_val_tendsto u a).const_mul r
  bound := by
    intro a
    apply le_of_tendsto (V.ultra_val_tendsto u a).abs
    exact Filter.Eventually.of_forall fun i => (V.bound _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero a i)
  lipschitz_positive := by
    intro a b ha hb
    apply le_of_tendsto ((V.ultra_val_tendsto u a).sub (V.ultra_val_tendsto u b)).abs
    exact Filter.Eventually.of_forall fun i =>
      (V.lipschitz_positive ((boundedProduct_nonneg_iff a).mp ha i)
        ((boundedProduct_nonneg_iff b).mp hb i)).trans
        (lp.norm_apply_le_norm ENNReal.top_ne_zero (a-b) i)
  square_swap := by
    intro a
    apply tendsto_nhds_unique (V.ultra_val_tendsto u (a*star a))
    change Tendsto (fun i => V.val (a i*star (a i))) u _
    have h := V.ultra_val_tendsto u (star a*a)
    change Tendsto (fun i => V.val (star (a i)*a i)) u _ at h
    simpa only [V.square_swap] using h
  weighted_add := by
    intro a b ha hb r hr
    apply le_of_tendsto_of_tendsto (V.ultra_val_tendsto u (a+b))
      (((V.ultra_val_tendsto u a).const_mul (1+r^2)).add
        ((V.ultra_val_tendsto u b).const_mul (1+r⁻¹^2)))
    exact Filter.Eventually.of_forall fun i => V.weighted_add
      ((boundedProduct_nonneg_iff a).mp ha i) ((boundedProduct_nonneg_iff b).mp hb i) r hr
  add_commute := by
    intro a b ha hb hc
    apply tendsto_nhds_unique (V.ultra_val_tendsto u (a+b))
    convert (V.ultra_val_tendsto u a).add (V.ultra_val_tendsto u b) using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    exact V.add_commute (seq_eval_selfAdjoint ha i) (seq_eval_selfAdjoint hb i) (seq_eval_commute hc i)

def constHom : A →⋆ₐ[ℂ] Sequences (A:=A) (ι:=ι) where
  toFun a := ⟨fun _ => a,memℓp_infty ⟨‖a‖,by rintro _ ⟨i,rfl⟩; exact le_rfl⟩⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  commutes' _ := rfl

@[simp] lemma constHom_apply (a : A) (i : ι) : constHom (A:=A) (ι:=ι) a i=a := rfl


end KaplanskyConsequences.QuasiValue

end

end OAI
end


