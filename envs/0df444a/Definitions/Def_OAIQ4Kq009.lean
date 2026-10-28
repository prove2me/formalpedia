-- Prove2me | Definitions.Def_OAIQ4Kq009
-- name    : OAIQ4Kq009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T08:42:26.790199+00:00
-- url     : https://prove2.me/theorems/6fb170ef-f0bf-46cf-9d2b-94cbe4967a13
-- title:
--   Definitions bundle OAIQ4Kq009 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kaplansky.kaplansky_quasitrace_counterexample`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 163 declarations of OpenAI's Lean: 68 definitions, 5 instances and 90 theorems. The definitions and types are `OAI.Kaplansky.ActualAlgebra`, `OAI.Kaplansky.ActualDefectAlgebra`, `OAI.Kaplansky.ComplexGrassmann.productGraphDenominatorLinear`, `OAI.Kaplansky.ComplexGrassmann.projectiveProductGraphChart`, `OAI.Kaplansky.ComplexGrassmann.projectiveProductGraphHomeomorph`, `OAI.Kaplansky.ComplexGrassmann.projectiveProductGraphIntersection`, `OAI.Kaplansky.ComplexGrassmann.projectiveProductGraphIntersectionHomeomorph`, `OAI.Kaplansky.ContinuousIndependentStageFrame.normalize`, `OAI.Kaplansky.ContinuousOrthonormalStageFrame.congr`, `OAI.Kaplansky.actualAlgebraSemiring`, `OAI.Kaplansky.actualAlgebraSpectralLE`, `OAI.Kaplansky.actualAlgebraSpectralOrder`, `OAI.Kaplansky.actualAlgebra_cstar`, `OAI.Kaplansky.actualBoundedGenerator`, `OAI.Kaplansky.actualMatrixRestriction`, `OAI.Kaplansky.actualMatrixStageMap`, `OAI.Kaplansky.actualRepresentation`, `OAI.Kaplansky.actualRetainedUnitary`, `OAI.Kaplansky.actualTestOperator`, `OAI.Kaplansky.canonicalChartExcisionIso`, `OAI.Kaplansky.canonicalChartRelativeInclusion`, `OAI.Kaplansky.canonicalChartSmallRelativeIso`, `OAI.Kaplansky.canonicalChartSphereHomologyIso`, `OAI.Kaplansky.canonicalLocalRelativeHomologyIso`, `OAI.Kaplansky.canonicalLocalSectionHomeomorph`, `OAI.Kaplansky.canonicalProductChartHomeomorph`, `OAI.Kaplansky.canonicalProductGraphChart`, `OAI.Kaplansky.canonicalProductGraphPoint`, `OAI.Kaplansky.canonicalProductLocalGenerator`, `OAI.Kaplansky.canonicalProductLocalHomologyIso`, `OAI.Kaplansky.firstCoordinateProduct`, `OAI.Kaplansky.productGraphLineEvaluation`, `OAI.Kaplansky.productGraphLineProjection`, `OAI.Kaplansky.productGraphLineUnit`, `OAI.Kaplansky.productGraphLineVector`, `OAI.Kaplansky.productSlopeEvaluationEquiv`, `OAI.Kaplansky.projectivePointChart`, `OAI.Kaplansky.projectivePointChartHomeomorph`, `OAI.Kaplansky.projectivePointLocalCoordinateIso`, `OAI.Kaplansky.projectiveProductFundamentalClass` and 28 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: `BundleTests_Assembly`, `BundleTests_Base`, `BundleTests_Complement`, `BundleTests_Normalization`, `BundleTests_Normalized`, `BundleTests_Obstruction`, `BundleTests_Retained`, `BundleTests_Sequence`, `BundleTests_Smooth`, `BundleTests_Twisted`, `ComplexBundle_Avoidance`, `ComplexBundle_GrassmannManifold`, `ComplexBundle_Hyperplane`, `ComplexBundle_HyperplaneProduct`, `ComplexBundle_Orthonormal`, `ComplexBundle_PointExpansion`, `ComplexBundle_Replacement`, `ComplexBundle_SmoothLine`, `ComplexBundle_StageMaps`, `ComplexBundle_ZeroSign`, `IntegralHomology_Excision`, `IntegralHomology_GraphCover`, `IntegralHomology_HyperplaneLocal`, `IntegralHomology_Obstruction`, `IntegralHomology_ProjectiveClass`, `IntegralHomology_ProjectiveLocal`, `IntegralHomology_Sphere`, `Kaplansky_ActualAlgebra`, `Kaplansky_MatrixImage`, `Kaplansky_MatrixTest`, `Kaplansky_PolynomialTest`, `Kaplansky_Polynomials`, `Kaplansky_TestAlgebra`.
--
--   **Imports.** It imports the bundles `OAIQ4Kq005`, `OAIQ4Kq006` and `OAIQ4Kq007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ4Kq011`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ4Kq005
import Definitions.Def_OAIQ4Kq006
import Definitions.Def_OAIQ4Kq007

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_GrassmannManifold
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpacePunctureHyperplane _root_.OAI.Kaplansky.ComplexGrassmann.projectiveGrassmannCompact _root_.OAI.Kaplansky.ComplexGrassmann.projectiveGrassmannT2 _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductChartedSpace _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductCompact _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductRealManifold _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductT2 _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm
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
-- module Solutions.OAIQ4_Kq.ComplexBundle_Avoidance
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpacePunctureHyperplane _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductChartedSpace _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductRealManifold _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth
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
-- module Solutions.OAIQ4_Kq.ComplexBundle_PointExpansion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpacePunctureHyperplane _root_.OAI.Kaplansky.ComplexGrassmann.projectiveGrassmannCompact _root_.OAI.Kaplansky.ComplexGrassmann.projectiveGrassmannT2 _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductChartedSpace _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductCompact _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductRealManifold _root_.OAI.Kaplansky.ComplexGrassmann.projectiveProductT2 _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm
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
-- module Solutions.OAIQ4_Kq.ComplexBundle_Replacement
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
-- module Solutions.OAIQ4_Kq.BundleTests_Base
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact bundle-test base, prefix dimensions, and retained multiplicities. -/

namespace Kaplansky
open scoped BigOperators

theorem retainedTrivialMultiplicity_eq (m R : ℕ) :
    retainedTrivialMultiplicity m R = 64*m^2*(∑ t : Fin (R+1),4^t.val) := by
  have ht : ∀ t : Fin (R+1), testMultiplicity m R (R-t.val) 0=64*m*4^t.val := by
    intro t
    change 64*m*4^(R-(R-t.val))=64*m*4^t.val
    have he : R-(R-t.val)=t.val := by omega
    rw [he]
  unfold retainedTrivialMultiplicity
  simp_rw [ht]
  rw [← Finset.mul_sum]
  ring

theorem retainedTrivialMultiplicity_bound {m R : ℕ} (hm : 0 < m) :
    retainedTrivialMultiplicity m R < 2*m*testRank m R 0 := by
  rw [retainedTrivialMultiplicity_eq,testRank_eq]
  have h := three_sum_pow_four (R+1)
  rw [pow_succ] at h
  have hp : 0<64*m^2 := by positivity
  have hsum : (∑ t : Fin (R+1),4^t.val)<2*4^R := by omega
  have hh := Nat.mul_lt_mul_of_pos_left hsum hp
  simpa only [Nat.add_zero] using (show 64*m^2*(∑ t : Fin (R+1),4^t.val)<2*m*(64*m*4^R) from by nlinarith [hh])

end Kaplansky

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_SmoothLine
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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
-- module Solutions.OAIQ4_Kq.BundleTests_Smooth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Smooth bases and test bundles with replacement maps. -/

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
-- module Solutions.OAIQ4_Kq.BundleTests_Assembly
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm
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
-- module Solutions.OAIQ4_Kq.ComplexBundle_Orthonormal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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

namespace ContinuousIndependentStageFrame
variable {a : LineStage K}

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
-- module Solutions.OAIQ4_Kq.BundleTests_Normalized
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor
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
-- module Solutions.OAIQ4_Kq.BundleTests_Retained
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.actualHilbert_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Retained bundle labels, positive multiplicities, regrouping, and complement rank. -/

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

theorem retainedLabel_some_stage_sum (m R : ℕ) (i : Fin R) (j : Fin (R+1)) :
    (∑ a : Fin (j.val+1), if testSummandLineIndex (Nat.le_of_lt_succ j.isLt) a=some i
      then testMultiplicity m R j.val a else 0) =
      if h : i.val<j.val then testMultiplicity m R j.val ⟨i.val+1,by omega⟩ else 0 := by
  by_cases h : i.val<j.val
  · rw [dite_eq_left h]
    let a : Fin (j.val+1) := ⟨i.val+1,by omega⟩
    have he : ∀ b : Fin (j.val+1), testSummandLineIndex (Nat.le_of_lt_succ j.isLt) b=some i ↔ b=a := by
      intro b
      rw [testSummandLineIndex_eq_some,Fin.ext_iff]
    simp_rw [he]
    simp [a]
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro a _
    rw [ite_eq_right]
    rw [testSummandLineIndex_eq_some]
    omega

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
-- module Solutions.OAIQ4_Kq.ComplexBundle_StageMaps
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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
-- module Solutions.OAIQ4_Kq.Kaplansky_Polynomials
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Star-word polynomials and matrix polynomial density in the generated algebra. -/

noncomputable section
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] {N : ℕ}

theorem generatedWordPolynomial_dense (x : Fin N → A) : DenseRange (generatedWordPolynomial x) := by
  apply Metric.denseRange_iff.mpr
  intro z ε hε
  obtain ⟨p,hp⟩ := generated_exists_wordPolynomial x z hε
  refine ⟨p,?_⟩
  rw [Subtype.dist_eq,dist_eq_norm]
  change ‖(z : A)-evalStarWordPolynomial x p‖ < ε
  simpa only [norm_sub_rev] using hp

/-- Arbitrary rectangular matrices over the actual generated algebra have
finite star-polynomial approximants in their C*-matrix operator norm. -/
theorem generated_matrix_polynomial_approximation (x : Fin N → A)
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (W : CStarMatrix m n (generatedAlgebra (Set.range x))) {ε : ℝ} (hε : 0<ε) :
    ∃ p : m → n → StarWordPolynomial N,
      ‖CStarMatrix.ofMatrix (fun i j => generatedWordPolynomial x (p i j)) - W‖ < ε := by
  have hd : DenseRange (fun p : m → n → StarWordPolynomial N =>
      CStarMatrix.ofMatrix (fun i j => generatedWordPolynomial x (p i j))) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => generatedWordPolynomial_dense x))
  obtain ⟨p,hp⟩ := Metric.denseRange_iff.mp hd W ε hε
  exact ⟨p,by simpa only [dist_eq_norm,norm_sub_rev] using hp⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Sequence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.actualHilbert_nontrivial
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
-- module Solutions.OAIQ4_Kq.Kaplansky_TestAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.retainedBundle_inner _root_.OAI.Kaplansky.retainedBundle_norm
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

abbrev actualAlgebra_cstar : CStarAlgebra ActualAlgebra := inferInstance

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_MatrixImage
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor
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

/-- All matrix input coordinates are actual copies of E₀. -/
theorem actualInput_label_none (m n R : ℕ)
    (s : (towerInputStage (testSequenceStage m R) n).Slot) :
    (towerInputStage (testSequenceStage m R) n).label s=none := by
  revert s
  unfold towerInputStage
  rw [testSequenceStage_prefix (Nat.zero_le R)]
  intro s
  obtain ⟨col,⟨j,k⟩⟩ := s
  have hj : j=0 := Fin.eq_zero j
  subst j
  rfl

theorem actualInput_finrank (m n R : ℕ) (y : SmoothTestBase m R) :
    Module.finrank ℂ ((towerInputStage (testSequenceStage m R) n).Fiber y)=n*testRank m R 0 := by
  change Module.finrank ℂ (EuclideanSpace ℂ (towerInputStage (testSequenceStage m R) n).Slot)=_
  rw [finrank_euclideanSpace]
  unfold towerInputStage
  change Fintype.card (Σ _ : Fin n, (testSequenceStage m R 0).Slot)=_
  rw [Fintype.card_sigma]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  congr 1
  rw [testSequenceStage_prefix (Nat.zero_le R)]
  exact testBundleSlot_card (Nat.zero_le R)

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

theorem actualMatrixRestriction_lower_bound {m n R : ℕ} (hm : 0 < m) {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) (y : SmoothTestBase m R) (c : ℝ)
    (h : ∀ v : MatrixTowerHilbert (testSequenceStage m R) n y,
      c*‖v‖ ≤ ‖matrixPolynomialAction (testSequenceStep (R := R) hm) s t y v‖)
    (v : (towerInputStage (testSequenceStage m R) n).Fiber y) :
    c*‖v‖ ≤ ‖actualMatrixRestriction hm s t y v‖ := by
  change c*‖v‖ ≤ ‖(actualRetainedUnitary m R).fiber y
    ((bundleMatrixPolynomial (testSequenceStep (R := R) hm) s t).map y v)‖
  rw [LinearIsometryEquiv.norm_map]
  exact bundleMatrixPolynomial_lower_bound _ s t y c h v

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_MatrixTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.retainedBundle_inner _root_.OAI.Kaplansky.retainedBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Polynomial evaluation and actual matrix test operators. -/

open scoped BigOperators
namespace Kaplansky

/-- Algebraic words in the constructed bounded-product generators evaluate
as the actual Hilbert-shift words, on arbitrary Hilbert vectors. -/
theorem actualAlgebraWord_eval (z : ActualTestIndex) (w : List (Bool × Fin 24)) (v : ActualHilbert z) :
    algebraStarWord actualBoundedGenerator w z v =
      applyWord (shiftLetter (fun i j => actualTestOperator i z j)
        (fun i j => actualTestOperator_norm i z j)) w v := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨b,i⟩ := l
    cases b with
    | false =>
      change forwardShift (actualTestOperator i z) (actualTestOperator_norm i z)
        (algebraStarWord actualBoundedGenerator w z v) = _
      rw [ih]
      rfl
    | true =>
      change (forwardShift (actualTestOperator i z) (actualTestOperator_norm i z)).adjoint
        (algebraStarWord actualBoundedGenerator w z v) = _
      rw [ih]
      rfl

/-- Exact representation of the finitely supported polynomial supplied by
density, before restriction to the bottom-level bundle. -/
theorem actualAlgebraPolynomial_eval (z : ActualTestIndex) (p : StarWordPolynomial 24)
    (v : ActualHilbert z) :
    actualRepresentation z (generatedWordPolynomial actualBoundedGenerator p) v =
      ∑ w ∈ p.support, p w • applyWord (shiftLetter (fun i j => actualTestOperator i z j)
        (fun i j => actualTestOperator_norm i z j)) w v := by
  change (∑ w ∈ p.support, p w • algebraStarWord actualBoundedGenerator w) z v = _
  rw [show ((∑ w ∈ p.support, p w • algebraStarWord actualBoundedGenerator w) z) =
      ∑ w ∈ p.support, p w • algebraStarWord actualBoundedGenerator w z from by
    exact map_sum (boundedProductEval z) _ _]
  simp only [sum_apply,smul_apply]
  exact Finset.sum_congr rfl (fun w _ => congrArg (fun u => p w • u) (actualAlgebraWord_eval z w v))

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem actualRepresentation_matrix_column {m n : ℕ}
    (W : CStarMatrix (Fin m) (Fin n) ActualAlgebra)
    (h : ∀ i j, (∑ row, star (W row i)*W row j)=if i=j then 1 else 0)
    (z : ActualTestIndex) (i j : Fin n) :
    (∑ row, (actualRepresentation z (W row i)).adjoint.comp (actualRepresentation z (W row j))) =
      if i=j then ContinuousLinearMap.id ℂ (ActualHilbert z) else 0 := by
  have he := congrArg (actualRepresentation z) (h i j)
  have hstar (b : ActualAlgebra) : actualRepresentation z (star b) = (actualRepresentation z b).adjoint := rfl
  simp only [map_sum,map_mul,hstar] at he
  have hone : actualRepresentation z 1 = ContinuousLinearMap.id ℂ (ActualHilbert z) := rfl
  have hzero : actualRepresentation z 0 = 0 := rfl
  change (∑ row, (actualRepresentation z (W row i)).adjoint * (actualRepresentation z (W row j))) = _
  by_cases hij : i=j
  · simpa only [hij,ite_true,hone] using he
  · simpa only [hij,ite_false,hzero] using he

theorem actualRepresentation_matrix_entry_close {m n : ℕ}
    (P W : CStarMatrix (Fin m) (Fin n) ActualAlgebra) {δ : ℝ} (h : ‖P-W‖ < δ)
    (z : ActualTestIndex) (i : Fin m) (j : Fin n) :
    ‖actualRepresentation z (P i j)-actualRepresentation z (W i j)‖ ≤ δ := by
  have hentry := CStarMatrix.norm_entry_le_norm (M := P-W) (i := i) (j := j)
  have he := NonUnitalStarAlgHom.norm_apply_le (actualRepresentation z) ((P-W) i j)
  have hsub := map_sub (actualRepresentation z) (P i j) (W i j)
  exact (congrArg norm hsub).symm.le.trans (he.trans (hentry.trans h.le))

/-- The matrix entries supplied by density and their extracted term list
have precisely the same action on the matching actual test Hilbert space. -/
theorem actualPolynomialMatrix_action {m n : ℕ} (hm : 0 < m)
    (p : Fin m → Fin n → StarWordPolynomial 24)
    (y : SmoothTestBase m (matrixPolynomialDegree p))
    (v : MatrixTowerHilbert (testSequenceStage m (matrixPolynomialDegree p)) n y) :
    operatorMatrixAction (fun row col => actualRepresentation
      ⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩
      (generatedWordPolynomial actualBoundedGenerator (p row col))) v =
    matrixPolynomialAction (testSequenceStep (R := matrixPolynomialDegree p) hm)
      Finset.univ (matrixPolynomialTerm p) y v := by
  apply (PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Fin m => ActualHilbert ⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩)).injective
  funext row
  change operatorMatrixAction (fun r c => actualRepresentation
    (⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩ : ActualTestIndex)
    (generatedWordPolynomial actualBoundedGenerator (p r c))) v row =
    (matrixPolynomialAction (testSequenceStep (R := matrixPolynomialDegree p) hm)
      Finset.univ (matrixPolynomialTerm p) y v) row
  have hleft := operatorMatrixAction_apply (fun r c => actualRepresentation
    (⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩ : ActualTestIndex)
    (generatedWordPolynomial actualBoundedGenerator (p r c))) v row
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun col _ => actualAlgebraPolynomial_eval
    (⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩ : ActualTestIndex)
    (p row col) (v col))
  exact hleft.trans (hsum.trans (matrixPolynomialTerm_sum p _ (fun col => v col) row).symm)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_PolynomialTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial test excluding proper infiniteness of the actual algebra. -/

noncomputable section
open scoped BigOperators
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem properlyInfinite_actual_polynomial_bound {m : ℕ} (hm : 0 < m)
    (hpi : ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)) :
    ∃ p : Fin m → Fin (m+m) → StarWordPolynomial 24,
      ∀ (y : SmoothTestBase m (matrixPolynomialDegree p))
        (v : MatrixTowerHilbert (testSequenceStage m (matrixPolynomialDegree p)) (m+m) y),
        (1/2 : ℝ)*‖v‖ ≤ ‖matrixPolynomialAction
          (testSequenceStep (R := matrixPolynomialDegree p) hm) Finset.univ
          (matrixPolynomialTerm p) y v‖ := by
  obtain ⟨s,t,hs,ht,hst⟩ := hpi
  let W := properIsometryColumns s t
  let δ : ℝ := 1/(4*((m : ℝ)*(m+m)+1))
  have hd : 0 < 4*((m : ℝ)*(m+m)+1) := by positivity
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨p,hp⟩ := generated_matrix_polynomial_approximation actualBoundedGenerator W hδ
  refine ⟨p,?_⟩
  intro y v
  let z : ActualTestIndex := ⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩
  let P : CStarMatrix (Fin m) (Fin (m+m)) ActualAlgebra :=
    CStarMatrix.ofMatrix (fun i j => generatedWordPolynomial actualBoundedGenerator (p i j))
  let Wz := fun i j => actualRepresentation z (W i j)
  let Pz := fun i j => actualRepresentation z (P i j)
  have hW : ∀ v : HilbertColumns (m+m) (ActualHilbert z), ‖operatorMatrixAction Wz v‖=‖v‖ :=
    operatorMatrixAction_norm Wz
      (actualRepresentation_matrix_column W (properIsometryColumns_column s t hs ht hst) z)
  have hb := operatorMatrix_perturbation_lower_bound Pz Wz hW hδ.le
    (actualRepresentation_matrix_entry_close P W hp z) v
  have hfactor : (1/2 : ℝ) ≤ 1-(m : ℝ)*(m+m)*δ := by
    have he : δ*(4*((m : ℝ)*(m+m)+1))=1 := by
      dsimp [δ]
      field_simp
    have hnonneg : 0 ≤ (m : ℝ)*(m+m) := by positivity
    nlinarith
  simp only [Nat.cast_add] at hb
  have h := (mul_le_mul_of_nonneg_right hfactor (norm_nonneg v)).trans hb
  change (1/2 : ℝ)*‖v‖ ≤ ‖operatorMatrixAction
    (fun i j => actualRepresentation z (generatedWordPolynomial actualBoundedGenerator (p i j))) v‖ at h
  rw [actualPolynomialMatrix_action hm p y v] at h
  exact h

theorem properlyInfinite_retained_frame {m : ℕ} (hm : 0 < m)
    (hpi : ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)) :
    ∃ R : ℕ, 0<R ∧ Nonempty (ContinuousOrthonormalStageFrame (retainedLineStage m R)
      (2*m*testRank m R 0)) := by
  obtain ⟨p,hp⟩ := properlyInfinite_actual_polynomial_bound hm hpi
  let R := matrixPolynomialDegree p
  let y₀ := testBaseProjectiveHomeomorph m R (bundleTestBasePoint m R)
  let L := actualMatrixStageMap hm Finset.univ (matrixPolynomialTerm p)
  have hi : ∀ y, Function.Injective (L.map y) := fun y =>
    norm_lower_bound_injective _ (by norm_num : (0 : ℝ)<1/2)
      (actualMatrixRestriction_lower_bound hm Finset.univ (matrixPolynomialTerm p) y (1/2) (hp y))
  let f := (trivialMapFrame L (actualInput_label_none m (m+m) R) y₀ hi).normalize
  have hc : Fintype.card (towerInputStage (testSequenceStage m R) (m+m)).Slot =
      2*m*testRank m R 0 := by
    have hr := actualInput_finrank m (m+m) R y₀
    change Module.finrank ℂ (EuclideanSpace ℂ (towerInputStage (testSequenceStage m R) (m+m)).Slot)=_ at hr
    rw [finrank_euclideanSpace] at hr
    rw [hr]
    ring
  refine ⟨R,matrixPolynomialDegree_pos p,?_⟩
  rw [← hc]
  exact ⟨f⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Complement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor
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

/-- The polynomial image frame is transported to the actual line-bundle
presentation used in the Chern computation. No characteristic-class
nonvanishing or obstruction is a premise. -/
theorem properlyInfinite_regrouped_frame {m : ℕ} (hm : 0 < m)
    (hpi : ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)) :
    ∃ R : ℕ, 0<R ∧ Nonempty (ContinuousOrthonormalStageFrame (retainedGroupedStage m R)
      (2*m*testRank m R 0)) := by
  obtain ⟨R,hR,⟨f⟩⟩ := properlyInfinite_retained_frame hm hpi
  exact ⟨R,hR,⟨f.congr (retainedRegroupingUnitary m R)⟩⟩

end Kaplansky

end

open Bundle Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Hyperplane
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
-- module Solutions.OAIQ4_Kq.ComplexBundle_HyperplaneProduct
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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
-- module Solutions.OAIQ4_Kq.ComplexBundle_ZeroSign
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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
-- module Solutions.OAIQ4_Kq.IntegralHomology_HyperplaneLocal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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
-- module Solutions.OAIQ4_Kq.IntegralHomology_Excision
attribute [-instance] _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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
-- module Solutions.OAIQ4_Kq.IntegralHomology_Sphere
attribute [-instance] _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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
-- module Solutions.OAIQ4_Kq.IntegralHomology_ProjectiveLocal
attribute [-instance] _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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

theorem canonicalProductLocalGenerator_coordinate (hp : 0 < ∑ i, K i) :
    (canonicalProductLocalHomologyIso K hp).hom (canonicalProductLocalGenerator K hp) = (1 : ℤ) :=
  ConcreteCategory.congr_hom (canonicalProductLocalHomologyIso K hp).inv_hom_id 1

theorem canonicalProductLocalGenerator_ne_zero (hp : 0 < ∑ i, K i) :
    canonicalProductLocalGenerator K hp ≠ 0 := by
  intro h
  have hc := canonicalProductLocalGenerator_coordinate K hp
  rw [h, map_zero] at hc
  norm_num at hc

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
-- module Solutions.OAIQ4_Kq.IntegralHomology_ProjectiveClass
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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

theorem projectiveProductTopLocalizationIso_hom (hp : 0 < ∑ i, K i) (P : ProjectiveProduct K) :
    (projectiveProductTopLocalizationIso K hp P).hom =
      absoluteToRelative (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K)))
        (2*(∑ i, K i)) := rfl

/-- The unique actual global lift of the PRESERVED canonical local generator.
This construction is unconditional apart from positive total dimension. -/
def projectiveProductFundamentalClass (hp : 0 < ∑ i, K i) :
    (integralSingularHomology (2*(∑ i, K i))).obj (TopCat.of (ProjectiveProduct K)) :=
  (projectiveProductTopLocalizationIso K hp (firstCoordinateProduct K)).inv
    (canonicalProductLocalGenerator K hp)

theorem projectiveProductFundamentalClass_localizes (hp : 0 < ∑ i, K i) :
    absoluteToRelative (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (2*(∑ i, K i))
      (projectiveProductFundamentalClass K hp) = canonicalProductLocalGenerator K hp := by
  rw [← projectiveProductTopLocalizationIso_hom K hp]
  exact ConcreteCategory.congr_hom
    (projectiveProductTopLocalizationIso K hp (firstCoordinateProduct K)).inv_hom_id _

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_GraphCover
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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
namespace ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

theorem projectiveProductGraphCharts_cover :
    (⋃ F : ∀ i, GraphFrame 1 (K i), (projectiveProductGraphChart K F).source) = univ := by
  ext P
  simp only [mem_iUnion, mem_univ, iff_true]
  choose F hF using fun i => grassmann_atlas_covers (P i)
  exact ⟨F,fun i _ => hF i⟩

/-- Compactness supplies a genuine finite cover of the actual projective
product by graph charts. Any specified chart can be retained in the cover. -/
theorem projectiveProduct_finiteGraphCover (F₀ : ∀ i, GraphFrame 1 (K i)) :
    ∃ S : Finset (∀ i, GraphFrame 1 (K i)), F₀ ∈ S ∧
      (⋃ F ∈ S, (projectiveProductGraphChart K F).source) = univ := by
  classical
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover
    (fun F : ∀ i, GraphFrame 1 (K i) => (projectiveProductGraphChart K F).source)
    (fun F => (projectiveProductGraphChart K F).open_source)
    (by rw [projectiveProductGraphCharts_cover])
  refine ⟨insert F₀ S, by simp, subset_antisymm (subset_univ _) ?_⟩
  intro P hP
  obtain ⟨F,hF,hPF⟩ := mem_iUnion.mp (hS hP) |>.imp fun _ => mem_iUnion.mp
  exact mem_iUnion.mpr ⟨F,mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hF,hPF⟩⟩

end ComplexGrassmann

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Twisted
attribute [-instance] _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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

/-- The summands of (trivial(h) ⊕ H) tensored with the hyperplane line
from the auxiliary factor. This is an explicit vector-bundle core. -/
def twistedHyperplaneLineCore (s : TwistedHyperplaneSlot K h) :=
  tensorLineCore
    (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s))
    (productLineCore (twistedProjectiveDimensions K h) (some none))

def twistedHyperplaneSumCore := finiteLineSumCore (twistedHyperplaneLineCore K h)

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

instance twistedHyperplaneFiberNormedAddCommGroup
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    NormedAddCommGroup ((twistedHyperplaneSumCore K h).Fiber P) :=
  finiteLineSumFiberNormedAddCommGroup (twistedHyperplaneLineCore K h) P

instance twistedHyperplaneFiberInnerProductSpace
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    InnerProductSpace ℂ ((twistedHyperplaneSumCore K h).Fiber P) :=
  finiteLineSumFiberInnerProductSpace (twistedHyperplaneLineCore K h) P

abbrev twistedGraphBundleDomain :=
  {z : TotalSpace (EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
    (twistedHyperplaneSumCore K h).Fiber | z.proj ∈ U}

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

abbrev twistedStandardChart := canonicalProductGraphChart (twistedProjectiveDimensions K h)

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedSourceLabel : TwistedHyperplaneSlot K h → Option ι
  | .inl _ => none
  | .inr s => some s.1

def twistedSourceStage : LineStage K :=
  ⟨TwistedHyperplaneSlot K h,inferInstance,twistedSourceLabel K h⟩

theorem continuous_twistedOldComponent
    (v : ∀ y, (twistedSourceStage K h).Fiber y)
    (hv : Continuous (fun y => TotalSpace.mk' (twistedSourceStage K h).Model y (v y)))
    (s : TwistedHyperplaneSlot K h) :
    Continuous (fun P => TotalSpace.mk' ℂ P
      (show (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s)).Fiber P from
        (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from v (twistedOldBase K h P)) s)) := by
  have hc := ((continuous_finiteLineSumComponent
    (fun s => productLineCore K (twistedSourceLabel K h s)) s).comp hv).comp
    (twistedOldBase K h).continuous
  apply continuous_iff_continuousAt.mpr
  intro P
  rw [FiberBundle.continuousAt_section]
  have hh := (FiberBundle.continuousAt_totalSpace ℂ _ (x₀ := P)).mp hc.continuousAt |>.2
  cases s with
  | inl j => exact hh
  | inr s => exact hh

/-- Tensor an arbitrary old section with a homogeneous auxiliary
coordinate, preserving the original bundle topologies. -/
def twistedSectionFromVector (v : ∀ y, (twistedSourceStage K h).Fiber y)
    (j : Fin (1+h)) (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (twistedHyperplaneSumCore K h).Fiber P :=
  WithLp.toLp 2 (fun s => tensorLinePair _ _ P
    (show (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s)).Fiber P from
      (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from v (twistedOldBase K h P)) s)
    (twistedCoordinateSection K h none j P))

theorem continuous_twistedSectionFromVector
    (v : ∀ y, (twistedSourceStage K h).Fiber y)
    (hv : Continuous (fun y => TotalSpace.mk' (twistedSourceStage K h).Model y (v y)))
    (j : Fin (1+h)) :
    Continuous (fun P => TotalSpace.mk' (EuclideanSpace ℂ (TwistedHyperplaneSlot K h)) P
      (twistedSectionFromVector K h v j P)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  refine ⟨continuous_id,fun s => ?_⟩
  exact continuous_tensorLinePair_section _ _ _ _
    (continuous_twistedOldComponent K h v hv s) (continuous_twistedCoordinateSection K h none j)

omit [Fintype ι] in
theorem twistedCoordinateSections_not_all_zero
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    ¬ (∀ j : Fin (1+h), twistedCoordinateSection K h none j P = 0) := by
  intro hz
  have hp := (twistedCoordinateSection_positive_zero_iff K h P none).mp
    (fun j => hz (positiveCoordinate h j))
  have he := hz 0
  change hyperplaneFunctionalSection (coordinateFunctional (0 : Fin (1+h)))
    (projectiveProjectionMap h (P none)) = 0 at he
  rw [hp] at he
  change hyperplaneFunctionalSection (coordinateFunctional (0 : Fin (1+h)))
    ((projectiveProjectionEquiv h).symm (projectiveProjectionEquiv h (firstCoordinateProjection h))) = 0 at he
  rw [Equiv.symm_apply_apply] at he
  exact hyperplaneFirstCoordinateSection_ne_zero h he

variable {d : ℕ}

def twistedFrameSection (f : ContinuousOrthonormalStageFrame (twistedSourceStage K h) d)
    (hd : 1+h ≤ d) (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    (twistedHyperplaneSumCore K h).Fiber P :=
  ∑ j : Fin (1+h), twistedSectionFromVector K h
    (fun y => f.vector y (Fin.castLE hd j)) j P

theorem continuous_twistedFrameSection
    (f : ContinuousOrthonormalStageFrame (twistedSourceStage K h) d) (hd : 1+h ≤ d) :
    Continuous (fun P => TotalSpace.mk' (EuclideanSpace ℂ (TwistedHyperplaneSlot K h)) P
      (twistedFrameSection K h f hd P)) := by
  apply continuousOn_univ.mp
  apply continuousOn_bundle_sum (𝕜 := ℂ)
  intro j _
  exact (continuous_twistedSectionFromVector K h _ (f.continuous_vector _) j).continuousOn

theorem twistedFrameSection_ne_zero
    (f : ContinuousOrthonormalStageFrame (twistedSourceStage K h) d) (hd : 1+h ≤ d)
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    twistedFrameSection K h f hd P ≠ 0 := by
  intro hz
  have hind := (f.orthonormal (twistedOldBase K h P)).linearIndependent.comp
    (Fin.castLE hd) (Fin.castLE_injective hd)
  have he : (∑ j : Fin (1+h),
      (show ℂ from twistedCoordinateSection K h none j P) •
        f.vector (twistedOldBase K h P) (Fin.castLE hd j)) = 0 := by
    change (∑ j : Fin (1+h),
      (show ℂ from twistedCoordinateSection K h none j P) •
        (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
          f.vector (twistedOldBase K h P) (Fin.castLE hd j))) = 0
    change (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
      twistedFrameSection K h f hd P) = 0 at hz
    convert hz using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro j _
    ext s
    exact mul_comm _ _
  have hc := Fintype.linearIndependent_iff.mp hind _ he
  exact twistedCoordinateSections_not_all_zero K h P hc

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Normalization
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
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

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Survival of hyperplane fiber classes and nonvanishing Thom obstructions. -/

open Bundle Topology CategoryTheory Limits
section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

theorem retainedTest_hyperplaneDegree_pos {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    0 < ∑ i : Fin R, testProjectiveDimension m R i := by
  have : Nonempty (Fin R) := ⟨⟨0,hR⟩⟩
  exact Finset.sum_pos (fun i _ => testProjectiveDimension_pos hm i) Finset.univ_nonempty

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Obstruction
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

theorem twistedOrdinaryRelativeMap_comparison (n : ℕ) :
    absoluteToRelative (subspaceInclusion
      ({firstCoordinateProduct (twistedProjectiveDimensions K h)}ᶜ :
        Set (ProjectiveProduct (twistedProjectiveDimensions K h)))) n ≫
      twistedOrdinaryRelativeMap K h n =
    ordinarySectionClassMap (twistedHyperplaneSection K h)
      (continuous_twistedHyperplaneSection K h) n :=
  absoluteToRelative_naturality _ _ _ _ _ n

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
-- module Solutions.OAIQ4_Kq.Kaplansky_ActualAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The actual M48 algebra, its fixed defect pair, and its Cuntz dimension state. -/

namespace Kaplansky

section
open scoped BigOperators
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

local instance (priority := 3100) actualAlgebraSemiring : Semiring ActualAlgebra :=
  actualAlgebra_cstar.toSemiring

local instance (priority := 3000) actualAlgebraSpectralOrder : PartialOrder ActualAlgebra :=
  CStarAlgebra.spectralOrder ActualAlgebra
local instance (priority := 3000) actualAlgebraSpectralLE : LE ActualAlgebra :=
  (CStarAlgebra.spectralOrder ActualAlgebra).toLE
local instance (priority := 3000) actualAlgebraSpectralOrderedRing : StarOrderedRing ActualAlgebra :=
  CStarAlgebra.spectralOrderedRing ActualAlgebra

abbrev ActualDefectAlgebra := CStarMatrix ActualDefectIndex ActualDefectIndex ActualAlgebra

end

end Kaplansky

end

end OAI
end


