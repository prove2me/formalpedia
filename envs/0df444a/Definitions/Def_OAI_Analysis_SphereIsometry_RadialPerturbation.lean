-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_RadialPerturbation
-- name    : OAI_Analysis_SphereIsometry_RadialPerturbation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:20:43.291646+00:00
-- url     : https://prove2.me/theorems/a268e835-2eca-4004-a28b-ea5cb6b07c3d
-- title:
--   Shortening a vector by a small radial perturbation
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $v$ be a unit vector and $y$ a vector such that every support $\varphi$ at $v$ has $\varphi(y)<0$.
--
--   1. **Dual gap.** In a finite-dimensional space there is $c<1$ such that every functional with $\|\varphi\|\le1$ and $\varphi(y)\ge0$ has $\varphi(v)\le c$, by compactness of the dual ball.
--   2. **Perturbation.** For $p>0$ there is $\delta>0$ with
--   $$
--   \|pv+\eta y\|<p\qquad(0<\eta<\delta),
--   $$
--   and $\eta$ can be chosen below any prescribed cap. Only the span of $v,y$ needs to be finite-dimensional, so this holds in every real normed space.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/RadialPerturbation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/RadialPerturbation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TingleySphereIsometry mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_TingleySphereIsometry
import Definitions.Def_OAI_Analysis_SphereIsometry_Basic
import Definitions.Def_OAI_Analysis_SphereIsometry_UnitRepresentatives
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraRealLimit
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraNormed
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraSphere
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectSequence
import Definitions.Def_OAI_Analysis_SphereIsometry_SphereCompletion
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectAttainment
import Definitions.Def_OAI_Analysis_SphereIsometry_RadialContact
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMap
import Definitions.Def_OAI_Analysis_SphereIsometry_Supports
import Definitions.Def_OAI_Analysis_SphereIsometry_PositiveConvexFace
import Definitions.Def_OAI_Analysis_SphereIsometry_ExtremalPropagation
import Definitions.Def_OAI_Analysis_SphereIsometry_PositiveScheduling
import Definitions.Def_OAI_Analysis_SphereIsometry_InvariantConvexSet
import Definitions.Def_OAI_Analysis_SphereIsometry_AlignmentSet
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapEstimate
import Definitions.Def_OAI_Analysis_SphereIsometry_DiameterBounds
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiBasic
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapBounds
import Definitions.Def_OAI_Analysis_SphereIsometry_ScalarBins
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapNoncompactness
import Definitions.Def_OAI_Analysis_SphereIsometry_ProbabilitySimplex
import Definitions.Def_OAI_Analysis_SphereIsometry_SimplexLimit
import Definitions.Def_OAI_Analysis_SphereIsometry_FiniteComplex
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricFlags
import Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionData
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricBasic
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricSupport
import Definitions.Def_OAI_Analysis_SphereIsometry_ConvexDiameter
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricMesh
import Definitions.Def_OAI_Analysis_SphereIsometry_IteratedPoints
import Definitions.Def_OAI_Analysis_SphereIsometry_SpernerFacet
import Definitions.Def_OAI_Analysis_SphereIsometry_SpernerIncidence
import Definitions.Def_OAI_Analysis_SphereIsometry_SpernerBoundary
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricRestriction
import Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionRestriction
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricIncidence
import Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionIncidence
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricZero
import Definitions.Def_OAI_Analysis_SphereIsometry_Sperner
import Definitions.Def_OAI_Analysis_SphereIsometry_SimplexFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_CompactApproximation
import Definitions.Def_OAI_Analysis_SphereIsometry_CompactConvexFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_CoefficientBins
import Definitions.Def_OAI_Analysis_SphereIsometry_ConvexCoverRegroup
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiConvexHull
import Definitions.Def_OAI_Analysis_SphereIsometry_CondensingIteration
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiTotalBounded
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiNested
import Definitions.Def_OAI_Analysis_SphereIsometry_CondensingFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_AlignedConfiguration
import Definitions.Def_OAI_Analysis_SphereIsometry_Alignment
import Definitions.Def_OAI_Analysis_SphereIsometry_ChordSecant

namespace OAI

/-!
# Small radial perturbations from strict support signs

Compactness is used only on the continuous dual of the span of two vectors.
The public result has no finite-dimensional or completeness hypothesis on the
ambient real normed space.
-/

noncomputable section

namespace Tingley

 theorem exists_dual_gap_of_supportAt_neg
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {v y : V}
    (hv : ‖v‖ = 1)
    (hneg : ∀ φ : V →L[ℝ] ℝ, SupportAt φ v → φ y < 0) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ φ : V →L[ℝ] ℝ, ‖φ‖ ≤ 1 → 0 ≤ φ y → φ v ≤ c := by
  classical
  let K : Set (V →L[ℝ] ℝ) :=
    Metric.closedBall 0 1 ∩ {φ | 0 ≤ φ y}
  have heval (z : V) : Continuous (fun φ : V →L[ℝ] ℝ => φ z) :=
    continuous_id.clm_apply continuous_const
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : V →L[ℝ] ℝ) 1).inter_right
      (isClosed_le continuous_const (heval y))
  have hzero : (0 : V →L[ℝ] ℝ) ∈ K := by simp [K]
  obtain ⟨φ₀, hφ₀, hmax⟩ := hK.exists_isMaxOn ⟨0, hzero⟩ (heval v).continuousOn
  have hφnorm : ‖φ₀‖ ≤ 1 := by
    simpa only [mem_closedBall_zero_iff] using hφ₀.1
  have hc_le : φ₀ v ≤ 1 := by
    simpa only [hv] using apply_le_norm hφnorm v
  have hc_lt : φ₀ v < 1 := by
    by_contra hnot
    have heq : φ₀ v = 1 := le_antisymm hc_le (le_of_not_gt hnot)
    have hs : SupportAt φ₀ v := ⟨hφnorm, heq.trans hv.symm⟩
    exact (not_lt_of_ge hφ₀.2) (hneg φ₀ hs)
  refine ⟨φ₀ v, ?_, hc_lt, ?_⟩
  · simpa using (isMaxOn_iff.mp hmax) 0 hzero
  · intro φ hφ hy
    apply (isMaxOn_iff.mp hmax) φ
    exact ⟨mem_closedBall_zero_iff.mpr hφ, hy⟩

 theorem exists_radial_perturbation_lt_finiteDimensional
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {v y : V} {p : ℝ}
    (hv : ‖v‖ = 1) (hp : 0 < p)
    (hneg : ∀ φ : V →L[ℝ] ℝ, SupportAt φ v → φ y < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η → η < δ →
      ‖p • v + η • y‖ < p := by
  obtain ⟨c, _hc0, hc, hgap⟩ := exists_dual_gap_of_supportAt_neg hv hneg
  have hden : 0 < ‖y‖ + 1 := by linarith [norm_nonneg y]
  refine ⟨p * (1 - c) / (‖y‖ + 1),
    div_pos (mul_pos hp (sub_pos.mpr hc)) hden, ?_⟩
  intro η hη hηδ
  obtain ⟨φ, hφ⟩ := exists_support (p • v + η • y)
  have hnorm : ‖p • v + η • y‖ = p * φ v + η * φ y := by
    calc
      ‖p • v + η • y‖ = φ (p • v + η • y) := hφ.2.symm
      _ = p * φ v + η * φ y := by simp only [map_add, map_smul, smul_eq_mul]
  rw [hnorm]
  by_cases hnegative : φ y < 0
  · have hunit : φ v ≤ 1 := by simpa only [hv] using apply_le_norm hφ.1 v
    have hfirst : p * φ v ≤ p * 1 := mul_le_mul_of_nonneg_left hunit hp.le
    have hsecond : η * φ y < 0 := mul_neg_of_pos_of_neg hη hnegative
    nlinarith only [hfirst, hsecond]
  · have hvbound : φ v ≤ c := hgap φ hφ.1 (le_of_not_gt hnegative)
    have hybound : φ y ≤ ‖y‖ := apply_le_norm hφ.1 y
    have hfirst : p * φ v ≤ p * c := mul_le_mul_of_nonneg_left hvbound hp.le
    have hsecond : η * φ y ≤ η * ‖y‖ := mul_le_mul_of_nonneg_left hybound hη.le
    have hmul : η * (‖y‖ + 1) < p * (1 - c) := (lt_div_iff₀ hden).mp hηδ
    have hstrict : p * c + η * ‖y‖ < p := by nlinarith only [hmul, hη]
    linarith only [hfirst, hsecond, hstrict]

/-- Strict negativity on the perturbing vector for every support at a unit
vector makes all sufficiently small positive radial perturbations shorter.
Only the span of the two specified vectors is made finite-dimensional. -/
theorem exists_radial_perturbation_lt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {v y : X} {p : ℝ} (hv : ‖v‖ = 1) (hp : 0 < p)
    (hneg : ∀ φ : X →L[ℝ] ℝ, SupportAt φ v → φ y < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η → η < δ →
      ‖p • v + η • y‖ < p := by
  classical
  let V : Submodule ℝ X := Submodule.span ℝ ({v, y} : Set X)
  have hv_mem : v ∈ V := Submodule.subset_span (by simp)
  have hy_mem : y ∈ V := Submodule.subset_span (by simp)
  let v₀ : V := ⟨v, hv_mem⟩
  let y₀ : V := ⟨y, hy_mem⟩
  have : FiniteDimensional ℝ V :=
    FiniteDimensional.span_of_finite ℝ ((Set.finite_singleton y).insert v)
  have hv₀ : ‖v₀‖ = 1 := hv
  have hneg₀ : ∀ φ : V →L[ℝ] ℝ, SupportAt φ v₀ → φ y₀ < 0 :=
    (forall_supportAt_apply_iff_submodule V v₀ y₀ (fun r : ℝ => r < 0)).mp hneg
  obtain ⟨δ, hδ, hsmall⟩ := exists_radial_perturbation_lt_finiteDimensional hv₀ hp hneg₀
  refine ⟨δ, hδ, ?_⟩
  intro η hη hηδ
  exact hsmall η hη hηδ

/-- The perturbation may also be chosen below any prescribed positive cap. -/
theorem exists_radial_perturbation_lt_with_cap
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {v y : X} {p t : ℝ} (hv : ‖v‖ = 1) (hp : 0 < p) (ht : 0 < t)
    (hneg : ∀ φ : X →L[ℝ] ℝ, SupportAt φ v → φ y < 0) :
    ∃ η : ℝ, 0 < η ∧ η < t ∧ ‖p • v + η • y‖ < p := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_radial_perturbation_lt hv hp hneg
  have hm : 0 < min t δ := lt_min ht hδ
  have hη : 0 < min t δ / 2 := by linarith
  have hηt : min t δ / 2 < t := by linarith [min_le_left t δ]
  have hηδ : min t δ / 2 < δ := by linarith [min_le_right t δ]
  exact ⟨min t δ / 2, hη, hηt, hsmall _ hη hηδ⟩

end Tingley

end

end OAI


