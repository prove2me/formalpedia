-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_SimplexFixedPoint
-- name    : OAI_Analysis_SphereIsometry_SimplexFixedPoint
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:52:13.148069+00:00
-- url     : https://prove2.me/theorems/0a7c74c4-42ae-4f5f-8ce2-75d29a728c37
-- title:
--   Brouwer's fixed point theorem for the probability simplex
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps.
--
--   1. **Finite coordinates.** Every continuous $P:\Delta_{m+1}\to\Delta_{m+1}$ has a fixed point, including $m=0$. Label each subdivision vertex $v$ by a coordinate $i$ with $p(v)_i>0$ and $P(p(v))_i\le p(v)_i$; this lies in its carrier. Sperner's lemma gives fully labelled cells with mesh $(m/(m+1))^k\to0$, and the shrinking-family lemma gives a fixed point.
--   2. **General index sets.** For a nonempty finite $\iota$, every continuous $P:\Delta_\iota\to\Delta_\iota$ has a fixed point:
--   $$
--   P(a)=a ,
--   $$
--   by reindexing the coordinates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/SimplexFixedPoint.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/SimplexFixedPoint.lean by skeleton subtraction
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

namespace OAI

/-!
# Fixed points in finite probability simplexes

The finite-coordinate theorem constructs its approximating points from the actual iterated
subdivision and the proved Sperner theorem. Positive coordinates enforce the boundary condition
on labels. The shrinking mesh and the labelled inequalities then give an exact fixed point.
Coordinate reindexing transports the result to every nonempty finite index type.
-/

open Filter
open scoped Topology

namespace Tingley

/-- Every continuous self-map of a probability simplex with `m + 1` coordinates has a fixed
point. The construction includes `m = 0`, the one-point simplex. -/
theorem continuous_fin_probabilitySimplex_fixedPoint (m : ℕ)
    (P : ProbabilitySimplex (Fin (m + 1)) → ProbabilitySimplex (Fin (m + 1)))
    (hP : Continuous P) : ∃ a, P a = a := by
  classical
  let point : (k : ℕ) → IterVertex m k → ProbabilitySimplex (Fin (m + 1)) :=
    fun k v => ⟨iterPoint m k v, iterPoint_mem_stdSimplex m k v⟩
  let label : (k : ℕ) → IterVertex m k → Fin (m + 1) :=
    fun k v => Classical.choose
      (exists_positive_dominating_coordinate (point k v) (P (point k v)))
  have hlabel (k : ℕ) (v : IterVertex m k) :
      0 < (point k v).val (label k v) ∧
        (P (point k v)).val (label k v) ≤ (point k v).val (label k v) :=
    Classical.choose_spec
      (exists_positive_dominating_coordinate (point k v) (P (point k v)))
  have hcarrier (k : ℕ) (v : IterVertex m k) : label k v ∈ iterCarrier m k v :=
    (iterPoint_pos_iff m k v (label k v)).mp (hlabel k v).1
  have hcells (k : ℕ) :
      ∃ s, s ∈ topCells m k ∧ s.image (label k) = Finset.univ :=
    iterated_sperner_exists m k (label k) (hcarrier k)
  let cell (k : ℕ) : Finset (IterVertex m k) := Classical.choose (hcells k)
  have hcell_mem (k : ℕ) : cell k ∈ topCells m k :=
    (Classical.choose_spec (hcells k)).1
  have hcell_labels (k : ℕ) : (cell k).image (label k) = Finset.univ :=
    (Classical.choose_spec (hcells k)).2
  have hvertices (k : ℕ) (i : Fin (m + 1)) :
      ∃ v, v ∈ cell k ∧ label k v = i := by
    apply Finset.mem_image.mp
    rw [hcell_labels k]
    exact Finset.mem_univ i
  let vertex (k : ℕ) (i : Fin (m + 1)) : IterVertex m k :=
    Classical.choose (hvertices k i)
  have hvertex_mem (k : ℕ) (i : Fin (m + 1)) : vertex k i ∈ cell k :=
    (Classical.choose_spec (hvertices k i)).1
  have hvertex_label (k : ℕ) (i : Fin (m + 1)) : label k (vertex k i) = i :=
    (Classical.choose_spec (hvertices k i)).2
  let a : ℕ → Fin (m + 1) → ProbabilitySimplex (Fin (m + 1)) :=
    fun k i => point k (vertex k i)
  have hden : (0 : ℝ) < (m : ℝ) + 1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) zero_lt_one
  have hq₀ : (0 : ℝ) ≤ (m : ℝ) / ((m : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg m) hden.le
  have hq₁ : (m : ℝ) / ((m : ℝ) + 1) < 1 :=
    (div_lt_one hden).mpr (lt_add_of_pos_right (m : ℝ) zero_lt_one)
  apply probabilitySimplex_fixedPoint_of_shrinking_family P hP a
    (fun k => ((m : ℝ) / ((m : ℝ) + 1)) ^ k)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁)
  · intro k i j
    change dist (iterPoint m k (vertex k i)) (iterPoint m k (vertex k j)) ≤
      ((m : ℝ) / ((m : ℝ) + 1)) ^ k
    rw [dist_eq_norm]
    exact iterPoint_mesh m k (cell k) (mem_topCells.mp (hcell_mem k)).1
      (vertex k i) (hvertex_mem k i) (vertex k j) (hvertex_mem k j)
  · intro k i
    change (P (point k (vertex k i))).val i ≤ (point k (vertex k i)).val i
    simpa only [hvertex_label k i] using (hlabel k (vertex k i)).2

/-- Every continuous self-map of a probability simplex indexed by a nonempty finite type has
a fixed point. All geometric and finite-incidence inputs are discharged by the finite theorem. -/
theorem continuous_probabilitySimplex_fixedPoint
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ProbabilitySimplex ι → ProbabilitySimplex ι) (hP : Continuous P) :
    ∃ a, P a = a := by
  classical
  let m := Fintype.card ι - 1
  have hc : Fintype.card ι = m + 1 := by
    dsimp [m]
    exact (Nat.sub_add_cancel (Nat.succ_le_of_lt
      (Fintype.card_pos : 0 < Fintype.card ι))).symm
  let e : ι ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hc
  let h := probabilitySimplexReindex e
  let Q : ProbabilitySimplex (Fin (m + 1)) → ProbabilitySimplex (Fin (m + 1)) :=
    fun b => h (P (h.symm b))
  have hQ : Continuous Q :=
    h.continuous.comp (hP.comp h.symm.continuous)
  obtain ⟨b, hb⟩ := continuous_fin_probabilitySimplex_fixedPoint m Q hQ
  refine ⟨h.symm b, ?_⟩
  simpa only [Q, Homeomorph.symm_apply_apply] using congrArg h.symm hb

end Tingley

end OAI


