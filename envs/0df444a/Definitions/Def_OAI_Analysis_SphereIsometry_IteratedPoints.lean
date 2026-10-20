-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_IteratedPoints
-- name    : OAI_Analysis_SphereIsometry_IteratedPoints
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:37:52.499412+00:00
-- url     : https://prove2.me/theorems/93df8b38-5afd-4611-8c66-e08d0ab88f2a
-- title:
--   Geometric realization of iterated subdivisions
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $I$ be a finite coordinate set.
--
--   1. **Vertex points.** At level $0$ the vertex $i$ is the unit vector $e_i$. At level $k+1$ a vertex, which is a nonempty old face $s$, is placed at the barycenter of the old points of $s$.
--   2. **Properties.** Every vertex point lies in the probability simplex, and its strictly positive coordinates are exactly its carrier:
--   $$
--   p(v)_i>0\iff i\in\mathrm{carrier}(v).
--   $$
--   Any two simplex points are within $1$ in the sup norm.
--   3. **Mesh.** In dimension $m$, any two vertices of a face at level $k$ are within $(m/(m+1))^k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/IteratedPoints.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/IteratedPoints.lean by skeleton subtraction
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

namespace OAI

/-!
# Actual geometric points of iterated subdivision

Initial vertices are coordinate unit vectors. Every later vertex is the finite
barycenter of the nonempty old face that it represents. Simplex membership,
exact carriers, and the geometric mesh bound follow from this recursive formula.
-/

noncomputable section

namespace Tingley

/-- The actual geometric realization of every recursively constructed vertex. -/
def iterDataPoint (I : Type) [Fintype I] [DecidableEq I] :
    (k : ℕ) → (iterData I k).Vertex → I → ℝ
  | 0, v => Pi.single v 1
  | k + 1, v => finiteBarycenter (iterDataPoint I k) v.val

@[simp] theorem iterDataPoint_zero (I : Type) [Fintype I] [DecidableEq I] (v : I) :
    iterDataPoint I 0 v = Pi.single v 1 := rfl

@[simp] theorem iterDataPoint_succ (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (v : (iterData I (k + 1)).Vertex) :
    iterDataPoint I (k + 1) v = finiteBarycenter (iterDataPoint I k) v.val := rfl

/-- The recursion produces simplex vectors at every level. -/
theorem iterDataPoint_mem_stdSimplex (I : Type) [Fintype I] [DecidableEq I] :
    ∀ (k : ℕ) (v : (iterData I k).Vertex),
      iterDataPoint I k v ∈ probabilitySimplexSet I := by
  intro k
  induction k with
  | zero =>
      intro v
      exact single_mem_probabilitySimplexSet v
  | succ k ih =>
      intro v
      exact finiteBarycenter_mem_stdSimplex (iterDataPoint I k) v.property.2
        (fun u _ => ih u)

/-- The recursively defined combinatorial carrier is exactly the set of
strict-positive coordinates of the actual recursive point. -/
theorem positiveCarrier_iterDataPoint (I : Type) [Fintype I] [DecidableEq I] :
    ∀ (k : ℕ) (v : (iterData I k).Vertex),
      positiveCarrier (iterDataPoint I k v) = (iterData I k).carrier v := by
  intro k
  induction k with
  | zero =>
      intro v
      change positiveCarrier (Pi.single v (1 : ℝ)) = {v}
      ext i
      by_cases hi : v = i
      · subst i
        simp [positiveCarrier]
      · simp [positiveCarrier, Pi.single_apply, Ne.symm hi]
  | succ k ih =>
      intro v
      change positiveCarrier (finiteBarycenter (iterDataPoint I k) v.val) =
        v.val.biUnion (fun u => (iterData I k).carrier u)
      rw [positiveCarrier_finiteBarycenter (iterDataPoint I k) v.property.2
        (fun u _ i => (iterDataPoint_mem_stdSimplex I k u).1 i)]
      ext i
      simp only [Finset.mem_biUnion, ih]

/-- The coordinate form used by the simplex fixed-point argument. -/
abbrev iterPoint (m k : ℕ) : IterVertex m k → Fin (m + 1) → ℝ :=
  iterDataPoint (Fin (m + 1)) k

@[simp] theorem iterPoint_zero (m : ℕ) (v : Fin (m + 1)) :
    iterPoint m 0 v = Pi.single v 1 := rfl

@[simp] theorem iterPoint_succ (m k : ℕ) (v : IterVertex m (k + 1)) :
    iterPoint m (k + 1) v = finiteBarycenter (iterPoint m k) v.val := rfl

theorem iterPoint_mem_stdSimplex (m k : ℕ) (v : IterVertex m k) :
    iterPoint m k v ∈ probabilitySimplexSet (Fin (m + 1)) :=
  iterDataPoint_mem_stdSimplex (Fin (m + 1)) k v

theorem positiveCarrier_iterPoint (m k : ℕ) (v : IterVertex m k) :
    positiveCarrier (iterPoint m k v) = iterCarrier m k v :=
  positiveCarrier_iterDataPoint (Fin (m + 1)) k v

/-- Exact boundary compatibility of the coordinate labelling rule. -/
theorem iterPoint_pos_iff (m k : ℕ) (v : IterVertex m k) (i : Fin (m + 1)) :
    0 < iterPoint m k v i ↔ i ∈ iterCarrier m k v := by
  rw [← mem_positiveCarrier, positiveCarrier_iterPoint]

/-- Any two probability vectors have distance at most one in the ambient sup norm. -/
theorem norm_sub_le_one_of_mem_stdSimplex {I : Type*} [Fintype I]
    {x y : I → ℝ} (hx : x ∈ probabilitySimplexSet I) (hy : y ∈ probabilitySimplexSet I) :
    ‖x - y‖ ≤ 1 := by
  rw [← dist_eq_norm]
  apply (dist_pi_le_iff zero_le_one).mpr
  intro i
  have hxi := mem_Icc_of_mem_probabilitySimplexSet hx i
  have hyi := mem_Icc_of_mem_probabilitySimplexSet hy i
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]

/-- The mesh of each actual level-k face is bounded by the kth power of the
barycentric contraction factor. No face coverage assertion is assumed. -/
theorem iterPoint_mesh (m : ℕ) :
    ∀ (k : ℕ) (s : Finset (IterVertex m k)), s ∈ iterComplex m k →
      ∀ u ∈ s, ∀ v ∈ s,
        ‖iterPoint m k u - iterPoint m k v‖ ≤
          ((m : ℝ) / (m + 1 : ℝ)) ^ k := by
  intro k
  induction k with
  | zero =>
      intro s _ u _ v _
      simpa only [pow_zero] using norm_sub_le_one_of_mem_stdSimplex
        (iterPoint_mem_stdSimplex m 0 u) (iterPoint_mem_stdSimplex m 0 v)
  | succ k ih =>
      intro s hs u hu v hv
      have hchain : (iterData (Fin (m + 1)) k).complex.chain s :=
        FiniteComplex.mem_sd_iff.mp hs
      have hD : 0 ≤ ((m : ℝ) / (m + 1 : ℝ)) ^ k :=
        pow_nonneg (div_nonneg (Nat.cast_nonneg m)
          (add_nonneg (Nat.cast_nonneg m) zero_le_one)) k
      rcases hchain u hu v hv with huv | hvu
      · have h := norm_finiteBarycenter_sub_le_mesh (p := iterPoint m k) m hD
          u.property.2 huv (iter_card_le (m := m) (k := k) v.property.1)
          (ih v.val v.property.1)
        simpa only [iterPoint_succ, pow_succ'] using h
      · have h := norm_finiteBarycenter_sub_le_mesh (p := iterPoint m k) m hD
          v.property.2 hvu (iter_card_le (m := m) (k := k) u.property.1)
          (ih u.val u.property.1)
        calc
          ‖iterPoint m (k + 1) u - iterPoint m (k + 1) v‖ =
              ‖iterPoint m (k + 1) v - iterPoint m (k + 1) u‖ := norm_sub_rev _ _
          _ ≤ ((m : ℝ) / (m + 1 : ℝ)) ^ (k + 1) := by
            simpa only [iterPoint_succ, pow_succ'] using h

end Tingley

end

end OAI


