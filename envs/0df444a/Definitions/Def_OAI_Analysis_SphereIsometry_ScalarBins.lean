-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_ScalarBins
-- name    : OAI_Analysis_SphereIsometry_ScalarBins
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:18:54.112041+00:00
-- url     : https://prove2.me/theorems/f4ea41d1-b529-4ede-bf3b-fcdb4714030e
-- title:
--   Covering an interval by short bins
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps.
--
--   1. **Scalar bins.** For $U\ge0$ and $\eta>0$, there are finitely many sets $B_0,\dots,B_{N-1}$ covering $[0,U]$ with
--   $$
--   |a-b|\le\eta\quad\text{for all }a,b\in B_i ,
--   $$
--   namely half-open intervals of length $\eta$ plus a final bin containing $U$. They are used to sort the radii of the return map before estimating its measure of noncompactness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/ScalarBins.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/ScalarBins.lean by skeleton subtraction
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

namespace OAI

/-!
# Finite scalar bins

A bounded interval is covered by explicitly indexed half-open intervals of
length `η`. The extra final bin includes the top endpoint even when `U / η`
is an integer.
-/

namespace Tingley

/-- Cover `[0,U]` by finitely many scalar bins with pairwise distance at most
`η` inside each bin. The construction also works when `U = 0`. -/
theorem exists_finite_scalar_bins {U η : ℝ} (_hU : 0 ≤ U) (hη : 0 < η) :
    ∃ N : ℕ, ∃ B : Fin N → Set ℝ,
      Set.Icc 0 U ⊆ ⋃ k, B k ∧
      ∀ k, ∀ x ∈ B k, ∀ y ∈ B k, |x - y| ≤ η := by
  let N : ℕ := Nat.floor (U / η) + 1
  let B : Fin N → Set ℝ := fun k =>
    Set.Ico ((k.val : ℝ) * η) (((k.val : ℝ) + 1) * η)
  refine ⟨N, B, ?_, ?_⟩
  · intro x hx
    have hkU : Nat.floor (x / η) ≤ Nat.floor (U / η) :=
      Nat.floor_mono (div_le_div_of_nonneg_right hx.2 hη.le)
    have hkN : Nat.floor (x / η) < N := Nat.lt_succ_of_le hkU
    refine Set.mem_iUnion.mpr ⟨⟨Nat.floor (x / η), hkN⟩, ?_⟩
    change (Nat.floor (x / η) : ℝ) * η ≤ x ∧
      x < ((Nat.floor (x / η) : ℝ) + 1) * η
    exact ⟨(le_div_iff₀ hη).mp (Nat.floor_le (div_nonneg hx.1 hη.le)),
      (div_lt_iff₀ hη).mp (Nat.lt_floor_add_one (x / η))⟩
  · intro k x hx y hy
    change (k.val : ℝ) * η ≤ x ∧ x < ((k.val : ℝ) + 1) * η at hx
    change (k.val : ℝ) * η ≤ y ∧ y < ((k.val : ℝ) + 1) * η at hy
    rw [add_mul, one_mul] at hx hy
    apply abs_le.mpr
    constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2]

end Tingley

end OAI


