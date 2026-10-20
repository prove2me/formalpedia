-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricZero
-- name    : OAI_Analysis_SphereIsometry_BarycentricZero
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:49:15.642924+00:00
-- url     : https://prove2.me/theorems/26d862bf-7751-4676-a81b-5aa5e534c4b4
-- title:
--   Subdividing a point
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps.
--
--   1. **Zero-dimensional complexes.** If all faces have at most one vertex, the subdivision has exactly one vertex for each old singleton face.
--   2. **Iterated point.** The iterated subdivision of the $0$-simplex has exactly one top cell at every level:
--   $$
--   \#\{\text{top cells at level }k\}=1 .
--   $$
--   It is incident to the unique empty codimension-one face. This is the base case of the inductive Sperner count.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/BarycentricZero.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/BarycentricZero.lean by skeleton subtraction
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

namespace OAI

/-!
# The zero-dimensional subdivision and its empty codimension-one face

The subdivision of a zero-dimensional complex has one vertex for each old
singleton face. In particular, iterated subdivision of the point has one
top face, incident to its unique empty codimension-one face.
-/

noncomputable section

namespace Tingley.FiniteComplex

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : FiniteComplex V}

@[simp] theorem incidentTop_empty (K : FiniteComplex V) (m : ℕ) :
    K.incidentTop m ∅ = K.topCells m := by
  classical
  ext s
  simp [incidentTop]

theorem sd_topCells_zero_card (hK : K.CardBound 0) :
    (K.sd.topCells 0).card = (K.topCells 0).card := by
  classical
  let v : ∀ s ∈ K.topCells 0, FaceVertex K := fun s hs =>
    ⟨s, (mem_topCells.mp hs).1,
      Finset.card_pos.mp (by have h := (mem_topCells.mp hs).2; omega)⟩
  let f : ∀ s ∈ K.topCells 0, Finset (FaceVertex K) := fun s hs => {v s hs}
  have hf : ∀ s hs, f s hs ∈ K.sd.topCells 0 := by
    intro s hs
    apply mem_topCells.mpr
    constructor
    · apply mem_sd_iff.mpr
      change K.chain {v s hs}
      simp [chain]
    · change ({v s hs} : Finset (FaceVertex K)).card = 0 + 1
      simp
  have hinj : ∀ s hs t ht, f s hs = f t ht → s = t := by
    intro s hs t ht h
    have hv : v s hs = v t ht := Finset.singleton_inj.mp h
    exact congrArg Subtype.val hv
  have hsurj : ∀ c ∈ K.sd.topCells 0, ∃ s hs, f s hs = c := by
    intro c hc
    obtain ⟨hcface, hccard⟩ := mem_topCells.mp hc
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (show c.card = 1 by omega)
    have hacard : a.val.card = 0 + 1 := by
      have hlo := Finset.card_pos.mpr a.property.2
      have hhi := hK a.val a.property.1
      omega
    have ha : a.val ∈ K.topCells 0 := mem_topCells.mpr ⟨a.property.1, hacard⟩
    refine ⟨a.val, ha, ?_⟩
    change ({v a.val ha} : Finset (FaceVertex K)) = {a}
    congr 1
  exact (Finset.card_bij f hf hinj hsurj).symm

end Tingley.FiniteComplex

namespace Tingley

theorem iter_topCells_zero_card (k : ℕ) : (topCells 0 k).card = 1 := by
  classical
  induction k with
  | zero =>
      change ((FiniteComplex.full : FiniteComplex (Fin 1)).topCells 0).card = 1
      have hfull : (FiniteComplex.full : FiniteComplex (Fin 1)).topCells 0 =
          {Finset.univ} := by
        ext s
        simp only [FiniteComplex.mem_topCells, FiniteComplex.mem_full,
          true_and, Finset.mem_singleton]
        constructor
        · intro hs
          apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
          simpa using hs.ge
        · rintro rfl
          simp
      rw [hfull]
      simp
  | succ k ih =>
      change (((iterData (Fin 1) k).complex).sd.topCells 0).card = 1
      have hK : (iterData (Fin 1) k).complex.CardBound 0 := by
        intro s hs
        exact iter_card_le (m := 0) (k := k) hs
      rw [FiniteComplex.sd_topCells_zero_card hK]
      exact ih

end Tingley

end

end OAI


