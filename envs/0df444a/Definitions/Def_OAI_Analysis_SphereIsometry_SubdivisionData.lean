-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionData
-- name    : OAI_Analysis_SphereIsometry_SubdivisionData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:27:21.917123+00:00
-- url     : https://prove2.me/theorems/140f0b7e-a82e-4540-a160-c97fcf112ab3
-- title:
--   Iterated barycentric subdivisions with carriers
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $I$ be a finite coordinate set.
--
--   1. **Carrier complex.** A finite vertex type, a complex on it, and a carrier for each vertex.
--   2. **Subdivision.** The barycentric subdivision with inherited carriers.
--   3. **Iterates.** Start from the full simplex on $I$, where each vertex $i$ has carrier $\{i\}$, and subdivide $k$ times. For $I=\{0,\dots,m\}$ this gives level-$k$ vertices, faces, top cells, codimension-one faces, face carriers and incidence counts.
--   4. **Carrier bound.** Every face has at most as many vertices as coordinates in its carrier:
--   $$
--   |s|\le|\mathrm{carrier}(s)| .
--   $$
--   In particular top cells have full carrier.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/SubdivisionData.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/SubdivisionData.lean by skeleton subtraction
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

namespace OAI

/-! # The concrete recursively iterated subdivision of a finite simplex -/

noncomputable section

namespace Tingley

structure CarrierComplex (I : Type) [DecidableEq I] where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  complex : FiniteComplex Vertex
  carrier : Vertex → Finset I

attribute [instance] CarrierComplex.vertexFintype CarrierComplex.vertexDecidableEq

namespace CarrierComplex

variable {I : Type} [DecidableEq I]

def sd (D : CarrierComplex I) : CarrierComplex I where
  Vertex := FiniteComplex.FaceVertex D.complex
  complex := D.complex.sd
  carrier := D.complex.sdCarrier D.carrier

def initial (I : Type) [Fintype I] [DecidableEq I] : CarrierComplex I where
  Vertex := I
  complex := FiniteComplex.full
  carrier := fun i => {i}

end CarrierComplex

def iterData (I : Type) [Fintype I] [DecidableEq I] : ℕ → CarrierComplex I
  | 0 => CarrierComplex.initial I
  | n + 1 => (iterData I n).sd

abbrev IterVertex (m k : ℕ) := (iterData (Fin (m + 1)) k).Vertex

def iterComplex (m k : ℕ) : Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.faces

def iterCarrier (m k : ℕ) : IterVertex m k → Finset (Fin (m + 1)) :=
  (iterData (Fin (m + 1)) k).carrier

def topCells (m k : ℕ) : Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.topCells m

def codimFaces (m k : ℕ) : Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.codimFaces m

def faceCarrier (m k : ℕ) (s : Finset (IterVertex m k)) : Finset (Fin (m + 1)) :=
  FiniteComplex.faceCarrier (iterCarrier m k) s

def incidentTop (m k : ℕ) (s : Finset (IterVertex m k)) :
    Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.incidentTop m s

@[simp] theorem mem_topCells {m k : ℕ} {s : Finset (IterVertex m k)} :
    s ∈ topCells m k ↔ s ∈ iterComplex m k ∧ s.card = m + 1 :=
  FiniteComplex.mem_topCells

@[simp] theorem mem_codimFaces {m k : ℕ} {s : Finset (IterVertex m k)} :
    s ∈ codimFaces m k ↔ s ∈ iterComplex m k ∧ s.card = m :=
  FiniteComplex.mem_codimFaces

@[simp] theorem mem_incidentTop {m k : ℕ} {s t : Finset (IterVertex m k)} :
    t ∈ incidentTop m k s ↔
      t ∈ iterComplex m k ∧ t.card = m + 1 ∧ s ⊆ t :=
  FiniteComplex.mem_incidentTop

theorem iterData_card_le_carrier (I : Type) [Fintype I] [DecidableEq I] (k : ℕ) :
    ∀ s ∈ (iterData I k).complex.faces,
      s.card ≤ (FiniteComplex.faceCarrier (iterData I k).carrier s).card := by
  induction k with
  | zero =>
      intro s hs
      simp [iterData, CarrierComplex.initial, FiniteComplex.faceCarrier]
      exact (congrArg (fun t : Finset I => t.card)
        (Finset.biUnion_singleton_eq_self (s := s))).ge
  | succ k ih =>
      intro s hs
      exact FiniteComplex.sd_card_le_carrier ih hs

theorem iter_card_le_carrier {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ iterComplex m k) : s.card ≤ (faceCarrier m k s).card :=
  iterData_card_le_carrier (Fin (m + 1)) k s hs

theorem iter_card_le {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ iterComplex m k) : s.card ≤ m + 1 := by
  have h := (iter_card_le_carrier hs).trans (Finset.card_le_univ (faceCarrier m k s))
  simpa using h

theorem top_faceCarrier {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ topCells m k) : faceCarrier m k s = Finset.univ := by
  obtain ⟨hs, hcard⟩ := mem_topCells.mp hs
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa [hcard] using iter_card_le_carrier hs

end Tingley

end

end OAI


