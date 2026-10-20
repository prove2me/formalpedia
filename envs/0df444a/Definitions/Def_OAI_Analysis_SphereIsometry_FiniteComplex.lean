-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_FiniteComplex
-- name    : OAI_Analysis_SphereIsometry_FiniteComplex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:24:05.202439+00:00
-- url     : https://prove2.me/theorems/29b6a672-767a-49ef-a6b7-8235d6ff9fa4
-- title:
--   Finite abstract simplicial complexes and barycentric subdivision
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $V$ be a finite vertex set.
--
--   1. **Complex.** A family of faces (finite subsets of $V$) containing $\varnothing$ and closed under subsets; the full complex has all subsets as faces.
--   2. **Subdivision.** The vertices of the subdivision are the nonempty faces. Its faces are the chains $s_1\subsetneq s_2\subsetneq\dots$ of faces.
--   3. **Counting data.** For a dimension $m$: top cells (faces with $m+1$ vertices), codimension-one faces ($m$ vertices), the top cells containing a given face, and the bound that all faces have at most $m+1$ vertices.
--   4. **Carriers.** A carrier assigns to each vertex a set of coordinates. A face's carrier is the union of its vertices' carriers, and a subdivision vertex inherits the carrier of its old face:
--   $$
--   \mathrm{carrier}(s)=\bigcup_{v\in s}\mathrm{carrier}(v).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/FiniteComplex.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/FiniteComplex.lean by skeleton subtraction
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

namespace OAI

/-!
# Finite complexes and their actual face-chain subdivision

The empty face is included. A subdivision vertex is always a nonempty old
face, and a subdivision face is an actual finite inclusion-chain.
-/

noncomputable section

namespace Tingley

universe u v

structure FiniteComplex (V : Type u) [Fintype V] [DecidableEq V] where
  faces : Finset (Finset V)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces

namespace FiniteComplex

variable {V : Type u} [Fintype V] [DecidableEq V]

def full : FiniteComplex V where
  faces := Finset.univ
  empty_mem := Finset.mem_univ _
  down_closed := fun _ _ => Finset.mem_univ _

@[simp] theorem mem_full (s : Finset V) : s ∈ (full : FiniteComplex V).faces :=
  Finset.mem_univ _

abbrev FaceVertex (K : FiniteComplex V) :=
  {s : Finset V // s ∈ K.faces ∧ s.Nonempty}

instance (K : FiniteComplex V) : Fintype (FaceVertex K) := by
  classical
  unfold FaceVertex
  infer_instance

def chain (K : FiniteComplex V) (c : Finset (FaceVertex K)) : Prop :=
  ∀ a ∈ c, ∀ b ∈ c, a.val ⊆ b.val ∨ b.val ⊆ a.val

theorem chain_mono {K : FiniteComplex V} {c d : Finset (FaceVertex K)}
    (hc : K.chain c) (hd : d ⊆ c) : K.chain d :=
  fun a ha b hb => hc a (hd ha) b (hd hb)

def sd (K : FiniteComplex V) : FiniteComplex (FaceVertex K) := by
  classical
  exact
    { faces := Finset.univ.filter K.chain
      empty_mem := by simp [chain]
      down_closed := by
        intro s t hs hts
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, K.chain_mono (Finset.mem_filter.mp hs).2 hts⟩ }

@[simp] theorem mem_sd_iff {K : FiniteComplex V} {c : Finset (FaceVertex K)} :
    c ∈ K.sd.faces ↔ K.chain c := by
  classical
  simp [sd]

def topCells (K : FiniteComplex V) (m : ℕ) : Finset (Finset V) :=
  K.faces.filter (fun s => s.card = m + 1)

def codimFaces (K : FiniteComplex V) (m : ℕ) : Finset (Finset V) :=
  K.faces.filter (fun s => s.card = m)

def incidentTop (K : FiniteComplex V) (m : ℕ) (s : Finset V) : Finset (Finset V) :=
  (K.topCells m).filter (fun t => s ⊆ t)

@[simp] theorem mem_topCells {K : FiniteComplex V} {m : ℕ} {s : Finset V} :
    s ∈ K.topCells m ↔ s ∈ K.faces ∧ s.card = m + 1 :=
  Finset.mem_filter

@[simp] theorem mem_codimFaces {K : FiniteComplex V} {m : ℕ} {s : Finset V} :
    s ∈ K.codimFaces m ↔ s ∈ K.faces ∧ s.card = m :=
  Finset.mem_filter

@[simp] theorem mem_incidentTop {K : FiniteComplex V} {m : ℕ}
    {s t : Finset V} :
    t ∈ K.incidentTop m s ↔ t ∈ K.faces ∧ t.card = m + 1 ∧ s ⊆ t := by
  simp [incidentTop, and_assoc]

def CardBound (K : FiniteComplex V) (m : ℕ) : Prop :=
  ∀ s ∈ K.faces, s.card ≤ m + 1

variable {I : Type v} [DecidableEq I]

def faceCarrier (carrier : V → Finset I) (s : Finset V) : Finset I :=
  s.biUnion carrier

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_faceCarrier {carrier : V → Finset I} {s : Finset V} {i : I} :
    i ∈ faceCarrier carrier s ↔ ∃ v ∈ s, i ∈ carrier v :=
  Finset.mem_biUnion

omit [Fintype V] [DecidableEq V] in
theorem faceCarrier_mono (carrier : V → Finset I) {s t : Finset V} (h : s ⊆ t) :
    faceCarrier carrier s ⊆ faceCarrier carrier t :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

omit [Fintype V] [DecidableEq V] in
@[simp] theorem faceCarrier_empty (carrier : V → Finset I) :
    faceCarrier carrier ∅ = ∅ := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem faceCarrier_singleton (carrier : V → Finset I) (v : V) :
    faceCarrier carrier {v} = carrier v := by
  simp [faceCarrier]

def sdCarrier (K : FiniteComplex V) (carrier : V → Finset I) :
    FaceVertex K → Finset I := fun s => faceCarrier carrier s.val

end FiniteComplex

end Tingley

end

end OAI


