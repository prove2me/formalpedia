-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricFlags
-- name    : OAI_Analysis_SphereIsometry_BarycentricFlags
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:26:29.427277+00:00
-- url     : https://prove2.me/theorems/f865831c-4c3f-4b1e-b5da-8a21cdd5377f
-- title:
--   Ranks of chains in a barycentric subdivision
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $K$ be a finite complex whose faces have at most $m+1$ vertices.
--
--   1. **Chains.** Faces in a chain are determined by their cardinalities, and are nested in the order of their sizes.
--   2. **Ranks.** The set of cardinalities of the faces in a chain $c$. A chain has as many ranks as faces.
--   3. **Missing rank.** A chain with $m$ faces has ranks
--   $$
--   \{1,\dots,m+1\}\setminus\{r\}
--   $$
--   for exactly one missing rank $r$.
--   4. **Greatest face.** Every nonempty chain has a greatest face containing all others, and the carrier of the chain equals the carrier of its greatest face.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/BarycentricFlags.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/BarycentricFlags.lean by skeleton subtraction
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

namespace OAI

/-! # Ranks and carriers of finite face-chains -/

noncomputable section

namespace Tingley.FiniteComplex

universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : FiniteComplex V}

theorem chain_eq_of_card_eq {c : Finset (FaceVertex K)} (hc : K.chain c)
    {a b : FaceVertex K} (ha : a ∈ c) (hb : b ∈ c) (h : a.val.card = b.val.card) :
    a = b := by
  apply Subtype.ext
  rcases hc a ha b hb with hab | hba
  · exact Finset.eq_of_subset_of_card_le hab h.ge
  · exact (Finset.eq_of_subset_of_card_le hba h.le).symm

theorem chain_subset_of_card_le {c : Finset (FaceVertex K)} (hc : K.chain c)
    {a b : FaceVertex K} (ha : a ∈ c) (hb : b ∈ c) (h : a.val.card ≤ b.val.card) :
    a.val ⊆ b.val := by
  rcases hc a ha b hb with hab | hba
  · exact hab
  · intro x hx
    rw [Finset.eq_of_subset_of_card_le hba h]
    exact hx

def ranks (K : FiniteComplex V) (c : Finset (FaceVertex K)) : Finset ℕ :=
  c.image (fun a => a.val.card)

@[simp] theorem mem_ranks {c : Finset (FaceVertex K)} {r : ℕ} :
    r ∈ K.ranks c ↔ ∃ a ∈ c, a.val.card = r :=
  Finset.mem_image

theorem card_ranks {c : Finset (FaceVertex K)} (hc : K.chain c) :
    (K.ranks c).card = c.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact chain_eq_of_card_eq hc ha hb hab

theorem ranks_subset {m : ℕ} (hK : K.CardBound m) (c : Finset (FaceVertex K)) :
    K.ranks c ⊆ Finset.Icc 1 (m + 1) := by
  intro r hr
  obtain ⟨a, _, rfl⟩ := mem_ranks.mp hr
  exact Finset.mem_Icc.mpr
    ⟨Finset.card_pos.mpr a.property.2, hK a.val a.property.1⟩

theorem missing_rank {m : ℕ} (hK : K.CardBound m) {c : Finset (FaceVertex K)}
    (hc : c ∈ K.sd.codimFaces m) :
    ∃ r, 1 ≤ r ∧ r ≤ m + 1 ∧ K.ranks c = (Finset.Icc 1 (m + 1)).erase r := by
  obtain ⟨hchain, hcard⟩ := mem_codimFaces.mp hc
  have hsub := ranks_subset hK c
  have hd : ((Finset.Icc 1 (m + 1)) \ K.ranks c).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, card_ranks (mem_sd_iff.mp hchain), hcard]
    simp
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hd
  have hrmem : r ∈ (Finset.Icc 1 (m + 1)) \ K.ranks c := by
    rw [hr]
    exact Finset.mem_singleton_self _
  obtain ⟨hrI, hrnot⟩ := Finset.mem_sdiff.mp hrmem
  refine ⟨r, (Finset.mem_Icc.mp hrI).1, (Finset.mem_Icc.mp hrI).2, ?_⟩
  ext q
  constructor
  · intro hq
    exact Finset.mem_erase.mpr ⟨fun hqr => hrnot (hqr ▸ hq), hsub hq⟩
  · intro hq
    obtain ⟨hqr, hqI⟩ := Finset.mem_erase.mp hq
    by_contra hnot
    have : q ∈ (Finset.Icc 1 (m + 1)) \ K.ranks c :=
      Finset.mem_sdiff.mpr ⟨hqI, hnot⟩
    rw [hr] at this
    exact hqr (Finset.mem_singleton.mp this)

theorem exists_greatest {c : Finset (FaceVertex K)} (hc : K.chain c)
    (hne : c.Nonempty) : ∃ a ∈ c, ∀ b ∈ c, b.val ⊆ a.val := by
  obtain ⟨a, ha, hmax⟩ := c.exists_max_image (fun b => b.val.card) hne
  exact ⟨a, ha, fun b hb => chain_subset_of_card_le hc hb ha (hmax b hb)⟩

theorem card_le_greatest {c : Finset (FaceVertex K)} (hc : K.chain c)
    {a : FaceVertex K} (_ha : a ∈ c) (hmax : ∀ b ∈ c, b.val ⊆ a.val) :
    c.card ≤ a.val.card := by
  have hsub : K.ranks c ⊆ Finset.Icc 1 a.val.card := by
    intro r hr
    obtain ⟨b, hb, rfl⟩ := mem_ranks.mp hr
    exact Finset.mem_Icc.mpr
      ⟨Finset.card_pos.mpr b.property.2, Finset.card_le_card (hmax b hb)⟩
  have h := Finset.card_le_card hsub
  rw [card_ranks hc] at h
  simpa using h

variable {I : Type v} [DecidableEq I]

theorem faceCarrier_sd_eq_greatest {carrier : V → Finset I}
    {c : Finset (FaceVertex K)} {a : FaceVertex K} (ha : a ∈ c)
    (hmax : ∀ b ∈ c, b.val ⊆ a.val) :
    faceCarrier (K.sdCarrier carrier) c = faceCarrier carrier a.val := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨b, hb, hbi⟩ := mem_faceCarrier.mp hi
    exact faceCarrier_mono carrier (hmax b hb) hbi
  · intro i hi
    exact mem_faceCarrier.mpr ⟨a, ha, hi⟩

theorem sd_card_le_carrier {carrier : V → Finset I}
    (hK : ∀ s ∈ K.faces, s.card ≤ (faceCarrier carrier s).card)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.faces) :
    c.card ≤ (faceCarrier (K.sdCarrier carrier) c).card := by
  rcases c.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨a, ha, hmax⟩ := exists_greatest (mem_sd_iff.mp hc) hne
    rw [faceCarrier_sd_eq_greatest ha hmax]
    exact (card_le_greatest (mem_sd_iff.mp hc) ha hmax).trans (hK a.val a.property.1)

end Tingley.FiniteComplex

end

end OAI


