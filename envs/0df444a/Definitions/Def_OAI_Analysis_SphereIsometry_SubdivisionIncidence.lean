-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionIncidence
-- name    : OAI_Analysis_SphereIsometry_SubdivisionIncidence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:47:14.158395+00:00
-- url     : https://prove2.me/theorems/f66212f3-8db6-479e-85cf-dc7e575bd30b
-- title:
--   Codimension-one incidence in iterated subdivisions
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Consider the $k$-th iterated barycentric subdivision of the $m$-simplex, $m\ge1$.
--
--   1. **Depth zero.** The only top cell is the full vertex set, and the carrier of a face is the face itself.
--   2. **Incidence.** Every codimension-one face $s$ lies in
--   $$
--   \#\{\text{top cells}\supseteq s\}=\begin{cases}1&\text{if the carrier of }s\text{ misses a coordinate},\\ 2&\text{otherwise},\end{cases}
--   $$
--   i.e. one top cell on the boundary of the original simplex and two in the interior. This is proved by induction on $k$ from the missing-rank alternative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/SubdivisionIncidence.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/SubdivisionIncidence.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Incidence counts for the concrete iterated simplex

The missing-rank alternative for an actual flag transports the old boundary
count, or gives two completions around a retained old top face. Iteration
therefore gives one incident top cell on the original boundary and two in
the interior.
-/

noncomputable section

namespace Tingley

/-- At depth zero the unique top cell is the full original vertex set. -/
theorem incidentTop_zero_eq_singleton (m : ℕ) (s : Finset (IterVertex m 0)) :
    incidentTop m 0 s = {Finset.univ} := by
  classical
  change Finset (Fin (m + 1)) at s
  change (FiniteComplex.full : FiniteComplex (Fin (m + 1))).incidentTop m s =
    {Finset.univ}
  ext t
  rw [FiniteComplex.mem_incidentTop, Finset.mem_singleton]
  constructor
  · rintro ⟨_, ht, _⟩
    exact t.eq_univ_of_card (by simpa only [Fintype.card_fin] using ht)
  · rintro rfl
    exact ⟨FiniteComplex.mem_full _, Finset.card_fin _, Finset.subset_univ _⟩

/-- The initial carrier of a face is that face itself. -/
theorem faceCarrier_zero (m : ℕ) (s : Finset (IterVertex m 0)) :
    faceCarrier m 0 s = s := by
  change Finset (Fin (m + 1)) at s
  change s.biUnion (fun i => {i}) = s
  exact Finset.biUnion_singleton_eq_self

/-- Actual codimension-one incidence for every positive-dimensional iterated
standard simplex. The boundary condition refers to the original coordinates. -/
theorem incidentTop_card_eq_if_boundary {m k : ℕ} (hm : 0 < m) :
    ∀ {s : Finset (IterVertex m k)}, s ∈ codimFaces m k →
      (incidentTop m k s).card =
        if (faceCarrier m k s).card = m then 1 else 2 := by
  classical
  induction k with
  | zero =>
      intro s hs
      have hcard := (mem_codimFaces.mp hs).2
      have hface : (faceCarrier m 0 s).card = m :=
        (congrArg (fun t : Finset (Fin (m + 1)) => t.card)
          (faceCarrier_zero m s)).trans hcard
      rw [incidentTop_zero_eq_singleton, Finset.card_singleton, ite_eq_left hface]
  | succ k ih =>
      intro s hs
      let K := (iterData (Fin (m + 1)) k).complex
      have hK : K.CardBound m := by
        intro t ht
        exact iter_card_le ht
      change s ∈ K.sd.codimFaces m at hs
      rcases FiniteComplex.incidentTop_sd_cases hm hK hs with
        ⟨hcount, T, hTs, hTcard, hmax⟩ | ⟨T, hTs, hTcard, hmax, hcount⟩
      · have hcarrier : faceCarrier m (k + 1) s = faceCarrier m k T.val :=
          FiniteComplex.faceCarrier_sd_eq_greatest hTs hmax
        have htop : T.val ∈ topCells m k :=
          mem_topCells.mpr ⟨T.property.1, hTcard⟩
        have hnot : (Finset.univ : Finset (Fin (m + 1))).card ≠ m := by simp
        rw [hcarrier, top_faceCarrier htop, ite_eq_right hnot]
        exact hcount
      · have hcarrier : faceCarrier m (k + 1) s = faceCarrier m k T.val :=
          FiniteComplex.faceCarrier_sd_eq_greatest hTs hmax
        have hcodim : T.val ∈ codimFaces m k :=
          mem_codimFaces.mpr ⟨T.property.1, hTcard⟩
        calc
          (incidentTop m (k + 1) s).card = (incidentTop m k T.val).card := hcount
          _ = if (faceCarrier m k T.val).card = m then 1 else 2 := ih hcodim
          _ = if (faceCarrier m (k + 1) s).card = m then 1 else 2 := by rw [hcarrier]

end Tingley

end

end OAI


