-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiBasic
-- name    : OAI_Analysis_SphereIsometry_KuratowskiBasic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:16:40.586733+00:00
-- url     : https://prove2.me/theorems/cc4c5cc8-cebd-451d-ac9c-598c6a6b5337
-- title:
--   The Kuratowski measure of noncompactness
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $E$ be a metric space and $H\subseteq E$.
--
--   1. **Finite diameter covers.** $H$ is covered by finitely many sets, each of diameter at most $\delta$. Such covers pass to subsets, larger radii and closures.
--   2. **Cover radii.** The positive $\delta$ admitting such a cover. For bounded $H$ this set is nonempty.
--   3. **Kuratowski measure.**
--   $$
--   \chi(H)=\inf\{\delta>0:\ H\text{ has a finite cover by sets of diameter}\le\delta\} .
--   $$
--   It is nonnegative and monotone, it satisfies $\chi(\overline H)=\chi(H)$, and $\chi(H)<\varepsilon$ yields a cover with some radius $\delta<\varepsilon$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/KuratowskiBasic.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/KuratowskiBasic.lean by skeleton subtraction
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

namespace OAI

/-! # The Kuratowski measure from finite diameter covers

The infimum uses positive real radii. The boundedness
hypotheses ensure that its defining set is nonempty. No compactness theorem
or fixed-point principle is part of this definition.
-/

namespace Tingley

variable {E : Type*} [PseudoMetricSpace E]

/-- A finite family of sets of pairwise diameter at most the given radius. -/
def FiniteDiameterCover (H : Set E) (δ : ℝ) : Prop :=
  ∃ n : ℕ, ∃ A : Fin n → Set E,
    (H ⊆ ⋃ i, A i) ∧ ∀ i, DiameterLE (A i) δ

namespace FiniteDiameterCover

variable {H A B : Set E} {δ ε : ℝ}

theorem of_fintype {ι : Type*} [Fintype ι] (U : ι → Set E)
    (hc : H ⊆ ⋃ i, U i) (hd : ∀ i, DiameterLE (U i) δ) :
    FiniteDiameterCover H δ := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => U (e.symm j), ?_, fun j => hd (e.symm j)⟩
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc hx)
  exact Set.mem_iUnion.mpr ⟨e i, by simpa only [Equiv.symm_apply_apply] using hi⟩

theorem empty (δ : ℝ) : FiniteDiameterCover (∅ : Set E) δ := by
  refine ⟨0, fun _ => ∅, Set.empty_subset _, ?_⟩
  intro i
  exact Fin.elim0 i

theorem mono_set (hc : FiniteDiameterCover B δ) (hAB : A ⊆ B) :
    FiniteDiameterCover A δ := by
  obtain ⟨n, U, hcover, hd⟩ := hc
  exact ⟨n, U, hAB.trans hcover, hd⟩

theorem mono_radius (hc : FiniteDiameterCover H δ) (hδε : δ ≤ ε) :
    FiniteDiameterCover H ε := by
  obtain ⟨n, U, hcover, hd⟩ := hc
  exact ⟨n, U, hcover, fun i => (hd i).mono_radius hδε⟩

theorem closure (hc : FiniteDiameterCover H δ) :
    FiniteDiameterCover (closure H) δ := by
  obtain ⟨n, U, hcover, hd⟩ := hc
  refine ⟨n, fun i => _root_.closure (U i), ?_, fun i => (hd i).closure⟩
  intro x hx
  have hx' : x ∈ _root_.closure (⋃ i, U i) := closure_mono hcover hx
  simpa only [closure_iUnion_of_finite] using hx'

end FiniteDiameterCover

/-- Positive radii admitting a finite diameter cover. -/
def coverRadii (H : Set E) : Set ℝ :=
  {δ | 0 < δ ∧ FiniteDiameterCover H δ}

/-- The Kuratowski measure of noncompactness, on bounded sets. -/
noncomputable def chi (H : Set E) : ℝ := sInf (coverRadii H)

theorem coverRadii_bddBelow (H : Set E) : BddBelow (coverRadii H) :=
  ⟨0, fun _ hδ => hδ.1.le⟩

theorem coverRadii_nonempty {H : Set E} (hH : Bornology.IsBounded H) :
    (coverRadii H).Nonempty := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hH
  have hc : FiniteDiameterCover H (max R 1) := by
    refine ⟨1, fun _ => H, ?_, ?_⟩
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
    · intro i x hx y hy
      exact (hR hx hy).trans (le_max_left R 1)
  exact ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right R 1), hc⟩

theorem chi_nonneg {H : Set E} (hH : Bornology.IsBounded H) : 0 ≤ chi H :=
  le_csInf (coverRadii_nonempty hH) (fun _ hδ => hδ.1.le)

theorem chi_le_of_cover {H : Set E} {δ : ℝ}
    (hδ : 0 ≤ δ) (hc : FiniteDiameterCover H δ) : chi H ≤ δ := by
  by_contra hnot
  have hlt : δ < chi H := lt_of_not_ge hnot
  let ε : ℝ := (chi H - δ) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hmem : δ + ε ∈ coverRadii H :=
    ⟨by linarith, hc.mono_radius (by linarith)⟩
  have hupper : chi H ≤ δ + ε := csInf_le (coverRadii_bddBelow H) hmem
  dsimp only [ε] at hupper
  linarith

@[simp] theorem chi_empty : chi (∅ : Set E) = 0 := by
  apply le_antisymm
  · exact chi_le_of_cover le_rfl (FiniteDiameterCover.empty 0)
  · exact chi_nonneg Bornology.isBounded_empty

theorem chi_mono {A B : Set E} (hB : Bornology.IsBounded B) (hAB : A ⊆ B) :
    chi A ≤ chi B := by
  apply csInf_le_csInf (coverRadii_bddBelow A) (coverRadii_nonempty hB)
  intro δ hδ
  exact ⟨hδ.1, hδ.2.mono_set hAB⟩

theorem exists_cover_of_chi_lt {H : Set E} {ε : ℝ}
    (hH : Bornology.IsBounded H) (hε : chi H < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ FiniteDiameterCover H δ := by
  obtain ⟨δ, hδ, hδε⟩ :=
    (csInf_lt_iff (coverRadii_bddBelow H) (coverRadii_nonempty hH)).mp hε
  exact ⟨δ, hδ.1, hδε, hδ.2⟩

theorem chi_closure {H : Set E} (hH : Bornology.IsBounded H) :
    chi (closure H) = chi H := by
  apply le_antisymm
  · apply le_csInf (coverRadii_nonempty hH)
    intro δ hδ
    exact chi_le_of_cover hδ.1.le hδ.2.closure
  · exact chi_mono hH.closure subset_closure

end Tingley

end OAI


