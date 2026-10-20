-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricMesh
-- name    : OAI_Analysis_SphereIsometry_BarycentricMesh
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:35:17.39717+00:00
-- url     : https://prove2.me/theorems/5a4093ed-01d1-4f2c-a2f2-8e87f447bc6f
-- title:
--   Barycenters of nested faces are close
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $p:V\to E$ with $\|p(u)-p(v)\|\le D$ on a finite set $T$.
--
--   1. **Nested faces.** For nonempty $S\subseteq T$,
--   $$
--   \|b(S)-b(T)\|\le\Bigl(1-\frac{|S|}{|T|}\Bigr)D ,
--   $$
--   because $b(T)$ is the weighted average of $b(S)$ and $b(T\setminus S)$. Barycenters of two nonempty subsets of $T$ are also within $D$.
--   2. **Uniform contraction.** If faces have at most $m+1$ vertices, consecutive barycenters in a chain are within $\frac m{m+1}D$. So each barycentric subdivision shrinks the mesh by the factor $m/(m+1)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/BarycentricMesh.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/BarycentricMesh.lean by skeleton subtraction
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

namespace OAI

/-!
# The mesh estimate for barycentric subdivision

The larger face is split into the smaller face and its complement. Its
barycenter is the corresponding weighted average, giving the exact factor
`1 - S.card / T.card`. A dimension bound gives the uniform contraction.
-/

noncomputable section

open scoped BigOperators

namespace Tingley

variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq V] in
theorem norm_finiteBarycenter_sub_le_of_subsets {p : V → E}
    {S R T : Finset V} {D : ℝ} (hs : S.Nonempty) (hr : R.Nonempty)
    (hst : S ⊆ T) (hrt : R ⊆ T)
    (hpair : ∀ u ∈ T, ∀ v ∈ T, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p R‖ ≤ D := by
  have hdiam : DiameterLE (p '' (↑T : Set V)) D := by
    rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
    simpa only [dist_eq_norm] using hpair u hu v hv
  have h := hdiam.convexHull
    (finiteBarycenter p S) (finiteBarycenter_mem_convexHull hs hst)
    (finiteBarycenter p R) (finiteBarycenter_mem_convexHull hr hrt)
  simpa only [dist_eq_norm] using h

theorem finiteBarycenter_partition {p : V → E} {S T : Finset V}
    (hs : S.Nonempty) (hst : S ⊆ T) (hr : (T \ S).Nonempty) :
    finiteBarycenter p T =
      ((S.card : ℝ) / (T.card : ℝ)) • finiteBarycenter p S +
      (((T \ S).card : ℝ) / (T.card : ℝ)) • finiteBarycenter p (T \ S) := by
  classical
  have hs0 : (S.card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hs))
  have hr0 : ((T \ S).card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hr))
  have ht0 : (T.card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr (hs.mono hst)))
  have hS : ((S.card : ℝ) / (T.card : ℝ)) • finiteBarycenter p S =
      (T.card : ℝ)⁻¹ • ∑ v ∈ S, p v := by
    rw [finiteBarycenter, smul_smul]
    congr 1
    field_simp [hs0, ht0]
  have hR : (((T \ S).card : ℝ) / (T.card : ℝ)) •
      finiteBarycenter p (T \ S) =
      (T.card : ℝ)⁻¹ • ∑ v ∈ T \ S, p v := by
    rw [finiteBarycenter, smul_smul]
    congr 1
    field_simp [hr0, ht0]
  rw [hS, hR, ← smul_add]
  unfold finiteBarycenter
  congr 1
  simpa only [add_comm] using (Finset.sum_sdiff (f := p) hst).symm

theorem norm_finiteBarycenter_sub_le_card {p : V → E}
    {S T : Finset V} {D : ℝ} (hs : S.Nonempty) (hst : S ⊆ T)
    (hpair : ∀ u ∈ T, ∀ v ∈ T, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p T‖ ≤
      (1 - (S.card : ℝ) / (T.card : ℝ)) * D := by
  classical
  have ht : T.Nonempty := hs.mono hst
  have htpos : 0 < (T.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ht)
  by_cases heq : S = T
  · subst S
    simp [ne_of_gt htpos]
  have hr : (T \ S).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hts
    exact heq (Finset.Subset.antisymm hst hts))
  have hcard : ((T \ S).card : ℝ) + (S.card : ℝ) = (T.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hst
  have hfrac : ((T \ S).card : ℝ) / (T.card : ℝ) =
      1 - (S.card : ℝ) / (T.card : ℝ) := by
    apply (div_eq_iff (ne_of_gt htpos)).2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt htpos)]
    linarith
  have hnonneg : 0 ≤ ((T \ S).card : ℝ) / (T.card : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) htpos.le
  have hid : finiteBarycenter p S - finiteBarycenter p T =
      (((T \ S).card : ℝ) / (T.card : ℝ)) •
        (finiteBarycenter p S - finiteBarycenter p (T \ S)) := by
    calc
      finiteBarycenter p S - finiteBarycenter p T =
          (1 - (S.card : ℝ) / (T.card : ℝ)) • finiteBarycenter p S -
            (((T \ S).card : ℝ) / (T.card : ℝ)) •
              finiteBarycenter p (T \ S) := by
        rw [finiteBarycenter_partition hs hst hr, sub_smul, one_smul]
        abel
      _ = _ := by rw [← hfrac, smul_sub]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    ((T \ S).card : ℝ) / (T.card : ℝ) *
        ‖finiteBarycenter p S - finiteBarycenter p (T \ S)‖ ≤
        ((T \ S).card : ℝ) / (T.card : ℝ) * D :=
      mul_le_mul_of_nonneg_left
        (norm_finiteBarycenter_sub_le_of_subsets hs hr hst Finset.sdiff_subset hpair)
        hnonneg
    _ = _ := by rw [hfrac]

theorem norm_finiteBarycenter_sub_le_mesh {p : V → E}
    {S T : Finset V} {D : ℝ} (m : ℕ) (hD : 0 ≤ D)
    (hs : S.Nonempty) (hst : S ⊆ T) (hcard : T.card ≤ m + 1)
    (hpair : ∀ u ∈ T, ∀ v ∈ T, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p T‖ ≤
      ((m : ℝ) / (m + 1 : ℝ)) * D := by
  have ht : T.Nonempty := hs.mono hst
  have htpos : 0 < (T.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ht)
  have hmpos : 0 < (m + 1 : ℝ) := by positivity
  have hsone : (1 : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Finset.card_pos.mpr hs))
  have htcard : (T.card : ℝ) ≤ (m + 1 : ℝ) := by exact_mod_cast hcard
  have hlow : 1 / (m + 1 : ℝ) ≤ (S.card : ℝ) / (T.card : ℝ) := by
    calc
      1 / (m + 1 : ℝ) ≤ 1 / (T.card : ℝ) :=
        one_div_le_one_div_of_le htpos htcard
      _ ≤ (S.card : ℝ) / (T.card : ℝ) :=
        (div_le_div_iff_of_pos_right htpos).2 hsone
  have hfactor : 1 - (S.card : ℝ) / (T.card : ℝ) ≤
      (m : ℝ) / (m + 1 : ℝ) := by
    have heq : (m : ℝ) / (m + 1 : ℝ) = 1 - 1 / (m + 1 : ℝ) := by
      apply (div_eq_iff (ne_of_gt hmpos)).2
      rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hmpos)]
      ring
    rw [heq]
    linarith
  exact (norm_finiteBarycenter_sub_le_card hs hst hpair).trans
    (mul_le_mul_of_nonneg_right hfactor hD)

end Tingley

end

end OAI


