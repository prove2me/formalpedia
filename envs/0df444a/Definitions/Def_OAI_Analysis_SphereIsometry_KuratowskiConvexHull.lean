-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiConvexHull
-- name    : OAI_Analysis_SphereIsometry_KuratowskiConvexHull
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:03:36.243088+00:00
-- url     : https://prove2.me/theorems/acd76895-c102-4516-b390-79bc637a9544
-- title:
--   Convex hulls do not increase the measure of noncompactness
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $\chi$ be the Kuratowski measure on a normed space.
--
--   1. **Mixture distances.** Two finite mixtures with points in sets of diameter at most $\delta$, all bounded by $R$, and weights $\eta$-close in $\ell_1$, are within $\delta+R\eta$.
--   2. **Covers of hulls.** If $H$ (bounded by $R$) has a finite cover by sets of diameter $\delta$, then $\mathrm{conv}\,H$ has a finite cover by sets of diameter at most $\delta+R\eta$ for every $\eta>0$, using coefficient bins.
--   3. **Invariance.**
--   $$
--   \chi(\mathrm{conv}\,H)=\chi(\overline{\mathrm{conv}}\,H)=\chi(H)\quad\text{for bounded }H .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/KuratowskiConvexHull.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/KuratowskiConvexHull.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_SphereIsometry_SimplexFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_CompactApproximation
import Definitions.Def_OAI_Analysis_SphereIsometry_CompactConvexFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_CoefficientBins
import Definitions.Def_OAI_Analysis_SphereIsometry_ConvexCoverRegroup

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! # Convex-hull invariance of the Kuratowski measure

Finite coefficient bins give actual finite covers of a convex hull. Cover
pieces are first intersected with the bounded original set; empty pieces are
replaced by a singleton from that set. Thus every coordinate has a valid point,
including coordinates with zero weight, and one norm bound controls all pieces.
-/

namespace Tingley

open scoped BigOperators

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A diameter bound and a coefficient `l1` bound control finite mixtures. -/
theorem dist_weighted_mixtures_le {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (z u : ι → E) (δ R η : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : (∑ i, w i) = 1)
    (hdiam : ∀ i, dist (z i) (u i) ≤ δ)
    (hnorm : ∀ i, ‖u i‖ ≤ R) (hR : 0 ≤ R)
    (hcoeff : (∑ i, |w i - v i|) ≤ η) :
    dist (∑ i, w i • z i) (∑ i, v i • u i) ≤ δ + R * η := by
  have hterm (i : ι) :
      ‖w i • z i - v i • u i‖ ≤ w i * δ + |w i - v i| * R := by
    calc
      ‖w i • z i - v i • u i‖ =
          ‖w i • (z i - u i) + (w i - v i) • u i‖ := by
        rw [smul_sub, sub_smul, sub_add_sub_cancel]
      _ ≤ ‖w i • (z i - u i)‖ + ‖(w i - v i) • u i‖ := norm_add_le _ _
      _ = w i * dist (z i) (u i) + |w i - v i| * ‖u i‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (hw i),
          Real.norm_eq_abs, ← dist_eq_norm]
      _ ≤ w i * δ + |w i - v i| * R :=
        add_le_add (mul_le_mul_of_nonneg_left (hdiam i) (hw i))
          (mul_le_mul_of_nonneg_left (hnorm i) (abs_nonneg _))
  calc
    dist (∑ i, w i • z i) (∑ i, v i • u i) =
        ‖∑ i, (w i • z i - v i • u i)‖ := by
      rw [dist_eq_norm, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖w i • z i - v i • u i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (w i * δ + |w i - v i| * R) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, w i) * δ + (∑ i, |w i - v i|) * R := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    _ = δ + R * (∑ i, |w i - v i|) := by
      rw [hmass, one_mul, mul_comm (∑ i, |w i - v i|) R]
    _ ≤ δ + R * η :=
      add_le_add_right (mul_le_mul_of_nonneg_left hcoeff hR) δ

/-- Construct a finite convex-hull cover with arbitrarily small coefficient
error, using a fixed norm bound on the original set. -/
theorem finiteDiameterCover_convexHull_of_norm_le
    {H : Set E} {δ R η : ℝ}
    (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hη : 0 < η)
    (hnorm : ∀ x ∈ H, ‖x‖ ≤ R) (hc : FiniteDiameterCover H δ) :
    FiniteDiameterCover (convexHull ℝ H) (δ + R * η) := by
  classical
  by_cases hH : H.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hH
    obtain ⟨n, U, hcover, hdiam⟩ := hc
    let A : Fin n → Set E := fun i =>
      if (U i ∩ H).Nonempty then U i ∩ H else {x₀}
    have hne (i : Fin n) : (A i).Nonempty := by
      by_cases hi : (U i ∩ H).Nonempty
      · simpa only [A, ite_eq_left hi] using hi
      · simp only [A, ite_eq_right hi, Set.singleton_nonempty]
    have hsub (i : Fin n) : A i ⊆ H := by
      intro x hx
      by_cases hi : (U i ∩ H).Nonempty
      · have hx' : x ∈ U i ∩ H := by simpa only [A, ite_eq_left hi] using hx
        exact hx'.2
      · have hx' : x = x₀ := by
          simpa only [A, ite_eq_right hi, Set.mem_singleton_iff] using hx
        simpa only [hx'] using hx₀
    have hAdiam (i : Fin n) : DiameterLE (A i) δ := by
      intro x hx y hy
      by_cases hi : (U i ∩ H).Nonempty
      · have hx' : x ∈ U i ∩ H := by simpa only [A, ite_eq_left hi] using hx
        have hy' : y ∈ U i ∩ H := by simpa only [A, ite_eq_left hi] using hy
        exact hdiam i x hx'.1 y hy'.1
      · have hx' : x = x₀ := by
          simpa only [A, ite_eq_right hi, Set.mem_singleton_iff] using hx
        have hy' : y = x₀ := by
          simpa only [A, ite_eq_right hi, Set.mem_singleton_iff] using hy
        simpa only [hx', hy', dist_self] using hδ
    have hAcover : ∀ x ∈ H, ∃ i, x ∈ A i := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
      have hni : (U i ∩ H).Nonempty := ⟨x, hi, hx⟩
      exact ⟨i, by simpa only [A, ite_eq_left hni] using (show x ∈ U i ∩ H from ⟨hi, hx⟩)⟩
    have hAnorm (i : Fin n) {x : E} (hx : x ∈ convexHull ℝ (A i)) : ‖x‖ ≤ R :=
      norm_le_of_mem_convexHull (fun y hy => hnorm y (hsub i hy)) hx
    obtain ⟨K, bins, hbins_cover, hbins_diam⟩ := exists_coefficient_bins n η hη
    let B : (Fin n → Fin (K + 1)) → Set E := fun q =>
      {x | ∃ (w : Fin n → ℝ) (z : Fin n → E),
        w ∈ bins q ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
        (∀ i, z i ∈ convexHull ℝ (A i)) ∧ (∑ i, w i • z i) = x}
    apply FiniteDiameterCover.of_fintype B
    · intro x hx
      obtain ⟨w, z, hw, hsum, hz, hrepr⟩ :=
        convexHull_cover_representation H A hne hAcover hx
      obtain ⟨q, hq⟩ := hbins_cover w ⟨hw, hsum⟩
      exact Set.mem_iUnion.mpr ⟨q, w, z, hq, hw, hsum, hz, hrepr⟩
    · intro q x hx y hy
      obtain ⟨w, z, hwbin, hw, hwsum, hz, hxrepr⟩ := hx
      obtain ⟨v, u, hvbin, hv, hvsum, hu, hyrepr⟩ := hy
      rw [← hxrepr, ← hyrepr]
      exact dist_weighted_mixtures_le w v z u δ R η hw hwsum
        (fun i => (hAdiam i).convexHull (z i) (hz i) (u i) (hu i))
        (fun i => hAnorm i (hu i)) hR (hbins_diam q w hwbin v hvbin)
  · have hHe : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hH
    simpa only [hHe, convexHull_empty] using
      (FiniteDiameterCover.empty (E := E) (δ + R * η))

/-- Convexification preserves the Kuratowski measure of every bounded set. -/
theorem chi_convexHull {H : Set E} (hH : Bornology.IsBounded H) :
    chi (convexHull ℝ H) = chi H := by
  apply le_antisymm
  · obtain ⟨R, hR, hnorm⟩ := hH.exists_pos_norm_le
    apply le_csInf (coverRadii_nonempty hH)
    intro δ hδ
    apply le_of_forall_pos_le_add
    intro ε hε
    have hc := finiteDiameterCover_convexHull_of_norm_le hδ.1.le hR.le
      (div_pos hε hR) hnorm hδ.2
    have hrad : δ + R * (ε / R) = δ + ε := by
      rw [mul_div_cancel₀ ε hR.ne']
    have hb := chi_le_of_cover (add_nonneg hδ.1.le
      (mul_nonneg hR.le (div_pos hε hR).le)) hc
    simpa only [hrad] using hb
  · exact chi_mono (isBounded_convexHull.mpr hH) (subset_convexHull ℝ H)

/-- Taking the closed convex hull also preserves the Kuratowski measure. -/
theorem chi_closedConvexHull {H : Set E} (hH : Bornology.IsBounded H) :
    chi (closure (convexHull ℝ H)) = chi H := by
  rw [chi_closure (isBounded_convexHull.mpr hH), chi_convexHull hH]

end Tingley

end OAI


