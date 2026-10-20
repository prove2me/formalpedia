-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapNoncompactness
-- name    : OAI_Analysis_SphereIsometry_ReturnMapNoncompactness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:19:37.884406+00:00
-- url     : https://prove2.me/theorems/ef05bbb9-ba00-4ea2-95d6-6c7e2dd10d6c
-- title:
--   The return map is condensing for the Kuratowski measure
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Let $\chi$ be the Kuratowski measure of noncompactness.
--
--   1. **Refinement by scalar bins.** If $H$ has a finite cover by sets of diameter at most $\delta$, and two bounded scalar observables $p,u$ are sorted into bins of width $\eta$, the intersections give a finite cover of the image $g(H)$. Each piece has diameter controlled by the two-point estimate.
--   2. **Contraction of $\chi$.** On a set $C$ where the return map $g$ satisfies the two-point estimate with radii in $[1-t,1+t]$, $s=p+M$ and $r=u+M$, every subset $H\subseteq C$ satisfies
--   $$
--   \chi(g(H))\le\Bigl(1-\frac M{1+t}\Bigr)^2\chi(H) .
--   $$
--   Since the factor is below $1$ for $M>0$, $g$ is condensing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/ReturnMapNoncompactness.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/ReturnMapNoncompactness.lean by skeleton subtraction
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

namespace OAI

/-!
# The return map contracts noncompactness on every subset

Finite scalar bins refine diameter covers after each piece is intersected
with the given subset. A positive-error argument then passes to the exact
Kuratowski infimum. Neither the subset nor its covering pieces need be compact.
-/

noncomputable section

namespace Tingley

/-- A finite refinement by two bounded scalar observables. -/
theorem finiteDiameterCover_image_of_scalar_bins
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C H : Set X} {g : X → Y} {p u : X → ℝ} {U a γ δ η : ℝ}
    (hHC : H ⊆ C) (hU : 0 ≤ U) (ha : 0 < a) (hγ : 0 ≤ γ)
    (hp : ∀ v ∈ C, p v ∈ Set.Icc 0 U)
    (hu : ∀ v ∈ C, u v ∈ Set.Icc 0 U)
    (hpair : ∀ v ∈ C, ∀ v' ∈ C,
      dist (g v) (g v') ≤ γ * dist v v' +
        (2 / a) * (|u v - u v'| + |p v - p v'|))
    (hc : FiniteDiameterCover H δ) (hη : 0 < η) :
    FiniteDiameterCover (g '' H) (γ * δ + 4 * η / a) := by
  obtain ⟨n, A, hcover, hdiam⟩ := hc
  obtain ⟨N, B, hBcover, hBdiam⟩ := exists_finite_scalar_bins hU hη
  let Q : (Fin n × Fin N × Fin N) → Set X := fun ijk =>
    H ∩ A ijk.1 ∩ p ⁻¹' B ijk.2.1 ∩ u ⁻¹' B ijk.2.2
  apply FiniteDiameterCover.of_fintype (fun ijk => g '' Q ijk)
  · rintro y ⟨v, hvH, rfl⟩
    obtain ⟨i, hvi⟩ := Set.mem_iUnion.mp (hcover hvH)
    obtain ⟨j, hvj⟩ := Set.mem_iUnion.mp (hBcover (hp v (hHC hvH)))
    obtain ⟨k, hvk⟩ := Set.mem_iUnion.mp (hBcover (hu v (hHC hvH)))
    exact Set.mem_iUnion.mpr
      ⟨(i, j, k), v, ⟨⟨⟨hvH, hvi⟩, hvj⟩, hvk⟩, rfl⟩
  · rintro ijk y ⟨v, hv, rfl⟩ z ⟨v', hv', rfl⟩
    change v ∈ H ∩ A ijk.1 ∩ p ⁻¹' B ijk.2.1 ∩ u ⁻¹' B ijk.2.2 at hv
    change v' ∈ H ∩ A ijk.1 ∩ p ⁻¹' B ijk.2.1 ∩ u ⁻¹' B ijk.2.2 at hv'
    rcases hv with ⟨⟨⟨hvH, hvA⟩, hvp⟩, hvu⟩
    rcases hv' with ⟨⟨⟨hvH', hvA'⟩, hvp'⟩, hvu'⟩
    have hpd : |p v - p v'| ≤ η := hBdiam ijk.2.1 _ hvp _ hvp'
    have hud : |u v - u v'| ≤ η := hBdiam ijk.2.2 _ hvu _ hvu'
    have herr : (2 / a) * (|u v - u v'| + |p v - p v'|) ≤ 4 * η / a := by
      calc
        (2 / a) * (|u v - u v'| + |p v - p v'|) ≤ (2 / a) * (η + η) :=
          mul_le_mul_of_nonneg_left (add_le_add hud hpd) (div_nonneg zero_le_two ha.le)
        _ = 4 * η / a := by ring
    exact (hpair v (hHC hvH) v' (hHC hvH')).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hdiam ijk.1 v hvA v' hvA') hγ) herr)

/-- The exact all-subsets contraction, including the empty subset. The scalar
relations and the two-point estimate are supplied by the actual return map. -/
theorem chi_return_image_le
    {X : Type*} [PseudoMetricSpace X]
    {C : Set X} {g : X → X} {p s u r : X → ℝ} {t M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 < M)
    (hCne : C.Nonempty) (hCb : Bornology.IsBounded C)
    (_hgC : Set.MapsTo g C C)
    (hbounds : ∀ v ∈ C,
      (1 - t ≤ p v ∧ p v ≤ 1 + t) ∧
      (1 - t ≤ s v ∧ s v ≤ 1 + t) ∧
      (1 - t ≤ u v ∧ u v ≤ 1 + t) ∧
      (1 - t ≤ r v ∧ r v ≤ 1 + t))
    (hs : ∀ v ∈ C, s v = p v + M)
    (hr : ∀ v ∈ C, r v = u v + M)
    (hpair : ∀ v ∈ C, ∀ v' ∈ C,
      dist (g v) (g v') ≤
        (u v * p v / (r v * s v)) * dist v v' +
        2 * |u v - u v'| / r v +
        2 * u v * |p v - p v'| / (r v * s v))
    {H : Set X} (hHC : H ⊆ C) :
    chi (g '' H) ≤ (1 - M / (1 + t)) ^ 2 * chi H := by
  let γ : ℝ := (1 - M / (1 + t)) ^ 2
  have ha : 0 < 1 - t := sub_pos.mpr ht1
  have hU : 0 ≤ 1 + t := by linarith
  have hfactor := return_contraction_factor_mem_Ico ht0 ht1 hM hCne
    (fun v hv => (hbounds v hv).1.1)
    (fun v hv => (hbounds v hv).2.1.2) hs
  have hγ : 0 ≤ γ := hfactor.1
  have hγ1 : γ ≤ 1 := hfactor.2.le
  have hp : ∀ v ∈ C, p v ∈ Set.Icc 0 (1 + t) := by
    intro v hv
    exact ⟨ha.le.trans (hbounds v hv).1.1, (hbounds v hv).1.2⟩
  have hu : ∀ v ∈ C, u v ∈ Set.Icc 0 (1 + t) := by
    intro v hv
    exact ⟨ha.le.trans (hbounds v hv).2.2.1.1, (hbounds v hv).2.2.1.2⟩
  have hpair' : ∀ v ∈ C, ∀ v' ∈ C,
      dist (g v) (g v') ≤ γ * dist v v' +
        (2 / (1 - t)) * (|u v - u v'| + |p v - p v'|) := by
    intro v hv v' hv'
    exact return_pair_uniform_bound ha hM.le (hp v hv).1 (hu v hv).1
      (hbounds v hv).2.2.2.1 (hbounds v hv).2.1.1
      (hbounds v hv).2.2.2.2 (hbounds v hv).2.1.2
      (hr v hv) (hs v hv) dist_nonneg (abs_nonneg _) (abs_nonneg _)
      (hpair v hv v' hv')
  have happrox : ∀ ε : ℝ, 0 < ε → chi (g '' H) ≤ γ * chi H + ε := by
    intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨δ, hδ0, hδ, hc⟩ := exists_cover_of_chi_lt (hCb.subset hHC)
      (show chi H < chi H + ε / 2 by linarith)
    let η : ℝ := ε * (1 - t) / 8
    have hη : 0 < η := div_pos (mul_pos hε ha) (by norm_num)
    have hc' := finiteDiameterCover_image_of_scalar_bins hHC hU ha hγ hp hu hpair' hc hη
    have hR : 0 ≤ γ * δ + 4 * η / (1 - t) :=
      add_nonneg (mul_nonneg hγ hδ0.le)
        (div_nonneg (mul_nonneg (by norm_num) hη.le) ha.le)
    have herror : 4 * η / (1 - t) = ε / 2 := by
      dsimp only [η]
      field_simp [ne_of_gt ha]
      ring
    calc
      chi (g '' H) ≤ γ * δ + 4 * η / (1 - t) := chi_le_of_cover hR hc'
      _ = γ * δ + ε / 2 := by rw [herror]
      _ ≤ γ * (chi H + ε / 2) + ε / 2 :=
        add_le_add_left (mul_le_mul_of_nonneg_left hδ.le hγ) _
      _ ≤ γ * chi H + ε := by
        have hh := mul_le_mul_of_nonneg_right hγ1 hε2.le
        nlinarith
  change chi (g '' H) ≤ γ * chi H
  by_contra hnot
  have hgap : 0 < chi (g '' H) - γ * chi H := sub_pos.mpr (lt_of_not_ge hnot)
  have hh := happrox ((chi (g '' H) - γ * chi H) / 2) (half_pos hgap)
  linarith

end Tingley

end

end OAI


