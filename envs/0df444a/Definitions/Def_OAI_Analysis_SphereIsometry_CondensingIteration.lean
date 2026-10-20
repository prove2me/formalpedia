-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_CondensingIteration
-- name    : OAI_Analysis_SphereIsometry_CondensingIteration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:05:07.669904+00:00
-- url     : https://prove2.me/theorems/96542ac7-aa80-495f-9b55-adb5d0147210
-- title:
--   Iterated closed convex images
-- statement:
--   These notions belong to a self-contained fixed-point toolkit used in the proof of Tingley's theorem: Sperner's lemma on iterated barycentric subdivisions, Brouwer's fixed point theorem for the probability simplex, Schauder's theorem for compact convex sets, the Kuratowski measure of noncompactness, and a Darbo–Sadovskii fixed point theorem for condensing maps. Let $C$ be a nonempty closed bounded convex set and $g$ a map with $g(C)\subseteq C$.
--
--   1. **Step.** $\Phi(H)=\overline{\mathrm{conv}}\,g(H)$, a monotone operation.
--   2. **Sequence.** $C_0=C$ and $C_{n+1}=\Phi(C_n)$. The sets decrease, are nonempty, closed, convex, bounded and invariant, and $g(C_n)\subseteq C_{n+1}$.
--   3. **Measure decay.** Taking hulls preserves $\chi$. So if $\chi(g(H))\le\gamma\chi(H)$ for $H\subseteq C$ with $0\le\gamma<1$, then
--   $$
--   \chi(C_n)\le\gamma^n\chi(C)\to0 .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/CondensingIteration.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/CondensingIteration.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiConvexHull

namespace OAI

/-!
# The closed-convex image iteration

Starting from a closed convex invariant set `C`, the actual successor set is
the closure of the convex hull of its image under `g`. All boundedness claims
come from containment in `C`. No boundedness-preservation property of an
arbitrary continuous map is used.
-/

noncomputable section

namespace Tingley

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The literal closed-convex image operator used in the condensing argument. -/
def condensingStep (g : E → E) (H : Set E) : Set E :=
  closure (convexHull ℝ (g '' H))

/-- The iteration begins at `C` and takes actual closed-convex images. -/
def condensingSequence (C : Set E) (g : E → E) : ℕ → Set E
  | 0 => C
  | n + 1 => condensingStep g (condensingSequence C g n)

@[simp] theorem condensingSequence_zero (C : Set E) (g : E → E) :
    condensingSequence C g 0 = C := rfl

@[simp] theorem condensingSequence_succ (C : Set E) (g : E → E) (n : ℕ) :
    condensingSequence C g (n + 1) = condensingStep g (condensingSequence C g n) := rfl

theorem condensingStep_mono (g : E → E) : Monotone (condensingStep g) := by
  intro H J hHJ
  exact closure_mono (convexHull_mono (image_mono hHJ))

theorem image_subset_condensingStep (g : E → E) (H : Set E) :
    g '' H ⊆ condensingStep g H :=
  (subset_convexHull ℝ (g '' H)).trans subset_closure

theorem condensingStep_subset {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) :
    condensingStep g C ⊆ C := by
  apply closure_minimal _ hclosed
  apply convexHull_min _ hconv
  rintro y ⟨x, hx, rfl⟩
  exact hmap hx

theorem condensingSequence_succ_subset {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) (n : ℕ) :
    condensingSequence C g (n + 1) ⊆ condensingSequence C g n := by
  induction n with
  | zero => exact condensingStep_subset hclosed hconv hmap
  | succ n ih => exact condensingStep_mono g ih

theorem condensingSequence_antitone {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) :
    Antitone (condensingSequence C g) :=
  antitone_nat_of_succ_le (condensingSequence_succ_subset hclosed hconv hmap)

theorem condensingSequence_subset {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) (n : ℕ) :
    condensingSequence C g n ⊆ C :=
  condensingSequence_antitone hclosed hconv hmap (Nat.zero_le n)

/-- Every image point belongs to the next set, before using antitonicity. -/
theorem condensingSequence_image_subset_succ (C : Set E) (g : E → E) (n : ℕ) :
    g '' condensingSequence C g n ⊆ condensingSequence C g (n + 1) :=
  image_subset_condensingStep g (condensingSequence C g n)

theorem condensingSequence_nonempty {C : Set E} (g : E → E)
    (hne : C.Nonempty) (n : ℕ) : (condensingSequence C g n).Nonempty := by
  induction n with
  | zero => exact hne
  | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      exact ⟨g x, condensingSequence_image_subset_succ C g n (mem_image_of_mem g hx)⟩

theorem condensingSequence_isClosed {C : Set E} (g : E → E)
    (hclosed : IsClosed C) (n : ℕ) : IsClosed (condensingSequence C g n) := by
  cases n with
  | zero => exact hclosed
  | succ n => exact isClosed_closure

theorem condensingSequence_convex {C : Set E} (g : E → E)
    (hconv : Convex ℝ C) (n : ℕ) : Convex ℝ (condensingSequence C g n) := by
  cases n with
  | zero => exact hconv
  | succ n => exact (convex_convexHull ℝ (g '' condensingSequence C g n)).closure

theorem condensingSequence_isBounded {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) (n : ℕ) :
    Bornology.IsBounded (condensingSequence C g n) :=
  hbounded.subset (condensingSequence_subset hclosed hconv hmap n)

theorem condensingSequence_mapsTo {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) (n : ℕ) :
    MapsTo g (condensingSequence C g n) (condensingSequence C g n) := by
  intro x hx
  exact condensingSequence_succ_subset hclosed hconv hmap n
    (condensingSequence_image_subset_succ C g n (mem_image_of_mem g hx))

theorem condensingSequence_image_subset {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C) (n : ℕ) :
    g '' condensingSequence C g n ⊆ C := by
  rintro y ⟨x, hx, rfl⟩
  exact hmap (condensingSequence_subset hclosed hconv hmap n hx)

theorem condensingSequence_image_isBounded {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) (n : ℕ) :
    Bornology.IsBounded (g '' condensingSequence C g n) :=
  hbounded.subset (condensingSequence_image_subset hclosed hconv hmap n)

/-- The hull step leaves the actual Kuratowski measure of its bounded image unchanged. -/
theorem condensingSequence_chi_succ_eq {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) (n : ℕ) :
    chi (condensingSequence C g (n + 1)) = chi (g '' condensingSequence C g n) := by
  exact chi_closedConvexHull
    (condensingSequence_image_isBounded hclosed hconv hmap hbounded n)

theorem condensingSequence_chi_succ_le {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) {γ : ℝ}
    (hχ : ∀ H : Set E, H ⊆ C → chi (g '' H) ≤ γ * chi H) (n : ℕ) :
    chi (condensingSequence C g (n + 1)) ≤ γ * chi (condensingSequence C g n) := by
  rw [condensingSequence_chi_succ_eq hclosed hconv hmap hbounded n]
  exact hχ _ (condensingSequence_subset hclosed hconv hmap n)

/-- Geometric decay allows `γ = 0`; no division by the contraction factor occurs. -/
theorem condensingSequence_chi_le {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hχ : ∀ H : Set E, H ⊆ C → chi (g '' H) ≤ γ * chi H) (n : ℕ) :
    chi (condensingSequence C g n) ≤ γ ^ n * chi C := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        chi (condensingSequence C g (n + 1)) ≤ γ * chi (condensingSequence C g n) :=
          condensingSequence_chi_succ_le hclosed hconv hmap hbounded hχ n
        _ ≤ γ * (γ ^ n * chi C) := mul_le_mul_of_nonneg_left ih hγ0
        _ = γ ^ (n + 1) * chi C := by rw [pow_succ', mul_assoc]

theorem condensingSequence_chi_nonneg {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) (n : ℕ) :
    0 ≤ chi (condensingSequence C g n) :=
  chi_nonneg (condensingSequence_isBounded hclosed hconv hmap hbounded n)

/-- The actual sequence has Kuratowski measure tending to zero for `0 ≤ γ < 1`. -/
theorem condensingSequence_chi_tendsto_zero {C : Set E} {g : E → E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hmap : MapsTo g C C)
    (hbounded : Bornology.IsBounded C) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hχ : ∀ H : Set E, H ⊆ C → chi (g '' H) ≤ γ * chi H) :
    Tendsto (fun n => chi (condensingSequence C g n)) atTop (𝓝 0) := by
  apply squeeze_zero
    (condensingSequence_chi_nonneg hclosed hconv hmap hbounded)
    (condensingSequence_chi_le hclosed hconv hmap hbounded hγ0 hχ)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (chi C)

end Tingley

end

end OAI


