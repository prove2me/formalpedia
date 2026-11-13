-- Prove2me | Definitions.Def_OAIQ249SI000
-- name    : OAIQ249SI000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T09:43:04.45876+00:00
-- url     : https://prove2.me/theorems/83f7204e-d200-4aa2-9e29-edc749d79d0e
-- title:
--   Definitions bundle OAIQ249SI000 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 451 declarations of OpenAI's Lean: 97 definitions, 15 inductive types or structures, 28 instances, 306 theorems and 5 other declarations. The definitions and types are `ContinuousGerm`, `ContinuousLinearEquiv.lowerTriangular`, `ContinuousLinearMap.compRightL`, `ContinuousLinearMap.coprodL`, `DualPair`, `DualPair.map`, `DualPair.spanV`, `DualPair.update`, `Equiv.toHomeomorphOfContDiff`, `EquivariantEquiv`, `EquivariantEquiv.equivariantMap`, `EquivariantEquiv.symm`, `EquivariantMap`, `FamilyJetSec`, `Filter.Germ.ContMDiffAt`, `Filter.Germ.ContMDiffAt'`, `Filter.Germ.ContMDiffAtProd`, `Filter.Germ.valueₛₗ`, `HtpyJetSec`, `HtpyJetSec.comp`, `IndexType`, `IndexType.fromNat`, `IndexType.succ`, `IsPathConnected.pathThrough`, `IsPathConnected.somePath`, `JetSec`, `JetSec.IsFormalSol`, `JetSec.IsFormalSol.formalSol`, `JetSec.IsHolonomicAt`, `JetSec.IsPartHolonomicAt`, `JetSec.IsShortAt`, `JetSec.constHtpy`, `JetSec.sliceAt`, `Landscape`, `Loop`, `Loop.IsConst`, `Loop.Surrounds`, `Loop.average`, `Loop.const`, `Loop.diff` and 72 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_AtlasWeights`, `Immersion_ClosedSurface_CompactPartition`, `Immersion_ClosedSurface_GlobalPartition`, `Immersion_ClosedSurface_GoodAtlas`, `Immersion_ClosedSurface_GridBumps`, `Immersion_ClosedSurface_GridPartition`, `Immersion_ClosedSurface_PhaseGrid`, `Indexing`, `InductiveConstructions`, `Local_AmpleRelation`, `Local_DualPair`, `Local_HPrinciple`, `Local_OneJet`, `Local_Relation`, `Loops_Basic`, `Loops_DeltaMollifier`, `Loops_Exists`, `Loops_Reparametrization`, `Loops_Surrounding`, `Notations`, `SurfaceImmersion_Atlas_GridCutoffSupport`, `SurfaceImmersion_Atlas_GridPhaseCutoffs`, `SurfaceImmersion_Atlas_GridSupportedCutoffs`, `SurfaceImmersion_Correction_SmoothPrimitiveFamily`, `ToMathlib_Algebra_Ring_Periodic`, `ToMathlib_Analysis_Calculus`, `ToMathlib_Analysis_ContDiff`, `ToMathlib_Analysis_Convex_Basic`, `ToMathlib_Analysis_NormedSpace_OperatorNorm_Prod`, `ToMathlib_Data_Nat_Basic`, `ToMathlib_Equivariant`, `ToMathlib_ExistsOfConvex`, `ToMathlib_Geometry_Manifold_Algebra_SmoothGerm`, `ToMathlib_MeasureTheory_ParametricIntervalIntegral`, `ToMathlib_Partition`, `ToMathlib_SmoothBarycentric`, `ToMathlib_Topology_Misc`, `ToMathlib_Topology_Path`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`; the bundle `OAIQ249SI003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI010` and `OAIQ249SI011`; the statements `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_cancel_crosscap_pair`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_remove_finite_quadratic_crosscaps` and `OAI.ClosedSurfaceR4.PhaseGeometry.anchored_polynomial_grid_phases`; the proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crosscap_source_embedded_path`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_smooth_crosscap_arc` and `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_smooth_finite_regular_path`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Ring.Subring.Order
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.AddTorsor.Coord
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.AmpleSet
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.AffineSpace.Matrix
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.Filter.Ring
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Choose
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Germ
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ShrinkingLemma
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI003

section
-- module Solutions.OAIQ249_SI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set
abbrev Index := ℤ × ℤ

def cell (h R : ℝ) (a : Index) : Set Base :=
  {x | |x.1 - h * a.1| < R * h ∧ |x.2 - h * a.2| < R * h}

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridBumps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set

def center (a : Index) : Base := ((a.1 : ℝ),(a.2 : ℝ))
def cutoff (h : ℝ) (a : Index) (x : Base) : ℝ :=
  gridBump (h⁻¹ • x - center a)

lemma cutoff_smooth (h : ℝ) (a : Index) : ContDiff ℝ ∞ (cutoff h a) := by
  have hs : ContDiff ℝ ∞ (fun x : Base => h⁻¹ • x) := contDiff_const_smul _
  exact gridBump.contDiff.comp (hs.sub contDiff_const)

lemma cutoff_one_on_cell {h : ℝ} (hh : 0 < h) (a : Index) {x : Base}
    (hx : x ∈ cell h 1 a) : cutoff h a x = 1 := by
  apply gridBump.one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, gridBump]
  change ‖h⁻¹ • x - center a‖ ≤ 1
  rw [Prod.norm_def, max_le_iff]
  have hx1 := (scaled_coordinate_lt hh).mpr hx.1
  have hx2 := (scaled_coordinate_lt hh).mpr hx.2
  exact ⟨hx1.le,hx2.le⟩

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set Function WeightedEstimates
attribute [local instance] Classical.propDecidable


def squareSum (s : Finset Index) (h : ℝ) (x : Base) : ℝ :=
  ∑ a ∈ s, (cutoff h a x)^2

def normalizedCutoff (s : Finset Index) (h : ℝ) (a : Index) (x : Base) : ℝ :=
  cutoff h a x / Real.sqrt (squareSum s h x)

lemma squareSum_smooth (s : Finset Index) (h : ℝ) : ContDiff ℝ ∞ (squareSum s h) :=
  ContDiff.sum (fun a _ => (cutoff_smooth h a).pow 2)

lemma squareSum_ge_one {s : Finset Index} {h : ℝ} (hh : 0 < h) {x : Base}
    (hcover : ∃ a ∈ s, x ∈ cell h 1 a) : 1 ≤ squareSum s h x := by
  obtain ⟨a,ha,hax⟩ := hcover
  have hb := Finset.single_le_sum (fun b (_ : b ∈ s) => sq_nonneg (cutoff h b x)) ha
  simpa [squareSum,cutoff_one_on_cell hh a hax] using hb

lemma normalizedCutoff_tsupport (s : Finset Index) (h : ℝ) (a : Index) :
    tsupport (normalizedCutoff s h a) ⊆ tsupport (cutoff h a) := by
  apply closure_mono
  intro x hx
  exact fun hz => hx (by simp [normalizedCutoff,hz])

end ClosedSurfaceR4.PhaseGrid

namespace ClosedSurfaceR4.PhaseGrid
open Set Function WeightedEstimates

lemma normalizedCutoff_smooth {U : Set Base} {s : Finset Index} {h : ℝ}
    (hh : 0 < h) (hcover : ∀ x ∈ U, ∃ a ∈ s, x ∈ cell h 1 a) (a : Index) :
    ContDiffOn ℝ ∞ (normalizedCutoff s h a) U := by
  have hm : MapsTo (squareSum s h) U (Ioi 0) :=
    fun x hx => zero_lt_one.trans_le (squareSum_ge_one hh (hcover x hx))
  have hi := inverse_sqrt_smooth.comp (squareSum_smooth s h).contDiffOn hm
  change ContDiffOn ℝ ∞ (fun x => cutoff h a x / Real.sqrt (squareSum s h x)) U
  simpa only [div_eq_mul_inv,Function.comp_apply] using (cutoff_smooth h a).contDiffOn.mul hi




end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CompactPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set

lemma isOpen_cell (h R : ℝ) (a : Index) : IsOpen (cell h R a) :=
  (isOpen_lt ((continuous_fst.sub continuous_const).abs) continuous_const).inter
    (isOpen_lt ((continuous_snd.sub continuous_const).abs) continuous_const)


def coverRegion (s : Finset Index) (h : ℝ) : Set Base := ⋃ a ∈ s, cell h 1 a

lemma coverRegion_open (s : Finset Index) (h : ℝ) : IsOpen (coverRegion s h) :=
  isOpen_iUnion (fun a => isOpen_iUnion (fun _ => isOpen_cell h 1 a))

lemma coverRegion_covers (s : Finset Index) (h : ℝ) {x : Base}
    (hx : x ∈ coverRegion s h) : ∃ a ∈ s, x ∈ cell h 1 a := by
  simpa only [coverRegion,mem_iUnion,exists_prop] using hx




end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GlobalPartition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set Function Filter PhaseGeometry SmallModes RealModes PhaseGrid

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

def refinedCutoff (p : M) (ψ : M → ℝ) (s : Finset Index) (h : ℝ) (a : Index) : M → ℝ :=
  fun q => ψ q * normalizedCutoff s h a (chartCoordinates p q)

omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
lemma refinedCutoff_tsupport_outer (p : M) (ψ : M → ℝ) (s : Finset Index) (h : ℝ) (a : Index) :
    tsupport (refinedCutoff p ψ s h a) ⊆ tsupport ψ := tsupport_mul_subset_left

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasWeights
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
  {ι : Type*} [Fintype ι]

abbrev AtlasCellPhase := ι × (Index × Fin 3)

def atlasActive (p : ι → M) (ψ : ι → M → ℝ) (s : ι → Finset Index)
    (h : ℝ) (a : AtlasCellPhase (ι := ι)) (q : M) : Prop :=
  a.2.1 ∈ s a.1 ∧ q ∈ tsupport (refinedCutoff (p a.1) (ψ a.1) (s a.1) h a.2.1)





end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set PhaseGrid WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {ι : Type*} [Fintype ι]




def AtlasPairMargins (p : ι → M) (ψ : ι → M → ℝ) (s : ι → Finset Index)
    (h κ : ℝ) (ξ : AtlasCellPhase (ι := ι) → SmallModes.Base) (w : AtlasCellPhase (ι := ι) → ℝ)
    (G : M → Space) : Prop :=
  ∀ a b j q, a ≠ b → atlasActive p ψ s h a q → atlasActive p ψ s h b q →
    q ∈ tsupport (ψ j) →
    κ*‖atlasSecondTensor G (p j) q‖ ≤ ‖secondQuadratic (atlasSecondTensor G (p j) q)
      (-(w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
         w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).2,
        (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
         w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).1)‖ ∧
    κ*‖atlasSecondTensor G (p j) q‖ ≤ ‖secondQuadratic (atlasSecondTensor G (p j) q)
      (-(w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
         w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).2,
        (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
         w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).1)‖ ∧
    Good (atlasSecondTensor G (p j) q)
      (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q + w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q) ∧
    Good (atlasSecondTensor G (p j) q)
      (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q - w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q)






end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Data_Nat_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

-- We make `P` and `Q` explicit to help the elaborator when applying the lemma
-- (elab_as_eliminator isn't enough).
theorem exists_by_induction' {α : Type*} (P : ℕ → α → Prop) (Q : ℕ → α → α → Prop)
    (h₀ : ∃ a, P 0 a) (ih : ∀ n a, P n a → ∃ a', P (n + 1) a' ∧ Q n a a') :
    ∃ f : ℕ → α, ∀ n, P n (f n) ∧ Q n (f n) (f <| n + 1) := by
  choose f₀ hf₀ using h₀
  choose! F hF hF' using ih
  have key : ∀ n, P n (Nat.recOn n f₀ F) := fun n ↦ Nat.rec hf₀ (fun n ih ↦ hF n _ ih) n
  exact ⟨fun n ↦ Nat.recOn n f₀ F, fun n ↦ ⟨key n, hF' n _ (key n)⟩⟩
end
end

section
-- module Solutions.OAIQ249_SI.Indexing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Indexing types

This file introduces `IndexType : ℕ → Type` such that `IndexType 0 = ℕ` and
`IndexType (N+1) = Fin (N+1)`. Each `IndexType N` has a total order and and inductive principle
together with supporting lemmas.
-/

section


open Fin Set

/-- Our model indexing type depending on `n : ℕ` is `ℕ` if `n = 0` and `Fin n` otherwise -/
def IndexType (n : ℕ) : Type :=
  Nat.casesOn n ℕ fun k ↦ Fin <| k + 1

open Fin.NatCast in -- TODO: remove this, by making the cast explicit
def IndexType.fromNat : ∀ {N : ℕ}, ℕ → IndexType N
  | 0 => id
  | N + 1 => (Nat.cast : ℕ → Fin (N + 1))

@[simp]
theorem indexType_zero : IndexType 0 = ℕ :=
  rfl

@[simp]
theorem indexType_succ (n : ℕ) : IndexType (n + 1) = Fin (n + 1) :=
  rfl

@[simp]
theorem indexType_of_zero_lt {n : ℕ} (h : 0 < n) : IndexType n = Fin n := by
  rw [← Nat.succ_pred_eq_of_pos h, indexType_succ]

instance instLinearOrderIndexType : ∀ n, LinearOrder (IndexType n)
  | 0 => inferInstanceAs (LinearOrder ℕ)
  | (N + 1) => inferInstanceAs (LinearOrder (Fin (N + 1)))

instance instOrderBotIndexType : ∀ n, OrderBot (IndexType n)
  | 0 => inferInstanceAs (OrderBot ℕ)
  | (N + 1) => inferInstanceAs (OrderBot (Fin (N + 1)))

instance instZeroIndexType : ∀ n, Zero (IndexType n)
  | 0 => inferInstanceAs (Zero ℕ)
  | (N + 1) => inferInstanceAs (Zero (Fin (N + 1)))

instance instSuccOrderIndexType : ∀ n, SuccOrder (IndexType n)
  | 0 => inferInstanceAs (SuccOrder ℕ)
  | (N + 1) => inferInstanceAs (SuccOrder (Fin (N + 1)))

variable {n : ℕ}

theorem IndexType.not_lt_zero (j : IndexType n) : ¬j < 0 :=
  Nat.casesOn n Nat.not_lt_zero (fun _ ↦ Fin.not_lt_zero) j

def IndexType.succ {N : ℕ} : IndexType N → IndexType N := Order.succ

theorem IndexType.succ_castSuccEmb (i : Fin n) :
    @IndexType.succ (n + 1) i.castSucc = i.succ :=
  (Fin.orderSucc_apply _).trans (lastCases_castSucc i)

theorem IndexType.lt_succ (i : IndexType n) (h : ¬IsMax i) : i < i.succ :=
  Order.lt_succ_of_not_isMax h

nonrec theorem IndexType.le_of_lt_succ (i : IndexType n) {j : IndexType n}
    (h : i < j.succ) : i ≤ j :=
  Order.le_of_lt_succ h

theorem IndexType.exists_castSucc_eq (i : IndexType (n + 1)) (hi : ¬IsMax i) :
    ∃ i' : Fin n, i'.castSucc = i := by
  revert hi
  refine Fin.lastCases ?_ (fun i _ ↦ ⟨_, rfl⟩) i
  intro hi; apply hi.elim; intro i _; exact le_last i

-- @[simp] can prove this
theorem IndexType.not_isMax (n : IndexType 0) : ¬IsMax n :=
  not_isMax_of_lt <| Nat.lt_succ_self n

set_option backward.isDefEq.respectTransparency false in
@[elab_as_elim]
theorem IndexType.induction_from {P : IndexType n → Prop} {i₀ : IndexType n} (h₀ : P i₀)
    (ih : ∀ i ≥ i₀, ¬IsMax i → P i → P i.succ) : ∀ i ≥ i₀, P i := by
  cases n
  · intro i h
    induction h with
    | refl => exact h₀
    | step hi₀i hi => exact ih _ hi₀i (IndexType.not_isMax _) hi
  intro i
  refine Fin.induction ?_ ?_ i
  · intro hi; convert h₀; exact (hi.le.antisymm <| Fin.zero_le _).symm
  · intro i hi hi₀i
    rcases hi₀i.le.eq_or_lt with (rfl | hi₀i)
    · exact h₀
    rw [← IndexType.succ_castSuccEmb]
    refine ih _ ?_ ?_ ?_
    · rwa [ge_iff_le, le_castSucc_iff]
    · exact not_isMax_of_lt castSucc_lt_succ
    · apply hi; rwa [ge_iff_le, le_castSucc_iff]

-- We make `P` and `Q` explicit to help the elaborator when applying the lemma
-- (elab_as_eliminator isn't enough).
theorem IndexType.exists_by_induction {α : Type*} (P : IndexType n → α → Prop)
    (Q : IndexType n → α → α → Prop) (h₀ : ∃ a, P 0 a)
    (ih : ∀ n a, P n a → ¬IsMax n → ∃ a', P n.succ a' ∧ Q n a a') :
    ∃ f : IndexType n → α, ∀ n, P n (f n) ∧ (¬IsMax n → Q n (f n) (f n.succ)) := by
  revert P Q h₀ ih
  cases n with
  | zero =>
    intro P Q h₀ ih
    rcases exists_by_induction' P Q h₀ (fun n a hn ↦ ih n a hn (not_isMax n)) with ⟨f, hf⟩
    exact ⟨f, fun n ↦ ⟨(hf n).1, fun _ ↦ (hf n).2⟩⟩
  | succ N =>
    -- dsimp only [IndexType, IndexType.succ]
    intro P Q h₀ ih
    choose f₀ hf₀ using h₀
    choose! F hF hF' using ih
    let G := fun i : Fin N ↦ F i.castSucc
    let f : Fin (N + 1) → α := fun i ↦ Fin.induction f₀ G i
    have key : ∀ i, P i (f i) := by
      refine fun i ↦ Fin.induction hf₀ ?_ i
      intro i hi
      simp_rw [f, induction_succ, ← IndexType.succ_castSuccEmb]
      exact hF _ _ hi (not_isMax_of_lt castSucc_lt_succ)
    refine ⟨f, fun i ↦ ⟨key i, fun hi ↦ ?_⟩⟩
    convert hF' _ _ (key i) hi
    rcases i.exists_castSucc_eq hi with ⟨i, rfl⟩
    simp_rw [IndexType.succ_castSuccEmb, f, induction_succ]
    rfl
end
end

section
-- module Solutions.OAIQ249_SI.Notations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

open scoped Topology ContDiff

scoped[SENot] notation "𝒞" => ContDiff ℝ

scoped[SENot] notation "hull" => convexHull ℝ

scoped[SENot] notation "D" => fderiv ℝ

-- `∀ᶠ x near s, p x` means property `p` holds at every point in a neighborhood of the set `s`.
scoped[SENot] notation3 (prettyPrint := false)
  "∀ᶠ " (...) " near " s ", " r:(scoped p => Filter.Eventually p <| 𝓝ˢ s) => r

scoped[SENot] notation:70 u " ⬝ " φ:65 => ContinuousLinearMap.comp (ContinuousLinearMap.toSpanSingleton ℝ u) φ
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Topology_Misc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open Set Function Filter TopologicalSpace
open scoped unitInterval Topology uniformity

section

/-! ## The standard ℤ action on ℝ is properly discontinuous

TODO: use that in ToMathlib.Algebra.Periodic?
-/

instance instVAddIntReal_solutions : VAdd ℤ ℝ :=
  ⟨fun n x ↦ (n : ℝ) + x⟩

instance instProperlyDiscontinuousVAddIntReal_solutions : ProperlyDiscontinuousVAdd ℤ ℝ :=
  ⟨fun {K L} hK hL ↦ by
    rcases eq_empty_or_nonempty K with (rfl | hK') <;>
        rcases eq_empty_or_nonempty L with (rfl | hL') <;>
      try simp only [image_empty, inter_self, ofPred_false, finite_empty, empty_inter, inter_empty,
        Set.not_nonempty_empty, image_inter_nonempty_iff]
    have hSK := (hK.isLUB_sSup hK').1
    have hIK := (hK.isGLB_sInf hK').1
    have hSL := (hL.isLUB_sSup hL').1
    have hIL := (hL.isGLB_sInf hL').1
    apply (finite_Icc ⌈sInf L - sSup K⌉ ⌊sSup L - sInf K⌋).subset
    intro n ⟨x, hk, hnk⟩
    replace hnk : (n : ℝ) + x ∈ L := hnk
    constructor
    · rw [Int.ceil_le]
      linarith [hIL hnk, hSK hk]
    · rw [Int.le_floor]
      linarith [hSL hnk, hIK hk]⟩

end

section Fract

open Int

/- properties of the (dis)continuity of `Int.fract` on `ℝ`.
To be PRed to Topology.Algebra.FloorRing
-/

theorem Ioo_floor_mem_nhds {x : ℝ} (h : x ∉ range (Int.cast : ℤ → ℝ)) : Ioo (⌊x⌋ : ℝ) (⌊x⌋ + 1 : ℝ) ∈ 𝓝 x :=
  Ioo_mem_nhds (floor_lt_self_iff.mpr h) (lt_floor_add_one x)

theorem fract_lt {x y : ℝ} {n : ℤ} (h1 : (n : ℝ) ≤ x) (h2 : x < n + y) : fract x < y := by
  obtain (hy | hy) := le_total y 1
  · rw [← fract_sub_intCast x n, fract_eq_self.mpr]
    · linarith
    · constructor <;> linarith
  · exact (fract_lt_one x).trans_le hy

theorem one_sub_lt_fract {x y : ℝ} {n : ℤ} (hy : y ≤ 1) (h1 : (n : ℝ) - y < x) (h2 : x < n) :
    1 - y < fract x := by
  have I₁ : 1 - y < x - (n - 1) := by linarith
  have I₂ : x - (n - 1) < 1 := by linarith
  norm_cast at I₁ I₂
  rw [← fract_sub_intCast x (n - 1), fract_eq_self.mpr]
  · exact I₁
  · constructor <;> linarith

theorem IsOpen.preimage_fract' {s : Set ℝ} (hs : IsOpen s) (h2s : 0 ∈ s → s ∈ 𝓝[<] (1 : ℝ)) :
    IsOpen (fract ⁻¹' s) := by
  rw [isOpen_iff_mem_nhds]
  rintro x (hx : fract x ∈ s)
  rcases eq_or_ne (fract x) 0 with (hx' | hx')
  · have H : (0 : ℝ) ∈ s := by rwa [hx'] at hx
    specialize h2s H
    rcases Int.fract_eq_zero_iff.mp hx' with ⟨n, rfl⟩; clear hx hx'
    have s_mem_0 := hs.mem_nhds H
    rcases(nhds_basis_zero_abs_lt ℝ).mem_iff.mp s_mem_0 with ⟨δ, δ_pos, hδ⟩
    rcases(nhdsWithin_hasBasis (nhds_basis_Ioo_pos (1 : ℝ)) _).mem_iff.mp h2s with ⟨ε, ε_pos, hε⟩
    rw [Set.Ioo_inter_Iio, min_eq_right (le_add_of_nonneg_right ε_pos.le)] at hε
    set ε' := min ε (1 / 2)
    have ε'_pos : 0 < ε' := lt_min ε_pos (by norm_num : (0 : ℝ) < 1 / 2)
    have hε' : Ioo (1 - ε') 1 ⊆ s := by
      apply Subset.trans _ hε
      apply Ioo_subset_Ioo_left
      linarith [min_le_left ε (1 / 2)]
    have mem : Ioo ((n : ℝ) - ε') (n + δ) ∈ 𝓝 (n : ℝ) := by apply Ioo_mem_nhds <;> linarith
    apply mem_of_superset mem
    rintro x ⟨hx, hx'⟩
    obtain (hx'' | hx'') := le_or_gt (n : ℝ) x
    · apply hδ
      rw [mem_ofPred_eq, abs_eq_self.mpr (fract_nonneg x)]
      exact fract_lt hx'' hx'
    · apply hε'
      exact ⟨one_sub_lt_fract (by linarith [min_le_right ε (1 / 2)]) (by linarith) hx'',
        fract_lt_one x⟩
  · rw [Int.fract_ne_zero_iff] at hx'
    have H : Ico (⌊x⌋ : ℝ) (⌊x⌋ + 1) ∈ 𝓝 x :=
      mem_of_superset (Ioo_floor_mem_nhds hx') Ioo_subset_Ico_self
    exact (continuousOn_fract ⌊x⌋).continuousAt H (hs.mem_nhds hx)

theorem IsOpen.preimage_fract {s : Set ℝ} (hs : IsOpen s) (h2s : (0 : ℝ) ∈ s → (1 : ℝ) ∈ s) :
    IsOpen (fract ⁻¹' s) :=
  hs.preimage_fract' fun h ↦ nhdsWithin_le_nhds <| hs.mem_nhds (h2s h)

-- is `sᶜ ∉ 𝓝[<] (1 : ℝ)` equivalent to something like `ClusterPt (𝓝[Iio (1 : ℝ) ∩ s] (1 : ℝ)` ?
theorem IsClosed.preimage_fract {s : Set ℝ} (hs : IsClosed s)
    (h2s : sᶜ ∉ 𝓝[<] (1 : ℝ) → (0 : ℝ) ∈ s) : IsClosed (fract ⁻¹' s) :=
  isOpen_compl_iff.mp <| hs.isOpen_compl.preimage_fract' fun h ↦ by_contra fun h' ↦ h <| h2s h'

end Fract

section projI

variable {α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {x c : α}

/-- If `α` is a `LinearOrderedSemiring`, then `projI : α → α` projection of `α` onto the unit
interval `[0, 1]`. -/
def projI : α → α := fun x ↦ projIcc (0 : α) 1 zero_le_one x

theorem projI_def : projI x = max 0 (min 1 x) :=
  rfl

@[simp]
theorem projI_zero : projI (0 : α) = 0 :=
  congr_arg Subtype.val <| projIcc_left _

@[simp]
theorem projI_one : projI (1 : α) = 1 :=
  congr_arg Subtype.val <| projIcc_right _

@[simp]
theorem projI_eq_zero : projI x = 0 ↔ x ≤ 0 := by
  rw [← projIcc_eq_left (zero_lt_one' α), Subtype.ext_iff]; rfl

@[simp]
theorem projI_eq_one : projI x = 1 ↔ 1 ≤ x := by
  rw [← projIcc_eq_right (zero_lt_one' α), Subtype.ext_iff]; rfl

theorem projI_mem_Icc : projI x ∈ Icc (0 : α) 1 :=
  (projIcc (0 : α) 1 zero_le_one x).prop

theorem projI_eq_self : projI x = x ↔ x ∈ Icc (0 : α) 1 :=
  ⟨fun h ↦ h ▸ projI_mem_Icc, fun h ↦ congr_arg Subtype.val <| projIcc_of_mem _ h⟩

@[simp]
theorem projI_projI : projI (projI x) = projI x :=
  projI_eq_self.mpr projI_mem_Icc

@[simp]
theorem projIcc_projI : projIcc (0 : α) 1 zero_le_one (projI x) = projIcc 0 1 zero_le_one x :=
  projIcc_of_mem _ projI_mem_Icc

@[simp]
theorem range_projI : range projI = Icc 0 1 := by
  erw [range_comp, range_projIcc, image_univ, Subtype.range_coe]

@[simp]
theorem projI_eq_min : projI x = min 1 x ↔ 0 ≤ x := by
  simp_rw [projI_def, max_eq_right_iff, le_min_iff, zero_le_one, true_and]

theorem continuous_projI [TopologicalSpace α] [OrderTopology α] : Continuous (projI : α → α) :=
  continuous_projIcc.subtype_val

end projI

section

-- TODO: move to Topology.Compactness.Compact
variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

theorem IsCompact.eventually_forall_mem {x₀ : α} {K : Set β} (hK : IsCompact K) {f : α → β → γ}
    (hf : Continuous ↿f) {U : Set γ} (hU : ∀ y ∈ K, U ∈ 𝓝 (f x₀ y)) :
    ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, f x y ∈ U :=
  hK.eventually_forall_of_forall_eventually fun y hy ↦
    (hf.tendsto _).eventually <| show U ∈ 𝓝 ((↿f) (x₀, y)) from hU y hy

end

section

open Metric

attribute [fun_prop] continuous_infDist_pt

theorem Continuous.infDist {α β : Type*} [TopologicalSpace α] [PseudoMetricSpace β] {s : Set β}
    {f : α → β} (hf : Continuous f) : Continuous fun x ↦ infDist (f x) s := by fun_prop

end

open Subtype
end
end
end

section
-- module Solutions.OAIQ249_SI.InductiveConstructions
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

-- set_option trace.filter_inst_type true

open Set Filter Function
open scoped Topology unitInterval

/-!
Notes by Patrick:

The goal of this file is to explore how to prove `exists_surrounding_loops` and the local to global
inductive homotopy construction in a way that uncouples the general
topological argument from the things specific to loops or homotopies of jet sections.

First there is a lemma `inductive_construction` which abstracts the locally ultimately constant
arguments, assuming we work with a fixed covering. It builds on
`LocallyFinite.exists_forall_eventually_of_indexType`.

From `inductive_construction` alone we deduce `inductive_htpy_construction` which builds a homotopy
in a similar context. This is meant to be used to go from Chapter 2 to Chapter 3.

Combining `inductive_construction` with an argument using local existence and exhaustions, we
get `inductive_construction_of_loc` building a function from local existence and patching
assumptions. It also has a version `relative_inductive_construction_of_loc` which does this
relative to a closed set. This is used for `exists_surrounding_loops`.

This file also contains supporting lemmas about `IndexType`. A short term goal will be to
get rid of the `indexing` abstraction and do everything in terms of `IndexType`, unless
`indexing` makes those supporting lemmas really cleaner to prove.
-/


section inductive_construction

theorem LocallyFinite.exists_forall_eventually_of_indexType {α X : Type*} [TopologicalSpace X]
    {N : ℕ} {f : IndexType N → X → α} {V : IndexType N → Set X} (hV : LocallyFinite V)
    (h : ∀ n : IndexType N, ¬IsMax n → ∀ x ∉ (V n.succ), f n.succ x = f n x) :
    ∃ F : X → α, ∀ x : X, ∀ᶠ n in Filter.atTop, f n =ᶠ[𝓝 x] F := by
  choose U hUx hU using hV
  choose i₀ hi₀ using fun x ↦ (hU x).bddAbove
  have key : ∀ {x} {n}, n ≥ i₀ x → ∀ {y}, y ∈ U x → f n y = f (i₀ x) y := fun {x} ↦ by
    refine @IndexType.induction_from N (fun i ↦ ∀ {y}, y ∈ U x → f i y = f (i₀ x) y) _ ?_ ?_
    · exact fun _ ↦ rfl
    · intro i hi h'i ih y hy
      rw [h i h'i, ih hy]
      intro h'y
      replace hi₀ := mem_upperBounds.mp (hi₀ x) i.succ ⟨y, h'y, hy⟩
      exact lt_irrefl _ (((i.lt_succ h'i).trans_le hi₀).trans_le hi)
  refine ⟨fun x ↦ f (i₀ x) x, fun x ↦ ?_⟩
  refine (eventually_ge_atTop (i₀ x)).mono fun n hn ↦ ?_
  refine mem_of_superset (hUx x) fun y hy ↦ ?_
  calc
    f n y = f (i₀ x) y := key hn hy
    _ = f (max (i₀ x) (i₀ y)) y := (key (le_max_left ..) hy).symm
    _ = f (i₀ y) y := key (le_max_right ..) (mem_of_mem_nhds <| hUx y)

end inductive_construction
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Analysis_NormedSpace_OperatorNorm_Prod
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

variable {𝕜 E F G Fₗ Gₗ X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup Fₗ] [NormedAddCommGroup Gₗ] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜 Gₗ] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
  [TopologicalSpace X]

@[simp]
theorem ContinuousLinearMap.comp_toSpanSingleton_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : E →L[ℝ] ℝ) (v : E)
    (u : F) : ((ContinuousLinearMap.toSpanSingleton ℝ u).comp φ) v = φ v • u :=
  rfl

universe u₁ u₂ u₃ u₄

theorem isBoundedLinearMap_coprod (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    IsBoundedLinearMap 𝕜 fun p : (E →L[𝕜] G) × (F →L[𝕜] G) ↦ p.1.coprod p.2 :=
  { map_add := by
      intros
      apply ContinuousLinearMap.coeFn_injective
      ext u
      simp only [Prod.fst_add, Prod.snd_add, ContinuousLinearMap.coprod_apply, add_apply]
      ac_rfl
    map_smul := by
      intro r p
      apply ContinuousLinearMap.coeFn_injective
      ext x
      simp
    bound := by
      refine ⟨2, zero_lt_two, fun ⟨φ, ψ⟩ ↦ ?_⟩
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      rintro ⟨e, f⟩
      calc
        ‖φ e + ψ f‖ ≤ ‖φ e‖ + ‖ψ f‖ := norm_add_le _ _
        _ ≤ ‖φ‖ * ‖e‖ + ‖ψ‖ * ‖f‖ := (add_le_add (φ.le_opNorm e) (ψ.le_opNorm f))
        _ ≤ 2 * max ‖φ‖ ‖ψ‖ * max ‖e‖ ‖f‖ := by
          rw [two_mul, add_mul]
          gcongr <;> first | apply le_max_left | apply le_max_right }

/-- The natural continuous linear map `((E →L[𝕜] G) × (F →L[𝕜] G)) →L[𝕜] (E × F →L[𝕜] G)` for
normed spaces `E`, `F`, `G` over a normed field `𝕜`.

If `g₁ : E →L[𝕜] G` and `g₂ : F →L[𝕜] G` then `continuous_linear_map.coprodL (g₁, g₂)` is the map
`(e, f) ↦ g₁ e + g₂ f`. -/
def ContinuousLinearMap.coprodL : (E →L[𝕜] G) × (F →L[𝕜] G) →L[𝕜] E × F →L[𝕜] G :=
  (isBoundedLinearMap_coprod 𝕜 E F G).toContinuousLinearMap

@[continuity, fun_prop]
theorem Continuous.coprodL {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x ↦ (f x).coprod (g x) :=
  ContinuousLinearMap.coprodL.continuous.comp₂ hf hg

theorem Continuous.prodL' {𝕜 : Type*} {E : Type*} {Fₗ : Type*} {Gₗ : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup Gₗ]
    [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜 Gₗ]
    {X : Type*} [TopologicalSpace X]
    {f : X → E →L[𝕜] Fₗ} {g : X → E →L[𝕜] Gₗ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x ↦ (f x).prod (g x) :=
  (ContinuousLinearMap.prodₗᵢ 𝕜).continuous.comp₂ hf hg

@[continuity, fun_prop]
theorem Continuous.prodL {𝕜 : Type*} {E : Type*} {Fₗ : Type*} {Gₗ : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup Gₗ]
    [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜 Gₗ] {X : Type*}
    [TopologicalSpace X] {f : X → E →L[𝕜] Fₗ} {g : X → E →L[𝕜] Gₗ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x ↦ (f x).prod (g x) :=
  hf.prodL' hg

@[continuity, fun_prop]
theorem ContinuousAt.compL {f : X → Fₗ →L[𝕜] Gₗ} {g : X → E →L[𝕜] Fₗ} {x₀ : X}
    (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀) :
    ContinuousAt (fun x ↦ (f x).comp (g x)) x₀ :=
  ((ContinuousLinearMap.compL 𝕜 E Fₗ Gₗ).continuous₂.tendsto (f x₀, g x₀)).comp
    (hf.prodMk_nhds hg)

@[continuity, fun_prop]
theorem Continuous.compL {f : X → Fₗ →L[𝕜] Gₗ} {g : X → E →L[𝕜] Fₗ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x ↦ (f x).comp (g x) :=
  (ContinuousLinearMap.compL 𝕜 E Fₗ Gₗ).continuous₂.comp₂ hf hg
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_DualPair
attribute [-instance] _root_.instVAddIntReal_solutions
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-! # Dual pairs

Convex integration improves maps by successively modify their derivative in a direction of a
vector field (almost) without changing their derivative along some complementary hyperplace.

In this file we introduce the linear algebra part of the story of such modifications.
The main gadget here are dual pairs on a real topological vector space `E`.
Each `p : DualPair E` is made of a (continuous) linear form `p.π : E →L[ℝ] ℝ` and a vector
`p.v : E` such that `p.π p.v = 1`.

Those pairs are used to build the updating operation turning `φ : E →L[ℝ] F` into
`p.update φ w` which equals `φ` on `ker p.π` and sends `v` to the given `w : F`.

After formalizing the above definitions, we first record a number of trivial algebraic lemmas.
Then we prove a lemma which is geometrically obvious but not so easy to formalize:
`injective_update_iff` states, starting with an injective `φ`, that the updated
map `p.update φ w` is injective if and only if `w` isn't in the image of `ker p.π` under `φ`.
This is crucial in order to apply convex integration to immersions.

Then we prove continuity and smoothness lemmas for this operation.
-/

section


noncomputable section

open Function ContinuousLinearMap

open LinearMap (ker)

open scoped ContDiff

/-! ## General theory -/

section NoNorm

variable (E : Type*) {E' F G : Type*}

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

variable [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A continuous linear form `π` and a vector `v` that pair to one. In particular `ker π` is a
hyperplane and `v` spans a complement of this hyperplane. -/
structure DualPair where
  π : E →L[ℝ] ℝ
  v : E
  pairing : π v = 1

namespace DualPair

variable {E}

attribute [local simp] ContinuousLinearMap.toSpanSingleton_apply

/-- Given a dual pair `p`, `p.span_v` is the line spanned by `p.v`. -/
def spanV (p : DualPair E) : Submodule ℝ E :=
  Submodule.span ℝ {p.v}

/-- Update a continuous linear map `φ : E →L[ℝ] F` using a dual pair `p` on `E` and a
vector `w : F`. The new map coincides with `φ` on `ker p.π` and sends `p.v` to `w`. -/
def update (p : DualPair E) (φ : E →L[ℝ] F) (w : F) : E →L[ℝ] F :=
  φ + (w - φ p.v) ⬝ p.π

@[simp]
theorem update_ker_pi (p : DualPair E) (φ : E →L[ℝ] F) (w : F) {u} (hu : u ∈ p.π.ker) :
    p.update φ w u = φ u := by
  rw [LinearMap.mem_ker] at hu
  simpa [update] using Or.inl hu

@[simp]
theorem update_v (p : DualPair E) (φ : E →L[ℝ] F) (w : F) : p.update φ w p.v = w := by
  simp [update, p.pairing]

@[simp]
theorem update_self (p : DualPair E) (φ : E →L[ℝ] F) : p.update φ (φ p.v) = φ := by
  simp only [update, add_zero, ContinuousLinearMap.toSpanSingleton_zero,
    ContinuousLinearMap.zero_comp, sub_self]

@[simp]
theorem update_update (p : DualPair E) (φ : E →L[ℝ] F) (w w' : F) :
    p.update (p.update φ w') w = p.update φ w := by
  simp_rw [update, add_apply, coe_comp, (· ∘ ·), toSpanSingleton_apply, p.pairing, one_smul,
    add_sub_cancel, add_assoc, ← ContinuousLinearMap.add_comp, ← toSpanSingleton_add,
    sub_add_eq_add_sub, add_sub_cancel]

/-- Map a dual pair under a linear equivalence. -/
@[simps]
def map (p : DualPair E) (L : E ≃L[ℝ] E') : DualPair E' :=
  ⟨p.π ∘L ↑L.symm, L p.v, (congr_arg p.π <| L.symm_apply_apply p.v).trans p.pairing⟩

/-! ## Injectivity criterion -/


end DualPair

end NoNorm

/-! ## Smoothness and continuity -/


namespace DualPair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/- In the next two lemmas, finite dimensionality of `E` is clearly uneeded, but allows
to use `contDiff_clm_apply_iff` and `continuous_clm_apply`. -/
theorem smooth_update [FiniteDimensional ℝ E] (p : DualPair E) {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {φ : G → E →L[ℝ] F} (hφ : 𝒞 ∞ φ) {w : G → F} (hw : 𝒞 ∞ w) :
    𝒞 ∞ fun g ↦ p.update (φ g) (w g) := by
  apply hφ.add
  rw [contDiff_clm_apply_iff]
  intro y
  exact (hw.sub (contDiff_clm_apply_iff.mp hφ p.v)).const_smul _

theorem continuous_update [FiniteDimensional ℝ E] (p : DualPair E) {X : Type*} [TopologicalSpace X]
    {φ : X → E →L[ℝ] F} (hφ : Continuous φ) {w : X → F} (hw : Continuous w) :
    Continuous fun g ↦ p.update (φ g) (w g) := by
  apply hφ.add
  rw [continuous_clm_apply]
  intro y
  exact (hw.sub (continuous_clm_apply.mp hφ p.v)).const_smul _

end DualPair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Given a finite basis `e : basis ι ℝ E`, and `i : ι`,
`e.DualPair i` is given by the `i`th basis element and its dual. -/
def Module.Basis.dualPair [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℝ E) (i : ι) : DualPair E where
  π := LinearMap.toContinuousLinearMap (e.dualBasis i)
  v := e i
  pairing := by simp
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_OneJet
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-! # Spaces of 1-jets and their sections

For real normed spaces `E` and `F`, this file defines the space `OneJetSec E F` of 1-jets
of maps from `E` to `F` as `E × F × (E →L[ℝ] F)`.

A section `𝓕 : JetSet E F` of this space is a map `(𝓕.f, 𝓕.φ) : E → F × (E →L[ℝ] F)`.

It is holonomic at `x`, spelled `𝓕.IsHolonomicAt x` if the differential of `𝓕.f` at `x`
is `𝓕.φ x`.

We then introduced parametrized families of sections, and especially homotopies of sections,
with type `HtpyJetSec E F` and their concatenation operation `HtpyJetSec.comp`.


Implementation note: the time parameter `t` for homotopies is any real number, but all the
homotopies we will construct will be constant for `t ≤ 0` and `t ≥ 1`. It looks like this imposes
more smoothness constraints at `t = 0` and `t = 1` (requiring flat functions), but this is needed
for smooth concatenations anyway.
 -/

section


noncomputable section

open Set Function Real Filter

open scoped unitInterval Topology ContDiff


variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]

/-! ## Spaces of 1-jets -/


/-- The space of 1-jets of maps from `E` to `F`. -/
abbrev OneJet :=
  E × F × (E →L[ℝ] F)

/-- A smooth section of J¹(E, F) → E. -/
@[ext]
structure JetSec where
  f : E → F
  f_diff : 𝒞 ∞ f
  φ : E → E →L[ℝ] F
  φ_diff : 𝒞 ∞ φ

namespace JetSec

variable {E F}

instance instFunLikeProdContinuousLinearMapRealId : FunLike (JetSec E F) E (F × (E →L[ℝ] F)) where
  coe 𝓕 := fun x ↦ (𝓕.f x, 𝓕.φ x)
  coe_injective := by
    rintro ⟨⟩ ⟨⟩ h; congr
    exacts [congr_arg (Prod.fst ∘ ·) h, congr_arg (Prod.snd ∘ ·) h]

@[simp]
theorem mk_apply (f : E → F) (f_diff φ φ_diff) (x : E) : mk f f_diff φ φ_diff x = (f x, φ x) := rfl

/-! ## Holonomic sections-/

/-- A jet section `𝓕` is holonomic if its linear map part at `x`
is the derivative of its function part at `x`. -/
def IsHolonomicAt (𝓕 : JetSec E F) (x : E) : Prop :=
  D 𝓕.f x = 𝓕.φ x

/-- A formal solution `𝓕` of `R` is partially holonomic in the direction of some subspace `E'`
if its linear map part at `x` is the derivative of its function part at `x` in restriction to
`E'`. -/
def IsPartHolonomicAt (𝓕 : JetSec E F) (E' : Submodule ℝ E) (x : E) :=
  ∀ v ∈ E', D 𝓕.f x v = 𝓕.φ x v

@[simp]
theorem isPartHolonomicAt_bot (𝓕 : JetSec E F) : IsPartHolonomicAt 𝓕 ⊥ = fun _ ↦ True := by
  ext x
  simp only [IsPartHolonomicAt, Submodule.mem_bot, forall_eq, map_zero]

end JetSec

/-! ## Homotopies of sections -/

section HtpyJetSec

/-- A parametrized family of sections of J¹(E, F). -/
structure FamilyJetSec where
  f : P → E → F
  f_diff : 𝒞 ∞ ↿f
  φ : P → E → E →L[ℝ] F
  φ_diff : 𝒞 ∞ ↿φ

/-- A homotopy of sections of J¹(E, F). -/
@[reducible]
def HtpyJetSec :=
  FamilyJetSec E F ℝ

variable {E F P}

namespace FamilyJetSec

instance instFunLikeJetSec : FunLike (FamilyJetSec E F P) P (JetSec E F) where
  coe S t :=
    { f := S.f t
      f_diff := S.f_diff.comp (contDiff_const.prodMk contDiff_id)
      φ := S.φ t
      φ_diff := S.φ_diff.comp (contDiff_const.prodMk contDiff_id) }
  coe_injective := by
    rintro ⟨⟩ ⟨⟩ h
    simp only [funext_iff, DFunLike.ext_iff, JetSec.mk_apply, Prod.ext_iff] at h
    congr <;> ext <;> simp [h]

@[simp] theorem mk_apply_apply (f : P → E → F) (f_diff φ φ_diff t x) :
    mk f f_diff φ φ_diff t x = (f t x, φ t x) :=
  rfl

@[simp] theorem mk_apply_f (f : P → E → F) (f_diff φ φ_diff t) :
    (mk f f_diff φ φ_diff t).f = f t :=
  rfl

@[simp] theorem mk_apply_φ (f : P → E → F) (f_diff φ φ_diff t) :
    (mk f f_diff φ φ_diff t).φ = φ t :=
  rfl

end FamilyJetSec

/-- The constant homotopy of formal solutions at a given formal solution. It will be used
as junk value for constructions of formal homotopies that need additional assumptions and also
for trivial induction initialization. -/
def JetSec.constHtpy (𝓕 : JetSec E F) : HtpyJetSec E F where
  f _ := 𝓕.f
  f_diff := 𝓕.f_diff.snd'
  φ _ := 𝓕.φ
  φ_diff := 𝓕.φ_diff.snd'

@[simp]
theorem JetSec.constHtpy_apply (𝓕 : JetSec E F) : ∀ t, 𝓕.constHtpy t = 𝓕 := fun t ↦ by
  ext x <;> rfl

/-! ## Concatenation of homotopies of sections

In this part of the file we build a concatenation operation for homotopies of 1-jet sections.
We first need to introduce a smooth step function on `ℝ`. There is already a version
of this in mathlib called `smooth_transition` but that version is not locally constant
near `0` and `1`, which is not convenient enough for gluing purposes.
-/


/-- A smooth step function on `ℝ`. -/
def smoothStep : ℝ → ℝ := fun t ↦ smoothTransition (2 * t - 1 / 2)

theorem smoothStep.smooth : 𝒞 ∞ smoothStep :=
  smoothTransition.contDiff.comp <| (contDiff_id.const_smul (2 : ℝ)).sub contDiff_const

@[simp]
theorem smoothStep.zero : smoothStep 0 = 0 := by
  apply smoothTransition.zero_of_nonpos
  norm_num

@[simp]
theorem smoothStep.one : smoothStep 1 = 1 := by
  apply smoothTransition.one_of_one_le
  norm_num

theorem smoothStep.of_lt {t : ℝ} (h : t < 1 / 4) : smoothStep t = 0 := by
  apply smoothTransition.zero_of_nonpos
  linarith

theorem smoothStep.of_gt {t : ℝ} (h : 3 / 4 < t) : smoothStep t = 1 := by
  apply smoothTransition.one_of_one_le
  linarith

theorem htpy_jet_sec_comp_aux {f g : ℝ → E → F} (hf : 𝒞 ∞ ↿f) (hg : 𝒞 ∞ ↿g) (hfg : f 1 = g 0) :
    𝒞 ∞ ↿(fun t x ↦ if t ≤ 1 / 2 then f (smoothStep <| 2 * t) x
      else g (smoothStep <| 2 * t - 1) x : ℝ → E → F) := by
  have s₁ : 𝒞 ∞ (fun p ↦ (smoothStep (2 * p.1), p.2) : ℝ × E → ℝ × E) :=
    (smoothStep.smooth.comp (contDiff_const.mul contDiff_id)).prodMap contDiff_id
  replace hf := hf.comp s₁
  have s₂ : 𝒞 ∞ (fun p ↦ (smoothStep <| 2 * p.1 - 1, p.2) : ℝ × E → ℝ × E) :=
    (smoothStep.smooth.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).prodMap
      contDiff_id
  replace hg := hg.comp s₂
  rw [contDiff_iff_contDiffAt] at *
  rintro ⟨t₀, x₀⟩
  rcases lt_trichotomy t₀ (1 / 2) with (ht | rfl | ht)
  · apply (hf (t₀, x₀)).congr_of_eventuallyEq
    have : (Iio (1 / 2) : Set ℝ) ×ˢ univ ∈ 𝓝 (t₀, x₀) :=
      prod_mem_nhds_iff.mpr ⟨Iio_mem_nhds ht, univ_mem⟩
    filter_upwards [this] with p hp
    obtain ⟨t, x⟩ := p
    replace hp : t < 1 / 2 := (prodMk_mem_set_prod_eq.mp hp).1
    change ite (t ≤ 1 / 2) (f (smoothStep (2 * t)) x) (g (smoothStep (2 * t - 1)) x) = _
    rw [ite_eq_left hp.le]
    rfl
  · apply (hf (1 / 2, x₀)).congr_of_eventuallyEq
    have : (Ioo (3 / 8) (5 / 8) : Set ℝ) ×ˢ univ ∈ 𝓝 (1 / (2 : ℝ), x₀) := by
      refine prod_mem_nhds_iff.mpr ⟨Ioo_mem_nhds ?_ ?_, univ_mem⟩ <;> norm_num
    filter_upwards [this] with p hp
    obtain ⟨t, x⟩ := p
    obtain ⟨lt_t, t_lt⟩ := (prodMk_mem_set_prod_eq.mp hp).1
    change ite (t ≤ 1 / 2) (f (smoothStep (2 * t)) x) (g (smoothStep (2 * t - 1)) x) = _
    split_ifs
    · rfl
    · change g _ x = f (smoothStep <| 2 * t) x
      apply congr_fun
      rw [show smoothStep (2 * t - 1) = 0 by apply smoothStep.of_lt; linarith,
        show smoothStep (2 * t) = 1 by apply smoothStep.of_gt; linarith, hfg]
  · apply (hg (t₀, x₀)).congr_of_eventuallyEq
    have : (Ioi (1 / 2) : Set ℝ) ×ˢ univ ∈ 𝓝 (t₀, x₀) :=
      prod_mem_nhds_iff.mpr ⟨Ioi_mem_nhds ht, univ_mem⟩
    filter_upwards [this] with p hp
    obtain ⟨t, x⟩ := p
    replace hp : ¬t ≤ 1 / 2 := by push Not; exact (prodMk_mem_set_prod_eq.mp hp).1
    change ite (t ≤ 1 / 2) (f (smoothStep (2 * t)) x) (g (smoothStep (2 * t - 1)) x) = _
    rw [ite_eq_right hp]
    rfl

/-- Concatenation of homotopies of formal solution. The result depend on our choice of
a smooth step function in order to keep smoothness with respect to the time parameter. -/
def HtpyJetSec.comp (𝓕 𝓖 : HtpyJetSec E F) (h : 𝓕 1 = 𝓖 0) : HtpyJetSec E F where
  f t x := if t ≤ 1 / 2 then 𝓕.f (smoothStep <| 2 * t) x else 𝓖.f (smoothStep <| 2 * t - 1) x
  f_diff := htpy_jet_sec_comp_aux 𝓕.f_diff 𝓖.f_diff (show (𝓕 1).f = (𝓖 0).f by rw [h])
  φ t x := if t ≤ 1 / 2 then 𝓕.φ (smoothStep <| 2 * t) x else 𝓖.φ (smoothStep <| 2 * t - 1) x
  φ_diff := htpy_jet_sec_comp_aux 𝓕.φ_diff 𝓖.φ_diff (show (𝓕 1).φ = (𝓖 0).φ by rw [h])

@[simp]
theorem HtpyJetSec.comp_of_le (𝓕 𝓖 : HtpyJetSec E F) (h) {t : ℝ} (ht : t ≤ 1 / 2) :
    𝓕.comp 𝓖 h t = 𝓕 (smoothStep <| 2 * t) := by
  ext x : 2 <;> · dsimp [HtpyJetSec.comp]; exact ite_eq_left ht

@[simp]
theorem HtpyJetSec.comp_of_not_le (𝓕 𝓖 : HtpyJetSec E F) (h) {t : ℝ} (ht : ¬t ≤ 1 / 2) :
    𝓕.comp 𝓖 h t = 𝓖 (smoothStep <| 2 * t - 1) := by
  rw [one_div] at ht
  ext x : 2 <;> simp [comp, ite_eq_right ht] <;> rfl

end HtpyJetSec
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_Relation
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Local partial differential relations and their formal solutions

This file defines `RelLoc E F`, the type of first order partial differential relations
for maps between two real normed spaces `E` and `F`.

To any `R : RelLoc E F` we associate the type `sol R` of maps `f : E → F` of
solutions of `R`, and its formal counterpart `FormalSol R`.
(FIXME(grunweg): `sol` is never mentioned; is this docstring outdated?)

The h-principle question is whether we can deform any formal solution into a solution.
The type of deformations is `HtpyJetSet E F` (homotopies of 1-jet sections).
-/

section


noncomputable section

open Set Function Real Filter

open scoped unitInterval Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A first order relation for maps between real vector spaces. -/
abbrev RelLoc :=
  Set (OneJet E F)

instance instMembershipProdContinuousLinearMapRealIdRelLoc : Membership (E × F × (E →L[ℝ] F)) (RelLoc E F) := by delta RelLoc; infer_instance

variable {E F}

/-- A predicate stating that a 1-jet section is a formal solution to a first order relation for
maps between vector spaces. -/
def JetSec.IsFormalSol (𝓕 : JetSec E F) (R : RelLoc E F) : Prop :=
  ∀ x, (x, 𝓕.f x, 𝓕.φ x) ∈ R

namespace RelLoc

/-- A formal solution to a local relation `R`. -/
@[ext]
structure FormalSol (R : RelLoc E F) extends JetSec E F where
  is_sol : ∀ x, (x, f x, φ x) ∈ R

attribute [coe] FormalSol.toJetSec

instance instCoeOutFormalSolJetSec (R : RelLoc E F) : CoeOut (FormalSol R) (JetSec E F) :=
  ⟨FormalSol.toJetSec⟩

-- Note: syntactic tautology
@[simp]
theorem FormalSol.toJetSec_eq_coe {R : RelLoc E F} (𝓕 : FormalSol R) :
    𝓕.toJetSec = (𝓕 : JetSec E F) :=
  rfl

@[simp]
theorem FormalSol.coeIsFormalSol {R : RelLoc E F} (𝓕 : FormalSol R) :
    (𝓕 : JetSec E F).IsFormalSol R :=
  𝓕.is_sol

/-- Bundling a formal solution from a 1-jet section that is a formal solution. -/
def _root_.JetSec.IsFormalSol.formalSol {𝓕 : JetSec E F} {R : RelLoc E F} (h : 𝓕.IsFormalSol R) :
    FormalSol R :=
  { 𝓕 with is_sol := h }

instance instFunLikeFormalSolProdContinuousLinearMapRealId (R : RelLoc E F) : FunLike (FormalSol R) E (F × (E →L[ℝ] F)) :=
  ⟨fun 𝓕 x ↦ (𝓕.f x, 𝓕.φ x),
  by
     intros 𝓕 𝓕' h
     ext x : 2 <;> replace h := Prod.mk_inj.mp <| congrFun h x
     exacts [h.1, h.2]⟩

@[simp]
theorem FormalSol.coe_apply {R : RelLoc E F} (𝓕 : FormalSol R) (x : E) : (𝓕 : JetSec E F) x = 𝓕 x :=
  rfl

variable {R : RelLoc E F}

/-- A family of formal solutions is a 1-parameter family of formal solutions. -/
@[ext]
structure FamilyFormalSol (R : RelLoc E F) extends FamilyJetSec E F P where
  is_sol : ∀ t x, (x, f t x, φ t x) ∈ R

/-- A homotopy of formal solutions is a 1-parameter family of formal solutions. -/
@[reducible]
def HtpyFormalSol (R : RelLoc E F) :=
  R.FamilyFormalSol ℝ

open RelLoc

end RelLoc
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_AmpleRelation
attribute [-instance] _root_.instVAddIntReal_solutions
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-! # Slices of first order relations

Recal that a first order partial differential relation for maps between real normed vector spaces
`E` and `F` is a set `R` in `OneJet E F := E × F × (E →L[ℝ] F)`. In this file we study slices
of such relations. The word slice is meant to convey the idea of intersecting with an affine
subspace. Here we fix `(x, y, φ) : OneJet E F` and some hyperplane `H` in `E`. The points
`x` and `y` are fixed and we will take a slice in `E →L[ℝ] F` by intersecting `R` with the affine
subspace of linear maps that coincide with `φ` on `H`.

It will be convenient for convex integration purposes to identify this slice with `F`. There is
no natural identification but we can build one by fixing more data that a hyperplane in `E`.
Namely we fix `p : DualPair E` (where `ker p.π` is the relevant hyperplane) and reformulate
"linear map that coincides with `φ` on `H`" as `p.update φ w` for some `w : F`.

This `slice` definition allows to define `RelLoc.isAmple`, the ampleness condition for first
order relations: a relation is ample if all its slices are ample sets.

At the end of the file we consider 1-jet sections and slices corresponding to points in their image.
-/

section


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

variable {R : RelLoc E F}

open Set

/-! ## Slices and ampleness -/


namespace RelLoc

/-- The slice of a local relation `R : RelLoc E F` for a dual pair `p` at a jet `θ` is
the set of `w` in `F` such that updating `θ` using `p` and `w` leads to a jet in `R`. -/
def slice (R : RelLoc E F) (p : DualPair E) (θ : E × F × (E →L[ℝ] F)) : Set F :=
  {w | (θ.1, θ.2.1, p.update θ.2.2 w) ∈ R}

open scoped Pointwise

end RelLoc

open RelLoc

/-! ## Slices for 1-jet sections and formal solutions. -/

namespace JetSec

/-- The slice associated to a jet section and a dual pair at some point. -/
def sliceAt (𝓕 : JetSec E F) (R : RelLoc E F) (p : DualPair E) (x : E) : Set F :=
  R.slice p (x, 𝓕.f x, 𝓕.φ x)

/-- A 1-jet section `𝓕` is short for a dual pair `p` at a point `x` if the derivative of
the function `𝓕.f` at `x` is in the convex hull of the relevant connected component of the
corresponding slice. -/
def IsShortAt (𝓕 : JetSec E F) (R : RelLoc E F) (p : DualPair E) (x : E) : Prop :=
  D 𝓕.f x p.v ∈ hull (connectedComponentIn (𝓕.sliceAt R p x) <| 𝓕.φ x p.v)

end JetSec
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Equivariant
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open Set Function FiniteDimensional Prod Int

open scoped Topology unitInterval

/-- Equivariant maps from `ℝ` to itself are functions `f : ℝ → ℝ` with `f (t + 1) = f t + 1`. -/
structure EquivariantMap where
  toFun : ℝ → ℝ
  eqv' : ∀ t, toFun (t + 1) = toFun t + 1

namespace EquivariantMap

variable (φ : EquivariantMap)

instance instCoeFunForallReal : CoeFun EquivariantMap fun _ => ℝ → ℝ :=
  ⟨EquivariantMap.toFun⟩

theorem eqv : ∀ t, φ (t + 1) = φ t + 1 :=
  φ.eqv'

theorem sub_one (t : ℝ) : φ (t - 1) = φ t - 1 := by rw [eq_sub_iff_add_eq, ← eqv, sub_add_cancel]

theorem add_coe (t : ℝ) (n : ℤ) : φ (t + n) = φ t + n := by
  refine Int.inductionOn' n 0 ?_ ?_ ?_
  · simp_rw [cast_zero, add_zero]
  · intro k _ h; simp_rw [cast_add, cast_one, ← add_assoc, eqv, h]
  · intro k _ h; simp_rw [cast_sub, cast_one, ← add_sub_assoc, sub_one, h]

theorem coe_int (n : ℤ) : φ n = φ 0 + n := by convert add_coe φ 0 n; rw [zero_add]

protected theorem one : φ 1 = φ 0 + 1 := by rw [← cast_one, φ.coe_int]

protected theorem not_bounded_above (y : ℝ) : ∃ x : ℝ, y ≤ φ x :=
  ⟨⌈y - φ 0⌉, by simp_rw [φ.coe_int, ← sub_le_iff_le_add', le_ceil]⟩

protected theorem not_bounded_below (y : ℝ) : ∃ x : ℝ, φ x ≤ y :=
  ⟨⌊y - φ 0⌋, by simp_rw [φ.coe_int, ← le_sub_iff_add_le', floor_le]⟩

protected theorem surjective (h : Continuous φ) : Surjective φ := by
  rw [← range_eq_univ, eq_univ_iff_forall]
  exact fun y =>
    mem_range_of_exists_le_of_exists_ge h (φ.not_bounded_below y) (φ.not_bounded_above y)

protected theorem fract_add_floor (t : ℝ) : φ (fract t) + ⌊t⌋ = φ t := by
  rw [← φ.add_coe, fract_add_floor]

protected theorem monotone (h : MonotoneOn φ I) : Monotone φ := fun x y hxy ↦ by
  rw [← φ.fract_add_floor x, ← φ.fract_add_floor y]
  obtain (h2 | h2) := (floor_mono hxy).eq_or_lt
  · rw [h2]
    refine add_le_add_left (h (unitInterval.fract_mem _) (unitInterval.fract_mem _) ?_) _
    simp_rw [fract, h2]
    gcongr
  · refine (add_le_add_left (h (unitInterval.fract_mem _) unitInterval.one_mem
      (fract_lt_one _).le) _).trans
      (le_trans ?_ <|
        add_le_add_left (h unitInterval.zero_mem (unitInterval.fract_mem _) (fract_nonneg _)) _)
    rw [φ.one, add_assoc, add_comm (1 : ℝ)]
    gcongr
    norm_cast

protected theorem fract_fract (t : ℝ) : fract (φ (fract t)) = fract (φ t) := by
  rw [← φ.fract_add_floor t, fract_add_intCast]

end EquivariantMap

/-- continuous equivariant reparametrization that is locally constant around `0`.
  It is piecewise linear, connecting `(0, 0)`, `(1/4, 0)` and `(3/4, 1)` and `(1, 1)`,
  and extended to an equivariant function. -/
def linearReparam : EquivariantMap :=
  ⟨fun t => t + 4⁻¹ - abs (fract (t - 4⁻¹) - 2⁻¹), fun t => by
    simp only [← sub_add_eq_add_sub t, fract_add_one] <;> ring⟩

theorem linearReparam_eq_zero {t : ℝ} (h1 : -4⁻¹ ≤ t) (h2 : t ≤ 4⁻¹) : linearReparam t = 0 := by
  rcases h2.eq_or_lt with (rfl | h2)
  · rw [linearReparam]; norm_num
  have : ⌊t - 4⁻¹⌋ = -1 :=
    floor_eq_iff.mpr ⟨le_sub_iff_add_le.mpr <| le_trans (by norm_num) h1,
      sub_lt_iff_lt_add.mpr <| h2.trans_le (by norm_num)⟩
  have : (⌊t - 4⁻¹⌋ : ℝ) = -1 := by exact_mod_cast this
  simp_rw [linearReparam, fract, this, sub_eq_zero]
  refine (abs_eq_self.mpr <| ?_).symm.trans (by ring_nf)
  rwa [← sub_le_iff_le_add, zero_sub]

theorem linearReparam_eq_zero' {t : ℝ} (h1 : 0 ≤ t) (h2 : t ≤ 4⁻¹) : linearReparam t = 0 :=
  linearReparam_eq_zero (le_trans (by norm_num) h1) h2

@[simp]
theorem linearReparam_zero : linearReparam 0 = 0 :=
  linearReparam_eq_zero' le_rfl <| by norm_num1

theorem linearReparam_eq_one {t : ℝ} (h1 : 3 / 4 ≤ t) (h2 : t ≤ 5 / 4) : linearReparam t = 1 := by
  rw [← eq_sub_iff_add_eq.mp (linearReparam.sub_one t), ← eq_sub_iff_add_eq, sub_self]
  apply linearReparam_eq_zero
  · rw [le_sub_iff_add_le]; exact le_trans (by norm_num1) h1
  · rw [sub_le_iff_le_add]; exact h2.trans (by norm_num1)

theorem linearReparam_eq_one' {t : ℝ} (h1 : 3 / 4 ≤ t) (h2 : t ≤ 1) : linearReparam t = 1 :=
  linearReparam_eq_one h1 (h2.trans <| by norm_num)

@[simp]
theorem linearReparam_one : linearReparam 1 = 1 :=
  linearReparam_eq_one' (by norm_num1) le_rfl

theorem linearReparam_monotone : Monotone linearReparam := by
  have : ∀ x ∈ Icc (4 : ℝ)⁻¹ (3 / 4), linearReparam x = 2 * x - 2⁻¹ := fun x hx ↦ by
    have : ⌊x - 4⁻¹⌋ = 0 :=
      floor_eq_iff.mpr ⟨le_sub_iff_add_le.mpr <| le_trans (by norm_num) hx.1,
        sub_lt_iff_lt_add.mpr <| hx.2.trans_lt (by norm_num)⟩
    have : (⌊x - 4⁻¹⌋ : ℝ) = 0 := by exact_mod_cast this
    simp_rw [linearReparam, fract, this, sub_zero, sub_sub,
      show (4 : ℝ)⁻¹ + 2⁻¹ = 3 / 4 by norm_num, abs_eq_neg_self.mpr (sub_nonpos.mpr hx.2)]
    norm_num <;> linarith
  have : MonotoneOn linearReparam (Icc 4⁻¹ (3 / 4)) := fun x hx y hy hxy ↦ by
    rw [this x hx, this y hy]
    gcongr
  have : MonotoneOn linearReparam (Icc 4⁻¹ 1) := fun x hx y hy hxy ↦ by
    obtain (h1y | h1y) := le_total y (3 / 4)
    · exact this ⟨hx.1, hxy.trans h1y⟩ ⟨hy.1, h1y⟩ hxy
    rw [linearReparam_eq_one' h1y hy.2]
    obtain (h1x | h1x) := le_total x (3 / 4)
    · rw [← linearReparam_eq_one le_rfl (by norm_num)]
      exact this ⟨hx.1, h1x⟩ ⟨by norm_num, le_rfl⟩ h1x
    rw [linearReparam_eq_one' h1x hx.2]
  have : MonotoneOn linearReparam I := by
    intro x hx y hy hxy
    obtain (h1x | h1x) := le_total x 4⁻¹
    · rw [linearReparam_eq_zero' hx.1 h1x]
      obtain (h1y | h1y) := le_total y 4⁻¹
      · rw [linearReparam_eq_zero' hy.1 h1y]
      rw [← linearReparam_eq_zero (by norm_num) le_rfl]
      exact this ⟨le_rfl, by norm_num⟩ ⟨h1y, hy.2⟩ h1y
    exact this ⟨h1x, hx.2⟩ ⟨h1x.trans hxy, hy.2⟩ hxy
  exact linearReparam.monotone this

theorem linearReparam_nonpos {t : ℝ} (ht : t ≤ 4⁻¹) : linearReparam t ≤ 0 :=
  (linearReparam_monotone ht).trans_eq (linearReparam_eq_zero (by norm_num1) le_rfl)

theorem linearReparam_nonneg {t : ℝ} (ht : -4⁻¹ ≤ t) : 0 ≤ linearReparam t :=
  (linearReparam_eq_zero le_rfl (by norm_num1)).symm.trans_le (linearReparam_monotone ht)

theorem linearReparam_le_one {t : ℝ} (ht : t ≤ 5 / 4) : linearReparam t ≤ 1 :=
  (linearReparam_monotone ht).trans_eq (linearReparam_eq_one (by norm_num1) le_rfl)

theorem one_le_linearReparam {t : ℝ} (ht : 3 / 4 ≤ t) : 1 ≤ linearReparam t :=
  (linearReparam_eq_one le_rfl (by norm_num1)).symm.trans_le (linearReparam_monotone ht)

set_option linter.style.multiGoal false in
@[simp]
theorem linearReparam_projI {t : ℝ} : linearReparam (projI t) = projI (linearReparam t) := by
  rw [eq_comm]
  rcases le_total 0 t with (h1t | h1t)
  rcases le_total t 1 with (h2t | h2t)
  · rw [projI_eq_self.mpr ⟨h1t, h2t⟩, projI_eq_self]
    exact ⟨linearReparam_nonneg (le_trans (by norm_num1) h1t),
      linearReparam_le_one (h2t.trans (by norm_num1))⟩
  · rw [projI_eq_one.mpr h2t, linearReparam_one, projI_eq_one]
    exact one_le_linearReparam (le_trans (by norm_num1) h2t)
  · rw [projI_eq_zero.mpr h1t, linearReparam_zero, projI_eq_zero]
    exact linearReparam_nonpos (h1t.trans (by norm_num1))

@[simp]
theorem fract_linearReparam_eq_zero {t : ℝ} (h : fract t ≤ 4⁻¹ ∨ 3 / 4 ≤ fract t) :
    fract (linearReparam t) = 0 := by
  rw [← linearReparam.fract_fract]; rcases h with (h | h)
  · rw [linearReparam_eq_zero' (fract_nonneg _) h, fract_zero]
  · rw [linearReparam_eq_one' h (fract_lt_one _).le, fract_one]

/-- A bijection from `ℝ` to itself that fixes `0` and is equivariant with respect to the `ℤ`
action by translations.

Morally, these are bijections of the circle `ℝ / ℤ` to itself. -/
structure EquivariantEquiv extends ℝ ≃ ℝ where
  map_zero' : toFun 0 = 0
  eqv' : ∀ t, toFun (t + 1) = toFun t + 1

namespace EquivariantEquiv

variable (φ : EquivariantEquiv)

instance instCoeFunForallReal : CoeFun EquivariantEquiv fun _ => ℝ → ℝ :=
  ⟨fun f => f.toFun⟩

instance hasCoeToEquiv : Coe EquivariantEquiv (ℝ ≃ ℝ) :=
  ⟨toEquiv⟩

/-- Forgetting its bijective properties, an `equivariant_equiv` can be regarded as an
`equivariant_map`. -/
@[simps]
protected def equivariantMap : EquivariantMap :=
  { φ with toFun := φ }

theorem eqv : ∀ t, φ (t + 1) = φ t + 1 :=
  φ.eqv'

@[simp]
theorem map_zero : φ 0 = 0 :=
  φ.map_zero'

@[simp]
theorem map_zero'' : (⇑(φ : ℝ ≃ ℝ) : ℝ → ℝ) 0 = 0 :=
  φ.map_zero'

@[simp]
theorem map_one : φ 1 = 1 := by conv_lhs => rw [← zero_add (1 : ℝ), eqv, map_zero, zero_add]

instance instHasUncurryForallProdReal {α : Type*} : HasUncurry (α → EquivariantEquiv) (α × ℝ) ℝ :=
  ⟨fun φ p => φ p.1 p.2⟩

@[simp]
theorem coe_mk (f : ℝ ≃ ℝ) (h₀ h₁) : ⇑(⟨f, h₀, h₁⟩ : EquivariantEquiv) = f := rfl

-- Warning: making this a simp lemma creates a loop with `Equiv.toFun_as_coe` or
-- `Equiv.toFun_as_coe_apply`
theorem coe_toEquiv (e : EquivariantEquiv) : (⇑(e : ℝ ≃ ℝ) : ℝ → ℝ) = e :=
  rfl

/-- The inverse of an `equivariant_equiv` is an `equivariant_equiv`. -/
def symm (e : EquivariantEquiv) : EquivariantEquiv :=
  { (e : ℝ ≃ ℝ).symm with
    map_zero' := by
      rw [← (e : ℝ ≃ ℝ).apply_eq_iff_eq, Equiv.toFun_as_coe, Equiv.apply_symm_apply, coe_toEquiv,
        map_zero]
    eqv' := fun t => by
      let f := (e : ℝ ≃ ℝ)
      let g := (e : ℝ ≃ ℝ).symm
      change g (t + 1) = g t + 1
      calc
        g (t + 1) = g (f (g t) + 1) := by rw [(e : ℝ ≃ ℝ).apply_symm_apply]
        _ = g (f (g t + 1)) := by congr; exact (e.eqv (g t)).symm
        _ = g t + 1 := (e : ℝ ≃ ℝ).symm_apply_apply _ }

instance instEquivLikeReal : EquivLike EquivariantEquiv ℝ ℝ where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by
    rcases e₁ with ⟨f₁, hf₁⟩
    rcases e₂ with ⟨f₂, hf₂⟩
    suffices f₁ = f₂ by simpa
    ext
    change (f₁ : ℝ → ℝ)  = f₂ at h₁
    rw [h₁]

@[ext]
theorem ext {e₁ e₂ : EquivariantEquiv} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ :=
  DFunLike.ext e₁ e₂ h

@[simp]
theorem symm_symm (e : EquivariantEquiv) : e.symm.symm = e := by
  ext x
  change (e : ℝ ≃ ℝ).symm.symm x = e x
  simp only [Equiv.symm_symm]
  rfl

@[simp]
theorem apply_symm_apply (e : EquivariantEquiv) : ∀ x, e (e.symm x) = x :=
  (e : ℝ ≃ ℝ).apply_symm_apply

@[simp]
theorem symm_apply_apply (e : EquivariantEquiv) : ∀ x, e.symm (e x) = x :=
  (e : ℝ ≃ ℝ).symm_apply_apply

end EquivariantEquiv
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Analysis_Calculus
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open Set Function Filter

open scoped Topology ContDiff

section Calculus

open ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] {E₂ : Type*}
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : WithTop ℕ∞}

theorem HasFDerivAt.partial_fst {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
    (h : HasFDerivAt (uncurry φ) φ' (e₀, f₀)) :
    HasFDerivAt (fun e ↦ φ e f₀) (φ'.comp (inl 𝕜 E F)) e₀ := by
  exact h.comp e₀ <| hasFDerivAt_prodMk_left (𝕜 := 𝕜) e₀ f₀

theorem HasFDerivAt.partial_snd {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
    (h : HasFDerivAt (uncurry φ) φ' (e₀, f₀)) :
    HasFDerivAt (fun f ↦ φ e₀ f) (φ'.comp (inr 𝕜 E F)) f₀ :=
  h.comp f₀ <| hasFDerivAt_prodMk_right e₀ f₀

variable (𝕜)

/-- The first partial derivative of a binary function. -/
def partialFDerivFst {F : Type*} (φ : E → F → G) : E → F → E →L[𝕜] G := fun (e₀ : E) (f₀ : F) ↦
  fderiv 𝕜 (fun e ↦ φ e f₀) e₀

/-- The second partial derivative of a binary function. -/
def partialFDerivSnd {E : Type*} (φ : E → F → G) : E → F → F →L[𝕜] G := fun (e₀ : E) (f₀ : F) ↦
  fderiv 𝕜 (fun f ↦ φ e₀ f) f₀

@[inherit_doc] local notation "∂₁" => partialFDerivFst

@[inherit_doc] local notation "∂₂" => partialFDerivSnd

variable {𝕜}

theorem fderiv_partial_fst {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
    (h : HasFDerivAt (uncurry φ) φ' (e₀, f₀)) : ∂₁ 𝕜 φ e₀ f₀ = φ'.comp (inl 𝕜 E F) :=
  h.partial_fst.fderiv

theorem fderiv_partial_snd {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
    (h : HasFDerivAt (uncurry φ) φ' (e₀, f₀)) : ∂₂ 𝕜 φ e₀ f₀ = φ'.comp (inr 𝕜 E F) :=
  h.partial_snd.fderiv

theorem DifferentiableAt.hasFDerivAt_partial_fst {φ : E → F → G} {e₀ : E} {f₀ : F}
    (h : DifferentiableAt 𝕜 (uncurry φ) (e₀, f₀)) :
    HasFDerivAt (fun e ↦ φ e f₀) (partialFDerivFst 𝕜 φ e₀ f₀) e₀ := by
  apply (h.comp e₀ <| differentiableAt_id.prodMk <| differentiableAt_const f₀).hasFDerivAt (𝕜 := 𝕜)

theorem DifferentiableAt.hasFDerivAt_partial_snd {φ : E → F → G} {e₀ : E} {f₀ : F}
    (h : DifferentiableAt 𝕜 (uncurry φ) (e₀, f₀)) :
    HasFDerivAt (fun f ↦ φ e₀ f) (partialFDerivSnd 𝕜 φ e₀ f₀) f₀ := by
  rw [fderiv_partial_snd h.hasFDerivAt]
  exact h.hasFDerivAt.partial_snd

/-- Precomposition by a continuous linear map as a continuous linear map between spaces of
continuous linear maps. -/
def ContinuousLinearMap.compRightL (φ : E →L[𝕜] F) : (F →L[𝕜] G) →L[𝕜] E →L[𝕜] G :=
  precomp G φ

/-- The second partial derivative of `φ : E → 𝕜 → G` seen as a function from `E → 𝕜 → G` -/
def partialDerivSnd (φ : E → 𝕜 → G) : E → 𝕜 → G := fun e k ↦ ∂₂ 𝕜 φ e k 1

omit [NormedAddCommGroup E] [NormedSpace 𝕜 E] in
theorem partialFDerivSnd_eq_smulRight (φ : E → 𝕜 → G) (e : E) (k : 𝕜) :
    ∂₂ 𝕜 φ e k = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (partialDerivSnd φ e k) :=
  toSpanSingleton_deriv.symm

omit [NormedAddCommGroup E] [NormedSpace 𝕜 E] in
theorem partialFDerivSnd_one (φ : E → 𝕜 → G) (e : E) (k : 𝕜) :
    ∂₂ 𝕜 φ e k 1 = partialDerivSnd φ e k := by
  simp [partialFDerivSnd_eq_smulRight]

theorem ContDiff.contDiff_partial_fst {φ : E → F → G} {n : ℕ}
    (hF : ContDiff 𝕜 (n + 1) (uncurry φ)) : ContDiff 𝕜 n ↿(∂₁ 𝕜 φ) :=
  ContDiff.fderiv (hF.comp <| contDiff_snd.prodMk contDiff_fst.snd) contDiff_fst le_rfl

-- XXX: fix this!
theorem ContDiff.contDiff_top_partial_fst {φ : E → F → G} (hF : ContDiff 𝕜 ∞ (uncurry φ)) :
    ContDiff 𝕜 ∞ ↿(∂₁ 𝕜 φ) :=
  contDiff_infty.mpr fun n ↦ (contDiff_infty.mp hF (n + 1)).contDiff_partial_fst

theorem ContDiff.contDiff_partial_snd {φ : E → F → G} {n : ℕ}
    (hF : ContDiff 𝕜 (n + 1) (uncurry φ)) : ContDiff 𝕜 n ↿(∂₂ 𝕜 φ) :=
  ContDiff.fderiv (hF.comp <| contDiff_fst.fst.prodMk contDiff_snd) contDiff_snd le_rfl

-- FIXME: upgrade again to include analyticity
theorem ContDiff.contDiff_top_partial_snd {φ : E → F → G} (hF : ContDiff 𝕜 ∞ (uncurry φ)) :
    ContDiff 𝕜 ∞ ↿(∂₂ 𝕜 φ) :=
  contDiff_infty.mpr fun n ↦ (contDiff_infty.mp (hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (n + 1)).contDiff_partial_snd

end Calculus

section RealCalculus -- PRed in #12673

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem ContDiff.lipschitzOnWith {s : Set E} {f : E → F} {n} (hf : ContDiff ℝ n f) (hn : 1 ≤ n)
    (hs : Convex ℝ s) (hs' : IsCompact s) : ∃ K, LipschitzOnWith K f s := by
  obtain ⟨M, M_nonneg, hM⟩ := (bddAbove_iff_exists_ge (0 : ℝ)).mp
    (hs'.image (hf.continuous_fderiv (by positivity)).norm).bddAbove
  simp_rw [forall_mem_image] at hM
  use ⟨M, M_nonneg⟩
  exact Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ ↦ hf.differentiable (by positivity) x) hM hs

end RealCalculus

open Filter
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_MeasureTheory_ParametricIntervalIntegral
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

open TopologicalSpace MeasureTheory Filter FirstCountableTopology Metric Set Function
open scoped Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-!
We could weaken `FiniteDimensional ℝ H` with `SecondCountable (H →L[ℝ] E)` if needed,
but that is less convenient to work with.
-/

open Real ContinuousLinearMap Asymptotics Interval

/-- This statement is a new version using the continuity note in mathlib.
See commit `39e3f3f` for an older version
Maybe todo: let `a` depend on `x`.
-/
theorem hasFDerivAt_parametric_primitive_of_lip' (F : H → ℝ → E) (F' : ℝ → H →L[ℝ] E) {x₀ : H}
    {G' : H →L[ℝ] E} {bound : ℝ → ℝ} {s : H → ℝ} {ε : ℝ} (ε_pos : 0 < ε) {a a₀ b₀ : ℝ}
    {s' : H →L[ℝ] ℝ} (ha : a ∈ Ioo a₀ b₀) (hsx₀ : s x₀ ∈ Ioo a₀ b₀)
    (hF_meas : ∀ x ∈ ball x₀ ε, AEStronglyMeasurable (F x) (volume.restrict (Ioo a₀ b₀)))
    (hF_int : IntegrableOn (F x₀) (Ioo a₀ b₀)) (hF_cont : ContinuousAt (F x₀) (s x₀))
    (hF'_meas : AEStronglyMeasurable F' (volume.restrict <| Ι a (s x₀)))
    (h_lipsch :
      ∀ᵐ t ∂volume.restrict <| Ioo a₀ b₀,
        LipschitzOnWith (nnabs <| bound t) (fun x ↦ F x t) (ball x₀ ε))
    (bound_integrable : IntegrableOn bound (Ioo a₀ b₀)) (bound_cont : ContinuousAt bound (s x₀))
    (bound_nonneg : ∀ t, 0 ≤ bound t)
    -- this is not really needed, but much more convenient
    (h_diff : ∀ᵐ a ∂volume.restrict (Ι a (s x₀)), HasFDerivAt (fun x ↦ F x a) (F' a) x₀)
    (s_diff : HasFDerivAt s s' x₀)
    (hG' : (∫ t in a..s x₀, F' t) + (toSpanSingleton ℝ (F x₀ (s x₀))).comp s' = G') :
    IntervalIntegrable F' volume a (s x₀) ∧
      HasFDerivAt (fun x : H ↦ ∫ t in a..s x, F x t) G' x₀ := by
  subst hG'
  let φ : H → ℝ → E := fun x t ↦ ∫ s in a..t, F x s
  have Ioo_nhds : Ioo a₀ b₀ ∈ 𝓝 (s x₀) := Ioo_mem_nhds hsx₀.1 hsx₀.2
  have bound_int : ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ →
      IntervalIntegrable bound volume s u := fun hs hu ↦
    (bound_integrable.mono_set <| ordConnected_Ioo.uIcc_subset hs hu).intervalIntegrable
  have mem_nhds : ball x₀ ε ∩ s ⁻¹' Ioo a₀ b₀ ∈ 𝓝 x₀ :=
    Filter.inter_mem (ball_mem_nhds x₀ ε_pos) (s_diff.continuousAt.preimage_mem_nhds Ioo_nhds)
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have hF_meas_ball : ∀ {x}, x ∈ ball x₀ ε → ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ →
      AEStronglyMeasurable (F x) (volume.restrict <| Ι s u) := fun hx s u hs hu ↦
    (hF_meas _ hx).mono_set (ordConnected_Ioo.uIoc_subset hs hu)
  have hF_int_ball : ∀ x ∈ ball x₀ ε, ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ →
      IntervalIntegrable (F x) volume s u := fun x hx s u hs hu ↦ by
    have : IntegrableOn (F x) (Ioo a₀ b₀) := by
      apply integrable_of_norm_sub_le (hF_meas x hx) hF_int (bound_integrable.mul_const ‖x - x₀‖)
      apply h_lipsch.mono
      intro t ht
      rw [norm_sub_rev]
      rw [lipschitzOnWith_iff_norm_sub_le] at ht
      simpa [bound_nonneg t] using ht hx x₀_in
    exact (this.mono_set <| ordConnected_Ioo.uIcc_subset hs hu).intervalIntegrable
  constructor
  · apply (bound_int ha hsx₀).mono_fun' hF'_meas _
    replace h_lipsch : ∀ᵐ t ∂volume.restrict (Ι a (s x₀)),
        LipschitzOnWith (nnabs (bound t)) (fun x : H ↦ F x t) (ball x₀ ε) :=
      ae_restrict_of_ae_restrict_of_subset (ordConnected_Ioo.uIoc_subset ha hsx₀) h_lipsch
    filter_upwards [h_lipsch, h_diff]
    intro t ht_lip ht_diff
    rw [show bound t = nnabs (bound t) by simp [bound_nonneg t] ]
    exact ht_diff.le_of_lipschitzOn (ball_mem_nhds x₀ ε_pos) ht_lip
  · have D₁ : HasFDerivAt (fun x ↦ φ x (s x₀)) (∫ t in a..s x₀, F' t) x₀ := by
      replace hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (volume.restrict (Ι a (s x₀))) :=
        Eventually.mono (ball_mem_nhds x₀ ε_pos) fun x hx ↦ hF_meas_ball hx ha hsx₀
      replace hF_int : IntervalIntegrable (F x₀) volume a (s x₀) := hF_int_ball x₀ x₀_in ha hsx₀
      exact (hasFDerivAt_integral_of_dominated_loc_of_lip_interval (ball_mem_nhds x₀ ε_pos)
        hF_meas hF_int hF'_meas
        (ae_restrict_of_ae_restrict_of_subset (ordConnected_Ioo.uIoc_subset ha hsx₀) h_lipsch)
        (bound_int ha hsx₀) h_diff).2
    have D₂ : HasFDerivAt (fun x ↦ φ x₀ (s x)) ((toSpanSingleton ℝ (F x₀ (s x₀))).comp s') x₀ := by
      suffices HasFDerivAt (φ x₀) (toSpanSingleton ℝ (F x₀ (s x₀))) (s x₀) from this.comp _ s_diff
      rw [hasFDerivAt_iff_hasDerivAt, toSpanSingleton_apply, one_smul]
      exact intervalIntegral.integral_hasDerivAt_right (hF_int_ball x₀ x₀_in ha hsx₀)
        ⟨Ioo a₀ b₀, Ioo_nhds, hF_meas x₀ x₀_in⟩ hF_cont
    have D₃ : HasFDerivAt (𝕜 := ℝ) (fun x ↦ ∫ t in s x₀..s x, F x t - F x₀ t) 0 x₀ := by
      refine IsBigO.hasFDerivAt (𝕜 := ℝ) ?_ one_lt_two
      have O₁ : (fun x ↦ ∫ s in s x₀..s x, bound s) =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ := by
        have : (fun x ↦ s x - s x₀) =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ := s_diff.isBigO_sub.norm_right
        refine IsBigO.trans ?_ this
        change ((fun t ↦ ∫ s in s x₀..t, bound s) ∘ s) =O[𝓝 x₀] ((fun t ↦ t - s x₀) ∘ s)
        refine IsBigO.comp_tendsto ?_ s_diff.continuousAt
        have M : StronglyMeasurableAtFilter bound (𝓝 (s x₀)) volume :=
          ⟨Ioo a₀ b₀, Ioo_nhds, bound_integrable.1⟩
        refine (intervalIntegral.integral_hasDerivAt_right (bound_int ha hsx₀)
          M bound_cont).hasFDerivAt.isBigO_sub.congr' ?_ EventuallyEq.rfl
        filter_upwards [Ioo_nhds]
        rintro t ht
        rw [intervalIntegral.integral_interval_sub_left (bound_int ha ht) (bound_int ha hsx₀)]
      have O₂ : (fun x ↦ ‖x - x₀‖) =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ := isBigO_refl _ _
      have O₃ : (fun x ↦ ∫ t : ℝ in s x₀..s x, F x t - F x₀ t) =O[𝓝 x₀] fun x ↦
          (∫ t' in s x₀..s x, bound t') * ‖x - x₀‖ := by
        have bdd : ∀ᶠ x in 𝓝 x₀,
            ‖∫ s in s x₀..s x, F x s - F x₀ s‖ ≤ |∫ s in s x₀..s x, bound s| * ‖x - x₀‖ := by
          filter_upwards [mem_nhds]
          rintro x ⟨hx : x ∈ ball x₀ ε, hsx : s x ∈ Ioo a₀ b₀⟩
          rw [← abs_of_nonneg (norm_nonneg <| x - x₀), ← abs_mul, ←
            intervalIntegral.integral_mul_const]
          apply intervalIntegral.norm_integral_le_abs_of_norm_le _
            ((bound_int hsx₀ hsx).mul_const _)
          apply ae_restrict_of_ae_restrict_of_subset (ordConnected_Ioo.uIoc_subset hsx₀ hsx)
          apply h_lipsch.mono
          intro t ht
          rw [lipschitzOnWith_iff_norm_sub_le] at ht
          simp only [coe_nnabs] at ht
          rw [← abs_of_nonneg (bound_nonneg t)]
          exact ht hx (mem_ball_self ε_pos)
        rw [← isBigO_norm_right]
        simp only [norm_eq_abs, abs_mul, abs_norm]
        exact bdd.isBigO
      simp_rw [pow_two]
      exact O₃.trans (O₁.mul O₂)
    have : ∀ᶠ x in 𝓝 x₀,
        ∫ t in a..s x, F x t =
          (φ x (s x₀) + φ x₀ (s x) + ∫ t in s x₀..s x, F x t - F x₀ t) - φ x₀ (s x₀) := by
      filter_upwards [mem_nhds]
      rintro x ⟨hx : x ∈ ball x₀ ε, hsx : s x ∈ Ioo a₀ b₀⟩
      have int₁ : IntervalIntegrable (F x₀) volume a (s x₀) := hF_int_ball x₀ x₀_in ha hsx₀
      have int₂ : IntervalIntegrable (F x₀) volume (s x₀) (s x) := hF_int_ball x₀ x₀_in hsx₀ hsx
      have int₃ : IntervalIntegrable (F x) volume a (s x₀) := hF_int_ball x hx ha hsx₀
      have int₄ : IntervalIntegrable (F x) volume (s x₀) (s x) := hF_int_ball x hx hsx₀ hsx
      dsimp [φ]
      rw [intervalIntegral.integral_sub int₄ int₂, add_sub, add_right_comm, sub_sub,
        intervalIntegral.integral_add_adjacent_intervals int₃ int₄,
        ← intervalIntegral.integral_add_adjacent_intervals int₁ int₂]
      abel
    apply HasFDerivAt.congr_of_eventuallyEq _ this
    simpa [Pi.sub_def] using ((D₁.add D₂).add D₃).sub (hasFDerivAt_const (φ x₀ (s x₀)) x₀)

variable [FiniteDimensional ℝ H]

theorem hasFDerivAt_parametric_primitive_of_contDiff' {F : H → ℝ → E} (hF : ContDiff ℝ 1 ↿F)
    {s : H → ℝ} (hs : ContDiff ℝ 1 s) (x₀ : H) (a : ℝ) :
    (IntervalIntegrable (fun t ↦ fderiv ℝ (fun x ↦ F x t) x₀) volume a <| s x₀) ∧
      HasFDerivAt (fun x : H ↦ ∫ t in a..s x, F x t)
        ((∫ t in a..s x₀, fderiv ℝ (fun x ↦ F x t) x₀) + (ContinuousLinearMap.toSpanSingleton ℝ (F x₀ (s x₀))).comp (fderiv ℝ s x₀)) x₀ := by
  set a₀ := min a (s x₀) - 1
  set b₀ := max a (s x₀) + 1
  have ha : a ∈ Ioo a₀ b₀ := by
    dsimp [a₀, b₀]
    constructor
    · linarith [min_le_left a (s x₀)]
    · linarith [le_max_left a (s x₀)]
  have ht₀ : s x₀ ∈ Ioo a₀ b₀ := by
    dsimp [a₀, b₀]
    constructor
    · linarith [min_le_right a (s x₀)]
    · linarith [le_max_right a (s x₀)]
  have cpct : IsCompact (closedBall x₀ 1 ×ˢ Icc a₀ b₀) :=
    (ProperSpace.isCompact_closedBall x₀ 1).prod isCompact_Icc
  obtain ⟨K, F_lip⟩ : ∃ K, ∀ t ∈ Ioo a₀ b₀, LipschitzOnWith K (fun x ↦ F x t) (ball x₀ 1) := by
    have conv : Convex ℝ (closedBall x₀ 1 ×ˢ Icc a₀ b₀) :=
      (convex_closedBall x₀ 1).prod (convex_Icc a₀ b₀)
    rcases hF.lipschitzOnWith le_rfl conv cpct with ⟨K, hK⟩
    use K
    intro t t_in
    rw [show (fun x : H ↦ F x t) = uncurry F ∘ fun x : H ↦ (x, t) by ext; simp, ← mul_one K]
    apply hK.comp (LipschitzWith.prodMk_right t).lipschitzOnWith
    rw [mapsTo_iff_image_subset]
    rintro ⟨x, s⟩ ⟨x', hx, h⟩; cases h
    exact ⟨ball_subset_closedBall hx, mem_Icc_of_Ioo t_in⟩
  have cont_x (x) : Continuous (F x) := hF.continuous.comp (Continuous.prodMk_right x)
  have int_Icc (x) : IntegrableOn (F x) (Icc a₀ b₀) := (cont_x x).continuousOn.integrableOn_Icc
  have int_Ioo (x) : IntegrableOn (F x) (Ioo a₀ b₀) := (int_Icc x).mono_set Ioo_subset_Icc_self
  apply
    hasFDerivAt_parametric_primitive_of_lip' _ _ zero_lt_one ha ht₀
      (fun x _hx ↦ (cont_x x).aestronglyMeasurable) (int_Ioo x₀) (cont_x x₀).continuousAt _ _ _
      (continuousAt_const : (ContinuousAt fun _ : ℝ ↦ (K : ℝ)) <| s x₀) fun _t ↦
      NNReal.coe_nonneg K
  · apply ae_of_all
    intro t
    apply (ContDiff.hasStrictFDerivAt _ one_ne_zero).hasFDerivAt
    rw [show (fun x ↦ F x t) = uncurry F ∘ fun x ↦ (x, t) by ext; simp]
    exact hF.comp ((contDiff_prodMk_left t).of_le le_top)
  · exact (ContDiff.hasStrictFDerivAt hs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  · rfl
  · apply Continuous.aestronglyMeasurable
    have :
      (fun t ↦ fderiv ℝ (fun x : H ↦ F x t) x₀) =
        (fun φ : H × ℝ →L[ℝ] E ↦ φ.comp (inl ℝ H ℝ)) ∘
          (fderiv ℝ <| uncurry F) ∘ fun t ↦ (x₀, t) := by
      ext t
      have : HasFDerivAt (fun e ↦ F e t) ((fderiv ℝ (uncurry F) (x₀, t)).comp (inl ℝ H ℝ)) x₀ :=
        (hF.hasStrictFDerivAt (by norm_num)).hasFDerivAt.comp _ (hasFDerivAt_prodMk_left _ _)
      rw [this.fderiv]
      rfl
    rw [this]
    exact (inl ℝ H ℝ).compRightL.continuous.comp
      ((hF.continuous_fderiv (by norm_num)).comp <| Continuous.prodMk_right x₀)
  · simp_rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with t t_in
    rw [nnabs_coe K]
    exact F_lip t t_in
  · exact integrableOn_const measure_Ioo_lt_top.ne

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

open Real ContinuousLinearMap Asymptotics

theorem contDiff_parametric_primitive_of_contDiff' {F : H → ℝ → E} {n : ℕ} (hF : ContDiff ℝ n ↿F)
    {s : H → ℝ} (hs : ContDiff ℝ n s) (a : ℝ) : ContDiff ℝ n fun x : H ↦ ∫ t in a..s x, F x t := by
  induction n generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero] at *
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF hs
  | succ n ih =>
    have hF₁ : ContDiff ℝ 1 ↿F := hF.one_of_succ (n := n)
    have hs₁ : ContDiff ℝ 1 s := hs.one_of_succ (n := n)
    have h :
      ∀ x,
        HasFDerivAt (fun x ↦ ∫ t in a..s x, F x t)
          ((∫ t in a..s x, fderiv ℝ (fun x' ↦ F x' t) x) + (ContinuousLinearMap.toSpanSingleton ℝ (F x (s x))).comp (fderiv ℝ s x)) x :=
      fun x ↦ (hasFDerivAt_parametric_primitive_of_contDiff' hF₁ hs₁ x a).2
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = n + 1 by rfl] at hs ⊢
    rw [contDiff_succ_iff_fderiv_apply]
    constructor
    · exact fun x₀ ↦ ⟨_, h x₀⟩
    · simp only [WithTop.natCast_ne_top, IsEmpty.forall_iff, true_and]
      intro x
      rw [fderiv_eq h]
      apply ContDiff.add
      · simp only [ContinuousLinearMap.coe_coe]
        have hD' : ContDiff ℝ n ↿fun x₀ t ↦ fderiv ℝ (fun x ↦ F x t) x₀ :=
          ContDiff.fderiv (hF.comp₂ contDiff_snd contDiff_fst.snd) contDiff_fst le_rfl
        have hD : ContDiff ℝ n ↿fun x' a ↦ (fderiv ℝ (fun e ↦ F e a) x') x :=
          hD'.clm_apply contDiff_const
        convert ih hD hs.of_succ with x'
        refine ContinuousLinearMap.intervalIntegral_apply ?_ x
        exact (continuous_curry x' hD'.continuous).intervalIntegrable _ _
      · exact ((contDiff_succ_iff_fderiv.mp hs).2.2.smulRight
          (hF.of_succ.comp <| contDiff_id.prodMk hs.of_succ)).clm_apply contDiff_const

end

section

universe v u

variable {E : Type u}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Type v}
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

-- Should we directly prove the version below?
set_option backward.isDefEq.respectTransparency false in
theorem contDiff_parametric_primitive_of_contDiff {F : H → ℝ → E} {n : ℕ∞} (hF : ContDiff ℝ n ↿F)
    {s : H → ℝ} (hs : ContDiff ℝ n s) (a : ℝ) : ContDiff ℝ n fun x : H ↦ ∫ t in a..s x, F x t := by
  induction n using WithTop.recTopCoe
  · rw [contDiff_infty] at *
    exact fun n ↦ contDiff_parametric_primitive_of_contDiff' (hF n) (hs n) a
  · exact contDiff_parametric_primitive_of_contDiff' hF hs a

theorem contDiff_parametric_primitive_of_contDiff'' {F : H → ℝ → E} {n : ℕ∞} (hF : ContDiff ℝ n ↿F)
    (a : ℝ) : ContDiff ℝ n fun x : H × ℝ ↦ ∫ t in a..x.2, F x.1 t :=
  have cd : ContDiff ℝ n ↿fun (x : H × ℝ) (t : ℝ) ↦ F x.1 t :=
    hF.comp (contDiff_fst.prodMap contDiff_id)
  contDiff_parametric_primitive_of_contDiff cd contDiff_snd a

theorem contDiff_parametric_integral_of_contDiff {F : H → ℝ → E} {n : ℕ∞} (hF : ContDiff ℝ n ↿F)
    (a b : ℝ) : ContDiff ℝ n fun x : H ↦ ∫ t in a..b, F x t :=
  contDiff_parametric_primitive_of_contDiff hF contDiff_const a

end
end
end

section
-- module Solutions.OAIQ249_SI.Loops_Basic
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Basic definitions and properties of loops
-/

section

open Set Function FiniteDimensional Int TopologicalSpace

open scoped Topology unitInterval

noncomputable section

variable {K X X' Y Z : Type*}

-- variable [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-! ## Definition and periodicity lemmas -/


variable (X)

/-- A loop is a function with domain `ℝ` and is periodic with period 1. -/
structure Loop where
  toFun : ℝ → X
  per' : ∀ t, toFun (t + 1) = toFun t

attribute [coe] Loop.toFun

instance instCoeFunLoopForallReal : CoeFun (Loop X) fun _ ↦ ℝ → X :=
  ⟨fun γ ↦ γ.toFun⟩

initialize_simps_projections Loop (toFun → apply)

/-- Any function `φ : α → loop X` can be seen as a function `α × ℝ → X`. -/
instance hasUncurryLoop {α : Type*} : HasUncurry (α → Loop X) (α × ℝ) X :=
  ⟨fun φ p ↦ φ p.1 p.2⟩

variable {X}

namespace Loop

@[ext]
protected theorem ext : ∀ {γ₁ γ₂ : Loop X}, (γ₁ : ℝ → X) = γ₂ → γ₁ = γ₂
  | ⟨_x, _h1⟩, ⟨.(_x), _h2⟩, rfl => rfl

/-- The constant loop. -/
@[simps]
def const (f : X) : Loop X :=
  ⟨fun _ ↦ f, fun _ ↦ rfl⟩

instance Zero [Zero X] : Zero (Loop X) :=
  ⟨const 0⟩

@[simp]
theorem zero_fun [_root_.Zero X] : ((0 : Loop X) : ℝ → X) = (0 : ℝ → X) :=
  rfl

-- unused
@[simp]
theorem const_zero [_root_.Zero X] : const (0 : X) = (0 : Loop X) :=
  rfl

instance instInhabited [Inhabited X] : Inhabited (Loop X) :=
  ⟨Loop.const default⟩

/-- Periodicity of loops restated in terms of the function coercion. -/
theorem per (γ : Loop X) : ∀ t, γ (t + 1) = γ t :=
  Loop.per' γ

theorem periodic (γ : Loop X) : Function.Periodic γ 1 :=
  Loop.per' γ

protected theorem one (γ : Loop X) : γ 1 = γ 0 := by convert γ.per 0; rw [zero_add]

theorem add_int_eq (γ : Loop X) (t : ℝ) (n : ℤ) : γ (t + n) = γ t := by
  induction n using Int.induction_on with
  | zero => norm_cast; rw [add_zero]
  | succ n hn => rw [← hn, Int.cast_add, ← add_assoc, Int.cast_one, γ.per]
  | pred n hn => rw [← hn, Int.cast_sub, add_sub, Int.cast_one, ← γ.per, sub_add_cancel]

theorem fract_eq (γ : Loop X) : ∀ t, γ (fract t) = γ t := by
  intro t
  unfold fract
  rw [sub_eq_add_neg, ← Int.cast_neg]
  exact γ.add_int_eq ..

theorem range_eq_image (γ : Loop X) : range γ = γ '' I := by
  apply eq_of_subset_of_subset
  · rw [range_subset_iff]
    exact fun y ↦ ⟨fract y, unitInterval.fract_mem y, γ.fract_eq _⟩
  · rintro y ⟨x, -, hxy⟩
    exact ⟨x, hxy⟩

/-- Transforming a loop by applying function `f`. -/
@[simps]
def transform (γ : Loop X) (f : X → X') : Loop X' :=
  ⟨fun t ↦ f (γ t), fun t ↦ by rw [γ.per]⟩

/-- Adding two loops pointwise. -/
@[simps]
instance Add [Add X] : Add (Loop X) :=
  ⟨fun γ₁ γ₂ ↦ ⟨fun t ↦ γ₁ t + γ₂ t, fun t ↦ by simp_rw [Loop.per]⟩⟩

@[simps]
instance Neg [Neg X] : Neg (Loop X) :=
  ⟨fun γ ↦ ⟨fun t ↦ -γ t, fun t ↦ by simp_rw [Loop.per]⟩⟩

instance instAddCommGroup [AddCommGroup X] : AddCommGroup (Loop X) :=
  { Loop.Add, Loop.Zero, Loop.Neg with
    add_assoc := fun γ₁ γ₂ γ₃ ↦ by ext t; apply add_assoc
    add_comm := fun γ₁ γ₂ ↦ by ext t; apply add_comm
    zero_add := fun γ ↦ by ext t; apply zero_add
    add_zero := fun γ ↦ by ext t; apply add_zero
    neg_add_cancel := fun γ ↦ by ext t; apply neg_add_cancel
    nsmul := nsmulRec
    zsmul := zsmulRec }

/-- Shifting a loop, or equivalently, adding a constant value to a loop. -/
instance instVAddOfAdd [_root_.Add X] : VAdd X (Loop X) :=
  ⟨fun x γ ↦ γ.transform fun y ↦ x + y⟩

@[simp]
theorem vadd_apply [_root_.Add X] {x : X} {γ : Loop X} {t : ℝ} : (x +ᵥ γ) t = x + γ t :=
  rfl

/-- Multiplying a loop by a scalar value. -/
instance instSMul [SMul K X] : SMul K (Loop X) :=
  ⟨fun k γ ↦ γ.transform fun y ↦ k • y⟩

instance instModule [Semiring K] [AddCommGroup X] [Module K X] : Module K (Loop X) where
  one_smul γ := by ext t; apply one_smul
  mul_smul k₁ k₂ γ := by ext t; apply mul_smul
  smul_zero k := by ext; apply smul_zero
  smul_add k γ₁ γ₂ := by ext t; apply smul_add
  add_smul k₁ k₂ γ := by ext t; apply add_smul
  zero_smul γ := by ext t; apply zero_smul

@[simp]
theorem smul_apply [SMul K X] {k : K} {γ : Loop X} {t : ℝ} : (k • γ) t = k • γ t :=
  rfl

/-- Reparametrizing loop `γ` using an equivariant map `φ`. -/
@[simps +simpRhs]
def reparam {F : Type*} (γ : Loop F) (φ : EquivariantMap) : Loop F where
  toFun := γ ∘ φ
  per' t := by rw [comp_apply, φ.eqv, γ.per]; rfl

/-! ## Support of a loop family -/


/-- A loop is constant if it takes the same value at every time.
See also `Loop.isConst_iff_forall_avg` and `Loop.isConst_iff_const_avg` for characterizations in
terms of average values. -/
def IsConst (γ : Loop X) :=
  ∀ t s, γ t = γ s

variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The support of a loop family is the closure of the set of parameters where
the loop is not constant. -/
def support (γ : X → Loop X') : Set X :=
  closure {x | ¬(γ x).IsConst}

/-! ## From paths to loops -/


/-- Turn a path into a loop. -/
@[simps]
noncomputable def ofPath {x : X} (γ : Path x x) : Loop X where
  toFun t := γ.extend (fract t)
  per' t := by rw [fract_add_one]

@[simp]
theorem range_ofPath {x : X} (γ : Path x x) : range (ofPath γ) = range γ := by
  rw [Loop.range_eq_image, ofPath, image_eq_range]
  apply congrArg
  ext t
  by_cases ht1 : t.val = 1
  · have : t = ⟨1, right_mem_Icc.mpr zero_le_one⟩ := Subtype.ext ht1
    rw [this]
    norm_cast
    simp only [fract, floor_one, Path.extend_zero, Int.cast_one, sub_self]
    exact γ.target.symm
  · change (t : ℝ) ≠ 1 at ht1
    have : fract ↑t = t.val := by
      rw [fract_eq_iff]
      refine ⟨t.2.1, t.2.2.lt_of_ne ht1, ⟨0, ?_⟩⟩
      rw [Int.cast_zero, sub_self]
    simp only [this, γ.extend_apply t.2]

/-- `Loop.ofPath` is continuous, general version. -/
@[fun_prop]
theorem _root_.Continuous.ofPath (x : X → Y) (t : X → ℝ) (γ : ∀ i, Path (x i) (x i))
    (hγ : Continuous ↿γ) (ht : Continuous t) : Continuous fun i ↦ ofPath (γ i) (t i) := by
  change Continuous fun i ↦ (fun s ↦ (γ s).extend) i (fract (t i))
  refine ContinuousOn.comp_fract ?_ ht ?_
  · have : Continuous (fun x : X × ℝ ↦ (x.1, projIcc 0 1 zero_le_one x.2)) :=
      continuous_id.prodMap continuous_projIcc
    exact (hγ.comp this).continuousOn
  · simp only [Icc.mk_zero, zero_le_one, Path.target, Path.extend_apply, imp_true_iff,
      Path.source, right_mem_Icc, left_mem_Icc, Icc.mk_one]

/-- `Loop.ofPath` is continuous, where the endpoints of `γ` are fixed. TODO: remove -/
@[fun_prop]
theorem ofPath_continuous_family {x : Y} (γ : X → Path x x) (h : Continuous ↿γ) :
    Continuous ↿fun s ↦ ofPath <| γ s :=
  Continuous.ofPath _ _ (fun i : X × ℝ ↦ γ i.1) (h.comp <| continuous_fst.prodMap continuous_id)
    continuous_snd

/-! ## Round trips -/


/-- The round-trip defined by `γ` is `γ` followed by `γ⁻¹`. -/
def roundTrip {x y : X} (γ : Path x y) : Loop X :=
  ofPath (γ.trans γ.symm)

theorem roundTrip_range {x y : X} {γ : Path x y} : range (roundTrip γ) = range γ := by
  simp [roundTrip, range_ofPath, Path.trans_range, Path.symm_range]

theorem roundTrip_based_at {x y : X} {γ : Path x y} : roundTrip γ 0 = x := by
  simp [roundTrip, ofPath, fract_zero]

theorem roundTrip_eq {x y x' y' : X} {γ : Path x y} {γ' : Path x' y'} (h : ∀ s, γ s = γ' s) :
    roundTrip γ = roundTrip γ' := by
  obtain rfl : x = x' := γ.source.symm.trans ((h 0).trans γ'.source)
  obtain rfl : y = y' := γ.target.symm.trans ((h 1).trans γ'.target)
  obtain rfl : γ = γ' := by ext; apply h
  rfl

/-- The round trip loop family associated to a path `γ`. For each parameter `t`,
the loop `roundTripFamily γ t` backtracks at `γ t`. -/
noncomputable def roundTripFamily {x y : X} (γ : Path x y) : ℝ → Loop X :=
  have key : ∀ {t}, x = γ.extend (min 0 t) := (γ.extend_of_le_zero <| min_le_left _ _).symm
  fun t ↦ roundTrip ((γ.truncate 0 t).cast key rfl)

attribute [fun_prop] Path.trans_continuous_family

@[fun_prop]
theorem roundTripFamily_continuous {x y : X} {γ : Path x y} : Continuous ↿(roundTripFamily γ) :=
  ofPath_continuous_family _
    (Path.trans_continuous_family _ (γ.truncate_const_continuous_family 0) _ <|
      Path.symm_continuous_family _ <|
        -- Was `fun_prop` before v4.21.0
        (by continuity))

theorem roundTripFamily_based_at {x y : X} {γ : Path x y} : ∀ t, (roundTripFamily γ) t 0 = x :=
  fun _ ↦ roundTrip_based_at

theorem roundTripFamily_zero {x y : X} {γ : Path x y} :
    (roundTripFamily γ) 0 = ofPath (Path.refl x) := by
  simp only [roundTripFamily, roundTrip, Path.truncate_zero_zero, ofPath]
  congr with t
  simp [← Path.cast_symm, ← Path.cast_trans]

theorem roundTripFamily_one {x y : X} {γ : Path x y} : (roundTripFamily γ) 1 = roundTrip γ := by
  simp only [roundTripFamily, roundTrip, Path.truncate_zero_one, ofPath]
  rfl

/-! ## Average value of a loop -/
section Average

/-- The average value of a loop. -/
noncomputable def average (γ : Loop F) : F :=
  ∫ x in (0 : ℝ)..1, γ x

-- unused
@[simp]
theorem zero_average : average (0 : Loop F) = 0 :=
  intervalIntegral.integral_zero

@[simp]
theorem average_const [CompleteSpace F] {f : F} : (const f).average = f := by simp [Loop.average]

open MeasureTheory

@[simp]
theorem average_add {γ₁ γ₂ : Loop F} (hγ₁ : IntervalIntegrable γ₁ volume 0 1)
    (hγ₂ : IntervalIntegrable γ₂ volume 0 1) : (γ₁ + γ₂).average = γ₁.average + γ₂.average := by
  simp [Loop.average, intervalIntegral.integral_add hγ₁ hγ₂]

@[simp]
theorem average_smul {γ : Loop F} {c : ℝ} : (c • γ).average = c • γ.average := by
  simp [Loop.average, intervalIntegral.integral_smul]

@[fun_prop]
theorem continuous_average {E : Type*} [TopologicalSpace E]
    {γ : E → Loop F} (hγ_cont : Continuous ↿γ) :
    Continuous fun x ↦ (γ x).average :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by apply hγ_cont) _ _

/-- The normalization of a loop `γ` is the loop `γ - γ.average`. -/
def normalize (γ : Loop F) : Loop F where
  toFun t := γ t - γ.average
  per' t := by simp [γ.per]

@[simp]
theorem normalize_apply (γ : Loop F) (t : ℝ) : Loop.normalize γ t = γ t - γ.average :=
  rfl

end Average

end Loop

section C1

/-! ## Differentiation of loop families -/


@[inherit_doc] local notation "∂₁" => partialFDerivFst ℝ

variable (π : E → ℝ) (N : ℝ) (γ : E → Loop F) (hγ : IsCompact (Loop.support γ))

/-- Differential of a loop family with respect to the parameter. -/
def Loop.diff (γ : E → Loop F) (e : E) : Loop (E →L[ℝ] F) where
  toFun t := ∂₁ (fun e t ↦ γ e t) e t
  per' t := by simp only [partialFDerivFst, Loop.per]

@[simp]
theorem Loop.diff_apply (γ : E → Loop F) (e : E) (t : ℝ) :
    Loop.diff γ e t = ∂₁ (fun e t ↦ γ e t) e t :=
  rfl

attribute [fun_prop] contDiff_parametric_integral_of_contDiff

end C1
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Algebra_Ring_Periodic
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

-- TODO: the file this references doesn't exist in mathlib any more; rename this one appropriately!

/-!

# Boundedness property of periodic function

The main purpose of that file it to prove
```
lemma Continuous.bounded_of_onePeriodic_of_isCompact {f : X → ℝ → E} (cont : Continuous ↿f)
  (hper : ∀ x, OnePeriodic (f x)) {K : Set X} (hK : IsCompact K) (hfK : ∀ x ∉ K, f x = 0) :
  ∃ C, ∀ x t, ‖f x t‖ ≤ C
```

This is done by introducing the quotient 𝕊₁ = ℝ/ℤ as a compact topological space.
Patrick is not sure this is the optimal version.

In the first part, generalize many lemmas to any period and add to `Algebra.Ring.Periodic.lean`?
-/

section


noncomputable section

open Set Function Filter TopologicalSpace Int

open scoped Topology

section OnePeriodic

variable {α : Type*}

/-- The proposition that a function on `ℝ` is periodic with period `1`. -/
def OnePeriodic (f : ℝ → α) : Prop := Periodic f 1

theorem OnePeriodic.add_int {f : ℝ → α} (h : OnePeriodic f) (k : ℤ) (x : ℝ) : f (x + k) = f x := by
  simpa using h.int_mul k x

end OnePeriodic
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Analysis_ContDiff
attribute [-instance] _root_.EquivariantEquiv.instHasUncurryForallProdReal _root_.hasUncurryLoop _root_.instMembershipProdContinuousLinearMapRealIdRelLoc
attribute [-simp] _root_.Loop.diff_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open scoped Topology Filter ContDiff
open Function

section

universe u₁ u₂ u₃ u₄ u₅

open ContinuousLinearMap

variable {𝕜 : Type u₁} [NontriviallyNormedField 𝕜]
  {M₁ : Type u₂} [NormedAddCommGroup M₁] [NormedSpace 𝕜 M₁]
  {M₂ : Type u₃} [NormedAddCommGroup M₂] [NormedSpace 𝕜 M₂]
  {M₃ : Type u₄} [NormedAddCommGroup M₃] [NormedSpace 𝕜 M₃]
  {M₄ : Type u₅} [NormedAddCommGroup M₄] [NormedSpace 𝕜 M₄]

/-- Given `(A : M₁ ≃L[𝕜] M₃)`, `(C : M₁ →L[𝕜] M₄)` and `(D : M₂ ≃L[𝕜] M₄)`,
construct the continuous linear equiv with "matrix"
A 0
C D.
-/
-- TODO: generalise this to larger constructors? or is this useful as-is?
def ContinuousLinearEquiv.lowerTriangular (A : M₁ ≃L[𝕜] M₃) (C : M₁ →L[𝕜] M₄) (D' : M₂ ≃L[𝕜] M₄) :
    (M₁ × M₂) ≃L[𝕜] M₃ × M₄ :=
  ContinuousLinearEquiv.equivOfInverse (((A : M₁ →L[𝕜] M₃).comp (fst 𝕜 M₁ M₂)).prod (C.coprod D'))
    (((A.symm : M₃ →L[𝕜] M₁).comp (fst 𝕜 M₃ M₄)).prod
      ((-((D'.symm : M₄ →L[𝕜] M₂).comp C).comp (A.symm : M₃ →L[𝕜] M₁)).coprod D'.symm))
    (fun ⟨x, y⟩ ↦ by simp)
    fun ⟨x, y⟩ ↦ by simp

theorem ContinuousLinearEquiv.continuous_lowerTriangular {X : Type*} [TopologicalSpace X]
    {A : X → M₁ ≃L[𝕜] M₃} {C : X → M₁ →L[𝕜] M₄} {D' : X → M₂ ≃L[𝕜] M₄}
    (hA : Continuous fun x ↦ (A x : M₁ →L[𝕜] M₃)) (hC : Continuous C)
    (hD : Continuous fun x ↦ (D' x : M₂ →L[𝕜] M₄)) :
    Continuous fun x ↦ ((A x).lowerTriangular (C x) (D' x) : M₁ × M₂ →L[𝕜] M₃ × M₄) :=
  (hA.compL continuous_const).prodL (hC.coprodL hD)

end

section

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : WithTop ℕ∞}

variable {𝕜}

theorem DifferentiableAt.hasFDerivAt_coprod_partial {f : E → F → G} {x : E} {y : F}
    (hf : DifferentiableAt 𝕜 (uncurry f) (x, y)) :
    HasFDerivAt (uncurry f)
      ((partialFDerivFst 𝕜 f x y).coprod (partialFDerivSnd 𝕜 f x y)) (x, y) := by
  rcases hf with ⟨θ, hθ⟩
  rwa [fderiv_partial_fst hθ, fderiv_partial_snd hθ, θ.coprod_comp_inl_inr]

theorem DifferentiableAt.hasFDerivAt_coprod {f : E → F → G} {x : E} {y : F}
    (hf : DifferentiableAt 𝕜 (uncurry f) (x, y)) {φ : E →L[𝕜] G} {ψ : F →L[𝕜] G}
    (hφ : HasFDerivAt (fun p ↦ f p y) φ x) (hψ : HasFDerivAt (f x) ψ y) :
    HasFDerivAt (uncurry f) (φ.coprod ψ) (x, y) := by
  rw [hφ.unique hf.hasFDerivAt_partial_fst, hψ.unique hf.hasFDerivAt_partial_snd]
  exact hf.hasFDerivAt_coprod_partial

variable [CompleteSpace E]

theorem Equiv.continuous_symm_of_contDiff (φ : E ≃ F) {Dφ : E → E ≃L[𝕜] F}
    (hφ : ∀ x, HasStrictFDerivAt φ (Dφ x : E →L[𝕜] F) x) : Continuous φ.symm := by
  rw [continuous_iff_continuousAt]
  intro x
  let y := φ.symm x
  let g := (hφ y).localInverse φ (Dφ y) y
  rw [← φ.apply_symm_apply x]
  have ev_eq : g =ᶠ[𝓝 (φ y)] φ.symm := by
    apply (hφ y).eventually_right_inverse.mono
    rintro x (hx : φ (g x) = x)
    exact (Equiv.eq_symm_apply φ).mpr hx
  apply ContinuousAt.congr _ ev_eq
  apply (hφ y).localInverse_continuousAt

/-- A bijection that is strictly differentiable at every point is a homeomorphism. -/
def Equiv.toHomeomorphOfContDiff (φ : E ≃ F) {Dφ : E → E ≃L[𝕜] F}
    (hφ : ∀ x, HasStrictFDerivAt φ (Dφ x : E →L[𝕜] F) x) : E ≃ₜ F :=
  { φ with
    continuous_toFun := Differentiable.continuous fun x ↦ (hφ x).differentiableAt
    continuous_invFun := φ.continuous_symm_of_contDiff hφ }

end

section

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞}

@[inherit_doc] local notation "∂₁" => partialFDerivFst 𝕜

@[inherit_doc] local notation "∂₂" => partialFDerivSnd 𝕜

theorem contDiff_parametric_symm [CompleteSpace E] [CompleteSpace F] {f : E → F ≃ G}
    {f' : E → F → F ≃L[𝕜] G} (hf : ContDiff 𝕜 ∞ fun p : E × F ↦ f p.1 p.2)
    (hf' : ∀ x y, ∂₂ (fun x y ↦ f x y) x y = f' x y) :
    ContDiff 𝕜 ∞ fun p : E × G ↦ (f p.1).symm p.2 := by
  let φ₀ : E × F ≃ E × G :=
    { toFun := fun p : E × F ↦ (p.1, f p.1 p.2)
      invFun := fun p : E × G ↦ (p.1, (f p.1).symm p.2)
      left_inv := fun x ↦ by simp
      right_inv := fun x ↦ by simp }
  let ff x y := f x y
  have hff : ContDiff 𝕜 ∞ (uncurry ff) := hf
  let d₁f := ∂₁ ff
  let Dφ : E × F → (E × F) ≃L[𝕜] E × G := fun x ↦
    (ContinuousLinearEquiv.refl 𝕜 E).lowerTriangular (d₁f x.1 x.2) (f' x.1 x.2)
  let Dφ' : E × F → E × F →L[𝕜] E × G := fun x ↦ Dφ x
  have hderiv : ∀ x : E × F, HasStrictFDerivAt φ₀ (Dφ' x) x := fun p ↦ by
    apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    · filter_upwards
      rintro ⟨x, y⟩
      apply HasFDerivAt.prodMk
      · simp only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_comp, hasFDerivAt_fst]
      have diff : Differentiable 𝕜 (uncurry fun x y ↦ f x y) := hf.differentiable (by simp)
      rw [show (fun x : E × F ↦ (f x.fst) x.snd) = uncurry fun x y ↦ f x y by ext; rfl]
      apply DifferentiableAt.hasFDerivAt_coprod
      · exact hf.differentiable (by simp) _
      · exact diff.differentiableAt.hasFDerivAt_partial_fst
      · rw [← hf' x y]
        exact diff.differentiableAt.hasFDerivAt_partial_snd
    · apply Continuous.continuousAt (ContinuousLinearEquiv.continuous_lowerTriangular ..)
      · exact continuous_const
      · exact hff.contDiff_top_partial_fst.continuous
      · simp_rw [← hf']
        exact hff.contDiff_top_partial_snd.continuous
  let φ := φ₀.toHomeomorphOfContDiff hderiv
  exact contDiff_snd.comp (φ.contDiff_symm (fun x ↦ (hderiv x).hasFDerivAt)
    (contDiff_fst.prodMk hf))

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem contDiff_parametric_symm_of_deriv_pos {f : E → ℝ → ℝ} (hf : ContDiff ℝ ∞ ↿f)
    (hderiv : ∀ x t, 0 < partialDerivSnd f x t) (hsurj : ∀ x, Surjective <| f x) :
    ContDiff ℝ ∞ fun p : E × ℝ ↦
      (StrictMono.orderIsoOfSurjective (f p.1) (strictMono_of_deriv_pos <| hderiv p.1)
            (hsurj p.1)).symm p.2 := by
  have hmono := fun x ↦ strictMono_of_deriv_pos (hderiv x)
  let F x := (StrictMono.orderIsoOfSurjective (f x) (hmono x) <| hsurj x).toEquiv
  change ContDiff ℝ ∞ fun p : E × ℝ ↦ (F p.1).symm p.snd
  refine contDiff_parametric_symm hf (f' := ?_) ?_
  · exact fun x t ↦
      ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv (f x) t) <| ne_of_gt (hderiv x t))
  · intro x t
    suffices partialFDerivSnd ℝ f x t 1 = partialDerivSnd f x t by
      ext
      simpa
    apply partialFDerivSnd_one

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem contDiffWithinAt_finsum {ι : Type*} {f : ι → E → F}
    (lf : LocallyFinite fun i ↦ support <| f i) {n : WithTop ℕ∞} {s : Set E} {x₀ : E}
    (h : ∀ i, ContDiffWithinAt 𝕜 n (f i) s x₀) : ContDiffWithinAt 𝕜 n (fun x ↦ ∑ᶠ i, f i x) s x₀ :=
  let ⟨_I, hI⟩ := finsum_eventually_eq_sum lf x₀
  ContDiffWithinAt.congr_of_eventuallyEq (ContDiffWithinAt.sum fun i _ ↦ h i)
    (eventually_nhdsWithin_of_eventually_nhds hI) hI.self_of_nhds

theorem contDiffAt_finsum {ι : Type*} {f : ι → E → F} (lf : LocallyFinite fun i ↦ support <| f i)
    {n : WithTop ℕ∞} {x₀ : E} (h : ∀ i, ContDiffAt 𝕜 n (f i) x₀) :
    ContDiffAt 𝕜 n (fun x ↦ ∑ᶠ i, f i x) x₀ :=
  contDiffWithinAt_finsum lf h

end
end
end
end

section
-- module Solutions.OAIQ249_SI.Loops_DeltaMollifier
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Delta mollifiers

A key ingredient in the proof of the reparametrization lemma is the existence of a smooth
approximation to the Dirac delta function. Such an approximation is a sequence of functions
`δ : ℕ × S¹ → S¹`, `(i, t) ↦ δᵢ t` such that:
 * `δᵢ` is smooth for all `i`,
 * `δᵢ` is non-negative for all `i`,
 * `∫ x in 0..1, (δᵢ x) = 1` for all `i`,
* `∫ x in 0..1, (δᵢ x) • f x → f 0`, as `i → ∞` for any continuous function `f` on `S¹`.

This file contains a construction `approxDirac` of such a family `δ` together with code which
packages this into the precise form required for the proof of the reparametrization lemma:
`deltaMollifier`, `Loop.mollify`.

The key ingredients are the existence of smooth "bump functions" and a powerful theory of
convolutions.
-/

section


noncomputable section

open Set Function MeasureTheory.MeasureSpace ContinuousLinearMap
open scoped Topology Filter Convolution ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
section

/-! ## Bump family

In this section we construct `bump (n : ℕ)`, a bump function with support in
`Ioo (-1/(n+2)) (1/(n+2))`.
-/


/-- `bump n` is a bump function on `ℝ` which has support `Ioo (-(1/(n+2))) (1/(n+2))`
and equals one on `Icc (-(1/(n+3))) (1/(n+3))`.
-/
def bump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / (n + 3)
  rOut := 1 / (n + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply one_div_lt_one_div_of_lt
    · exact_mod_cast Nat.succ_pos _
    · exact_mod_cast lt_add_one (n + 2)

theorem support_bump (n : ℕ) : support (bump n) = Ioo (-((1 : ℝ) / (n + 2))) (1 / (n + 2)) := by
  rw [(bump n).support_eq, Real.ball_eq_Ioo, zero_sub, zero_add, bump]

theorem support_bump_subset (n : ℕ) : support (bump n) ⊆ Ioc (-(1 / 2)) (1 / 2) := by
  have ineg : 1 / (n + 2 : ℝ) ≤ 1 / 2 := by apply one_div_le_one_div_of_le <;> norm_num
  rw [support_bump n]
  exact Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc (neg_le_neg ineg) ineg)

theorem support_shifted_normed_bump_subset (n : ℕ) (t : ℝ) :
    (support fun x ↦ (bump n).normed volume (x - t)) ⊆ Ioc (t - 1 / 2) (t + 1 / 2) := by
  change support ((bump n).normed volume ∘ (· - t)) ⊆ _
  rw [Function.support_comp_eq_preimage, (bump n).support_normed_eq, ← (bump n).support_eq]
  refine (preimage_mono (support_bump_subset n)).trans ?_
  simp [sub_eq_add_neg, add_comm]

end

section

/-! # Periodize

In this section we turn any function `f : ℝ → E` into a 1-periodic function
`fun t : ℝ ↦ ∑ᶠ n : ℤ, f (t+n)`.
-/


variable {M : Type*} [AddCommMonoid M]

/-- Turn a function into a 1-periodic function. If its support lies in a (non-closed) interval
of length 1, then this will be that function made periodic with period 1. -/
def periodize (f : ℝ → M) (t : ℝ) : M :=
  ∑ᶠ n : ℤ, f (t + n)

theorem periodic_periodize (f : ℝ → M) : Periodic (_root_.periodize f) 1 := by
  intro t
  unfold _root_.periodize
  have : (fun n : ℤ ↦ f (t + 1 + ↑n)) = fun n ↦ f (t + (n + 1 : ℤ)) := by
    ext n; simp_rw [Int.cast_add, Int.cast_one, add_assoc, add_comm]
  simp_rw [this]
  let e := Equiv.addRight (1 : ℤ)
  let F : ℤ → M := fun n ↦ f (t + n)
  change ∑ᶠ n : ℤ, F (e n) = ∑ᶠ n : ℤ, f (t + ↑n)
  apply finsum_comp_equiv

theorem periodize_nonneg {f : ℝ → ℝ} (h : ∀ t, 0 ≤ f t) (t : ℝ) : 0 ≤ _root_.periodize f t := by
  unfold _root_.periodize
  obtain (H | H) := (support fun i : ℤ ↦ f (t + i)).finite_or_infinite
  · rw [finsum_eq_sum _ H]
    exact Finset.sum_nonneg fun i _ ↦ h _
  · rwa [finsum_of_infinite_support]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[fun_prop]
theorem ContDiff.periodize {f : ℝ → E} {n : ℕ∞} (h : ContDiff ℝ n f) (h' : HasCompactSupport f) :
    ContDiff ℝ n (periodize f) := by
  refine contDiff_iff_contDiffAt.mpr fun x ↦ contDiffAt_finsum ?_ ?_
  · intro y
    set N := Ioo (y - 1) (y + 1)
    refine ⟨N, (nhds_basis_Ioo_pos y).mem_of_mem zero_lt_one, ?_⟩
    let e := fun i : ℤ ↦ Equiv.addRight (i : ℝ)
    change {i : ℤ | ((support fun x : ℝ ↦ f (e i x)) ∩ N).Nonempty}.Finite
    have hsupp : ∀ i : ℤ, (support fun x : ℝ ↦ f (e i x)) = e i ⁻¹' support f := fun _ ↦ rfl
    have hsupp' : ∀ i, (e i ⁻¹' support f ∩ N).Nonempty ↔ (support f ∩ e i '' N).Nonempty := by
      intro i
      conv_lhs => rw [← (e i).preimage_image N, ← preimage_inter]
      rw [(e i).surjective.nonempty_preimage]
    simp_rw [hsupp, hsupp', inter_comm (support f)]
    refine (ProperlyDiscontinuousVAdd.finite_disjoint_inter_image
      (isCompact_Icc : IsCompact <| Icc (y - 1) (y + 1)) h').subset ?_
    intro i hi
    rw [mem_ofPred_eq]
    apply Nonempty.mono _ hi
    gcongr
    · rw [show (e i : ℝ → ℝ) = VAdd.vadd i by ext x; exact add_comm x i]
      exact image_mono Ioo_subset_Icc_self
    exact subset_tsupport f
  · fun_prop

theorem periodize_comp_sub (f : ℝ → M) (x t : ℝ) :
    periodize (fun x' ↦ f (x' - t)) x = periodize f (x - t) := by
  simp_rw [periodize, sub_add_eq_add_sub]

theorem periodize_smul_periodic (f : ℝ → ℝ) {g : ℝ → E} (hg : Periodic g 1) (t : ℝ) :
    periodize f t • g t = periodize (fun x ↦ f x • g x) t := by
  dsimp only [periodize]
  rw [finsum_smul]
  congr 1
  ext n
  rw [OnePeriodic.add_int hg]

open MeasureTheory

theorem integral_periodize (f : ℝ → E) {a : ℝ} (hf : support f ⊆ Ioc a (a + 1)) :
    ∫ t in a..a + 1, periodize f t = ∫ t in a..a + 1, f t := by
  apply intervalIntegral.integral_congr_ae
  have : ∀ᵐ x : ℝ, x ∈ uIoc a (a + 1) → x ∈ Ioo a (a + 1) := by
    rw [uIoc_of_le (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1))]
    have : ∀ᵐ x : ℝ, x ≠ a + 1 := by simp [ae_iff]
    apply this.mono
    rintro x (x_ne : x ≠ a + 1) ⟨hx, hx'⟩
    exact ⟨hx, x_ne.le_iff_lt.mp hx'⟩
  apply this.mono
  intro t ht ht'
  specialize ht ht'
  dsimp only [periodize]
  have : (support fun n : ℤ ↦ f (t + n)) ⊆ ({0} : Finset ℤ) := fun n hn ↦ by
    suffices n = 0 by simpa
    replace hn : t + n ∈ Ioc a (a + 1) := hf (mem_support.mpr hn)
    cases ht
    cases hn
    have : -(1 : ℝ) < n := by linarith
    have : -1 < n := mod_cast this
    have : (n : ℝ) < 1 := by linarith
    norm_cast at this
    linarith
  simp [finsum_eq_sum_of_support_subset _ this]

-- if convenient we could set `[c,d] = [0,1]`
theorem intervalIntegral_periodize_smul (f : ℝ → ℝ) (γ : Loop E) {a b c d : ℝ} (h : b ≤ a + 1)
    (h2 : d = c + 1) (hf : support f ⊆ Ioc a b) :
    ∫ t in c..d, periodize f t • γ t = ∫ t, f t • γ t := by
  rw [h2]
  have : (support fun t ↦ f t • γ t) ⊆ Ioc a (a + 1) := by
    erw [support_smul]
    exact (inter_subset_left.trans hf).trans (Ioc_subset_Ioc_right h)
  rw [← intervalIntegral.integral_eq_integral_of_support_subset this]
  simp_rw [periodize_smul_periodic _ γ.periodic,
    Function.Periodic.intervalIntegral_add_eq (periodic_periodize fun x : ℝ ↦ f x • γ x) c a]
  exact integral_periodize _ this

end

section DeltaApprox

/-! ## An approximate Dirac "on the circle". -/


/-- A periodized bump function, which we can view as a function from `𝕊¹ → ℝ`. As `n → ∞` this
tends to the Dirac delta function located at `0`. -/
def approxDirac (n : ℕ) : ℝ → ℝ :=
  periodize <| (bump n).normed volume

theorem periodic_approxDirac (n : ℕ) : Periodic (approxDirac n) 1 := periodic_periodize _

theorem approxDirac_nonneg (n : ℕ) (t : ℝ) : 0 ≤ approxDirac n t :=
  periodize_nonneg (bump n).nonneg_normed t

@[fun_prop]
theorem contDiff_approxDirac (n : ℕ) : ContDiff ℝ ∞ (approxDirac n) :=
  (bump n).contDiff_normed.periodize (bump n).hasCompactSupport_normed

theorem approxDirac_integral_eq_one (n : ℕ) {a b : ℝ} (h : b = a + 1) :
    ∫ s in a..b, approxDirac n s = 1 := by
  have supp : support ((bump n).normed volume) ⊆ Ioc (-(1 / 2)) (-(1 / 2) + 1) := by
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
      show support ((bump n).normed volume) = _ from (bump n).support_normed_eq,
      Real.ball_zero_eq_Ioo, show (bump n).rOut = 1 / (n + 2 : ℝ) from rfl]
    have key : 1 / (n + 2 : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le
      · norm_num
      norm_cast
      norm_num
    exact (Ioo_subset_Ioo (neg_le_neg key) key).trans Ioo_subset_Ioc_self
  rw [approxDirac, h,
    Function.Periodic.intervalIntegral_add_eq (periodic_periodize _) a (-(1 / 2 : ℝ)),
    integral_periodize _ supp, intervalIntegral.integral_eq_integral_of_support_subset supp]
  exact (bump n).integral_normed

end DeltaApprox

section VersionOfDeltaMollifierUsingN

/-- A sequence of functions that converges to the Dirac delta function located at `t`, with the
properties that this sequence is everywhere positive and -/
def deltaMollifier (n : ℕ) (t : ℝ) : ℝ → ℝ := fun x ↦
  n / (n + 1) * approxDirac n (x - t) + 1 / (n + 1)

variable {n : ℕ} {t : ℝ}

theorem deltaMollifier_periodic : Periodic (deltaMollifier n t) 1 := fun x ↦ by
  simp_rw [deltaMollifier, ← sub_add_eq_add_sub, periodic_approxDirac n (x - t)]

theorem deltaMollifier_pos (s : ℝ) : 0 < deltaMollifier n t s := by
  have := approxDirac_nonneg n (s - t)
  exact add_pos_of_nonneg_of_pos (by positivity) (by positivity)

@[fun_prop]
theorem contDiff_deltaMollifier : ContDiff ℝ ∞ (deltaMollifier n t) := by
  unfold deltaMollifier; fun_prop

open intervalIntegral

@[simp]
theorem deltaMollifier_integral_eq_one : ∫ s in (0)..1, deltaMollifier n t s = 1 := by
  simp_rw [deltaMollifier]
  rw [integral_comp_sub_right (fun x ↦ (n : ℝ) / (n + 1) * approxDirac n x + 1 / (n + 1)) t,
    integral_add, integral_const_mul, integral_const, zero_sub, sub_neg_eq_add, sub_add_cancel,
    one_smul, approxDirac_integral_eq_one, mul_one, ← add_div, div_self]
  · exact n.cast_add_one_pos.ne'
  · rw [sub_eq_add_neg, add_comm]
  · exact ((contDiff_approxDirac n).continuous.intervalIntegrable _ _).const_mul _
  · exact intervalIntegrable_const

/-- `γ.mollify n t` is a weighted average of `γ` using weights `deltaMollifier n t`.
This means that as `n → ∞` this value tends to `γ t`, but because `deltaMollifier n t` is positive,
we know that we can reparametrize `γ` to obtain a loop that has `γ.mollify n t` as its actual
average. -/
def Loop.mollify (γ : Loop F) (n : ℕ) (t : ℝ) : F :=
  ∫ s in (0)..1, deltaMollifier n t s • γ s

theorem Loop.mollify_eq_convolution (γ : Loop F) (hγ : Continuous γ) (t : ℝ) :
    γ.mollify n t =
      ((n : ℝ) / (n + 1)) • ((bump n).normed volume ⋆[lsmul ℝ ℝ]γ) t +
        ((1 : ℝ) / (n + 1)) • ∫ t in (0)..1, γ t := by
  simp_rw [Loop.mollify, deltaMollifier, add_smul, mul_smul]
  rw [integral_add]
  on_goal 1 =>
    simp_rw [integral_smul, approxDirac, ← periodize_comp_sub]
    rw [intervalIntegral_periodize_smul _ γ _ _ (support_shifted_normed_bump_subset n t)]
  · simp_rw [MeasureTheory.convolution_eq_swap, ← neg_sub t, (bump n).normed_neg, lsmul_apply]
  · linarith
  · rw [zero_add]
  · exact (continuous_const.smul
      (((contDiff_approxDirac n).continuous.comp (by fun_prop)).smul hγ)).intervalIntegrable _ _
  · apply Continuous.intervalIntegrable (by fun_prop)

end VersionOfDeltaMollifierUsingN
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Analysis_Convex_Basic
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

open Function Set

section

variable {𝕜 𝕜' E E₂ E' : Type*} [Semiring 𝕜] [PartialOrder 𝕜] --[IsOrderedRing 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid E₂] [Module 𝕜 E₂] [AddCommMonoid E']
  [Semiring 𝕜'] [PartialOrder 𝕜'] [IsOrderedRing 𝕜'] [Module 𝕜' E'] (σ : 𝕜 →+*o 𝕜')

def reallyConvexHull (𝕜 : Type*) {E : Type*}
    [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]
    (s : Set E) : Set E :=
  {e | ∃ w : E → 𝕜, 0 ≤ w ∧ support w ⊆ s ∧ ∑ᶠ x, w x = 1 ∧ e = ∑ᶠ x, w x • x}

-- https://xkcd.com/927/
theorem finsum.exists_ne_zero_of_sum_ne_zero {β α : Type*} {s : Finset α} {f : α → β}
    [AddCommMonoid β] : ∑ᶠ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f a ≠ 0 := by
  rw [finsum_mem_finset_eq_sum]
  exact Finset.exists_ne_zero_of_sum_ne_zero

theorem sum_mem_reallyConvexHull [IsOrderedRing 𝕜]
    {s : Set E} {ι : Type*} {t : Finset ι} {w : ι → 𝕜} {z : ι → E}
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s) :
    ∑ i ∈ t, w i • z i ∈ reallyConvexHull 𝕜 s := by
  classical
  refine ⟨fun e ↦ ∑ᶠ i ∈ t.filter fun j ↦ z j = e, w i, ?_, ?_, ?_, ?_⟩
  · rw [Pi.le_def]
    exact fun e ↦ finsum_nonneg fun i ↦ finsum_nonneg fun hi ↦ h₀ _ (Finset.mem_of_mem_filter i hi)
  · intro e he
    rw [mem_support] at he
    obtain ⟨a, h, ha⟩ := finsum.exists_ne_zero_of_sum_ne_zero he
    rw [Finset.mem_filter] at h
    rcases h with ⟨h, rfl⟩
    exact hz a h
  · simp_rw [← h₁, finsum_mem_finset_eq_sum, finsum_sum_filter z ..]
  · simp_rw [finsum_mem_finset_eq_sum, Finset.sum_smul]
    rw [← finsum_sum_filter z]
    congr with x
    rw [Finset.sum_congr rfl]
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [hy.2]

theorem reallyConvexHull_mono : Monotone (reallyConvexHull 𝕜 : Set E → Set E) := by
  rintro s t h _ ⟨w, w_pos, supp_w, sum_w, rfl⟩
  exact ⟨w, w_pos, supp_w.trans h, sum_w, rfl⟩

/-- Generalization of `Convex` to semirings. We only add the `s = ∅` clause if `𝕜` is trivial. -/
def ReallyConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] (s : Set E) : Prop :=
  s = ∅ ∨ ∀ w : E → 𝕜, 0 ≤ w → support w ⊆ s → ∑ᶠ x, w x = 1 → ∑ᶠ x, w x • x ∈ s

variable {s : Set E}

@[simp]
theorem reallyConvex_empty : ReallyConvex 𝕜 (∅ : Set E) := Or.inl rfl

@[simp]
theorem reallyConvex_univ : ReallyConvex 𝕜 (univ : Set E) := Or.inr fun _ _ _ _ ↦ mem_univ _

-- for every lemma that requires `Nontrivial` should we also add a lemma that has the condition
-- `s.Nonempty` (or even `Nontrivial 𝕜 ∨ s.Nonempty`)?
theorem Nontrivial.reallyConvex_iff [Nontrivial 𝕜] :
    ReallyConvex 𝕜 s ↔ ∀ w : E → 𝕜, 0 ≤ w → support w ⊆ s → ∑ᶠ x, w x = 1 → ∑ᶠ x, w x • x ∈ s := by
  rw [ReallyConvex, or_iff_right_iff_imp]
  rintro rfl w hw h2w h3w
  obtain rfl : w = 0 := by ext; simp at h2w; simp [h2w]
  simp at h3w

theorem reallyConvex_iff_hull [Nontrivial 𝕜] : ReallyConvex 𝕜 s ↔ reallyConvexHull 𝕜 s ⊆ s := by
  rw [Nontrivial.reallyConvex_iff]
  constructor
  · rintro h _ ⟨w, w_pos, supp_w, sum_w, rfl⟩
    exact h w w_pos supp_w sum_w
  · rintro h w w_pos supp_w sum_w
    exact h ⟨w, w_pos, supp_w, sum_w, rfl⟩

-- turn this into an iff
theorem ReallyConvex.sum_mem [Nontrivial 𝕜] [IsOrderedRing 𝕜]
    (hs : ReallyConvex 𝕜 s) {ι : Type*} {t : Finset ι} {w : ι → 𝕜} {z : ι → E}
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s) :
    ∑ i ∈ t, w i • z i ∈ s :=
  reallyConvex_iff_hull.mp hs (sum_mem_reallyConvexHull h₀ h₁ hz)

set_option backward.isDefEq.respectTransparency.types false in
theorem ReallyConvex.finsum_mem [Nontrivial 𝕜] [IsOrderedRing 𝕜]
    (hs : ReallyConvex 𝕜 s) {ι : Type*} {w : ι → 𝕜} {z : ι → E}
    (h₀ : ∀ i, 0 ≤ w i) (h₁ : ∑ᶠ i, w i = 1) (hz : ∀ i ∈ support w, z i ∈ s) :
    ∑ᶠ i, w i • z i ∈ s := by
  rw [finsum_eq_sum_of_support_subset_of_finite _ _ (hasFiniteSupport_of_finsum_eq_one h₁)]
  swap; · exact support_smul_subset_left w z
  apply hs.sum_mem fun i _ ↦ h₀ i
  · rw [← finsum_eq_sum, h₁]
  · simp_rw [Set.Finite.mem_toFinset]; exact hz

theorem ReallyConvex.add_mem [IsOrderedRing 𝕜] (hs : ReallyConvex 𝕜 s) {w₁ w₂ : 𝕜} {z₁ z₂ : E}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) (hz₁ : z₁ ∈ s) (hz₂ : z₂ ∈ s) :
    w₁ • z₁ + w₂ • z₂ ∈ s := by
  cases subsingleton_or_nontrivial 𝕜
  · have := Module.subsingleton 𝕜 E
    rwa [Subsingleton.mem_iff_nonempty] at hz₁ ⊢
  suffices ∑ b : Bool, cond b w₁ w₂ • cond b z₁ z₂ ∈ s by simpa using this
  apply hs.sum_mem <;> simp [*]

theorem ReallyConvex.inter {t : Set E} (hs : ReallyConvex 𝕜 s) (ht : ReallyConvex 𝕜 t) :
    ReallyConvex 𝕜 (s ∩ t) := by
  rcases hs with (rfl | hs); · simp
  rcases ht with (rfl | ht); · simp
  refine Or.inr fun w w_pos supp_w sum_w ↦ ?_
  cases Set.subset_inter_iff.mp supp_w
  constructor
  · apply hs <;> assumption
  · apply ht <;> assumption

theorem ReallyConvex.preimageₛₗ (f : E →ₛₗ[σ.toRingHom] E') {s : Set E'} (hs : ReallyConvex 𝕜' s) :
    ReallyConvex 𝕜 (f ⁻¹' s) := by
  -- this proof would be easier by casing on `s = ∅`, and
  cases subsingleton_or_nontrivial 𝕜'
  · have : Subsingleton E' := Module.subsingleton 𝕜' E'
    refine Subsingleton.set_cases ?_ ?_ s
    · simp_rw [preimage_empty, reallyConvex_empty]
    · simp_rw [preimage_univ, reallyConvex_univ]
  · refine Or.inr fun w hw h2w h3w ↦ ?_
    have h4w : (support w).Finite := hasFiniteSupport_of_finsum_eq_one h3w
    have : (support fun x ↦ w x • x).Finite := h4w.subset (support_smul_subset_left w id)
    simp_rw [mem_preimage, map_finsum f this, map_smulₛₗ f]
    apply hs.finsum_mem
    · intro i; rw [← map_zero σ]; apply σ.monotone'; apply hw
    · rw [← map_finsum _ h4w, h3w, map_one]
    · intro i hi; apply h2w; rw [mem_support] at hi ⊢; contrapose! hi; rw [hi, map_zero]

end

section

variable (𝕜 : Type*) {E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E]

theorem reallyConvex_iff_convex {s : Set E} : ReallyConvex 𝕜 s ↔ Convex 𝕜 s := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro x hx y hy v w hv hw hvw; apply ReallyConvex.add_mem <;> assumption
  · exact Or.inr fun w hw h2w h3w ↦ h.finsum_mem hw h3w fun i hi ↦ h2w <| mem_support.mpr hi

end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Geometry_Manifold_Algebra_SmoothGerm
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
## Germs of smooth functions
under construction: might need further refactoring to be usable!
-/

section

-- TODO: please confirm authorship and copyright are appropriate

noncomputable section

open Filter Set

open scoped Manifold Topology ContDiff

-- FIXME: move to `Manifold/Algebra/SmoothFunctions`, around line 46
section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
  {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' ∞ G]

@[to_additive]
theorem SmoothMap.coe_prod {ι : Type*} (f : ι → C^∞⟮I, N; I', G⟯) (s : Finset ι) :
    ⇑(∏ i ∈ s, f i) = ∏ i ∈ s, ⇑(f i) :=
  map_prod (ContMDiffMap.coeFnMonoidHom : C^∞⟮I, N; I', G⟯ →* N → G) f s

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (G : Type*) [AddCommGroup G] [Module ℝ G]

/-- The map `C^∞(N, ℝ) → Germ (𝓝 x) ℝ` as a ring homomorphism. -/
def RingHom.germOfContMDiffMap (x : N) : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯ →+* Germ (𝓝 x) ℝ :=
  RingHom.comp (Germ.coeRingHom _) ContMDiffMap.coeFnRingHom

/-- All germs of smooth functions `N → ℝ` at `x : N`, as a subring of `Germ (𝓝 x) ℝ`. -/
def smoothGerm (x : N) : Subring (Germ (𝓝 x) ℝ) :=
  (RingHom.germOfContMDiffMap I x).range

instance instCoeContMDiffMapRealModelWithCornersSelfSomeENatTopSubtypeGermNhdsMemSubringSmoothGerm (x : N) : Coe C^∞⟮I, N; 𝓘(ℝ), ℝ⟯ (smoothGerm I x) :=
  ⟨fun f ↦ ⟨(f : N → ℝ), ⟨f, rfl⟩⟩⟩

@[simp]
theorem smoothGerm.coe_coe (f : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) (x : N) :
    ((f : smoothGerm I x) : (𝓝 x).Germ ℝ) = (f : (𝓝 x).Germ ℝ) :=
  rfl

@[simp]
theorem smoothGerm.coe_sum {ι} (f : ι → C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) (s : Finset ι) (x : N) :
    ((∑ i ∈ s, f i : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) : smoothGerm I x) = ∑ i ∈ s, (f i : smoothGerm I x) :=
  map_sum (RingHom.rangeRestrict (RingHom.germOfContMDiffMap I x)) f s

@[simp]
theorem smoothGerm.coe_eq_coe (f g : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) {x : N} (h : ∀ᶠ y in 𝓝 x, f y = g y) :
    (f : smoothGerm I x) = (g : smoothGerm I x) := by
  ext
  apply Quotient.sound
  exact h

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {HG : Type*} [TopologicalSpace HG]
  (IG : ModelWithCorners ℝ G HG) {N : Type*} [TopologicalSpace N] [ChartedSpace HG N]
  [IsManifold IG ∞ N]

def smoothGerm.valueOrderRingHom (x : N) : smoothGerm IG x →+*o ℝ :=
  Filter.Germ.valueOrderRingHom.comp <| Subring.orderedSubtype _

def smoothGerm.valueRingHom (x : N) : smoothGerm IG x →+* ℝ :=
  Filter.Germ.valueRingHom.comp <| Subring.subtype _

omit [IsManifold IG ∞ N] in
theorem smoothGerm.valueOrderRingHom_toRingHom (x : N) :
    (smoothGerm.valueOrderRingHom IG x).toRingHom = smoothGerm.valueRingHom IG x :=
  rfl

namespace Filter.Germ

def valueₛₗ {F} [AddCommMonoid F] [Module ℝ F] (x : N) :
    Germ (𝓝 x) F →ₛₗ[smoothGerm.valueRingHom IG x] F :=
  { Filter.Germ.valueAddHom with
    toFun := Filter.Germ.value
    map_smul' := fun φ ψ ↦ (φ : Germ (𝓝 x) ℝ).value_smul ψ }

variable (I)

protected def ContMDiffAt' {x : M} (φ : Germ (𝓝 x) N) (n : WithTop ℕ∞) : Prop :=
  Quotient.liftOn' φ (fun f ↦ CMDiffAt n f x) fun f g h ↦
    propext <| by
      constructor
      all_goals refine fun H ↦ H.congr_of_eventuallyEq ?_
      exacts [h.symm, h]

/-- The predicate selecting germs of `ContMDiffAt` functions.
TODO: merge with the next def that generalizes target space -/
protected nonrec def ContMDiffAt {x : M} (φ : Germ (𝓝 x) F) (n : WithTop ℕ∞) : Prop :=
  φ.ContMDiffAt' I 𝓘(ℝ, F) n

variable {I}

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

theorem _root_.smoothGerm.contMDiffAt {x : M} (φ : smoothGerm I x) {n : ℕ∞} :
    (φ : Germ (𝓝 x) ℝ).ContMDiffAt I n := by
  rcases φ with ⟨_, g, rfl⟩
  apply g.contMDiff.of_le (mod_cast le_top)

protected nonrec theorem ContMDiffAt.add {x : M} {φ ψ : Germ (𝓝 x) F} {n : ℕ∞} :
    φ.ContMDiffAt I n → ψ.ContMDiffAt I n → (φ + ψ).ContMDiffAt I n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg ↦ hf.add hg

protected nonrec theorem ContMDiffAt.smul {x : M} {φ : Germ (𝓝 x) ℝ} {ψ : Germ (𝓝 x) F}
    {n : ℕ∞} : φ.ContMDiffAt I n → ψ.ContMDiffAt I n → (φ • ψ).ContMDiffAt I n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg ↦ hf.smul hg

theorem ContMDiffAt.sum {x : M} {ι} {s : Finset ι} {n : ℕ∞} {f : ι → Germ (𝓝 x) F}
    (h : ∀ i ∈ s, (f i).ContMDiffAt I n) : (∑ i ∈ s, f i).ContMDiffAt I n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact contMDiffAt_const
  | insert φ s hφs hs =>
  simp only [Finset.mem_insert, forall_eq_or_imp] at h
  rw [Finset.sum_insert hφs]
  exact h.1.add (hs h.2)

end Filter.Germ

end

section

variable {E₁ E₂ F H₁ M₁ H₂ M₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H₁] (I₁ : ModelWithCorners ℝ E₁ H₁)
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [SigmaCompactSpace M₁] [T2Space M₁]
  [TopologicalSpace H₂] (I₂ : ModelWithCorners ℝ E₂ H₂)
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

open scoped Filter

open Function

namespace Filter.Germ

-- TODO: generalize the next def?
def ContMDiffAtProd {x : M₁} (φ : Germ (𝓝 x) (M₂ → F)) (n : ℕ∞) : Prop :=
  Quotient.liftOn' φ (fun f ↦ ∀ y : M₂, ContMDiffAt (I₁.prod I₂) 𝓘(ℝ, F) n (uncurry f) (x, y))
    fun f g h ↦ propext <| by
        change {x' | f x' = g x'} ∈ 𝓝 x at h
        constructor
        all_goals
          refine fun H y ↦ (H y).congr_of_eventuallyEq ?_
          clear H
          replace h : {x' | f x' = g x'} ×ˢ (univ : Set M₂) ∈ 𝓝 x ×ˢ 𝓝 y := prod_mem_prod h univ_mem
          rw [← nhds_prod_eq] at h
          apply mem_of_superset h
          rintro ⟨x', y'⟩ ⟨hx' : f x' = g x', -⟩
          simp only [mem_ofPred_eq, uncurry_apply_pair]
          apply congr_fun
        exacts [hx'.symm, hx']

/- potential generalization of the above.
note(grunweg): fixed some names for Lean 4, but not the core syntax
def contMDiffAt_comp {x : M₁} (φ : germ (𝓝 x) M₂) (n : ℕ∞)
  (g : M₂ → M₃) (h : M₄ → M₁) : Prop :=
quotient.lift_on' φ (λ f, ∀ y ∈ h⁻¹' {x}, ContMDiffAt I₄ I₃ n (g ∘ f ∘ h) y) (λ f g h, propext begin
  change {x' | f x' = g x'} ∈ 𝓝 x at h,
  split,
  all_goals
  { refine λ H y, (H y).congr_of_eventuallyEq _,
    clear H,
    replace h : {x' | f x' = g x'} ×ˢ (univ : Set M₂) ∈ (𝓝 x) ×ᶠ (𝓝 y) := prod_mem_prod h univ_mem,
    rw ← nhds_prod_eq at h,
    apply mem_of_superset h,
    rintros ⟨x', y'⟩ ⟨(hx' : f x' = g x'), -⟩,
    simp only [mem_ofPred_eq, uncurry_apply_pair],
    apply congr_fun, },
  exacts [hx'.symm, hx']
end)
-/
variable {I₁ I₂}

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [IsManifold I₁ ∞ M₁]
  [SigmaCompactSpace M₁] [T2Space M₁] [IsManifold I₂ ∞ M₂]

theorem ContMDiffAtProd.add {x : M₁} {φ ψ : Germ (𝓝 x) <| M₂ → F} {n : ℕ∞} :
    φ.ContMDiffAtProd I₁ I₂ n → ψ.ContMDiffAtProd I₁ I₂ n → (φ + ψ).ContMDiffAtProd I₁ I₂ n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg y ↦ (hf y).add (hg y)

theorem ContMDiffAt.smul_prod {x : M₁} {φ : Germ (𝓝 x) ℝ} {ψ : Germ (𝓝 x) (M₂ → F)}
    {n : ℕ∞} : φ.ContMDiffAt I₁ n → ψ.ContMDiffAtProd I₁ I₂ n → (φ • ψ).ContMDiffAtProd I₁ I₂ n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg y ↦
    .smul (.comp _ hf contMDiffAt_fst) (hg y)

theorem ContMDiffAtProd.sum {x : M₁} {ι} {s : Finset ι} {n : ℕ∞}
    {f : ι → Germ (𝓝 x) (M₂ → F)} (h : ∀ i ∈ s, (f i).ContMDiffAtProd I₁ I₂ n) :
    (∑ i ∈ s, f i).ContMDiffAtProd I₁ I₂ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]; intro y
    exact contMDiffAt_const (x := (x, y)) (c := (0 : F))
  | insert φ s hφs hs =>
  simp only [Finset.mem_insert, forall_eq_or_imp] at h
  rw [Finset.sum_insert hφs]
  exact h.1.add (hs h.2)

end Filter.Germ

end
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Partition
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open scoped Topology
open Set Function Filter

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

namespace SmoothPartitionOfUnity

variable {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) {x : M}

theorem sum_germ (hx : x ∈ interior s := by simp) :
    ∑ i ∈ ρ.fintsupport x, (ρ i : smoothGerm I x) = 1 := by
  have : ∀ᶠ y in 𝓝 x, y ∈ interior s := isOpen_interior.eventually_mem hx
  have : ∀ᶠ y in 𝓝 x, (⇑(∑ i ∈ ρ.fintsupport x, ρ i)) y = 1 := by
    filter_upwards [ρ.eventually_finsupport_subset x, this] with y hy hy'
    rw [SmoothMap.coe_sum, Finset.sum_apply]
    apply ρ.toPartitionOfUnity.sum_finsupport' (interior_subset hy') hy
  rw [← smoothGerm.coe_sum]
  exact smoothGerm.coe_eq_coe _ _ 1 this

def combine (ρ : SmoothPartitionOfUnity ι I M s) (φ : ι → M → F) (x : M) : F :=
  ∑ᶠ i, ρ i x • φ i x

theorem germ_combine_mem (φ : ι → M → F) (hx : x ∈ interior s := by simp) :
    (ρ.combine φ : Germ (𝓝 x) F) ∈
      reallyConvexHull (smoothGerm I x) ((fun i ↦ (φ i : Germ (𝓝 x) F)) '' ρ.fintsupport x) := by
  change x ∈ interior s at hx
  have : (ρ.combine φ : Germ (𝓝 x) F) =
      ∑ i ∈ ρ.fintsupport x, (ρ i : smoothGerm I x) • (φ i : Germ (𝓝 x) F) := by
    suffices (ρ.combine φ : Germ (𝓝 x) F) =
        ↑(∑ i ∈ ρ.fintsupport x, ((ρ i : M → ℝ) • φ i : M → F)) by
      rw [this, Germ.coe_sum]; rfl
    rw [Germ.coe_eq]
    filter_upwards [ρ.eventually_finsupport_subset x] with x' hx'
    simp_rw [SmoothPartitionOfUnity.combine, Finset.sum_apply, Pi.smul_apply']
    rw [finsum_eq_sum_of_support_subset]
    refine Subset.trans ?_ (Finset.coe_subset.mpr hx')
    rw [SmoothPartitionOfUnity.finsupport, PartitionOfUnity.finsupport, Finite.coe_toFinset]
    apply support_smul_subset_left
  rw [this]
  refine sum_mem_reallyConvexHull ?_ (ρ.sum_germ hx) (fun i hi ↦ mem_image_of_mem _ hi)
  · intro i _
    filter_upwards using fun a ↦ ρ.nonneg i a

end SmoothPartitionOfUnity

end
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_ExistsOfConvex
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open scoped Topology Manifold ContDiff

open Set Function Filter

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

section

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

theorem exists_of_convex {P : (Σ x : M, Germ (𝓝 x) F) → Prop}
    (hP : ∀ x : M, ReallyConvex (smoothGerm I x) {φ | P ⟨x, φ⟩})
    (hP' : ∀ x : M, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, P ⟨x', f⟩) : ∃ f : M → F, ∀ x, P ⟨x, f⟩ := by
  replace hP' : ∀ x : M, ∃ f : M → F, ∃ U ∈ 𝓝 x, ∀ x' ∈ U, P ⟨x', f⟩ := by
    intro x
    rcases hP' x with ⟨f, hf⟩
    exact ⟨f, {x' | P ⟨x', ↑f⟩}, hf, fun _ ↦ id⟩
  choose φ U hU hφ using hP'
  rcases SmoothBumpCovering.exists_isSubordinate I isClosed_univ fun x _ ↦ hU x with ⟨ι, b, hb⟩
  let ρ := b.toSmoothPartitionOfUnity
  refine ⟨fun x : M ↦ ∑ᶠ i, ρ i x • φ (b.c i) x, fun x₀ ↦ ?_⟩
  let g : ι → Germ (𝓝 x₀) F := fun i ↦ φ (b.c i)
  have :
    (fun x : M ↦ ∑ᶠ i, ρ i x • φ (b.c i) x : Germ (𝓝 x₀) F) ∈
      reallyConvexHull (smoothGerm I x₀) (g '' ρ.fintsupport x₀) :=
    ρ.germ_combine_mem fun i x ↦ φ (b.c i) x
  simp_rw [reallyConvex_iff_hull] at hP
  apply hP x₀; clear hP
  have H : g '' (ρ.fintsupport x₀) ⊆ {φ : (𝓝 x₀).Germ F | P ⟨x₀, φ⟩} := by
    rintro _ ⟨i, hi, rfl⟩
    exact hφ _ _ (hb.toSmoothPartitionOfUnity  i <| (ρ.mem_fintsupport_iff _ i).mp hi)
  exact reallyConvexHull_mono H this

end

end

section

variable {E₁ E₂ F : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {H₁ M₁ H₂ M₂ : Type*}
  [TopologicalSpace H₁] (I₁ : ModelWithCorners ℝ E₁ H₁)
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [TopologicalSpace H₂] (I₂ : ModelWithCorners ℝ E₂ H₂)
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]
  [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂] in
set_option backward.isDefEq.respectTransparency.types false in
theorem reallyConvex_contMDiffAtProd {x : M₁} (n : ℕ∞) :
    ReallyConvex (smoothGerm I₁ x) {φ : Germ (𝓝 x) (M₂ → F) | φ.ContMDiffAtProd I₁ I₂ n} := by
  classical
  rw [Nontrivial.reallyConvex_iff]
  rintro w _w_pos w_supp w_sum
  set fin_supp := (hasFiniteSupport_of_finsum_eq_one w_sum).toFinset with H
  have : (support fun i : (𝓝 x).Germ (M₂ → F) ↦ w i • i) ⊆ fin_supp := by
    rw [Set.Finite.coe_toFinset]
    exact support_smul_subset_left w id
  rw [finsum_eq_sum_of_support_subset _ this]
  apply Filter.Germ.ContMDiffAtProd.sum
  refine fun φ hφ ↦ (smoothGerm.contMDiffAt _).smul_prod (w_supp ?_)
  simpa [H] using hφ

omit [FiniteDimensional ℝ E₂] [IsManifold I₂ ∞ M₂] in
theorem exists_contMDiff_of_convex₂ {P : M₁ → (M₂ → F) → Prop} [SigmaCompactSpace M₁] [T2Space M₁]
    (hP : ∀ x, Convex ℝ {f | P x f}) {n : ℕ∞}
    (hP' : ∀ x : M₁, ∃ U ∈ 𝓝 x, ∃ f : M₁ → M₂ → F,
      CMDiff[U ×ˢ (univ : Set M₂)] n (uncurry f) ∧ ∀ y ∈ U, P y (f y)) :
    ∃ f : M₁ → M₂ → F, CMDiff n (uncurry f) ∧ ∀ x, P x (f x) := by
  let PP : (Σ x : M₁, Germ (𝓝 x) (M₂ → F)) → Prop := fun p ↦
    p.2.ContMDiffAtProd I₁ I₂ n ∧ P p.1 p.2.value
  have hPP : ∀ x : M₁, ReallyConvex (smoothGerm I₁ x) {φ | PP ⟨x, φ⟩} := fun x ↦ by
    apply ReallyConvex.inter
    · apply reallyConvex_contMDiffAtProd
    let v : Germ (𝓝 x) (M₂ → F) →ₛₗ[smoothGerm.valueRingHom I₁ x] M₂ → F := Filter.Germ.valueₛₗ I₁ x
    change ReallyConvex (smoothGerm I₁ x) (v ⁻¹' {y | P x y})
    dsimp only [← smoothGerm.valueOrderRingHom_toRingHom] at v
    apply ReallyConvex.preimageₛₗ
    rw [reallyConvex_iff_convex]
    apply hP
  have hPP' : ∀ x, ∃ f : M₁ → M₂ → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩ := fun x ↦ by
    rcases hP' x with ⟨U, U_in, f, hf, hf'⟩
    use f
    filter_upwards [eventually_mem_nhds_iff.mpr U_in] with y hy
    exact ⟨fun z ↦ hf.contMDiffAt (prod_mem_nhds hy univ_mem), hf' y (mem_of_mem_nhds hy)⟩
  rcases exists_of_convex hPP hPP' with ⟨f, hf⟩
  exact ⟨f, fun ⟨x, y⟩ ↦ (hf x).1 y, fun x ↦ (hf x).2⟩

omit [FiniteDimensional ℝ E₂] in
theorem exists_contDiff_of_convex₂ {P : E₁ → (E₂ → F) → Prop} (hP : ∀ x, Convex ℝ {f | P x f})
    {n : ℕ∞}
    (hP' : ∀ x : E₁, ∃ U ∈ 𝓝 x, ∃ f : E₁ → E₂ → F,
      ContDiffOn ℝ n (uncurry f) (U ×ˢ (univ : Set E₂)) ∧ ∀ y ∈ U, P y (f y)) :
    ∃ f : E₁ → E₂ → F, ContDiff ℝ n (uncurry f) ∧ ∀ x, P x (f x) := by
  simp_rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod] at hP'
  simp_rw [← contMDiff_iff_contDiff, modelWithCornersSelf_prod]
  rw [← chartedSpaceSelf_prod] at hP' ⊢
  -- Why does `simp_rw` not succeed here?
  exact exists_contMDiff_of_convex₂ 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) hP hP'

end
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_SmoothBarycentric
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open Set Function

open scoped Affine Matrix ContDiff

section BarycentricDet

variable (ι R k P : Type*) {M : Type*} [Ring R] [AddCommGroup M] [Module R M] [AffineSpace M P]

/-- The set of affine bases for an affine space. -/
def affineBases : Set (ι → P) :=
  {v | AffineIndependent R v ∧ affineSpan R (range v) = ⊤}

theorem affineBases_findim [Fintype ι] [Field k] [Module k M] [FiniteDimensional k M]
    (h : Fintype.card ι = Module.finrank k M + 1) :
    affineBases ι k P = {v | AffineIndependent k v} := by
  ext v
  simp only [affineBases, mem_ofPred_eq, and_iff_left_iff_imp]
  exact fun h_ind ↦ h_ind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr h

theorem mem_affineBases_iff [Fintype ι] [DecidableEq ι] [Nontrivial R] (b : AffineBasis ι R P)
    (v : ι → P) : v ∈ affineBases ι R P ↔ IsUnit (b.toMatrix v) :=
  (b.isUnit_toMatrix_iff v).symm

/-- If `P` is an affine space over the ring `R`, `v : ι → P` is an affine basis (for some indexing
set `ι`) and `p : P` is a point, then `eval_barycentric_coords ι R P p v` are the barycentric
coordinates of `p` with respect to the affine basis `v`.

Actually for convenience `eval_barycentric_coords` is defined even when `v` is not an affine basis.
In this case its value should be regarded as "junk". -/
def evalBarycentricCoords [DecidablePred (· ∈ affineBases ι R P)] (p : P) (v : ι → P) : ι → R :=
  if h : v ∈ affineBases ι R P then ((AffineBasis.mk v h.1 h.2).coords p : ι → R) else 0

@[simp]
theorem evalBarycentricCoords_apply_of_mem_bases [DecidablePred (· ∈ affineBases ι R P)] (p : P)
    {v : ι → P} (h : v ∈ affineBases ι R P) :
    evalBarycentricCoords ι R P p v = (AffineBasis.mk v h.1 h.2).coords p :=
  dite_eq_left h

@[simp]
theorem evalBarycentricCoords_apply_of_not_mem_bases [DecidablePred (· ∈ affineBases ι R P)] (p : P)
    {v : ι → P} (h : v ∉ affineBases ι R P) : evalBarycentricCoords ι R P p v = 0 :=
  dite_eq_right h

variable {ι R P}

theorem evalBarycentricCoords_eq_det [Fintype ι] [DecidableEq ι] (S : Type*) [Field S] [Module S M]
    [∀ v, Decidable (v ∈ affineBases ι S P)] (b : AffineBasis ι S P) (p : P) (v : ι → P) :
    evalBarycentricCoords ι S P p v =
      (b.toMatrix v).det⁻¹ • (b.toMatrix v)ᵀ.cramer (b.coords p) := by
  ext i
  by_cases h : v ∈ affineBases ι S P
  · simp only [evalBarycentricCoords, h, dite_eq_left, smul_eq_mul, Pi.smul_apply,
      AffineBasis.coords_apply]
    erw [← b.det_smul_coords_eq_cramer_coords ⟨v, h.1, h.2⟩ p]
    simp only [Pi.smul_apply, AffineBasis.coords_apply, smul_eq_mul]
    have hu := b.isUnit_toMatrix ⟨v, h.1, h.2⟩
    rw [Matrix.isUnit_iff_isUnit_det] at hu
    erw [← mul_assoc, ← Ring.inverse_eq_inv, Ring.inverse_mul_cancel _ hu, one_mul]
  · simp only [evalBarycentricCoords, h, smul_eq_mul, Pi.zero_apply, inv_eq_zero,
      dite_eq_right, not_false_iff, zero_eq_mul, Pi.smul_apply]
    left
    rwa [mem_affineBases_iff ι S P b v, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      Classical.not_not] at h

end BarycentricDet

namespace Matrix

variable (ι k : Type*) [Fintype ι] [DecidableEq ι] [NontriviallyNormedField k]

attribute [instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_det (m : WithTop ℕ∞) : ContDiff k m (det : Matrix ι ι k → k) := by
  suffices ∀ n : ℕ, ContDiff k m (det : Matrix (Fin n) (Fin n) k → k) by
    have h : (det : Matrix ι ι k → k) = det ∘ reindex (Fintype.equivFin ι) (Fintype.equivFin ι) :=
  by ext; simp
    rw [h]
    apply (this (Fintype.card ι)).comp
    exact contDiff_pi.mpr fun i ↦ contDiff_pi.mpr fun j ↦ contDiff_apply_apply _ _ _ _
  intro n
  induction n with
  | zero =>
    rw [coe_det_isEmpty]
    exact contDiff_const
  | succ n ih =>
  change ContDiff k m fun A : Matrix (Fin n.succ) (Fin n.succ) k ↦ A.det
  simp_rw [det_succ_column_zero]
  apply ContDiff.sum fun l _ ↦ ?_
  apply ContDiff.mul
  · refine contDiff_const.mul ?_
    apply contDiff_apply_apply
  · apply ih.comp
    refine contDiff_pi.mpr fun i ↦ contDiff_pi.mpr fun j ↦ ?_
    simp only [submatrix_apply]
    apply contDiff_apply_apply

end Matrix

section smooth_barycentric

variable (ι 𝕜 F : Type*)

variable [Fintype ι] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- An alternative approach would be to prove the affine version of `contDiffAt_map_inverse`
-- and prove that barycentric coordinates give a continuous affine equivalence to
-- `{ f : ι →₀ 𝕜 | f.sum = 1 }`.
-- This should obviate the need for the finite-dimensionality assumption.
theorem smooth_barycentric [DecidablePred (· ∈ affineBases ι 𝕜 F)] [FiniteDimensional 𝕜 F]
    (h : Fintype.card ι = Module.finrank 𝕜 F + 1) {n : WithTop ℕ∞} :
    ContDiffOn 𝕜 n (uncurry (evalBarycentricCoords ι 𝕜 F)) (@univ F ×ˢ affineBases ι 𝕜 F) := by
  classical
  obtain ⟨b⟩ : Nonempty (AffineBasis ι 𝕜 F) := AffineBasis.exists_affineBasis_of_finiteDimensional h
  simp_rw [uncurry_def, contDiffOn_pi, evalBarycentricCoords_eq_det 𝕜 b]
  intro i
  change ContDiffOn 𝕜 n
    (fun x : F × (ι → F)  ↦
      (Matrix.det (AffineBasis.toMatrix b x.snd))⁻¹ •
        (Matrix.cramer (AffineBasis.toMatrix b x.snd)ᵀ : (ι → 𝕜) → ι → 𝕜)
          ((AffineBasis.coords b : F → ι → 𝕜) x.1) i)
    (univ ×ˢ affineBases ι 𝕜 F)
  simp only [Matrix.cramer_transpose_apply]
  have hcont : ContDiff 𝕜 n fun x : ι → F ↦ b.toMatrix x :=
    contDiff_pi.mpr fun j ↦ contDiff_pi.mpr fun j' ↦
      ((smooth_barycentric_coord b j').of_le le_top).comp (contDiff_apply 𝕜 F j)
  have h_snd : ContDiff 𝕜 n fun x : F × (ι → F) ↦ b.toMatrix x.snd := hcont.comp contDiff_snd
  apply ContDiffOn.mul
  · apply ((Matrix.smooth_det ι 𝕜 n).comp h_snd).contDiffOn.inv
    rintro ⟨p, v⟩ hpv
    have hv : IsUnit (b.toMatrix v) := by simpa [mem_affineBases_iff ι 𝕜 F b v] using hpv
    rw [← isUnit_iff_ne_zero, comp_apply, ← Matrix.isUnit_iff_isUnit_det]
    exact hv
  · refine ((Matrix.smooth_det ι 𝕜 n).comp ?_).contDiffOn
    refine contDiff_pi.mpr fun j ↦ contDiff_pi.mpr fun j' ↦ ?_
    simp only [Matrix.updateRow_apply]
    simp only [AffineBasis.toMatrix_apply, AffineBasis.coords_apply]
    by_cases hij : j = i
    · simp only [hij, ite_true, if_true]
      exact (smooth_barycentric_coord b j').fst'.of_le le_top
    · simp only [hij, ite_false, if_false]
      exact ((smooth_barycentric_coord b j').of_le le_top).comp (contDiff_pi.mp contDiff_snd j)

end smooth_barycentric
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Topology_Path
attribute [-instance] _root_.hasUncurryLoop _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

open Set Function

open scoped Topology unitInterval

noncomputable section

variable {X X' Y Z : Type*} [TopologicalSpace X]
  [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]

namespace Path

variable {x : X} {γ γ' : Path x x}

/-- A loop evaluated at `t / t` is equal to its endpoint. Note that `t / t = 0` for `t = 0`. -/
@[simp]
theorem extend_div_self (γ : Path x x) (t : ℝ) : γ.extend (t / t) = x := by
  by_cases h : t = 0 <;> simp [h]

/-- Concatenation of two loops which moves through the first loop on `[0, t₀]` and
through the second one on `[t₀, 1]`. All endpoints are assumed to be the same so that this
function is also well-defined for `t₀ ∈ {0, 1}`.
`strans` stands either for a *s*kewed transitivity, or a transitivity with different *s*peeds. -/
def strans (γ γ' : Path x x) (t₀ : I) : Path x x where
  toFun t := if t ≤ t₀ then γ.extend (t / t₀) else γ'.extend ((t - t₀) / (1 - t₀))
  continuous_toFun := by
    refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
    · continuity
    · continuity
    · simp only [extend_div_self, Icc.mk_zero, zero_le_one, zero_div, forall_eq,
        extend_apply, Path.source, left_mem_Icc, sub_self]
  source' := by simp
  target' := by
    simp +contextual only [unitInterval.le_one'.ge_iff_eq.trans eq_comm,
      extend_div_self, Icc.coe_one, imp_true_iff, ite_eq_right_iff]

@[simp]
theorem strans_of_ge {t t₀ : I} (h : t₀ ≤ t) :
    γ.strans γ' t₀ t = γ'.extend ((t - t₀) / (1 - t₀)) := by
  simp only [Path.coe_mk_mk, Path.strans, ite_eq_right_iff]
  intro h2; obtain rfl := le_antisymm h h2; simp

@[simp]
theorem strans_zero (γ γ' : Path x x) : γ.strans γ' 0 = γ' := by
  ext t
  simp +contextual only [strans_of_ge unitInterval.nonneg', Icc.coe_zero, div_one,
    extend_extends', sub_zero]

@[simp]
theorem strans_one {x : X} (γ γ' : Path x x) : γ.strans γ' 1 = γ := by
  ext t
  simp only [strans, unitInterval.le_one', Path.coe_mk_mk, ite_eq_left, div_one, extend_extends',
    Icc.coe_one]

@[simp]
theorem refl_strans_refl {x : X} {t₀ : I} : (refl x).strans (refl x) t₀ = refl x := by
  ext s
  simp [strans]

theorem Continuous.path_strans {X Y : Type*} [UniformSpace X]
    [LocallyCompactSpace X] [UniformSpace Y] {f : X → Y} {t : X → I} {s : X → I}
    {γ γ' : ∀ x, Path (f x) (f x)} (hγ : Continuous ↿γ) (hγ' : Continuous ↿γ')
    (hγ0 : ∀ ⦃x s⦄, t x = 0 → γ x s = f x) (hγ'1 : ∀ ⦃x s⦄, t x = 1 → γ' x s = f x)
    (ht : Continuous t) (hs : Continuous s) :
    Continuous fun x ↦ strans (γ x) (γ' x) (t x) (s x) := by
  have hγ0 : ∀ {x₀}, t x₀ = 0 →
      TendstoUniformly (fun x ↦ γ x) (fun _ ↦ f x₀) (𝓝 x₀) := fun h₀ ↦ by
    convert Continuous.tendstoUniformly (fun x ↦ γ x) hγ _; rw [hγ0 h₀]
  have hγ'1 : ∀ {x₀}, t x₀ = 1 →
      TendstoUniformly (fun x ↦ γ' x) (fun _ ↦ f x₀) (𝓝 x₀) := fun h₀ ↦ by
    convert Continuous.tendstoUniformly (fun x ↦ γ' x) hγ' _; rw [hγ'1 h₀]
  refine Continuous.if_le ?_ ?_ hs ht ?_
  · rw [continuous_iff_continuousAt]
    intro x
    refine (continuous_subtype_val.comp hs).continuousAt.comp_div_cases (fun x s ↦ (γ x).extend s)
      (continuous_subtype_val.comp ht).continuousAt ?_ ?_
    · intro _
      refine ContinuousAt.pathExtend _ ?_ continuousAt_snd
      exact hγ.continuousAt.comp (continuousAt_fst.fst.prodMk continuousAt_snd)
    · intro h
      have ht : t x = 0 := Subtype.ext h
      apply Filter.Tendsto.pathExtend
      rw [(projIcc_surjective _).filter_map_top, extend_zero]
      exact tendsto_prod_top_iff.mpr (hγ0 ht)
  · rw [continuous_iff_continuousAt]
    intro x
    refine (continuous_subtype_val.comp hs).sub (continuous_subtype_val.comp ht)
      |>.continuousAt.comp_div_cases (fun x s ↦ (γ' x).extend s)
      (continuous_const.sub <| continuous_subtype_val.comp ht).continuousAt ?_ ?_
    · intro _
      refine ContinuousAt.pathExtend _ ?_ continuousAt_snd
      exact hγ'.continuousAt.comp (continuousAt_fst.fst.prodMk continuousAt_snd)
    · intro h
      have ht : t x = 1 := Subtype.ext (sub_eq_zero.mp h).symm
      apply Filter.Tendsto.pathExtend
      rw [(projIcc_surjective _).filter_map_top, extend_zero]
      exact tendsto_prod_top_iff.mpr (hγ'1 ht)
  · rintro x h; rw [h, sub_self, zero_div, extend_div_self, extend_zero]

end Path
end
end
end

section
-- module Solutions.OAIQ249_SI.Loops_Surrounding
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Surrounding families of loops

In order to carry out the corrugation technique of convex integration, one needs to a family of
loops with various prescribed properties.

This file begins the work of constructing such a family.

The key definitions are:
 * `Surrounded`
 * `SurroundingPts`
 * `SurroundingFamily`

The key results are:
 * `surrounded_iff_mem_interior_convexHull_aff_basis`
 * `surrounded_of_convexHull`
 * `smooth_surrounding`
 * `eventually_surroundingPts_of_tendsto_of_tendsto`
 * `surrounding_loop_of_convexHull`
 * `local_loops`
 * `satisfied_or_refund`
 * `extend_loops`
 * `exists_surrounding_loops`
-/

section

-- to obtain that normed spaces are locally connected
open Set Function Module Int Prod Path Filter
open scoped Topology unitInterval ContDiff

namespace IsPathConnected

-- we redo `exists_path_through_family` to use `def`s
variable {X : Type*} [TopologicalSpace X] {F : Set X}

/-- An arbitrary path joining `x` and `y` in `F`. -/
noncomputable def somePath (hF : IsPathConnected F) {x y : X} (hx : x ∈ F) (hy : y ∈ F) :
    Path x y :=
  (hF.joinedIn x hx y hy).somePath

theorem somePath_mem (hF : IsPathConnected F) {x y : X} (hx : x ∈ F) (hy : y ∈ F) (t : I) :
    hF.somePath hx hy t ∈ F :=
  JoinedIn.somePath_mem _ t

theorem range_somePath_subset (hF : IsPathConnected F) {x y : X} (hx : x ∈ F) (hy : y ∈ F) :
    range (hF.somePath hx hy) ⊆ F := by rintro _ ⟨t, rfl⟩; apply somePath_mem

open Fin.NatCast in -- TODO: fix this
/-- A path through `p 0`, ..., `p n`. Usually this is used with `n := m`. -/
noncomputable def pathThrough (hF : IsPathConnected F) {m : ℕ} {p : Fin (m + 1) → X}
    (hp : ∀ i, p i ∈ F) : ∀ n : ℕ, Path (p 0) (p n)
  | 0 => Path.refl (p 0)
  | n + 1 => (pathThrough hF hp n).trans <| hF.somePath (hp _) (hp _)

attribute [simp] Path.trans_range

theorem range_pathThrough_subset (hF : IsPathConnected F) {m : ℕ} {p : Fin (m + 1) → X}
    (hp : ∀ i, p i ∈ F) : ∀ {n : ℕ}, range (hF.pathThrough hp n) ⊆ F
  | 0 => by simp [pathThrough, hp]
  | n + 1 => by simpa [pathThrough, hp, range_somePath_subset]
    using range_pathThrough_subset hF hp (n := n)

open Fin.NatCast in -- TODO: fix this
theorem mem_range_pathThrough' (hF : IsPathConnected F) {m : ℕ} {p : Fin (m + 1) → X}
    (hp : ∀ i, p i ∈ F) {i n : ℕ} (h : i ≤ n) : p i ∈ range (hF.pathThrough hp n) := by
  induction h with
  | refl => exact ⟨1, by simp⟩
  | step _ ih => simp only [pathThrough, Path.trans_range, mem_union, ih, true_or]

theorem mem_range_pathThrough (hF : IsPathConnected F) {m : ℕ} {p : Fin (m + 1) → X}
    (hp : ∀ i, p i ∈ F) {i : Fin (m + 1)} : p i ∈ range (hF.pathThrough hp m) := by
  convert hF.mem_range_pathThrough' hp (Nat.le_of_lt_succ i.2); simp [Fin.cast_val_eq_self]

end IsPathConnected

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

set_option hygiene false
@[inherit_doc] local notation "d" => finrank ℝ F
set_option hygiene true

/-
The definition below gets a prime because it clashes with a manifold definition
in mathlib which is in the root namespace.
XXX: this is no longer true.
-/
/-- `f` is smooth at `x` if `f` is smooth on some neighborhood of `x`. -/
def SmoothAt' (f : E → F) (x : E) : Prop :=
  ∃ s ∈ 𝓝 x, ContDiffOn ℝ ∞ f s

section SurroundingPoints

set_option hygiene false
@[inherit_doc] local notation "ι" => Fin (d + 1)
set_option hygiene true

-- def:surrounds_points
/-- `p` is a collection of points surrounding `f` with weights `w` (that are positive and sum to 1)
if the weighted average of the points `p` is `f` and the points `p` form an affine basis of the
space. -/
structure SurroundingPts (f : F) (p : ι → F) (w : ι → ℝ) : Prop where
  indep : AffineIndependent ℝ p
  w_pos : ∀ i, 0 < w i
  w_sum : ∑ i, w i = 1
  avg : ∑ i, w i • p i = f

theorem SurroundingPts.tot [FiniteDimensional ℝ F] {f : F} {p : ι → F} {w : ι → ℝ}
    (h : SurroundingPts f p w) : affineSpan ℝ (range p) = ⊤ :=
  h.indep.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (Fintype.card_fin _)

theorem SurroundingPts.mem_affineBases [FiniteDimensional ℝ F] {f : F} {p : ι → F} {w : ι → ℝ}
    (h : SurroundingPts f p w) : p ∈ affineBases ι ℝ F :=
  ⟨h.indep, h.tot⟩

theorem SurroundingPts.coord_eq_w [FiniteDimensional ℝ F] {f : F} {p : ι → F} {w : ι → ℝ}
    (h : SurroundingPts f p w) : (⟨p, h.indep, h.tot⟩ : AffineBasis ι ℝ F).coords f = w := by
  let b : AffineBasis ι ℝ F := ⟨p, h.indep, h.tot⟩
  change b.coords f = w
  ext i
  rw [← h.avg, ← Finset.univ.affineCombination_eq_linear_combination _ w h.w_sum,
    AffineBasis.coords_apply]
  exact AffineBasis.coord_apply_combination_of_mem _ (Finset.mem_univ i) h.w_sum

-- `lem:smooth_barycentric_coord`
theorem smooth_surrounding [FiniteDimensional ℝ F] {x : F} {p : ι → F} {w : ι → ℝ}
    (h : SurroundingPts x p w) :
    ∃ W : F → (ι → F) → ι → ℝ, ∀ᶠ yq : F × (ι → F) in 𝓝 (x, p),
      SmoothAt' (uncurry W) yq ∧ (∀ i, 0 < W yq.1 yq.2 i) ∧ ∑ i, W yq.1 yq.2 i = 1 ∧
        ∑ i, W yq.1 yq.2 i • yq.2 i = yq.1 := by
  classical
  use evalBarycentricCoords ι ℝ F
  let V : Set (ι → ℝ) := Set.pi Set.univ fun _ ↦ Ioi (0 : ℝ)
  let W' : F × (ι → F) → ι → ℝ := uncurry (evalBarycentricCoords ι ℝ F)
  let A : Set (F × (ι → F)) := univ ×ˢ affineBases ι ℝ F
  let U : Set (F × (ι → F)) := A ∩ W' ⁻¹' V
  have hι : Fintype.card ι = d + 1 := Fintype.card_fin _
  have hp : p ∈ affineBases ι ℝ F := h.mem_affineBases
  have hV : IsOpen V := isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioi
  have hW' : ContinuousOn W' A := (smooth_barycentric ι ℝ F hι (n := 0)).continuousOn
  have hxp : W' (x, p) ∈ V := by simp [W', V, hp, h.coord_eq_w, h.w_pos]
  have hA : IsOpen A := by
    simp only [A, affineBases_findim ι ℝ F hι]
    exact isOpen_univ.prod isOpen_setOfPred_affineIndependent
  have hU₂ : IsOpen U := hW'.isOpen_inter_preimage hA hV
  have hU₃ : U ∈ 𝓝 (x, p) :=
    mem_nhds_iff.mpr ⟨U, le_refl U, hU₂, Set.mem_inter (by simp [hp, A]) (mem_preimage.mpr hxp)⟩
  apply eventually_of_mem hU₃
  rintro ⟨y, q⟩ hyq
  have hq : q ∈ affineBases ι ℝ F := by simpa [A] using inter_subset_left hyq
  have hyq' : (y, q) ∈ W' ⁻¹' V := inter_subset_right hyq
  refine ⟨⟨U, mem_nhds_iff.mpr ⟨U, le_refl U, hU₂, hyq⟩,
    ((smooth_barycentric ι ℝ F hι).mono inter_subset_left).of_le le_top⟩, ?_, ?_, ?_⟩
  · simpa [V] using! hyq'
  · simp [hq]
  · simp only [hq, evalBarycentricCoords_apply_of_mem_bases, AffineBasis.coords_apply]
    exact AffineBasis.linear_combination_coord_eq_self _ y

theorem smooth_surroundingPts [FiniteDimensional ℝ F] {x : F} {p : ι → F} {w : ι → ℝ}
    (h : SurroundingPts x p w) :
    ∃ W : F → (ι → F) → ι → ℝ,
      ∀ᶠ yq : F × (ι → F) in 𝓝 (x, p),
        SmoothAt' (uncurry W) yq ∧ SurroundingPts yq.1 yq.2 (W yq.1 yq.2) := by
  refine Exists.imp (fun W hW ↦ ?_) (smooth_surrounding h)
  rw [nhds_prod_eq] at hW ⊢
  have := (IsOpen.eventually_mem isOpen_setOfPred_affineIndependent h.indep).prod_inr (𝓝 x)
  filter_upwards [hW, this]; rintro ⟨y, q⟩ ⟨hW, h2W, h3W, hq⟩ h2q
  exact ⟨hW, h2q, h2W, h3W, hq⟩

theorem surroundingPts_evalBarycentricCoords_iff (q : F) (v : ι → F)
    [DecidablePred (· ∈ affineBases ι ℝ F)] :
    SurroundingPts q v (evalBarycentricCoords ι ℝ F q v) ↔
      ∀ i, 0 < evalBarycentricCoords ι ℝ F q v i := by
  refine ⟨fun h ↦ h.w_pos, fun h ↦ ?_⟩
  have hv : v ∈ affineBases ι ℝ F := by
    by_contra contra
    simpa [evalBarycentricCoords_apply_of_not_mem_bases ι ℝ F q contra] using h 0
  have hv' : ∑ i, evalBarycentricCoords ι ℝ F q v i = 1 := by
    simp [evalBarycentricCoords_apply_of_mem_bases ι ℝ F q hv]
  refine ⟨hv.1, h, hv', ?_⟩
  simp_rw [← Finset.univ.affineCombination_eq_linear_combination v _ hv',
    evalBarycentricCoords_apply_of_mem_bases ι ℝ F q hv]
  convert! AffineBasis.affineCombination_coord_eq_self _ q
  rfl

end SurroundingPoints

section SurroundingPointsLimits

variable {X Y : Type*} [FiniteDimensional ℝ F]

local notation:arg "ι" => Fin (finrank ℝ F + 1)

theorem eventually_surroundingPts_of_tendsto_of_tendsto {l : Filter X} {m : Filter Y} {v : ι → F}
    {q : F} {p : ι → X → F} {f : Y → F} (hq : ∃ w, SurroundingPts q v w)
    (hp : ∀ i, Tendsto (p i) l (𝓝 (v i))) (hf : Tendsto f m (𝓝 q)) :
    ∀ᶠ z : X × Y in l ×ˢ m, ∃ w, SurroundingPts (f z.2) (fun i ↦ p i z.1) w := by
  classical
  obtain ⟨w, hw⟩ := hq
  let V : Set (ι → ℝ) := Set.pi Set.univ fun _ ↦ Ioi (0 : ℝ)
  let W' : F × (ι → F) → ι → ℝ := uncurry (evalBarycentricCoords ι ℝ F)
  let A : Set (F × (ι → F)) := (univ : Set F) ×ˢ affineBases ι ℝ F
  let S : Set (F × (ι → F)) := W' ⁻¹' V
  have hι : Fintype.card ι = finrank ℝ F + 1 := Fintype.card_fin _
  have hq' : v ∈ affineBases ι ℝ F := hw.mem_affineBases
  have hqv : (q, v) ∈ A := by simp [A, hq']
  have hxp : W' (q, v) ∈ V := by simp [W', V, hq', hw.coord_eq_w, hw.w_pos]
  have hV' : V ∈ 𝓝 (W' (q, v)) := (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioi).mem_nhds hxp
  have hA : IsOpen A := by
    simp only [A, affineBases_findim ι ℝ F hι]
    exact isOpen_univ.prod isOpen_setOfPred_affineIndependent
  have hW' : ContinuousAt W' (q, v) :=
    (smooth_barycentric ι ℝ F hι (n := 0)).continuousOn.continuousAt
      (mem_nhds_iff.mpr ⟨A, Subset.rfl, hA, hqv⟩)
  have hS : S ∈ 𝓝 (q, v) := hW'.preimage_mem_nhds hV'
  obtain ⟨n₁, hn₁, n₂, hn₂, hS'⟩ := mem_nhds_prod_iff.mp hS
  have hn₁' := tendsto_def.mp hf _ hn₁
  have hn₂' := tendsto_def.mp (tendsto_pi_nhds.mpr hp) _ hn₂
  have come_on : (swap p ⁻¹' n₂) ×ˢ (f ⁻¹' n₁) ∈ l  ×ˢ m :=
    mem_prod_iff.mpr ⟨_, hn₂', _, hn₁', Subset.rfl⟩
  filter_upwards [come_on]
  rintro ⟨y₂, y₁⟩ ⟨hy₂ : swap p y₂ ∈ n₂, hy₁ : f y₁ ∈ n₁⟩
  refine ⟨W' (f y₁, swap p y₂),
    (surroundingPts_evalBarycentricCoords_iff (f y₁) (swap p y₂)).mpr fun i ↦ ?_⟩
  change W' (f y₁, swap p y₂) i ∈ Ioi (0 : ℝ)
  suffices (f y₁, swap p y₂) ∈ S from this i (mem_univ _)
  apply hS'
  simp [hy₁, hy₂]

theorem eventually_surroundingPts_of_tendsto_of_tendsto' {v : ι → F} {q : F} {p : ι → X → F}
    {l : Filter X} {f : X → F} (hq : ∃ w, SurroundingPts q v w)
    (hp : ∀ i, Tendsto (p i) l (𝓝 (v i))) (hf : Tendsto f l (𝓝 q)) :
    ∀ᶠ y in l, ∃ w, SurroundingPts (f y) (fun i ↦ p i y) w := by
  have := eventually_surroundingPts_of_tendsto_of_tendsto hq hp hf
  simp_rw [eventually_iff_exists_mem, mem_prod_iff] at this
  obtain ⟨nnn, ⟨n₁, hn₁, n₂, hn₂, hh⟩, h⟩ := this
  rw [eventually_iff_exists_mem]
  exact ⟨n₁ ∩ n₂, inter_mem hn₁ hn₂, fun y hy ↦ h (y, y) (by apply hh; simpa using hy)⟩

end SurroundingPointsLimits

namespace Loop

variable {γ γ' : Loop F} {x y : F} {t : ℝ}

/-- A loop `γ` surrounds a point `x` if `x` is surrounded by values of `γ`. -/
def Surrounds (γ : Loop F) (x : F) : Prop :=
  ∃ t w : Fin (d + 1) → ℝ, SurroundingPts x (γ ∘ t) w

theorem surrounds_iff_range_subset_range :
    γ.Surrounds x ↔
      ∃ (p : Fin (d + 1) → F) (w : Fin (d + 1) → ℝ), SurroundingPts x p w ∧ range p ⊆ range γ := by
  constructor
  · exact fun ⟨t, w, h⟩ ↦ ⟨γ ∘ t, w, h, range_comp_subset_range _ _⟩
  · rintro ⟨p, w, h₀, h₁⟩
    rw [range_subset_iff] at h₁
    choose t ht using h₁
    have hpt : γ ∘ t = p := funext ht
    exact ⟨t, w, hpt.symm ▸ h₀⟩

theorem affineEquiv_surrounds_iff (e : F ≃ᵃ[ℝ] F) :
    γ.Surrounds x ↔ (γ.transform e).Surrounds (e x) := by
  suffices ∀ (γ : Loop F) (x) (e : F ≃ᵃ[ℝ] F), γ.Surrounds x → (γ.transform e).Surrounds (e x) by
    refine ⟨this γ x e, fun h ↦ ?_⟩
    specialize this (γ.transform e) (e x) e.symm h
    rw [AffineEquiv.symm_apply_apply] at this
    convert this
    ext
    simp
  rintro γ x e ⟨t, w, indep, w_pos, w_sum, rfl⟩
  refine ⟨t, w, ⟨e.affineIndependent_iff.mpr indep, w_pos, w_sum, ?_⟩⟩
  simp only [← Finset.affineCombination_eq_linear_combination _ _ _ w_sum]
  erw [Finset.map_affineCombination _ (γ ∘ t) _ w_sum (e : F →ᵃ[ℝ] F)]
  congr

omit [NormedSpace ℝ F] in
@[simp]
theorem zero_vadd : (0 : F) +ᵥ γ = γ := by
  ext t
  simp

theorem vadd_surrounds : γ.Surrounds x ↔ (y +ᵥ γ).Surrounds (y + x) := by
  rw [add_comm]
  convert! affineEquiv_surrounds_iff (AffineEquiv.vaddConst ℝ y) using 2
  all_goals try with_reducible_and_instances rfl
  ext u
  simp [add_comm y]

theorem Surrounds.vadd (h : γ.Surrounds x) : (y +ᵥ γ).Surrounds (y + x) :=
  vadd_surrounds.mp h

theorem Surrounds.vadd0 (h : γ.Surrounds 0) : (y +ᵥ γ).Surrounds y := by
  convert h.vadd
  rw [add_zero]

theorem Surrounds.smul0 (h : γ.Surrounds 0) (ht : t ≠ 0) : (t • γ).Surrounds 0 := by
  rw [affineEquiv_surrounds_iff (AffineEquiv.homothetyUnitsMulHom (0 : F) (Units.mk0 t ht)⁻¹),
    AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply_same]
  convert h
  ext u
  simp [AffineMap.homothety_apply, smul_smul, inv_mul_cancel₀ ht]

theorem Surrounds.mono (h : γ.Surrounds x) (h2 : range γ ⊆ range γ') : γ'.Surrounds x := by
  revert h; simp_rw [Loop.surrounds_iff_range_subset_range]
  refine Exists.imp fun t ↦ ?_
  refine Exists.imp fun w ↦ ?_
  exact And.imp_right fun h3 ↦ Subset.trans h3 h2

protected theorem Surrounds.reparam (h : γ.Surrounds x) {φ : EquivariantMap} (hφ : Continuous φ) :
    (γ.reparam φ).Surrounds x := by
  refine h.mono ?_
  convert! subset_of_eq (range_comp γ φ).symm
  rw [(φ.surjective hφ).range_eq, image_univ]

/-- This is only a stepping stone potentially useful for `SurroundingFamily.surrounds_of_close`,
  but not needed by itself. -/
theorem Surrounds.eventually_surrounds [FiniteDimensional ℝ F] (h : γ.Surrounds x) :
    ∃ ε > 0,
      ∀ (γ' : Loop F) (y : F), (∀ z, dist (γ' z) (γ z) < ε) → dist y x < ε → γ'.Surrounds y := by
  obtain ⟨t, w, h⟩ := h
  obtain ⟨W, hW⟩ := smooth_surroundingPts h
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp hW
  refine ⟨ε, hε, fun γ' y hγ' hy ↦ ⟨t, W y (γ' ∘ t), ?_⟩⟩
  refine (@h ⟨y, γ' ∘ t⟩ ?_).2
  simp_rw [Prod.dist_eq, max_lt_iff, dist_pi_lt_iff hε]
  exact ⟨hy, fun b ↦ hγ' (t b)⟩

end Loop

section surroundingLoop

variable {O : Set F} {b : F} {p : Fin (d + 1) → F} (O_conn : IsPathConnected O)
  (hp : ∀ i, p i ∈ O) (hb : b ∈ O)

/-- witness of `surrounding_loop_of_convexHull` -/
def surroundingLoop : ℝ → Loop F :=
  Loop.roundTripFamily <| (O_conn.somePath hb (hp 0)).trans <| O_conn.pathThrough hp d

variable {O_conn hp hb}

/-- TODO: continuity note -/
@[fun_prop]
theorem continuous_surroundingLoop : Continuous ↿(surroundingLoop O_conn hp hb) := by
  unfold surroundingLoop; fun_prop

@[simp]
theorem surroundingLoop_zero_right (t : ℝ) : surroundingLoop O_conn hp hb t 0 = b :=
  Loop.roundTripFamily_based_at t

@[simp]
theorem surroundingLoop_zero_left (s : ℝ) : surroundingLoop O_conn hp hb 0 s = b := by
  simp only [surroundingLoop, Loop.roundTripFamily_zero]; rfl

end surroundingLoop

/-- `γ` forms a family of loops surrounding `g` with base `b`.
In contrast to the notes we assume that `base` and `t₀` hold universally. -/
structure SurroundingFamily (g b : E → F) (γ : E → ℝ → Loop F) (U : Set E) : Prop where
  protected base : ∀ (x : E) (t : ℝ), γ x t 0 = b x
  protected t₀ : ∀ (x : E) (s : ℝ), γ x 0 s = b x
  protected projI : ∀ (x : E) (t : ℝ) (s : ℝ), γ x (projI t) s = γ x t s
  protected surrounds : ∀ x ∈ U, (γ x 1).Surrounds <| g x
  protected cont : Continuous ↿γ

namespace SurroundingFamily

variable {g b : E → F} {γ : E → ℝ → Loop F} {U : Set E}

omit [NormedSpace ℝ E]

protected theorem one (h : SurroundingFamily g b γ U) (x : E) (t : ℝ) : γ x t 1 = b x := by
  rw [Loop.one, h.base]

-- proof using `surrounds_of_close`
-- begin
--   obtain ⟨ε, hε, hcε, hγε⟩ := h.surrounds_of_close hg isOpen_univ,
--   exact ⟨ε, λ x, hε x (mem_univ _), continuous_iff_continuous_on_univ.mpr hcε,
--     λ x, hγε x (mem_univ _)⟩
-- end
/-- A surrounding family induces a family of paths from `b x` to `b x`.
We defined the concatenation we need on `path`, so we need to turn a surrounding
family into the family of paths. -/
@[simps]
protected def path (h : SurroundingFamily g b γ U) (x : E) (t : ℝ) : Path (b x) (b x) where
  toFun s := γ x t s
  continuous_toFun :=
    (h.cont.comp₃ continuous_const continuous_const continuous_id).comp continuous_subtype_val
  source' := h.base x t
  target' := h.one x t

@[fun_prop]
theorem continuous_path {X : Type*} [TopologicalSpace X] (h : SurroundingFamily g b γ U)
    {t : X → ℝ} {f : X → E} {s : X → I} (hf : Continuous f) (ht : Continuous t)
    (hs : Continuous s) : Continuous fun x ↦ h.path (f x) (t x) (s x) :=
  h.cont.comp₃ hf ht hs.subtype_val

@[simp]
theorem path_extend_fract (h : SurroundingFamily g b γ U) (t s : ℝ) (x : E) :
    (h.path x t).extend (fract s) = γ x t s := by
  rw [extend_apply _ (unitInterval.fract_mem s), ← Loop.fract_eq]; rfl

@[simp]
theorem range_path (h : SurroundingFamily g b γ U) (x : E) (t : ℝ) :
    range (h.path x t) = range (γ x t) := by
  simp only [Loop.range_eq_image, SurroundingFamily.path, Path.coe_mk_mk]
  erw [range_comp]
  simp only [Subtype.range_coe]

@[simp]
theorem path_t₀ (h : SurroundingFamily g b γ U) (x : E) : h.path x 0 = .refl (b x) := by
  ext t
  exact h.t₀ x t

end SurroundingFamily

variable {g b : E → F} {U K C : Set E} {Ω : Set (E × F)}

/-- Function used in `satisfied_or_refund`. Rename. -/
def ρ (t : ℝ) : ℝ :=
  projI <| 2 * (1 - t)

attribute [fun_prop] continuous_projI

@[fun_prop]
theorem continuous_ρ : Continuous ρ := by unfold ρ; fun_prop

@[simp]
theorem ρ_eq_one {x : ℝ} : ρ x = 1 ↔ x ≤ 1 / 2 := by
  rw [ρ, projI_eq_one]
  constructor <;> intros <;> linarith

@[simp]
theorem ρ_eq_one_of_le {x : ℝ} (h : x ≤ 1 / 2) : ρ x = 1 :=
  ρ_eq_one.mpr h

@[simp]
theorem ρ_eq_one_of_nonpos {x : ℝ} (h : x ≤ 0) : ρ x = 1 :=
  ρ_eq_one_of_le <| h.trans <| by norm_num

@[simp]
theorem ρ_eq_zero {x : ℝ} : ρ x = 0 ↔ 1 ≤ x := by
  rw [ρ, projI_eq_zero]
  constructor <;> intros <;> linarith

@[simp]
theorem ρ_eq_zero_of_le {x : ℝ} (h : 1 ≤ x) : ρ x = 0 :=
  ρ_eq_zero.mpr h

section satisfied_or_refund

variable {γ₀ γ₁ : E → ℝ → Loop F}

variable (h₀ : SurroundingFamily g b γ₀ U) (h₁ : SurroundingFamily g b γ₁ U)

/-- The homotopy of surrounding families of loops used in lemma `satisfied_or_refund`.
  Having this as a separate definition is useful, because the construction actually gives some
  more information about the homotopy than the theorem `satisfied_or_refund` gives. -/
def sfHomotopy (τ : ℝ) (x : E) (t : ℝ) :=
  Loop.ofPath <|
    (h₀.path x <| ρ τ * projI t).strans (h₁.path x <| ρ (1 - τ) * projI t) <|
      projIcc 0 1 zero_le_one (1 - τ)

variable {h₀ h₁}

omit [NormedSpace ℝ E]

@[simp]
theorem sfHomotopy_zero : sfHomotopy h₀ h₁ 0 = γ₀ := by
  ext x t s
  simp only [sfHomotopy, one_mul, ρ_eq_one_of_nonpos le_rfl, SurroundingFamily.path_extend_fract,
             sub_zero, Loop.ofPath_apply, Icc.mk_one, projIcc_right, Path.strans_one, h₀.projI]

@[simp]
theorem sfHomotopy_one : sfHomotopy h₀ h₁ 1 = γ₁ := by
  ext x t s
  simp only [sfHomotopy, Path.strans_zero, Icc.mk_zero, one_mul, ρ_eq_one_of_nonpos le_rfl,
    SurroundingFamily.path_extend_fract, projIcc_left, Loop.ofPath_apply, sub_self, h₁.projI]

attribute [fun_prop] continuous_projIcc

@[fun_prop]
theorem Continuous.sfHomotopy {X : Type*} [UniformSpace X]
    [LocallyCompactSpace X] {τ t s : X → ℝ} {f : X → E} (hτ : Continuous τ) (hf : Continuous f)
    (ht : Continuous t) (hs : Continuous s) :
    Continuous fun x ↦ sfHomotopy h₀ h₁ (τ x) (f x) (t x) (s x) := by
  refine Continuous.ofPath _ _ _ ?_ hs
  refine Continuous.path_strans ?_ ?_ ?_ ?_ ?_ continuous_snd
  · fun_prop
  · fun_prop
  · intro x s hs; simp only [projIcc_eq_zero, sub_nonpos] at hs
    simp only [hs, h₀.t₀, MulZeroClass.zero_mul, SurroundingFamily.path_apply, ρ_eq_zero_of_le]
  · intro x s hs; simp only [projIcc_eq_one] at hs
    simp only [hs, h₁.t₀, MulZeroClass.zero_mul, SurroundingFamily.path_apply, ρ_eq_zero_of_le]
  · fun_prop

/-- In this lemmas and the lemmas below we add `FiniteDimensional ℝ E` so that we can conclude
 `LocallyCompactSpace E`. -/
@[fun_prop]
theorem continuous_sfHomotopy [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Continuous ↿(sfHomotopy h₀ h₁) := by fun_prop

end satisfied_or_refund

def ContinuousGerm {x : E} (φ : Germ (𝓝 x) (ℝ → Loop F)) : Prop :=
  Quotient.liftOn' φ
    (fun γ ↦ ∀ t s : ℝ, ContinuousAt (fun p : E × ℝ × ℝ ↦ γ p.1 p.2.1 p.2.2) (x, t, s))
    (by
      rintro γ γ' (h : {x | γ x = γ' x} ∈ 𝓝 x)
      ext
      refine forall_congr' fun t ↦ forall_congr' fun s ↦ continuousAt_congr ?_
      rw [nhds_prod_eq]
      apply mem_of_superset (Filter.prod_mem_prod h univ_mem)
      rintro ⟨x', p⟩ ⟨hx' : γ x' = γ' x', -⟩
      simp only [mem_ofPred_eq, hx'])

variable (g b Ω)
omit [NormedSpace ℝ E]

structure LoopFamilyGerm (x : E) (φ : Germ (𝓝 x) (ℝ → Loop F)) : Prop where
  base : ∀ t, φ.value t 0 = b x
  t₀ : ∀ s, φ.value 0 s = b x
  projI : ∀ (t : ℝ) (s : ℝ), φ.value (projI t) s = φ.value t s
  cont : ContinuousGerm φ
end
end
end

section
-- module Solutions.OAIQ249_SI.Loops_Reparametrization
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# The reparametrization lemma

This file contains a proof of Gromov's parametric reparametrization lemma. It concerns the behaviour
of the average value of a loop `γ : S¹ → F` when the loop is reparametrized by precomposing with a
diffeomorphism `S¹ → S¹`.

Given a loop `γ : S¹ → F` for some real vector space `F`, one may integrate to obtain its average
`∫ x in 0..1, (γ x)` in `F`. Although this average depends on the loop's parametrization, it
satisfies a contraint that depends only on the image of the loop: the average is contained in the
convex hull of the image of `γ`. The non-parametric version of the reparametrization lemma says that
conversely, given any point `g` in the interior of the convex hull of the image of `γ`, one may find
a reparametrization of `γ` whose average is `g`.

The reparametrization lemma thus allows one to reduce the problem of constructing a loop whose
average is a given point, to the problem of constructing a loop subject to a condition that depends
only on its image.

In fact the reparametrization lemma holds parametrically. Given a smooth family of loops:
`γ : E × S¹ → F`, `(x, t) ↦ γₓ t`, together with a smooth function `g : E → F`, such that `g x` is
contained in the interior of the convex hull of the image of `γₓ` for all `x`, there exists a smooth
family of diffeomorphism `φ : E × S¹ → S¹`, `(x, t) ↦ φₓ t` such that the average of `γₓ ∘ φₓ` is
`g x` for all `x`.

The idea of the proof is simple: since `g x` is contained in the interior of the convex hull of
the image of `γₓ` one may find `t₀, t₁, ..., tₙ` and barycentric coordinates `w₀, w₁, ..., wₙ` such
that `g x = ∑ᵢ wᵢ • γₓ(tᵢ)`. If there were no smoothness requirement on `φₓ` one could define
it to be a step function which spends time `wᵢ` at each `tᵢ`. However because there is a smoothness
condition, one rounds off the corners of the would-be step function by using a "delta mollifier"
(an approximation to a Dirac delta function).

The above construction works locally in the neighbourhood of any `x` in `E` and one uses a partition
of unity to globalise all the local solutions into the required family: `φ : E × S¹ → S¹`.

The key ingredients are theories of calculus, convex hulls, barycentric coordinates,
existence of delta mollifiers, partitions of unity, and the inverse function theorem.
-/

section


noncomputable section

open Set Function MeasureTheory Module intervalIntegral Filter
open scoped Topology Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option hygiene false
local notation "ι" => Fin (finrank ℝ F + 1)
set_option hygiene true

section MetricSpace

variable [MetricSpace E] [FiniteDimensional ℝ F]

theorem Loop.tendsto_mollify_apply (γ : E → Loop F) (h : Continuous ↿γ) (x : E) (t : ℝ) :
    Tendsto (fun z : E × ℕ ↦ (γ z.1).mollify z.2 t) (𝓝 x ×ˢ atTop) (𝓝 (γ x t)) := by
  have hγ : ∀ x, Continuous (γ x) := fun x ↦ h.comp <| Continuous.prodMk_right _
  simp_rw [Loop.mollify_eq_convolution _ (hγ _)]
  rw [← add_zero (γ x t)]
  refine Tendsto.add ?_ ?_
  · rw [← one_smul ℝ (γ x t)]
    refine ((tendsto_natCast_div_add_atTop 1).comp tendsto_snd).smul ?_
    refine ContDiffBump.convolution_tendsto_right ?_ ?_ ?_ tendsto_const_nhds
    · simp_rw [bump]; norm_cast
      exact
        ((tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat 1)).comp tendsto_snd
    · filter_upwards with x using (hγ _).aestronglyMeasurable
    · have := h.tendsto (x, t)
      rw [nhds_prod_eq] at this
      exact this.comp ((tendsto_fst.comp tendsto_fst).prodMk tendsto_snd)
  · have : Continuous fun z ↦ intervalIntegral (γ z) 0 1 volume :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (by apply h)
        continuous_const
    rw [← zero_smul ℝ (_ : F)]
    exact (tendsto_one_div_add_atTop_nhds_zero_nat.comp tendsto_snd).smul
      ((this.tendsto x).comp tendsto_fst)

end MetricSpace

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Given a smooth function `g : E → F` between normed vector spaces, a smooth surrounding family
is a smooth family of loops `E → loop F`, `x ↦ γₓ` such that `γₓ` surrounds `g x` for all `x`. -/
structure SmoothSurroundingFamily (g : E → F) where
  smooth_surrounded : 𝒞 ∞ g
  toFun : E → Loop F
  smooth : 𝒞 ∞ ↿toFun
  Surrounds : ∀ x, (toFun x).Surrounds <| g x

namespace SmoothSurroundingFamily

variable {g : E → F} (γ : SmoothSurroundingFamily g) (x y : E)

instance instCoeFunForallLoop : CoeFun (SmoothSurroundingFamily g) fun _ ↦ E → Loop F :=
  ⟨toFun⟩

protected theorem continuous : Continuous (γ x) := by
  apply Continuous.uncurry_left x γ.smooth.continuous

/-- Given `γ : SmoothSurroundingFamily g` and `x : E`, `γ.surroundingParametersAt x` are the
`tᵢ : ℝ`, for `i = 0, 1, ..., dim F` such that `γ x tᵢ` surround `g x`. -/
def surroundingParametersAt : ι → ℝ :=
  Classical.choose (γ.Surrounds x)

/-- Given `γ : SmoothSurroundingFamily g` and `x : E`, `γ.surroundingPointsAt x` are the
points `γ x tᵢ` surrounding `g x` for parameters `tᵢ : ℝ`, `i = 0, 1, ..., dim F` (defined
by `γ.surroundingParametersAt x`). -/
def surroundingPointsAt : ι → F :=
  γ x ∘ γ.surroundingParametersAt x

/-- Given `γ : SmoothSurroundingFamily g` and `x : E`, `γ.surrounding_weights_at x` are the
barycentric coordinates of `g x` wrt to the points `γ x tᵢ`, for parameters `tᵢ : ℝ`,
`i = 0, 1, ..., dim F` (defined by `γ.surroundingParametersAt x`). -/
def surroundingWeightsAt : ι → ℝ :=
  Classical.choose (Classical.choose_spec (γ.Surrounds x))

theorem surroundPtsPointsWeightsAt :
    SurroundingPts (g x) (γ.surroundingPointsAt x) (γ.surroundingWeightsAt x) :=
  Classical.choose_spec _

/-- Note that we are mollifying the loop `γ y` at the surrounding parameters for `γ x`. -/
def approxSurroundingPointsAt (n : ℕ) (i : ι) : F :=
  (γ y).mollify n (γ.surroundingParametersAt x i)

variable [FiniteDimensional ℝ E] [CompleteSpace F] in
theorem approxSurroundingPointsAt_smooth (n : ℕ) :
    𝒞 ∞ fun y ↦ γ.approxSurroundingPointsAt x y n := by
  refine contDiff_pi.mpr fun i ↦ ?_
  suffices 𝒞 ∞ fun y ↦ ∫ s in (0 : ℝ)..1, deltaMollifier n (γ.surroundingParametersAt x i) s • γ y s
    by simpa [approxSurroundingPointsAt, Loop.mollify]
  apply contDiff_parametric_integral_of_contDiff
  exact ContDiff.smul contDiff_deltaMollifier.snd' γ.smooth

variable [FiniteDimensional ℝ F]

/-- The key property from which it should be easy to construct `localCenteringDensity`,
`localCenteringDensityNhd` etc below. -/
theorem eventually_exists_surroundingPts_approxSurroundingPointsAt :
    ∀ᶠ z : E × ℕ in 𝓝 x ×ˢ atTop,
      ∃ w, SurroundingPts (g z.1) (γ.approxSurroundingPointsAt x z.1 z.2) w := by
  let a : ι → E × ℕ → F := fun i z ↦ γ.approxSurroundingPointsAt x z.1 z.2 i
  suffices ∀ i, Tendsto (a i) (𝓝 x ×ˢ atTop) (𝓝 (γ.surroundingPointsAt x i)) by
    have hg : Tendsto (fun z : E × ℕ ↦ g z.fst) (𝓝 x ×ˢ atTop) (𝓝 (g x)) :=
      Tendsto.comp γ.smooth_surrounded.continuous.continuousAt tendsto_fst
    exact eventually_surroundingPts_of_tendsto_of_tendsto'
      ⟨_, γ.surroundPtsPointsWeightsAt x⟩ this hg
  intro i
  let t := γ.surroundingParametersAt x i
  change Tendsto (fun z : E × ℕ ↦ (γ z.1).mollify z.2 t) (𝓝 x ×ˢ atTop) (𝓝 (γ x t))
  exact Loop.tendsto_mollify_apply γ γ.smooth.continuous x t

/-- This is an auxiliary definition to help construct `centeringDensity` below.

Given `x : E`, it represents a smooth probability distribution on the circle with the property that:
`∫ s in 0..1, γ.localCenteringDensity x y s • γ y s = g y`
for all `y` in a neighbourhood of `x` (see `localCenteringDensity_average` below). -/
def localCenteringDensity [DecidablePred (· ∈ affineBases ι ℝ F)] : E → ℝ → ℝ := fun y ↦ by
  choose n hn₁ _ using
    Filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surroundingPts_approxSurroundingPointsAt x)
  choose u _u v hv _huv using mem_prod_iff.mp hn₁
  choose m _hmv using mem_atTop_sets.mp hv
  exact ∑ i, evalBarycentricCoords ι ℝ F (g y) (γ.approxSurroundingPointsAt x y m) i •
      deltaMollifier m (γ.surroundingParametersAt x i)

/-- This is an auxiliary definition to help construct `centeringDensity` below. -/
def localCenteringDensityMp : ℕ := by
  choose n hn₁ _hn₂ using
    Filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surroundingPts_approxSurroundingPointsAt x)
  choose u _hu v hv _huv using mem_prod_iff.mp hn₁
  choose m _hmv using mem_atTop_sets.mp hv
  exact m

theorem localCenteringDensity_spec [DecidablePred (· ∈ affineBases ι ℝ F)] :
    γ.localCenteringDensity x y =
      ∑ i,
        evalBarycentricCoords ι ℝ F (g y)
            (γ.approxSurroundingPointsAt x y (γ.localCenteringDensityMp x)) i •
          deltaMollifier (γ.localCenteringDensityMp x) (γ.surroundingParametersAt x i) :=
  rfl

/-- This is an auxiliary definition to help construct `centeringDensity` below. -/
def localCenteringDensityNhd : Set E := by
  choose n hn₁ _hn₂ using
    Filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surroundingPts_approxSurroundingPointsAt x)
  choose u _hu v _hv _huv using mem_prod_iff.mp hn₁
  exact interior u

theorem localCenteringDensityNhd_isOpen : IsOpen <| γ.localCenteringDensityNhd x :=
  isOpen_interior

theorem localCenteringDensityNhd_self_mem : x ∈ γ.localCenteringDensityNhd x := by
  let h :=
    Filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surroundingPts_approxSurroundingPointsAt x)
  exact mem_interior_iff_mem_nhds.mpr
    (Classical.choose_spec <| mem_prod_iff.mp (Classical.choose_spec h).1).1

theorem approxSurroundingPointsAt_of_localCenteringDensityNhd
    (hy : y ∈ γ.localCenteringDensityNhd x) :
    ∃ w, SurroundingPts (g y)
      (γ.approxSurroundingPointsAt x y (γ.localCenteringDensityMp x)) w := by
  let h :=
    Filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surroundingPts_approxSurroundingPointsAt x)
  let nn := Classical.choose h
  let hnn := mem_prod_iff.mp (Classical.choose_spec h).1
  let n := Classical.choose hnn
  let hn := Classical.choose_spec hnn
  change y ∈ interior n at hy
  let v := Classical.choose hn.2
  let hv : v ∈ atTop := (Classical.choose_spec hn.2).1
  let m := Classical.choose (mem_atTop_sets.mp hv)
  let hm := Classical.choose_spec (mem_atTop_sets.mp hv)
  change ∃ w, SurroundingPts (g y) (γ.approxSurroundingPointsAt x y m) w
  suffices (y, m) ∈ nn from (Classical.choose_spec h).2 _ this
  apply (Classical.choose_spec hn.2).2
  change y ∈ n ∧ m ∈ v
  exact ⟨interior_subset hy, hm _ (le_refl _)⟩

theorem approxSurroundingPointsAt_mem_affineBases (hy : y ∈ γ.localCenteringDensityNhd x) :
    γ.approxSurroundingPointsAt x y (γ.localCenteringDensityMp x) ∈ affineBases ι ℝ F :=
  (Classical.choose_spec
      (γ.approxSurroundingPointsAt_of_localCenteringDensityNhd x y hy)).mem_affineBases

section DecidablePred

variable [DecidablePred (· ∈ affineBases ι ℝ F)]

@[simp]
theorem localCenteringDensity_pos (hy : y ∈ γ.localCenteringDensityNhd x) (t : ℝ) :
    0 < γ.localCenteringDensity x y t := by
  simp only [γ.localCenteringDensity_spec x, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_pos (fun i _ ↦ mul_pos ?_ (deltaMollifier_pos _)) Finset.univ_nonempty
  obtain ⟨w, hw⟩ := γ.approxSurroundingPointsAt_of_localCenteringDensityNhd x y hy
  convert! hw.w_pos i
  rw [← hw.coord_eq_w]
  simp [evalBarycentricCoords, γ.approxSurroundingPointsAt_mem_affineBases x y hy]

theorem localCenteringDensity_periodic : Periodic (γ.localCenteringDensity x y) 1 :=
  Finset.univ.periodic_sum fun _ _ ↦ Periodic.smul deltaMollifier_periodic _

variable [FiniteDimensional ℝ E] in
@[fun_prop]
theorem contDiffOn_localCenteringDensity :
    ContDiffOn ℝ ∞ ↿(γ.localCenteringDensity x)
      <| γ.localCenteringDensityNhd x ×ˢ (univ : Set ℝ) := by
  let h₀ (yt : E × ℝ) (_ : yt ∈ γ.localCenteringDensityNhd x ×ˢ (univ : Set ℝ)) :=
    congr_fun (γ.localCenteringDensity_spec x yt.fst) yt.snd
  refine ContDiffOn.congr ?_ h₀
  simp only [Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine ContDiffOn.sum fun i _ ↦ ContDiffOn.mul ?_ (ContDiff.contDiffOn ?_)
  · let w : F × (ι → F) → ℝ := fun z ↦ evalBarycentricCoords ι ℝ F z.1 z.2 i
    let z : E → F × (ι → F) :=
      (Prod.map g fun y ↦ γ.approxSurroundingPointsAt x y (γ.localCenteringDensityMp x)) ∘
        fun x ↦ (x, x)
    change ContDiffOn ℝ ∞ ((w ∘ z) ∘ Prod.fst) (γ.localCenteringDensityNhd x ×ˢ (univ : Set ℝ))
    rw [prod_univ]
    refine ContDiffOn.comp ?_ contDiff_fst.contDiffOn Subset.rfl
    have h₁ := smooth_barycentric ι ℝ F (Fintype.card_fin _) (n := ∞)
    have h₂ : 𝒞 ∞ (eval i : (ι → ℝ) → ℝ) := contDiff_apply _ _ i
    refine (h₂.comp_contDiffOn h₁).comp ?_ ?_
    · have h₃ := (diag_preimage_prod_self (γ.localCenteringDensityNhd x)).symm.subset
      refine ContDiffOn.comp ?_ (contDiff_id.prodMk contDiff_id).contDiffOn h₃
      refine γ.smooth_surrounded.contDiffOn.prodMap (ContDiff.contDiffOn ?_)
      exact γ.approxSurroundingPointsAt_smooth x _
    · intro y hy
      simp [z, γ.approxSurroundingPointsAt_mem_affineBases x y hy]
  · exact contDiff_deltaMollifier.comp contDiff_snd

variable [FiniteDimensional ℝ E] in
@[fun_prop]
theorem localCenteringDensity_continuous (hy : y ∈ γ.localCenteringDensityNhd x) :
    Continuous fun t ↦ γ.localCenteringDensity x y t := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  have hyt : γ.localCenteringDensityNhd x ×ˢ univ ∈ 𝓝 (y, t) :=
    mem_nhds_prod_iff'.mpr
      ⟨γ.localCenteringDensityNhd x, univ, γ.localCenteringDensityNhd_isOpen x, hy,
        isOpen_univ, mem_univ t, rfl.subset⟩
  have := γ.contDiffOn_localCenteringDensity x |>.continuousOn.continuousAt hyt
  fun_prop

@[simp]
theorem localCenteringDensity_integral_eq_one (hy : y ∈ γ.localCenteringDensityNhd x) :
    ∫ s in (0 : ℝ)..1, γ.localCenteringDensity x y s = 1 := by
  let n := γ.localCenteringDensityMp x
  simp only [γ.localCenteringDensity_spec x, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [intervalIntegral.integral_finsetSum]
  · have h : γ.approxSurroundingPointsAt x y n ∈ affineBases ι ℝ F :=
      γ.approxSurroundingPointsAt_mem_affineBases x y hy
    simp_rw [← smul_eq_mul, intervalIntegral.integral_smul, deltaMollifier_integral_eq_one,
      smul_eq_mul, mul_one]
    rw [evalBarycentricCoords_apply_of_mem_bases ι ℝ F (g y) h]
    simp_rw [AffineBasis.coords_apply, AffineBasis.sum_coord_apply_eq_one]
  · exact fun i hi ↦ Continuous.intervalIntegrable (by fun_prop) 0 1

@[simp]
theorem localCenteringDensity_average (hy : y ∈ γ.localCenteringDensityNhd x) :
    ∫ s in (0 : ℝ)..1, γ.localCenteringDensity x y s • γ y s = g y := by
  let n := γ.localCenteringDensityMp x
  simp only [γ.localCenteringDensity_spec x, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_smul]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [mul_smul, intervalIntegral.integral_smul]
    change ∑ i, _ • γ.approxSurroundingPointsAt x y n i = _
    have h : γ.approxSurroundingPointsAt x y n ∈ affineBases ι ℝ F :=
      γ.approxSurroundingPointsAt_mem_affineBases x y hy
    erw [evalBarycentricCoords_apply_of_mem_bases ι ℝ F (g y) h]
    simp only [AffineBasis.coords_apply]
    exact AffineBasis.linear_combination_coord_eq_self ..
  · simp_rw [mul_smul]
    refine fun i hi ↦ ((Continuous.smul ?_ (γ.continuous y)).const_smul _).intervalIntegrable 0 1
    exact contDiff_deltaMollifier.continuous

end DecidablePred

/-- Given `γ : SmoothSurroundingFamily g`, together with a point `x : E` and a map `f : ℝ → ℝ`,
`γ.is_centeringDensity x f` is the proposition that `f` is periodic, strictly positive, and
has integral one and that the average of `γₓ` with respect to the measure that `f` defines on
the circle is `g x`.

The continuity assumption is just a legacy convenience and should be dropped. -/
structure IsCenteringDensity (x : E) (f : ℝ → ℝ) : Prop where
  Pos : ∀ t, 0 < f t
  Periodic : Periodic f 1
  integral_one : ∫ s in (0 : ℝ)..1, f s = 1
  average : ∫ s in (0 : ℝ)..1, f s • γ x s = g x
  Continuous : Continuous f

omit [FiniteDimensional ℝ F] in
-- Can drop if/when have `intervalIntegrable.smul_continuous_on`
theorem isCenteringDensity_convex (x : E) : Convex ℝ { f | γ.IsCenteringDensity x f } := by
  classical
  rintro f ⟨hf₁, hf₂, hf₃, hf₄, hf₅⟩ k ⟨hk₁, hk₂, hk₃, hk₄, hk₅⟩ a b ha hb hab
  have hf₆ : IntervalIntegrable f volume 0 1 := by
    apply intervalIntegrable_of_integral_ne_zero
    rw [hf₃]; exact one_ne_zero
  have hf₇ : IntervalIntegrable (f • (γ x : ℝ → F)) volume 0 1 :=
    (hf₅.smul (γ.continuous x)).intervalIntegrable 0 1
  have hk₆ : IntervalIntegrable k volume 0 1 := by
    apply intervalIntegrable_of_integral_ne_zero
    rw [hk₃]; exact one_ne_zero
  have hk₇ : IntervalIntegrable (k • (γ x : ℝ → F)) volume 0 1 :=
    (hk₅.smul (γ.continuous x)).intervalIntegrable 0 1
  exact {
    Pos := fun t ↦ convex_Ioi (0 : ℝ) (hf₁ t) (hk₁ t) ha hb hab
    Periodic := (hf₂.smul a).add (hk₂.smul b)
    integral_one := by
      simp_rw [Pi.add_apply]
      rw [intervalIntegral.integral_add (hf₆.smul a) (hk₆.smul b)]
      simp [hf₃, hk₃, hab]
    average := by
      simp_rw [Pi.add_apply, Pi.smul_apply, add_smul, smul_assoc]
      erw [intervalIntegral.integral_add (hf₇.smul a) (hk₇.smul b)]
      simp [intervalIntegral.integral_smul, ← add_smul, hf₄, hk₄, hab]
    Continuous := Continuous.add (hf₅.const_smul a) (hk₅.const_smul b) }

variable [FiniteDimensional ℝ E]

theorem exists_smooth_isCenteringDensity (x : E) :
    ∃ U ∈ 𝓝 x,
      ∃ f : E → ℝ → ℝ,
        ContDiffOn ℝ ∞ (uncurry f) (U ×ˢ (univ : Set ℝ)) ∧
          ∀ y ∈ U, γ.IsCenteringDensity y (f y) := by
  classical
  exact ⟨γ.localCenteringDensityNhd x,
    mem_nhds_iff.mpr
      ⟨_, Subset.rfl, γ.localCenteringDensityNhd_isOpen x, γ.localCenteringDensityNhd_self_mem x⟩,
    γ.localCenteringDensity x, γ.contDiffOn_localCenteringDensity x, fun y hy ↦
    ⟨γ.localCenteringDensity_pos x y hy, γ.localCenteringDensity_periodic x y,
      γ.localCenteringDensity_integral_eq_one x y hy, γ.localCenteringDensity_average x y hy,
      γ.localCenteringDensity_continuous x y hy⟩⟩

/-- This the key construction. It represents a smooth probability distribution on the circle with
the property that:
`∫ s in 0..1, γ.centeringDensity x s • γ x s = g x`
for all `x : E` (see `centeringDensity_average` below). -/
def centeringDensity : E → ℝ → ℝ :=
  Classical.choose
    (exists_contDiff_of_convex₂ γ.isCenteringDensity_convex γ.exists_smooth_isCenteringDensity)

theorem centeringDensity_smooth : 𝒞 ∞ <| uncurry fun x t ↦ γ.centeringDensity x t :=
  (Classical.choose_spec <|
      exists_contDiff_of_convex₂ γ.isCenteringDensity_convex γ.exists_smooth_isCenteringDensity).1

theorem isCenteringDensityCenteringDensity (x : E) :
    γ.IsCenteringDensity x (γ.centeringDensity x) :=
  (Classical.choose_spec <|
        exists_contDiff_of_convex₂ γ.isCenteringDensity_convex γ.exists_smooth_isCenteringDensity).2
    x

@[simp]
theorem centeringDensity_pos (t : ℝ) : 0 < γ.centeringDensity x t :=
  (γ.isCenteringDensityCenteringDensity x).Pos t

theorem centeringDensity_periodic : Periodic (γ.centeringDensity x) 1 :=
  (γ.isCenteringDensityCenteringDensity x).Periodic

@[simp]
theorem centeringDensity_integral_eq_one : ∫ s in (0)..1, γ.centeringDensity x s = 1 :=
  (γ.isCenteringDensityCenteringDensity x).integral_one

@[simp]
theorem centeringDensity_average : ∫ s in (0)..1, γ.centeringDensity x s • γ x s = g x :=
  (γ.isCenteringDensityCenteringDensity x).average

theorem centeringDensity_continuous : Continuous (γ.centeringDensity x) :=
  (γ.centeringDensity_smooth.continuous).uncurry_left x

theorem centeringDensity_intervalIntegrable (t₁ t₂ : ℝ) :
    IntervalIntegrable (γ.centeringDensity x) volume t₁ t₂ :=
  (γ.centeringDensity_continuous x).intervalIntegrable t₁ t₂

@[simp]
theorem integral_add_one_centeringDensity (t : ℝ) :
    ∫ s in (0)..t + 1, γ.centeringDensity x s = (∫ s in (0)..t, γ.centeringDensity x s) + 1 := by
  have h₁ := γ.centeringDensity_intervalIntegrable x 0 t
  have h₂ := γ.centeringDensity_intervalIntegrable x t (t + 1)
  simp [← integral_add_adjacent_intervals h₁ h₂,
    (γ.centeringDensity_periodic x).intervalIntegral_add_eq t 0]

theorem deriv_integral_centeringDensity_pos (t : ℝ) :
    0 < deriv (fun t ↦ ∫ s in (0)..t, γ.centeringDensity x s) t := by
  rw [intervalIntegral.deriv_integral_right (γ.centeringDensity_intervalIntegrable _ _ _)
      ((γ.centeringDensity_continuous x).stronglyMeasurableAtFilter volume (𝓝 t))
      (centeringDensity_continuous γ x).continuousAt]
  exact centeringDensity_pos γ x t

theorem strictMono_integral_centeringDensity :
    StrictMono fun t ↦ ∫ s in (0)..t, γ.centeringDensity x s :=
  strictMono_of_deriv_pos (γ.deriv_integral_centeringDensity_pos x)

theorem surjective_integral_centeringDensity :
    Surjective fun t ↦ ∫ s in (0)..t, γ.centeringDensity x s :=
  haveI : Continuous fun t ↦ ∫ s in (0)..t, γ.centeringDensity x s :=
    continuous_primitive (γ.centeringDensity_intervalIntegrable x) 0
  EquivariantMap.surjective
    ⟨fun t ↦ ∫ s in (0)..t, γ.centeringDensity x s, γ.integral_add_one_centeringDensity x⟩ this

/-- Given `γ : SmoothSurroundingFamily g`, `x ↦ γ.reparametrize x` is a smooth family of
diffeomorphisms of the circle such that reparametrizing `γₓ` by `γ.reparametrize x` gives a loop
with average `g x`.

This is the key construction and the main "output" of the reparametrization lemma. -/
def reparametrize : E → EquivariantEquiv := fun x ↦
  ({ toFun := fun t ↦ ∫ s in (0)..t, γ.centeringDensity x s
     invFun :=
       (StrictMono.orderIsoOfSurjective _ (γ.strictMono_integral_centeringDensity x)
           (γ.surjective_integral_centeringDensity x)).symm
     left_inv := StrictMono.orderIsoOfSurjective_symm_apply_self _ _ _
     right_inv := fun t ↦ StrictMono.orderIsoOfSurjective_self_symm_apply _
       (γ.strictMono_integral_centeringDensity x) _ t
     map_zero' := integral_same
     eqv' := γ.integral_add_one_centeringDensity x } : EquivariantEquiv).symm

theorem hasDerivAt_reparametrize_symm (s : ℝ) :
    HasDerivAt (γ.reparametrize x).symm (γ.centeringDensity x s) s :=
  integral_hasDerivAt_right (γ.centeringDensity_intervalIntegrable x 0 s)
    ((γ.centeringDensity_continuous x).stronglyMeasurableAtFilter _ _)
    (γ.centeringDensity_continuous x).continuousAt

-- 𝒞 ∞ ↿γ.reparametrize
theorem reparametrize_smooth : 𝒞 ∞ <| uncurry fun (x : E) (t : ℝ) ↦ γ.reparametrize x t := by
  let f : E → ℝ → ℝ := fun x t ↦ ∫ s in (0)..t, γ.centeringDensity x s
  change 𝒞 ∞ fun p : E × ℝ ↦ (StrictMono.orderIsoOfSurjective (f p.1) _ _).symm p.2
  apply contDiff_parametric_symm_of_deriv_pos
  · exact contDiff_parametric_primitive_of_contDiff'' γ.centeringDensity_smooth 0
  · exact fun x ↦ deriv_integral_centeringDensity_pos γ x
  · exact fun x ↦ surjective_integral_centeringDensity γ x

@[simp]
theorem reparametrize_average :
    ((γ x).reparam <| (γ.reparametrize x).equivariantMap).average = g x := by
  change ∫ s : ℝ in (0)..1, γ x (γ.reparametrize x s) = g x
  have h₁ :
    ∀ s, s ∈ uIcc 0 (1 : ℝ) → HasDerivAt (γ.reparametrize x).symm (γ.centeringDensity x s) s :=
    fun s _ ↦ γ.hasDerivAt_reparametrize_symm x s
  have h₂ : ContinuousOn (fun s ↦ γ.centeringDensity x s) (uIcc 0 1) :=
    (γ.centeringDensity_continuous x).continuousOn
  have h₃ : Continuous fun s ↦ γ x (γ.reparametrize x s) :=
    (γ.continuous x).comp (γ.reparametrize_smooth.continuous.uncurry_left x)
  rw [← (γ.reparametrize x).symm.map_zero, ← (γ.reparametrize x).symm.map_one,
    ← integral_deriv_smul_comp h₁ h₂ h₃]
  simp only [comp_apply, EquivariantEquiv.apply_symm_apply, centeringDensity_average]

end SmoothSurroundingFamily
end
end
end

section
-- module Solutions.OAIQ249_SI.Loops_Exists
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open Set Function Int Metric Filter Real MeasureTheory
open scoped  MeasureTheory.Measure Topology unitInterval ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  {g b : E → F} {Ω : Set (E × F)} {U K C : Set E}

variable [NormedSpace ℝ F] [FiniteDimensional ℝ F]

attribute [fun_prop] Continuous.infDist Continuous.if_const

/- Some remarks about `exist_loops_aux2`:
  `δ`: loop after smoothing
  `γ`: loop before smoothing (defined on all of `E`)
  Requirements:
  (0) `δ x t` is a loop
  (1) `δ` lands in `Ω`
  (2) `δ` has the correct values: for `s = 0` and `t = 0` it should be `b`
  (3) `δ` should be constant on `t ≤ 0` and for `t ≥ 1`.
  (4) `δ x 1` surrounds `g x`.
  (5) Near `K`, the line connecting `b` and `δ` lies in `Ω`

  Strategy:
  (a) We need `ε₁` satisfying the following conditions:
  (a1) We need to ensure that an `ε₁ x`-ball around `(x, δ x s t)` lies in `Ω` for some
    continuous `ε₁`.
  (a4) Furthermore, `ε₁` should be small enough so that any function with that
    distance from `γ` still surrounds `g`, using `SurroundingFamily.surrounds_of_close`.
  (a5): `ε₁ x < ε₀` (obtained from `exist_loops_aux1`)
  (b) Replace `γ x t s` by `γ x (linearReparam t) (linearReparam s)`.
  (e) Let `δ' x` be a family of loops that is at most `ε₁` away from `γ` using
    `exists_smooth_and_eqOn`. Since `γ` is smooth near `s ∈ ℤ` and `t ≤ 0` we can also
    ensure that `δ' = γ` for those values (*).
    Now let `δ x t s = δ' x (smoothTransition t) (fract s)`
    We immediately get (0) and (3). We get (2) by (*).
    This is still smooth, since `δ'` is doesn't depend on `s` near `s ∈ ℤ`.
  (f) (a1) gives (1), (a4) gives (4) and (a5) gives (5).

  Note: to ensure (2) the reparamerization strategy that was originally in the blueprint
  (ensuring that `γ` is locally constant in the `t` and `s` directions)
  didn't work. Indeed it needed to take the convolution in the `x`-direction,
  meaning that the value won't stay the same, since `γ` is not constant in the `x`-direction.
-/

variable (g b Ω U K)

/-- A "nice" family of loops consists of all the properties we want from the `exist_loops` lemma:
it is a smooth homotopy in `Ω` with fixed endpoints from the constant loop at `b x` to a loop with
average `g x` that is also constantly `b x` near `K`.
The first two conditions are implementation specific: the homotopy is constant outside the unit
interval. -/
structure NiceLoop (γ : ℝ → E → Loop F) : Prop where
  t_le_zero : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x
  t_ge_one : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x
  t_zero : ∀ x s, γ 0 x s = b x
  s_zero : ∀ x t, γ t x 0 = b x
  avg : ∀ x, (γ 1 x).average = g x
  mem_Ω : ∀ x t s, (x, γ t x s) ∈ Ω
  smooth : 𝒞 ∞ ↿γ
  rel_K : ∀ᶠ x in 𝓝ˢ K, ∀ t s, γ t x s = b x
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_HPrinciple
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Local h-principle for open and ample relations

This file proves `lem:h_principle_open_ample_loc` from the blueprint. This is the local
version of the h-principle for open and ample relations. The proof brings together the
main result `exist_loops` from the loop folder (Chapter 1 in the blueprint) and
the corrugation technique.

One formalization issue is that the whole construction carries around a lot of data.
On paper it is easy to state one lemma listing once all this data and proving many properties.
Here it is more convenient to give each property its own lemma so carrying around data,
assumptions and constructions requires some planning. Our way to mitigate this issue
is to use two ad-hoc structures `Landscape` and `StepLandscape` which partly bundle
all this.

The `Landscape` structure record three sets in a vector space, a closed
set `C` and two nested compact sets `K₀` and `K₁`. This is the ambient data for
the local h-principle result. We call this partly bundled because it doesn't include
the data of the formal solution we want to improve. Instead we have a Prop-valued
structure `Landscape.accepts` that takes a landscape and a formal solution and assert
some compatibility conditions. There are four conditions, which is already enough
motivation to introduce a structure instead of one definition using the logical
conjunction operator that would lead to awkward and error prone access to the
individual conditions.

The proof of this proposition involves an induction on a flag of subspaces (nested
subspaces of increasing dimensions). For the purpose of this induction we use
a second structure `StepLandscape` that extends `Landscape` with two more pieces
of data, a subspace and a dual pair, and a compatibility condition, namely the subspace
has to be in the hyperplane defined by the dual pair.

In this setup, given `(L : StepLandscape E) {𝓕 : FormalSol R} (h : L.accepts R 𝓕)`,
the loop family constructed by Chapter 2 is `L.loop h`. Together with corrugation,
it is used to build `L.improveStep h` which is the homotopy of 1-jet sections improving
the formal solution `𝓕` in that step of the main inductive proof. A rather long series of
lemmas prove all the required properties of that homotopy, corresponding to
lemma `lem:integration_step` from the blueprint.

The inductive proof itself is the proof of `RelLoc.FormalSol.improve`.
Here all conclusions are stated at once this the induction requires to know about each
of them to proceed to the next step. We could have introduced one more ad-hoc structure
to record those conclusion but this isn't needed (at least in that Chapter) since we
need to access its components only once.

-/

section


noncomputable section

open scoped unitInterval Filter Topology ContDiff

open Filter Set RelLoc

open LinearMap (ker)

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The setup for local h-principle is two compact subsets `K₀ ⊆ K₁` in `E` with
`K₀ ⊆ interior K₁` and a closed subset `C`.
-/
structure Landscape where
  (C K₀ K₁ : Set E)
  hC : IsClosed C
  hK₀ : IsCompact K₀
  hK₁ : IsCompact K₁
  h₀₁ : K₀ ⊆ interior K₁
end
end
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridSupportedCutoffs
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized grid cutoffs multiplied by a supported chart
weight. The derivative constant is independent of the number of cells. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.PhaseGrid
open WeightedEstimates JetPolynomial

def supportedNormalizedCutoff {K : Compacts Base} (f : SupportedField (F := ℝ) K)
    {a : Finset Index} {h : ℝ} (hh : 0 < h) (hK : (K : Set Base) ⊆ coverRegion a h)
    (k : Index) : SupportedField (F := ℝ) K := by
  refine ⟨fun x => f x * normalizedCutoff a h k x,?_,?_⟩
  · apply contDiff_of_tsupport_subset (coverRegion_open a h)
      ((tsupport_mul_subset_left.trans f.tsupport_subset).trans hK)
    exact f.contDiff.contDiffOn.mul
      (normalizedCutoff_smooth hh (fun y hy => coverRegion_covers a h hy) k)
  · intro x hx
    change f x * normalizedCutoff a h k x = 0
    simp only [f.zero_on_compl hx,Pi.zero_apply,zero_mul]

@[simp] lemma supportedNormalizedCutoff_apply {K : Compacts Base}
    (f : SupportedField (F := ℝ) K) {a : Finset Index} {h : ℝ}
    (hh : 0 < h) (hK : (K : Set Base) ⊆ coverRegion a h) (k : Index) (x : Base) :
    supportedNormalizedCutoff f hh hK k x = f x * normalizedCutoff a h k x := rfl

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridPhaseCutoffs
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined chart weights with their actual small-cell support, and
polynomial bounds after transport to a selected linear phase. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseGrid
open WeightedEstimates JetPolynomial PhaseGeometry

def gridCutoffCompact (K : Compacts Base) (h : ℝ) (k : Index) : Compacts Base :=
  ⟨(K : Set Base) ∩ tsupport (cutoff h k),
    K.isCompact.of_isClosed_subset (K.isCompact.isClosed.inter (isClosed_tsupport _))
      inter_subset_left⟩

def supportedCellCutoff {K : Compacts Base} (f : SupportedField (F := ℝ) K)
    {a : Finset Index} {h : ℝ} (hh : 0 < h) (hK : (K : Set Base) ⊆ coverRegion a h)
    (k : Index) : SupportedField (F := ℝ) (gridCutoffCompact K h k) :=
  ContDiffMapSupportedIn.of_support_subset (supportedNormalizedCutoff f hh hK k).contDiff
    (fun x hx => by
      have ht : x ∈ tsupport (fun y => f y * normalizedCutoff a h k y) :=
        subset_tsupport _ hx
      exact ⟨f.tsupport_subset (tsupport_mul_subset_left ht),
        normalizedCutoff_tsupport a h k (tsupport_mul_subset_right ht)⟩)

@[simp] lemma supportedCellCutoff_apply {K : Compacts Base}
    (f : SupportedField (F := ℝ) K) {a : Finset Index} {h : ℝ}
    (hh : 0 < h) (hK : (K : Set Base) ⊆ coverRegion a h) (k : Index) (x : Base) :
    supportedCellCutoff f hh hK k x = f x * normalizedCutoff a h k x := rfl

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridCutoffSupport
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local cell cutoff has the exact global refined support used in
phase selection. This keeps the solver's geometry on that original support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def cellChartCompact (i : A.centers) (a : Finset Index) (h : ℝ) (k : Index) :
    TopologicalSpace.Compacts JetPolynomial.Base :=
  ⟨(chart (i : M)) '' tsupport (refinedCutoff (i : M) (A.weight i) a h k),
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono ((refinedCutoff_tsupport_outer
        (i : M) (A.weight i) a h k).trans (A.weight_support i)))⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPrimitiveFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite smooth primitive families and their partial-cycle metrics.
Different cycles may use different supports and phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance familyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end


