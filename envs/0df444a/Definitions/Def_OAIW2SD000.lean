-- Prove2me | Definitions.Def_OAIW2SD000
-- name    : OAIW2SD000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T02:30:39.157998+00:00
-- url     : https://prove2.me/theorems/bb59a06b-1cca-4f84-bfca-5cb3a2a70ede
-- title:
--   Definitions bundle OAIW2SD000 of the split of OpenAI, An Endpoint Gradient Bound for the Centered Disk Maximal Operator
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SignedDisk.CenteredDiskEndpoint.main_signed_finite_band`, carved from OpenAI's openai/math development (OpenAI, *An Endpoint Gradient Bound for the Centered Disk Maximal Operator*, OpenAI Math Release, September 26, 2026, result family 85, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 351 declarations of OpenAI's Lean: 209 definitions, 9 inductive types or structures, 4 instances and 129 theorems. The definitions and types are `OAI.SignedDisk.ActualLabels.Label`, `OAI.SignedDisk.ActualLabels.badWeight`, `OAI.SignedDisk.ActualLabels.before`, `OAI.SignedDisk.ActualLabels.boundaryCost`, `OAI.SignedDisk.ActualLabels.cellCost`, `OAI.SignedDisk.ActualLabels.comparisonConstant`, `OAI.SignedDisk.ActualLabels.costLimit`, `OAI.SignedDisk.ActualLabels.derivativeCost`, `OAI.SignedDisk.ActualLabels.directPriceConstant`, `OAI.SignedDisk.ActualLabels.energyRate`, `OAI.SignedDisk.ActualLabels.geometricRadii`, `OAI.SignedDisk.ActualLabels.initial`, `OAI.SignedDisk.ActualLabels.marginal`, `OAI.SignedDisk.ActualLabels.observation`, `OAI.SignedDisk.ActualLabels.observationJet`, `OAI.SignedDisk.ActualLabels.pointCost`, `OAI.SignedDisk.ActualLabels.rate`, `OAI.SignedDisk.ActualLabels.row`, `OAI.SignedDisk.ActualLabels.rowDerivative`, `OAI.SignedDisk.ActualLabels.spatialConstant`, `OAI.SignedDisk.ActualLabels.spatialPriceConstant`, `OAI.SignedDisk.ActualLabels.switchChance`, `OAI.SignedDisk.ActualLabels.switchCost`, `OAI.SignedDisk.ActualLabels.target`, `OAI.SignedDisk.ActualMarkTrees.lastVertex`, `OAI.SignedDisk.ActualMarkTrees.packingCharge`, `OAI.SignedDisk.ActualMarkTrees.packingConstant`, `OAI.SignedDisk.ActualMarkTrees.particleSwitches`, `OAI.SignedDisk.ActualMarkTrees.pathEnergy`, `OAI.SignedDisk.ActualMarkTrees.pathSwitches`, `OAI.SignedDisk.ActualMarkTrees.pathVertex`, `OAI.SignedDisk.ActualMarkTrees.pathWeight`, `OAI.SignedDisk.ActualMarkTrees.spatialCharge`, `OAI.SignedDisk.ActualMarkTrees.tree`, `OAI.SignedDisk.AffineDensities.rescale`, `OAI.SignedDisk.CenteredDiskEndpoint.complexPlane`, `OAI.SignedDisk.CommonPrices.ErrorIndex`, `OAI.SignedDisk.CommonPrices.badPiece`, `OAI.SignedDisk.CommonPrices.badPrice`, `OAI.SignedDisk.CommonPrices.badRoots` and 178 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/SignedDisk, in whole or in part: `SignedDisk_ActualLabels1`, `SignedDisk_ActualMarkTrees1`, `SignedDisk_ActualMarkTrees2`, `SignedDisk_AffineDensities1`, `SignedDisk_CommonPrices1`, `SignedDisk_CommonPrices2`, `SignedDisk_CommonPrices3`, `SignedDisk_CommonPrices4`, `SignedDisk_DirectionNeighbors1`, `SignedDisk_DiskGeometry1`, `SignedDisk_DiskGeometry2`, `SignedDisk_DiskKernels1`, `SignedDisk_DiskMaximalTools1`, `SignedDisk_DiskMaximalTools2`, `SignedDisk_DiskMoments1`, `SignedDisk_DiskScales1`, `SignedDisk_DiskScales2`, `SignedDisk_DiskScales3`, `SignedDisk_DyadicHats1`, `SignedDisk_DyadicHats2`, `SignedDisk_DyadicHats3`, `SignedDisk_FiniteLabels1`, `SignedDisk_FiniteLabels2`, `SignedDisk_IntrinsicMarks1`, `SignedDisk_LabelSwitches1`, `SignedDisk_LocalCancellation1`, `SignedDisk_LocalCancellation2`, `SignedDisk_LocalCancellation3`, `SignedDisk_LocalCancellation4`, `SignedDisk_Main`, `SignedDisk_Model`, `SignedDisk_PhysicalCells1`, `SignedDisk_PlanePotential1`, `SignedDisk_PlanePotential2`, `SignedDisk_ScalarCancellation1`, `SignedDisk_SignedRuns1`, `SignedDisk_SignedRuns2`, `SignedDisk_VectorRefinement1`.
--
--   **Imports.** It imports the published bundle `Def_SignedFiniteBand`.
--
--   **Imported by** (directly, in this split): the statements `OAI.SignedDisk.CommonPrices.patched_joint`, `OAI.SignedDisk.CommonPrices.patched_unfavorable`, `OAI.SignedDisk.CommonPrices.physical_joint_price`, `OAI.SignedDisk.CommonPrices.physical_size_price` and `OAI.SignedDisk.LocalCancellation.direction_majorant`; the proofs of `OAI.SignedDisk.CenteredDiskEndpoint.main_signed_finite_band`, `OAI.SignedDisk.CommonPrices.patched_joint`, `OAI.SignedDisk.CommonPrices.patched_unfavorable`, `OAI.SignedDisk.CommonPrices.physical_joint_price`, `OAI.SignedDisk.CommonPrices.physical_size_price` and `OAI.SignedDisk.LocalCancellation.direction_majorant`.
-- source:
--   OpenAI, An Endpoint Gradient Bound for the Centered Disk Maximal Operator, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 85; paper: https://github.com/openai/math; Apache License 2.0); definitions carved from lean/OAI/Analysis/SignedDisk at commit adc7f12

import Mathlib
import Definitions.Def_SignedFiniteBand

section
-- module Solutions.OAIW2_SignedDisk.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff

open scoped RealInnerProductSpace

open MeasureTheory Set Filter
open scoped Topology ENNReal

open scoped Real RealInnerProductSpace

namespace DiskGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def entryParameter (z y θ : E) : ℝ := ‖y - z‖ ^ 2 / (2 * ⟪y - z, θ⟫)

end DiskGeometry

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskGeometry1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace

noncomputable section

namespace SignedDisk

namespace DiskGeometry

/-- Mass in the increasing family of tangent disks, away from its tangency cap. -/
def tangentMass (S : Measure ℂ) (ρ : ℝ) (z θ : ℂ) (L : ℝ) : ℝ :=
  (S ({y : ℂ | ρ ≤ ‖y - z‖} ∩ Metric.ball (z + L • θ) L)).toReal

/-- The measurable condition whose planar cost is bounded by the ray-length estimate. -/
def rayCondition (S : Measure ℂ) (ρ T U v : ℝ) (x z : ℂ) : Prop :=
  1 / 2 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 3 ∧
    tangentMass S ρ z (‖x - z‖⁻¹ • (x - z)) (‖x - z‖ - v) ≤ T ∧
    U ≤ tangentMass S ρ z (‖x - z‖⁻¹ • (x - z)) (‖x - z‖ + v) -
      tangentMass S ρ z (‖x - z‖⁻¹ • (x - z)) (‖x - z‖ - v)

def thinShell (x : ℂ) (r δ : ℝ) : Set ℂ := {y | |‖y - x‖ - r| ≤ δ}

end DiskGeometry

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskGeometry2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace

noncomputable section

namespace SignedDisk

namespace DiskGeometry

def pairCondition (ρ δ : ℝ) (x z y : ℂ) : Prop :=
  1 / 2 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 3 ∧
    |‖y - x‖ - ‖x - z‖| ≤ 2 * δ ∧ ρ ≤ ‖y - z‖

def pairMass (ν : Measure ℂ) (ρ δ : ℝ) (x z : ℂ) : ℝ≥0∞ :=
  ν {y : ℂ | pairCondition ρ δ x z y}

def rayIndicator (S : Measure ℂ) (ρ T U v : ℝ) (x z : ℂ) : ℝ≥0∞ :=
  {p : ℂ × ℂ | rayCondition S ρ T U v p.1 p.2}.indicator 1 (x, z)

/-- A radius-independent Borel majorant combining separated shell pairs and ray jumps. -/
def shellMajorant (ν S : Measure ℂ) (ρ δ T U : ℝ) (x : ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal U)⁻¹ ^ 2 * (∫⁻ z, pairMass ν ρ δ x z ∂ν) +
    (ENNReal.ofReal U)⁻¹ * (∫⁻ z, rayIndicator S ρ T U (200 * δ / ρ ^ 2) x z ∂ν)

end DiskGeometry

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff

namespace DiskMoments

local instance instFactEqNatFinrankRealComplexOfNat_solutions : Fact (Module.finrank ℝ ℂ = 2) := ⟨Complex.finrank_real_complex⟩

def rotation (t : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.orientation.rotation (t : Real.Angle)

/-- Signed normalized average on a centered Euclidean disk in the complex plane. -/
def signedAverage (g : ℂ → ℝ) (x : ℂ) (t : ℝ) : ℝ :=
  (∫ y in Metric.ball x t, g y) / (Real.pi * t^2)

end DiskMoments

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskKernels1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff

noncomputable section

namespace SignedDisk

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

namespace DiskKernels

/-- An ordinary nonnegative probability density supported on a radius interval. -/
structure RadiusDensity (a b : ℝ) (M : ℝ≥0) where
  toFun : ℝ → ℝ
  integrable : Integrable toFun
  nonneg : ∀ t, 0 ≤ toFun t
  integral_one : ∫ t, toFun t = 1
  bound : ∀ t, toFun t ≤ M
  support : ∀ t, t ∉ Icc a b → toFun t = 0

instance instCoeFunRadiusDensityForallReal {a b : ℝ} {M : ℝ≥0} : CoeFun (RadiusDensity a b M) (fun _ => ℝ → ℝ) :=
  ⟨RadiusDensity.toFun⟩

def tail {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (u : ℝ) : ℝ :=
  ∫ t in Ioi u, k t

def kernel {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x y : ℂ) : ℝ :=
  tail k (dist y x)

/-- Convex combinations preserve all density and support bounds. -/
def mix {a b : ℝ} {M : ℝ≥0} (k l : RadiusDensity a b M)
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : RadiusDensity a b M where
  toFun t := w * k t + (1-w) * l t
  integrable := (k.integrable.const_mul w).add (l.integrable.const_mul (1-w))
  nonneg t := add_nonneg (mul_nonneg hw0 (k.nonneg t)) (mul_nonneg (sub_nonneg.mpr hw1) (l.nonneg t))
  integral_one := by
    rw [integral_add (k.integrable.const_mul w) (l.integrable.const_mul (1-w)),
      integral_const_mul, integral_const_mul, k.integral_one, l.integral_one]
    ring
  bound t := by
    have h₁ := mul_le_mul_of_nonneg_left (k.bound t) hw0
    have h₂ := mul_le_mul_of_nonneg_left (l.bound t) (sub_nonneg.mpr hw1)
    nlinarith
  support t ht := by rw [k.support t ht, l.support t ht]; ring

def inverseCube (t : ℝ) : ℝ := (t^3)⁻¹

def cubeMass (a b : ℝ) : ℝ := ∫ t in Icc a b, inverseCube t

lemma inverseCube_bounds {t : ℝ} (ht : t ∈ Icc ((1 : ℝ)/2) 3) :
    (1 : ℝ)/27 ≤ inverseCube t ∧ inverseCube t ≤ 8 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hl : (1 : ℝ)/8 ≤ t^3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) ht.1 3
    norm_num at this
    exact this
  have hu : t^3 ≤ 27 := by
    have := pow_le_pow_left₀ ht0.le ht.2 3
    norm_num at this
    exact this
  constructor
  · simpa [inverseCube, one_div] using one_div_le_one_div_of_le (pow_pos ht0 3) hu
  · simpa [inverseCube, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/8) hl

lemma continuousOn_inverseCube {a b : ℝ} (ha : 0 < a) :
    ContinuousOn inverseCube (Icc a b) := by
  apply (continuous_id.pow 3).continuousOn.inv₀
  intro t ht
  exact pow_ne_zero 3 (ne_of_gt (lt_of_lt_of_le ha ht.1))

lemma cubeMass_lower {a b : ℝ} (ha : (1 : ℝ)/2 ≤ a) (hb : b ≤ 3) :
    (b-a)/27 ≤ cubeMass a b := by
  by_cases hab : a ≤ b
  · have hi := (continuousOn_inverseCube (b := b) (show 0 < a by linarith)).integrableOn_Icc (μ := volume)
    have h := setIntegral_mono_on (f := fun _ : ℝ => (1 : ℝ)/27)
      (integrableOn_const isCompact_Icc.measure_ne_top) hi measurableSet_Icc
      (fun t ht => (inverseCube_bounds ⟨ha.trans ht.1, ht.2.trans hb⟩).1)
    simp only [setIntegral_const, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul] at h
    simpa only [cubeMass, div_eq_mul_inv, one_mul] using h
  · have he : Icc a b = ∅ := Icc_eq_empty hab
    have hx : cubeMass a b = 0 := by simp [cubeMass, he]
    rw [hx]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hab)) (by norm_num)

lemma cubeMass_pos {a b : ℝ} (ha : (1 : ℝ)/2 ≤ a) (hb : b ≤ 3) (hab : a < b) :
    0 < cubeMass a b := (div_pos (sub_pos.mpr hab) (by norm_num)).trans_le (cubeMass_lower ha hb)

def cubeDensity (a b t : ℝ) : ℝ :=
  (Icc a b).indicator (fun t => inverseCube t / cubeMass a b) t

lemma cubeDensity_integrable {a b : ℝ} (ha : 0 < a) : Integrable (cubeDensity a b) :=
  ((continuousOn_inverseCube ha).div_const (cubeMass a b)).integrableOn_Icc.integrable_indicator
    measurableSet_Icc

lemma cubeDensity_integral {a b : ℝ} (ha : (1 : ℝ)/2 ≤ a) (hb : b ≤ 3) (hab : a < b) :
    (∫ t, cubeDensity a b t) = 1 := by
  simp only [cubeDensity]
  rw [integral_indicator measurableSet_Icc, integral_div, ← cubeMass,
    div_self (cubeMass_pos ha hb hab).ne']

lemma cubeDensity_nonneg {a b : ℝ} (ha : (1 : ℝ)/2 ≤ a) (hb : b ≤ 3) (hab : a < b)
    (t : ℝ) : 0 ≤ cubeDensity a b t := by
  apply Set.indicator_nonneg
  intro t ht
  exact div_nonneg ((by norm_num : (0 : ℝ) ≤ 1/27).trans
    (inverseCube_bounds ⟨ha.trans ht.1, ht.2.trans hb⟩).1) (cubeMass_pos ha hb hab).le

lemma cubeDensity_bound {a b : ℝ} (ha : (1 : ℝ)/2 ≤ a) (hb : b ≤ 3) (hab : a < b)
    (t : ℝ) : cubeDensity a b t ≤ 216/(b-a) := by
  by_cases ht : t ∈ Icc a b
  · rw [cubeDensity, Set.indicator_of_mem ht]
    have hM := cubeMass_pos ha hb hab
    have hl := cubeMass_lower ha hb
    have hbnd := (inverseCube_bounds ⟨ha.trans ht.1, ht.2.trans hb⟩).2
    apply (div_le_iff₀ hM).mpr
    have hD : 0 < b-a := sub_pos.mpr hab
    have hl' : 8 ≤ 216/(b-a) * cubeMass a b := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hD).mpr
      linarith
    exact hbnd.trans hl'
  · simp only [cubeDensity, Set.indicator_of_notMem ht]
    positivity

/-- The concrete normalized inverse-cube density, with an absolute width bound. -/
def inverseCubeDensity (a b : ℝ) (ha : (1 : ℝ)/2 ≤ a) (hb : b ≤ 3) (hab : a < b) :
    RadiusDensity a b ⟨216/(b-a), by positivity⟩ where
  toFun := cubeDensity a b
  integrable := cubeDensity_integrable (by linarith)
  nonneg := cubeDensity_nonneg ha hb hab
  integral_one := cubeDensity_integral ha hb hab
  bound := cubeDensity_bound ha hb hab
  support t ht := Set.indicator_of_notMem ht _

def enlarge {a b a' b' : ℝ} {M N : ℝ≥0} (k : RadiusDensity a b M)
    (ha : a' ≤ a) (hb : b ≤ b') (hM : M ≤ N) : RadiusDensity a' b' N where
  toFun := k
  integrable := k.integrable
  nonneg := k.nonneg
  integral_one := k.integral_one
  bound t := (k.bound t).trans hM
  support t ht := k.support t (fun h => ht ⟨ha.trans h.1, h.2.trans hb⟩)

end DiskKernels

namespace DiskMoments
open DiskKernels

def moment (g : ℂ → ℝ) (x : ℂ) (t : ℝ) : ℂ :=
  ∫ y in Metric.ball x t, star (y-x) * gradient g y

def radialDerivative (g : ℂ → ℝ) (x : ℂ) (t : ℝ) : ℝ :=
  (∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x+t•z)) z) / Real.pi

end DiskMoments

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LocalCancellation1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal

noncomputable section

namespace SignedDisk

namespace LocalCancellation

structure ErrorPiece (Cs : ℝ) where
  density : ℂ → ℂ
  integrable : Integrable density
  size : ℝ
  size_pos : 0 < size
  size_le_one : size ≤ 1
  center : ℂ
  zero_mass : size < 1 → ∫ y, density y = 0
  support : size < 1 → ∀ᵐ y, density y ≠ 0 → ‖y-center‖ ≤ Cs * size

def ErrorPiece.mass {Cs : ℝ} (b : ErrorPiece Cs) : ℝ := ∫ y, ‖b.density y‖

def correction (x z y : ℂ) : ℂ := 1 - star (y-x) / star (z-x)

variable {ι : Type*} [Fintype ι]

def errorPrice {Cs : ℝ} (b : ι → ErrorPiece Cs) (α : ℝ) : ℝ :=
  ∑ d, (b d).size ^ α * (b d).mass

end LocalCancellation

open MeasureTheory Set Filter
open scoped Topology NNReal Real

namespace LocalCancellation

/-- Norm total-variation measure of an actual complex density. -/
def densityMeasure (b : ℂ → ℂ) : Measure ℂ := volume.withDensity (fun y => ENNReal.ofReal ‖b y‖)

variable {ι : Type*} [Fintype ι]

def coarseMeasure {Cs : ℝ} (b : ι → ErrorPiece Cs) (δ : ℝ) : Measure ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), densityMeasure (b d).density

def coarseMass {Cs : ℝ} (b : ι → ErrorPiece Cs) (δ : ℝ) (D : Set ℂ) : ℝ :=
  ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ∫ y in D, ‖(b d).density y‖

end LocalCancellation

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LocalCancellation2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace DiskGeometry

def shellMass (ν : Measure ℂ) (r δ : ℝ) (x : ℂ) : ℝ≥0∞ := ν (thinShell x r δ)

end DiskGeometry

namespace DiskScales

def width (δ : ℝ) (n : ℕ) : ℝ := δ*(1/2 : ℝ)^n

lemma width_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 < width δ n := by
  unfold width
  positivity

end DiskScales

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LocalCancellation3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace DiskGeometry

def endpointFailure (ν : Measure ℂ) (δ U : ℝ) : Set ℂ :=
  {x | ENNReal.ofReal U ≤ shellMass ν 1 (2*δ) x} ∪
  {x | ENNReal.ofReal U ≤ shellMass ν 2 (2*δ) x}

end DiskGeometry

namespace DiskMoments
open DiskKernels DiskGeometry

def EndpointRadius (g : ℂ → ℝ) (x : ℂ) (r : ℝ) : Prop :=
  r ∈ Icc (1 : ℝ) 2 ∧ (r = 1 ∨ r = 2 ∨
    ∀ t ∈ Icc (1 : ℝ) 2, signedAverage g x t ≤ signedAverage g x r)

end DiskMoments

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskScales1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace DiskScales

def sizeTailConstant : ℝ :=
  156/(1-(1/2 : ℝ)^(14/25 : ℝ))+2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ))

end DiskScales

namespace DyadicMajorant

section
variable {X : Type*} [MeasurableSpace X]

/-- A Borel price built from exceptions, rather than a measurability-dependent
selection of maximizing radii. -/
def price (t : ℝ) (E : ℕ → Set X) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal t + ∑' n : ℕ, (E n).indicator (fun _ => ENNReal.ofReal (t*2^(n+1))) x

end

end DyadicMajorant

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LocalCancellation4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace LocalCancellation

section
open DiskKernels DiskGeometry

/-- An integrable aggregate of vectors in a fixed acute cone. It covers the
positive pieces by taking their sum; no direction is imposed on errors. -/
structure ConeDensity (e : ℂ) (κ : ℝ) where
  density : ℂ → ℂ
  integrable : Integrable density
  cone : ∀ᵐ y, κ*‖density y‖ ≤ inner ℝ e (density y)

open DiskKernels DiskGeometry DiskScales

end

open DiskKernels DiskGeometry DiskScales

end LocalCancellation

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskScales2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace DiskScales

def errorGapConstant (Cs : ℝ) : ℝ :=
  2*(1+216*Cs)+(16+4538*Cs)/(1-(1/2 : ℝ)^(1/10 : ℝ))

def directionGapConstant (Cs κ : ℝ) : ℝ :=
  (16+4538*Cs)+4*(errorGapConstant Cs/κ)+14+(16+4538*Cs)/(1-(1/2 : ℝ)^(1/10 : ℝ))

end DiskScales

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

def directionShellBound {Cs : ℝ} (b : ι → ErrorPiece Cs) (κ t δ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ ^ 2 *
    (ENNReal.ofReal (156*δ/δ^(1/5 : ℝ))*
      ENNReal.ofReal (coarseMass b δ univ)*ENNReal.ofReal (coarseMass b δ univ)) +
  (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ *
    ((ENNReal.ofReal (6*Real.pi)*
      ENNReal.ofReal (2*(200*δ/(δ^(1/5 : ℝ))^2)*
        (1+((errorGapConstant Cs/κ)*t*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ)))))*
      ENNReal.ofReal (coarseMass b δ univ))

end LocalCancellation

namespace DiskMoments
open DiskKernels

def NeighborhoodRadius (g : ℂ → ℝ) (x : ℂ) (r : ℝ) : Prop :=
  r ∈ Icc (1 : ℝ) 2 ∧ ∀ t : ℝ, 0 < t → |t-r| ≤ 1/4 →
    signedAverage g x t ≤ signedAverage g x r

end DiskMoments

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskScales3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace DiskScales

def directionTailConstant (Cs κ : ℝ) : ℝ := (1+errorGapConstant Cs/κ)*sizeTailConstant

end DiskScales

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace DiskMaximalTools

/-- A countable measurable envelope, sufficiently rich for every actual disk. -/
def rationalMaximal (ν : Measure ℂ) (x : ℂ) : ℝ≥0∞ :=
  ⨆ (q : ℚ) (_ : 0 < q), ν (ball x q) / volume (ball x q)

end DiskMaximalTools

open MeasureTheory Set
open scoped ENNReal NNReal

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskMaximalTools1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ScalarCancellation

/-- A nonnegative scalar residual retaining exactly the net mass. Its removal
has the exact cancellation defect as L1 cost. -/
theorem positive_residual {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} (hh : Integrable h μ) (hc : 0 ≤ ∫ x, h x ∂μ) :
    ∃ ρ : α → ℝ, Integrable ρ μ ∧ (∀ x, 0 ≤ ρ x) ∧
      (∀ x, ρ x ≤ max (h x) 0) ∧ (∫ x, ρ x ∂μ) = ∫ x, h x ∂μ ∧
      (∫ x, |h x-ρ x| ∂μ) = (∫ x, |h x| ∂μ) - ∫ x, h x ∂μ ∧
      (∀ x, h x = 0 → ρ x = 0) := by
  let p : α → ℝ := fun x => max (h x) 0
  have hp : Integrable p μ := by
    convert (hh.add hh.abs).div_const 2 using 1
    funext x
    by_cases hx : 0 ≤ h x
    · simp only [p,max_eq_left hx,abs_of_nonneg hx,Pi.add_apply]
      ring
    · simp only [p,max_eq_right (le_of_not_ge hx),abs_of_nonpos (le_of_not_ge hx),Pi.add_apply]
      ring
  have hp0 : 0 ≤ ∫ x, p x ∂μ := integral_nonneg (fun x => le_max_right _ _)
  have hcp : (∫ x, h x ∂μ) ≤ ∫ x, p x ∂μ := integral_mono hh hp (fun x => le_max_left _ _)
  by_cases hP : (∫ x, p x ∂μ) = 0
  · have hc0 : (∫ x, h x ∂μ) = 0 := le_antisymm (hP ▸ hcp) hc
    refine ⟨0,integrable_zero _ _ _,fun _ => le_rfl,fun x => le_max_right _ _,?_,?_,fun _ _ => rfl⟩
    · simp [hc0]
    · simp [hc0]
  · have hPpos : 0 < ∫ x, p x ∂μ := lt_of_le_of_ne hp0 (Ne.symm hP)
    let q := (∫ x, h x ∂μ)/(∫ x, p x ∂μ)
    have hq0 : 0 ≤ q := div_nonneg hc hp0
    have hq1 : q ≤ 1 := (div_le_one hPpos).mpr hcp
    let ρ : α → ℝ := fun x => q*p x
    have hρ : Integrable ρ μ := hp.const_mul q
    have hρ0 : ∀ x, 0 ≤ ρ x := fun x => mul_nonneg hq0 (le_max_right _ _)
    have hρp : ∀ x, ρ x ≤ p x := fun x => mul_le_of_le_one_left (le_max_right _ _) hq1
    have hi : (∫ x, ρ x ∂μ) = ∫ x, h x ∂μ := by
      rw [show ρ = fun x => q*p x from rfl,integral_const_mul]
      exact div_mul_cancel₀ _ hP
    have habs : ∀ x, |h x-ρ x| = |h x|-ρ x := by
      intro x
      by_cases hhx : 0 ≤ h x
      · rw [abs_of_nonneg hhx,abs_of_nonneg]
        simpa only [p,max_eq_left hhx] using sub_nonneg.mpr (hρp x)
      · have hx0 : h x ≤ 0 := (lt_of_not_ge hhx).le
        have : ρ x = 0 := by simp [ρ,p,max_eq_right hx0]
        simp [this]
    refine ⟨ρ,hρ,hρ0,hρp,hi,?_,?_⟩
    · simp_rw [habs]
      rw [integral_sub hh.abs hρ,hi]
    · intro x hx
      simp [ρ,p,hx]

/-- Every integrable scalar density splits into a constant-sign root and a
zero-mass error, without replacing the actual terminal density by its mass. -/
theorem residual_split {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} (hh : Integrable h μ) :
    ∃ ρ β : α → ℝ, Integrable ρ μ ∧ Integrable β μ ∧
      (∀ x, h x = ρ x+β x) ∧ (∫ x, ρ x ∂μ) = ∫ x, h x ∂μ ∧
      (∫ x, β x ∂μ) = 0 ∧ (∫ x, |ρ x| ∂μ) = |∫ x, h x ∂μ| ∧
      (∫ x, |β x| ∂μ) = (∫ x, |h x| ∂μ)-|∫ x, h x ∂μ| ∧
      ((0 ≤ ∫ x, h x ∂μ) → ∀ x, 0 ≤ ρ x) ∧
      ((∫ x, h x ∂μ) < 0 → ∀ x, ρ x ≤ 0) ∧
      (∀ x, h x = 0 → ρ x = 0 ∧ β x = 0) := by
  by_cases hc : 0 ≤ ∫ x, h x ∂μ
  · obtain ⟨ρ,hρ,hρ0,_,hi,hcost,hzero⟩ := positive_residual hh hc
    refine ⟨ρ,fun x => h x-ρ x,hρ,hh.sub hρ,fun x => by ring,hi,?_,?_,?_,
      fun _ => hρ0,fun hn => (not_lt_of_ge hc hn).elim,?_⟩
    · rw [integral_sub hh hρ,hi,sub_self]
    · simp_rw [abs_of_nonneg (hρ0 _)]
      rw [hi,abs_of_nonneg hc]
    · rwa [abs_of_nonneg hc]
    · intro x hx
      simp [hx,hzero x hx]
  · have hc' : (∫ x, h x ∂μ) < 0 := lt_of_not_ge hc
    have hn : 0 ≤ ∫ x, -h x ∂μ := by rw [integral_neg]; linarith
    obtain ⟨ρ,hρ,hρ0,_,hi,hcost,hzero⟩ := positive_residual hh.neg hn
    have hi' : (∫ x, ρ x ∂μ) = -(∫ x, h x ∂μ) := by simpa only [Pi.neg_apply,integral_neg] using hi
    refine ⟨fun x => -ρ x,fun x => h x+ρ x,hρ.neg,hh.add hρ,fun x => by ring,?_,?_,?_,?_,
      fun hn => (not_le_of_gt hc' hn).elim,fun _ x => neg_nonpos.mpr (hρ0 x),?_⟩
    · rw [integral_neg,hi',neg_neg]
    · rw [integral_add hh hρ,hi',add_neg_cancel]
    · simp_rw [abs_neg,abs_of_nonneg (hρ0 _)]
      rw [hi',abs_of_neg hc']
    · have heq : (fun x => |-h x-ρ x|) = fun x => |h x+ρ x| := by
        funext x
        rw [show -h x-ρ x = -(h x+ρ x) by ring,abs_neg]
      simp only [Pi.neg_apply] at hcost
      rw [heq] at hcost
      simpa only [abs_neg,integral_neg,abs_of_neg hc',sub_neg_eq_add] using hcost
    · intro x hx
      have hz := hzero x (by simp [hx])
      simp [hx,hz]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Canonical positive/negative root selected from the proved scalar splitting,
not an assumed decomposition. -/
def root (μ : Measure α) (f : α → ℝ) : α → ℝ := by
  classical
  exact if h : Integrable f μ then (residual_split h).choose else 0

lemma root_spec {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (root μ f) μ ∧
      (∫ x, root μ f x ∂μ) = ∫ x, f x ∂μ ∧
      (∫ x, |root μ f x| ∂μ) = |∫ x, f x ∂μ| ∧
      (∫ x, |f x-root μ f x| ∂μ) = (∫ x, |f x| ∂μ)-|∫ x, f x ∂μ| ∧
      ((0 ≤ ∫ x, f x ∂μ) → ∀ x, 0 ≤ root μ f x) ∧
      ((∫ x, f x ∂μ) < 0 → ∀ x, root μ f x ≤ 0) ∧
      (∀ x, f x = 0 → root μ f x = 0) := by
  rw [root,dite_eq_left hf]
  obtain ⟨β,hR,_,hdec,hi,_,habs,hcost,hpos,hneg,hsupp⟩ := (residual_split hf).choose_spec
  refine ⟨hR,hi,habs,?_,hpos,hneg,fun x hx => (hsupp x hx).1⟩
  convert hcost using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp only; rw [hdec x]; congr 1; ring)

variable {ι : Type*} [Fintype ι]

def refined (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ) : ℕ → ι → α → ℝ
  | 0,q => f q
  | k+1,q => fun x => ∑ s, w k q s*refined w f k s x

def roots (μ : Measure α) (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ) : ℕ → ι → α → ℝ
  | 0,q => root μ (f q)
  | k+1,q => root μ (fun x => ∑ s, w k q s*roots μ w f k s x)

def errors (μ : Measure α) (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ) : ℕ → ι → α → ℝ
  | 0,q => fun x => f q x-roots μ w f 0 q x
  | k+1,q => fun x => (∑ s, w k q s*roots μ w f k s x)-roots μ w f (k+1) q x

lemma refined_integrable (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    Integrable (refined w f k q) μ := by
  induction k generalizing q with
  | zero => exact hf q
  | succ k ih => exact integrable_finsetSum _ (fun s _ => (ih s).const_mul _)

lemma roots_integrable (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    Integrable (roots μ w f k q) μ := by
  induction k generalizing q with
  | zero => exact (root_spec (hf q)).1
  | succ k ih => exact (root_spec (integrable_finsetSum _ (fun s _ => (ih s).const_mul _))).1

lemma roots_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, roots μ w f k q x ∂μ) = ∫ x, refined w f k q x ∂μ := by
  induction k generalizing q with
  | zero => exact (root_spec (hf q)).2.1
  | succ k ih =>
    rw [roots,(root_spec (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _))).2.1,
      refined,integral_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _),
      integral_finsetSum _ (fun s _ => (refined_integrable w hf k s).const_mul _)]
    simp_rw [integral_const_mul,ih]

lemma errors_integrable (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    Integrable (errors μ w f k q) μ := by
  cases k with
  | zero => exact (hf q).sub (roots_integrable w hf 0 q)
  | succ k =>
    exact (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _)).sub
      (roots_integrable w hf (k+1) q)

lemma errors_zero_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, errors μ w f k q x ∂μ) = 0 := by
  cases k with
  | zero =>
    rw [errors,integral_sub (hf q) (roots_integrable w hf 0 q),roots_mass]
    exact sub_self _
    exact hf
  | succ k =>
    rw [errors,integral_sub
      (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _))
      (roots_integrable w hf (k+1) q),roots,
      (root_spec (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _))).2.1,
      sub_self]

/-- Support nesting is preserved by the new construction, even when child
scalar masses vanish or overlapping densities cancel each other. -/
theorem roots_errors_support (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (S : ℕ → ι → Set α)
    (hfS : ∀ q x, x ∉ S 0 q → f q x = 0)
    (hS : ∀ k q s, w k q s ≠ 0 → S k s ⊆ S (k+1) q) :
    ∀ k q x, x ∉ S k q → roots μ w f k q x = 0 ∧ errors μ w f k q x = 0 := by
  intro k
  induction k with
  | zero =>
    intro q x hx
    have hf0 := hfS q x hx
    have hR0 := (root_spec (hf q)).2.2.2.2.2.2 x hf0
    exact ⟨hR0,by simp only [errors,roots,hf0,hR0,sub_self]⟩
  | succ k ih =>
    intro q x hx
    have hz : (∑ s, w k q s*roots μ w f k s x) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      by_cases hw : w k q s = 0
      · simp [hw]
      · have hs : x ∉ S k s := fun h => hx (hS k q s hw h)
        rw [(ih s x hs).1,mul_zero]
    have hR0 := (root_spec (integrable_finsetSum Finset.univ
      (fun s _ => (roots_integrable w hf k s).const_mul (w k q s)))).2.2.2.2.2.2 x hz
    exact ⟨hR0,by simp only [errors,roots,hz,hR0,sub_self]⟩

end ScalarCancellation

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_ScalarCancellation1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace DyadicHats

def tent (x : ℝ) : ℝ := max (1-|x|) 0

lemma tent_nonneg (x : ℝ) : 0 ≤ tent x := le_max_right _ _
lemma tent_le_one (x : ℝ) : tent x ≤ 1 := max_le (by linarith [abs_nonneg x]) (by norm_num)
lemma tent_pos_iff (x : ℝ) : 0 < tent x ↔ |x| < 1 := by
  unfold tent
  rw [lt_max_iff]
  constructor
  · intro h; rcases h with h|h <;> linarith
  · intro h; exact Or.inl (by linarith)
lemma tent_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ |x|) : tent x = 0 := by
  exact max_eq_right (by linarith)
lemma tent_of_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : tent x = 1-x := by
  simp only [tent, abs_of_nonneg hx, max_eq_left (sub_nonneg.mpr hx1)]
lemma tent_of_nonpos {x : ℝ} (hx : x ≤ 0) (hx1 : -1 ≤ x) : tent x = 1+x := by
  rw [tent,abs_of_nonpos hx,max_eq_left (by linarith)]
  ring
lemma tent_neg (x : ℝ) : tent (-x) = tent x := by simp only [tent,abs_neg]

lemma lipschitz_tent : LipschitzWith 1 tent := by
  have hn : LipschitzWith 1 (fun x : ℝ => |x|) := by
    change LipschitzWith 1 (norm : ℝ → ℝ)
    exact lipschitzWith_one_norm
  have h : LipschitzWith 1 (fun x : ℝ => 1-|x|) := by
    simpa only [zero_add] using (LipschitzWith.const (1:ℝ)).sub hn
  change LipschitzWith 1 (fun x : ℝ => max (1-|x|) 0)
  simpa only [max_eq_left (by norm_num : (0:ℝ≥0) ≤ 1)] using h.max (LipschitzWith.const (0:ℝ))

theorem tent_refine (x : ℝ) :
    tent x = (1/2)*tent (2*x+1)+tent (2*x)+(1/2)*tent (2*x-1) := by
  wlog hx : 0 ≤ x generalizing x
  · have h := this (-x) (by linarith)
    rw [tent_neg] at h
    have heq1 : 2*(-x)+1 = -(2*x-1) := by ring
    have heq2 : 2*(-x) = -(2*x) := by ring
    have heq3 : 2*(-x)-1 = -(2*x+1) := by ring
    rw [heq1,heq3,heq2,tent_neg,tent_neg,tent_neg] at h
    linarith
  have hplus : tent (2*x+1) = 0 := tent_eq_zero_of_one_le (by rw [abs_of_nonneg (by linarith)]; linarith)
  rw [hplus,mul_zero,zero_add]
  by_cases hx1 : x ≤ 1/2
  · rw [tent_of_nonneg hx (by linarith),tent_of_nonneg (by linarith) (by linarith),
      tent_of_nonpos (by linarith) (by linarith)]
    ring
  · by_cases hx2 : x ≤ 1
    · rw [tent_of_nonneg hx hx2,tent_eq_zero_of_one_le (by rw [abs_of_nonneg (by linarith)]; linarith),
        tent_of_nonneg (by linarith) (by linarith)]
      ring
    · rw [tent_eq_zero_of_one_le (by rw [abs_of_nonneg hx]; linarith),
        tent_eq_zero_of_one_le (by rw [abs_of_nonneg (by linarith)]; linarith),
        tent_eq_zero_of_one_le (by rw [abs_of_nonneg (by linarith)]; linarith)]
      ring

lemma tent_floor (x : ℝ) : tent (x-⌊x⌋) = 1-(x-⌊x⌋) :=
  tent_of_nonneg (sub_nonneg.mpr (Int.floor_le x)) (by linarith [Int.lt_floor_add_one x])
lemma tent_floor_succ (x : ℝ) : tent (x-(⌊x⌋+1)) = x-⌊x⌋ := by
  rw [tent_of_nonpos (by linarith [Int.lt_floor_add_one x]) (by linarith [Int.floor_le x])]
  ring
lemma tent_floor_partition (x : ℝ) : tent (x-⌊x⌋)+tent (x-(⌊x⌋+1)) = 1 := by
  rw [tent_floor,tent_floor_succ]; ring

lemma tent_eq_zero_of_ne_floor {x : ℝ} {j : ℤ}
    (hj : j ≠ ⌊x⌋) (hj' : j ≠ ⌊x⌋+1) : tent (x-j) = 0 := by
  apply tent_eq_zero_of_one_le
  have hcases : j < ⌊x⌋ ∨ ⌊x⌋+1 < j := by omega
  rcases hcases with h|h
  · have hjle : (j:ℝ)+1 ≤ ⌊x⌋ := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith [Int.floor_le x])]
    linarith [Int.floor_le x]
  · have hjle : (⌊x⌋:ℝ)+2 ≤ j := by exact_mod_cast (show ⌊x⌋+2 ≤ j by omega)
    rw [abs_of_nonpos (by linarith [Int.lt_floor_add_one x])]
    linarith [Int.lt_floor_add_one x]

lemma summable_tent (x : ℝ) : Summable (fun j : ℤ => tent (x-j)) := by
  apply summable_of_ne_finset_zero (s := {⌊x⌋,⌊x⌋+1})
  intro j hj
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
  exact tent_eq_zero_of_ne_floor hj.1 hj.2

/-- Partition of unity on the complete integer grid, including grid boundaries. -/
theorem tsum_tent (x : ℝ) : (∑' j : ℤ, tent (x-j)) = 1 := by
  rw [tsum_eq_sum (s := {⌊x⌋,⌊x⌋+1}) (fun j hj => by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
    exact tent_eq_zero_of_ne_floor hj.1 hj.2)]
  rw [Finset.sum_insert (by simp),Finset.sum_singleton]
  simpa only [Int.cast_add,Int.cast_one] using tent_floor_partition x

/-- Actual Euclidean-plane product hats at a positive physical scale. -/
def hat (r : ℝ) (p : ℤ × ℤ) (x : ℂ) : ℝ :=
  tent (x.re/r-p.1)*tent (x.im/r-p.2)
lemma hat_nonneg (r : ℝ) (p : ℤ × ℤ) (x : ℂ) : 0 ≤ hat r p x :=
  mul_nonneg (tent_nonneg _) (tent_nonneg _)
lemma hat_le_one (r : ℝ) (p : ℤ × ℤ) (x : ℂ) : hat r p x ≤ 1 := by
  calc
    _ ≤ 1*1 := mul_le_mul (tent_le_one _) (tent_le_one _) (tent_nonneg _) (by norm_num)
    _ = _ := one_mul _
lemma continuous_hat (r : ℝ) (p : ℤ × ℤ) : Continuous (hat r p) := by
  unfold hat
  exact (lipschitz_tent.continuous.comp (by fun_prop)).mul
    (lipschitz_tent.continuous.comp (by fun_prop))

lemma summable_hat (r : ℝ) (x : ℂ) : Summable (fun p : ℤ × ℤ => hat r p x) :=
  (summable_tent (x.re/r)).mul_of_nonneg (summable_tent (x.im/r))
    (fun _ => tent_nonneg _) (fun _ => tent_nonneg _)

theorem tsum_hat (r : ℝ) (x : ℂ) : (∑' p : ℤ × ℤ, hat r p x) = 1 := by
  rw [Summable.tsum_prod (summable_hat r x)]
  simp_rw [hat,tsum_mul_left,tsum_tent,mul_one]
  exact tsum_tent _

/-- One-dimensional refinement written with the actual interpolation weights. -/
lemma tent_half_integer {j : ℤ} (hj : j ∉ Finset.Icc (-1) 1) : tent ((j:ℝ)/2) = 0 := by
  apply tent_eq_zero_of_one_le
  simp only [Finset.mem_Icc,not_and_or,not_le] at hj
  rcases hj with hj|hj
  · have h : (j:ℝ) ≤ -2 := by exact_mod_cast (show j ≤ -2 by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h : (2:ℝ) ≤ j := by exact_mod_cast (show 2 ≤ j by omega)
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma tent_half_refine (x : ℝ) :
    tent (x/2) = ∑ j ∈ Finset.Icc (-1:ℤ) 1, tent ((j:ℝ)/2)*tent (x-j) := by
  rw [show Finset.Icc (-1:ℤ) 1 = {-1,0,1} by decide]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,
    Finset.mem_singleton,Int.reduceEq,or_self,not_false_eq_true,
    Int.cast_neg,Int.cast_one,Int.cast_zero,sub_neg_eq_add,sub_zero]
  norm_num [tent] at ⊢
  have h := tent_refine (x/2)
  unfold tent at h
  convert h using 1
  ring_nf

lemma tent_half_tsum_refine (x : ℝ) (p : ℤ) :
    tent (x/2-p) = ∑' j : ℤ, tent ((j:ℝ)/2-p)*tent (x-j) := by
  have heq : (∑' j : ℤ, tent ((j:ℝ)/2-p)*tent (x-j)) =
      ∑' j : ℤ, tent ((j:ℝ)/2)*tent ((x-2*p)-j) := by
    rw [← (Equiv.addRight (2*p)).tsum_eq]
    apply tsum_congr
    intro j
    simp only [Equiv.coe_addRight,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
    congr 2 <;> ring
  rw [heq,tsum_eq_sum (s := Finset.Icc (-1:ℤ) 1)]
  · convert tent_half_refine (x-2*p) using 1
    congr 1
    ring
  · intro j hj
    rw [tent_half_integer hj,zero_mul]

lemma summable_tent_weight (x : ℝ) (a : ℤ → ℝ) :
    Summable (fun j : ℤ => a j*tent (x-j)) := by
  apply summable_of_ne_finset_zero (s := {⌊x⌋,⌊x⌋+1})
  intro j hj
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
  rw [tent_eq_zero_of_ne_floor hj.1 hj.2,mul_zero]

/-- Positive interpolation coefficients, indexed by coarse and fine grid indices. -/
def step (p q : ℤ × ℤ) : ℝ :=
  tent ((q.1:ℝ)/2-p.1)*tent ((q.2:ℝ)/2-p.2)
lemma step_nonneg (p q : ℤ × ℤ) : 0 ≤ step p q :=
  mul_nonneg (tent_nonneg _) (tent_nonneg _)

lemma summable_step_hat (p : ℤ × ℤ) (r : ℝ) (x : ℂ) :
    Summable (fun q : ℤ × ℤ => step p q*hat r q x) := by
  have h1 := summable_tent_weight (x.re/r) (fun j => tent ((j:ℝ)/2-p.1))
  have h2 := summable_tent_weight (x.im/r) (fun j => tent ((j:ℝ)/2-p.2))
  convert h1.mul_of_nonneg h2 (fun j => mul_nonneg (tent_nonneg _) (tent_nonneg _))
    (fun j => mul_nonneg (tent_nonneg _) (tent_nonneg _)) using 1
  funext q
  simp only [step,hat]
  ring

/-- Exact planar hat refinement; no grid truncation is hidden in the identity. -/
theorem hat_refine (r : ℝ) (p : ℤ × ℤ) (x : ℂ) :
    hat (2*r) p x = ∑' q : ℤ × ℤ, step p q*hat r q x := by
  rw [Summable.tsum_prod (summable_step_hat p r x)]
  have heq : (fun j : ℤ => ∑' k : ℤ,
      step p (j,k)*hat r (j,k) x) = fun j : ℤ =>
      (tent ((j:ℝ)/2-p.1)*tent (x.re/r-j))*
        ∑' k : ℤ, tent ((k:ℝ)/2-p.2)*tent (x.im/r-k) := by
    funext j
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    simp only [step,hat]
    ring
  rw [heq,tsum_mul_right,← tent_half_tsum_refine,← tent_half_tsum_refine]
  unfold hat
  congr 2 <;> ring

end DyadicHats

open MeasureTheory Set Metric
open scoped ENNReal NNReal

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_PlanePotential1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal

open Finset
open scoped RealInnerProductSpace

namespace FiniteLabels
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

structure Law (ι : Type*) [Fintype ι] where
  mass : ι → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1

instance instCoeFunLawForallReal : CoeFun (Law ι) (fun _ => ι → ℝ) := ⟨Law.mass⟩

def delta [DecidableEq ι] (i : ι) : Law ι where
  mass j := if j=i then 1 else 0
  nonneg j := by split_ifs <;> norm_num
  total := by simp

def move (μ : Law ι) (P : ι → Law κ) : Law κ where
  mass j := ∑ i, μ i*P i j
  nonneg j := sum_nonneg fun i _ => mul_nonneg (μ.nonneg i) ((P i).nonneg j)
  total := by
    rw [sum_comm]
    simp_rw [← mul_sum,(P _).total,mul_one]
    exact μ.total

def l1dist (a b : ι → ℝ) : ℝ := ∑ i, |a i-b i|

end FiniteLabels

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace PlanePotential

def greenScalar (ψ : ℂ → ℝ) (x y : ℂ) : ℝ :=
  ∫ t in Ioc (0:ℝ) 1, ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)
def green (ψ : ℂ → ℝ) (x y : ℂ) : ℂ := -greenScalar ψ x y • (y-x)

end PlanePotential

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_VectorRefinement1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace PlanePotential

def segmentForm (ψ g : ℂ → ℝ) (x : ℂ) (t : ℝ) (z : ℂ) : ℝ :=
  ψ z*fderiv ℝ g (x+t • (z-x)) (z-x)
def pullbackForm (ψ g : ℂ → ℝ) (x : ℂ) (t : ℝ) (y : ℂ) : ℝ :=
  ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)*fderiv ℝ g y (y-x)

end PlanePotential

open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

open scoped RealInnerProductSpace
namespace PlanePotential

/-- The center is subtracted only off the near region, so this measurable
kernel retains integrability at the center and realizes zero-mass cancellation. -/
def cancelledGreen (ψ : ℂ → ℝ) (z : ℂ) (a : ℝ) (x y : ℂ) : ℂ :=
  if ‖x-z‖ ≤ 2*a then green ψ x y else green ψ x y-green ψ x z

end PlanePotential

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_PlanePotential2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace SignedDisk

open scoped RealInnerProductSpace

namespace IntrinsicMarks

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def direction (e v : E) : E := by
  classical
  exact if v = 0 then e else ‖v‖⁻¹ • v

lemma norm_direction {e : E} (he : ‖e‖ = 1) (v : E) : ‖direction e v‖ = 1 := by
  by_cases hv : v = 0
  · simp [direction,hv,he]
  · rw [direction,ite_eq_right hv,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

lemma mass_direction (e v : E) : ‖v‖ • direction e v = v := by
  by_cases hv : v = 0
  · simp [hv]
  · simp [direction,hv,smul_smul,norm_ne_zero_iff.mpr hv]

/-- Finite uniform branching includes each finite positive-refinement path forest
by padding absent children with zero vectors. No triangle defect is assumed. -/
inductive Tree (ι : Type*) (E : Type*) where
  | leaf : E → Tree ι E
  | branch : (ι → Tree ι E) → Tree ι E

variable {ι : Type*} [Fintype ι]

def vector : Tree ι E → E
  | .leaf v => v
  | .branch t => ∑ i, vector (t i)

def terminalMass : Tree ι E → ℝ
  | .leaf v => ‖v‖
  | .branch t => ∑ i, terminalMass (t i)

/-- Only the first crossing from the most recent marked direction is counted;
a crossing resets the anchor before descending further. -/
def markedCost (e : E) (δ : ℝ) : Tree ι E → E → ℝ
  | .leaf v, n => if δ < ‖direction e v-n‖ then ‖v‖ else 0
  | .branch t, n =>
      let v := ∑ i, vector (t i)
      if δ < ‖direction e v-n‖ then
        ‖v‖ + ∑ i, markedCost e δ (t i) (direction e v)
      else ∑ i, markedCost e δ (t i) n

def costWithRoot (e : E) (δ : ℝ) : Tree ι E → ℝ
  | .leaf v => ‖v‖
  | .branch t =>
      let v := ∑ i, vector (t i)
      ‖v‖+∑ i, markedCost e δ (t i) (direction e v)

end

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The fraction of the child capacity occupied by particles already alive. -/
def survival (t : ι → Tree ι E) : ℝ :=
  ‖∑ i, vector (t i)‖ / ∑ i, ‖vector (t i)‖

/-- Explicit finite weighted evaluation on terminal paths, for the population
born at the current root. Every branching has its true capacity ratio. -/
def rootEval : Tree ι E → (List ι → ℝ) → ℝ
  | .leaf v, F => ‖v‖ * F []
  | .branch t, F => survival t * ∑ i, rootEval (t i) (fun p => F (i::p))

/-- Explicit finite evaluation of populations born strictly below this root.
The complete prefix is retained, including the part before birth. -/
def lateEval : Tree ι E → (List ι → ℕ → ℝ) → ℝ
  | .leaf _, _ => 0
  | .branch t, F =>
      (1-survival t) * (∑ i, rootEval (t i) (fun p => F (i::p) 1)) +
        ∑ i, lateEval (t i) (fun p b => F (i::p) (b+1))

def particleEval (t : Tree ι E) (F : List ι → ℕ → ℝ) : ℝ :=
  rootEval t (fun p => F p 0) + lateEval t F

/-- Sum a node charge only at and after the particle's birth. -/
def pathCharge (C : List ι → ℝ) : List ι → ℕ → ℝ
  | [], 0 => C []
  | [], _+1 => 0
  | i::p, 0 => C [] + pathCharge (fun q => C (i::q)) p 0
  | i::p, b+1 => pathCharge (fun q => C (i::q)) p b

def nodeCharge : Tree ι E → (List ι → ℝ) → ℝ
  | .leaf v, C => ‖v‖*C []
  | .branch t, C => ‖∑ i, vector (t i)‖*C [] + ∑ i, nodeCharge (t i) (fun p => C (i::p))

end IntrinsicMarks

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_IntrinsicMarks1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace SignedDisk

namespace IntrinsicMarks
open Finset
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

def validPath : Tree ι E → List ι → Prop
  | .leaf _, p => p = []
  | .branch _, [] => False
  | .branch t, i::p => validPath (t i) p

/-- Intrinsic marks as an actual function on prefixes, with first-crossing
reset. Prefixes outside the tree have zero charge. -/
def markIndicator (e : E) (δ : ℝ) : Tree ι E → E → List ι → ℝ
  | .leaf v, n, [] => if δ < ‖direction e v-n‖ then 1 else 0
  | .leaf _, _, _::_ => 0
  | .branch t, n, [] => if δ < ‖direction e (∑ i, vector (t i))-n‖ then 1 else 0
  | .branch t, n, i::p =>
      let v := ∑ j, vector (t j)
      markIndicator e δ (t i) (if δ < ‖direction e v-n‖ then direction e v else n) p

def rootMarkIndicator (e : E) (δ : ℝ) : Tree ι E → List ι → ℝ
  | _, [] => 1
  | .leaf _, _::_ => 0
  | .branch t, i::p => markIndicator e δ (t i) (direction e (∑ j, vector (t j))) p

end IntrinsicMarks

namespace SignedAssembly
open Finset
open scoped RealInnerProductSpace
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure RowJet (ι E : Type*) [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  law : FiniteLabels.Law ι
  grad : ι → E
  total_grad : ∑ i, grad i = 0

inductive JetTree (ι E : Type*) [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  | leaf : E → JetTree ι E
  | branch : RowJet ι E → E → ℝ → (ι → JetTree ι E) → JetTree ι E

def mean : JetTree ι E → E
  | .leaf v => v
  | .branch row _ _ t => ∑ i, row.law i • mean (t i)

def flux : JetTree ι E → ℝ
  | .leaf _ => 0
  | .branch row _ _ t => ∑ i, ⟪row.grad i,mean (t i)⟫ + ∑ i, row.law i*flux (t i)

/-- Product-rule expansion over all terminal label histories. The carried mass
and its derivative are updated by the exact Leibniz rule. -/
def pathFlux : JetTree ι E → ℝ → E → ℝ
  | .leaf v, _, G => ⟪G,v⟫
  | .branch row _ _ t, q, G =>
      ∑ i, pathFlux (t i) (q*row.law i) (q • row.grad i+row.law i • G)

def TerminalBound : JetTree ι E → E → ℝ → Prop
  | .leaf v, c, B => ‖v-c‖ ≤ B
  | .branch _ _ _ t, c, B => ∀ i, TerminalBound (t i) c B

def Controlled : JetTree ι E → Prop
  | .leaf _ => True
  | .branch _ c B t => (∀ i, TerminalBound (t i) c B) ∧ ∀ i, Controlled (t i)

def cost : JetTree ι E → ℝ
  | .leaf _ => 0
  | .branch row _ B t => (∑ i, ‖row.grad i‖)*B+∑ i, row.law i*cost (t i)

end SignedAssembly

open scoped ContDiff

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_LabelSwitches1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff

noncomputable section

namespace SignedDisk

open Finset

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace RadiusEnvelope
variable {E : Type*}

/-- The signed envelope over the entire compact real-radius interval. -/
def envelope (u : ℝ → E → ℝ) (a b : ℝ) (x : E) : ℝ :=
  sSup ((fun r => u r x) '' Icc a b)

end RadiusEnvelope

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DyadicHats1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

noncomputable section

namespace SignedDisk

namespace DyadicHats

def point (r : ℝ) (p : ℤ × ℤ) : ℂ := ⟨r*p.1,r*p.2⟩
def boxNorm (x : ℂ) : ℝ := max |x.re| |x.im|

lemma norm_le_two_boxNorm (x : ℂ) : ‖x‖ ≤ 2*boxNorm x := by
  have h := Complex.norm_le_abs_re_add_abs_im x
  have hr : |x.re| ≤ boxNorm x := le_max_left _ _
  have hi : |x.im| ≤ boxNorm x := le_max_right _ _
  linarith

lemma hat_pos_iff {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) (x : ℂ) :
    0 < hat r p x ↔ boxNorm (x-point r p) < r := by
  have hp : 0 < hat r p x ↔ 0 < tent (x.re/r-p.1) ∧ 0 < tent (x.im/r-p.2) := by
    constructor
    · intro h
      exact ⟨pos_of_mul_pos_left h (tent_nonneg _),pos_of_mul_pos_right h (tent_nonneg _)⟩
    · intro h
      exact mul_pos h.1 h.2
  rw [hp,tent_pos_iff,tent_pos_iff]
  have hr0 : r ≠ 0 := ne_of_gt hr
  have h1 : x.re/r-p.1 = (x.re-r*p.1)/r := by field_simp
  have h2 : x.im/r-p.2 = (x.im-r*p.2)/r := by field_simp
  rw [h1,h2,abs_div,abs_div,abs_of_pos hr,div_lt_one hr,div_lt_one hr]
  simp only [boxNorm,Complex.sub_re,Complex.sub_im,point,max_lt_iff]

lemma hat_ne_zero_iff {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) (x : ℂ) :
    hat r p x ≠ 0 ↔ boxNorm (x-point r p) < r := by
  constructor
  · intro h
    exact (hat_pos_iff hr p x).mp (lt_of_le_of_ne (hat_nonneg r p x) (Ne.symm h))
  · intro h
    exact ne_of_gt ((hat_pos_iff hr p x).mpr h)

lemma support_hat_subset {r : ℝ} (hr : 0 < r) (p : ℤ × ℤ) :
    Function.support (hat r p) ⊆ Metric.closedBall (point r p) (2*r) := by
  intro x hx
  rw [Metric.mem_closedBall,dist_eq_norm]
  exact (norm_le_two_boxNorm _).trans (mul_le_mul_of_nonneg_left ((hat_ne_zero_iff hr p x).mp hx).le (by norm_num))

open scoped BigOperators

/-- Literal nine-child support of an adjacent dyadic refinement row. -/
def children (p : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (2*p.1-1) (2*p.1+1)).product (Finset.Icc (2*p.2-1) (2*p.2+1))

lemma tent_half_zero {j k : ℤ} (h : j ∉ Finset.Icc (2*k-1) (2*k+1)) :
    tent ((j:ℝ)/2-k) = 0 := by
  have ht : j-2*k ∉ Finset.Icc (-1) 1 := by
    simp only [Finset.mem_Icc] at *
    omega
  convert tent_half_integer ht using 1
  push_cast
  congr 1
  ring

lemma step_zero_of_not_child {p q : ℤ × ℤ} (hq : q ∉ children p) : step p q = 0 := by
  have hq' : ¬(q.1 ∈ Finset.Icc (2*p.1-1) (2*p.1+1) ∧ q.2 ∈ Finset.Icc (2*p.2-1) (2*p.2+1)) := by
    exact fun hn => hq (Finset.mem_product.mpr hn)
  rw [not_and_or] at hq'
  rcases hq' with hq | hq
  · rw [step,tent_half_zero hq,zero_mul]
  · rw [step,tent_half_zero hq,mul_zero]

lemma hat_refine_finite (r : ℝ) (p : ℤ × ℤ) (x : ℂ) :
    hat (2*r) p x = ∑ q ∈ children p, step p q*hat r q x := by
  rw [hat_refine,tsum_eq_sum (s := children p)]
  intro q hq
  rw [step_zero_of_not_child hq,zero_mul]

/-- The vector mass of the actual density, not an abstract additive tree. -/
def vectorMass (h : ℂ → ℂ) (r : ℝ) (p : ℤ × ℤ) : ℂ := ∫ y, hat r p y • h y

def scalarMass (h : ℂ → ℂ) (r : ℝ) (p : ℤ × ℤ) : ℝ := ‖vectorMass h r p‖

lemma integrable_hat_smul {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ) (p : ℤ × ℤ) :
    Integrable (fun y => hat r p y • h y) := by
  apply hh.bdd_smul 1 (continuous_hat r p).aestronglyMeasurable
  filter_upwards with y
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hat_nonneg r p y)] using hat_le_one r p y

/-- A finite index set that contains every hat meeting a fixed bounded region. -/
def boundedIndices (r R : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-⌈R/r+1⌉) ⌈R/r+1⌉).product (Finset.Icc (-⌈R/r+1⌉) ⌈R/r+1⌉)

lemma mem_boundedIndices {r R : ℝ} (hr : 0 < r) {x : ℂ} (hx : ‖x‖ ≤ R)
    {p : ℤ × ℤ} (hp : hat r p x ≠ 0) : p ∈ boundedIndices r R := by
  have hpos : 0 < hat r p x := lt_of_le_of_ne (hat_nonneg r p x) (Ne.symm hp)
  have h1 := (tent_pos_iff _).mp (pos_of_mul_pos_left hpos (tent_nonneg _))
  have h2 := (tent_pos_iff _).mp (pos_of_mul_pos_right hpos (tent_nonneg _))
  have hbound (a : ℝ) (j : ℤ) (ha : |a| ≤ R) (hj : |a/r-j| < 1) :
      j ∈ Finset.Icc (-⌈R/r+1⌉) ⌈R/r+1⌉ := by
    have hq : |a/r| ≤ R/r := by rw [abs_div,abs_of_pos hr]; exact div_le_div_of_nonneg_right ha hr.le
    have hja : |(j:ℝ)| ≤ R/r+1 := by
      calc
        _ = |a/r-(a/r-j)| := by congr 1; ring
        _ ≤ |a/r|+|a/r-j| := abs_sub _ _
        _ ≤ R/r+1 := add_le_add hq hj.le
    have hlo := (abs_le.mp hja).1
    have hhi := (abs_le.mp hja).2
    have hc := Int.le_ceil (R/r+1)
    simp only [Finset.mem_Icc]
    constructor
    · have : (-(⌈R/r+1⌉:ℝ)) ≤ j := by linarith
      exact_mod_cast this
    · have : (j:ℝ) ≤ ⌈R/r+1⌉ := hhi.trans hc
      exact_mod_cast this
  exact Finset.mem_product.mpr ⟨hbound x.re p.1 ((Complex.abs_re_le_norm x).trans hx) h1,
    hbound x.im p.2 ((Complex.abs_im_le_norm x).trans hx) h2⟩

end DyadicHats

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff

open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace DyadicHats

def indexBox (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(N:ℤ)) N).product (Finset.Icc (-(N:ℤ)) N)
abbrev Grid (N : ℕ) := {p : ℤ × ℤ // p ∈ indexBox N}

lemma mem_indexBox_of_le {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {x : ℂ} (hx : ‖x‖ ≤ R) {p : ℤ × ℤ} (hp : hat r p x ≠ 0) :
    p ∈ indexBox N := by
  have hm := mem_boundedIndices hr hx hp
  have hc : ⌈R/r+1⌉ ≤ (N:ℤ) := Int.ceil_le.mpr (by simpa only [Int.cast_natCast] using hN)
  have h1 := Finset.mem_Icc.mp (Finset.mem_product.mp hm).1
  have h2 := Finset.mem_Icc.mp (Finset.mem_product.mp hm).2
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega

lemma hat_mul_zero_outside {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    {p : ℤ × ℤ} (hp : p ∉ indexBox N) (x : ℂ) : hat r p x*h x = 0 := by
  by_cases hx : h x = 0
  · rw [hx,mul_zero]
  · have ht : hat r p x = 0 := by
      by_contra hn
      exact hp (mem_indexBox_of_le hr hN (hs x hx) hn)
    rw [ht,zero_mul]

lemma density_refine_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (p : Grid N) (x : ℂ) :
    hat (2*r) p x*h x = ∑ q : Grid N, step p q*(hat r q x*h x) := by
  rw [hat_refine,← tsum_mul_right,tsum_eq_sum (s := indexBox N)]
  · rw [Finset.sum_coe_sort (indexBox N) (fun q => step p q*(hat r q x*h x))]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  · intro q hq
    rw [mul_assoc,hat_mul_zero_outside hr hN hs hq x,mul_zero]

lemma integrable_hat_mul {h : ℂ → ℝ} (hh : Integrable h) (r : ℝ) (p : ℤ × ℤ) :
    Integrable (fun y => hat r p y*h y) := by
  exact hh.bdd_smul 1 (continuous_hat r p).aestronglyMeasurable
    (ae_of_all _ (fun y => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hat_nonneg r p y)] using hat_le_one r p y))

def scale (r : ℝ) (k : ℕ) : ℝ := (2:ℝ)^k*r
lemma scale_pos {r : ℝ} (hr : 0 < r) (k : ℕ) : 0 < scale r k := by unfold scale; positivity
lemma scale_succ (r : ℝ) (k : ℕ) : scale r (k+1) = 2*scale r k := by
  unfold scale
  rw [pow_succ]
  ring
lemma le_scale {r : ℝ} (hr : 0 ≤ r) (k : ℕ) : r ≤ scale r k := by
  have hp : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  simpa only [one_mul,scale] using mul_le_mul_of_nonneg_right hp hr

lemma scale_index_bound {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) (k : ℕ) : R/scale r k+1 ≤ (N:ℝ) := by
  have hd : R / scale r k ≤ R / r := div_le_div_of_nonneg_left hR hr (le_scale hr.le k)
  linarith

end DyadicHats

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DyadicHats2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DyadicHats

section
open scoped BigOperators

lemma step_support {r : ℝ} (_hr : 0 < r) {p q : ℤ × ℤ} (hw : step p q ≠ 0) :
    Function.support (hat r q) ⊆ Function.support (hat (2*r) p) := by
  have hq : q ∈ children p := by
    by_contra hn
    exact hw (step_zero_of_not_child hn)
  intro x hx
  have hpos : 0 < step p q*hat r q x := mul_pos
    (lt_of_le_of_ne (step_nonneg p q) (Ne.symm hw))
    (lt_of_le_of_ne (hat_nonneg r q x) (Ne.symm hx))
  have hle : step p q*hat r q x ≤ hat (2*r) p x := by
    rw [hat_refine_finite]
    exact Finset.single_le_sum (fun s _ => mul_nonneg (step_nonneg p s) (hat_nonneg r s x)) hq
  exact ne_of_gt (hpos.trans_le hle)

variable {N : ℕ}
def weights (N : ℕ) : ℕ → Grid N → Grid N → ℝ := fun _ p q => step p q
def pieces (N : ℕ) (r : ℝ) (h : ℂ → ℝ) : Grid N → ℂ → ℝ := fun q x => hat r q x*h x

def densityRoot (N : ℕ) (r : ℝ) (h : ℂ → ℝ) :=
  ScalarCancellation.roots volume (weights N) (pieces N r h)
def densityError (N : ℕ) (r : ℝ) (h : ℂ → ℝ) :=
  ScalarCancellation.errors volume (weights N) (pieces N r h)

lemma pieces_integrable {h : ℂ → ℝ} (hh : Integrable h) (r : ℝ) (q : Grid N) :
    Integrable (pieces N r h q) := integrable_hat_mul hh r q

lemma refined_eq_density {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (q : Grid N) (x : ℂ) :
    ScalarCancellation.refined (weights N) (pieces N r h) k q x = hat (scale r k) q x*h x := by
  induction k generalizing q with
  | zero => simp only [ScalarCancellation.refined,pieces,scale,pow_zero,one_mul]
  | succ k ih =>
    simp only [ScalarCancellation.refined,weights,ih,scale_succ]
    exact (density_refine_grid (scale_pos hr k) (scale_index_bound hr hR hN k) hs q x).symm

lemma densityRoot_integrable {h : ℂ → ℝ} (hh : Integrable h) (r : ℝ) (k : ℕ) (q : Grid N) :
    Integrable (densityRoot N r h k q) :=
  ScalarCancellation.roots_integrable _ (pieces_integrable hh r) k q
lemma densityError_integrable {h : ℂ → ℝ} (hh : Integrable h) (r : ℝ) (k : ℕ) (q : Grid N) :
    Integrable (densityError N r h k q) :=
  ScalarCancellation.errors_integrable _ (pieces_integrable hh r) k q
lemma densityError_zero_mass {h : ℂ → ℝ} (hh : Integrable h) (r : ℝ) (k : ℕ) (q : Grid N) :
    (∫ x, densityError N r h k q x) = 0 :=
  ScalarCancellation.errors_zero_mass _ (pieces_integrable hh r) k q

lemma density_support {r : ℝ} (hr : 0 < r) {h : ℂ → ℝ} (hh : Integrable h)
    (k : ℕ) (q : Grid N) (x : ℂ) (hx : hat (scale r k) q x = 0) :
    densityRoot N r h k q x = 0 ∧ densityError N r h k q x = 0 := by
  apply ScalarCancellation.roots_errors_support (weights N) (pieces_integrable hh r)
    (fun k q => Function.support (hat (scale r k) q)) ?_ ?_ k q x (by simpa using hx)
  · intro q y hy
    have hz : hat r q y = 0 := by simpa [scale] using hy
    simp only [pieces,hz,zero_mul]
  · intro k p q hw
    rw [scale_succ]
    exact step_support (scale_pos hr k) hw

def densityDefect (N : ℕ) (r : ℝ) (h : ℂ → ℝ) : ℕ → Grid N → ℝ
  | 0,q => ((∫ x, hat r q x*|h x|)-|∫ x, hat r q x*h x|)/2
  | k+1,q => ((∑ s : Grid N, step q s*|∫ x, hat (scale r k) s x*h x|)-
      |∫ x, hat (scale r (k+1)) q x*h x|)/2

end

open Finset

/-- Coherent refinement coefficients, evaluated by exact positive matrix
composition on the finite box. These are not row-stochastic transitions. -/
def coeff (N : ℕ) : ℕ → Grid N → Grid N → ℝ
  | 0,p,q => if p=q then 1 else 0
  | d+1,p,q => ∑ a : Grid N, step p a*coeff N d a q

/-- The common scalar price assigned to a root. The geometric discount is
applied at the actual birth scale of each zero-mass error. -/
def scalarPrice (N : ℕ) (r : ℝ) (h : ℂ → ℝ) (ρ : ℝ) (k : ℕ) (q : Grid N) : ℝ :=
  ∑ j ∈ range (k+1), ρ^(k-j)*∑ s : Grid N, coeff N (k-j) q s*densityDefect N r h j s

open Finset

open Finset

def activeIndices (r : ℝ) (x : ℂ) : Finset (ℤ × ℤ) :=
  ({⌊x.re/r⌋,⌊x.re/r⌋+1} : Finset ℤ).product {⌊x.im/r⌋,⌊x.im/r⌋+1}

lemma hat_zero_of_not_active (r : ℝ) (x : ℂ) {p : ℤ × ℤ} (hp : p ∉ activeIndices r x) :
    hat r p x = 0 := by
  have hp' : ¬(p.1 ∈ ({⌊x.re/r⌋,⌊x.re/r⌋+1} : Finset ℤ) ∧
      p.2 ∈ ({⌊x.im/r⌋,⌊x.im/r⌋+1} : Finset ℤ)) := fun hn => hp (mem_product.mpr hn)
  rw [not_and_or] at hp'
  rcases hp' with h|h
  · simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at h
    rw [hat,tent_eq_zero_of_ne_floor h.1 h.2,zero_mul]
  · simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at h
    rw [hat,tent_eq_zero_of_ne_floor h.1 h.2,mul_zero]

lemma summable_weighted_hat (r : ℝ) (x : ℂ) (f : ℤ × ℤ → ℝ) :
    Summable (fun p => hat r p x*f p) := by
  apply summable_of_ne_finset_zero (s := activeIndices r x)
  intro p hp
  rw [hat_zero_of_not_active r x hp,zero_mul]

/-- The literal locally finite tent interpolation, indexed by the whole grid. -/
def interpolate (r : ℝ) (f : ℤ × ℤ → ℝ) (x : ℂ) : ℝ := ∑' p, hat r p x*f p

lemma interpolate_sub (r : ℝ) (f g : ℤ × ℤ → ℝ) (x : ℂ) :
    interpolate r (fun p => f p-g p) x = interpolate r f x-interpolate r g x := by
  simp only [interpolate,mul_sub]
  exact (summable_weighted_hat r x f).tsum_sub (summable_weighted_hat r x g)
lemma interpolate_mul_const (r : ℝ) (f : ℤ × ℤ → ℝ) (x : ℂ) (c : ℝ) :
    interpolate r (fun p => f p*c) x = interpolate r f x*c := by
  simp only [interpolate,← mul_assoc,tsum_mul_right]
lemma interpolate_const (r : ℝ) (x : ℂ) (c : ℝ) : interpolate r (fun _ => c) x = c := by
  rw [interpolate,tsum_mul_right,tsum_hat,one_mul]
lemma interpolate_nonneg (r : ℝ) (x : ℂ) {f : ℤ × ℤ → ℝ} (hf : ∀ p, 0 ≤ f p) :
    0 ≤ interpolate r f x := tsum_nonneg fun p => mul_nonneg (hat_nonneg r p x) (hf p)
lemma interpolate_mono (r : ℝ) (x : ℂ) {f g : ℤ × ℤ → ℝ} (h : ∀ p, f p ≤ g p) :
    interpolate r f x ≤ interpolate r g x := by
  exact Summable.tsum_le_tsum (fun p => mul_le_mul_of_nonneg_left (h p) (hat_nonneg r p x))
    (summable_weighted_hat r x f) (summable_weighted_hat r x g)
lemma interpolate_le_const (r : ℝ) (x : ℂ) {f : ℤ × ℤ → ℝ} {c : ℝ} (hf : ∀ p, f p ≤ c) :
    interpolate r f x ≤ c := (interpolate_mono r x hf).trans_eq (interpolate_const r x c)

lemma interpolate_finset_sum {ι : Type*} (s : Finset ι) (r : ℝ)
    (f : ι → ℤ × ℤ → ℝ) (x : ℂ) :
    interpolate r (fun p => ∑ i ∈ s, f i p) x = ∑ i ∈ s, interpolate r (f i) x := by
  simp only [interpolate,mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => summable_weighted_hat r x (f i))

end DyadicHats

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_FiniteLabels1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace FiniteLabels
open DyadicHats
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual locally finite transition row on the entire spatial grid. -/
def spatialRow (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ) : Law ι where
  mass j := delta old j+interpolate r (fun z => p z*(delta (target z) j-delta old j)) x
  nonneg j := by
    simp only [mul_sub,interpolate_sub,interpolate_mul_const]
    have h0 := interpolate_nonneg r x hp0
    have h1 := interpolate_le_const r x hp1
    have h2 := interpolate_nonneg r x (fun z => mul_nonneg (hp0 z) ((delta (target z)).nonneg j))
    have hd := (delta old).nonneg j
    nlinarith
  total := by
    rw [sum_add_distrib,(delta old).total,← interpolate_finset_sum]
    have he : (fun z => ∑ j : ι, p z*(delta (target z) j-delta old j)) = fun _ => 0 := by
      funext z
      rw [← mul_sum,sum_sub_distrib,(delta _).total,(delta _).total,sub_self,mul_zero]
    rw [he,interpolate_const,add_zero]

lemma spatialRow_formula (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ) (j : ι) :
    spatialRow old target p hp0 hp1 r x j =
      delta old j+interpolate r (fun z => p z*(delta (target z) j-delta old j)) x := rfl

end FiniteLabels

namespace DyadicHats
open Finset Filter

def truncate (r : ℝ) (q : ℂ) (p : ℤ × ℤ → ℝ) (z : ℤ × ℤ) : ℝ :=
  if boxNorm (point r z-q) ≤ 200*r then p z else 0

lemma truncate_nonneg (r : ℝ) (q : ℂ) {p : ℤ × ℤ → ℝ} (hp : ∀ z, 0 ≤ p z) (z : ℤ × ℤ) :
    0 ≤ truncate r q p z := by unfold truncate; split_ifs <;> simp [hp]
lemma truncate_le {r B : ℝ} {q : ℂ} {p : ℤ × ℤ → ℝ} (hB : 0 ≤ B)
    (hp : ∀ z, boxNorm (point r z-q) ≤ 200*r → p z ≤ B) (z : ℤ × ℤ) :
    truncate r q p z ≤ B := by unfold truncate; split_ifs with h; exact hp z h; exact hB

end DyadicHats

namespace FiniteLabels

def probability (τ d : ℝ) : ℝ := min 1 ((τ⁻¹*max (d-τ) 0)^2)
def amplitude (τ d : ℝ) : ℝ := min 1 (τ⁻¹*max (d-τ) 0)

lemma probability_nonneg (τ d : ℝ) : 0 ≤ probability τ d := le_min (by norm_num) (sq_nonneg _)
lemma probability_le_one (τ d : ℝ) : probability τ d ≤ 1 := min_le_left _ _

open DyadicHats

def switchRate (τ r : ℝ) (Θ : ℤ × ℤ → ℂ) (n x : ℂ) : ℝ :=
  interpolate r (fun z => probability τ ‖n-Θ z‖) x

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def spatialSwitchRow (τ r : ℝ) (label : ι → ℂ) (Θ : ℤ × ℤ → ℂ)
    (target : ℤ × ℤ → ι) (old : ι) (x : ℂ) : Law ι :=
  spatialRow old target (fun z => probability τ ‖label old-Θ z‖)
    (fun _ => probability_nonneg _ _) (fun _ => probability_le_one _ _) r x

end FiniteLabels

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DyadicHats3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DyadicHats

open Finset

def nearParent (q : ℤ × ℤ) : ℤ × ℤ := ((q.1+2048)/4096,(q.2+2048)/4096)

lemma nearParent_mem {N : ℕ} {q : ℤ × ℤ} (hq : q ∈ indexBox N) : nearParent q ∈ indexBox N := by
  have h1 := Finset.mem_Icc.mp (Finset.mem_product.mp hq).1
  have h2 := Finset.mem_Icc.mp (Finset.mem_product.mp hq).2
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_Icc.mpr <;> dsimp only [nearParent] <;> constructor <;> omega

end DyadicHats

namespace DirectionNeighbors
open DyadicHats Finset

/-- The complete fixed grid window. No spatial observation enters the choices. -/
def window (d : ℕ) (q : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (q.1-d) (q.1+d)).product (Finset.Icc (q.2-d) (q.2+d))

lemma self_mem_window (d : ℕ) (q : ℤ × ℤ) : q ∈ window d q := by
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,
    Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩

lemma max_exists (f : ℤ × ℤ → ℝ) (d : ℕ) (q : ℤ × ℤ) :
    ∃ z ∈ window d q, ∀ z' ∈ window d q, f z' ≤ f z :=
  Finset.exists_max_image (window d q) f ⟨q,self_mem_window d q⟩

def maxVertex (f : ℤ × ℤ → ℝ) (d : ℕ) (q : ℤ × ℤ) : ℤ × ℤ :=
  Classical.choose (max_exists f d q)

def chosen (h : ℂ → ℂ) (r : ℝ) : ℤ × ℤ → ℤ × ℤ := maxVertex (scalarMass h r) 300

def theta (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : ℂ :=
  IntrinsicMarks.direction 1 (vectorMass h r q)
def Theta (h : ℂ → ℂ) (r : ℝ) (z : ℤ × ℤ) : ℂ := theta h r (chosen h r z)

def worstVertex (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : ℤ × ℤ :=
  maxVertex (fun z => ‖Theta h r z-theta h r q‖^2) 200 q

def energy (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : ℝ :=
  ‖Theta h r (worstVertex h r q)-theta h r q‖^2

lemma norm_theta (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : ‖theta h r q‖ = 1 :=
  IntrinsicMarks.norm_direction (by norm_num) _

open DyadicHats

/-- The literal triangle defect over twelve positive refinements. -/
def coarseDefect (N : ℕ) (h : ℂ → ℂ) (r : ℝ) (d : ℕ) (p : Grid N) : ℝ :=
  (∑ q : Grid N, coeff N d p q*scalarMass h r q)-scalarMass h (scale r d) p

def parent (N : ℕ) (q : Grid N) : Grid N := ⟨nearParent q,nearParent_mem q.property⟩

end DirectionNeighbors

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DirectionNeighbors1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

/-! Actual fixed palette and literal cone coordinates. -/

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace ConeCoordinates

def axis (n : ℂ) (s : ℝ) : ℂ := (Real.sqrt 3/2) • n + (s/2) • (Complex.I*n)
def coordinate (n : ℂ) (s : ℝ) : ℂ →L[ℝ] ℝ :=
  (1 / Real.sqrt 3) • innerSL ℝ n + s • innerSL ℝ (Complex.I*n)

lemma sqrt3_sq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
lemma inner_im (n z : ℂ) : inner ℝ (Complex.I*n) z = (star n*z).im := by
  simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.mul_re, Complex.mul_im]
  ring
lemma mul_star_of_unit {n : ℂ} (hn : ‖n‖ = 1) : n * star n = 1 := by
  simpa [Complex.normSq_eq_norm_sq, hn] using Complex.mul_conj n
lemma axis_norm {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    ‖axis n s‖ = 1 := by
  have he : axis n s = (↑(Real.sqrt 3/2)+(↑s/2)*Complex.I)*n := by
    apply Complex.ext <;> simp [axis,Complex.mul_re,Complex.mul_im]; ring
  rw [he,norm_mul,hn,mul_one]
  have hsq := sqrt3_sq
  have h : Complex.normSq (↑(Real.sqrt 3/2)+(↑s/2)*Complex.I) = 1 := by
    simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    nlinarith
  have hn0 := norm_nonneg (↑(Real.sqrt 3/2)+(↑s/2)*Complex.I : ℂ)
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith
lemma inner_axis (n z : ℂ) (s : ℝ) :
    inner ℝ (axis n s) z = Real.sqrt 3/2 * inner ℝ n z + s/2*inner ℝ (Complex.I*n) z := by
  simp only [axis,inner_add_left,real_inner_smul_left]

/-- Closed sector between the literal two palette axes. -/
def Good (n z : ℂ) : Prop := 0 ≤ coordinate n 1 z ∧ 0 ≤ coordinate n (-1) z

lemma inner_quarter_self {n : ℂ} (hn : ‖n‖ = 1) : inner ℝ (Complex.I*n) n = 0 := by
  rw [inner_im,show star n*n = 1 by simpa [mul_comm] using mul_star_of_unit hn]
  simp
lemma axes_inner {n : ℂ} (hn : ‖n‖ = 1) : inner ℝ (axis n 1) (axis n (-1)) = 1/2 := by
  rw [inner_axis]
  simp only [axis,inner_add_right,real_inner_smul_right]
  have hnn : inner ℝ n n = 1 := by simp [hn]
  have hnp : inner ℝ n (Complex.I*n) = 0 := by rw [real_inner_comm]; exact inner_quarter_self hn
  have hpn := inner_quarter_self hn
  have hpp : inner ℝ (Complex.I*n) (Complex.I*n) = 1 := by simp [hn]
  rw [hnn,hnp,hpn,hpp]
  nlinarith [sqrt3_sq]

/-- A finite fixed palette, all members genuinely on the unit circle. -/
structure Palette where
  labels : Finset ℂ
  unit : ∀ n ∈ labels, ‖n‖ = 1
  cover : ∀ z : ℂ, ‖z‖ = 1 → ∃ n ∈ labels, ‖z-n‖ < 1/2000

lemma exists_palette : Nonempty Palette := by
  classical
  let S := Metric.sphere (0 : ℂ) 1
  have hc : IsCompact S := isCompact_sphere 0 1
  obtain ⟨t,hts,htfin,ht⟩ := hc.elim_finite_subcover_image (fun n (_ : n ∈ S) => Metric.isOpen_ball (x := n) (ε := (1/2000:ℝ))) (by
      intro z hz
      exact Set.mem_iUnion₂.2 ⟨z,hz,by simp⟩)
  refine ⟨⟨htfin.toFinset,?_,?_⟩⟩
  · intro n hn
    simpa [S,Metric.mem_sphere,dist_zero_right] using hts (htfin.mem_toFinset.mp hn)
  · intro z hz
    have hzS : z ∈ S := by simpa [S,Metric.mem_sphere,dist_zero_right] using hz
    obtain ⟨n,hn,hzn⟩ := Set.mem_iUnion₂.mp (ht hzS)
    exact ⟨n,htfin.mem_toFinset.mpr hn,by simpa [Metric.mem_ball,dist_eq_norm] using hzn⟩

def fixedPalette : Palette := Classical.choice exists_palette

def quantize (z : ℂ) (hz : ‖z‖ = 1) : {n : ℂ // n ∈ fixedPalette.labels} :=
  ⟨Classical.choose (fixedPalette.cover z hz), (Classical.choose_spec (fixedPalette.cover z hz)).1⟩

end ConeCoordinates

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks Finset

def tree {N : ℕ} (v : Grid N → ℂ) : ℕ → ℝ → Grid N → Tree (Grid N) ℂ
  | 0,b,p => .leaf (b • v p)
  | k+1,b,p => .branch (fun q => tree v k (b*step p q) q)

end ActualMarkTrees

namespace ScalarCancellation
variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]
lemma roots_nonneg_of_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι)
    (hm : 0 ≤ ∫ x, refined w f k q x ∂μ) : ∀ x, 0 ≤ roots μ w f k q x := by
  cases k with
  | zero => exact (root_spec (hf q)).2.2.2.2.1 hm
  | succ k =>
    have hi := integrable_finsetSum Finset.univ
      (fun s _ => (roots_integrable w hf k s).const_mul (w k q s))
    have hs := root_spec hi
    have he := roots_mass w hf (k+1) q
    change (∫ x, root μ _ x ∂μ) = _ at he
    rw [hs.2.1] at he
    exact hs.2.2.2.2.1 (by rw [he]; exact hm)
end ScalarCancellation

namespace ConeScalar
open ConeCoordinates DyadicHats IntrinsicMarks

lemma scalar_integrable {h : ℂ → ℂ} (hh : Integrable h) (c : ℂ →L[ℝ] ℝ) :
    Integrable (fun x => c (h x)) := c.integrable_comp hh
lemma scalar_support {h : ℂ → ℂ} {R : ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (c : ℂ →L[ℝ] ℝ) : ∀ y, c (h y) ≠ 0 → ‖y‖ ≤ R := by
  intro y hy
  exact hs y (fun h => hy (by simp [h]))
lemma scalar_mass {h : ℂ → ℂ} (hh : Integrable h) (c : ℂ →L[ℝ] ℝ) (r : ℝ) (q : ℤ × ℤ) :
    (∫ y, hat r q y*c (h y)) = c (vectorMass h r q) := by
  have he := c.integral_comp_comm (integrable_hat_smul hh r q)
  simpa only [map_smul,smul_eq_mul,vectorMass] using he

lemma coordinate_mass_nonneg {n v : ℂ}
    (hg : Good n (direction 1 v)) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    0 ≤ coordinate n s v := by
  have he := congrArg (coordinate n s) (mass_direction (1:ℂ) v)
  rw [map_smul,smul_eq_mul] at he
  rw [← he]
  exact mul_nonneg (norm_nonneg _) (hs.elim (fun h => h ▸ hg.1) (fun h => h ▸ hg.2))

lemma good_root_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) {n : ℂ}
    (hg : Good n (direction 1 (vectorMass h (scale r k) q))) {s : ℝ}
    (hs : s = 1 ∨ s = -1) (y : ℂ) :
      0 ≤ densityRoot N r (fun x => coordinate n s (h x)) k q y := by
  apply ScalarCancellation.roots_nonneg_of_mass (weights N)
    (pieces_integrable (scalar_integrable hh _) r) k q _ y
  simp_rw [refined_eq_density hr hR hN (scalar_support hsupp _),scalar_mass hh]
  exact coordinate_mass_nonneg hg hs

lemma root_vector_integrable {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h)
    (r : ℝ) (k : ℕ) (q : Grid N) (n : ℂ) (s : ℝ) :
    Integrable (fun y => densityRoot N r (fun x => coordinate n s (h x)) k q y • axis n s) :=
  (densityRoot_integrable (scalar_integrable hh _) r k q).smul_const _

lemma pair_cone {n : ℂ} (hn : ‖n‖ = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {s : ℝ} (hs : s = 1 ∨ s = -1) :
    (1/2:ℝ)*‖a • axis n 1+b • axis n (-1)‖ ≤ inner ℝ (axis n s)
      (a • axis n 1+b • axis n (-1)) := by
  have hnorm : ‖a • axis n 1+b • axis n (-1)‖ ≤ a+b := by
    convert norm_add_le (a • axis n 1) (b • axis n (-1)) using 1
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,
      axis_norm hn (by norm_num : (1:ℝ)^2=1),axis_norm hn (by norm_num : (-1:ℝ)^2=1),mul_one]
  have hp : inner ℝ (axis n 1) (axis n 1) = 1 := by simp [axis_norm hn (by norm_num : (1:ℝ)^2=1)]
  have hm : inner ℝ (axis n (-1)) (axis n (-1)) = 1 := by simp [axis_norm hn (by norm_num : (-1:ℝ)^2=1)]
  have hpm := axes_inner hn
  have hmp : inner ℝ (axis n (-1)) (axis n 1) = 1/2 := by rw [real_inner_comm]; exact hpm
  rcases hs with rfl | rfl <;> simp only [inner_add_right,real_inner_smul_right,hp,hm,hpm,hmp] <;> linarith

end ConeScalar

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_AffineDensities1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace AffineDensities

def rescale (p : ℂ) (r : ℝ) (h : ℂ → ℂ) (X : ℂ) : ℂ := r • h (p+r • X)

lemma integrable_rescale {h : ℂ → ℂ} (hh : Integrable h) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    Integrable (rescale p r h) := ((hh.comp_add_left p).comp_smul hr).smul r

lemma integral_affine (h : ℂ → ℂ) (p : ℂ) (r : ℝ) :
    (∫ X : ℂ, h (p+r • X)) = (r^2)⁻¹ • ∫ y, h y := by
  have he := Measure.integral_comp_smul volume (fun y : ℂ => h (p+y)) r
  simpa only [Complex.finrank_real_complex,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r)),
    integral_add_left_eq_self] using he

lemma integral_rescale (h : ℂ → ℂ) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫ X, rescale p r h X) = r⁻¹ • ∫ y, h y := by
  simp only [rescale,integral_smul,integral_affine,smul_smul]
  congr 1
  field_simp

lemma rescale_support {h : ℂ → ℂ} {p z : ℂ} {r t : ℝ} (hr : 0 < r)
    (hs : ∀ y, h y ≠ 0 → ‖y-z‖ ≤ t) (X : ℂ) (hX : rescale p r h X ≠ 0) :
    ‖X-r⁻¹ • (z-p)‖ ≤ t/r := by
  have hh : h (p+r • X) ≠ 0 := fun h => hX (by change r • _ = 0; rw [h,smul_zero])
  have hi := hs (p+r • X) hh
  have he : p+r • X-z = r • (X-r⁻¹ • (z-p)) := by
    rw [smul_sub,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.le] at hi
  exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hi)

end AffineDensities

namespace PricePieces
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities

lemma error_support {N : ℕ} {h : ℂ → ℝ} (hh : Integrable h) {r : ℝ} (hr : 0 < r)
    (j : ℕ) (q : Grid N) (y : ℂ) (hy : densityError N r h j q y ≠ 0) :
    ‖y-point (scale r j) q‖ ≤ 2*scale r j := by
  have hn : hat (scale r j) q y ≠ 0 := fun hn => hy ((density_support hr hh j q y hn).2)
  simpa only [Metric.mem_closedBall,dist_eq_norm] using support_hat_subset (scale_pos hr j) q hn

lemma scale_le {r : ℝ} (hr : 0 < r) {j k : ℕ} (hj : j ≤ k) : scale r j ≤ scale r k := by
  apply mul_le_mul_of_nonneg_right _ hr.le
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj

def errorPiece {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h) {r : ℝ} (hr : 0 < r)
    (k j : ℕ) (hj : j ≤ k) (p : ℂ) (q : Grid N) (n : ℂ) (s : ℝ) : ErrorPiece 2 where
  density := rescale p (scale r k)
    (fun y => densityError N r (fun x => coordinate n s (h x)) j q y • axis n s)
  integrable := integrable_rescale
    ((densityError_integrable (scalar_integrable hh _) r j q).smul_const _) p (scale_pos hr k).ne'
  size := scale r j / scale r k
  size_pos := div_pos (scale_pos hr j) (scale_pos hr k)
  size_le_one := (div_le_one (scale_pos hr k)).mpr (scale_le hr hj)
  center := (scale r k)⁻¹ • (point (scale r j) q-p)
  zero_mass := by
    intro _
    rw [integral_rescale _ _ (scale_pos hr k).ne',integral_smul_const,
      densityError_zero_mass (scalar_integrable hh _),zero_smul,smul_zero]
  support := by
    intro _
    apply ae_of_all
    intro X hX
    have hs : ∀ y, densityError N r (fun x => coordinate n s (h x)) j q y • axis n s ≠ 0 →
        ‖y-point (scale r j) q‖ ≤ 2*scale r j := by
      intro y hy
      apply error_support (scalar_integrable hh _) hr j q y
      exact fun h => hy (by rw [h,zero_smul])
    simpa only [mul_div_assoc] using rescale_support (scale_pos hr k) hs X hX

end PricePieces

namespace LocalCancellation

/-- Multiplication of an error density by a nonnegative path coefficient.
Zero coefficients are retained as genuine zero-density pieces. -/
def ErrorPiece.weight {Cs : ℝ} (b : ErrorPiece Cs) (w : ℝ) : ErrorPiece Cs where
  density := fun y => w • b.density y
  integrable := b.integrable.smul w
  size := b.size
  size_pos := b.size_pos
  size_le_one := b.size_le_one
  center := b.center
  zero_mass := by intro hs; rw [integral_smul,b.zero_mass hs,smul_zero]
  support := by
    intro hs
    filter_upwards [b.support hs] with y hy h
    exact hy (fun hz => h (by rw [hz,smul_zero]))

/-- An unrestricted integrable root term is a legitimate size-one piece. -/
def unitPiece (h : ℂ → ℂ) (hh : Integrable h) (Cs : ℝ) : ErrorPiece Cs where
  density := h
  integrable := hh
  size := 1
  size_pos := zero_lt_one
  size_le_one := le_rfl
  center := 0
  zero_mass := by intro hs; exact (lt_irrefl (1:ℝ) hs).elim
  support := by intro hs; exact (lt_irrefl (1:ℝ) hs).elim

lemma cone_sum {ι : Type*} {e : ℂ} {κ : ℝ} (hκ : 0 ≤ κ) (s : Finset ι) (v : ι → ℂ)
    (hv : ∀ i ∈ s, κ*‖v i‖ ≤ inner ℝ e (v i)) :
    κ*‖∑ i ∈ s, v i‖ ≤ inner ℝ e (∑ i ∈ s, v i) := by
  calc
    _ ≤ κ*∑ i ∈ s, ‖v i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hκ
    _ = ∑ i ∈ s, κ*‖v i‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ s, inner ℝ e (v i) := Finset.sum_le_sum hv
    _ = _ := (inner_sum _ _ _).symm

end LocalCancellation

namespace PricePieces
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities

/-- The vector root comprises the two actual signed scalar surviving roots. -/
def rootVector (N : ℕ) (r : ℝ) (h : ℂ → ℂ) (k : ℕ) (q : Grid N) (n : ℂ) (y : ℂ) : ℂ :=
  densityRoot N r (fun x => coordinate n 1 (h x)) k q y • axis n 1+
    densityRoot N r (fun x => coordinate n (-1) (h x)) k q y • axis n (-1)

def errorVector (N : ℕ) (r : ℝ) (h : ℂ → ℂ) (j : ℕ) (q : Grid N) (n : ℂ) (y : ℂ) : ℂ :=
  densityError N r (fun x => coordinate n 1 (h x)) j q y • axis n 1+
    densityError N r (fun x => coordinate n (-1) (h x)) j q y • axis n (-1)

lemma rootVector_integrable {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h)
    (r : ℝ) (k : ℕ) (q : Grid N) (n : ℂ) : Integrable (rootVector N r h k q n) :=
  (root_vector_integrable hh r k q n 1).add (root_vector_integrable hh r k q n (-1))

lemma rootVector_cone {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) {n : ℂ} (hn : ‖n‖ = 1)
    (hg : Good n (IntrinsicMarks.direction 1 (vectorMass h (scale r k) q)))
    {s : ℝ} (hs : s = 1 ∨ s = -1) (y : ℂ) :
    (1/2:ℝ)*‖rootVector N r h k q n y‖ ≤ inner ℝ (axis n s) (rootVector N r h k q n y) :=
  pair_cone hn (good_root_nonneg hr hR hN hh hsupp k q hg (Or.inl rfl) y)
    (good_root_nonneg hr hR hN hh hsupp k q hg (Or.inr rfl) y) hs

end PricePieces

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset

def rho : ℝ := (1/2:ℝ)^(1/100:ℝ)

/-- A common root price sums the two exact coordinate defects for every
member of one fixed finite palette; it does not depend on the active label. -/
def rootPrice (N : ℕ) (r : ℝ) (h : ℂ → ℂ) (k : ℕ) (q : Grid N) : ℝ :=
  ∑ n ∈ fixedPalette.labels,
    (scalarPrice N r (fun x => coordinate n 1 (h x)) rho k q+
      scalarPrice N r (fun x => coordinate n (-1) (h x)) rho k q)

end CommonPrices

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats

abbrev Label := {n : ℂ // n ∈ fixedPalette.labels}
instance instFintypeLabel : Fintype Label := Finset.fintypeCoeSort fixedPalette.labels
instance instDecidableEqLabel : DecidableEq Label := Classical.decEq _

def target (h : ℂ → ℂ) (r : ℝ) (z : ℤ × ℤ) : Label :=
  quantize (Theta h r z) (norm_theta h r (chosen h r z))

def switchChance (h : ℂ → ℂ) (r : ℝ) (n : Label) (z : ℤ × ℤ) : ℝ :=
  probability (1/100) ‖(n:ℂ)-Theta h r z‖
lemma switchChance_nonneg (h : ℂ → ℂ) (r : ℝ) (n : Label) (z : ℤ × ℤ) :
    0 ≤ switchChance h r n z := probability_nonneg _ _
lemma switchChance_le_one (h : ℂ → ℂ) (r : ℝ) (n : Label) (z : ℤ × ℤ) :
    switchChance h r n z ≤ 1 := probability_le_one _ _

def row (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) : Law Label :=
  spatialRow n (target h r) (switchChance h r n) (switchChance_nonneg h r n)
    (switchChance_le_one h r n) r x

def initial (h : ℂ → ℂ) (r : ℝ) (x : ℂ) : Law Label :=
  spatialRow (quantize 1 (by norm_num)) (target h r) (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_rfl) r x

/-- The actual finite-state label marginal, with its scale-dependent spatial
rows. This definition introduces no geometric or probabilistic hypothesis. -/
def marginal (h : ℂ → ℂ) (r : ℕ → ℝ) : ℕ → ℂ → Law Label
  | 0,x => initial h (r 0) x
  | k+1,x => move (marginal h r k x) (row h (r (k+1)) x)

end ActualLabels

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_FiniteLabels2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace FiniteLabels
open DyadicHats Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def expect (μ : Law ι) (f : ι → ℝ) : ℝ := ∑ i, μ i*f i

variable [DecidableEq ι]
lemma expect_delta (i : ι) (f : ι → ℝ) : expect (delta i) f = f i := by
  simp [expect,delta]

lemma spatialRow_expect (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ) (f : ι → ℝ) :
    expect (spatialRow old target p hp0 hp1 r x) f =
      f old+interpolate r (fun z => p z*(f (target z)-f old)) x := by
  simp only [expect,spatialRow_formula,add_mul,sum_add_distrib]
  rw [show (∑ i : ι, delta old i*f i) = f old from expect_delta old f]
  congr 1
  simp_rw [← interpolate_mul_const]
  rw [← interpolate_finset_sum]
  congr 1
  funext z
  simp only [mul_sub,sub_mul,sum_sub_distrib,mul_assoc,← mul_sum]
  rw [show (∑ i : ι, delta (target z) i*f i) = f (target z) from expect_delta _ _,
    show (∑ i : ι, delta old i*f i) = f old from expect_delta _ _]

end FiniteLabels

namespace ActualLabels
open FiniteLabels DyadicHats DirectionNeighbors ConeCoordinates

def badWeight (anchor : ℂ) (n : Label) : ℝ :=
  if ‖(n:ℂ)-anchor‖ ≤ (1/200:ℝ) then 0 else 1

def rate (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) : ℝ :=
  interpolate r (switchChance h r n) x

open FiniteLabels DyadicHats DirectionNeighbors Finset

def switchCost (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) : ℕ → ℝ
  | 0 => 1
  | k+1 => expect (marginal h r k x) (rate h (r (k+1)) x)

end ActualLabels

namespace IntrinsicMarks
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- Only paths ending in a nonzero terminal vector can carry particles. -/
def activePath : Tree ι E → List ι → Prop
  | .leaf v, [] => v ≠ 0
  | .leaf _, _::_ => False
  | .branch _, [] => False
  | .branch t, i::p => activePath (t i) p

/-- The subtree at a prefix (values beyond terminal nodes are immaterial). -/
def atPath : Tree ι E → List ι → Tree ι E
  | t, [] => t
  | .leaf v, _::_ => .leaf v
  | .branch t, i::p => atPath (t i) p

end IntrinsicMarks

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks

def lastVertex {N : ℕ} (q : Grid N) : List (Grid N) → Grid N
  | [] => q
  | s::p => lastVertex s p

def pathWeight {N : ℕ} (q : Grid N) : List (Grid N) → ℝ
  | [] => 1
  | s::p => step q s*pathWeight s p

end ActualMarkTrees

namespace IntrinsicMarks
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def reset (δ : ℝ) (v n : E) : E := if δ < ‖v-n‖ then v else n

def anchor (e : E) (δ : ℝ) : Tree ι E → E → List ι → E
  | .leaf v,n,_ => reset δ (direction e v) n
  | .branch t,n,[] => reset δ (direction e (∑ i,vector (t i))) n
  | .branch t,n,i::p => anchor e δ (t i) (reset δ (direction e (∑ j,vector (t j))) n) p

def rootAnchor (e : E) (δ : ℝ) (t : Tree ι E) : List ι → E :=
  anchor e δ t (direction e (vector t))

end IntrinsicMarks

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_ActualMarkTrees1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks

open DyadicHats IntrinsicMarks Finset DirectionNeighbors ActualLabels

def pathEnergy (h : ℂ → ℂ) (r : ℝ) (k : ℕ) {N : ℕ} (q : Grid N)
    (p : List (Grid N)) : ℝ := energy h (scale r (k-p.length)) (lastVertex q p)

def pathSwitches (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (x : ℂ)
    {N : ℕ} (p : List (Grid N)) (b : ℕ) : ℝ :=
  ∑ i ∈ Ico b (p.length+1), switchCost h (fun j => scale r (k-j)) x i

end ActualMarkTrees

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

def sign (b : Bool) : ℝ := if b then 1 else -1

def cellPrice (N : ℕ) (r : ℝ) (h : ℂ → ℂ) (k : ℕ) (S : Finset (Grid N)) : ℝ :=
  ∑ q ∈ S, rootPrice N r h k q

def rootWeight {N : ℕ} (S : Finset (Grid N)) (k j : ℕ) (s : Grid N) : ℝ :=
  ∑ q ∈ S, coeff N (k-j) q s

abbrev ErrorIndex (N k : ℕ) := Fin (k+1) × Grid N × Bool

def smallPiece {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) (i : ErrorIndex N k) : ErrorPiece 2 :=
  (errorPiece hh hr k i.1 (Nat.le_of_lt_succ i.1.isLt) p i.2.1 n (sign i.2.2)).weight
    (rootWeight S k i.1 i.2.1)

open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

def goodRoots {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) : Finset (Grid N) :=
  by classical exact S.filter (fun q => Good n (DirectionNeighbors.theta h (scale r k) q))
def badRoots {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) : Finset (Grid N) :=
  by classical exact S.filter (fun q => ¬Good n (DirectionNeighbors.theta h (scale r k) q))

def rootSum {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) (y : ℂ) : ℂ :=
  ∑ q ∈ S, rootVector N r h k q n y

lemma rootSum_integrable {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h)
    (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) : Integrable (rootSum h r k S n) :=
  integrable_finsetSum S (fun _ _ => rootVector_integrable hh r k _ n)

/-- The actual normalized positive-cone part on one cell. -/
def goodCone {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s = 1 ∨ s = -1) : ConeDensity (axis n s) (1/2) where
  density := rescale p (scale r k) (rootSum h r k (goodRoots h r k S n) n)
  integrable := integrable_rescale (rootSum_integrable hh r k _ n) p (scale_pos hr k).ne'
  cone := by
    classical
    apply ae_of_all
    intro X
    have hc := cone_sum (by norm_num : (0:ℝ) ≤ 1/2) (goodRoots h r k S n)
      (fun q => rootVector N r h k q n (p+scale r k • X)) (by
        intro q hq
        have hg : Good n (DirectionNeighbors.theta h (scale r k) q) := (mem_filter.mp hq).2
        exact rootVector_cone hr hR hN hh hsupp k q hn hg hs _)
    simp only [rescale,norm_smul,Real.norm_eq_abs,abs_of_pos (scale_pos hr k),real_inner_smul_right]
    change (1/2:ℝ)*(scale r k*‖rootSum h r k (goodRoots h r k S n) n (p+scale r k • X)‖) ≤ _
    dsimp only [rootSum]
    nlinarith [mul_le_mul_of_nonneg_left hc (scale_pos hr k).le]

def badPrice {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) : ℝ :=
  ∑ q ∈ badRoots h r k S n, scalarMass h (scale r k) q

/-- Bad cone roots are exactly the unrestricted size-one part. -/
def badPiece {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) : ErrorPiece 2 :=
  unitPiece (rescale p (scale r k) (rootSum h r k (badRoots h r k S n) n))
    (integrable_rescale (rootSum_integrable hh r k _ n) p (scale_pos hr k).ne') 2

def cellErrors {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) : Option (ErrorIndex N k) → ErrorPiece 2
  | none => badPiece hr hh k p S n
  | some i => smallPiece hh hr k p S n i

open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

end CommonPrices

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_CommonPrices1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DirectionNeighbors

def cellRoots (N : ℕ) (p : ℤ × ℤ) : Finset (Grid N) :=
  univ.filter (fun q => (q : ℤ × ℤ) ∈ window 20 p)

end CommonPrices

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks Finset DirectionNeighbors

def spatialCharge {N : ℕ} (C : ℕ → Grid N → ℝ) (k : ℕ) (q : Grid N)
    (p : List (Grid N)) : ℝ := C (k-p.length) (lastVertex q p)

/-- Particle observations use the prescribed terminal vertex, not a hat-density
surrogate. This is the frozen spatial location carried throughout the process. -/
def particleSwitches {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (q : Grid N)
    (p : List (Grid N)) (b : ℕ) : ℝ :=
  pathSwitches h r k (point r (lastVertex q p)) p b

end ActualMarkTrees

namespace FiniteLabels
variable {ι : Type*} [Fintype ι]
lemma expect_const (μ : Law ι) (c : ℝ) : expect μ (fun _ => c) = c := by
  rw [expect,← Finset.sum_mul,μ.total,one_mul]
lemma expect_mul (μ : Law ι) (f : ι → ℝ) (c : ℝ) :
    expect μ (fun i => c*f i) = c*expect μ f := by
  simp only [expect,Finset.mul_sum,mul_left_comm]
lemma expect_mono (μ : Law ι) {f g : ι → ℝ} (h : ∀ i, f i ≤ g i) :
    expect μ f ≤ expect μ g := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (μ.nonneg i))
end FiniteLabels

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats Finset

def comparisonConstant : ℝ := 1280000*((Fintype.card Label:ℝ)+1)

def rowDerivative (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) : ℝ :=
  r*∑ j : Label, ‖gradient (fun y => row h r y n j) x‖
def derivativeCost (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) : ℕ → ℝ
  | 0 => r 0*∑ j : Label, ‖gradient (fun y => initial h (r 0) y j) x‖
  | i+1 => expect (marginal h r i x) (rowDerivative h (r (i+1)) x)

end ActualLabels

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_ActualLabels1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats Finset

def energyRate (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ) (y : ℂ) (i : ℕ) : ℝ :=
  switchCost h r y i+energy h (r i) (q i)

end ActualLabels

namespace GeometricFilter
open Finset
/-- Causal dyadic averaging, with both the present and the complete past. -/
def filt (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => c 0
  | i+1 => c (i+1)+filt c i/2

open Finset
end GeometricFilter

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats Finset GeometricFilter

def spatialConstant : ℝ := 208*comparisonConstant^2
end ActualLabels

namespace DyadicHats

def neighborhood (r : ℝ) (q : ℤ × ℤ) : Set ℂ := {x | boxNorm (x-point r q) ≤ 25*r}
end DyadicHats

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks

def pathVertex {N : ℕ} (q : Grid N) (p : List (Grid N)) (i : ℕ) : ℤ × ℤ := lastVertex q (p.take i)

end ActualMarkTrees

namespace DyadicHats
noncomputable def localSup (f : ℂ → ℝ) (r : ℝ) (q : ℤ × ℤ) : ℝ :=
  sSup (f '' neighborhood r q)
end DyadicHats

namespace ActualLabels
open DyadicHats GeometricFilter FiniteLabels Finset

def cellCost (h : ℂ → ℂ) (r : ℕ → ℝ) (m l : ℕ) (q : ℤ × ℤ) : ℝ :=
  localSup (fun x => switchCost h r x l) (r l) q+
  (if l=m then 1 else localSup (fun x => switchCost h r x (l+1)) (r l) q)+
  filt (fun i => localSup (fun x => derivativeCost h r x i) (r l) q) l

end ActualLabels

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_ActualMarkTrees2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks ActualLabels GeometricFilter Finset

open DyadicHats IntrinsicMarks ActualLabels GeometricFilter DirectionNeighbors Finset

def packingCharge {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (m : ℕ) (q : Grid N) : List (Grid N) → ℝ :=
  spatialCharge (fun j z => cellCost h (fun i => scale r (m-i)) m (m-j) z) m q

def packingConstant : ℝ :=
  8*spatialConstant*(2560004+2000000*(576*(4097:ℝ)^2))+
  8*spatialConstant*(576*(4097:ℝ)^2)+(130*spatialConstant+1)
end ActualMarkTrees

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces

def rootMass {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) : ℝ :=
  ∑ q ∈ S, scalarMass h (scale r k) q

def sizeErrors {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) : Option (ErrorIndex N k) → ErrorPiece 2
  | none => unitPiece (rescale p (scale r k) (rootSum h r k S n))
      (integrable_rescale (rootSum_integrable hh r k S n) p (scale_pos hr k).ne') 2
  | some i => smallPiece hh hr k p S n i

end CommonPrices

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskMaximalTools2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace PhysicalCells
open MeasureTheory Set

def unitCell : Set ℂ := {X | X.re ∈ Ico (0:ℝ) 1 ∧ X.im ∈ Ico (0:ℝ) 1}
def toUnit (p : ℂ) (r : ℝ) (y : ℂ) : ℂ := r⁻¹ • (y-p)
def cell (p : ℂ) (r : ℝ) : Set ℂ := toUnit p r ⁻¹' unitCell

end PhysicalCells

namespace DiskMoments

def PhysicalNeighborhoodRadius (g : ℂ → ℝ) (r : ℝ) (x : ℂ) (t : ℝ) : Prop :=
  t ∈ Icc r (2*r) ∧ ∀ s, 0 < s → |s-t| ≤ r/4 → signedAverage g x s ≤ signedAverage g x t

def PhysicalEndpointRadius (g : ℂ → ℝ) (r : ℝ) (x : ℂ) (t : ℝ) : Prop :=
  t ∈ Icc r (2*r) ∧ (t = r ∨ t = 2*r ∨ ∀ s ∈ Icc r (2*r), signedAverage g x s ≤ signedAverage g x t)

end DiskMoments

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_PhysicalCells1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace SignedRuns

section
open DiskMoments RadiusEnvelope ActualLabels Finset

variable (g : ℂ → ℝ) (r : ℕ → ℝ)
def runEnvelope (i j : ℕ) (x : ℂ) : ℝ :=
  envelope (fun t y => signedAverage g y t) (r j) (2*r i) x

/-- Reversed chronological histories. The active run's start is retained when
its new label agrees, and is reset to the new time at a switch. -/
def activeStart : List Label → ℕ
  | [] => 0
  | [_] => 0
  | n::old::p => if n = old then activeStart (old::p) else (old::p).length

/-- The exact closed-prefix vector potential, updated without ever taking the
absolute size of an old large-radius envelope. -/
def potential (x : ℂ) : List Label → ℂ
  | [] => 0
  | [n] => (runEnvelope g r 0 0 x-signedAverage g x (r 0)) • (n:ℂ)
  | n::old::p => potential x (old::p)+
      (if n = old then (runEnvelope g r (activeStart (old::p)) (p.length+1) x-
        runEnvelope g r (activeStart (old::p)) p.length x) • (n:ℂ)
      else (runEnvelope g r (p.length+1) (p.length+1) x-
        signedAverage g x (r (p.length+1))) • (n:ℂ))

end

open SignedAssembly FiniteLabels ActualLabels Finset

variable (g : ℂ → ℝ) (r : ℕ → ℝ) (x : ℂ)
variable (J : ℕ → Label → RowJet Label ℂ) (v : ℕ → ℝ)

/-- The actual closed-prefix potentials at the leaves, with the stochastic
row jet at every observation time. -/
def jet : ℕ → List Label → Label → JetTree Label ℂ
  | 0,p,_ => .leaf (potential g r x p)
  | d+1,p,n => .branch (J p.length n) (potential g r x p)
      (∑ k ∈ Ico p.length (p.length+d+1), v k) (fun a => jet d (a::p) a)

/-- Backward expected reward for an arbitrary time-dependent finite Markov law. -/
def rewardCost (reward : ℕ → Label → ℝ) : ℕ → ℕ → Label → ℝ
  | _,0,_ => 0
  | k,d+1,n => reward k n+expect (J k n).law (fun a => rewardCost reward (k+1) d a)

end SignedRuns

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_SignedRuns1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace SignedRuns
open DiskMoments RadiusEnvelope ActualLabels ConeCoordinates

structure Run where
  dir : Label
  first : ℕ
  last : ℕ

/-- Completed runs, in reverse chronological order. -/
def closedRuns : List Label → List Run
  | [] => []
  | [_] => []
  | n::old::p => if n = old then closedRuns (old::p)
      else ⟨old,activeStart (old::p),p.length⟩::closedRuns (old::p)

def runs : List Label → List Run
  | [] => []
  | n::p => ⟨n,activeStart (n::p),p.length⟩::closedRuns (n::p)

end SignedRuns

namespace SignedAssembly
open Finset FiniteLabels
variable {ι : Type*} [Fintype ι]

/-- The zero row-sum is obtained by differentiating the actual stochastic
partition of unity, not postulated for the row derivatives. -/
def RowJet.ofLawAt (P : ℂ → Law ι) (x : ℂ)
    (hd : ∀ i, DifferentiableAt ℝ (fun y => P y i) x) : RowJet ι ℂ where
  law := P x
  grad i := gradient (fun y => P y i) x
  total_grad := by
    have ht : (fun y => ∑ i, P y i) = fun _ => (1:ℝ) := funext fun y => (P y).total
    have hs : (∑ i, fderiv ℝ (fun y => P y i) x) = 0 := by
      rw [← fderiv_fun_sum (fun i _ => hd i),ht]
      exact fderiv_const_apply (1:ℝ)
    simp only [gradient,← _root_.map_sum,hs,map_zero]
end SignedAssembly

namespace ActualLabels
open FiniteLabels SignedAssembly Finset ConeCoordinates

/-- Observation time zero is the true initial spatial row. Subsequent times
are the true state-dependent spatial switch rows. -/
def observation (h : ℂ → ℂ) (r : ℕ → ℝ) : ℕ → ℂ → Label → Law Label
  | 0,x,_ => initial h (r 0) x
  | k+1,x,n => row h (r (k+1)) x n

def before (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ) : ℕ → Law Label
  | 0 => delta old
  | k+1 => marginal h r k x

def observationJet (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ)
    (hd : ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x)
    (k : ℕ) (n : Label) : RowJet Label ℂ :=
  RowJet.ofLawAt (fun y => observation h r k y n) x (hd k n)

end ActualLabels

namespace SignedRuns
open ActualLabels FiniteLabels SignedAssembly Finset

def weight (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ) : List Label → ℝ
  | [] => 1
  | n::p => weight h r old x p*observation h r p.length x (p.headD old) n

def leafSum {E : Type*} [AddCommMonoid E] (f : List Label → E) : ℕ → List Label → E
  | 0,p => f p
  | d+1,p => ∑ n, leafSum f d (n::p)

open DiskMoments RadiusEnvelope ActualLabels ConeCoordinates

def coneContribution (n : Label) (z : ℂ) : ℝ :=
  inner ℝ (n:ℂ) z+max 0 (-inner ℝ (axis n 1) z)+max 0 (-inner ℝ (axis n (-1)) z)

end SignedRuns

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_DiskMoments1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace SignedRuns
open DiskMoments ActualLabels

def Regular (f : ℂ → ℂ) : Prop := HasCompactSupport f ∧ ∃ L : ℝ≥0, LipschitzWith L f

open Complex

def divergence (V : ℂ → ℂ) (x : ℂ) : ℝ :=
  fderiv ℝ (fun y => (V y).re) x 1+fderiv ℝ (fun y => (V y).im) x I

open ActualLabels FiniteLabels SignedAssembly Finset DiskMoments

open DiskMoments ActualLabels Complex

open DiskMoments ActualLabels Finset ConeCoordinates

def unfavorable (n : Label) (z : ℂ) : ℝ :=
  max 0 (-inner ℝ (axis n 1) z)+max 0 (-inner ℝ (axis n (-1)) z)

end SignedRuns

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_SignedRuns2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace SignedRuns
open ActualLabels FiniteLabels Finset

/-- Additive reward along a reversed history, with its true previous state. -/
def pathReward (old : Label) (A : ℕ → Label → Label → ℝ) : List Label → ℝ
  | [] => 0
  | n::p => pathReward old A p+A p.length (p.headD old) n

open ActualLabels FiniteLabels Finset

def startReward (J : ℕ → ℝ) : ℕ → Label → Label → ℝ
  | 0,_,_ => J 0
  | k+1,n,j => if j = n then 0 else J (k+1)

def boundaryReward (J : ℕ → ℝ) : ℕ → Label → Label → ℝ
  | 0,_,_ => J 0
  | k+1,n,j => if j = n then 0 else J k+J (k+1)

end SignedRuns

namespace ActualLabels
open FiniteLabels DyadicHats Finset

lemma row_change_le_rate (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) :
    expect (row h r x n) (fun j => if j = n then 0 else 1) ≤ rate h r x n := by
  rw [row,spatialRow_expect]
  simp only [ite_true,sub_zero,zero_add]
  apply interpolate_mono
  intro z
  split_ifs <;> simp [switchChance_nonneg]

open FiniteLabels Finset

def boundaryCost (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (m k : ℕ) : ℝ :=
  switchCost h r x k+(if k=m then 1 else switchCost h r x (k+1))

lemma observation_boundaryReward_le (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (J : ℕ → ℝ) (hJ : ∀ k, 0 ≤ J k) (k : ℕ) :
    expect (before h r old x k)
      (fun n => expect (observation h r k x n) (SignedRuns.boundaryReward J k n)) ≤
      (match k with | 0 => J 0 | l+1 => switchCost h r x (l+1)*(J l+J (l+1))) := by
  cases k with
  | zero =>
    change (expect (delta old) fun _ => expect (initial h (r 0) x) (fun _ => J 0)) ≤ J 0
    rw [FiniteLabels.expect_const,FiniteLabels.expect_const]
  | succ k =>
    change expect (marginal h r k x) (fun n => expect (row h (r (k+1)) x n)
      (fun j => if j = n then 0 else J k+J (k+1))) ≤ _
    have he (n : Label) : (fun j : Label => if j = n then (0:ℝ) else J k+J (k+1)) =
        fun j => (J k+J (k+1))*(if j = n then 0 else 1) := by funext j; split_ifs <;> simp
    simp_rw [he,FiniteLabels.expect_mul]
    rw [switchCost,mul_comm _ (J k+J (k+1))]
    apply mul_le_mul_of_nonneg_left _ (add_nonneg (hJ _) (hJ _))
    exact expect_mono _ (fun n => row_change_le_rate h (r (k+1)) x n)

end ActualLabels

namespace PhysicalCells
open DyadicHats DirectionNeighbors CommonPrices Finset

def gridIndex (r : ℝ) (y : ℂ) : ℤ × ℤ := (⌊y.re/r⌋,⌊y.im/r⌋)

end PhysicalCells

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_CommonPrices2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace PhysicalCells
open DyadicHats Finset

/-- Measurable full-lattice patch; no choice of maximizing radius occurs. -/
def patch (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (x : ℂ) : ℝ≥0∞ :=
  ∑' p, (cell (point r p) r).indicator (F p) x

end PhysicalCells

namespace ActualLabels
open DyadicHats FiniteLabels GeometricFilter Finset

/-- Global geometric extension of the finite descending radius grid. -/
def geometricRadii (base : ℝ) (m : ℕ) (k : ℕ) : ℝ := scale base m/(2:ℝ)^k
end ActualLabels

namespace PhysicalCells
open DyadicHats
noncomputable def cellSup (f : ℂ → ℝ) (r : ℝ) (p : ℤ × ℤ) : ℝ :=
  sSup (f '' cell (point r p) r)
end PhysicalCells

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells CommonPrices DirectionNeighbors FiniteLabels Finset

def pointCost (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (m k : ℕ) : ℝ :=
  boundaryCost h r x m k+filt (fun i => derivativeCost h r x i) k

def costLimit : ℝ := 2+32*(Fintype.card Label:ℝ)
end ActualLabels

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_CommonPrices3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace CommonPrices
open DyadicHats ConeCoordinates Finset

def priceConstant : ℝ := 1681*((fixedPalette.labels.card:ℝ)*2/(1-rho))
end CommonPrices

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells CommonPrices DirectionNeighbors FiniteLabels Finset ActualMarkTrees

open DyadicHats PhysicalCells CommonPrices ActualMarkTrees Finset FiniteLabels

def spatialPriceConstant : ℝ := 1681*packingConstant+costLimit*priceConstant

def directPriceConstant : ℝ := 1000000*1681*(576*(4097:ℝ)^2)+priceConstant
end ActualLabels

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_CommonPrices4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace WeakSobolev
open ContinuousLinearMap
open scoped Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Directional, coordinate-free distributional gradient. -/
def HasGradient (f : E → ℝ) (g : E → E) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ v : E,
    (∫ x, f x * fderiv ℝ φ x v ∂μ) = -∫ x, ⟪g x,v⟫ * φ x ∂μ

end WeakSobolev

end SignedDisk

end

end OAI
end

section
-- module Solutions.OAIW2_SignedDisk.SignedDisk_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace SobolevBand
open DiskMoments RadiusEnvelope

def band (f : ℂ → ℝ) (a b : ℝ) := envelope (fun r x => signedAverage f x r) a b

open DiskMoments RadiusEnvelope SignedRuns GeometricFilter DyadicHats ActualLabels

end SobolevBand

namespace CenteredDiskEndpoint
open WeakSobolev

/-- The coordinate isometry preserves Euclidean, not max-product, norms. -/
def complexPlane : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

end CenteredDiskEndpoint

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff Convolution

namespace SobolevBand
open DiskMoments RadiusEnvelope ContinuousLinearMap

/-- The normalized open-disk kernel, without an absolute value on the input. -/
def diskKernel (a : ℝ) : ℂ → ℝ :=
  (Metric.ball (0 : ℂ) a).indicator (fun _ => (Real.pi * a^2)⁻¹)

end SobolevBand

end SignedDisk

end

end OAI
end


