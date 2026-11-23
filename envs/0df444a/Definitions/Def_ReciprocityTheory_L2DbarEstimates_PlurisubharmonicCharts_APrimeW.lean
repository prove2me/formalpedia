-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeW
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:48.723712+00:00
-- url     : https://prove2.me/theorems/8fbd35ae-bfb2-4781-be66-c8ada3bcc9dc
-- title:
--   APrime W
-- statement:
--   Definitions and structural lemmas for APrime W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeW.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
structure APGeom (A : WeightedAtlas n Y ι La) (la : La) (d m : ℕ) (r r' : ℝ) (B : Fin m → Set Y)
    (π : Fin m → Y → EuclideanSpace ℂ (Fin d)) (f : Fin m → ι → Y → ℂ) : Prop where
  r_pos : 0 < r
  r_lt : r < r'
  isOpen : ∀ a, IsOpen (B a)
  disj : Pairwise (Function.onFun Disjoint B)
  holo : ∀ a i, DifferentiableOn ℂ (π a ∘ (A.chart i).symm)
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' B a)
  lt_r' : ∀ a, ∀ y ∈ B a, ‖π a y‖ < r'
  proper : ∀ a (K : Set (EuclideanSpace ℂ (Fin d))), IsCompact K → K ⊆ Metric.ball 0 r' →
    IsCompact (B a ∩ π a ⁻¹' K)
  sec : ∀ a, A.IsSecOn (A.kap + la) (B a) (f a)
def apBump {m d : ℕ} (B : Fin m → Set Y) (π : Fin m → Y → EuclideanSpace ℂ (Fin d)) (r : ℝ)
    (Φ : ℝ → ℝ) (y : Y) : ℝ :=
  ∑ a, (B a).indicator (fun x => Φ (‖π a x‖ ^ 2 / r ^ 2)) y
def chartCutoffSum {m d : ℕ} (B : Fin m → Set Y) (π : Fin m → Y → EuclideanSpace ℂ (Fin d)) (r : ℝ)
    (χ : ℝ → ℝ) (f : Fin m → ι → Y → ℂ) : ι → Y → ℂ :=
  fun i y => ∑ a, (B a).indicator (fun x => ((χ (‖π a x‖ ^ 2 / r ^ 2) : ℝ) : ℂ) * f a i x) y
def apH {m d : ℕ} (A : WeightedAtlas n Y ι La) (la : La) (B : Fin m → Set Y)
    (π : Fin m → Y → EuclideanSpace ℂ (Fin d)) (r : ℝ) (χ : ℝ → ℝ) (f : Fin m → ι → Y → ℂ)
    (c : ℝ) (y : Y) : ℝ≥0∞ :=
  ∑ a, (B a).indicator (fun x => ENNReal.ofReal (A.nsq (A.kap + la) (f a) x *
    deriv χ (‖π a x‖ ^ 2 / r ^ 2) ^ 2 * (‖π a x‖ ^ 2 / r ^ 2) / c)) y
end
end ReciprocityTheory.L2DbarEstimates.Y


