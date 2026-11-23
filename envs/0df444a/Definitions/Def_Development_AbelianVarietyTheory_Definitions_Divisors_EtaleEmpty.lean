-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EtaleEmpty
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_EtaleEmpty
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:32.55412+00:00
-- url     : https://prove2.me/theorems/98f5f6c9-0ade-4fb8-a9db-6a3d2ed9169d
-- title:
--   Etale Empty
-- statement:
--   Definitions and structural lemmas for Etale Empty, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EtaleEmpty.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.OTY
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
noncomputable section
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
def jz (A : WeightedAtlas n Y ι La) (z : Y → V n) (i : ι) (y : Y) : V n →L[ℂ] V n :=
  fderiv ℂ (z ∘ (A.chart i).symm) (A.chart i y)
def jdet (A : WeightedAtlas n Y ι La) (z : Y → V n) : ι → Y → ℂ :=
  fun i y => (jz A z i y).det
structure Etale (A : WeightedAtlas n Y ι La) (U : Set Y) (z : Y → V n) : Prop where
  isOpen : IsOpen U
  holo : ∀ i, DifferentiableOn ℂ (z ∘ (A.chart i).symm)
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)
  det_ne : ∀ i y, y ∈ U → y ∈ (A.chart i).source → jdet A z i y ≠ 0
def nz (A : WeightedAtlas n Y ι La) (τ : ι → Y → ℂ) : Set Y := {y | τ (A.pick y) y ≠ 0}
structure Cover (A : WeightedAtlas n Y ι La) where

  m : ℕ

  idx : Fin m → ι

  c : Fin m → V n

  r : Fin m → ℝ

  chi : Fin m → Y → ℝ
  r_pos : ∀ a, 0 < r a
  sub : ∀ a, Metric.closedBall (c a) (r a) ⊆ (A.chart (idx a)).target
  smooth : ∀ a, A.SmoothFn (chi a)
  supp : ∀ a, tsupport (chi a) ⊆
    (A.chart (idx a)).source ∩ A.chart (idx a) ⁻¹' Metric.ball (c a) (r a)
  nonneg : ∀ a y, 0 ≤ chi a y
  sum_one : ∀ y, ∑ a, chi a y = 1
def n0 (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) F y) ∂A.mu
def n1 {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (F : ι → Y → ℂ) : ℝ≥0∞ :=
  ∑ a, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
    ((∑ j, ‖wdb n j (F (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
      Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
def CurvGe {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (t : ℝ) : Prop :=
  ∀ a, ∀ v ∈ Metric.ball (C.c a) (C.r a), ∀ ξ : Fin n → ℂ,
    t * ∑ j, ‖ξ j‖ ^ 2 ≤ A.leviAt (C.idx a) (A.ph la (C.idx a)) ((A.chart (C.idx a)).symm v) ξ
def glue {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) :
    ι → Y → ℂ :=
  fun i y => ∑ a, (C.chi a y : ℂ) * A.g (A.kap + la) i (C.idx a) y * u a (A.chart (C.idx a) y)
def wT (T x : ℝ) : ℝ := 1 / (1 + min (x ^ 2) ((T + 1) ^ 2))
def IsCut (T : ℝ) (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) θ ∧ (∀ x, x ≤ -T - 1 → θ x = 1) ∧ (∀ x, -T + 1 ≤ x → θ x = 0) ∧
    (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧ ∀ x, |deriv θ x| ≤ 3 / 4
end
end GlobalTheory.OTY


