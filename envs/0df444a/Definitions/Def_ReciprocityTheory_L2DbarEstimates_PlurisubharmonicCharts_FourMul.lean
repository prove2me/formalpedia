-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:58.057633+00:00
-- url     : https://prove2.me/theorems/a5c3ed63-283b-43d5-a5b0-25575a100db9
-- title:
--   Four Mul
-- statement:
--   Definitions and structural lemmas for Four Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourMul.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ComplexConjugate
noncomputable section
def FOURMulStatement (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h1 h2 : (Fin f → ℂ) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ h1 (tube f Ω) → DifferentiableOn ℂ h2 (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h1 (s + fun k => (m k : ℂ)) = h1 s) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h2 (s + fun k => (m k : ℂ)) = h2 s) →
    ∀ b ∈ Ω,
    Summable (fun ν : Fin f → ℤ => ‖fourCoeff h1 b ν‖) →
    Summable (fun ν : Fin f → ℤ => ‖fourCoeff h2 b ν‖) →
    ∀ ν : Fin f → ℤ,
      fourCoeff (h1 * h2) b ν = ∑' ν' : Fin f → ℤ, fourCoeff h1 b ν' * fourCoeff h2 b (ν - ν')
def FOURMulStatement' (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h1 h2 : (Fin f → ℂ) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ h1 (tube f Ω) → DifferentiableOn ℂ h2 (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h1 (s + fun k => (m k : ℂ)) = h1 s) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h2 (s + fun k => (m k : ℂ)) = h2 s) →
    ∀ b ∈ Ω, ∀ ν : Fin f → ℤ,
      HasSum (fun ν' : Fin f → ℤ => fourCoeff h1 b ν' * fourCoeff h2 b (ν - ν'))
        (fourCoeff (h1 * h2) b ν)
def FOURMulSuppStatement (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h1 h2 : (Fin f → ℂ) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ h1 (tube f Ω) → DifferentiableOn ℂ h2 (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h1 (s + fun k => (m k : ℂ)) = h1 s) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h2 (s + fun k => (m k : ℂ)) = h2 s) →
    ∀ b ∈ Ω, ∀ ν : Fin f → ℤ, fourCoeff (h1 * h2) b ν ≠ 0 →
      ∃ ν1 ν2, ν1 + ν2 = ν ∧ fourCoeff h1 b ν1 ≠ 0 ∧ fourCoeff h2 b ν2 ≠ 0
local instance _p2m_local_instance_19aabe418c_38 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance _p2m_local_instance_19aabe418c_40 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
def fmLine {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ) : (Fin f → ℝ) → ℂ :=
  fun x => h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I)
end
end ReciprocityTheory.L2DbarEstimates.Y


