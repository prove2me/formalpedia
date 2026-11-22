-- Prove2me | Definitions.Def_Formalism_LogVandermondeBounds_EvenOddPowerQuotientEqualityCases
-- name    : Formalism_LogVandermondeBounds_EvenOddPowerQuotientEqualityCases
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:42:25.644901+00:00
-- url     : https://prove2.me/theorems/ad1166f2-54c8-4e45-9c6c-acb09d13bea8
-- title:
--   Even Odd Power Quotient Equality Cases
-- statement:
--   Definitions and structural lemmas for Even Odd Power Quotient Equality Cases, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/EvenOddPowerQuotientEqualityCases.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LogVandermondeBounds.TaylorLogMetric
open Finset
def EvenOddPowerQuotientLowerBound : Prop :=
  ∀ (p i j : ℕ), 2 ≤ p → i ≤ j → (i, j) ≠ (0, 0) →
    ((p : ℚ) - 2) + 1 / ((p : ℚ) - 1) ≤
      (((p : ℚ) ^ 2) ^ i + (p : ℚ) * ((p : ℚ) ^ 2) ^ j) / ((p : ℚ) ^ 2 - 1) - ((i : ℚ) + j + 1)
def EvenOddPowerQuotientEqualityCases : Prop :=
  ∀ (p : ℕ), 2 ≤ p →
    ((((p : ℚ) ^ 2) ^ 0 + (p : ℚ) * ((p : ℚ) ^ 2) ^ 1) / ((p : ℚ) ^ 2 - 1) - (0 + 1 + 1) =
      ((p : ℚ) - 2) + 1 / ((p : ℚ) - 1)) ∧
    ((((p : ℚ) ^ 2) ^ 1 + (p : ℚ) * ((p : ℚ) ^ 2) ^ 1) / ((p : ℚ) ^ 2 - 1) - (1 + 1 + 1) =
      ((p : ℚ) - 2) + 1 / ((p : ℚ) - 1))
def LegendreFactorialBound : Prop :=
  ∀ (p i : ℕ), p.Prime → 1 ≤ i → (p - 1) * padicValNat p i.factorial ≤ i - 1
open Classical in

noncomputable def coefL (p a : ℕ) : ℚ :=
  if h : ∃ j, a = (p ^ 2) ^ j then 1 / (p : ℚ) ^ (Classical.choose h) else 0
open Classical in
noncomputable def coefG (p a : ℕ) : ℚ :=
  if h : ∃ j, a = p * (p ^ 2) ^ j then 1 / (p : ℚ) ^ (Classical.choose h + 1) else 0
open Classical in

noncomputable def coefA (p a b : ℕ) : ℚ :=
  if h : ∃ i j, i ≤ j ∧ a = (p ^ 2) ^ i ∧ b = p * (p ^ 2) ^ j then
    1 / (p : ℚ) ^ (Classical.choose h + Classical.choose (Classical.choose_spec h) + 1) else 0
noncomputable def coefB (p a b : ℕ) : ℚ := coefA p b a
def LogarithmSeriesIdentities : Prop :=
  ∀ (p : ℕ), p.Prime →
    (∀ a : ℕ, (if p ∣ a then coefG p (a / p) else 0) = coefL p a - (if a = 1 then 1 else 0)) ∧
    (∀ a b : ℕ, (if p ∣ a ∧ p ∣ b then coefA p (a / p) (b / p) else 0) =
      (p : ℚ) * (coefG p a * coefL p b - coefB p a b))
def UnitaryDeterminantPhase : Prop :=
  ∀ (n : ℕ) (δ : Matrix (Fin n) (Fin n) ℂ), δ ∈ Matrix.unitaryGroup (Fin n) ℂ →
    (1 - δ⁻¹).det ≠ 0 →
    (starRingEnd ℂ) (1 - δ⁻¹).det / (1 - δ⁻¹).det = (-1) ^ n * δ.det
end Formalism.LogVandermondeBounds.TaylorLogMetric


