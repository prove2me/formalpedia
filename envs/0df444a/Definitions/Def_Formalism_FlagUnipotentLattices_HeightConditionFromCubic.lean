-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_HeightConditionFromCubic
-- name    : Formalism_FlagUnipotentLattices_HeightConditionFromCubic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:01.334987+00:00
-- url     : https://prove2.me/theorems/81d31ec7-3487-413d-a30b-c3cbf1435355
-- title:
--   Height Condition From Cubic
-- statement:
--   Definitions and structural lemmas for Height Condition From Cubic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/HeightConditionFromCubic.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_BlockDistFromLows
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.HermitianLatticeCounting.S8
def SizeAR : Prop :=
  (∀ x : ℝ, 1801 ≤ x → 120 * x * (x / 2 * Real.sqrt (x / 2)) ≤ x ^ 3) ∧
  ∀ k m t j : ℕ, 1801 ≤ (k + m - 1) + t → 1 ≤ j →
    120 * ((k + m - 1 + j * t : ℕ) : ℝ) * (((k + m - 1 + j * t : ℕ) : ℝ) / 2 * Real.sqrt (((k + m - 1 + j * t : ℕ) : ℝ) / 2))
      ≤ ((k + m - 1 + j * t : ℕ) : ℝ) ^ 3
def HeightConditionFromCubic : Prop :=
  ∀ k m t : ℕ, 1 ≤ k → 2 ≤ m → (k + m - 1) + 5 ≤ t →
    3 * ((k + m - 1 : ℕ) : ℝ) < Mrk k m t ∧ 54 * ((k + m - 1 : ℕ) : ℝ) ^ 3 < 2 * Mrk k m t ^ 3 ∧
    ∀ h : ℝ, 2 * Mrk k m t ^ 3 + t + 3 < h →
      43 * (((k + m - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((k + m - 1 : ℕ) : ℝ)) ≤ h
def ParamDCosetMinus : Prop :=
  ∀ (k m t j : ℕ) (v : List ℝ) (b e : ℕ → ℝ), 1 ≤ k → Even m → Odd t →
    (∀ x ∈ v, ∃ z : ℤ, x = (z : ℝ) + (k : ℝ) / 2) → (∀ i < m, ∃ z : ℤ, b i = (z : ℝ) + (k : ℝ) / 2) →
    (∀ i < m, ∃ z : ℤ, e i = (z : ℝ) + (k : ℝ) / 2) →
    ∀ x ∈ paramD t j m v b e, Odd j → ∃ z : ℤ, x - 1 / 2 - (((k + m - 1 + j * t : ℕ) : ℝ) - 1) / 2 = (z : ℝ)
def hcCompact (a t' : ℕ) (c : ℝ) (ν : ℕ → ℤ) (i : ℕ) : ℝ :=
  (ν i : ℝ) + ((a : ℝ) + ((a + t' : ℕ) : ℝ) + 1) / 2 - (i : ℝ) + c
def CompactPairParam : Prop :=
  ∀ (a t' : ℕ) (c : ℝ),
    (List.range t').map (fun l : ℕ => ((a : ℝ) + ((a + t' : ℕ) : ℝ) + 1) / 2 - ((a + 1 + l : ℕ) : ℝ) + c) = blockP c t' ∧
    (∀ ν : ℝ, (c + ((t' : ℝ) + 1) / 2 ≤ ν + ((a : ℝ) + ((a + t' : ℕ) : ℝ) + 1) / 2 - a + c ↔ 0 ≤ ν)) ∧
    (∀ ν : ℕ → ℤ,
      (∀ i : ℕ, hcCompact a t' c ν i - (c + ((t' : ℝ) + 1) / 2) = ((ν i + (a : ℤ) - (i : ℤ) : ℤ) : ℝ)) ∧
      (∀ i : ℕ, ν (i + 1) ≤ ν i ↔ hcCompact a t' c ν (i + 1) < hcCompact a t' c ν i) ∧
      (0 ≤ ν a ↔ c + ((t' : ℝ) + 1) / 2 ≤ hcCompact a t' c ν a)) ∧
    (∀ α : ℕ → ℝ, (∀ i, ∃ z : ℤ, α i = c + ((t' : ℝ) + 1) / 2 + (z : ℝ)) → ∃! ν : ℕ → ℤ, ∀ i, α i = hcCompact a t' c ν i)
def GArithC : Prop :=
  ∀ k m t : ℕ, 1 ≤ k → 2 ≤ m → (k + m - 1) + 5 ≤ t → 1801 ≤ (k + m - 1) + t →
    ((k + m - 1 : ℕ) : ℝ) + (t : ℝ) ≤ Mrk k m t ∧
    40 * Real.sqrt ((m : ℝ) / 2) ≤ Mrk k m t ∧
      ∀ n q₀ : ℝ, 0 ≤ n → n ≤ Mrk k m t → 0 ≤ q₀ → q₀ ≤ (m : ℝ) / 2 →
        40 * n ^ 2 * Real.sqrt q₀ ≤ Mrk k m t ^ 3
def UnitIntegrableArithmetic : Prop :=
  ∀ n q : ℝ, 1 ≤ n → 1 ≤ q →
    16 * (n - 1) * q < 120 * n * (q * Real.sqrt q) ∧
    ∀ h : ℝ, 120 * n * (q * Real.sqrt q) ≤ h → 8 * 0 * Real.sqrt q + 16 * (n - 1) * q < h
def CorConsts : Prop :=
  ∀ n q : ℝ, 0 ≤ q → q ≤ n / 2 →
    120 * n * (q * Real.sqrt q) ≤ 42.5 * (n ^ 2 * Real.sqrt n) ∧
    (2 ≤ n →
      8 * (n ^ 2 + 2) * Real.sqrt q + 16 * (n - 1) * q ≤ 8.5 * (n ^ 2 * Real.sqrt n) + 8 * n ^ 2 ∧
      8.5 * (n ^ 2 * Real.sqrt n) + 8 * n ^ 2 ≤ 17 * (n ^ 2 * Real.sqrt n))
end Formalism.HermitianLatticeCounting.S8


