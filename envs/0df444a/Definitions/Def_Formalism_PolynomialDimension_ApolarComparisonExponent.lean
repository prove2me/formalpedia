-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_ApolarComparisonExponent
-- name    : Formalism_PolynomialDimension_ApolarComparisonExponent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:11.359808+00:00
-- url     : https://prove2.me/theorems/66bcfa91-b1ac-4833-b748-0f2eaeacc34d
-- title:
--   Apolar Comparison Exponent
-- statement:
--   Definitions and structural lemmas for Apolar Comparison Exponent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/ApolarComparisonExponent.lean

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_WeylDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.CountingSumsFrames
def logScale (C₀ : ℝ) (N₁ : ℕ) (a : ℝ) : ℝ := C₀ * (N₁ : ℝ) ^ 2 * Real.log a
def logBaseP (p : ℕ) (a : ℝ) (k : ℕ) : ℝ := Real.logb p (8 * a + k) + 1
def levelProjectorExponent (p : ℕ) (a : ℝ) (k : ℕ) : ℝ := 3 * logBaseP p a k + 4 * k * logBaseP p a k
def apolarComparisonExponent (p N k : ℕ) (a : ℝ) : ℝ := 2 * N * k * Real.logb p a
def totalSegmentDepth (C5 : ℝ) (p N N₁ J k : ℕ) (Y a : ℝ) : ℝ :=
  J * (C5 * Y ^ 2 * (N₁ : ℝ) ^ 2 * (k : ℝ) ^ 2 * logBaseP p a k + 2 * apolarComparisonExponent p N k a) + 4 * apolarComparisonExponent p N k a
def depthWithKappa (C5 K : ℝ) (p N N₁ J k : ℕ) (Y a kap1 : ℝ) : ℝ :=
  2 * (totalSegmentDepth C5 p N N₁ J k Y a + 6 * N * levelProjectorExponent p a k) + 2 * N * kap1 + K * apolarComparisonExponent p N k a
def c64 (p N k n' : ℕ) (a cl cStar : ℝ) : ℝ :=
  cStar + 4 * N * levelProjectorExponent p a k + 4 * apolarComparisonExponent p N k a + 4 * N * cl + 2 * n' * cl
def cThmI (C : ℝ) (p N k n' : ℕ) (a cl cStar : ℝ) : ℝ :=
  cStar + C * N * k * Real.logb p a + 4 * N * cl + 2 * n' * cl
def PolynomialDimensionIntervalConditions (C C₀ : ℝ) (p N N₁ J k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ) : Prop :=
  2 ≤ p ∧ 1 ≤ Y ∧ (k : ℝ) ^ 2 * Y ^ 2 ≤ p ∧ 1 ≤ N ∧ 1 ≤ N₁ ∧ 2 * N₁ + 2 ≤ k - 1 ∧ 1 ≤ J ∧ J ≤ N ∧
  1 ≤ G' ∧ 2 ≤ n' ∧
  8 * Real.log (N * Y) ≤ logScale C₀ N₁ a ∧
  Yb * N * logScale C₀ N₁ a * b' / k ≤ Ib ∧ Ib ≤ b' / 2 ∧ C ≤ Yb ∧ 2 * Yb * N * logScale C₀ N₁ a < k ∧
  (k : ℝ) * Y ^ 2 * Yb * N * logScale C₀ N₁ a * Real.log a ≤ a / b' ∧ 0 < b' ∧ (p : ℝ) < a / b' ∧
  C * N * logScale C₀ N₁ a ^ 2 ≤ k ∧ 0 ≤ cl ∧ cl ≤ logScale C₀ N₁ a * b' / k ∧
  C * N * Y ^ 2 * ((N₁ : ℝ) ^ 5 + (k : ℝ) ^ 3) * Real.logb p a ≤ D ∧ 8 * (D + 1) ≤ cStar ∧
  C * (k : ℝ) ^ 3 * N * ((p : ℝ) ^ G') ^ 4 * (cStar + N * cl + n' * cl) * Y ≤ b'
def DepthI : Prop :=
  ∀ C5 K : ℝ, 0 ≤ C5 → 0 ≤ K → ∃ C : ℝ, 1 ≤ C ∧ ∀ C₀ : ℝ, 1 ≤ C₀ →
    ∀ (p N N₁ J k n' G' : ℕ) (Y Yb a b' Ib cl D cStar kap1 : ℝ),
      PolynomialDimensionIntervalConditions C C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar →
      0 ≤ kap1 → kap1 ≤ ((k : ℝ) - 1) ^ 2 * logBaseP p a k →
      depthWithKappa C5 K p N N₁ J k Y a kap1 ≤ D
def CleanDepthI : Prop :=
  ∀ C5 K : ℝ, 0 ≤ C5 → 0 ≤ K → ∃ C : ℝ, 1 ≤ C ∧ ∀ C₀ : ℝ, 1 ≤ C₀ →
    ∀ (p N N₁ J k n' G' : ℕ) (Y Yb a b' Ib cl D cStar kap1 : ℝ),
      PolynomialDimensionIntervalConditions C C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar →
      0 ≤ kap1 → kap1 ≤ ((k : ℝ) - 1) ^ 2 * logBaseP p a k →
      4 * totalSegmentDepth C5 p N N₁ J k Y a < c64 p N k n' a cl cStar ∧
      totalSegmentDepth C5 p N N₁ J k Y a + 4 * apolarComparisonExponent p N k a + 6 * N * levelProjectorExponent p a k <
        (c64 p N k n' a cl cStar - 4 * apolarComparisonExponent p N k a - 4 * N * levelProjectorExponent p a k) / 2 ∧
      2 * (totalSegmentDepth C5 p N N₁ J k Y a + 4 * apolarComparisonExponent p N k a + 6 * N * levelProjectorExponent p a k) <
        (c64 p N k n' a cl cStar - 4 * apolarComparisonExponent p N k a - 4 * N * levelProjectorExponent p a k) / 2 ∧
      c64 p N k n' a cl cStar - 4 * N * levelProjectorExponent p a k - 2 * N * (2 * cl) - 2 * n' * cl - 4 * apolarComparisonExponent p N k a = cStar ∧
      8 * depthWithKappa C5 K p N N₁ J k Y a kap1 < cStar ∧
      c64 p N k n' a cl cStar ≤ cThmI C p N k n' a cl cStar
def truncationThreshold {ι : Type} (C4 : ℝ) (p N N₁ k n' G' : ℕ) (C₀ a b' cl cStar : ℝ) (T : Finset ι) (A B pd : ι → ℝ) : ℝ :=
  (∑ y ∈ T, min (B y) (A y / pd y)) +
    C4 * N * (a / (p : ℝ) ^ 2 + b' / p + logScale C₀ N₁ a * a / (p * k) + logScale C₀ N₁ a * b' / k +
      k * (p : ℝ) ^ G' + (p : ℝ) ^ G' * c64 p N k n' a cl cStar)
def tThmI {ι : Type} (C : ℝ) (p N N₁ k n' G' : ℕ) (C₀ a b' cl cStar : ℝ) (T : Finset ι) (am bo pd : ι → ℝ) : ℝ :=
  (∑ y ∈ T, min (bo y) (am y / pd y)) +
    C * N * N₁ * (a / (p : ℝ) ^ 2 + b' / p + logScale C₀ N₁ a * a / (p * k) + logScale C₀ N₁ a * b' / k) +
    C * N * ((p : ℝ) ^ G' * cThmI C p N k n' a cl cStar + k * (p : ℝ) ^ G' + k * Real.logb p a + cl) +
    2 * n' * cl
def CutI : Prop :=
  ∀ C4 : ℝ, 0 ≤ C4 → ∃ C : ℝ, 1 ≤ C ∧ ∀ C₀ : ℝ, 1 ≤ C₀ →
    ∀ (p N N₁ J k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ),
      PolynomialDimensionIntervalConditions C C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar →
      ∀ (ι : Type) (T : Finset ι) (am bo A B pd : ι → ℝ), T.card ≤ N →
        (∀ y ∈ T, 1 ≤ pd y ∧ 0 ≤ am y ∧ 0 ≤ bo y ∧
          B y ≤ bo y + logScale C₀ N₁ a * b' / k + 2 * cl ∧ A y ≤ am y + logScale C₀ N₁ a * b' / k + 2 * cl) →
        (∀ jb ja : ι → ℝ, (∀ y ∈ T, 0 ≤ jb y ∧ jb y ≤ logScale C₀ N₁ a * b' / k ∧
            0 ≤ ja y ∧ ja y ≤ logScale C₀ N₁ a * b' / k) →
          truncationThreshold C4 p N N₁ k n' G' C₀ a b' cl cStar T A B pd ≤
            truncationThreshold C4 p N N₁ k n' G' C₀ a b' cl cStar T (fun y => A y - ja y) (fun y => B y - jb y) pd +
              N * (logScale C₀ N₁ a * b' / k)) ∧
        truncationThreshold C4 p N N₁ k n' G' C₀ a b' cl cStar T A B pd + N * (logScale C₀ N₁ a * b' / k) +
            2 * N * levelProjectorExponent p a k + 2 * apolarComparisonExponent p N k a + 4 * N * cl + 2 * n' * cl ≤
          tThmI C p N N₁ k n' G' C₀ a b' cl cStar T am bo pd
def KapI : Prop :=
  ∀ CW C1 : ℝ, 0 ≤ CW → 0 ≤ C1 → ∃ C : ℝ, 1 ≤ C ∧ ∀ C₀ : ℝ, 1 ≤ C₀ →
    ∀ (p N N₁ J k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ),
      PolynomialDimensionIntervalConditions C C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar →
      ∀ mH mHp : ℝ, mH ≤ C1 * N * N₁ / Y → mHp ≤ C1 * N * N₁ / Y →
        mH + 2 * mHp + CW * N * k * (2 * cl) / b' + N * cl * (1 / (a / (k * Y)) + 1 / Ib) ≤ C * N * N₁ / Y
def MarginI : Prop :=
  ∀ Cm : ℝ, 0 ≤ Cm → ∃ C : ℝ, 1 ≤ C ∧ ∀ C₀ : ℝ, 1 ≤ C₀ →
    ∀ (p N N₁ J k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ),
      PolynomialDimensionIntervalConditions C C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar →
      Cm * k * N₁ * (p : ℝ) ^ G' * c64 p N k n' a cl cStar + 12 * c64 p N k n' a cl cStar ≤
        b' / (k * (p : ℝ) ^ G' * Y)
end Formalism.CountingSumsFrames


