-- Prove2me | Definitions.Def_Formalism_RankGapBounds_CloudMinFalse
-- name    : Formalism_RankGapBounds_CloudMinFalse
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:41.895341+00:00
-- url     : https://prove2.me/theorems/193b459a-7273-4501-8e51-02472e349149
-- title:
--   Cloud Min False
-- statement:
--   Definitions and structural lemmas for Cloud Min False, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/CloudMinFalse.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.RankGapBounds.JumpSetsAlt
open Finset
def maxVal (l n : ℕ) : ℕ := (Finset.range (n + 1)).sup fun i => (Nat.choose n i).factorization l
def posPairs (N : ℕ) : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 < p.2
def eExp {N : ℕ} (U : Fin N → ℤ) (l : ℕ) : ℕ :=
  ∑ p ∈ posPairs N, maxVal l (U p.1 - U p.2 - 1).toNat
def SummandLeLog : Prop :=
  ∀ l n : ℕ, l.Prime → maxVal l n ≤ Nat.log l (n + 1)
def SummandZero : Prop :=
  ∀ l n : ℕ, l.Prime → n + 1 < l → maxVal l n = 0
def CloudLog : Prop :=
  ∀ (l k : ℕ) (U : Fin k → ℤ) (xm xp : ℤ), l.Prime → StrictAnti U →
    (∀ a, xm ≤ U a ∧ U a ≤ xp) →
    eExp U l ≤ k ^ 2 * Nat.log l ((xp - xm).toNat + k)
def CloudZero : Prop :=
  ∀ (l k : ℕ) (U : Fin k → ℤ) (xm xp : ℤ), l.Prime → StrictAnti U →
    (∀ a, xm ≤ U a ∧ U a ≤ xp) → (xp - xm).toNat + k < l →
    eExp U l = 0
def RestZero : Prop :=
  ∀ (l N : ℕ) (U : Fin N → ℤ) (lo : ℤ) (w : ℕ), l.Prime → StrictAnti U →
    (∀ a, lo ≤ U a ∧ U a ≤ lo + w) → w + N < l →
    eExp U l = 0
def RestLog : Prop :=
  ∀ (l N h : ℕ) (U : Fin N → ℤ), l.Prime → StrictAnti U →
    (∀ a, 0 ≤ U a ∧ U a ≤ h) →
    eExp U l ≤ N ^ 2 * Nat.log l (2 * h + N)
def CloudMinFalse : Prop :=
  ¬ ∀ (l k : ℕ) (U : Fin k → ℤ) (xm xp : ℤ), l.Prime → StrictAnti U →
    (∀ a, xm ≤ U a ∧ U a ≤ xp) →
    (eExp U l : ℝ) ≤ min ((k : ℝ) ^ 2 * (Nat.log l ((xp - xm).toNat + k) : ℝ))
                         ((k : ℝ) * (((xp - xm).toNat : ℝ) + k) / ((l : ℝ) - 1))
def witnessU : Fin 10 → ℤ := ![114, 113, 112, 111, 110, 4, 3, 2, 1, 0]
def WitnessBig : Prop := 25 ≤ eExp witnessU 101
end Formalism.RankGapBounds.JumpSetsAlt


