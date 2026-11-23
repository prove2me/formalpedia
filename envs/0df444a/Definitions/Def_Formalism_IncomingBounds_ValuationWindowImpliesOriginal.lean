-- Prove2me | Definitions.Def_Formalism_IncomingBounds_ValuationWindowImpliesOriginal
-- name    : Formalism_IncomingBounds_ValuationWindowImpliesOriginal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:52.944823+00:00
-- url     : https://prove2.me/theorems/12667da7-be9c-4b1f-a883-870bf000a5dd
-- title:
--   Valuation Window Implies Original
-- statement:
--   Definitions and structural lemmas for Valuation Window Implies Original, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/ValuationWindowImpliesOriginal.lean

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.IncomingBounds
def ValuationWindowBound : Prop :=
  ∃ C0 : ℝ, ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (i : ℕ), Odd i → ∀ (n n0 : ℕ), 1 ≤ n → n0 ≤ n →
    ∀ h1 : MvPowerSeries (PVar n0) C, MvPowerSeries.constantCoeff h1 = 0 →
      WeightCond v l i n0 h1 →
      ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧
        (y : ℝ) < Y0 + C0 * (n : ℝ) ^ 2 * ((i : ℝ) + Real.log ((n : ℝ) + 1)) ∧
        v (LamP C l i n0 h1 y) ≤
          ((((n0 : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) + n * (Real.logb l n + 1)) : ℝ) :
            WithTop ℝ)
def ValuationWindowOfCayley : Prop := CayleyId → ValuationWindowBound
def ValuationWindowImpliesOriginal : Prop := ValuationWindowBound → ThmP
end Formalism.IncomingBounds


