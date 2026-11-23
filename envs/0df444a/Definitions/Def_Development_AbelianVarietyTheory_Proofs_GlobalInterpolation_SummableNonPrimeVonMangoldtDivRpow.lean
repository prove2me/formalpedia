-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:15.057909+00:00
-- url     : https://prove2.me/theorems/136d2fd7-41b5-4973-8728-50339efb7255
-- title:
--   Summable Non Prime Von Mangoldt Div Rpow
-- statement:
--   Definitions and structural lemmas for Summable Non Prime Von Mangoldt Div Rpow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNonPrimeVonMangoldtDivRpow.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
namespace GlobalTheory.Lin.NonPrimeVonMangoldt
noncomputable def F₀ (n : ℕ) : ℝ := (if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ (3 / 4 : ℝ)
noncomputable def F₁ (pk : Nat.Primes × ℕ) : ℝ := F₀ (pk.1 ^ (pk.2 + 1))
noncomputable def F₂ : Nat.Primes × ℕ → ℝ := F₁ ∘ (Prod.map _root_.id (· + 1))
end GlobalTheory.Lin.NonPrimeVonMangoldt


