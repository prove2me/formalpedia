-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EqZeroOfPartialSumsNonneg
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EqZeroOfPartialSumsNonneg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:06.542893+00:00
-- url     : https://prove2.me/theorems/be06b0d8-abdf-4fd7-880d-0b8bb74f523f
-- title:
--   Eq Zero Of Partial Sums Nonneg
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Partial Sums Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.Harm
open Finset
def mixedWeight (m : ℕ) {p q : ℕ} (a : Fin p → ℕ) (b : Fin q → ℕ) : Fin m → ℤ := fun k =>
  (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) -
    (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0)
end GlobalTheory.Harm


