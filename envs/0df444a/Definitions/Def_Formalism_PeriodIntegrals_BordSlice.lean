-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_BordSlice
-- name    : Formalism_PeriodIntegrals_BordSlice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:44:39.524574+00:00
-- url     : https://prove2.me/theorems/3a1bcf30-9139-4a1f-b2fd-f3bc6b807af5
-- title:
--   Bord Slice
-- statement:
--   Definitions and structural lemmas for Bord Slice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/BordSlice.lean

import Definitions.Def_Formalism_PeriodIntegrals_BordDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI
open Formalism.QuantumDeterminants
def BordSlice : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ),
  inWb k r z → inWb k r z' → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μ ∈ UH (Hb k) →
    omG k r z z' (bigCell k r c μ) = omF k r z z' c μ ∧ omG' k r z z' (bigCell k r c μ) = omF' k r z z' c μ
end PI


