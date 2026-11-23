-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_BordInv
-- name    : Formalism_PeriodIntegrals_BordInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:45:09.323193+00:00
-- url     : https://prove2.me/theorems/bd237250-94a9-4e2c-92f6-5e887ec16355
-- title:
--   Bord Inv
-- statement:
--   Definitions and structural lemmas for Bord Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/BordInv.lean

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
def BordInv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ),
  inWb k r z → inWb k r z' → ∀ g, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
    omG k r z z' (n * g * n') = omG k r z z' g ∧ omG' k r z z' (n * g * n') = omG' k r z z' g
end PI


