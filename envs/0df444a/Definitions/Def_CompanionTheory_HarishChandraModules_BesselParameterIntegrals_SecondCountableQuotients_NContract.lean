-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:33:51.658346+00:00
-- url     : https://prove2.me/theorems/ee4ba8a3-a2f2-4e2e-b0a1-8d0913234905
-- title:
--   NContract
-- statement:
--   Definitions and structural lemmas for NContract, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace CompanionTheory.D.Upq.QuotSetU
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
def expo (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then (r : ℤ) - i.val else if i.val ≤ r + k then 0 else -((i.val : ℤ) - r - k)
noncomputable def dvec (t : ℝ) (i : Fin (2 * r + k + 1)) : ℂ := ((t ^ expo k r i : ℝ) : ℂ)
noncomputable def cdiag (k r : ℕ) (t : ℝ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  diagonal (dvec (k := k) (r := r) t)
variable {z : Fin (2 * r + k + 1) → ℂ}
end CompanionTheory.D.Upq.QuotSetU


