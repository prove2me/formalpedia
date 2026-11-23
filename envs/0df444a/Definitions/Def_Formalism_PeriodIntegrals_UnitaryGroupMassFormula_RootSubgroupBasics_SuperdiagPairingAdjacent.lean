-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:35.657649+00:00
-- url     : https://prove2.me/theorems/0cafb3da-eb01-4ccf-a7bc-370dbba1ba98
-- title:
--   Superdiag Pairing Adjacent
-- statement:
--   Definitions and structural lemmas for Superdiag Pairing Adjacent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/SuperdiagPairingAdjacent.lean

import Mathlib
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
namespace PI.AmpRootCommon
variable {n : ℕ}
section Rel
variable {Z u u' : Matrix (Fin n) (Fin n) ℂ} {σ : Fin n → Fin n} {ζ : Fin n → ℂ}
end Rel
section Sum
variable {m : ℕ}
def tau (σ : Fin (m + 1) → Fin (m + 1)) (i : Fin m) : Fin m :=
  if h : (σ i.succ).val + 1 = (σ i.castSucc).val then ⟨(σ i.succ).val, by have := (σ i.castSucc).isLt; omega⟩
  else i
end Sum
end PI.AmpRootCommon


