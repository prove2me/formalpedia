-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:14:15.438878+00:00
-- url     : https://prove2.me/theorems/bd265bc8-7654-435c-9421-35cb6da50c3f
-- title:
--   Unipotent Radical Contracting
-- statement:
--   Definitions and structural lemmas for Unipotent Radical Contracting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnipotentRadicalContracting.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
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
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
def fexp (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then (r : ℤ) - i.val else if i.val ≤ r + k then 0 else (r : ℤ) + k - i.val
def dS (k r : ℕ) (s : ℝ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  diagonal fun i => ((s : ℂ)) ^ (fexp k r i)
end PI.QuotSetU.UnitaryGroupMassFormula.SW


