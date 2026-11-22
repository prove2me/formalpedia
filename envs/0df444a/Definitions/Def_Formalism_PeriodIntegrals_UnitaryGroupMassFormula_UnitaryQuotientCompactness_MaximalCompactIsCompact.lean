-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:30.234011+00:00
-- url     : https://prove2.me/theorems/bd8a6e58-621c-42ee-96ff-59a7611d4df0
-- title:
--   Maximal Compact Is Compact
-- statement:
--   Definitions and structural lemmas for Maximal Compact Is Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
namespace PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU
def hσ (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i
def hs (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1
end PI.QuotSetU.UnitaryGroupMassFormula
end


