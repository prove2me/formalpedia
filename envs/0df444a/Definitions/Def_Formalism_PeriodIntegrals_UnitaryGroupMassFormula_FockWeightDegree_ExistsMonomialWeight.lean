-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:35.417028+00:00
-- url     : https://prove2.me/theorems/ca0b73f4-c0ed-495f-8b73-6e40a45b3809
-- title:
--   Exists Monomial Weight
-- statement:
--   Definitions and structural lemmas for Exists Monomial Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
namespace PI.FockWtDegWork
def lw {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) : ℚ :=
  if linePos l then (α l : ℚ) + 1 / 2 else -(α l : ℚ) - 1 / 2
def W1 {p q r s : ℕ} (a : Ix p q) (α : Ln p q r s →₀ ℕ) : ℚ :=
  ∑ c : Ix r s, lw ((a, c) : Ln p q r s) α
def W2 {p q r s : ℕ} (c : Ix r s) (α : Ln p q r s →₀ ℕ) : ℚ :=
  ∑ a : Ix p q, lw ((a, c) : Ln p q r s) α
end PI.FockWtDegWork


