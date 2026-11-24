-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:11.641581+00:00
-- url     : https://prove2.me/theorems/9997673d-4961-4a63-8da0-b14f6340d7c7
-- title:
--   Conj Transpose One Kronecker
-- statement:
--   Definitions and structural lemmas for Conj Transpose One Kronecker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
namespace PI.FHS
section Sums
variable {σ : Type*}
end Sums
variable {p q r s : ℕ}
def Mixed (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) : Prop :=
  ∀ l l', M l l' ≠ 0 → linePos l ≠ linePos l'
end PI.FHS


