-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowExpansionMinor_FirstColumnSplitBijective
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowExpansionMinor_FirstColumnSplitBijective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:45:17.519971+00:00
-- url     : https://prove2.me/theorems/351d5800-a293-4041-9ecb-b0ac271271c5
-- title:
--   First Column Split Bijective
-- statement:
--   Definitions and structural lemmas for First Column Split Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowExpansionMinor/FirstColumnSplitBijective.lean

import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace PI.QmRowExpWork
open Formalism.REAL
def cyc0 (m : ℕ) (j : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) := (Fin.cycleRange j).symm
def ext0 {m : ℕ} (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  ((finSuccEquiv m).trans (Equiv.optionCongr τ)).trans (finSuccEquiv m).symm
def phi0 (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  cyc0 m p.1 * ext0 p.2
end PI.QmRowExpWork
namespace PI
end PI


