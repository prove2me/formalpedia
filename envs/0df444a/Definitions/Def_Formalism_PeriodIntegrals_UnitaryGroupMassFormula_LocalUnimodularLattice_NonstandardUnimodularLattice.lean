-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_NonstandardUnimodularLattice
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_NonstandardUnimodularLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:31:13.392814+00:00
-- url     : https://prove2.me/theorems/b58779f7-16a4-48e0-8947-83d7907afd35
-- title:
--   Nonstandard Unimodular Lattice
-- statement:
--   Definitions and structural lemmas for Nonstandard Unimodular Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/NonstandardUnimodularLattice.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ExistsModularFunction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
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
namespace PI.NUnimodLoc.UnitaryGroupMassFormula
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
def NStdUnimod : Prop :=
  ∀ k r : ℕ, ∀ μ : Measure (MtM (2 * r + k + 1)), IsHaarOnM (Nset k r) μ → IsRightInvM (Nset k r) μ
end PI.NUnimodLoc.UnitaryGroupMassFormula


