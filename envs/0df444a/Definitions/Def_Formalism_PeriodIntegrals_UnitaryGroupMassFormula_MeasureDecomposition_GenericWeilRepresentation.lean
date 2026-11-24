-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_GenericWeilRepresentation
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_GenericWeilRepresentation
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:00:17.637553+00:00
-- url     : https://prove2.me/theorems/5b40dbc7-dbd1-4bad-8f31-702d0e00c07e
-- title:
--   Generic Weil Representation
-- statement:
--   Definitions and structural lemmas for Generic Weil Representation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/GenericWeilRepresentation.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
noncomputable section
namespace PI.ScMuExists.UnitaryGroupMassFormula
section Bruhat
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
end Bruhat
end PI.ScMuExists.UnitaryGroupMassFormula


