-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientSigmaFiniteness_SigmaFiniteOfWeil
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientSigmaFiniteness_SigmaFiniteOfWeil
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:41.086046+00:00
-- url     : https://prove2.me/theorems/877efa6b-0e87-55e6-ae9d-0db7bfc1ef7d
-- title:
--   Sigma Finite Of Weil
-- statement:
--   Definitions and structural lemmas for Sigma Finite Of Weil, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientSigmaFiniteness/SigmaFiniteOfWeil.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotNuSigma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
namespace PI.UnitaryGroupMassFormula.QuotNuSigma
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
end PI.UnitaryGroupMassFormula.QuotNuSigma


