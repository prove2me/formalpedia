-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_GaloisClause
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_GaloisClause
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:43.230233+00:00
-- url     : https://prove2.me/theorems/d3624468-faec-44ac-ac73-771a14d25a4e
-- title:
--   Galois Clause
-- statement:
--   Definitions and structural lemmas for Galois Clause, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/GaloisClause.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
namespace PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end PI.GreenLabelMapW


