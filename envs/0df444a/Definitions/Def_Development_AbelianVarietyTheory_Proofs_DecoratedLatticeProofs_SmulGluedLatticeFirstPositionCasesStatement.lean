-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmulGluedLatticeFirstPositionCasesStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmulGluedLatticeFirstPositionCasesStatement
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:58.189474+00:00
-- url     : https://prove2.me/theorems/5e8ca15b-b991-485a-bd75-c0b82bcc651b
-- title:
--   Smul Glued Lattice First Position Cases Statement
-- statement:
--   Definitions and structural lemmas for Smul Glued Lattice First Position Cases Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SmulGluedLatticeFirstPositionCasesStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmulGluedLatticeFirstPositionCases
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiesOnRamOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)


