-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_GaussSec
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_GaussSec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:58.842281+00:00
-- url     : https://prove2.me/theorems/3fae9208-2afb-49e4-aa4f-4af18c646e4c
-- title:
--   Gauss Sec
-- statement:
--   Definitions and structural lemmas for Gauss Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/GaussSec.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix PositivityTheory.Rg.Sw
open scoped Matrix ComplexConjugate
namespace PositivityTheory.SiegelWeilFormula.KLI
variable {m n : ℕ}
end PositivityTheory.SiegelWeilFormula.KLI
end


