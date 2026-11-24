-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_IntegralParts_QuasiOrbits_ModulusSquares_WtI
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_IntegralParts_QuasiOrbits_ModulusSquares_WtI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:53.495308+00:00
-- url     : https://prove2.me/theorems/0cc65892-de33-42f0-b896-2622d02206e1
-- title:
--   Wt I
-- statement:
--   Definitions and structural lemmas for Wt I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/IntegralParts/QuasiOrbits/ModulusSquares/WtI.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_LaurentCoeffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
namespace PositivityTheory.RgUd.TP.Nil.Orb.Mod
open PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
variable {k : Type} [Field k] {n : ℕ}
end PositivityTheory.RgUd.TP.Nil.Orb.Mod


