-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivComm
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivComm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:10:14.232457+00:00
-- url     : https://prove2.me/theorems/6255edb0-01e4-44e7-994c-5e08b95b841c
-- title:
--   Pderiv Comm
-- statement:
--   Definitions and structural lemmas for Pderiv Comm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivComm.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.LC.FK
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
def sw (k : Fin m × Fin n × Bool) : Fin m × Fin n × Bool := (k.1, k.2.1, !k.2.2)
end PositivityTheory.Rg.Sw.LC.FK
namespace PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC.FK
end PositivityTheory.Rg.Sw.LC


