-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatticeBasisPolynomial
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatticeBasisPolynomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:59.086806+00:00
-- url     : https://prove2.me/theorems/e3c60c44-1c75-4d22-b6dd-1fb2f2b5a343
-- title:
--   Lattice Basis Polynomial
-- statement:
--   Definitions and structural lemmas for Lattice Basis Polynomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatticeBasisPolynomial.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
namespace LatticeBasis
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end LatticeBasis
end Formalism.InvariantFactorPaths.PW


