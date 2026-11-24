-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:24.135003+00:00
-- url     : https://prove2.me/theorems/beea30f8-9ba9-4e2a-96f3-f26106f27666
-- title:
--   Fischer Adjointness Holds
-- statement:
--   Definitions and structural lemmas for Fischer Adjointness Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean

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
section fockForm
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end fockForm
section divided
variable {K A : Type} [Field K] [CharZero K] [CommRing A] [Algebra K A]
end divided
section glDivided
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end glDivided
end Formalism.InvariantFactorPaths.PW


