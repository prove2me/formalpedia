-- Prove2me | Definitions.Def_QMAvsQCIP_qqQueries
-- name    : QMAvsQCIP_qqQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:05.068248+00:00
-- url     : https://prove2.me/theorems/a82acda5-41bc-4710-b51d-b99dae87b5e3
-- title:
--   Number of oracle queries of a query-model verifier
-- statement:
--   The number of oracle queries of a quantum query verifier: the number of query operations over all its rounds. The circuit is fixed, so this bound holds on every oracle and against every prover.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 5, p.17

import Definitions.Def_QMAvsQCIP_QQVerifier

set_option autoImplicit false

namespace QMAvsQCIP

/-- The **number of oracle queries** of a query-model verifier `V`: the number of query
operations over all rounds. The circuit is fixed, so the count is the same on every oracle and
against every prover.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 5, p.17 (PDF p.20): "On every input oracle and against every
prover, V_λ makes at most T(λ) oracle queries". -/
def qqQueries {Z : Type} [Fintype Z] [DecidableEq Z] (V : QQVerifier Z) : ℕ :=
  ∑ j : Fin (V.R + 1), ((V.ops j).filter (fun o => o.isNone)).length

end QMAvsQCIP


