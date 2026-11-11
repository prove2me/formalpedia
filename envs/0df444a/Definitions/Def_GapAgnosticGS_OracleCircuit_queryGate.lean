-- Prove2me | Definitions.Def_GapAgnosticGS_OracleCircuit_queryGate
-- name    : GapAgnosticGS_OracleCircuit_queryGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:27.778322+00:00
-- url     : https://prove2.me/theorems/3b147123-6ed7-41f4-ab83-1ea1ad9fc987
-- title:
--   Controlled oracle gate $|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes U$
-- statement:
--   On the register $Z\otimes\mathbb C^2\otimes\mathbb C^P$, the controlled oracle
--
--   $$|0\rangle\langle0|\otimes I_Z\otimes I_P+|1\rangle\langle1|\otimes U\otimes I_P ,$$
--
--   with control the qubit, target the oracle register $Z$, and identity on the workspace. One application is one query.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.1 (PDF p.2): "controlled versions of both; one controlled use … counts as one query"

import Mathlib

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.1 (PDF p.2): "controlled versions of both; one controlled use … counts as one
query". The controlled oracle `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U` on the register `Z × Bool × P`, with the
control the `Bool` factor, the target the oracle register `Z`, and the identity on `P`. -/
def OracleCircuit.queryGate {Z P : Type} [Fintype Z] [DecidableEq Z] [DecidableEq P]
    (U : Matrix Z Z ℂ) : Matrix (Z × Bool × P) (Z × Bool × P) ℂ :=
  Matrix.of fun x x' =>
    if x.2 = x'.2 then (if x.2.1 then U x.1 x'.1 else if x.1 = x'.1 then 1 else 0) else 0

end GapAgnosticGS


