-- Prove2me | Definitions.Def_GapAgnosticGS_OracleCircuit_unitary
-- name    : GapAgnosticGS_OracleCircuit_unitary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:35.011038+00:00
-- url     : https://prove2.me/theorems/e759eaa4-2749-404f-8426-afd237ecfac3
-- title:
--   Operator of an oracle circuit for a given oracle
-- statement:
--   The operator of a $T$-query oracle circuit with oracle $U$ is
--
--   $$V_T\,O_{T-1}\,V_{T-1}\cdots V_1\,O_0\,V_0 ,$$
--
--   where $O_i$ is the controlled $U$ or the controlled $U^\dagger$ according to the circuit's $i$-th flag. Only the $O_i$ depend on the oracle.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.5, p.10 (PDF p.11); proof of Theorem 3.15, p.15 (PDF p.16): "|Ψ_{t+1}⟩ = V_t O |Ψ_t⟩"

import Definitions.Def_GapAgnosticGS_OracleCircuit
import Definitions.Def_GapAgnosticGS_OracleCircuit_queryGate
import Definitions.Def_QAlgorithms_Defs_Basic

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.5, p.10 (PDF p.11); proof of Theorem 3.15, p.15 (PDF p.16):
"|Ψ_{t+1}⟩ = V_t O |Ψ_t⟩". The operator of the circuit `circ` with oracle `U`:
`V_T · O_{T−1} · V_{T−1} ⋯ V_1 · O_0 · V_0`, where `O_i` is the controlled `U` or the controlled
`U†` according to `circ.adj i`. -/
noncomputable def OracleCircuit.unitary {Z P : Type} [Fintype Z] [DecidableEq Z] [Fintype P]
    [DecidableEq P] {T : ℕ} (circ : OracleCircuit Z P T) (U : Matrix Z Z ℂ) :
    Matrix (Z × Bool × P) (Z × Bool × P) ℂ :=
  QAlgorithms.orderedProd (fun i : Fin T =>
      circ.V i.succ * OracleCircuit.queryGate (P := P) (if circ.adj i then U.conjTranspose else U)) *
    circ.V 0

end GapAgnosticGS


