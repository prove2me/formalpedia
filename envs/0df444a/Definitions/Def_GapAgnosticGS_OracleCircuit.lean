-- Prove2me | Definitions.Def_GapAgnosticGS_OracleCircuit
-- name    : GapAgnosticGS_OracleCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:29.0509+00:00
-- url     : https://prove2.me/theorems/77a65137-2ce7-4f1f-aa72-c242a0e62132
-- title:
--   Fixed-length oracle circuit with controlled $U$/$U^\dagger$ queries
-- statement:
--   A **$T$-query oracle circuit** on the register $Z\otimes\mathbb C^2\otimes\mathbb C^P$ (oracle register, query-control qubit, workspace) consists of oracle-independent unitaries $V_0,\dots,V_T$ and, for each of the $T$ queries, a flag saying whether it applies the controlled oracle or its controlled adjoint. It models a unitary "constructed using $T$ queries to $E$ and $E^\dagger$" (Lemma 3.5) and the purified $T$-query algorithm of the hybrid argument in the proof of Theorem 3.15.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.5, p.10 (PDF p.11); proof of Theorem 3.15, p.15 (PDF p.16): "V_t the algorithm's oracle-independent unitary between the t-th and (t+1)-th queries"

import Mathlib

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.5, p.10 (PDF p.11): "There is a unitary GTT(η, a; τ) … which can be constructed
using O((1/η) log(1/a)) queries to E and E†"; proof of Theorem 3.15, p.15 (PDF p.16): "V_t the
algorithm's oracle-independent unitary between the t-th and (t+1)-th queries". A fixed-length
oracle circuit with `T` queries on the register `Z × Bool × P` (oracle register `Z`, query-control
qubit, workspace `P`): oracle-free unitaries `V 0, …, V T` and, for each query, a flag saying
whether it uses the oracle (`false`) or its adjoint (`true`). Its unitary is
`OracleCircuit.unitary`. -/
structure OracleCircuit (Z P : Type) [Fintype Z] [DecidableEq Z] [Fintype P] [DecidableEq P]
    (T : ℕ) where
  V : Fin (T + 1) → Matrix (Z × Bool × P) (Z × Bool × P) ℂ
  V_unitary : ∀ i, V i ∈ Matrix.unitaryGroup (Z × Bool × P) ℂ
  adj : Fin T → Bool

end GapAgnosticGS


