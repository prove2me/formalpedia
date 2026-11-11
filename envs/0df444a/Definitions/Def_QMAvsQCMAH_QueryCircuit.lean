-- Prove2me | Definitions.Def_QMAvsQCMAH_QueryCircuit
-- name    : QMAvsQCMAH_QueryCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:19:28.309554+00:00
-- url     : https://prove2.me/theorems/dfd61713-348e-4d78-a992-3ee8392f56ac
-- title:
--   Quantum oracle algorithms as linear maps
-- statement:
--   A **quantum oracle algorithm with $T$ queries** acting on a register is a unitary, followed by $T$ rounds of an oracle call $|u\rangle|b\rangle|w\rangle\mapsto|u\rangle|b\oplus\mathcal O(u)\rangle|w\rangle$ and a unitary. Unlike a verifier it has no fixed initial state; it denotes a linear map on the register. A round whose query register is in the non-querying state makes no query, so $T$ rounds mean at most $T$ queries.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 6, p.23

import Definitions.Def_BBBV_RandomOracle_QueryModel

set_option autoImplicit false

namespace QMAvsQCMAH

/-- A **quantum oracle algorithm with `T` queries** acting on a register: a first unitary `U0`,
then `T` rounds of "query, then unitary `U i`", on the configuration space
`Option X × R × W` of the public query model (query register, answer register, workspace).
Its action on an input state is `apply`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 6, p.23 (PDF p.26): "There is a quantum oracle algorithm using at most 2h queries
that implements |z⟩|b⟩ ↦ |z⟩|b ⊕ T^O(z)⟩ exactly, including on coherent inputs. Its local
computation and description may be unrestricted."

**Formalization Note.** Unlike `BBBV.RandomOracle.QueryAlg` it has no fixed initial state, so it
denotes a linear map; a query with the query register in the non-querying value is the
identity, so `T` slots mean "at most `T` queries". -/
structure QueryCircuit (X R W : Type) [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    [Fintype W] [DecidableEq W] (T : ℕ) where
  /-- the unitary before the first query -/
  U0 : BBBV.RandomOracle.State X R W ≃ₗᵢ[ℂ] BBBV.RandomOracle.State X R W
  /-- the unitary after query `i` -/
  U : Fin T → (BBBV.RandomOracle.State X R W ≃ₗᵢ[ℂ] BBBV.RandomOracle.State X R W)

/-- The output state of the algorithm on input state `ψ` with oracle `f`:
`U_{T−1} O_f ⋯ U_0 O_f U0 ψ`. -/
noncomputable def QueryCircuit.apply {X R W : Type} [Fintype X] [DecidableEq X] [Fintype R]
    [DecidableEq R] [AddGroup R] [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryCircuit X R W T) (f : X → R) (ψ : BBBV.RandomOracle.State X R W) :
    BBBV.RandomOracle.State X R W :=
  (List.finRange T).foldl (fun φ i => A.U i (BBBV.RandomOracle.oracleOp f φ)) (A.U0 ψ)

end QMAvsQCMAH


