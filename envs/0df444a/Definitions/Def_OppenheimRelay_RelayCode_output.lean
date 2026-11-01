-- Prove2me | Definitions.Def_OppenheimRelay_RelayCode_output
-- name    : OppenheimRelay_RelayCode_output
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:29:40.687812+00:00
-- url     : https://prove2.me/theorems/5b53e5ae-4939-4379-b8b8-20274a96f2bc
-- title:
--   Output state of a relay code
-- statement:
--   For a relay code and a vector $\psi$ on the relay source, the output state is
--   $$
--   (\mathrm{id}_{R^n}\otimes\mathcal{N})(\rho_{\text{initial}}),
--   $$
--   where $\mathcal N$ is the whole relay protocol (`relayApply`) and $\rho_{\text{initial}}$ the initial state. The identity acts on the reference, and every block of the density matrix, including the blocks off the diagonal in $R^n$, is kept.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.2, protocol steps 1–3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_RelayCode_relayApply
import Definitions.Def_OppenheimRelay_RelayCode_initial

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **The output state.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.2, protocol steps 1–3: the relay protocol applied to the
initial state, with the identity on `R^n` ("R" is a reference, on which no party acts; every
block of the density matrix, including the off-diagonal ones, is kept). -/
noncomputable def RelayCode.output {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B]
    [Fintype R] {n : ℕ} (P : RelayCode A C B n) (psi : EuclideanSpace ℂ (RelaySource A C B R)) :
    Matrix
      (Copies R n × ((Qubits P.lAC × ((Copies C n × Qubits P.lAC) × Qubits P.lCB)) ×
        ((Copies A n × Copies B n) × Qubits P.lCB)))
      (Copies R n × ((Qubits P.lAC × ((Copies C n × Qubits P.lAC) × Qubits P.lCB)) ×
        ((Copies A n × Copies B n) × Qubits P.lCB))) ℂ :=
  idTensorSuperop P.relayApply (P.initial psi)

end OppenheimRelay


