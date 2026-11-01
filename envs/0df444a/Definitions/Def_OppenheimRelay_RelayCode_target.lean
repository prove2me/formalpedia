-- Prove2me | Definitions.Def_OppenheimRelay_RelayCode_target
-- name    : OppenheimRelay_RelayCode_target
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:15.761822+00:00
-- url     : https://prove2.me/theorems/734c01dc-4653-4238-bc44-83e5715563b2
-- title:
--   Target state of a relay code
-- statement:
--   For a relay code and a vector $\psi$ on the relay source, the target is the pure state
--   $$
--   |\psi\rangle^{\otimes n}_{ABCR}\otimes|\Phi_{l_{AC}}\rangle_{\text{Alice–Charlie}}\otimes|\Phi_{l_{CB}}\rangle_{\text{Charlie–Bob}}
--   $$
--   with $A^n$ now held by Bob: the source state is unchanged, except that Alice's share has moved to Bob, and the two links share the final numbers of Bell pairs.
--
--   This is the paper's task, "for Alice to transfer $\rho_A$ to Bob while otherwise keeping the overall state $|\psi\rangle^{\otimes n}_{ABCR}$ virtually unchanged", in the relay setting of Fig. 1, panel 3.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, "The task is for Alice to transfer ρA to Bob while otherwise keeping the overall state … virtually unchanged"; p.2, Fig. 1, panel 3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_RelaySource
import Definitions.Def_OppenheimRelay_RelayCode

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **The target state.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, "The task is for Alice to transfer ρA to Bob while otherwise
keeping the overall state |ψ⟩⊗n ABCR virtually unchanged", and p.2, Fig. 1, panel 3: the pure state
`|ψ⟩^⊗n ⊗ Φ_lAC ⊗ Φ_lCB`, with `A^n` now at Bob. The amplitude at
`(r, (l₁, ((c, l₂), h₁)), ((a, b), h₂))` is `ψ^⊗n(r, a, c, b) · Φ(l₁, l₂) · Φ(h₁, h₂)`. Alice holds
`l₁`, Charlie `c, l₂, h₁`, Bob `a, b, h₂`. -/
noncomputable def RelayCode.target {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B]
    [Fintype R] {n : ℕ} (P : RelayCode A C B n) (psi : EuclideanSpace ℂ (RelaySource A C B R)) :
    Matrix
      (Copies R n × ((Qubits P.lAC × ((Copies C n × Qubits P.lAC) × Qubits P.lCB)) ×
        ((Copies A n × Copies B n) × Qubits P.lCB)))
      (Copies R n × ((Qubits P.lAC × ((Copies C n × Qubits P.lAC) × Qubits P.lCB)) ×
        ((Copies A n × Copies B n) × Qubits P.lCB))) ℂ :=
  pureDensity (WithLp.toLp 2 fun p =>
    sourceAmplitude psi n p.1 p.2.2.1.1 p.2.1.2.1.1 p.2.2.1.2 *
      maxEntangled P.lAC (p.2.1.1, p.2.1.2.1.2) *
      maxEntangled P.lCB (p.2.1.2.2, p.2.2.2))

end OppenheimRelay


