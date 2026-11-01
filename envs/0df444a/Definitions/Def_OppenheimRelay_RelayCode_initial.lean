-- Prove2me | Definitions.Def_OppenheimRelay_RelayCode_initial
-- name    : OppenheimRelay_RelayCode_initial
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:19.471028+00:00
-- url     : https://prove2.me/theorems/0092d97a-b2f5-4f9b-82e5-ec6dcc499975
-- title:
--   Initial state of a relay code
-- statement:
--   For a relay code and a vector $\psi$ on the relay source, the initial state is the pure state
--   $$
--   |\psi\rangle^{\otimes n}_{ABCR}\otimes|\Phi_{k_{AC}}\rangle_{\text{Alice–Charlie}}\otimes|\Phi_{k_{CB}}\rangle_{\text{Charlie–Bob}},
--   $$
--   where $|\Phi_k\rangle = 2^{-k/2}\sum_{x\in\{0,1\}^k}|x\rangle|x\rangle$ is $k$ Bell pairs $|\phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$. Alice holds $A^n$ and her Bell halves, Charlie $C^n$ and his halves of both banks, Bob $B^n$ and his halves; $R^n$ is the reference.
--
--   **Formalization Note** Written as the density matrix $|\cdot\rangle\langle\cdot|$ of this vector, with $R^n$ as the first tensor factor; $|\psi\rangle^{\otimes n}$ is the published `sourceAmplitude`.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, "n copies of state ρABC … a total pure state |ψ⟩ABCR", "shared entanglement in state |φ+⟩ = (|00⟩ + |11⟩)/√2"; p.2, Fig. 1, panel 0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_RelaySource
import Definitions.Def_OppenheimRelay_RelayCode

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **The initial state.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, "n copies of state ρABC … a total pure state |ψ⟩ABCR" and
"shared entanglement in state |φ+⟩ = (|00⟩ + |11⟩)/√2", and p.2, Fig. 1, panel 0: the pure state
`|ψ⟩^⊗n ⊗ Φ_kAC ⊗ Φ_kCB`, where `Φ_k` is `k` Bell pairs (`maxEntangled k`). The amplitude at
`(r, ((a, k₁), ((c, k₂), h₁)), (b, h₂))` is `ψ^⊗n(r, a, c, b) · Φ(k₁, k₂) · Φ(h₁, h₂)`. Alice holds
`a, k₁`, Charlie `c, k₂, h₁`, Bob `b, h₂`. -/
noncomputable def RelayCode.initial {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B]
    [Fintype R] {n : ℕ} (P : RelayCode A C B n) (psi : EuclideanSpace ℂ (RelaySource A C B R)) :
    Matrix
      (Copies R n × (((Copies A n × Qubits P.kAC) ×
        ((Copies C n × Qubits P.kAC) × Qubits P.kCB)) × (Copies B n × Qubits P.kCB)))
      (Copies R n × (((Copies A n × Qubits P.kAC) ×
        ((Copies C n × Qubits P.kAC) × Qubits P.kCB)) × (Copies B n × Qubits P.kCB))) ℂ :=
  pureDensity (WithLp.toLp 2 fun p =>
    sourceAmplitude psi n p.1 p.2.1.1.1 p.2.1.2.1.1 p.2.2.1 *
      maxEntangled P.kAC (p.2.1.1.2, p.2.1.2.1.2) *
      maxEntangled P.kCB (p.2.1.2.2, p.2.2.2))

end OppenheimRelay


