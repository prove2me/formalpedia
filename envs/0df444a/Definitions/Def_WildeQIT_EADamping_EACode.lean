-- Prove2me | Definitions.Def_WildeQIT_EADamping_EACode
-- name    : WildeQIT_EADamping_EACode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:12.117513+00:00
-- url     : https://prove2.me/theorems/b81c4b9a-17c7-4a56-aab9-da0c6ce43f60
-- title:
--   Entanglement-assisted classical code
-- statement:
--   An **entanglement-assisted classical code** with block length $n$ and message set $\mathcal M=\{0,\dots,k-1\}$ for a channel $\mathcal N_{A'\to B}$ consists of
--
--   1. a pure state $\Psi_{T_AT_B}$ shared by Alice ($T_A$) and Bob ($T_B$) before the protocol, in whatever finite-dimensional form they wish;
--   2. for each message $m$, an encoding channel $\mathcal E^m_{T_A\to A'^n}$ that Alice applies to her share;
--   3. a decoding POVM $\{\Lambda^m_{B^nT_B}\}_{m\in\mathcal M}$ that Bob performs on the channel outputs $B^n$ and his share $T_B$.
--
--   The global state after encoding and the $n$ channel uses is $\mathcal N_{A'^n\to B^n}(\mathcal E^m_{T_A\to A'^n}(\Psi_{T_AT_B}))$.
--
--   **Formalization Note** $T_A$ and $T_B$ are indexed by `Fin dA` and `Fin dB` of arbitrary dimension. The encoders are published `WildeQIT.QChannel`s (Kraus form) and the decoder is a published `QAlgorithms.IsPOVM` (positive semidefinite elements summing to the identity).
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §21.1, pp. 589–590, (21.4)–(21.6), Figure 21.1

import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §21.1, pp. 589–590,
(21.4)–(21.9) and Figure 21.1 (an entanglement-assisted classical code).
-/

namespace WildeQIT.EADamping

/-- **Entanglement-assisted classical code** of block length `n` with `k` messages for a channel
with input space `a` and output space `b` (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, §21.1, pp. 589–590): a pure entangled state `Ψ_{T_A T_B}` shared by Alice and
Bob "in whatever form they wish", an encoding channel `E^m_{T_A→A′ⁿ}` for each message
`m ∈ M = {0, …, k − 1}`, and a decoding POVM `{Λ^m_{Bⁿ T_B}}` on the channel outputs `Bⁿ` and Bob's
share `T_B`.

**Formalization Note.** Alice's share `T_A` is `Fin dA` and Bob's share `T_B` is `Fin dB`, both of
arbitrary finite dimension. The encoders are published `WildeQIT.QChannel`s (Kraus form); the
decoder is a published `QAlgorithms.IsPOVM` (positive semidefinite, summing to the identity).
The `n` channel inputs are indexed by `Fin n → a`, the outputs by `Fin n → b`. -/
structure EACode (a b : Type) [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (n k : ℕ) where
  /-- The dimension of Alice's share `T_A` of the entanglement. -/
  dA : ℕ
  /-- The dimension of Bob's share `T_B` of the entanglement. -/
  dB : ℕ
  /-- The shared pure state `|Ψ⟩_{T_A T_B}`. -/
  Ψ : EuclideanSpace ℂ (Fin dA × Fin dB)
  /-- `|Ψ⟩` is a unit vector. -/
  norm_Ψ : ‖Ψ‖ = 1
  /-- The encoding channel `E^m_{T_A→A′ⁿ}` of message `m`. -/
  enc : Fin k → QChannel (Fin dA) (Fin n → a)
  /-- The decoding POVM element `Λ^m_{Bⁿ T_B}` of message `m`. -/
  dec : Fin k → Matrix ((Fin n → b) × Fin dB) ((Fin n → b) × Fin dB) ℂ
  /-- `{Λ^m}` is a POVM. -/
  dec_povm : QAlgorithms.IsPOVM dec

end WildeQIT.EADamping


