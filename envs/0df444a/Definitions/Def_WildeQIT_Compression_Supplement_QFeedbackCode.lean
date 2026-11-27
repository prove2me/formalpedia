-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_QFeedbackCode
-- name    : WildeQIT_Compression_Supplement_QFeedbackCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:01:59.719114+00:00
-- url     : https://prove2.me/theorems/0aec1ac4-d205-5528-81b4-a2cbef0027b4
-- title:
--   Protocol for classical communication with quantum feedback (Figure 21.4)
-- statement:
--   A **protocol for classical communication with quantum feedback** over $n$ uses of a channel $\mathcal N_{A\to B}$, with message set $\mathcal M$, is the most general protocol of Figure 21.4: a noiseless quantum channel of arbitrarily large dimension carries systems from Bob to Alice before every channel use. It consists of
--
--   1. a state $\rho^m_{A'_0}$ of Alice's memory, correlated with the message $m$;
--   2. a state of Bob's systems $X_0B'_1$; Bob sends $X_0$ to Alice through the feedback channel;
--   3. encoders $\mathcal E^i_{A'_{i-1}X_{i-1}\to A'_iA_i}$ of Alice, $i=1,\dots,n$; the system $A_i$ is sent through the $i$-th use of $\mathcal N$;
--   4. decoders $\mathcal D^i_{B_iB'_i\to X_iB'_{i+1}}$ of Bob, $i=1,\dots,n-1$, whose output $X_i$ is fed back to Alice;
--   5. a final measurement $\{\Lambda_m\}$ of Bob's systems $B_nB'_n$, giving his estimate $M'$.
--
--   The protocol needs no prior shared entanglement: the feedback channel can create it.
--
--   **Formalization Note** All memories of one party share one finite dimension, and so do the feedback systems; a protocol with round-dependent dimensions embeds isometrically into one of the maximal dimension. Encoders and decoders are published `WildeQIT.QChannel`s indexed by the round $i\in\mathbb N$ (only rounds $i<n$ are used). Bob's last decoder and the readout of $M'$ form the final POVM. The message enters only through $\rho^m_{A'_0}$, as in Figure 21.4; message-dependent encoders are the case in which $A'_0$ holds a copy of $m$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 21.5.2, pp. 605–606, Figure 21.4

import Mathlib
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QMemory_IsPOVM

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, proof of Theorem 21.5.2,
pp. 605–606, and Figure 21.4 (the most general protocol for classical communication with a
quantum feedback channel).
-/

namespace WildeQIT.Compression.Supplement

/-- **Protocol for classical communication with quantum feedback** over `n` uses of a channel
`N_{A→B}` with `k` messages (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, pp. 605–606, Figure 21.4): "free access to a quantum feedback channel" is "a
noiseless quantum channel of arbitrarily large dimension connecting the receiver Bob to the sender
Alice". "Alice preparing a classical register `M` with a uniformly random message to be sent, which
is correlated with some system `A′₀`. Bob uses the quantum feedback channel to send a quantum
system `X₀` to Alice, which is correlated with some quantum system `B′₁`. Alice performs an
encoding `E¹_{A′₀X₀→A′₁A₁}`. Alice sends system `A₁` through the first use of the channel `N`. Bob
now applies the decoding channel `D¹_{B₁B′₁→X₁B′₂}`. The next encoder of Alice occurs, and the
procedure repeats." At the end Bob measures his systems `BₙB′ₙ` to obtain his estimate `M′`.

Fields: the dimensions of Alice's memory `A′ᵢ`, Bob's memory `B′ᵢ` and the feedback systems `Xᵢ`;
the state `ρᵐ_{A′₀}` correlated with message `m`; Bob's initial state on `X₀B′₁`; the encoders
`enc i = E^{i+1}_{A′ᵢXᵢ→A′_{i+1}A_{i+1}}`; the decoders `dec i = D^{i+1}_{B_{i+1}B′_{i+1}→X_{i+1}B′_{i+2}}`;
and Bob's final measurement, a POVM `{Λ_m}` on `BₙB′ₙ`.

**Formalization Note.** All memories of one party have one common finite dimension, and so do the
feedback systems: a protocol with round-dependent dimensions embeds isometrically into one with
the maximal dimension in every round, so nothing is lost. Encoders and decoders are arbitrary
quantum channels in the published Kraus form `WildeQIT.QChannel`, indexed by the round
`i : ℕ`; only rounds `i < n` are used (the encoders `enc i`, `i < n`, and the decoders `dec i`,
`i < n − 1`; Bob's last decoder and the readout of `M′` are together the final POVM, which is
general because a channel followed by a measurement is a measurement). The message enters only
through `ρᵐ_{A′₀}`, as in Figure 21.4; encoders that also read `m` are the special case in which
`A′₀` keeps a copy of `m`. -/
structure QFeedbackCode (a b : Type) [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (n k : ℕ) where
  /-- Dimension of Alice's memory systems `A′ᵢ`. -/
  dA : ℕ
  /-- Dimension of Bob's memory systems `B′ᵢ`. -/
  dB : ℕ
  /-- Dimension of the feedback systems `Xᵢ`. -/
  dX : ℕ
  /-- Alice's initial state `ρᵐ_{A′₀}`, correlated with the message `m`. -/
  aliceInit : Fin k → Matrix (Fin dA) (Fin dA) ℂ
  aliceInit_density : ∀ m, IsDensityOperator (aliceInit m)
  /-- Bob's initial state on `X₀B′₁`. -/
  bobInit : Matrix (Fin dX × Fin dB) (Fin dX × Fin dB) ℂ
  bobInit_density : IsDensityOperator bobInit
  /-- Alice's encoder `E^{i+1}_{A′ᵢXᵢ→A′_{i+1}A_{i+1}}` of round `i + 1`. -/
  enc : ℕ → QChannel (Fin dA × Fin dX) (Fin dA × a)
  /-- Bob's decoder `D^{i+1}_{B_{i+1}B′_{i+1}→X_{i+1}B′_{i+2}}` of round `i + 1`. -/
  dec : ℕ → QChannel (b × Fin dB) (Fin dX × Fin dB)
  /-- Bob's final measurement `{Λ_m}` on `BₙB′ₙ`. -/
  meas : Fin k → Matrix (b × Fin dB) (b × Fin dB) ℂ
  meas_povm : WildeQIT.QMemory.IsPOVM meas

end WildeQIT.Compression.Supplement


