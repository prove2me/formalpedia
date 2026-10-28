-- Prove2me | Definitions.Def_RetroCorr_Separation_TwoWay
-- name    : RetroCorr_Separation_TwoWay
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:30.54307+00:00
-- url     : https://prove2.me/theorems/0e2271a9-86b9-47a7-8628-a87964649efd
-- title:
--   Introduction, p. 1 — quantum capacity Q₂ assisted by two-way classical communication: adaptive protocols, codes with exact channel-use count, achievable rates
-- statement:
--   The **quantum capacity assisted by two-way classical communication**, $Q_2$, of a channel $\mathcal N=(\mathcal N_k)_k$ with a classical output $k\sim\mu$ (as in the definition of the one-shot Holevo capacity).
--
--   **Adaptive protocols.** Alice (sender) and Bob (receiver) hold finite-dimensional quantum memories $\mathbb C^a$ and $\mathbb C^b$ and share no entanglement at the start. A protocol with exactly $n$ channel uses is built from the following steps, in any order and any number:
--
--   1. *Local instrument of Alice* (resp. Bob): a complete family of Kraus operators $E_i:\mathbb C^a\to\mathbb C^h$ (resp. on Bob's memory), $\sum_iE_i^\dagger E_i=I$, applied to her (his) memory, which may change dimension (ancillas, discarding). The outcome $i$ is announced over the free classical channel and the rest of the protocol may depend on it; the branches are summed.
--   2. *Channel use*: Alice designates a register of her memory as the channel input; it goes through $\mathcal N_k$ with a fresh $k\sim\mu$, independent of all earlier uses. Bob receives the quantum output, and the classical output $k$ is announced to both parties; the rest of the protocol may depend on $k$, and the final output is averaged over $k$. Nothing done before the use depends on its $k$.
--   3. *Finish* (after exactly $n$ uses): Bob applies a quantum channel to his memory to produce the output on $m$ qubits; Alice's memory is discarded.
--
--   A **two-way code** for $m$ qubits with $n$ channel uses consists of a quantum channel encoding the $m$-qubit message into Alice's memory, Bob's memory starting one-dimensional, and an adaptive protocol with exactly $n$ uses. Its output for message $\rho$ is Bob's final state.
--
--   **Achievable rates and capacity.** A rate $R\ge0$ is achievable if for every $\eta>0$ there is $n_0$ such that for every $n\ge n_0$ there is a code with $n$ uses for $m\ge Rn$ qubits whose fidelity $\langle\psi|\,\mathrm{out}(|\psi\rangle\langle\psi|)\,|\psi\rangle$ is at least $1-\eta$ for every pure message $\psi$. Then
--   $$Q_2(\mathcal N)=\sup\{R\ge0: R\text{ achievable}\}\in[0,\infty],$$
--   in qubits per channel use.
--
--   This is the standard operational capacity named in the paper's Introduction; it is the quantity that Fig. 2's protocol lower-bounds.
--
--   **Formalization Note** `Adaptive μ N m run` is an inductive predicate on the map `run` from the joint memory state (Alice `Fin a` first, Bob `Fin b` second) to Bob's output on `QAlgorithms.Qubits m`, indexed by the number `n` of channel uses. A channel use relabels Alice's memory by a bijection `Fin a ≃ Fin a' × I` and Bob's new memory by `Fin b' ≃ O × Fin b`, both chosen by the protocol (`sendVia`); the average over the flag is a Bochner integral of matrices against `μ`. A protocol whose output is not integrable in `k` gets the integral $0$, which can only lower its fidelity, so this default cannot raise $Q_2$. Outcomes of instruments and flags are public, which is equivalent to free two-way classical communication. Fidelity uses `QAlgorithms.effectProb (pureDensity ψ)` and pure states `QAlgorithms.IsState ψ`. The "for all large $n$, $m\ge Rn$" form of achievability is the textbook one; it is at least as strict as any "some $(m,n)$ with $m/n>R$" variant, and both give the same supremum. The capacity is an `sSup` in `ℝ≥0∞`.
-- source:
--   Bennett, Devetak, Shor & Smolin, Inequalities and separations among assisted capacities of quantum channels, arXiv:quant-ph/0406086v1, p. 1, Introduction (Q₂); p. 3, Fig. 2 (two-way protocol)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel

namespace RetroCorr.Separation

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise

/-- One branch of a local Kraus instrument of Alice (first memory factor), Bob's memory
untouched: `X ↦ (E ⊗ I) X (E ⊗ I)†`. -/
def aliceBranch {a b h : ℕ} (E : Matrix (Fin h) (Fin a) ℂ) :
    QAlgorithms.Superop (Fin a × Fin b) (Fin h × Fin b) :=
  QAlgorithms.conjSuperop (Matrix.kronecker E (1 : Matrix (Fin b) (Fin b) ℂ))

/-- One branch of a local Kraus instrument of Bob (second memory factor), Alice's memory
untouched: `X ↦ (I ⊗ E) X (I ⊗ E)†`. -/
def bobBranch {a b h : ℕ} (E : Matrix (Fin h) (Fin b) ℂ) :
    QAlgorithms.Superop (Fin a × Fin b) (Fin a × Fin h) :=
  QAlgorithms.conjSuperop (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) E)

/-- One channel use: Alice's memory `Fin a` is split by her choice of bijection
`e : Fin a ≃ Fin a' × I` into a kept part `Fin a'` and the channel input `I`; the input goes
through the superoperator `Φ`, whose output `O` joins Bob's memory, which becomes `Fin b'` via
`f : Fin b' ≃ O × Fin b`. Off-diagonal blocks are kept, so entanglement with both memories is
preserved: this is `id_{A'} ⊗ Φ ⊗ id_B` up to the two relabellings. -/
def sendVia {I O : Type*} {a a' b b' : ℕ} (e : Fin a ≃ Fin a' × I) (f : Fin b' ≃ O × Fin b)
    (Φ : QAlgorithms.Superop I O) :
    QAlgorithms.Superop (Fin a × Fin b) (Fin a' × Fin b') :=
  fun X p q =>
    Φ (Matrix.of fun i i' => X (e.symm (p.1, i), (f p.2).2) (e.symm (q.1, i'), (f q.2).2))
      (f p.2).1 (f q.2).1

/-- Introduction, p. 1, and Fig. 2, p. 3: adaptive protocols of Alice and Bob that use the
channel `N` (with classical output `k ∼ μ`) exactly `n` times, assisted by unlimited local
operations and free two-way classical communication, and no prior entanglement. The protocol's
state is an operator on Alice's memory `Fin a` times Bob's memory `Fin b`; the predicate holds
of the map from that state to Bob's final `m`-qubit output.
* `finish`: Bob applies a channel `D` to his memory; Alice's memory is discarded.
* `alice` / `bob`: a party applies a complete Kraus instrument (ancillas and discarding
  included through the dimensions); its outcome `i` is announced and the rest of the protocol
  may depend on it.
* `send`: a register of Alice's memory goes through the channel; Bob receives the quantum
  output, and the classical output `k` (drawn from `μ` independently at every use) is announced
  to both parties; the rest of the protocol may depend on `k`, and the outcome is averaged
  over `k`. Nothing before the use depends on its `k`. -/
inductive Adaptive {K : Type*} [MeasurableSpace K] (μ : Measure K)
    {I O : Type*} [Fintype I] [Fintype O] (N : K → QAlgorithms.Superop I O) (m : ℕ) :
    {n a b : ℕ} → QAlgorithms.Superop (Fin a × Fin b) (QAlgorithms.Qubits m) → Prop
  | finish {a b : ℕ} (D : QAlgorithms.Superop (Fin b) (QAlgorithms.Qubits m))
      (hD : QAlgorithms.IsChannel D) :
      Adaptive μ N m (n := 0) (a := a) (b := b) (fun X => D (QAlgorithms.traceLeft X))
  | alice {n a b h r : ℕ} (E : Fin r → Matrix (Fin h) (Fin a) ℂ)
      (complete : QAlgorithms.IsKrausFamily E)
      (next : Fin r → QAlgorithms.Superop (Fin h × Fin b) (QAlgorithms.Qubits m))
      (valid : ∀ i, Adaptive μ N m (n := n) (next i)) :
      Adaptive μ N m (n := n) (fun X => ∑ i, next i (aliceBranch (b := b) (E i) X))
  | bob {n a b h r : ℕ} (E : Fin r → Matrix (Fin h) (Fin b) ℂ)
      (complete : QAlgorithms.IsKrausFamily E)
      (next : Fin r → QAlgorithms.Superop (Fin a × Fin h) (QAlgorithms.Qubits m))
      (valid : ∀ i, Adaptive μ N m (n := n) (next i)) :
      Adaptive μ N m (n := n) (fun X => ∑ i, next i (bobBranch (a := a) (E i) X))
  | send {n a a' b b' : ℕ} (e : Fin a ≃ Fin a' × I) (f : Fin b' ≃ O × Fin b)
      (next : K → QAlgorithms.Superop (Fin a' × Fin b') (QAlgorithms.Qubits m))
      (valid : ∀ k, Adaptive μ N m (n := n) (next k)) :
      Adaptive μ N m (n := n + 1)
        (fun X => ∫ k, next k (sendVia e f (N k) X) ∂μ)

/-- A two-way assisted quantum code for `m` qubits using the channel `n` times: Alice encodes
the message with a channel into her memory `Fin memory`; Bob's memory starts one-dimensional
(no prior entanglement); then an `Adaptive` protocol with exactly `n` channel uses runs. -/
structure TwoWayCode {K : Type*} [MeasurableSpace K] (μ : Measure K)
    {I O : Type*} [Fintype I] [Fintype O] (N : K → QAlgorithms.Superop I O) (n m : ℕ) where
  memory : ℕ
  encode : QAlgorithms.Superop (QAlgorithms.Qubits m) (Fin memory)
  encode_channel : QAlgorithms.IsChannel encode
  run : QAlgorithms.Superop (Fin memory × Fin 1) (QAlgorithms.Qubits m)
  valid : Adaptive μ N m (n := n) run

/-- The state Bob holds at the end of the code, for the message state `ρ`. -/
def TwoWayCode.output {K : Type*} [MeasurableSpace K] {μ : Measure K}
    {I O : Type*} [Fintype I] [Fintype O] {N : K → QAlgorithms.Superop I O} {n m : ℕ}
    (P : TwoWayCode μ N n m) (ρ : Matrix (QAlgorithms.Qubits m) (QAlgorithms.Qubits m) ℂ) :
    Matrix (QAlgorithms.Qubits m) (QAlgorithms.Qubits m) ℂ :=
  P.run (Matrix.kronecker (P.encode ρ) (1 : Matrix (Fin 1) (Fin 1) ℂ))

/-- `R ≥ 0` qubits per channel use are achievable with two-way classical communication: for
every `η > 0` and every sufficiently large number `n` of channel uses there is a code for
`m ≥ R n` qubits whose fidelity `⟨ψ|output(|ψ⟩⟨ψ|)|ψ⟩` is at least `1 − η` for every pure
message state `ψ`. -/
def TwoWayAchievable {K : Type*} [MeasurableSpace K] (μ : Measure K)
    {I O : Type*} [Fintype I] [Fintype O] (N : K → QAlgorithms.Superop I O) (R : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ m : ℕ, R * n ≤ m ∧
    ∃ P : TwoWayCode μ N n m, ∀ ψ : EuclideanSpace ℂ (QAlgorithms.Qubits m),
      QAlgorithms.IsState ψ →
        1 - η ≤ QAlgorithms.effectProb (QAlgorithms.pureDensity ψ)
          (P.output (QAlgorithms.pureDensity ψ))

/-- Introduction, p. 1: the quantum capacity `Q₂` assisted by two-way classical communication,
in qubits per channel use: the supremum of the achievable rates, in `[0, ∞]`. -/
def twoWayQuantumCapacity {K : Type*} [MeasurableSpace K] (μ : Measure K)
    {I O : Type*} [Fintype I] [Fintype O] (N : K → QAlgorithms.Superop I O) : ENNReal :=
  sSup {q | ∃ R : ℝ, 0 ≤ R ∧ TwoWayAchievable μ N R ∧ q = ENNReal.ofReal R}

end

end RetroCorr.Separation


