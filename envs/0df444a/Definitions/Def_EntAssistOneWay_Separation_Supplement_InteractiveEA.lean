-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_Supplement_InteractiveEA
-- name    : EntAssistOneWay_Separation_Supplement_InteractiveEA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:49:03.51721+00:00
-- url     : https://prove2.me/theorems/15710fd9-e164-4198-a6e2-dbbbe24deb3d
-- title:
--   Interactive entanglement-assisted protocols with an arbitrary shared state
-- statement:
--   An **interactive entanglement-assisted protocol** with $C$ bits of classical communication is specified as follows. Alice and Bob share a quantum state $\rho$, an arbitrary density matrix on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ (positive semidefinite, trace one), fixed before the inputs $x\in X$ (Alice) and $y\in Y$ (Bob) are revealed.
--
--   The bits are produced one at a time. Before bit $j$ is sent ($0\le j<C$), the prefix $t_{<j}$ of the transcript determines the speaker. The speaker, depending on its own input and on $t_{<j}$, applies a two-outcome **quantum instrument** to its own register: two completely positive maps $\mathcal E_0,\mathcal E_1$ in Kraus form, $\mathcal E_b(\sigma)=\sum_{i=1}^m K_{b,i}\sigma K_{b,i}^\dagger$, with $\sum_{b,i}K_{b,i}^\dagger K_{b,i}=I$. The outcome is the bit sent, and the post-measurement state is carried to the next round. After $C$ bits, a party determined by the full transcript $t$ measures a binary effect $0\preceq E\preceq I$ on its register, chosen from its input and $t$; this outcome is the protocol's output.
--
--   Writing $\sigma_t$ for the unnormalized joint state after all $C$ branches of $t$ have been applied (each branch tensored with the identity on the other register), the acceptance probability is
--
--   $$\Pr[\text{output }1\mid x,y]=\sum_{t\in\{0,1\}^C}\operatorname{Re}\operatorname{tr}\big((E_t\otimes I)\,\sigma_t\big)\quad\text{(or }I\otimes E_t\text{ if Bob outputs).}$$
--
--   This is the model of Theorem 3.4's general clause: entanglement independent of the inputs, local operations depending on input and transcript, classical messages only.
--
--   **Formalization Note** Protocols with shorter transcripts are padded to exactly $C$ bits with trivial instruments; ancillas and private randomness are absorbed into the local dimensions and the instruments. Instruments are the published `KAQROM.Instrument` with Kraus index `Fin m`; the protocol type is parametrised by $m$, and statements quantify over all $m$. At each node only the speaker's instrument is used.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 17, §3.3 (entanglement-assisted model); pp. 17–18, proof of Theorem 3.4

import Definitions.Def_EntAssistOneWay_Separation_POVM
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_KAQROM_Instrument

open scoped BigOperators ComplexOrder Matrix
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation.Supplement

noncomputable section

/-- The two players of a two-party protocol. -/
inductive Party
  | alice
  | bob
  deriving DecidableEq

/-- The first `j` bits of a full transcript of `C` bits. -/
def transcriptPrefix {C : ℕ} (t : Fin C → Bool) (j : ℕ) (h : j ≤ C) : Fin j → Bool :=
  fun i => t (Fin.castLE h i)

/-- §3.3, p. 17: a general interactive entanglement-assisted protocol with `C` bits of
classical communication. The shared state is an arbitrary density matrix on
`ℂ^{dA} ⊗ ℂ^{dB}`, fixed before the inputs. Before bit `j` is sent, the transcript prefix
determines the speaker; the speaker applies a two-outcome quantum instrument (Kraus form,
at most `m` Kraus operators per outcome) on its own register, chosen from its input and the
prefix, and announces the outcome. After `C` bits, a party chosen by the transcript measures
a binary effect on its own register, chosen from its input and the transcript; outcome
`1` means accept. Only the speaker's instrument at each node is ever used. -/
structure InteractiveEAProtocol (X Y : Type) (dA dB m C : ℕ) where
  state : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ
  density : WildeQIT.IsDensityOperator state
  speaker : (j : Fin C) → (Fin j → Bool) → Party
  aliceStep : X → (j : Fin C) → (Fin j → Bool) →
    KAQROM.Instrument Bool (Fin dA) (Fin dA) (Fin m)
  bobStep : Y → (j : Fin C) → (Fin j → Bool) →
    KAQROM.Instrument Bool (Fin dB) (Fin dB) (Fin m)
  outputParty : (Fin C → Bool) → Party
  aliceOutput : X → (Fin C → Bool) → BinaryEffect (Fin dA)
  bobOutput : Y → (Fin C → Bool) → BinaryEffect (Fin dB)

variable {X Y : Type} {dA dB m C : ℕ}

/-- The unnormalized joint state after the first `j` bits of the full transcript `t` have
been produced: each step applies the speaker's outcome branch `σ ↦ ∑ᵢ (Kᵢ ⊗ I) σ (Kᵢ ⊗ I)†`
(or `I ⊗ Kᵢ` for Bob). Its trace is the probability of that prefix. -/
def runState (P : InteractiveEAProtocol X Y dA dB m C) (x : X) (y : Y)
    (t : Fin C → Bool) : (j : ℕ) → j ≤ C → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ
  | 0, _ => P.state
  | j + 1, h =>
    let σ := runState P x y t j (Nat.le_of_succ_le h)
    let k : Fin C := ⟨j, h⟩
    let pre : Fin j → Bool := transcriptPrefix t j (Nat.le_of_succ_le h)
    match P.speaker k pre with
    | .alice => ∑ i, Matrix.kronecker ((P.aliceStep x k pre).kraus (t k) i) 1 * σ *
        (Matrix.kronecker ((P.aliceStep x k pre).kraus (t k) i) 1)ᴴ
    | .bob => ∑ i, Matrix.kronecker 1 ((P.bobStep y k pre).kraus (t k) i) * σ *
        (Matrix.kronecker 1 ((P.bobStep y k pre).kraus (t k) i))ᴴ

/-- The final accepting effect, on the joint register, after the full transcript `t`. -/
def outputEffect (P : InteractiveEAProtocol X Y dA dB m C) (x : X) (y : Y)
    (t : Fin C → Bool) : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ :=
  match P.outputParty t with
  | .alice => Matrix.kronecker (P.aliceOutput x t).op 1
  | .bob => Matrix.kronecker 1 (P.bobOutput y t).op

/-- Acceptance probability: the sum over all full transcripts of
`Re tr(E_t · σ_t)`. -/
def interactiveAccept (P : InteractiveEAProtocol X Y dA dB m C) (x : X) (y : Y) : ℝ :=
  ∑ t : Fin C → Bool, ((outputEffect P x y t * runState P x y t C le_rfl).trace).re

end

end EntAssistOneWay.Separation.Supplement


