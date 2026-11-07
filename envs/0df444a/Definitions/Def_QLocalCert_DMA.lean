-- Prove2me | Definitions.Def_QLocalCert_DMA
-- name    : QLocalCert_DMA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:11.104221+00:00
-- url     : https://prove2.me/theorems/c8e2632d-8fda-4824-b16b-f6ed62532833
-- title:
--   $\mu$-round dMA protocol with private and public randomness, its acceptance probability, and correctness
-- statement:
--   A **$\mu$-round dMA protocol** on $n$-node networks with identifier bound $U$ (Definition 7) consists of arbitrary sets of states and messages, a law $\pi$ of private random samples and a law $\varpi$ of public random samples, and local rules:
--   1. the initial state of node $v$ is a function of its identifier, its degree, its certificate $z_v\in\{0,1\}^{*}$, its private sample $\omega_v$ and the public sample $\varrho$;
--   2. in each of $\mu$ synchronous rounds, every node computes from its state one message per port, sends them, and then updates its state from the messages received on its ports (the message arriving on port $p$ of $v$ is the one the neighbour behind that port sent on its port leading back to $v$);
--   3. after $\mu$ rounds every node outputs accept or reject.
--
--   The private samples are independent with law $\pi$; the public sample $\varrho\sim\varpi$ is drawn after the certificates are fixed and is seen by every node. $\Pr[\mathrm{Acc}\mid I,\Gamma]$ is the probability that all nodes accept. With certificates of at most $b$ bits, the protocol decides $L$ with completeness $c$ and soundness error $s$ if for every instance $I$: $G\in L$ implies $\Pr[\mathrm{Acc}\mid I,\Gamma]\ge c$ for some assignment $\Gamma$ of certificates of at most $b$ bits, and $G\notin L$ implies $\Pr[\mathrm{Acc}\mid I,\Gamma]\le s$ for every such $\Gamma$. A protocol is **deterministic** if its initial states do not depend on the samples.
--
--   **Formalization Note** States, messages and sample spaces are arbitrary types (local computation and message sizes are unrestricted). Allowing a public sample and arbitrary laws is the generalization the paper claims for its lower bounds (p.16); private fair coins are a special case. Certificates are `List Bool`; the count on p.43 includes the empty string.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Definition 7, pp.15–16; Lemma 27, p.37 (deterministic)

import Mathlib
import Definitions.Def_QLocalCert_Instance

set_option autoImplicit false

namespace QLocalCert

/-- A `μ`-round dMA protocol (distributed Merlin–Arthur, classical certificates and randomized
classical verifiers) on `n`-node networks with identifier bound `U`.

B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Definition 7, pp.15–16: "In a classical
protocol (dMA), Merlin supplies a classical certificate z_v to each node v. The nodes perform
randomized classical computation and exchange classical messages. … After receiving their
certificates, the nodes execute µ synchronous communication rounds along the edges of G, with no
further interaction with Merlin. In each round, every node prepares and sends its outgoing messages
before receiving the messages sent to it in that round, and may then perform local computation. …
Local computation, local workspace, and message sizes are unrestricted. … Our classical lower
bounds also hold when the verifiers additionally share public randomness, sampled after the
certificates have been supplied. At the end of verification, each node outputs accept or reject,
and the network accepts if and only if every node accepts."

**Formalization Note.**
* A certificate is a bit string `List Bool`; certificates of size at most `b` are those of length
  at most `b` (the counting on p.43 includes the empty string).
* The initial state of node `v` is computed from its local view: identifier `id v`, degree `deg v`,
  certificate, its private random sample and the public random sample (`n`, `U`, `μ` are fixed
  with the protocol). Private samples are independent and identically distributed with law
  `privDist`; the public sample has law `pubDist` and is seen by every node. Arbitrary laws and
  the public sample are a generalization the paper claims for its lower bounds (p.16); a protocol
  with private fair coins only is the special case of a trivial public sample.
* In each round a node of degree `d` computes from its state one message per port (`send`),
  then updates its state from the messages received on its ports (`update`). States and messages
  have arbitrary types: local computation and message size are unrestricted. After `μ` rounds each
  node outputs `output state`; `true` is accept. -/
structure DMA (n U μ : ℕ) where
  /-- Local states. -/
  State : Type
  /-- Messages. -/
  Msg : Type
  /-- Private random samples. -/
  PrivRand : Type
  /-- Public random samples. -/
  PubRand : Type
  /-- Law of each node's private sample. -/
  privDist : PMF PrivRand
  /-- Law of the shared public sample. -/
  pubDist : PMF PubRand
  /-- Initial state from (identifier, degree, certificate, private sample, public sample). -/
  init : Fin U → ℕ → List Bool → PrivRand → PubRand → State
  /-- The message sent on each port, from the current state and the degree. -/
  send : State → (d : ℕ) → Fin d → Msg
  /-- The state update from the messages received on each port. -/
  update : State → (d : ℕ) → (Fin d → Msg) → State
  /-- The final decision (`true` = accept). -/
  output : State → Bool

namespace DMA

variable {n U μ : ℕ} (P : DMA n U μ) (I : Instance n U)

/-- The state of every node after `k` rounds, on instance `I`, with certificates `Γ`, private
samples `ω` and public sample `ϱ`. In round `k + 1` node `v` receives on its port `p` the message
that `u := I.port v p` sent on its port leading back to `v`. -/
def state (Γ : Fin n → List Bool) (ω : Fin n → P.PrivRand) (ϱ : P.PubRand) :
    ℕ → Fin n → P.State
  | 0, v => P.init (I.id v) (I.deg v) (Γ v) (ω v) ϱ
  | k + 1, v => P.update (state Γ ω ϱ k v) (I.deg v)
      (fun p => P.send (state Γ ω ϱ k (I.port v p)) (I.deg (I.port v p)) (I.backPort v p))

/-- The event `Acc`: after `μ` rounds every node accepts. -/
def Accepts (Γ : Fin n → List Bool) (ω : Fin n → P.PrivRand) (ϱ : P.PubRand) : Prop :=
  ∀ v, P.output (P.state I Γ ω ϱ μ v) = true

open Classical in
/-- `Pr[Acc | I, Γ]`, over the public sample `ϱ ∼ pubDist` and independent private samples
`ω_v ∼ privDist`, one per node. -/
noncomputable def acceptProb (Γ : Fin n → List Bool) : ℝ :=
  (∑' ϱ : P.PubRand, ∑' ω : Fin n → P.PrivRand,
    P.pubDist ϱ * (∏ v, P.privDist (ω v)) * (if P.Accepts I Γ ω ϱ then 1 else 0)).toReal

/-- Definition 7, p.16: with certificates of at most `b` bits per node, the protocol decides the
property `L` with completeness `c` and soundness error `s`: for every instance (every connected
graph, identifier and port assignment), `I ∈ L ⟹ ∃Γ : Pr[Acc | I, Γ] ≥ c` and
`I ∉ L ⟹ ∀Γ : Pr[Acc | I, Γ] ≤ s`, `Γ` ranging over certificate assignments of at most `b` bits
per node. -/
def Correct (L : SimpleGraph (Fin n) → Prop) (b : ℕ) (c s : ℝ) : Prop :=
  ∀ I : Instance n U,
    (L I.G → ∃ Γ : Fin n → List Bool, (∀ v, (Γ v).length ≤ b) ∧ c ≤ P.acceptProb I Γ) ∧
    (¬ L I.G → ∀ Γ : Fin n → List Bool, (∀ v, (Γ v).length ≤ b) → P.acceptProb I Γ ≤ s)

/-- The protocol is deterministic: initial states, and hence the whole execution, do not depend on
the random samples (Lemma 27, p.37, "deterministic one-round dMA protocol"). -/
def IsDeterministic : Prop :=
  ∀ i d z ω ω' ϱ ϱ', P.init i d z ω ϱ = P.init i d z ω' ϱ'

end DMA

end QLocalCert


