-- Prove2me | Definitions.Def_QLocalCert_DQMA1
-- name    : QLocalCert_DQMA1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:02.972932+00:00
-- url     : https://prove2.me/theorems/93357948-72dc-4f05-ab53-2f4814cef742
-- title:
--   One-round dQMA protocol, its acceptance probability, and correctness for a graph property
-- statement:
--   A **one-round dQMA protocol** on $n$-node networks with identifier bound $U$ (Definition 7, in the precise one-round form of Definition 18) fixes a number $c$ of certificate qubits per node, a number $k$ of kept qubits and a number $q$ of qubits per message, and, for each local view (identifier $i$, degree $d$):
--   1. an isometry $V_{i,d}:\mathbb C^{2^c}\to\mathbb C^{2^k}\otimes(\mathbb C^{2^q})^{\otimes d}$ producing a kept part and one outgoing message per port;
--   2. an effect $0\preceq E_{i,d}\preceq I$ on $\mathbb C^{2^k}\otimes(\mathbb C^{2^q})^{\otimes d}$ (the kept part and the messages received on the $d$ ports).
--
--   The prover supplies an arbitrary state $\rho$ on $\bigotimes_v\mathbb C^{2^c}$, possibly entangled across nodes. Every node $v$ applies $V_v=V_{\mathrm{id}(v),\deg v}$; the message sent by $v$ on port $p$ is delivered to the neighbour $u$ behind that port, on the port of $u$ leading back to $v$ (a permutation $W$ of registers); then every node measures $\{E_v,I-E_v\}$. The acceptance probability is
--   $$
--   \Pr[\mathrm{Acc}\mid I,\rho]=\operatorname{tr}\Big[\Big(\bigotimes_vE_v\Big)\,W\Big(\bigotimes_vV_v\Big)\rho\Big(\bigotimes_vV_v\Big)^\dagger W^\dagger\Big].
--   $$
--   The protocol decides a property $L$ with completeness $c$ and soundness error $s$ if for every instance $I$: $G\in L$ implies $\Pr[\mathrm{Acc}\mid I,\rho]\ge c$ for some density operator $\rho$, and $G\notin L$ implies $\Pr[\mathrm{Acc}\mid I,\rho]\le s$ for every density operator $\rho$.
--
--   **Formalization Note** The local operations of a node depend only on its identifier and degree ($n$, $U$ and the problem parameters are fixed with the protocol), so nodes do not see the topology. Uniform register sizes are padding, as on p.16. Isometries followed by one two-outcome measurement are fully general one-round local operations (Stinespring dilation; private coins are ancillas; measured classical fields controlling routing are controlled isometries). Density operators are `WildeQIT.IsDensityOperator`.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Definition 7, pp.15–16; Definition 18, p.32

import Mathlib
import Definitions.Def_QLocalCert_piKron
import Definitions.Def_QLocalCert_Instance
import Definitions.Def_WildeQIT_IsDensityOperator

open scoped ComplexOrder
set_option autoImplicit false

namespace QLocalCert

open Matrix

/-- A one-round dQMA protocol (distributed quantum Merlin–Arthur) on `n`-node networks with
identifier bound `U`.

B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Definition 7, pp.15–16, in the precise
one-round form of Definition 18, p.32: "1. The prover prepares an arbitrary pure state ξ on
⊗_{j=0}^r H_j, where H_j has c(v_j) qubits, and node v_j receives H_j. 2. Simultaneously, each
node applies an isometry to its register, producing a kept part and outgoing message registers,
and sends each message to the corresponding neighbour … 3. Each node measures its kept part
together with its incoming messages with a two-outcome POVM (accept/reject)."

Definition 7 (p.16): "The nodes may perform arbitrary local quantum operations, including
measurements, and exchange quantum messages. Classical fields are allowed as qubits in the
computational basis … verification can be viewed as a µ-round (classical or quantum) LOCAL
algorithm with private randomness and no prior shared entanglement beyond the supplied quantum
certificates."

**Formalization Note.**
* `cert` is the number of certificate qubits of every node (the certificate size, p.16), `keep`
  the number of kept qubits, `msg` the number of qubits of every directed-edge message (the message
  size). Uniform sizes are padding, as on p.16 ("reserve a fixed maximum register budget").
* The local operations of node `v` depend only on its local view: its identifier `id v` and its
  degree `deg v` (`n`, `U` and the problem parameters are fixed with the protocol). A node of
  degree `d` applies the isometry `iso (id v) d : ℂ^{2^cert} → ℂ^{2^keep} ⊗ (ℂ^{2^msg})^{⊗ d}`,
  sending the `p`-th message register through its port `p`, and then measures the two-outcome POVM
  `{eff (id v) d, I − eff (id v) d}` (accept on `eff`) on its kept part and the messages received
  on its ports `0, …, d − 1`.
* Isometries followed by a two-outcome measurement are fully general one-round local operations:
  any local channel or instrument has a Stinespring isometry, private coins are ancillas, and
  measured classical fields controlling routing are controlled isometries. -/
structure DQMA1 (n U : ℕ) where
  /-- Certificate qubits per node. -/
  cert : ℕ
  /-- Kept qubits per node. -/
  keep : ℕ
  /-- Qubits per directed-edge message. -/
  msg : ℕ
  /-- The isometry of a node with identifier `i` and degree `d`. -/
  iso : Fin U → (d : ℕ) → Matrix (Qb keep × (Fin d → Qb msg)) (Qb cert) ℂ
  /-- It is an isometry: `V†V = I`. -/
  iso_isometry : ∀ i d, (iso i d)ᴴ * iso i d = 1
  /-- The accepting effect of a node with identifier `i` and degree `d`. -/
  eff : Fin U → (d : ℕ) → Matrix (Qb keep × (Fin d → Qb msg)) (Qb keep × (Fin d → Qb msg)) ℂ
  /-- `0 ⪯ E`. -/
  eff_nonneg : ∀ i d, (eff i d).PosSemidef
  /-- `E ⪯ I`. -/
  eff_le_one : ∀ i d, (1 - eff i d).PosSemidef

namespace DQMA1

variable {n U : ℕ} (P : DQMA1 n U) (I : Instance n U)

/-- The joint space after the isometries: at every node, its kept part and one message register
per port. -/
abbrev Global := ∀ v : Fin n, Qb P.keep × (Fin (I.deg v) → Qb P.msg)

/-- Message delivery, on basis configurations. If `x` lists, at every node, its kept part and the
messages it sends on each of its ports, then `recv I x` lists, at every node `u`, its kept part
and on each port `p` the message received there: the message that `v := I.port u p` sent on its
port `I.backPort u p`, the port of `v` leading to `u`. This is a bijection of configurations. -/
def recv (x : P.Global I) : P.Global I :=
  fun u => ((x u).1, fun p => (x (I.port u p)).2 (I.backPort u p))

/-- `Pr[Acc | I, ρ]`: the probability that every node accepts when the prover's joint certificate
is the density operator `ρ` on `⊗_v ℂ^{2^cert}` (arbitrarily entangled across the nodes):
`tr[(⊗_v E_v) · W (⊗_v V_v) ρ (⊗_v V_v)† W†]`, with `W` the delivery permutation `recv`. -/
noncomputable def acceptProb (ρ : Matrix (Fin n → Qb P.cert) (Fin n → Qb P.cert) ℂ) : ℝ :=
  let V : Matrix (P.Global I) (Fin n → Qb P.cert) ℂ := piKron fun v => P.iso (I.id v) (I.deg v)
  let E : Matrix (P.Global I) (P.Global I) ℂ := piKron fun v => P.eff (I.id v) (I.deg v)
  (trace (E.submatrix (P.recv I) (P.recv I) * (V * ρ * Vᴴ))).re

/-- Definition 7, p.16: the protocol decides the property `L` with completeness `c` and soundness
error `s`: for every instance (every connected graph, identifier and port assignment),
`I ∈ L ⟹ ∃Γ : Pr[Acc | I, Γ] ≥ c` and `I ∉ L ⟹ ∀Γ : Pr[Acc | I, Γ] ≤ s`, where `Γ` ranges over
all density operators on the joint certificate space. -/
def Correct (L : SimpleGraph (Fin n) → Prop) (c s : ℝ) : Prop :=
  ∀ I : Instance n U,
    (L I.G → ∃ ρ, WildeQIT.IsDensityOperator ρ ∧ c ≤ P.acceptProb I ρ) ∧
    (¬ L I.G → ∀ ρ, WildeQIT.IsDensityOperator ρ → P.acceptProb I ρ ≤ s)

end DQMA1

end QLocalCert


