-- Prove2me | Definitions.Def_QCSepTotal_QProtocol
-- name    : QCSepTotal_QProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:33:18.223928+00:00
-- url     : https://prove2.me/theorems/46be5d3d-1652-4c2c-a5c3-bed67c4b68de
-- title:
--   $r$-message quantum protocols without prior entanglement and $Q_r(F)\le q$
-- statement:
--   An **$r$-message quantum protocol** for inputs $X\times Y$ acts on $W$ qubits, all starting in the state $|0\cdots0\rangle$, which is a product state, so there is no prior entanglement. Each qubit is held by Alice or by Bob at each time. Messages alternate between the parties; message $t$ moves some qubits from its sender to the receiver, and its cost is the number of qubits moved. Before each message, and once after the last one, each party applies a unitary that depends only on its own input and acts only on the qubits it holds at that time. At the end, the **last receiver** measures one of its qubits in the computational basis and outputs the result.
--
--   The **cost** of the protocol is the total number of qubits sent. We write $Q_r(F)\le q$ when $F$ has a quantum protocol with **at most** $r$ messages, cost at most $q$, and error at most $1/3$ on every input in $\mathrm{dom}(F)$.
--
--   The upper bound $Q_{r+1}(F_{\mathrm{tot}})=\tilde O(q)$ of Theorems 1.4 and 3.2 is stated in this model.
--
--   **Formalization Note** This is the standard model of Yao and Kremer. The party that is not sending may also apply a local unitary at each step; this changes nothing, since that unitary acts only on qubits the party keeps and can be postponed to its next turn. Private randomness and intermediate measurements are simulated by unitaries on ancilla qubits (deferred measurement), so omitting them does not weaken the model.
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), pp.1 and 5 (quantum complexities $Q(f)$, $Q_r(f)$: no prior entanglement, last receiver outputs, cost in qubits)

import Mathlib
import Definitions.Def_QCSepTotal_PartialFn

open Matrix

namespace QCSepTotal

/-- The sender of message `t` (`t = 0, 1, …`) when messages alternate and Alice sends first iff
`aliceFirst` (`true` = Alice). -/
def sender (aliceFirst : Bool) (t : ℕ) : Bool :=
  if t % 2 = 0 then aliceFirst else !aliceFirst

/-- An **`r`-message quantum communication protocol without prior entanglement** (F. Le Gall,
*Improved Separations between Quantum and Classical Communication Complexity of Total Functions*,
arXiv:2609.16726, held version sha256 970e1476…, pp.1, 5: "The quantum complexities `Q(f)` and
`Q_r(f)` allow no prior entanglement. In an `r`-message quantum protocol, the last receiver
produces the output.").

The protocol acts on `W` qubits, whose computational basis states are `σ : Fin W → Bool`.
* `owner t q` says who holds qubit `q` (`true` = Alice) before message `t` (`t < r`), and
  `owner r q` after the last message.
* Messages alternate, message `t` being sent by `sender aliceFirst t`; message `t` moves qubits
  from its sender to the receiver only (`transfer`), and its cost is the number of qubits moved.
* At each time `t ≤ r` Alice applies a unitary `uA t x`, depending only on her input `x`, to the
  qubits she holds at time `t`, and Bob a unitary `uB t y` to the qubits he holds; their joint
  action is `uA t x ⊗ uB t y`.
* All qubits start in `|0…0⟩`, a product state: there is no prior entanglement.
* At the end the last receiver measures its qubit `out` in the computational basis and outputs
  the outcome.

**Formalization Note.** This is the standard (Yao/Kremer) model. Letting the party that is not
sending also apply a local unitary at each step changes nothing: that unitary acts only on qubits
the party keeps, so it can be postponed to the party's next turn, and at the end it does not
affect the measured qubit. Private randomness and intermediate measurements are simulated
unitarily on ancilla qubits (deferred measurement), so the model is not weakened by omitting
them. -/
structure QProtocol (X Y : Type) (r : ℕ) where
  /-- number of qubits -/
  W : ℕ
  /-- whether Alice sends message `0` -/
  aliceFirst : Bool
  /-- `owner t q = true` iff Alice holds qubit `q` before message `t` (after the last if `t = r`) -/
  owner : Fin (r + 1) → Fin W → Bool
  /-- message `t` only moves qubits from its sender to the receiver -/
  transfer : ∀ (t : Fin r) (q : Fin W), owner t.castSucc q ≠ owner t.succ q →
    owner t.castSucc q = sender aliceFirst t
  /-- the measured output qubit -/
  out : Fin W
  /-- the output qubit is held by the last receiver -/
  out_owner : owner (Fin.last r) out = !(sender aliceFirst (r - 1))
  /-- Alice's unitary at time `t` on the qubits she holds then -/
  uA : (t : Fin (r + 1)) → X → Matrix.unitaryGroup ({q : Fin W // owner t q = true} → Bool) ℂ
  /-- Bob's unitary at time `t` on the qubits he holds then -/
  uB : (t : Fin (r + 1)) → Y → Matrix.unitaryGroup ({q : Fin W // owner t q = false} → Bool) ℂ

namespace QProtocol

variable {X Y : Type} {r : ℕ}

/-- The joint operation `uA t x ⊗ uB t y` at time `t`, as a matrix on the computational basis
of all `W` qubits. -/
noncomputable def stepOp (P : QProtocol X Y r) (x : X) (y : Y) (t : Fin (r + 1)) :
    Matrix (Fin P.W → Bool) (Fin P.W → Bool) ℂ :=
  fun σ σ' =>
    (P.uA t x : Matrix ({q : Fin P.W // P.owner t q = true} → Bool)
        ({q : Fin P.W // P.owner t q = true} → Bool) ℂ) (fun q => σ q.1) (fun q => σ' q.1) *
      (P.uB t y : Matrix ({q : Fin P.W // P.owner t q = false} → Bool)
        ({q : Fin P.W // P.owner t q = false} → Bool) ℂ) (fun q => σ q.1) (fun q => σ' q.1)

/-- The final state: start from `|0…0⟩` and apply the operations of times `0, 1, …, r` in
order (messages only change who holds which qubit). -/
noncomputable def finalState (P : QProtocol X Y r) (x : X) (y : Y) : (Fin P.W → Bool) → ℂ :=
  (List.finRange (r + 1)).foldl (fun ψ t => P.stepOp x y t *ᵥ ψ) (Pi.single (fun _ => false) 1)

/-- The probability that the protocol outputs `1` on `(x, y)`: the squared norm of the part of
the final state in which the output qubit is `1`. -/
noncomputable def acceptProb (P : QProtocol X Y r) (x : X) (y : Y) : ℝ :=
  ∑ σ : Fin P.W → Bool, if σ P.out then ‖P.finalState x y σ‖ ^ 2 else 0

/-- The probability that the output differs from `b`. -/
noncomputable def errQ (P : QProtocol X Y r) (x : X) (y : Y) (b : Bool) : ℝ :=
  if b then 1 - P.acceptProb x y else P.acceptProb x y

/-- The **cost** of the protocol: the total number of qubits sent, over all `r` messages. The
model is oblivious, so this is also its worst-case cost. -/
def cost (P : QProtocol X Y r) : ℕ :=
  ∑ t : Fin r, (Finset.univ.filter fun q => P.owner t.castSucc q ≠ P.owner t.succ q).card

end QProtocol

/-- `Q_r(F) ≤ q` (pp.1, 5): `F` has a quantum protocol with **at most `r` messages**, at least
one, of cost at most `q` qubits, and error at most `1/3` on every promised input. -/
def HasQProtocol {X Y : Type} (F : PartialFn X Y) (r q : ℕ) : Prop :=
  ∃ r' : ℕ, 1 ≤ r' ∧ r' ≤ r ∧ ∃ P : QProtocol X Y r', P.cost ≤ q ∧
    ∀ x y b, F x y = some b → P.errQ x y b ≤ 1 / 3

end QCSepTotal


