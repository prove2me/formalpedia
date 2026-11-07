-- Prove2me | Definitions.Def_ByzSigT_Msg
-- name    : ByzSigT_Msg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:52:49.600441+00:00
-- url     : https://prove2.me/theorems/a88792c1-bf81-4767-8472-9fced5d29443
-- title:
--   The messages of the k-SigT protocol and the syntax of corruption proofs
-- statement:
--   This definition fixes the encoding of the messages of Algorithm 2 as terms: suggest, propose, vote1, vote2, vote3, decided, viewchange, equiv and allgood are classically signed tuples with the fields printed in the algorithm, and a value-SigT is a token on $(\mathrm{value},a,\sigma,J)$. An **input justification** for $a$ from layer $j$ is a tuple holding the party's own allgood/equiv message of layer $j$, its blame, the $n-f$ messages of line 46 and the evidence of lines 52 and 54–65; in layer 1 it is $\bot$, the empty tuple.
--
--   It also fixes the syntax that the analysis reads off messages:
--
--   1. the certificate kinds $V_a$, $V2_a$, $V3_a$ of a view, $\mathrm{SigT}^{(i)}$ and allgood, and the message type each consists of;
--   2. the leader of view $v$, the party with index $v \bmod n$;
--   3. the **corruption proofs**: two messages of $q$ from one layer that are vote1 messages or vote2 messages for different values in the same view, vote3 or value-SigT messages for different values, an allgood message for $a$ and a vote3 or value-SigT message for $b\ne a$, or an allgood and an equiv message;
--   4. the tally winner of line 65: with $S_a=P_a\setminus(P_{1-a}\cup O)$, the value with more remaining signers, ties going to $0$.
--
--   **Formalization Note** A lock $(a,\mathrm{evidence},w)$ stores $w+1$, so that $0$ encodes the input lock of view $-1$. Token index $i$ belongs to layer $i+1$.
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), §4.2, pp.14–18 (PDF 15–19)

import Mathlib
import Definitions.Def_ByzSigT_Term

namespace ByzSigT

/-!
# The messages of the k-SigT protocol and the syntax of corruption proofs

Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…), §4.2, pp.14–17 (PDF 15–18): Algorithm 2 and the
paragraphs "Views and signatures", "Certificates", "Corruption proofs", "Justifications" and the
list of carried justifications on p.16.

**Formalization Note (encoding).**
* Values `0, 1` are `Bool` (`0 = false`), encoded in terms as `bval a = nat 0` or `nat 1`.
  Layers `ℓ ∈ {1, …, k + 1}` and views `v = 0, 1, …` are natural numbers. Layer `ℓ ≤ k` uses the
  token index `ℓ − 1 : Fin k` (`IsTokIdx ℓ i`), i.e. the paper's `SigT^{(ℓ)}`.
* Every message except the value-SigT is a classically signed tuple `sig q (list [nat tag, …])`
  with the fields of Algorithm 2: `⟨suggest, i, lock, v, J_p⟩`, `⟨propose, i, a, L, v, J_p⟩`,
  `⟨vote1, i, a, v, P, J_p⟩`, `⟨vote2, i, V_a, a, v, J_p⟩`, `⟨vote3, i, V2_a, a, v, J_p⟩`,
  `⟨decided, a⟩`, `⟨viewchange, i, v, J_p⟩`, `⟨equiv, i, ownSigT, σ_a, σ_b, J_p⟩`,
  `⟨allgood, i, a, ownSigT, σ, J_p⟩`.
* A value-SigT is the token `tok q i (list [nat 7, bval a, σ, J])`, the paper's
  `SigT^{(i)}(value, a, σ, J_p)` (lines 33, 43); the equiv token (line 38) is
  `tok q i (list [nat 8, σ_a, σ_b, J])`.
* A lock `(a, evidence, w)` is `list [bval a, nat c, evidence]` with `c = w + 1`, so `c = 0` is the
  input lock of view `−1` (Algorithm 2's header) whose evidence is an input justification, and
  `c = w + 1 ≥ 1` a lock whose evidence is a `V_a` certificate of view `w`.
* A certificate is a tuple `list ms` of messages.
* A justification for `a` from layer `j` (an input justification for layer `j + 1`) is
  `list [nat 11, nat j, bval a, nat type, own, blame, list ms, extra]` (`justTerm`): the party's
  own allgood/equiv message of layer `j`, its blame (stored as the evidence that proves its members
  corrupt), the `n − f` messages of line 46, and the evidence and choices of lines 52 and 54–65.
  The input justification `⊥` of layer 1 is `list []`.
* `leader(v)` is the party with index `v mod n` (a fixed round-robin order).
-/

variable {n k : ℕ}

/-- The term encoding a value: `0 ↦ nat 0`, `1 ↦ nat 1` (`false = 0`). -/
def bval (a : Bool) : Term n k := .nat (if a then 1 else 0)

/-- The lock `(a, ev, c − 1)`: value `a`, lock view `c − 1` (`c = 0` is view `−1`), evidence `ev`. -/
def lockTerm (a : Bool) (c : ℕ) (ev : Term n k) : Term n k := .list [bval a, .nat c, ev]

/-- The classically signed message types of Algorithm 2 (layer `ℓ`, view `v`, value `a`). -/
inductive Msg (n k : ℕ) : Type where
  | suggest (ℓ : ℕ) (L : Term n k) (v : ℕ) (J : Term n k) : Msg n k
  | propose (ℓ : ℕ) (a : Bool) (L : Term n k) (v : ℕ) (J : Term n k) : Msg n k
  | vote1 (ℓ : ℕ) (a : Bool) (v : ℕ) (P J : Term n k) : Msg n k
  | vote2 (ℓ : ℕ) (σ : Term n k) (a : Bool) (v : ℕ) (J : Term n k) : Msg n k
  | vote3 (ℓ : ℕ) (σ : Term n k) (a : Bool) (v : ℕ) (J : Term n k) : Msg n k
  | decided (a : Bool) : Msg n k
  | viewchange (ℓ v : ℕ) (J : Term n k) : Msg n k
  | equiv (ℓ : ℕ) (s σa σb J : Term n k) : Msg n k
  | allgood (ℓ : ℕ) (a : Bool) (s σ J : Term n k) : Msg n k

/-- The tuple encoding of a message body. -/
def Msg.body : Msg n k → Term n k
  | .suggest ℓ L v J => .list [.nat 0, .nat ℓ, L, .nat v, J]
  | .propose ℓ a L v J => .list [.nat 1, .nat ℓ, bval a, L, .nat v, J]
  | .vote1 ℓ a v P J => .list [.nat 2, .nat ℓ, bval a, .nat v, P, J]
  | .vote2 ℓ σ a v J => .list [.nat 3, .nat ℓ, σ, bval a, .nat v, J]
  | .vote3 ℓ σ a v J => .list [.nat 4, .nat ℓ, σ, bval a, .nat v, J]
  | .decided a => .list [.nat 5, bval a]
  | .viewchange ℓ v J => .list [.nat 6, .nat ℓ, .nat v, J]
  | .equiv ℓ s σa σb J => .list [.nat 9, .nat ℓ, s, σa, σb, J]
  | .allgood ℓ a s σ J => .list [.nat 10, .nat ℓ, bval a, s, σ, J]

/-- Message `m` signed by `q`. -/
def Msg.signed (q : Fin n) (m : Msg n k) : Term n k := .sig q m.body

/-- The content `(value, a, σ, J)` of a value-SigT. -/
def valueBody (a : Bool) (σ J : Term n k) : Term n k := .list [.nat 7, bval a, σ, J]

/-- The content `(equiv, σ_a, σ_b, J)` of the equiv token of line 38. -/
def equivBody (σa σb J : Term n k) : Term n k := .list [.nat 8, σa, σb, J]

/-- `IsTokIdx ℓ i`: the token index `i` is the one of layer `ℓ` (`SigT^{(ℓ)}`). -/
def IsTokIdx (ℓ : ℕ) (i : Fin k) : Prop := i.val + 1 = ℓ

/-- The value-SigT `SigT^{(i+1)}_q(value, a, σ, J)`. -/
def valueSigT (q : Fin n) (i : Fin k) (a : Bool) (σ J : Term n k) : Term n k :=
  .tok q i (valueBody a σ J)

/-- The three justification types. -/
inductive JType : Type where
  | clean | adopt | tally
  deriving DecidableEq

/-- The code of a justification type in its term encoding. -/
def JType.code : JType → ℕ
  | .clean => 0
  | .adopt => 1
  | .tally => 2

/-- A justification for `a` from layer `j` of type `ty` (see the module note). -/
def justTerm (j : ℕ) (a : Bool) (ty : JType) (own bl : Term n k) (ms : List (Term n k))
    (extra : Term n k) : Term n k :=
  .list [.nat 11, .nat j, bval a, .nat ty.code, own, bl, .list ms, extra]

/-- The input justification `⊥` of layer 1. -/
def botJust : Term n k := .list []

/-- `IsLeader q v`: `q = leader(v)`, round robin by index. -/
def IsLeader (q : Fin n) (v : ℕ) : Prop := q.val = v % n

/-- Certificate kinds: `V_a`, `V2_a`, `V3_a` certificates of view `v`, `SigT^{(i)}` certificates
and allgood certificates. -/
inductive CertKind : Type where
  | V (v : ℕ) | V2 (v : ℕ) | V3 (v : ℕ) | sigT | allgood

/-- `CertMsg κ ℓ a s`: `s` is a message of the kind that a certificate of kind `κ` for `a` of
layer `ℓ` consists of: vote1, vote2 or vote3 messages for `a` of view `v`, value-SigT^{(ℓ)}
messages for `a`, or allgood messages for `a`. -/
def CertMsg (κ : CertKind) (ℓ : ℕ) (a : Bool) (s : Term n k) : Prop :=
  match κ with
  | .V v => ∃ (q : Fin n) (P J : Term n k), s = (Msg.vote1 ℓ a v P J).signed q
  | .V2 v => ∃ (q : Fin n) (σ J : Term n k), s = (Msg.vote2 ℓ σ a v J).signed q
  | .V3 v => ∃ (q : Fin n) (σ J : Term n k), s = (Msg.vote3 ℓ σ a v J).signed q
  | .sigT => ∃ (q : Fin n) (i : Fin k) (σ J : Term n k), IsTokIdx ℓ i ∧ s = valueSigT q i a σ J
  | .allgood => ∃ (q : Fin n) (s' σ J : Term n k), s = (Msg.allgood ℓ a s' σ J).signed q

/-- The signers of a certificate (or of any tuple of messages). -/
def certSigners (σ : Term n k) : Finset (Fin n) :=
  match σ with
  | .list ms => (ms.filterMap Term.signer).toFinset
  | _ => ∅

/-- `s` is a vote1 message whose proposal carries a lock from a view before `v` (its lock code
`c` satisfies `c − 1 < v`). -/
def Vote1LockBefore (s : Term n k) (v : ℕ) : Prop :=
  ∃ (q q' : Fin n) (ℓ ℓ' c w w' : ℕ) (b b' : Bool) (J J' ev : Term n k),
    s = (Msg.vote1 ℓ b w ((Msg.propose ℓ' b' (lockTerm b' c ev) w' J').signed q') J).signed q ∧
      (c : ℤ) - 1 < v

/-- `s` is an allgood message of `q` for `a` of layer `ℓ`. -/
def IsAllgoodOf (q : Fin n) (ℓ : ℕ) (a : Bool) (s : Term n k) : Prop :=
  ∃ s' σ J : Term n k, s = (Msg.allgood ℓ a s' σ J).signed q

/-- `s` is an equiv message of `q` of layer `ℓ`. -/
def IsEquivOf (q : Fin n) (ℓ : ℕ) (s : Term n k) : Prop :=
  ∃ s' σa σb J : Term n k, s = (Msg.equiv ℓ s' σa σb J).signed q

/-- `s` is a value-SigT^{(ℓ)} of `q` for `a`. -/
def IsValueSigTOf (q : Fin n) (ℓ : ℕ) (a : Bool) (s : Term n k) : Prop :=
  ∃ (i : Fin k) (σ J : Term n k), IsTokIdx ℓ i ∧ s = valueSigT q i a σ J

/-- `s` is a vote3 or a value-SigT^{(ℓ)} message of `q` for `a` of layer `ℓ`. -/
def IsV3OrValueOf (q : Fin n) (ℓ : ℕ) (a : Bool) (s : Term n k) : Prop :=
  (∃ (σ J : Term n k) (v : ℕ), s = (Msg.vote3 ℓ σ a v J).signed q) ∨ IsValueSigTOf q ℓ a s

/-- `ProofPair q s s'`: the two messages `s, s'` of `q` from one layer prove `q` corrupt (p.15):
vote1 messages, or vote2 messages, for different values in the same view; vote3 or value-SigT
messages for different values; an allgood message for `a` and a vote3 or value-SigT message for
`b ≠ a`; or an allgood and an equiv message. (Validity of the two messages is required where the
pair is used.) -/
def ProofPair (q : Fin n) (s s' : Term n k) : Prop :=
  ∃ ℓ : ℕ,
    (∃ (v : ℕ) (a b : Bool) (P J P' J' : Term n k), a ≠ b ∧
      s = (Msg.vote1 ℓ a v P J).signed q ∧ s' = (Msg.vote1 ℓ b v P' J').signed q) ∨
    (∃ (v : ℕ) (a b : Bool) (σ J σ' J' : Term n k), a ≠ b ∧
      s = (Msg.vote2 ℓ σ a v J).signed q ∧ s' = (Msg.vote2 ℓ σ' b v J').signed q) ∨
    (∃ a b : Bool, a ≠ b ∧ IsV3OrValueOf q ℓ a s ∧ IsV3OrValueOf q ℓ b s') ∨
    (∃ a b : Bool, a ≠ b ∧ IsAllgoodOf q ℓ a s ∧ IsV3OrValueOf q ℓ b s') ∨
    ((∃ a : Bool, IsAllgoodOf q ℓ a s) ∧ IsEquivOf q ℓ s')

/-- `tallyWinner P₀ P₁ O`: line 65 for `V = {0, 1}`: with `S_a = P_a \ (P_{1−a} ∪ O)`, the value
with more remaining signers, ties broken in favour of `0 = false`. -/
def tallyWinner (P₀ P₁ O : Finset (Fin n)) : Bool :=
  Decidable.decide ((P₀ \ (P₁ ∪ O)).card < (P₁ \ (P₀ ∪ O)).card)

end ByzSigT


