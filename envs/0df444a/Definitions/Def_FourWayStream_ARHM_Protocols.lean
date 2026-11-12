-- Prove2me | Definitions.Def_FourWayStream_ARHM_Protocols
-- name    : FourWayStream_ARHM_Protocols
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:44:27.13219+00:00
-- url     : https://prove2.me/theorems/2a3bd028-1515-4a88-9b05-a0e68e19d53f
-- title:
--   Definitions 5.8, 6.1, 6.9, Remark 6.2 — one-way protocols with sequential or simultaneous requests, admissible cuts
-- statement:
--   **One-way protocols.** Alice receives $x\in\{0,1\}^N$, Bob receives requests $q_1,\dots,q_s$ (request $q$ names the edge set $\mu(q)$); both see public coins $r$ drawn from a distribution. There is no prior entanglement.
--
--   1. A **quantum protocol with sequential requests** (Definition 6.9, SeqHM): Alice's message is a density matrix on $\mathbb C^d$ depending on $(r,x)$; it has $q$ qubits when $d\le 2^q$ and includes any classical information. Bob applies a channel from the message into a memory of unrestricted dimension, then in round $t$, having received only $q_t$, an instrument whose outcome is his answer $o_t$. Answers are **legal** (Remark 6.2) if on every request naming a perfect matching Bob's answer is an edge of it.
--   2. A **quantum protocol with simultaneous requests** (Definition 6.1, MHM): Bob measures the message with a POVM depending on $r$ and all requests; the outcome is his list of answers.
--   3. A **classical public-coin protocol with sequential requests**: Alice sends one of $M$ symbols ($c$ bits when $M\le 2^c$), Bob updates a randomized state round by round, seeing only $q_t$ in round $t$.
--
--   The joint law of SeqHM$_{N,s}(D)$ draws $X$ uniform, the coins, and the requests i.i.d. from $D$, independently of each other, and Bob's answers from the protocol; so every request is **fresh**. The history $H_{t-1}$ is the coins together with the requests and answers of rounds $1,\dots,t-1$. The error vector is $Z_t=b_t\oplus X_{u_t}\oplus X_{v_t}$.
--
--   **Cuts (Definition 5.8).** A cut of the ARHM stream followed by $s$ requests is given by public randomness $r$ and private randomness $p$ with their distributions, the stream up to the cut as a function of $(r,p,x)$, and the tags of the $s$ requests after the cut as a function of $r$; their factor indices are inputs, independent of $x$ and of the prefix. Nothing is conditioned on the prefix: its outputs are summed over. The cut position is **public** if the prefix length depends on $r$ alone. For a streaming algorithm one obtains the conditional law of its answers to the $s$ requests given $(r,x)$ and the indices, and, for Proposition 5.13, the probability that all $s$ answers are correct when $X$ is uniform and the indices are independent uniform factors.
--
--   **Formalization Note** Coins are indexed by `Fin nR`, private randomness by `Fin nP`; probabilities are real parts of traces of compositions of `QAlgorithms.krausApply`, or `QAlgorithms.effectProb` of a POVM element.
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §4.3, pp.16–17; Definition 5.8, p.22; Definition 6.1 and Remark 6.2, p.28; information budget (1), p.29; Definition 6.9, pp.30–31

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information

set_option autoImplicit false

/-!
# One-way protocols with several requests, admissible cuts

Nadezhda Voronova, *Four Ways to Stream*, STOC 2027 submission #1371 (October 2026): §4.3
(pp.16–17), Definition 5.8 (p.22), Definitions 6.1, 6.9 and Remark 6.2 (pp.28–31), the information
budget (1) (p.29).

Alice gets `x ∈ {0,1}^N` and public coins `r` (drawn from `coin`); Bob gets public coins and his
requests `q_1, …, q_s ∈ Q`, request `q` naming the matching `μ q`. The answer to a request is an
`Output N`; it is correct if it is an edge of `μ q` with the parity of `x` on it.

* `QSeqProtocol`: a quantum one-way protocol with sequential requests (Definition 6.9, p.30): Alice's
  message is a density matrix on `C^d` (it includes any classical information, §4.3); Bob first applies
  a channel from the message into his memory `C^e` (unrestricted `e`), then in round `t`, having
  received only `q_t`, an instrument whose output is his answer `o_t`. Requests are fresh: the joint law
  draws them independently of everything else, and round `t` sees only `q_t`.
* `SimProtocol`: a quantum one-way protocol for simultaneous requests (Multiple Hidden Matching,
  Definition 6.1, p.28): Bob measures the message with a POVM chosen from `r` and all requests.
* `CSeqProtocol`: a classical public-coin one-way protocol with sequential requests; the message is
  one of `M` symbols (`c` bits when `M ≤ 2^c`).
-/

noncomputable section
open Classical

namespace FourWayStream.ARHM

open QAlgorithms
open scoped Matrix

/-- Remark 6.2 (p.28): the answer `o` to a request naming `M` is legal if it is an edge of `M`
(with some bit). -/
def IsLegal {N : ℕ} (M : Finset (Sym2 (Fin N))) (o : Output N) : Prop :=
  ∃ e b, o = some (e, b) ∧ e ∈ M

/-- The edges `{e_i : i ∈ T}` of the answers in the rounds `T` (a missing answer has no edge). -/
def selEdges {N s : ℕ} (o : Fin s → Output N) (T : Finset (Fin s)) : Finset (Sym2 (Fin N)) :=
  T.biUnion
    (fun i => match o i with
      | some (e, _) => {e}
      | none => ∅)

/-- The set `E_t = {e_i : i < t}` of the edges of the first `t` answers (0-based rounds). -/
def outEdges {N s : ℕ} (o : Fin s → Output N) (t : ℕ) : Finset (Sym2 (Fin N)) :=
  selEdges o (Finset.univ.filter (fun i : Fin s => i.val < t))

/-- §6.4.1 (p.31): the error vector `Z_t = b_t ⊕ x_{u_t} ⊕ x_{v_t}` (for a missing answer, `Z_t`
is set to `false`; legal protocols never miss). -/
def errVec {N s : ℕ} (x : Fin N → Bool) (o : Fin s → Output N) : Fin s → Bool :=
  fun t => match o t with
    | some (e, b) => xor b (edgeParity x e)
    | none => false

/-! ### Quantum one-way protocols with sequential requests (SeqHM) -/

/-- A quantum one-way protocol with `s` sequential requests from `Q` and `nR` public coin values
(Definition 6.9, p.30, with the requests of §4.3 and Lemma 5.9). -/
structure QSeqProtocol (N s : ℕ) (Q : Type) (nR : ℕ) where
  coin : Fin nR → ℝ
  d : ℕ
  msg : Fin nR → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℂ
  e : ℕ
  nI : ℕ
  init : Fin nR → Fin nI → Matrix (Fin e) (Fin d) ℂ
  nK : ℕ
  bob : Fin nR → Fin s → Q → Output N → Fin nK → Matrix (Fin e) (Fin e) ℂ

namespace QSeqProtocol

variable {N s : ℕ} {Q : Type} {nR : ℕ}

/-- The coins form a probability vector, every message is a density matrix, Bob's initial map is a
channel and every round's instrument is complete. -/
def Valid (P : QSeqProtocol N s Q nR) : Prop :=
  ((∀ r, 0 ≤ P.coin r) ∧ ∑ r, P.coin r = 1) ∧ (∀ r x, IsDensityMatrix (P.msg r x)) ∧
    (∀ r, IsKrausFamily (P.init r)) ∧
    ∀ r t q, IsKrausFamily (fun p : Output N × Fin P.nK => P.bob r t q p.1 p.2)

/-- Remark 6.2 and Definition 6.9 ("Outputs are legal as in remark 6.2"): on every request naming a
perfect matching, Bob's answer is an edge of that matching. -/
def LegalOutputs (P : QSeqProtocol N s Q nR) (μ : Q → Finset (Sym2 (Fin N))) : Prop :=
  ∀ r t q o j, IsPerfectMatching (μ q) → P.bob r t q o j ≠ 0 → IsLegal (μ q) o

/-- The probability that Bob's answers are `o_1, …, o_s` given the coins `r`, Alice's input `x` and
the requests `qs`. -/
def outProb (P : QSeqProtocol N s Q nR) (r : Fin nR) (x : Fin N → Bool) (qs : Fin s → Q)
    (o : Fin s → Output N) : ℝ :=
  (Fin.foldl s (fun ρ t => krausApply (fun j => P.bob r t (qs t) (o t) j) ρ)
    (krausApply (P.init r) (P.msg r x))).trace.re

/-- The sample space `(R, X, M, O)` of SeqHM: coins, Alice's string, the requests, Bob's answers. -/
abbrev Sample (N s : ℕ) (Q : Type) (nR : ℕ) := Fin nR × (Fin N → Bool) × (Fin s → Q) × (Fin s → Output N)

/-- The joint law of SeqHM_{N,s}(D) (§6.2, p.28; Definition 6.9): `X` uniform, the coins, the
requests i.i.d. from `D` independent of `X` and the coins, and Bob's answers. -/
def law (P : QSeqProtocol N s Q nR) (D : Q → ℝ) : Sample N s Q nR → ℝ :=
  fun ω => P.coin ω.1 * ((2 : ℝ) ^ N)⁻¹ * (∏ t, D (ω.2.2.1 t)) * P.outProb ω.1 ω.2.1 ω.2.2.1 ω.2.2.2

/-- §6.4 (p.31): the history `H_{t−1}`, the classical record before round `t` (rounds numbered
`1, …, s`; round `t` is index `t − 1`): the public coins, the requests and the answers of rounds
`1, …, t − 1`. -/
def history (t : ℕ) (ω : Sample N s Q nR) : Fin nR × (Fin s → Option (Q × Output N)) :=
  (ω.1, fun i => if i.val + 1 < t then some (ω.2.2.1 i, ω.2.2.2 i) else none)

end QSeqProtocol

/-! ### Quantum one-way protocols with simultaneous requests (MHM) -/

/-- A quantum one-way protocol for `m` simultaneous requests (Definition 6.1, p.28): Bob measures
Alice's message with a POVM depending on the coins and on all requests; its outcome is the list of
his answers. -/
structure SimProtocol (N m : ℕ) (Q : Type) (nR : ℕ) where
  coin : Fin nR → ℝ
  d : ℕ
  msg : Fin nR → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℂ
  povm : Fin nR → (Fin m → Q) → (Fin m → Output N) → Matrix (Fin d) (Fin d) ℂ

namespace SimProtocol

variable {N m : ℕ} {Q : Type} {nR : ℕ}

/-- Coins form a probability vector, messages are density matrices, Bob's measurements are POVMs. -/
def Valid [Fintype Q] (P : SimProtocol N m Q nR) : Prop :=
  ((∀ r, 0 ≤ P.coin r) ∧ ∑ r, P.coin r = 1) ∧ (∀ r x, IsDensityMatrix (P.msg r x)) ∧
    ∀ r qs, IsPOVM (P.povm r qs)

/-- The probability that Bob outputs `o` given `r`, `x` and the requests `qs`. -/
def outProb (P : SimProtocol N m Q nR) (r : Fin nR) (x : Fin N → Bool) (qs : Fin m → Q)
    (o : Fin m → Output N) : ℝ :=
  effectProb (P.povm r qs o) (P.msg r x)

/-- The sample space `(R, X, M, O, Λ)`, with a side variable `Λ` taking `nΛ` values. -/
abbrev SideSample (N m : ℕ) (Q : Type) (nR nΛ : ℕ) :=
  Fin nR × (Fin N → Bool) × (Fin m → Q) × (Fin m → Output N) × Fin nΛ

/-- The joint law of MHM_{N,m} with requests i.i.d. from `D` (§6.2) together with a side variable
`Λ` on the same probability space, given by its conditional law `κ r x qs o` given everything else. -/
def sideLaw (P : SimProtocol N m Q nR) (D : Q → ℝ) {nΛ : ℕ}
    (κ : Fin nR → (Fin N → Bool) → (Fin m → Q) → (Fin m → Output N) → Fin nΛ → ℝ) :
    SideSample N m Q nR nΛ → ℝ :=
  fun ω => P.coin ω.1 * ((2 : ℝ) ^ N)⁻¹ * (∏ t, D (ω.2.2.1 t)) *
    P.outProb ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 * κ ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2

end SimProtocol

/-! ### Classical public-coin one-way protocols with sequential requests -/

/-- A classical public-coin one-way protocol with `s` sequential requests: Alice sends one of `M`
symbols, chosen with probability `alice r x ω` (private randomness allowed); Bob starts in a state
drawn from `bobInit r ω` among `B` states and in round `t`, having received only `q_t`, moves from
state `a` to `b` writing the answer `o` with probability `bob r t q_t a (b, o)`. -/
structure CSeqProtocol (N s : ℕ) (Q : Type) (nR : ℕ) where
  coin : Fin nR → ℝ
  M : ℕ
  alice : Fin nR → (Fin N → Bool) → Fin M → ℝ
  B : ℕ
  bobInit : Fin nR → Fin M → Fin B → ℝ
  bob : Fin nR → Fin s → Q → Fin B → Fin B × Output N → ℝ

namespace CSeqProtocol

variable {N s : ℕ} {Q : Type} {nR : ℕ}

/-- All of `coin`, `alice r x`, `bobInit r ω`, `bob r t q a` are probability vectors. -/
def Valid (P : CSeqProtocol N s Q nR) : Prop :=
  ((∀ r, 0 ≤ P.coin r) ∧ ∑ r, P.coin r = 1) ∧
    (∀ r x, (∀ w, 0 ≤ P.alice r x w) ∧ ∑ w, P.alice r x w = 1) ∧
    (∀ r w, (∀ b, 0 ≤ P.bobInit r w b) ∧ ∑ b, P.bobInit r w b = 1) ∧
    ∀ r t q a, (∀ p, 0 ≤ P.bob r t q a p) ∧ ∑ p, P.bob r t q a p = 1

/-- The probability that Bob's answers are `o_1, …, o_s` given `r`, `x` and the requests `qs`. -/
def outProb (P : CSeqProtocol N s Q nR) (r : Fin nR) (x : Fin N → Bool) (qs : Fin s → Q)
    (o : Fin s → Output N) : ℝ :=
  ∑ w, P.alice r x w *
    ∑ b, (Fin.foldl s (fun v t => fun b' => ∑ a, v a * P.bob r t (qs t) a (b', o t))
      (P.bobInit r w)) b

/-- The probability that all `s` answers are correct when `X` is uniform, the coins are drawn from
`coin` and the requests are i.i.d. from `D`, request `q` naming `μ q`. -/
def jointSucc [Fintype Q] (P : CSeqProtocol N s Q nR) (μ : Q → Finset (Sym2 (Fin N)))
    (D : Q → ℝ) : ℝ :=
  ∑ r, ∑ x : Fin N → Bool, ∑ qs : Fin s → Q, ∑ o : Fin s → Output N,
    P.coin r * ((2 : ℝ) ^ N)⁻¹ * (∏ t, D (qs t)) * P.outProb r x qs o *
      (if ∀ t, AnswerCorrect (μ (qs t)) x (o t) then 1 else 0)

end CSeqProtocol

/-! ### Cuts (Definition 5.8) -/

/-- A cut of the stream of `ARHM_{N,m}` with `L` copies, followed by `s` requests (Definition 5.8,
p.22): the stream up to the cut is the list `pre r p x`, determined by the input `x`, public
randomness `r` (drawn from `pub`) and private randomness `p` (drawn from `priv`); the `s` items after
the cut are requests with tags `tag r i` whose factor indices are the protocol's requests, independent
of `x` and of the prefix (they are arguments, quantified separately). Nothing is conditioned on the
prefix: its outputs are summed over. -/
structure Cut (N m L s : ℕ) where
  nR : ℕ
  nP : ℕ
  pub : Fin nR → ℝ
  priv : Fin nP → ℝ
  pre : Fin nR → Fin nP → (Fin N → Bool) → List (Item N m L)
  tag : Fin nR → Fin s → Fin m

namespace Cut

variable {N m L s : ℕ}

/-- `pub` and `priv` are probability vectors. -/
def Valid (C : Cut N m L s) : Prop :=
  ((∀ r, 0 ≤ C.pub r) ∧ ∑ r, C.pub r = 1) ∧ ((∀ p, 0 ≤ C.priv p) ∧ ∑ p, C.priv p = 1)

/-- The position of the cut is determined by the public randomness alone. -/
def PositionPublic (C : Cut N m L s) : Prop :=
  ∀ r p p' x x', (C.pre r p x).length = (C.pre r p' x').length

/-- The `s` request items after the cut, for factor indices `ks`. -/
def suffix (C : Cut N m L s) (r : Fin C.nR) (ks : Fin s → Fin (N - 1)) : Fin s → Item N m L :=
  fun i => Item.request (C.tag r i) (ks i)

/-- The memory state of the quantum algorithm `A` at the cut (all prefix outputs summed). -/
def qState (C : Cut N m L s) (A : QStreamAlg N m L) (r : Fin C.nR) (p : Fin C.nP)
    (x : Fin N → Bool) : Matrix (Fin A.d) (Fin A.d) ℂ :=
  A.runFrom 0 (fun i => (C.pre r p x).get i) (fun _ _ => True) A.ρ0

/-- The probability that `A`'s answers to the `s` requests after the cut are `o`, given `r`, `x`
and the factor indices `ks` (averaged over the private randomness). -/
def qSuffixLaw (C : Cut N m L s) (A : QStreamAlg N m L) (r : Fin C.nR) (x : Fin N → Bool)
    (ks : Fin s → Fin (N - 1)) (o : Fin s → Output N) : ℝ :=
  ∑ p, C.priv p * (A.runFrom (C.pre r p x).length (C.suffix r ks) (fun i o' => o' = o i)
    (C.qState A r p x)).trace.re

/-- Proposition 5.13's experiment: `X` uniform, the cut's randomness, and the `s` requests asking
for independent uniform factors; the probability that `A` answers all `s` requests correctly. -/
def qCutSucc (C : Cut N m L s) (A : QStreamAlg N m L) (F : Fin (N - 1) → Finset (Sym2 (Fin N))) :
    ℝ :=
  ∑ r, ∑ p, ∑ x : Fin N → Bool, ∑ ks : Fin s → Fin (N - 1),
    C.pub r * C.priv p * ((2 : ℝ) ^ N)⁻¹ * (∏ _i : Fin s, uniformFactor N (ks _i)) *
      (A.runFrom (C.pre r p x).length (C.suffix r ks)
        (fun i o' => AnswerCorrect (F (ks i)) x o') (C.qState A r p x)).trace.re

/-- The state distribution of the classical algorithm `A` at the cut. -/
def cState (C : Cut N m L s) (A : CStreamAlg N m L) (r : Fin C.nR) (p : Fin C.nP)
    (x : Fin N → Bool) : Fin A.S → ℝ :=
  A.runFrom 0 (fun i => (C.pre r p x).get i) (fun _ _ => True) A.init

/-- The probability that the classical algorithm's answers to the `s` requests after the cut are
`o`, given `r`, `x` and `ks`. -/
def cSuffixLaw (C : Cut N m L s) (A : CStreamAlg N m L) (r : Fin C.nR) (x : Fin N → Bool)
    (ks : Fin s → Fin (N - 1)) (o : Fin s → Output N) : ℝ :=
  ∑ p, C.priv p * ∑ b, A.runFrom (C.pre r p x).length (C.suffix r ks) (fun i o' => o' = o i)
    (C.cState A r p x) b

end Cut

end FourWayStream.ARHM


