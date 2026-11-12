-- Prove2me | Definitions.Def_NovyPQZK_Main_Commitment
-- name    : NovyPQZK_Main_Commitment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:35:21.19827+00:00
-- url     : https://prove2.me/theorems/d8af7677-148a-46f5-9b34-a4960332109a
-- title:
--   Classical commitment schemes (Definition 4), public verifiability, hiding, unique openings and parallel composition (Definitions 5, 6, 10, 12)
-- statement:
--   A **classical commitment scheme** $\Pi = (\mathrm{SetUp}, S_{com}, R_{com}, S_{open}, R_{open})$ for a message space $M$ (depending on $n$) consists of: deterministic public parameters $\mathrm{Public}_n = \mathrm{SetUp}(1^n)$; a committing phase of $\mathrm{rounds}(n)$ rounds between the receiver $R_{com}(\mathrm{Public}_n)$, speaking first in each round, and the sender $S_{com}(m,\mathrm{Public}_n)$, producing the transcript $\mathrm{Comm}$, the sender's view $\mathrm{Priv}_S$ and the receiver's coins $\mathrm{Priv}_R$; a one-message opening $(m,u) = S_{open}(\mathrm{Priv}_S)$; and the deterministic check $ok = R_{open}(m,u,\mathrm{Comm},\mathrm{Priv}_R,\mathrm{Public}_n)$. All five are PPT. A **bit commitment** has $M = \{0,1\}$ (the strings `[false]`, `[true]`).
--
--   - **Publicly verifiable** (Def. 5): $R_{open}$ does not depend on $\mathrm{Priv}_R$.
--   - **Unique openings** (Def. 10): for every $\mathrm{Comm},\mathrm{Priv}_R,\mathrm{Public}_n$ and bit $b$, at most one $u$ with $R_{open}(b,u,\dots) = 1$.
--   - **Perfectly / statistically hiding** (Def. 6): for every $n$, all $m,m'\in M$ and every (unbounded) receiver strategy, the distributions of the receiver's view in the two committing phases are equal / at statistical distance at most $\mu(n)$ for one negligible $\mu$.
--   - **Correct** (a reading, not in Def. 4): the honest opening of an honest commitment to $m\in M$ is accepted, for all coins.
--   - **$k$-fold parallel composition** $\Pi^k$ (Def. 12, $k = k(n)$): $k$ committing phases run in parallel, the messages of a round packed together; the opening is $(m,(u_1,\dots,u_k))$ and $R^k_{open}$ accepts iff every component opening is accepted on its own transcript and receiver coins.
--
--   **Formalization Note** A receiver strategy is deterministic (its next message as a function of the sender's messages so far); a randomized receiver is a mixture. $\Pi^k$'s public parameters are $\mathrm{pack}[1^{k(n)},\mathrm{Public}_n]$ so that the receiver knows $k$. Negligible is the published `CompNonlocal.Negligible`.
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §3.4 pp. 22–26, Definitions 4, 5, 6, 10, 12

import Mathlib
import Definitions.Def_CompNonlocal_Negligible
import Definitions.Def_NovyPQZK_Main_Classical

namespace NovyPQZK.Main

/-!
Dupuis, Ligez, Medhioub, Salvail, Thibodeau, arXiv:2610.33185 (sha256 857d8563…3257f), §3.4,
pp. 22–26: classical commitment schemes with non-interactive openings (Definition 4), public
verifiability (Definition 5), statistical and perfect hiding (Definition 6), unique openings
(Definition 10) and the `k`-fold parallel composition (Definition 12).

The committing phase is a run of `rounds n` rounds of the receiver `R_com` (speaking first in
each round, input `Public_n`) with the sender `S_com` (input `pack [m, Public_n]`); a party with
nothing to say sends the empty string. `Comm` is the transcript, `Priv_R` the receiver's coins and
`Priv_S` the sender's view. The opening is one message `(m, u)` computed by `S_open` from the
sender's view; `R_open(m, u, Comm, Priv_R, Public_n)` is deterministic.
-/

/-- Definition 4 (pp. 22–23): a classical commitment scheme `Π = (SetUp, S_com, R_com, S_open,
R_open)` for the message space `msgSpace n`. -/
structure CommitmentScheme where
  /-- The message space `M` (which may depend on `n`). -/
  msgSpace : ℕ → Set Bits
  /-- `Public_n := SetUp(1^n)`, deterministic. -/
  setup : ℕ → Bits
  /-- The number of rounds of the committing phase. -/
  rounds : ℕ → ℕ
  /-- `S_com`, with input `pack [m, Public_n]`. -/
  sender : Party
  /-- `R_com`, with input `Public_n`. -/
  receiver : Party
  /-- `S_open`: from the sender's view at the end of the committing phase, the message `(m, u)`. -/
  sopen : Bits → Bits × Bits
  /-- `R_open(m, u, Comm, Priv_R, Public_n) ∈ {0, 1}`. -/
  ropen : Bits → Bits → List Bits → Bits → Bits → Bool

/-- The sender's input `(m, Public_n)`. -/
def senderInput (m pub : Bits) : Bits := pack [m, pub]

/-- Definition 4: all five components are (uniform) probabilistic polynomial time; `S_open`'s
output is polynomial in the sender's input. -/
def CommitmentScheme.IsPPT (Cm : CommitmentScheme) : Prop :=
  PolyTimeFn (fun s => Cm.setup s.length) ∧ PolyTimeNat (fun s => Cm.rounds s.length) ∧
    Cm.sender.IsPPT ∧ Cm.receiver.IsPPT ∧
    PolyTimeFn (fun s => pack [(Cm.sopen s).1, (Cm.sopen s).2]) ∧
    (∃ p : Polynomial ℕ, ∀ (inp : Bits) (c : CoinSpace (Cm.sender.coins inp)) (msgs : List Bits),
      (Cm.sopen (Cm.sender.view inp c msgs)).1.length + (Cm.sopen (Cm.sender.view inp c msgs)).2.length
        ≤ p.eval inp.length) ∧
    PolyTimeFn (fun s => match unpack s with
      | m :: u :: pub :: privR :: comm => [Cm.ropen m u comm privR pub]
      | _ => [false])

/-- A bit commitment scheme: `M = {0, 1}`, the bit `b` written as the one-bit string `[b]`. -/
def CommitmentScheme.IsBit (Cm : CommitmentScheme) : Prop :=
  ∀ n, Cm.msgSpace n = {[false], [true]}

/-- The honest committing phase on message `m` with receiver coins `cR` and sender coins `cS`:
(receiver's messages, sender's messages). -/
def CommitmentScheme.honestRun (Cm : CommitmentScheme) (n : ℕ) (m : Bits)
    (cR : CoinSpace (Cm.receiver.coins (Cm.setup n)))
    (cS : CoinSpace (Cm.sender.coins (senderInput m (Cm.setup n)))) : List Bits × List Bits :=
  runMsgs Cm.receiver Cm.sender (Cm.setup n) (senderInput m (Cm.setup n)) cR cS (Cm.rounds n)

/-- Correctness (a reading: Definition 4 states none; the completeness of Protocol 18 needs it):
the honest opening of an honest commitment to any `m ∈ M` is accepted, for all coins. -/
def CommitmentScheme.IsCorrect (Cm : CommitmentScheme) : Prop :=
  ∀ n, ∀ m ∈ Cm.msgSpace n, ∀ (cR : CoinSpace (Cm.receiver.coins (Cm.setup n)))
    (cS : CoinSpace (Cm.sender.coins (senderInput m (Cm.setup n)))),
    let run := Cm.honestRun n m cR cS
    let op := Cm.sopen (Cm.sender.view (senderInput m (Cm.setup n)) cS run.1)
    op.1 = m ∧ Cm.ropen op.1 op.2 (interleave run.1 run.2) (encCoins cR) (Cm.setup n) = true

/-- Definition 5 (p. 23): publicly verifiable, `R_open` does not use `Priv_R`. -/
def CommitmentScheme.IsPubliclyVerifiable (Cm : CommitmentScheme) : Prop :=
  ∀ (m u : Bits) (comm : List Bits) (r r' pub : Bits), Cm.ropen m u comm r pub = Cm.ropen m u comm r' pub

/-- Definition 10 (p. 25): unique openings, for every `Comm, Priv_R, Public_n` and bit `b` at most
one `u` with `R_open(b, u, Comm, Priv_R, Public_n) = 1`. -/
def CommitmentScheme.HasUniqueOpenings (Cm : CommitmentScheme) : Prop :=
  ∀ (comm : List Bits) (privR pub : Bits) (b : Bool) (u u' : Bits),
    Cm.ropen [b] u comm privR pub = true → Cm.ropen [b] u' comm privR pub = true → u = u'

/-- The committing phase between the honest sender (message `m`, coins `c`) and a deterministic,
possibly unbounded receiver `Rs` (its next message as a function of the sender's messages so
far): (receiver's messages, sender's messages). A randomized receiver is a mixture of these. -/
def CommitmentScheme.hidingRun (Cm : CommitmentScheme) (n : ℕ) (m : Bits) (Rs : List Bits → Bits)
    (c : CoinSpace (Cm.sender.coins (senderInput m (Cm.setup n)))) : ℕ → List Bits × List Bits
  | 0 => ([], [])
  | r + 1 =>
      let p := Cm.hidingRun n m Rs c r
      let a := Rs p.2
      (p.1 ++ [a], p.2 ++ [Cm.sender.msg (senderInput m (Cm.setup n)) c (p.1 ++ [a])])

/-- The view of the receiver `Rs` (its transcript) when the honest sender commits to `m`. -/
def CommitmentScheme.receiverView (Cm : CommitmentScheme) (n : ℕ) (m : Bits) (Rs : List Bits → Bits)
    (c : CoinSpace (Cm.sender.coins (senderInput m (Cm.setup n)))) : List Bits :=
  let p := Cm.hidingRun n m Rs c (Cm.rounds n)
  interleave p.1 p.2

/-- The probability that the receiver's view is `t`. -/
noncomputable def CommitmentScheme.viewProb (Cm : CommitmentScheme) (n : ℕ) (m : Bits)
    (Rs : List Bits → Bits) (t : List Bits) : ℝ :=
  avgOver (CoinSpace (Cm.sender.coins (senderInput m (Cm.setup n)))) fun c =>
    if Cm.receiverView n m Rs c = t then 1 else 0

/-- Definition 6 (p. 23), perfectly hiding: for every (possibly unbounded) receiver and all
`m, m' ∈ M`, its views in the two committing phases are identically distributed. -/
def CommitmentScheme.IsPerfectlyHiding (Cm : CommitmentScheme) : Prop :=
  ∀ n, ∀ m ∈ Cm.msgSpace n, ∀ m' ∈ Cm.msgSpace n, ∀ (Rs : List Bits → Bits) (t : List Bits),
    Cm.viewProb n m Rs t = Cm.viewProb n m' Rs t

/-- The statistical distance between the receiver's views for `m` and `m'`. -/
noncomputable def CommitmentScheme.viewDist (Cm : CommitmentScheme) (n : ℕ) (m m' : Bits)
    (Rs : List Bits → Bits) : ℝ :=
  (1 / 2 : ℝ) * ∑ t ∈ (Finset.univ.image (Cm.receiverView n m Rs) ∪
      Finset.univ.image (Cm.receiverView n m' Rs)),
    |Cm.viewProb n m Rs t - Cm.viewProb n m' Rs t|

/-- Definition 6 (p. 23), statistically hiding: the views are statistically indistinguishable,
uniformly over all (possibly unbounded) receivers. -/
def CommitmentScheme.IsStatisticallyHiding (Cm : CommitmentScheme) : Prop :=
  ∃ μ : ℕ → ℝ, CompNonlocal.Negligible μ ∧
    ∀ n, ∀ m ∈ Cm.msgSpace n, ∀ m' ∈ Cm.msgSpace n, ∀ Rs : List Bits → Bits,
      Cm.viewDist n m m' Rs ≤ μ n

/-! ### Parallel composition (Definition 12, p. 26) -/

/-- Cut a list into consecutive pieces of the given lengths. -/
def splitLens {α : Type*} : List ℕ → List α → List (List α)
  | [], _ => []
  | k :: ks, l => l.take k :: splitLens ks (l.drop k)

/-- Component `i` of a composite message `pack [x₁, …, x_k]`. -/
def component (i : ℕ) (msg : Bits) : Bits := (unpack msg).getD i []

/-- The views of the `k` component executions inside a composite view: instance `i` has input
`instInp i`, its own block of the composite coins, and component `i` of every message received. -/
def parInstViews (A : Party) (instInp : ℕ → Bits) (k : ℕ) (cenc : Bits) (msgs : List Bits) :
    List Bits :=
  let chunks := splitLens ((List.range k).map fun i => (A.coins (instInp i)).length)
    ((unpack cenc).map bitsToNat)
  (List.range k).map fun i =>
    pack (instInp i :: pack ((chunks.getD i []).map natToBits) :: msgs.map (component i))

/-- The composite receiver `R^k_com`: input `pack [1^k, Public_n]`; it runs `k` copies of `R_com`
with independent coins and sends `pack` of their messages. -/
def parRecv (R : Party) : Party where
  coins inp := match unpack inp with
    | [a, pub] => (List.replicate a.length (R.coins pub)).flatten
    | _ => []
  next view := match unpack view with
    | inp :: cenc :: msgs => match unpack inp with
      | [a, pub] => pack ((parInstViews R (fun _ => pub) a.length cenc msgs).map R.next)
      | _ => []
    | _ => []

/-- The sender inputs of the components: `pack [m_i, Public_n]` for `m = pack [m₁, …, m_k]`. -/
def parSendInp (m pub : Bits) (i : ℕ) : Bits := senderInput (component i m) pub

/-- The composite sender `S^k_com`: input `pack [pack [m₁, …, m_k], pack [1^k, Public_n]]`. -/
def parSend (S : Party) : Party where
  coins inp := match unpack inp with
    | [m, inp'] => match unpack inp' with
      | [a, pub] => ((List.range a.length).map fun i => S.coins (parSendInp m pub i)).flatten
      | _ => []
    | _ => []
  next view := match unpack view with
    | inp :: cenc :: msgs => match unpack inp with
      | [m, inp'] => match unpack inp' with
        | [a, pub] => pack ((parInstViews S (parSendInp m pub) a.length cenc msgs).map S.next)
        | _ => []
      | _ => []
    | _ => []

/-- `S^k_open`: `(m, (u₁, …, u_k))` with `u_i` the opening of component `i`. -/
def parSopen (Cm : CommitmentScheme) (view : Bits) : Bits × Bits :=
  match unpack view with
  | inp :: cenc :: msgs => match unpack inp with
    | [m, inp'] => match unpack inp' with
      | [a, pub] =>
          let ops := (parInstViews Cm.sender (parSendInp m pub) a.length cenc msgs).map Cm.sopen
          (pack (ops.map Prod.fst), pack (ops.map Prod.snd))
      | _ => ([], [])
    | _ => ([], [])
  | _ => ([], [])

/-- `R^k_open`: accept iff `m` and `u` are `k`-tuples and every component opening is accepted by
`R_open` on its own transcript and receiver coins. -/
def parRopen (Cm : CommitmentScheme) (m u : Bits) (comm : List Bits) (privR pub' : Bits) : Bool :=
  match unpack pub' with
  | [a, pub] =>
      let k := a.length
      let ms := unpack m
      let us := unpack u
      let privs := splitLens (List.replicate k (Cm.receiver.coins pub).length)
        ((unpack privR).map bitsToNat)
      decide (m = pack ms ∧ u = pack us ∧ ms.length = k ∧ us.length = k) &&
        (List.range k).all fun i =>
          Cm.ropen (ms.getD i []) (us.getD i []) (comm.map (component i))
            (pack ((privs.getD i []).map natToBits)) pub
  | _ => false

/-- Definition 12 (p. 26): the `k`-fold parallel composition `Π^k`, message space `M^k`. Its public
parameters `pack [1^{k(n)}, Public_n]` carry `k(n)` so that the receiver knows it. -/
def CommitmentScheme.parallel (Cm : CommitmentScheme) (k : ℕ → ℕ) : CommitmentScheme where
  msgSpace n := {m | ∃ l : List Bits, l.length = k n ∧ (∀ x ∈ l, x ∈ Cm.msgSpace n) ∧ m = pack l}
  setup n := pack [unary (k n), Cm.setup n]
  rounds := Cm.rounds
  sender := parSend Cm.sender
  receiver := parRecv Cm.receiver
  sopen := parSopen Cm
  ropen := parRopen Cm

/-- `k = k(n)` is polynomially bounded. -/
def IsPolyBounded (k : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, k n ≤ p.eval n

end NovyPQZK.Main


