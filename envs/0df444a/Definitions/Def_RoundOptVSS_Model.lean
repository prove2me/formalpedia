-- Prove2me | Definitions.Def_RoundOptVSS_Model
-- name    : RoundOptVSS_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:58:30.55992+00:00
-- url     : https://prove2.me/theorems/46edbf0a-98ee-4a68-9cc8-228ec6f04d04
-- title:
--   The synchronous execution model with private channels, broadcast and a static rushing adversary; statistical VSS (Definition 4.2)
-- statement:
--   There are $n$ parties $P_1,\dots,P_n$ (indexed by $\mathrm{Fin}\,n$), one of them the dealer $D$, connected by private authenticated channels and an ideal broadcast channel. Public parameters are $(n,t,\kappa,h,D)$; they are **valid** when $t<n/2$.
--
--   A **(3,1)-round protocol** consists of, for every party and every round $r\in\{0,1,2,3\}$ (rounds $0,1,2$ are the sharing rounds and round $3$ is the reconstruction round): an initial state (the dealer receives its secret $x\in\mathrm{Val}^h$), a list of moduli $N_1,\dots,N_k$ of the coins it draws (answered by independent uniform values in $\{0,\dots,N_j-1\}$), a rule computing from its state and coins one private message to each party and one broadcast, a rule updating its state from the messages it receives (indexed by sender), and an output rule giving an element of $\mathrm{Val}^h\cup\{\bot\}$. A public cap bounds message length; a missing message, or one longer than the cap, is received as missing.
--
--   The adversary corrupts a fixed set $C$ with $|C|\le t$ (static). It is **rushing**: in every round it first sees all honest broadcasts and all honest private messages addressed to corrupt parties, never a message between two honest parties, and then chooses the corrupt parties' private messages (which may differ between recipients) and broadcasts (a broadcast is one value received by everybody). It is an arbitrary randomized strategy with an arbitrary state space (computationally unbounded), split into a sharing part, which starts from the dealer's secret if the dealer is corrupt, and a reconstruction part, which continues from the sharing part's final state.
--
--   The **honest joint view** $S$ at the end of sharing consists, for each honest party, of its input, its coins and every private and broadcast message it received in rounds $0,1,2$. The **adversary's view** at the end of sharing is its state after round $2$.
--
--   A protocol is a **VSS with error $\varepsilon$** (Definition 4.2) if for all valid parameters and every corrupt set $C$ with $|C|\le t$:
--
--   1. for every secret $x$ and every sharing-phase adversary there is a deterministic function $\rho$ of $S$, with values in $\mathrm{Val}^h\cup\{\bot\}$, such that against every reconstruction-phase adversary (commitment) with probability at least $1-\varepsilon$ all honest parties output $\rho(S)$, and (correctness) if the dealer is honest, with probability at least $1-\varepsilon$ we have $\rho(S)=x$ and all honest parties output $x$;
--   2. (perfect privacy) if the dealer is honest, then for every two secrets $x_0,x_1$ and every adversary the adversary's view at the end of sharing has the same distribution.
--
--   This model and definition are the ones of §4 of the paper; the goal theorem is stated in it.
--
--   **Formalization Note** Probabilities are `PMF.toOuterMeasure`; ⊥ is `none`. The honest coins of every party are drawn in each round as independent uniform values; corrupt parties' prescribed messages are computed but never delivered or observed.
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), §1 (p.1), §4 Model and Definition 4.2 (p.15)

import Mathlib

open scoped ENNReal

namespace RoundOptVSS

/-!
# The execution model and statistical VSS

Liu-Zhang, Masserova, *Round-Optimal Statistical Verifiable Secret Sharing with Polynomial
Complexity*, manuscript (STOC 2027 submission, sha256 3a45d95d…): the model of §1 (p.1) and §4
(p.15), "(rs, rr) for a protocol with rs sharing rounds and rr reconstruction rounds" (p.1), and
Definition 4.2 (Statistical verifiable secret sharing), p.15.

**Formalization Note.**
* Parties are `Fin P.n`; the dealer is the index `P.dealer`. The corrupt set is a
  `C : Finset (Fin P.n)`, fixed before the execution (static), with `C.card ≤ P.t`; validity of
  the parameters is `2 * P.t < P.n` (`t < n/2`).
* A protocol has exactly three sharing rounds (`0, 1, 2`) and one reconstruction round (`3`):
  every map takes a round index in `Fin 4`. The reconstruction round is one exchange from the
  saved end-of-sharing state followed by the local `output`; no other exchange exists.
* In a round every honest party, from its state and fresh coins, sends one private message to
  each party and one broadcast. Coins are a request of moduli `N₁, …, N_k` answered by
  independent uniform values in `{0, …, N_j − 1}` (a modulus `0` is read as `1`).
* The adversary is **rushing**: in each round it first sees every honest broadcast and every
  honest private message addressed to a corrupt party (never an honest-to-honest private
  message), then chooses the corrupt parties' private messages (possibly different for different
  recipients) and broadcasts (one value delivered to every party). It is an arbitrary randomized
  strategy (any state type, PMF-valued steps; computationally unbounded), split into a sharing
  part and a reconstruction part that continues from the sharing part's final state.
* Channels are authenticated: an inbox is indexed by sender. A missing message is `none`; a
  delivered message longer than the protocol's public cap `msgCap P` is read as `none`.
* The honest joint view `S` at the end of sharing is, for each honest party, its input, its coins
  and its received private and broadcast messages of rounds `0, 1, 2` (the states are functions
  of these). It contains nothing of the corrupt parties or of the adversary's state. The
  adversary's view at the end of sharing is its state after round `2`.
* Secrets are vectors `Fin P.h → Val`; ⊥ is `none`. Probabilities are `PMF.toOuterMeasure`.
-/

/-- The public parameters: `n` parties, threshold `t`, security parameter `κ`, secret length `h`
and the dealer's index. -/
structure Params where
  n : ℕ
  t : ℕ
  κ : ℕ
  h : ℕ
  dealer : Fin n

/-- `t < n/2`. -/
def Params.Valid (P : Params) : Prop := 2 * P.t < P.n

/-- A (3, 1)-round protocol over message type `Msg`, local state type `St` and secret alphabet
`Val`. Rounds `0, 1, 2 : Fin 4` are the sharing rounds and round `3` the reconstruction round.
* `init P i x` is the initial state of party `i` (the dealer gets `some x`, others `none`);
* `coins P i r st` is the list of moduli of the uniform coins party `i` draws in round `r`;
* `send P i r st c` gives the private message to each party and the broadcast;
* `recv P i r st c priv bc` is the new state after receiving the private inbox `priv` and the
  broadcasts `bc`, both indexed by sender (`none` = missing or over the cap);
* `output P i st` is the reconstruction output (`none` = ⊥);
* `msgLen` measures messages and `msgCap P` is the public length cap. -/
structure Protocol (Msg St Val : Type) where
  init : (P : Params) → Fin P.n → Option (Fin P.h → Val) → St
  coins : (P : Params) → Fin P.n → Fin 4 → St → List ℕ
  send : (P : Params) → Fin P.n → Fin 4 → St → List ℕ → (Fin P.n → Msg) × Msg
  recv : (P : Params) → Fin P.n → Fin 4 → St → List ℕ →
    (Fin P.n → Option Msg) → (Fin P.n → Option Msg) → St
  output : (P : Params) → Fin P.n → St → Option (Fin P.h → Val)
  msgLen : Msg → ℕ
  msgCap : Params → ℕ

/-- Independent uniform coins for a list of requested moduli (modulus `N` read as `max N 1`). -/
noncomputable def coinPMF : List ℕ → PMF (List ℕ)
  | [] => PMF.pure []
  | N :: L => (PMF.uniformOfFintype (Fin (N - 1 + 1))).bind fun v =>
      (coinPMF L).map fun vs => (v : ℕ) :: vs

/-- Independent product of finitely many PMFs. -/
noncomputable def pmfPi {α : Type} : (n : ℕ) → (Fin n → PMF α) → PMF (Fin n → α)
  | 0, _ => PMF.pure (fun i => Fin.elim0 i)
  | n + 1, f => (f 0).bind fun a => (pmfPi n (fun i => f i.succ)).map fun r => Fin.cons a r

/-- The adversary's choice in a round: `(priv, bc)` where `priv c j` is the private message of
sender `c` to `j` and `bc c` the broadcast of `c`. Entries of honest senders are ignored. -/
abbrev AdvChoice (P : Params) (Msg : Type) :=
  (Fin P.n → Fin P.n → Option Msg) × (Fin P.n → Option Msg)

/-- The rushing observation of a round: honest private messages to corrupt parties (`priv i j`
for honest `i`, corrupt `j`; `none` elsewhere) and the honest broadcasts (`none` for corrupt
senders). -/
abbrev AdvObs (P : Params) (Msg : Type) :=
  (Fin P.n → Fin P.n → Option Msg) × (Fin P.n → Option Msg)

/-- The sharing-phase part of a static rushing adversary: a state type, an initial state drawn
from the corrupt parties' inputs (the dealer's secret if the dealer is corrupt), and one step per
sharing round. -/
structure ShareAdv (P : Params) (Msg Val : Type) where
  σ : Type
  init : Option (Fin P.h → Val) → PMF σ
  step : Fin 3 → σ → AdvObs P Msg → PMF (AdvChoice P Msg × σ)

/-- The reconstruction-phase part: one rushing step from the sharing part's final state. -/
def RecAdv {P : Params} {Msg Val : Type} (A : ShareAdv P Msg Val) : Type :=
  A.σ → AdvObs P Msg → PMF (AdvChoice P Msg)

/-- What happened in one round. `coins i`: the coins of `i`; `priv j i`: the message delivered
from `j` to `i`; `bcast j`: the broadcast of `j` delivered to every party; `sent i j`, `sentB i`:
the messages the protocol prescribes for party `i` (the actual ones for honest `i`). -/
structure RoundRec (P : Params) (Msg : Type) where
  coins : Fin P.n → List ℕ
  priv : Fin P.n → Fin P.n → Option Msg
  bcast : Fin P.n → Option Msg
  sent : Fin P.n → Fin P.n → Msg
  sentB : Fin P.n → Msg

variable {Msg St Val : Type}

/-- Delivery through the cap: a message longer than `msgCap P` is read as missing. -/
def capped (prot : Protocol Msg St Val) (P : Params) (m : Option Msg) : Option Msg :=
  m.filter fun x => decide (prot.msgLen x ≤ prot.msgCap P)

/-- One synchronous round `r` from the parties' states `st`, against a rushing adversary step
`adv` that sees the round's observation before choosing the corrupt messages. -/
noncomputable def runRound (prot : Protocol Msg St Val) (P : Params) (C : Finset (Fin P.n))
    (r : Fin 4) (st : Fin P.n → St) {τ : Type}
    (adv : AdvObs P Msg → PMF (AdvChoice P Msg × τ)) : PMF (RoundRec P Msg × τ) :=
  (pmfPi P.n fun i => coinPMF (prot.coins P i r (st i))).bind fun c =>
    let out : Fin P.n → (Fin P.n → Msg) × Msg := fun i => prot.send P i r (st i) (c i)
    let obs : AdvObs P Msg :=
      (fun i j => if i ∉ C ∧ j ∈ C then some ((out i).1 j) else none,
       fun i => if i ∉ C then some (out i).2 else none)
    (adv obs).map fun cs =>
      (⟨c,
        fun i j => capped prot P (if i ∈ C then cs.1.1 i j else some ((out i).1 j)),
        fun i => capped prot P (if i ∈ C then cs.1.2 i else some (out i).2),
        fun i => (out i).1,
        fun i => (out i).2⟩, cs.2)

/-- The states after round `r`. -/
def nextStates (prot : Protocol Msg St Val) (P : Params) (r : Fin 4) (st : Fin P.n → St)
    (rr : RoundRec P Msg) : Fin P.n → St :=
  fun i => prot.recv P i r (st i) (rr.coins i) (fun j => rr.priv j i) rr.bcast

/-- The result of the sharing phase: the inputs, the three rounds, the states before rounds
`0, 1, 2` and after sharing (`states 3`), and the adversary's final sharing state (its view). -/
structure ShareOutcome (P : Params) (Msg St Val σ : Type) where
  inputs : Fin P.n → Option (Fin P.h → Val)
  rounds : Fin 3 → RoundRec P Msg
  states : Fin 4 → Fin P.n → St
  adv : σ

/-- The sharing phase (three rounds) with secret `x` at the dealer. -/
noncomputable def shareExec (prot : Protocol Msg St Val) (P : Params) (C : Finset (Fin P.n))
    (x : Fin P.h → Val) (A : ShareAdv P Msg Val) : PMF (ShareOutcome P Msg St Val A.σ) :=
  let inp : Fin P.n → Option (Fin P.h → Val) := fun i => if i = P.dealer then some x else none
  let st0 : Fin P.n → St := fun i => prot.init P i (inp i)
  (A.init (if P.dealer ∈ C then some x else none)).bind fun s0 =>
  (runRound prot P C 0 st0 (A.step 0 s0)).bind fun p0 =>
  let st1 := nextStates prot P 0 st0 p0.1
  (runRound prot P C 1 st1 (A.step 1 p0.2)).bind fun p1 =>
  let st2 := nextStates prot P 1 st1 p1.1
  (runRound prot P C 2 st2 (A.step 2 p1.2)).map fun p2 =>
  ⟨inp, ![p0.1, p1.1, p2.1], ![st0, st1, st2, nextStates prot P 2 st2 p2.1], p2.2⟩

/-- The honest parties' joint view at the end of sharing: for each honest `i`, its input, its
coins of rounds `0, 1, 2`, its private inbox (indexed by sender) and the broadcasts of those
rounds (the public sharing transcript). -/
abbrev HonestView (P : Params) (C : Finset (Fin P.n)) (Msg Val : Type) :=
  {i : Fin P.n // i ∉ C} →
    Option (Fin P.h → Val) × (Fin 3 → List ℕ) × (Fin 3 → Fin P.n → Option Msg) ×
      (Fin 3 → Fin P.n → Option Msg)

/-- The honest joint view `S` of a sharing outcome. -/
def ShareOutcome.view {P : Params} {C : Finset (Fin P.n)} {σ : Type}
    (o : ShareOutcome P Msg St Val σ) : HonestView P C Msg Val :=
  fun i => (o.inputs i.1, fun r => (o.rounds r).coins i.1, fun r j => (o.rounds r).priv j i.1,
    fun r => (o.rounds r).bcast)

/-- A whole execution: the sharing outcome, the reconstruction round, the final states and every
party's output. -/
structure Outcome (P : Params) (Msg St Val σ : Type) where
  share : ShareOutcome P Msg St Val σ
  recon : RoundRec P Msg
  final : Fin P.n → St
  out : Fin P.n → Option (Fin P.h → Val)

/-- The round record of round `r` (`0, 1, 2` sharing, `3` reconstruction). -/
def Outcome.roundAt {P : Params} {σ : Type} (o : Outcome P Msg St Val σ) (r : Fin 4) :
    RoundRec P Msg :=
  if h : r.val < 3 then o.share.rounds ⟨r.val, h⟩ else o.recon

/-- The parties' states before round `r` (`stateAt 4` = the final states). -/
def Outcome.stateAt {P : Params} {σ : Type} (o : Outcome P Msg St Val σ) (r : Fin 5) :
    Fin P.n → St :=
  if h : r.val < 4 then o.share.states ⟨r.val, h⟩ else o.final

/-- The honest joint view at the end of sharing of a whole execution. -/
def Outcome.view {P : Params} {C : Finset (Fin P.n)} {σ : Type}
    (o : Outcome P Msg St Val σ) : HonestView P C Msg Val :=
  ShareOutcome.view (C := C) o.share

/-- The whole execution: sharing, then one reconstruction round from the saved states against the
reconstruction part `B`, then local output. -/
noncomputable def exec (prot : Protocol Msg St Val) (P : Params) (C : Finset (Fin P.n))
    (x : Fin P.h → Val) (A : ShareAdv P Msg Val) (B : RecAdv A) :
    PMF (Outcome P Msg St Val A.σ) :=
  (shareExec prot P C x A).bind fun o =>
    (runRound prot P C 3 (o.states 3) (fun obs => (B o.adv obs).map fun ch => (ch, ()))).map
      fun p =>
        let fin := nextStates prot P 3 (o.states 3) p.1
        ⟨o, p.1, fin, fun i => prot.output P i (fin i)⟩

/-- **Definition 4.2** (statistical VSS with error `ε`), p.15, for every valid parameter set:
against every static rushing adversary corrupting `C`, `|C| ≤ t`,
* (iii) commitment: there is a deterministic function `ρ` of the honest view `S`, chosen after
  the sharing adversary and before (independently of) the reconstruction adversary, such that
  with probability `≥ 1 − ε` all honest parties output `ρ(S)`;
* (i) correctness: if the dealer is honest, with probability `≥ 1 − ε` the same `ρ(S)` equals the
  input `x` and every honest party outputs `x`;
* (ii) perfect privacy: if the dealer is honest, the adversary's view at the end of sharing has
  the same law for every two inputs. -/
def IsVSS (prot : Protocol Msg St Val) (ε : Params → ℝ≥0∞) : Prop :=
  ∀ P : Params, P.Valid → ∀ C : Finset (Fin P.n), C.card ≤ P.t →
    (∀ (x : Fin P.h → Val) (A : ShareAdv P Msg Val),
      ∃ ρ : HonestView P C Msg Val → Option (Fin P.h → Val), ∀ B : RecAdv A,
        (P.dealer ∉ C → 1 - ε P ≤ (exec prot P C x A B).toOuterMeasure
            {o | ρ (Outcome.view (C := C) o) = some x ∧ ∀ i, i ∉ C → o.out i = some x}) ∧
        1 - ε P ≤ (exec prot P C x A B).toOuterMeasure
            {o | ∀ i, i ∉ C → o.out i = ρ (Outcome.view (C := C) o)}) ∧
    (P.dealer ∉ C → ∀ (x₀ x₁ : Fin P.h → Val) (A : ShareAdv P Msg Val),
      (shareExec prot P C x₀ A).map (fun o => o.adv) = (shareExec prot P C x₁ A).map (fun o => o.adv))

end RoundOptVSS


