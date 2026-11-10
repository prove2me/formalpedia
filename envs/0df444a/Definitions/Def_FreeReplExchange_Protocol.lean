-- Prove2me | Definitions.Def_FreeReplExchange_Protocol
-- name    : FreeReplExchange_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:17:29.949748+00:00
-- url     : https://prove2.me/theorems/ebaef453-4029-4733-b185-4e1ae822574a
-- title:
--   Multi-round protocols, histories, strategies, runs and terminal outcomes
-- statement:
--   For a fixed instance, a **protocol** $M=(M_t)_{t\ge1}$ posts in round $t$ a set of proposals $P_t=M_t(H_{t-1},P)$, where $P$ is the participating set and the **history** $H_{t-1}$ lists all previous proposal sets with the acceptance and rejection decisions they received. The participants then simultaneously accept or reject each proposal involving them; a proposal executes iff both participants accept. With $A_t\subseteq P_t$ the accepted proposals,
--   $$x^{(t)}=x^{(t-1)}[A_t],\qquad D_t=D_{t-1}\cup(P_t\setminus A_t),\qquad D_0=\varnothing .$$
--   The protocol terminates when $P_t=\varnothing$, with terminal allocation $x^{(\infty)}$ and rejected set $D_\infty$.
--
--   A **strategy** of agent $i$ prescribes, for each proposal $p\in P_t$ involving her, a decision $\sigma_i(p,P,P_t,H_{t-1})\in\{0,1\}$; she sees the participating set, the history and the whole proposal set, but not the other decisions of the same round. The **accepting policy** $\sigma^\star_i$ accepts everything, and $\sigma^\star$ is the accepting profile. For a profile $\sigma$, $x^{(\infty)}(M,P,\sigma)$ is the terminal allocation and $u_i(M,P,\sigma)=\tilde u_i(x^{(\infty)}(M,P,\sigma))$, defined for every agent including nonparticipants. A round with $P_t\neq\varnothing$ is **nonterminal**.
--
--   These objects state every desideratum and every guarantee of the protocol.
--
--   **Formalization Note** A round record holds $P_t$ and each participant's decision on each proposal. The run is the history after $t$ rounds; it stops growing at the first empty proposal set. Terminal quantities are read at the horizon $L$, the number of quadruples $((i,r),(j,s))$, which bounds the number of nonterminal rounds of a protocol that never re-proposes an executed or rejected exchange; the predicate `TerminatesByHorizon` states that the protocol has stopped by then. A profile is a map from agents to strategies; only participants' strategies are consulted. The round index $t$ is the length of the history plus one.
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), §2.2, p.14 (PDF pp.16–17)

import Mathlib
import Definitions.Def_FreeReplExchange_util
import Definitions.Def_FreeReplExchange_Exchange

namespace FreeReplExchange

/-- The record of one round of a multi-round protocol, Yang–Kandasamy, *Pairwise Exchanges of
Freely Replicable Goods with Negative Externalities*, arXiv:2603.12403 (held version, sha256
3ae07967…), §2.2, p.14 (PDF p.16): the posted proposal set `P_t` and, for each proposal, the
decision of each of its two participants (`true` = accept).

**Formalization Note.** `dec₁ p` is the decision of agent `p.i` and `dec₂ p` that of `p.j`. The
runs below set both to `false` outside `proposed`. -/
structure RoundRecord (A : Type*) (m : ℕ) where
  /-- the proposal set `P_t` -/
  proposed : Finset (Exchange A m)
  /-- the decision of the first participant `p.i` on `p` -/
  dec₁ : Exchange A m → Bool
  /-- the decision of the second participant `p.j` on `p` -/
  dec₂ : Exchange A m → Bool

/-- A history `H_t`: the list of the records of rounds `1, …, t`, oldest first (p.14: "all
previous proposals together with the acceptance and rejection decisions they received"). -/
abbrev History (A : Type*) (m : ℕ) := List (RoundRecord A m)

/-- A protocol `M = (M_t)_{t≥1}` for a fixed instance, p.14: the rule `P_t = M_t(H_{t−1}, P)`
mapping the participating set and the history to the next proposal set.

**Formalization Note.** The round index `t` is the length of the history plus one, so a rule
that depends on `t` is a function of the history. -/
abbrev Protocol (A : Type*) (m : ℕ) := Finset A → History A m → Finset (Exchange A m)

/-- An agent's strategy, p.14: for a proposal `p ∈ P_t` involving her, the decision
`σ_i(p, P, P_t, H_{t−1}) ∈ {0, 1}` (`true` = accept). A strategy profile is a map `A → Strategy`;
only participants' strategies are ever consulted. -/
abbrev Strategy (A : Type*) (m : ℕ) :=
  Exchange A m → Finset A → Finset (Exchange A m) → History A m → Bool

/-- The accepting policy `σ⋆_i`, p.14, and the accepting profile `σ⋆`. -/
def acceptAll {A : Type*} {m : ℕ} : A → Strategy A m := fun _ _ _ _ _ => true

/-- The accepted exchanges `A_t ⊆ P_t` of a round: both participants accept. -/
def RoundRecord.accepted {A : Type*} {m : ℕ} (rr : RoundRecord A m) : Finset (Exchange A m) :=
  rr.proposed.filter fun p => rr.dec₁ p && rr.dec₂ p

/-- The rejected exchanges `P_t \ A_t` of a round. -/
def RoundRecord.rejected {A : Type*} {m : ℕ} (rr : RoundRecord A m) : Finset (Exchange A m) :=
  rr.proposed.filter fun p => !(rr.dec₁ p && rr.dec₂ p)

/-- All exchanges executed in a history (the union of the `A_t`). -/
def executed {A : Type*} [DecidableEq A] {m : ℕ} (H : History A m) : Finset (Exchange A m) :=
  H.foldr (fun rr acc => rr.accepted ∪ acc) ∅

/-- The set `D_t` of proposals rejected by at least one participant so far, p.14
(`D_0 = ∅`, `D_t = D_{t−1} ∪ (P_t \ A_t)`). -/
def rejectedSet {A : Type*} [DecidableEq A] {m : ℕ} (H : History A m) : Finset (Exchange A m) :=
  H.foldr (fun rr acc => rr.rejected ∪ acc) ∅

/-- The current allocation after a history, p.14: `x^(t) = x^(t−1)[A_t]`, i.e. `x^(0)` with all
executed exchanges applied (by (6), executing rounds in sequence equals executing their union). -/
noncomputable def alloc {A : Type*} [DecidableEq A] {m : ℕ} (x0 : A → Fin m → Bool)
    (H : History A m) : A → Fin m → Bool :=
  exec x0 (executed H)

/-- The record of the next round: the protocol posts `P_t = M(P, H_{t−1})` and each participant
of each `p ∈ P_t` decides by her strategy, seeing exactly `(p, P, P_t, H_{t−1})` (p.14). -/
def nextRecord {A : Type*} [DecidableEq A] {m : ℕ} (M : Protocol A m) (P : Finset A) (σ : A → Strategy A m)
    (H : History A m) : RoundRecord A m :=
  { proposed := M P H
    dec₁ := fun p => decide (p ∈ M P H) && σ p.i p P (M P H) H
    dec₂ := fun p => decide (p ∈ M P H) && σ p.j p P (M P H) H }

/-- The run of a protocol: the history after `t` rounds. Once the posted set is empty the protocol
has terminated (p.14: "The protocol terminates when `P_t = ∅`") and the history is frozen. -/
def hist {A : Type*} [DecidableEq A] {m : ℕ} (M : Protocol A m) (P : Finset A) (σ : A → Strategy A m) :
    ℕ → History A m
  | 0 => []
  | t + 1 => if M P (hist M P σ t) = ∅ then hist M P σ t
      else hist M P σ t ++ [nextRecord M P σ (hist M P σ t)]

/-- The horizon at which runs are read: the number of quadruples `((i, r), (j, s))`, which
bounds the number of well-formed exchanges and hence (p.14: "There are finitely many
well-formed exchanges. Every proposed exchange is either rejected permanently or executed […]")
the number of nonterminal rounds of a protocol that proposes each exchange at most once. -/
def horizon (A : Type*) [Fintype A] (m : ℕ) : ℕ := Fintype.card (Exchange A m)

/-- The terminal history: the run read at the horizon. -/
def termHist {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ} (M : Protocol A m) (P : Finset A)
    (σ : A → Strategy A m) : History A m :=
  hist M P σ (horizon A m)

/-- The protocol has terminated by the horizon under every participating set and profile: the
proposal set posted after the terminal history is empty. For such a protocol `termHist` is the
history at termination and `xInf` below is the terminal allocation `x^(∞)`. -/
def TerminatesByHorizon {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ} (M : Protocol A m) : Prop :=
  ∀ (P : Finset A) (σ : A → Strategy A m), M P (termHist M P σ) = ∅

/-- The terminal allocation `x^(∞)(M, P, σ_P)`, p.14. -/
noncomputable def xInf {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ} (x0 : A → Fin m → Bool)
    (M : Protocol A m) (P : Finset A) (σ : A → Strategy A m) : A → Fin m → Bool :=
  alloc x0 (termHist M P σ)

/-- `D_∞`, the set of exchanges rejected by at least one participant by termination (p.17). -/
def Dinf {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ} (M : Protocol A m) (P : Finset A)
    (σ : A → Strategy A m) : Finset (Exchange A m) :=
  rejectedSet (termHist M P σ)

/-- The number of nonterminal rounds (rounds with `P_t ≠ ∅`): every recorded round is
nonterminal, since the run stops recording at the first empty proposal set. -/
def nonterminalRounds {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ} (M : Protocol A m) (P : Finset A)
    (σ : A → Strategy A m) : ℕ :=
  (termHist M P σ).length

end FreeReplExchange


