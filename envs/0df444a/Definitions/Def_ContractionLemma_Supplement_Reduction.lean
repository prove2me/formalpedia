-- Prove2me | Definitions.Def_ContractionLemma_Supplement_Reduction
-- name    : ContractionLemma_Supplement_Reduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:17:56.8702+00:00
-- url     : https://prove2.me/theorems/d8be314e-ca86-4cb9-9d95-7eedbc552ec8
-- title:
--   Oracle machines, randomized runs and tensor-preserving reductions (Definition 2.2)
-- statement:
--   A **tensor-preserving reduction** (Definition 2.2) is an algorithm that computes the answer to an instance $x$ of a problem $\Pi$ from contraction values. Here it is a primitive machine $R$ with a query tape, a reply tape and query states: in a query state the oracle reads the word on the query tape and writes its reply on the reply tape, and $R$ continues in the return state. Each oracle step costs one step.
--
--   For an entry machine $E$, a constant $c$, the input length $L=|x|$ and the scale $s=s(L)$, a query is answered correctly when it is the description $I$ of a network $G$ with entries in $R_{P,\ell}$ such that
--
--   1. $G$ has at most $c\,s$ edges;
--   2. $G$ has maximum degree at most $c\,s^{9/10}$;
--   3. $1\le P,\ell\le c\,s$;
--   4. the description has length $N\le c(L+s+1)^c$, and $E$ computes every entry in time $c(L+N+s+1)^c\,2^{c s^{9/10}}$ and space $c(L+N+s+1)^c$;
--
--   and the reply is the word of $Z(G)\in R_{P,\ell}$ (its $\ell$ coefficients). A **deterministic $(s,q,H)$-tensor-preserving reduction** halts on every instance, with these replies, with an admissible answer after at most $H(L)$ steps and $q(L)$ queries, in space at most $c(L+s+1)^c$ outside the evaluations. A **randomized** reduction also reads fair coins, one at a time on request (a query with an empty query tape is answered by a fresh coin; one step and one visited cell per coin; coin requests are not among the $q(L)$ queries); its error bound $\delta(x)$ bounds the probability over the coins that the answer computed with exact replies is not admissible. A **randomized run** of an algorithm within time $\tau$ and space $\sigma$ is a run of such a machine with coins and no other oracle: for every coin string in $\{0,1\}^{\lceil\tau\rceil}$ it halts within the bounds with an output that is never forbidden (one-sided error), and the fraction of coin strings whose output is wrong is at most $\delta$.
--
--   This is the interface of the meta-theorem (Theorem 2.3), through which every algorithm of the paper is written.
--
--   **Formalization Note** The paper defines no oracle mechanics: a query must be a clean word on the query tape (head on its first cell), the reply replaces the reply tape from its head, and its cells count as visited. Networks are the base mission's explicit-edge-list instances, whose field `input` carries the data passed to the entry machine.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Definition 2.2, p.17; Theorem 2.3, p.17

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_Net
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Instance
import Definitions.Def_ContractionLemma_Supplement_Common

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **A machine with oracle access** — the algorithms of Definition 2.2 (Gajulapalli, *The
Contraction Lemma Beyond ETH*, manuscript sha256 049caea1…, p.17), which compute an answer from
contraction values.

A published `PrimitiveMachine` with a query tape, a reply tape, and query states: in a query state
`q` with `returnState q = some q'` the machine does not take its own transition; instead the oracle
reads the word on the query tape and writes its reply on the reply tape, and the machine continues in
`q'`.

**Formalization Note.** The paper defines no oracle mechanics; this is a declared reading. A query
is the whole content of the query tape, which must be a clean word `w` with the head on its first
cell (`Turing.Tape.mk₁ w`); the reply `y` replaces the reply tape, starting at its head. An oracle
step costs one step, and the reply cells count as visited. -/
structure OracleMachine where
  /-- the underlying machine -/
  machine : PrimitiveMachine
  /-- the query tape -/
  queryTape : Fin machine.tapeCount
  /-- the reply tape -/
  replyTape : Fin machine.tapeCount
  /-- the query states and the states they return to -/
  returnState : Fin machine.stateCount → Option (Fin machine.stateCount)

namespace OracleMachine

/-- One step of an oracle machine, where `reply w y` says that `y` is a correct reply to the query
`w`. A halted configuration has no step. -/
def ostep (O : OracleMachine) (reply : List Bool → List Bool → Prop)
    (c c' : LocatedCfg O.machine) : Prop :=
  match c.config.state with
  | .inl _ => False
  | .inr q =>
    match O.returnState q with
    | none => locatedStep O.machine c = some c'
    | some q' => ∃ w y : List Bool,
        c.config.tapes O.queryTape = Turing.Tape.mk₁ (w.map some) ∧ reply w y ∧
        c' = { config := ⟨.inr q', Function.update c.config.tapes O.replyTape
                  (Turing.Tape.mk₁ (y.map some))⟩
               position := c.position
               lower := Function.update c.lower O.replyTape
                  (min (c.lower O.replyTape) (c.position O.replyTape))
               upper := Function.update c.upper O.replyTape
                  (max (c.upper O.replyTape) (c.position O.replyTape + (y.length : ℤ) - 1)) }

/-- A configuration in a query state. -/
def IsQueryCfg (O : OracleMachine) (c : LocatedCfg O.machine) : Prop :=
  ∃ q, c.config.state = .inr q ∧ (O.returnState q).isSome

open scoped Classical in
/-- **A run of an oracle machine with query-indexed replies**: a sequence of configurations from the
initial one on `input`, each step an `ostep` whose oracle is `reply k` for the index `k` of the query
(the number of earlier query steps), ending after `T ≤ τ` steps in a halted configuration with
`output` on tape `out`, with at most `σ` visited cells at every step and at most `q` oracle steps
with a nonempty query (coin requests, `coinReply`, are not counted among the `q` queries). -/
def ORunWith (O : OracleMachine) (out : Fin O.machine.tapeCount)
    (reply : ℕ → List Bool → List Bool → Prop) (input output : List Bool) (τ σ q : ℝ) : Prop :=
  ∃ (T : ℕ) (run : ℕ → LocatedCfg O.machine),
    run 0 = locatedInit O.machine input ∧
    (∀ i < T, O.ostep (reply ((Finset.range i).filter fun j => O.IsQueryCfg (run j)).card)
      (run i) (run (i + 1))) ∧
    (∃ b : Bool, (run T).config.state = Sum.inl b) ∧
    (run T).config.tapes out = Turing.Tape.mk₁ (output.map some) ∧
    (T : ℝ) ≤ τ ∧
    (∀ i ≤ T, (visitedSpace (run i) : ℝ) ≤ σ) ∧
    (((Finset.range T).filter fun i => O.IsQueryCfg (run i) ∧
      (run i).config.tapes O.queryTape ≠ Turing.Tape.mk₁ []).card : ℝ) ≤ q

/-- **A run of an oracle machine within time `τ`, space `σ` and `q` queries**, every query answered
by the oracle `reply` (`ORunWith` with the same oracle at every query). -/
def ORunsWithin (O : OracleMachine) (out : Fin O.machine.tapeCount)
    (reply : List Bool → List Bool → Prop) (input output : List Bool) (τ σ q : ℝ) : Prop :=
  O.ORunWith out (fun _ => reply) input output τ σ q

/-- **Coins as oracle steps.** A query with an empty query tape (the empty word) is a coin request:
the `k`-th query of the run, if it is a coin request, is answered by the one-bit word `[r k]`; every
other query is answered by `reply`. -/
def coinReply (r : ℕ → Bool) (reply : List Bool → List Bool → Prop) (k : ℕ) (w y : List Bool) :
    Prop :=
  if w = [] then y = [r k] else reply w y

/-- The coin string of length `ρ` extended by `false`. -/
def extCoins {ρ : ℕ} (r : Fin ρ → Bool) : ℕ → Bool := fun k => if h : k < ρ then r ⟨k, h⟩ else false

open scoped Classical in
/-- **A randomized run of an oracle machine** within time `τ`, space `σ` and `q` queries: for every
coin string `r ∈ {0,1}^{⌈τ⌉}` (each coin request reads a fresh bit, one-way; a run of at most `τ` steps
makes fewer than `⌈τ⌉ + 1` requests, so indices below `⌈τ⌉` suffice), the run with coins `r` and
oracle `reply` halts within the bounds with an output satisfying `Ok`, and the fraction of coin strings
whose output fails `Good` is at most `δ`.

**Formalization Note.** Randomness is the paper's coin model (§2.5, p.20: "each of the `T` steps
receives one fair coin"), given on request: a coin costs one step and one visited cell, and coins
already read are not stored unless the machine copies them, so a polynomial-space machine may use
up to `τ` coins. `Ok` expresses errors that are never allowed (one-sided error); `Good` is the event
whose failure probability is bounded. -/
def RandORunsWithin (O : OracleMachine) (out : Fin O.machine.tapeCount)
    (reply : List Bool → List Bool → Prop) (x : List Bool) (τ σ q : ℝ)
    (Ok Good : List Bool → Prop) (δ : ℝ) : Prop :=
  (∀ r : Fin ⌈τ⌉₊ → Bool, ∃ y, Ok y ∧
    O.ORunWith out (coinReply (extCoins r) reply) x y τ σ q) ∧
  ((Finset.univ.filter fun r : Fin ⌈τ⌉₊ → Bool => ∃ y, ¬ Good y ∧
    O.ORunWith out (coinReply (extCoins r) reply) x y τ σ q).card : ℝ) ≤ δ * 2 ^ ⌈τ⌉₊

/-- **A randomized run** (an algorithm with fair coins and no other oracle) within time `τ` and
space `σ`: `RandORunsWithin` with no admissible reply to any nonempty query. -/
def RandRunsWithin (O : OracleMachine) (out : Fin O.machine.tapeCount) (x : List Bool) (τ σ : ℝ)
    (Ok Good : List Bool → Prop) (δ : ℝ) : Prop :=
  O.RandORunsWithin out (fun _ _ => False) x τ σ τ Ok Good δ

end OracleMachine

/-- **A correct contraction reply under the conditions of Definition 2.2** (p.17). For a reduction
with entry machine `E`, constant `c`, original input length `L` and scale `s`, the query `w` is the
description `I.encode` of a network with entries in `R_{P,ℓ}` such that

1. it has at most `c·s` edges (`I.s = s`);
2. its maximum degree is at most `c·s^{9/10}`;
3. `1 ≤ P, ℓ ≤ c·s`;
4. its description has length at most `c (L+s+1)^c`, and `E` computes its entries in time
   `c (L+N+s+1)^c 2^{c s^{9/10}}` and space `c (L+N+s+1)^c`, `N = |I.encode|`;

and the reply `y` is the word of its contraction `Z(G) ∈ R_{P,ℓ}` (its `ℓ` coefficients).

**Formalization Note.** A network is the published base `Instance` (explicit edge list; the field
`input` carries whatever data the reduction passes to the entry machine), its tables are computed by
the fixed entry machine `E` of the reduction (the base reading of "an entry algorithm"), and the
replies are the base `truncWord`. Because `N ≤ c(L+s+1)^c`, the entry bound is `poly(L+s)·2^{O(s^{9/10})}`
as in (iv). -/
def contractionReply (E : PrimitiveMachine) (outE : Fin E.tapeCount) (c L s : ℕ)
    (w y : List Bool) : Prop :=
  ∃ (I : ContractionLemma.Instance) (T : I.Tables (ContractionLemma.TruncPoly I.P)),
    w = I.encode ∧ I.s = s ∧ I.m ≤ c * I.s ∧
    (I.maxDeg : ℝ) ≤ c * (I.s : ℝ) ^ ((9 : ℝ) / 10) ∧
    1 ≤ I.P ∧ I.P ≤ c * I.s ∧ 1 ≤ I.ℓ ∧ I.ℓ ≤ c * I.s ∧
    (I.encode.length : ℝ) ≤ c * ((L : ℝ) + s + 1) ^ c ∧
    I.EntryComputes E outE T
      (c * ((L : ℝ) + I.encode.length + s + 1) ^ c * (2 : ℝ) ^ (c * (s : ℝ) ^ ((9 : ℝ) / 10)))
      (c * ((L : ℝ) + I.encode.length + s + 1) ^ c) ∧
    y = ContractionLemma.truncWord I.ℓ (I.net T).Z

/-- **A deterministic `(s, q, H)`-tensor-preserving reduction for `Π`** (Definition 2.2, p.17), with
oracle machine `R`, entry machine `E` and constant `c`: on every instance `x` (length `L = |x|`) the
machine `R`, whose oracle answers every query by `contractionReply E outE c L (s L)`, halts with an
admissible answer (`Prob x y`, the problem `Π`) after at most `H L` steps and `q L` queries, using space at most
`c (L + s + 1)^c` outside the evaluations. -/
def IsDetReduction (Prob : List Bool → List Bool → Prop) (s q : ℕ → ℕ) (H : ℕ → ℝ)
    (R : OracleMachine) (outR : Fin R.machine.tapeCount)
    (E : PrimitiveMachine) (outE : Fin E.tapeCount) (c : ℕ) : Prop :=
  ∀ x : List Bool, ∃ y, Prob x y ∧
    R.ORunsWithin outR (contractionReply E outE c x.length (s x.length)) x y (H x.length)
      (c * ((x.length : ℝ) + s x.length + 1) ^ c) (q x.length)

/-- **A randomized `(s, q, H)`-tensor-preserving reduction for `Π` with error bound `δ`**
(Definition 2.2 and Theorem 2.3, p.17): as `IsDetReduction`, with fair coins given on request
(`RandORunsWithin`; coin requests are not counted among the `q(L)` queries);
for every instance `x`, the probability over the random string that the answer computed with exact
contraction values is not admissible is at most `δ x`. -/
def IsRandReduction (Prob : List Bool → List Bool → Prop) (s q : ℕ → ℕ) (H : ℕ → ℝ)
    (R : OracleMachine) (outR : Fin R.machine.tapeCount)
    (E : PrimitiveMachine) (outE : Fin E.tapeCount) (c : ℕ) (δ : List Bool → ℝ) : Prop :=
  ∀ x : List Bool,
    R.RandORunsWithin outR (contractionReply E outE c x.length (s x.length)) x (H x.length)
      (c * ((x.length : ℝ) + s x.length + 1) ^ c) (q x.length) (fun _ => True) (Prob x) (δ x)

end ContractionLemma.Supplement


