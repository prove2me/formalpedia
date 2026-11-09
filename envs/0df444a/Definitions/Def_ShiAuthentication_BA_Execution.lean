-- Prove2me | Definitions.Def_ShiAuthentication_BA_Execution
-- name    : ShiAuthentication_BA_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:07:46.898863+00:00
-- url     : https://prove2.me/theorems/9f12bbb5-919b-43d7-a99a-e57a786132ec
-- title:
--   Synchronous executions with idealized signatures, static rushing adversary, Byzantine agreement and broadcast
-- statement:
--   This file fixes the execution model of §3.1.
--
--   1. **Messages and idealized signatures.** Messages are finite symbolic terms built from numbers (bits, names, identifiers), verification-key atoms, signature atoms $\sigma_{vk,m}$ and tuples. Distinct pairs $(vk,m)$ give distinct signatures, and $\mathrm{Verify}(vk,m,\sigma)=1[\sigma=\sigma_{vk,m}]$. A key atom carries no owner. A party or the adversary can derive (Dolev–Yao): every term it has observed, every public atom, tuples and their components, the message inside a signature, and $\sigma_{vk,m}$ for a derivable $m$ only if it holds the signing capability of $vk$.
--   2. **Setup.** Each party $i$ has a designated key $vk_i$; the assignment $i\mapsto vk_i$ is injective. Party $j$ knows its own key and receives the initial key table $KT_j=\{(x,vk_x):x\in K_j\}$ with the *actual* designated keys, also for faulty signers. In the public-graph setting each party additionally receives $G$; in the local-table setting it does not.
--   3. **Protocols.** A deterministic protocol consists of a sending rule and an output rule, both arbitrary functions of the party's initial data ($n$, $t$, its name, own key, key table, input, designated sender, and $G$ when public) and of its view (all messages received so far, round by round, with "no message" distinguished from any message). Honest sends are expressions over the view: public atoms, tuples, components, received (sub)terms, and signatures under the party's own key only. The first defined value of the output rule is the party's irrevocable output.
--   4. **Executions.** Rounds are synchronous; channels are complete and identify the immediate sender. A static adversary fixes $F\subseteq P$ before the execution. A trace is an **execution** if every honest party sends what the protocol prescribes for its view, and every message from a corrupted party to an honest party in round $r$ is derivable from all honest messages of rounds $\le r$ (rushing) with the capabilities of every key that is not an honest party's designated key (corrupted parties' keys and fresh keys).
--   5. **Byzantine agreement (Definition 3.2).** A protocol solves BA on $G$ against $t$ faults with public round bound $T$ if, for every input assignment, every injective key assignment, every $F$ with $|F|\le t$ and every execution: every honest party outputs by round $T$ (termination); all honest outputs agree (agreement); if all honest inputs equal $b$, every honest output equals $b$ (validity). **BA is possible on $G$** if some protocol and some $T$ achieve this.
--   6. **Byzantine broadcast (Definition 3.1).** Only the designated sender $S$ has an input bit $b$. Consistency is agreement, and validity requires that every honest output equals $b$ when $S$ is honest. $BB(G,S,t)$ asks for a public round bound; the eventual variant only asks that every honest party outputs at some finite round.
--
--   These definitions are the semantic content of every theorem of the mission: feasibility is quantified over all deterministic protocols, all key assignments, all fault sets and all admissible adversaries, and nothing about the three-set condition is built in.
--
--   **Formalization Note** Parties are `Fin n`; inside a party's local data they are the names $0,\dots,n-1$. A trace assigns to each round, sender and recipient an optional message; messages between corrupted parties are unconstrained and irrelevant. Honest parties' sends are values of the expression type `Expr`, which has no signature literal: the only way to create a signature is `signOwn`, the use of the party's own capability. The adversary sees every honest message of the current and earlier rounds before choosing its own.
--
--   **Encoding and invocation convention (moderation repair).** Each execution carries a fresh public root session identifier and a public encoding word budget κ. Every signed call context includes that session, the designated sender when present, protocol tag, phase, subcall, message type, signer, and public graph when supplied. The call and message type determine its scheduled round. Correctness quantifies over every session and every compatible budget: the fixed binary codes of n, t, session and all designated keys have length at most κ. Every finite injective key assignment admits arbitrarily large compatible budgets, so no assignment is excluded and the key universe is unbounded. Adversarial keys and messages have no size bound. The impossibility quantifier deliberately also includes noncomputable deterministic rules; the efficient construction must supply an actual Turing machine.
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), §3.1 pp. 15–16 (model, idealized signatures, adversary and correctness), Definition 3.1 and Definition 3.2, p. 16

import Definitions.Def_ShiAuthentication_BA_Graph

set_option autoImplicit false

namespace ShiAuthentication.BA

/-! # Messages, idealized signatures, deterministic protocols and executions

Shi, STOC 2027 submission #203, §3.1 (pp. 15–16): synchronous complete network with
sender-authenticated channels, idealized (Dolev–Yao) signatures, designated keys and initial key
tables given by the authentication graph, a static rushing adversary, Definitions 3.1 (Byzantine
broadcast) and 3.2 (Byzantine agreement). -/

/-- Messages: finite symbolic terms. `num k` is a number (bit, party name, identifier, tag),
`key k` a verification-key atom, `sig k m` the signature atom `σ_{vk,m}` of the message `m` under
the verification key `k`; `nil`/`cons` build tuples and lists. Distinct pairs `(k, m)` give
distinct signature atoms (constructor injectivity). A key atom carries no owner. -/
inductive Msg where
  | num : ℕ → Msg
  | key : ℕ → Msg
  | sig : ℕ → Msg → Msg
  | nil : Msg
  | cons : Msg → Msg → Msg
  deriving DecidableEq

/-- Self-delimiting binary code of a natural number: each binary digit (least significant
first) is preceded by `true`, and the code ends with `false`. -/
def encNat (k : ℕ) : List Bool :=
  (Nat.bits k).flatMap (fun d => [true, d]) ++ [false]

/-- Unary code `1^k 0`. -/
def encUnary (k : ℕ) : List Bool :=
  List.replicate k true ++ [false]

/-- Code of a list: each element preceded by `true`, then a final `false`. -/
def encList {α : Type} (e : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (fun a => true :: e a) ++ [false]

/-- Code of an option: `none ↦ [false]`, `some a ↦ true :: e a`. -/
def encOption {α : Type} (e : α → List Bool) : Option α → List Bool
  | none => [false]
  | some a => true :: e a

/-- Code of a pair of numbers. -/
def encPair (p : ℕ × ℕ) : List Bool :=
  encNat p.1 ++ encNat p.2

/-- Prefix-free code of a message term (3-bit constructor tags). -/
def encMsg : Msg → List Bool
  | .num k => [false, false, false] ++ encNat k
  | .key k => [false, false, true] ++ encNat k
  | .sig k m => [false, true, false] ++ encNat k ++ encMsg m
  | .nil => [false, true, true]
  | .cons a b => [true, false, false] ++ encMsg a ++ encMsg b

/-- `Verify(vk, m, σ) = 1[σ = σ_{vk,m}]` (p. 15); any other input is rejected. -/
def verify (k : ℕ) (m σ : Msg) : Bool := decide (σ = Msg.sig k m)

/-- Dolev–Yao derivability. From the set of observed terms `K` and the signing capabilities
`cap` one can derive: observed terms, all public atoms (numbers, verification keys, `nil`),
tuples and their components, the message inside a signature, and `σ_{k,m}` for a derivable `m`
**only when** the capability for `k` is held. A signature under a key without capability is
obtainable only by having observed a term containing it. -/
inductive Derivable (cap : ℕ → Prop) (K : Set Msg) : Msg → Prop
  | known {m : Msg} : m ∈ K → Derivable cap K m
  | num (k : ℕ) : Derivable cap K (.num k)
  | key (k : ℕ) : Derivable cap K (.key k)
  | nil : Derivable cap K .nil
  | cons {a b : Msg} : Derivable cap K a → Derivable cap K b → Derivable cap K (.cons a b)
  | fst {a b : Msg} : Derivable cap K (.cons a b) → Derivable cap K a
  | snd {a b : Msg} : Derivable cap K (.cons a b) → Derivable cap K b
  | body {k : ℕ} {m : Msg} : Derivable cap K (.sig k m) → Derivable cap K m
  | sign {k : ℕ} {m : Msg} : cap k → Derivable cap K m → Derivable cap K (.sig k m)

/-- A party's local view at the start of round `r`: entry `[r'][i]` is the message received in
round `r' < r` on the channel from party `i` (`none` = no message). Its length is the current
round number. -/
abbrev View := List (List (Option Msg))

/-- Outgoing-message expressions of an honest party. An honest party cannot write a signature
atom: it may use public atoms, tuples, components, (sub)terms of messages it has received
(`recv r i`, the message received in round `r` from `i`), and signatures under its **own**
designated key (`signOwn`, the use of its signing capability). This is exactly Dolev–Yao
derivability from the party's knowledge with its own capability only. -/
inductive Expr where
  | num : ℕ → Expr
  | key : ℕ → Expr
  | nil : Expr
  | cons : Expr → Expr → Expr
  | recv : ℕ → ℕ → Expr
  | fst : Expr → Expr
  | snd : Expr → Expr
  | body : Expr → Expr
  | signOwn : Expr → Expr
  deriving DecidableEq

/-- The value of an outgoing expression for the party with own key `own` and view `v`.
Components of non-tuples, bodies of non-signatures and absent messages evaluate to `nil`. -/
def Expr.eval (own : ℕ) (v : View) : Expr → Msg
  | .num k => .num k
  | .key k => .key k
  | .nil => .nil
  | .cons a b => .cons (Expr.eval own v a) (Expr.eval own v b)
  | .recv r i => ((v.getD r []).getD i none).getD .nil
  | .fst a => match Expr.eval own v a with
      | .cons x _ => x
      | _ => .nil
  | .snd a => match Expr.eval own v a with
      | .cons _ y => y
      | _ => .nil
  | .body a => match Expr.eval own v a with
      | .sig _ m => m
      | _ => .nil
  | .signOwn a => .sig own (Expr.eval own v a)

/-- Everything an honest party initially holds (p. 15): `n` and `t`, its own name, its own
designated key (known for free; the capability for it is used through `Expr.signOwn`), its
initial key table `KT_j = {(x, vk_x) : x ∈ K_j}` listed by increasing `x`, its input (`none` for a
non-sender in broadcast), the designated sender of a broadcast instance (`none` for agreement),
and, only in the public-graph setting, the edge list of `G`. -/
structure LocalInit where
  /-- Public fresh root invocation identifier. -/
  session : ℕ
  /-- Public encoding word budget (the source O(κ) convention). -/
  κ : ℕ
  n : ℕ
  t : ℕ
  self : ℕ
  ownKey : ℕ
  table : List (ℕ × ℕ)
  input : Option Bool
  sender : Option ℕ
  graph : Option (List (ℕ × ℕ))
  deriving DecidableEq

/-- A deterministic protocol with outputs in `O`. In each round an honest party's sends are a
function of its initial data and its view at the start of the round (entry `j` of `send` is the
message to party `j`, `none` = silent). `decide` gives the party's output once it is `some`;
the first `some` along the execution is the party's irrevocable output. Both are arbitrary
functions (the impossibility claims deliberately cover even noncomputable rules): no correctness, finiteness of computation or knowledge of `G` beyond `LocalInit` is
built in. -/
structure Protocol (O : Type) where
  send : LocalInit → View → List (Option Expr)
  decide : LocalInit → View → Option O

/-- Exact fixed BA schedule: a decision is available precisely after the last of the
5(t+1) rounds. The first available decision is irrevocable by `Outputs`. This condition is
asserted of the construction, never assumed for arbitrary protocols in impossibility claims. -/
def Protocol.ExactBARounds (P : Protocol Bool) : Prop :=
  ∀ (I : LocalInit) (v : View), (P.decide I v).isSome = true ↔ 5 * (I.t + 1) ≤ v.length

/-- The two knowledge settings: `G` public (every party gets its edge list), or local key tables
only (`G` is not an input; the protocol is a fixed object not depending on `G`). -/
inductive Knowledge where
  | publicGraph
  | localTables
  deriving DecidableEq

/-- The data of one execution: fault bound `t`, knowledge setting, authentication graph,
designated key assignment `vk`, inputs, designated sender (broadcast) and the static fault set
`F`. Admissibility (`vk` injective, `|F| ≤ t`) is imposed where executions are quantified. -/
structure Setup (n : ℕ) where
  session : ℕ
  κ : ℕ
  t : ℕ
  mode : Knowledge
  G : AuthGraph n
  vk : Fin n → ℕ
  input : Fin n → Option Bool
  sender : Option (Fin n)
  F : Finset (Fin n)

namespace Setup

variable {n : ℕ}

/-- The edge list of `G`. -/
def edgeList (s : Setup n) : List (ℕ × ℕ) :=
  (List.finRange n).flatMap fun x =>
    (List.finRange n).filterMap fun y => if s.G.adj x y then some (x.val, y.val) else none

/-- The initial key table `KT_i = {(x, vk_x) : x ∈ K_i}` with the **actual** designated keys
(also for faulty signers). -/
def table (s : Setup n) (i : Fin n) : List (ℕ × ℕ) :=
  (List.finRange n).filterMap fun x => if s.G.adj x i then some (x.val, s.vk x) else none

/-- Party `i`'s initial data. -/
def init (s : Setup n) (i : Fin n) : LocalInit where
  session := s.session
  κ := s.κ
  n := n
  t := s.t
  self := i.val
  ownKey := s.vk i
  table := s.table i
  input := s.input i
  sender := s.sender.map Fin.val
  graph := match s.mode with
    | .publicGraph => some s.edgeList
    | .localTables => none

/-- Fix the source's O(κ) encoding convention: all designated key atoms and identifiers
have at most κ bits in `encNat`. This is only a choice of encoding budget, not a restriction
on the key universe: every finite injective assignment and session admits arbitrarily large
such budgets. Signature terms used by Protocols 1–3 then have O(κ) encoded size, with a fixed
absolute coefficient; rescaling κ once makes it a signature-size bound as on p.15.
Adversarial messages and adversarial keys have no size restriction. -/
def EncodingOK (s : Setup n) : Prop :=
  1 ≤ s.κ ∧ (encNat n).length ≤ s.κ ∧ (encNat s.t).length ≤ s.κ ∧
    (encNat s.session).length ≤ s.κ ∧ ∀ i : Fin n, (encNat (s.vk i)).length ≤ s.κ

end Setup

/-- An execution trace: `tr r i j` is the message sent in round `r` on the channel from `i` to `j`
(the channel identifies the immediate sender). -/
abbrev Trace (n : ℕ) := ℕ → Fin n → Fin n → Option Msg

/-- The view of party `j` at the start of round `r`. -/
def viewAt {n : ℕ} (tr : Trace n) (j : Fin n) (r : ℕ) : View :=
  (List.range r).map fun r' => (List.finRange n).map fun i => tr r' i j

/-- What the adversary has observed by the end of the sending phase of round `r`: every message
sent by an honest party in rounds `≤ r` (rushing: the honest messages of round `r` are seen before
the corrupted parties' round-`r` messages are chosen). -/
def advKnowledge {n : ℕ} (s : Setup n) (tr : Trace n) (r : ℕ) : Set Msg :=
  {m | ∃ r' ≤ r, ∃ i : Fin n, i ∉ s.F ∧ ∃ j : Fin n, tr r' i j = some m}

/-- The adversary's signing capabilities: those of the corrupted parties' designated keys and of
any fresh key it creates, i.e. of every key that is not an honest party's designated key. -/
def advCap {n : ℕ} (s : Setup n) (k : ℕ) : Prop :=
  ∀ h : Fin n, h ∉ s.F → s.vk h ≠ k

/-- The message honest party `i` sends to `j` in round `r` of trace `tr`. -/
def honestMsg {n : ℕ} {O : Type} (P : Protocol O) (s : Setup n) (tr : Trace n) (r : ℕ)
    (i j : Fin n) : Option Msg :=
  ((P.send (s.init i) (viewAt tr i r)).getD j.val none).map
    (Expr.eval (s.vk i) (viewAt tr i r))

/-- `tr` is an admissible execution of `P` on `s`: honest parties follow the protocol, and every
message a corrupted party sends to an honest party is derivable by the adversary at that time.
(Messages between corrupted parties are irrelevant and unconstrained.) The adversary knows all
designated verification keys (public atoms) and is otherwise arbitrary. -/
def IsRun {n : ℕ} {O : Type} (P : Protocol O) (s : Setup n) (tr : Trace n) : Prop :=
  (∀ r : ℕ, ∀ i j : Fin n, i ∉ s.F → tr r i j = honestMsg P s tr r i j) ∧
  (∀ r : ℕ, ∀ i j : Fin n, i ∈ s.F → j ∉ s.F → ∀ m : Msg, tr r i j = some m →
    Derivable (advCap s) (advKnowledge s tr r) m)

/-- Party `j`'s (irrevocable) output in `tr` is `o`: the first round at which `decide` is defined
gives `o`. -/
def Outputs {n : ℕ} {O : Type} (P : Protocol O) (s : Setup n) (tr : Trace n) (j : Fin n)
    (o : O) : Prop :=
  ∃ r : ℕ, P.decide (s.init j) (viewAt tr j r) = some o ∧
    ∀ r' < r, P.decide (s.init j) (viewAt tr j r') = none

/-- Party `j` has output by round `T`. -/
def DecidedBy {n : ℕ} {O : Type} (P : Protocol O) (s : Setup n) (tr : Trace n) (j : Fin n)
    (T : ℕ) : Prop :=
  ∃ r ≤ T, (P.decide (s.init j) (viewAt tr j r)).isSome

/-- Setup in which every party `i` has input bit `b i` and there is no designated sender (used for
`Π_Confirm`, `Π_GBA` and agreement). -/
def baSetup {n : ℕ} (mode : Knowledge) (G : AuthGraph n) (t : ℕ) (vk : Fin n → ℕ)
    (b : Fin n → Bool) (F : Finset (Fin n)) (session κ : ℕ) : Setup n :=
  ⟨session, κ, t, mode, G, vk, fun i => some (b i), none, F⟩

/-- Broadcast setup: the designated sender `S` has input bit `c`; nobody else has an input. -/
def bbSetup {n : ℕ} (mode : Knowledge) (G : AuthGraph n) (t : ℕ) (vk : Fin n → ℕ)
    (S : Fin n) (c : Bool) (F : Finset (Fin n)) (session κ : ℕ) : Setup n :=
  ⟨session, κ, t, mode, G, vk, fun i => if i = S then some c else none, some S, F⟩

/-- Definition 3.2 (p. 16): `P` solves Byzantine agreement on `G` with fault bound `t` and
public round bound `T`: for every input assignment, every assignment of pairwise distinct
designated keys, every fault set with `|F| ≤ t` and every admissible execution,
termination by round `T`, agreement, and validity hold for the honest parties `H`, the complement of `F` in the party set (here `P` names the protocol). -/
def SolvesBA {n : ℕ} (P : Protocol Bool) (mode : Knowledge) (t : ℕ) (G : AuthGraph n)
    (T : ℕ) : Prop :=
  ∀ (vk : Fin n → ℕ), Function.Injective vk → ∀ (b : Fin n → Bool) (F : Finset (Fin n)),
    F.card ≤ t → ∀ session κ : ℕ, (baSetup mode G t vk b F session κ).EncodingOK →
    ∀ tr : Trace n, IsRun P (baSetup mode G t vk b F session κ) tr →
      (∀ j : Fin n, j ∉ F → DecidedBy P (baSetup mode G t vk b F session κ) tr j T) ∧
      (∀ j k : Fin n, j ∉ F → k ∉ F → ∀ o o' : Bool,
        Outputs P (baSetup mode G t vk b F session κ) tr j o →
        Outputs P (baSetup mode G t vk b F session κ) tr k o' → o = o') ∧
      (∀ c : Bool, (∀ j : Fin n, j ∉ F → b j = c) →
        ∀ j : Fin n, j ∉ F → ∀ o : Bool, Outputs P (baSetup mode G t vk b F session κ) tr j o → o = c)

/-- "Byzantine agreement is possible on `G`" in the given knowledge setting: some deterministic
protocol with some public finite round bound solves it. -/
def BAPossible {n : ℕ} (mode : Knowledge) (t : ℕ) (G : AuthGraph n) : Prop :=
  ∃ (P : Protocol Bool) (T : ℕ), SolvesBA P mode t G T

/-- Correctness of a broadcast protocol from sender `S` (Definition 3.1, p. 16), with the
termination requirement passed as a predicate `term` on (setup, trace, honest party). -/
def BBCorrect {n : ℕ} (P : Protocol Bool) (mode : Knowledge) (t : ℕ) (G : AuthGraph n)
    (S : Fin n) (term : Setup n → Trace n → Fin n → Prop) : Prop :=
  ∀ (vk : Fin n → ℕ), Function.Injective vk → ∀ (c : Bool) (F : Finset (Fin n)),
    F.card ≤ t → ∀ session κ : ℕ, (bbSetup mode G t vk S c F session κ).EncodingOK →
    ∀ tr : Trace n, IsRun P (bbSetup mode G t vk S c F session κ) tr →
      (∀ j : Fin n, j ∉ F → term (bbSetup mode G t vk S c F session κ) tr j) ∧
      (∀ j k : Fin n, j ∉ F → k ∉ F → ∀ o o' : Bool,
        Outputs P (bbSetup mode G t vk S c F session κ) tr j o →
        Outputs P (bbSetup mode G t vk S c F session κ) tr k o' → o = o') ∧
      (S ∉ F → ∀ j : Fin n, j ∉ F → ∀ o : Bool,
        Outputs P (bbSetup mode G t vk S c F session κ) tr j o → o = c)

/-- `BB(G, S, t)` (Definition 3.1): some deterministic protocol with a public finite round bound
`T` solves broadcast from `S`. -/
def BBPossible {n : ℕ} (mode : Knowledge) (t : ℕ) (G : AuthGraph n) (S : Fin n) : Prop :=
  ∃ (P : Protocol Bool) (T : ℕ), BBCorrect P mode t G S (fun s tr j => DecidedBy P s tr j T)

/-- `P` solves broadcast from `S` with **eventual** termination only: every honest party outputs
at some finite round, with no public bound (Lemma 4.2). -/
def SolvesBBEventually {n : ℕ} (P : Protocol Bool) (mode : Knowledge) (t : ℕ)
    (G : AuthGraph n) (S : Fin n) : Prop :=
  BBCorrect P mode t G S (fun s tr j => ∃ T : ℕ, DecidedBy P s tr j T)

end ShiAuthentication.BA


