-- Prove2me | Definitions.Def_ContractionLemma_Supplement_LocalMachine
-- name    : ContractionLemma_Supplement_LocalMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:18:37.168714+00:00
-- url     : https://prove2.me/theorems/64c34374-eb04-4e97-a365-eb527a4a1d33
-- title:
--   Local machines with coins, nondeterministic paths and oracles (§2.5)
-- statement:
--   **Local machines** (§2.5). Fix a number of tapes $k$, a tape alphabet $\Gamma$, a bound $d_0$ on head movement per step and a constant $C_0$. A program is an explicit transition table: in each non-halting state, the transition reads the $k$ scanned symbols and either performs one local update (deterministic step) or chooses one of two labeled local updates by its choice bit. A local update sets the next state, writes a symbol under each head and moves each head by at most $d_0$ cells. Halting states are absorbing, and each carries an accept bit and a postselection bit. The input, and any advice or witness, are on tapes.
--
--   An **oracle program** has a query tape and oracle states: an oracle step reads the delimited prefix of the query tape (the bits from its first cell up to the first non-bit) and moves to one of two states according to the one-bit reply, without moving any head.
--
--   The run for $T$ steps is determined by the input and the choice string $\gamma\in\{0,1\}^T$; it accepts if at time $T$ it is in an accepting halting state.
--
--   1. The number of **accepting coin strings** is $A=\#\{\gamma\in\{0,1\}^T:\text{the run accepts}\}$; deterministic, oracle and halted steps ignore their coin, so $\Pr[\text{accept by time }T]=2^{-T}A$.
--   2. The number of **accepting nondeterministic paths** counts the accepting $\gamma$ whose bits at deterministic, oracle and halted steps are $0$, so each path is counted once.
--
--   A program is encoded by its full transition table; with the input, the auxiliary word and $T$ this is the description of length $L$ of Theorems 10 and 8.2.
--
--   **Formalization Note** The alphabet is $\mathrm{Fin}(\gamma+3)$ with $0$ the blank and $1,2$ the bits. Tapes are indexed by $\mathbb Z$ and every head starts at cell $0$. A machine without oracle is run with the empty oracle, so its oracle states, if any, are deterministic steps.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), §2.5, p.20 ("Local machines"); §8.1, p.36

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_Supplement_Common

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **The fixed parameters of local machines** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), §2.5, p.20: "Fix a number of tapes `k`, a tape alphabet `Γ`, a bound
`d₀` on head movement per step, and a constant `C₀`."

**Formalization Note.** The alphabet is `Fin (γ + 3)`: symbol `0` is the blank and symbols `1`, `2`
are the bits `0`, `1` (the input, advice, witness, query and output words are written with them);
`γ` further symbols are free. -/
structure LocalParams where
  /-- the number of tapes `k` -/
  k : ℕ
  /-- the number of symbols besides blank and the two bits -/
  γ : ℕ
  /-- the head-movement bound `d₀` -/
  d0 : ℕ
  /-- the state-count exponent `C₀` -/
  C0 : ℕ

namespace LocalParams

/-- The tape alphabet `Γ`. -/
abbrev Sym (p : LocalParams) := Fin (p.γ + 3)

/-- The blank symbol. -/
def blank (p : LocalParams) : p.Sym := ⟨0, by omega⟩

/-- The symbol of a bit. -/
def bitSym (p : LocalParams) (b : Bool) : p.Sym := if b then ⟨2, by omega⟩ else ⟨1, by omega⟩

/-- Is the symbol a bit? -/
def isBit (p : LocalParams) (a : p.Sym) : Bool := decide (a.val = 1 ∨ a.val = 2)

/-- The cell `i` of a tape holding the word `w` from cell `0` on, blank elsewhere. -/
def wordCell (p : LocalParams) (w : List Bool) (i : ℤ) : p.Sym :=
  if 0 ≤ i ∧ i < w.length then p.bitSym (w.getD i.toNat false) else p.blank

end LocalParams

/-- **A local update** (§2.5, p.20): the next state, the symbol written under each head, and the
move of each head, `move j − d₀ ∈ [−d₀, d₀]`. -/
structure LUpdate (p : LocalParams) (Q : ℕ) where
  /-- next state -/
  next : Fin Q
  /-- the symbol written under each head -/
  write : Fin p.k → p.Sym
  /-- the move of each head, shifted by `d₀` -/
  move : Fin p.k → Fin (2 * p.d0 + 1)

/-- **A local program** (§2.5, p.20): "an explicit transition table with at most `(T + 2)^{C₀}`
states, in which each transition reads the `k` scanned symbols and chooses one of at most two labeled
local updates. The input, and any advice or witness, are on tapes … Halting states are absorbing."
An oracle program "has a query tape among its tapes. An oracle step reads a delimited prefix of the
query tape and puts the one-bit reply into the state, without moving any head."

Fields: `Q` states; a start state; halting states with an accept bit and a postselection bit
(Definition 2.8, PostBPTIME); universal states (Σ₂TIME); the input, auxiliary (advice or witness),
query and output tapes; the oracle states (`query q = some (q₁, q₀)`: continue in `q₁` on reply `1`,
in `q₀` on reply `0`); and the transition table, `inl u` for a deterministic step and `inr (u₀, u₁)`
for a step that chooses update `u_b` on choice bit `b`.

**Formalization Note.** The state bound `(T+2)^{C₀}` is imposed where a program is an input
(Theorems 10, 8.2). Oracle and non-oracle machines share the structure; a machine without oracle is
run with the empty oracle, so an oracle state is then one deterministic step. -/
structure LProgram (p : LocalParams) where
  /-- the number of states -/
  Q : ℕ
  /-- the start state -/
  start : Fin Q
  /-- halting states -/
  halting : Fin Q → Bool
  /-- accept bit of a halting state -/
  accept : Fin Q → Bool
  /-- postselection bit of a halting state -/
  post : Fin Q → Bool
  /-- universal states (alternating machines) -/
  univ : Fin Q → Bool
  /-- the input tape -/
  inTape : Fin p.k
  /-- the advice/witness tape -/
  auxTape : Fin p.k
  /-- the query tape -/
  queryTape : Fin p.k
  /-- the output tape -/
  outTape : Fin p.k
  /-- oracle states -/
  query : Fin Q → Option (Fin Q × Fin Q)
  /-- the transition table -/
  delta : Fin Q → (Fin p.k → p.Sym) → LUpdate p Q ⊕ (LUpdate p Q × LUpdate p Q)

/-- **A configuration**: the state, the contents of the `k` tapes (indexed by `ℤ`), the head
positions. -/
structure LCfg (p : LocalParams) (M : LProgram p) where
  /-- state -/
  state : Fin M.Q
  /-- tape contents -/
  tape : Fin p.k → ℤ → p.Sym
  /-- head positions -/
  head : Fin p.k → ℤ

namespace LProgram

variable {p : LocalParams}

/-- The initial configuration on input `x` with auxiliary word `aux` (advice or witness): `x` on the
input tape and `aux` on the auxiliary tape from cell `0`, all other cells blank, heads at `0`. -/
def init (M : LProgram p) (x aux : List Bool) : LCfg p M where
  state := M.start
  tape j i := if j = M.inTape then p.wordCell x i
    else if j = M.auxTape then p.wordCell aux i else p.blank
  head _ := 0

/-- The scanned symbols. -/
def scanned (M : LProgram p) (c : LCfg p M) : Fin p.k → p.Sym := fun j => c.tape j (c.head j)

/-- The delimited query: the bits on the query tape from cell `0` up to the first cell that does not
hold a bit, read among the first `B` cells. -/
def queryWord (M : LProgram p) (c : LCfg p M) (B : ℕ) : List Bool :=
  (((List.range B).map fun i => c.tape M.queryTape (i : ℤ)).takeWhile p.isBit).map
    fun a => decide (a.val = 2)

/-- Apply a local update. -/
def applyUpd (M : LProgram p) (c : LCfg p M) (u : LUpdate p M.Q) : LCfg p M where
  state := u.next
  tape j i := if i = c.head j then u.write j else c.tape j i
  head j := c.head j + ((u.move j : ℕ) : ℤ) - p.d0

/-- Is the step from `c` a choice step (a non-halted, non-oracle step with two labeled updates)?
Deterministic, oracle and halted steps ignore their coin. -/
def IsChoiceStep (M : LProgram p) (c : LCfg p M) : Prop :=
  M.halting c.state = false ∧ M.query c.state = none ∧ (M.delta c.state (M.scanned c)).isRight

open scoped Classical in
/-- **One step** with oracle `A`, query-reading bound `B` and choice bit `b`. Halting states are
absorbing; an oracle step only changes the state, according to `A` on the delimited query. -/
noncomputable def step (M : LProgram p) (A : List Bool → Prop) (B : ℕ) (b : Bool)
    (c : LCfg p M) : LCfg p M :=
  if M.halting c.state then c else
  match M.query c.state with
  | some (q₁, q₀) => { c with state := if A (M.queryWord c B) then q₁ else q₀ }
  | none =>
    match M.delta c.state (M.scanned c) with
    | .inl u => M.applyUpd c u
    | .inr (u₀, u₁) => M.applyUpd c (if b then u₁ else u₀)

/-- The query-reading bound for a run of `T` steps on `x`, `aux`: beyond it every cell of every tape
is blank, so the delimited query is read in full. -/
def readBound (_M : LProgram p) (x aux : List Bool) (T : ℕ) : ℕ :=
  x.length + aux.length + p.d0 * T + 1

/-- **The run** for `T` steps with oracle `A` and choice string `γ` (step `t` reads `γ t`). -/
noncomputable def run (M : LProgram p) (A : List Bool → Prop) (x aux : List Bool) (T : ℕ)
    (γ : ℕ → Bool) : ℕ → LCfg p M
  | 0 => M.init x aux
  | t + 1 => M.step A (M.readBound x aux T) (γ t) (M.run A x aux T γ t)

/-- The choice string of length `T` extended by `false`. -/
def ext {T : ℕ} (γ : Fin T → Bool) : ℕ → Bool := fun t => if h : t < T then γ ⟨t, h⟩ else false

/-- The run accepts by time `T`: at time `T` it is in an accepting halting state. -/
def AcceptsAt (M : LProgram p) (A : List Bool → Prop) (x aux : List Bool) (T : ℕ)
    (γ : ℕ → Bool) : Prop :=
  M.halting (M.run A x aux T γ T).state = true ∧ M.accept (M.run A x aux T γ T).state = true

/-- The run is postselected by time `T`: at time `T` it is in a halting state with postselection
bit `1`. -/
def PostAt (M : LProgram p) (A : List Bool → Prop) (x aux : List Bool) (T : ℕ)
    (γ : ℕ → Bool) : Prop :=
  M.halting (M.run A x aux T γ T).state = true ∧ M.post (M.run A x aux T γ T).state = true

/-- A choice string is a nondeterministic path: its bits at deterministic, oracle and halted steps are
`0` (§2.5, p.20, "the coins at deterministic and halted steps are pinned to 0"). -/
def IsPath (M : LProgram p) (A : List Bool → Prop) (x aux : List Bool) (T : ℕ)
    (γ : ℕ → Bool) : Prop :=
  ∀ t < T, ¬ M.IsChoiceStep (M.run A x aux T γ t) → γ t = false

open scoped Classical in
/-- **The number of accepting coin strings** `A` (§2.5): `Pr[accept by time T] = 2^{−T} A`. -/
noncomputable def coinCount (M : LProgram p) (A : List Bool → Prop) (x aux : List Bool) (T : ℕ) : ℕ :=
  (Finset.univ.filter fun γ : Fin T → Bool => M.AcceptsAt A x aux T (ext γ)).card

open scoped Classical in
/-- The number of coin strings that are postselected and accept. -/
noncomputable def postAcceptCount (M : LProgram p) (A : List Bool → Prop) (x aux : List Bool)
    (T : ℕ) : ℕ :=
  (Finset.univ.filter fun γ : Fin T → Bool =>
    M.AcceptsAt A x aux T (ext γ) ∧ M.PostAt A x aux T (ext γ)).card

open scoped Classical in
/-- The number of postselected coin strings. -/
noncomputable def postCount (M : LProgram p) (A : List Bool → Prop) (x aux : List Bool) (T : ℕ) : ℕ :=
  (Finset.univ.filter fun γ : Fin T → Bool => M.PostAt A x aux T (ext γ)).card

open scoped Classical in
/-- **The number of accepting nondeterministic paths** `#M(x)` (§2.5, Definition 2.8). -/
noncomputable def pathCount (M : LProgram p) (A : List Bool → Prop) (x aux : List Bool) (T : ℕ) : ℕ :=
  (Finset.univ.filter fun γ : Fin T → Bool =>
    M.IsPath A x aux T (ext γ) ∧ M.AcceptsAt A x aux T (ext γ)).card

/-- The acceptance probability `p_M(x) = 2^{−T} A` with fair coins. -/
noncomputable def accProb (M : LProgram p) (A : List Bool → Prop) (x aux : List Bool) (T : ℕ) : ℝ :=
  (M.coinCount A x aux T : ℝ) / 2 ^ T

/-- A deterministic program: every transition has a single update. -/
def IsDet (M : LProgram p) : Prop := ∀ q a, (M.delta q a).isLeft

/-- The query lengths of a run of `T` steps are at most `qb`: at every oracle step before time `T`,
for every choice string, the delimited query has length at most `qb`. -/
def QueriesBounded (M : LProgram p) (A : List Bool → Prop) (x aux : List Bool) (T : ℕ)
    (qb : ℝ) : Prop :=
  ∀ (γ : ℕ → Bool) (t : ℕ), t < T →
    M.halting (M.run A x aux T γ t).state = false →
    (M.query (M.run A x aux T γ t).state).isSome →
    ((M.queryWord (M.run A x aux T γ t) (M.readBound x aux T)).length : ℝ) ≤ qb

open scoped Classical in
/-- The number of oracle steps in the deterministic run of `t` steps (choice bits `0`). -/
noncomputable def queryCount (M : LProgram p) (A : List Bool → Prop) (x aux : List Bool) (t : ℕ) :
    ℕ :=
  ((Finset.range t).filter fun i =>
    M.halting (M.run A x aux t (fun _ => false) i).state = false ∧
      (M.query (M.run A x aux t (fun _ => false) i).state).isSome).card

/-- The code of a scanned tuple: tuple `a` has code `∑_j a_j |Γ|^j`; `tupleOf` inverts it. -/
def tupleOf (c : ℕ) : Fin p.k → p.Sym := fun j => ⟨c / (p.γ + 3) ^ (j : ℕ) % (p.γ + 3), by
  exact Nat.mod_lt _ (by omega)⟩

/-- The encoding of a local update. -/
def encodeUpd {Q : ℕ} (u : LUpdate p Q) : List Bool :=
  Encoding.encodeList id
    [countWord u.next, Encoding.encodeList (fun j => countWord (u.write j)) (List.finRange p.k),
      Encoding.encodeList (fun j => countWord (u.move j)) (List.finRange p.k)]

/-- **The encoding of a program** (its "explicit transition table"): the number of states, the start
state, the flags of every state, the four distinguished tapes, the oracle table, and for every state
and every scanned tuple (in the order of the codes `0, …, |Γ|^k − 1`) its one or two updates. -/
def encode (M : LProgram p) : List Bool :=
  Encoding.encodeList id
    [countWord M.Q, countWord M.start,
      Encoding.encodeList (fun q => [M.halting q, M.accept q, M.post q, M.univ q])
        (List.finRange M.Q),
      Encoding.encodeList countWord [M.inTape, M.auxTape, M.queryTape, M.outTape],
      Encoding.encodeList (fun q => optWord ((M.query q).map fun r =>
        Encoding.encodeList countWord [r.1, r.2])) (List.finRange M.Q),
      Encoding.encodeList (fun q => Encoding.encodeList (fun c =>
        match M.delta q (tupleOf c) with
        | .inl u => false :: encodeUpd u
        | .inr (u₀, u₁) => true :: Encoding.encodeList id [encodeUpd u₀, encodeUpd u₁])
        (List.range ((p.γ + 3) ^ p.k))) (List.finRange M.Q)]

/-- The input of a simulator: the program, the input word, the auxiliary word and the time bound `T`
(binary). Its length is the description length `L` of Theorems 10 and 8.2. -/
def simInput (M : LProgram p) (x aux : List Bool) (T : ℕ) : List Bool :=
  Encoding.encodeList id [M.encode, x, aux, countWord T]

end LProgram

end ContractionLemma.Supplement


