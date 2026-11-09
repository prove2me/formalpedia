-- Prove2me | Definitions.Def_NKtLB_Machine
-- name    : NKtLB_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:54:15.127512+00:00
-- url     : https://prove2.me/theorems/cffc7a2a-241c-496f-bb59-4f25e4a81a95
-- title:
--   Multi-tape oracle Turing machines with auxiliary, guess and randomness tapes
-- statement:
--   The computational model of the paper. A **machine** $M$ is a multi-tape Turing machine over the alphabet $\Sigma=\{0,1,\bot\}$ (plus a blank symbol). Besides the input tape and $k\ge 0$ work tapes it has three further read-only tapes, holding an **auxiliary string** $x$, a **nondeterministic guess** $w$ and a **random string** $r$, an output tape and an oracle query tape. All heads have *sequential access*: at each step a head stays, moves one cell left, or moves one cell right.
--
--   A run of $M$ on $(\alpha;x;w;r)$ with an oracle $O\subseteq\{0,1\}^*$ starts in the start state with all heads on the first cell. In the query state the machine moves in one step to the state $q_{\mathrm{yes}}$ if the bit string on its query tape lies in $O$, and to $q_{\mathrm{no}}$ otherwise. $M$ **halts within $t$ steps with output $z$** if after at most $t$ transitions it is in its halting state and its output tape holds $z$. $M$ **makes only queries of length at most $\ell$ in its first $t$ steps** if every query issued during those steps has length at most $\ell$.
--
--   This is the model on which all complexity measures of the mission are defined.
--
--   **Formalization Note** A machine has finitely many states `Fin nStates`, four read-only tapes (input, auxiliary, guess, randomness), `works` work tapes, an output tape and a query tape. Tapes are one-way infinite; a left move at the first cell stays. The query string is the longest prefix of $0/1$ cells of the query tape. The halting state is absorbing, so "halts within $t$ steps" is read off the configuration after exactly $t$ steps. `Machine.Computes M T u v` means that $M$, with input $u$, oracle $\emptyset$ and the other tapes empty, halts within $T$ steps with output $v$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21 (and footnote 14)

import Mathlib

namespace NKtLB

/-- **Tape symbols** of the computational model (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and
Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026),
§3.2, p.21): "multi-tape Turing machines over the alphabet Σ = {0, 1, ⊥}", together with the
blank symbol of unused cells.

**Formalization Note.** The tape alphabet is exactly `{0, 1, ⊥, blank}` on every tape. -/
inductive Sym
  | zero
  | one
  | bot
  | blank
  deriving DecidableEq

/-- The symbol `0` or `1` of a bit. -/
def Sym.ofBool (b : Bool) : Sym := if b then Sym.one else Sym.zero

/-- A bit string written as a word over `Σ`. -/
def bitsSym (x : List Bool) : List Sym := x.map Sym.ofBool

/-- **Head moves** (§3.2, footnote 14, p.21: "the tape head can remain at a given tape cell or
move left or right at each step"). -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq

/-- **Multi-tape oracle Turing machines with auxiliary, guess and randomness tapes**
(Goldberg, Hu, Lu, Lyu, Oliveira, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21):
"We consider multi-tape Turing machines over the alphabet Σ = {0, 1, ⊥}. In addition to the
usual input tape and work tapes, in some contexts we allow a machine to access three additional
tapes: one holding an auxiliary string, one holding a non-deterministic guess, and one holding
the randomness. We assume that the machine has sequential access (i.e., no random access) to the
randomness tape and the non-deterministic tape."

A machine has `nStates` control states (`Fin nStates`) with designated start, halting, query and
answer states, four read-only tapes (index `0` input, `1` auxiliary, `2` guess, `3` randomness)
and `works + 2` read/write tapes (indices `0, …, works - 1` work tapes, `works` the output tape,
`works + 1` the oracle query tape). The transition function maps the state and the symbols under
the heads to a new state, a move for each read-only head and a written symbol and a move for each
read/write head.

**Formalization Note.** All tapes are one-way infinite with cells `0, 1, …`; every head starts at
cell `0` and moves at most one cell per step (a left move at cell `0` stays), which is the
sequential access of footnote 14. Oracle access: in the query state the machine moves in one step
to `qyes` if the bit string on its query tape (the longest prefix of `0/1` cells) belongs to the
oracle and to `qno` otherwise, all tapes unchanged. The halting state is absorbing. These
conventions are not spelled out in the paper ("our results are robust with respect to encoding
choices", p.22). -/
structure Machine where
  nStates : ℕ
  start : Fin nStates
  halt : Fin nStates
  query : Fin nStates
  qyes : Fin nStates
  qno : Fin nStates
  works : ℕ
  δ : Fin nStates → (Fin 4 → Sym) → (Fin (works + 2) → Sym) →
    Fin nStates × (Fin 4 → Move) × (Fin (works + 2) → Sym × Move)

/-- The contents of the four read-only tapes: input `α`, auxiliary string `x`, guess `w`,
randomness `r` (the paper's `M(α; x; w; r)`, p.21). Each is written from cell `0`, blanks after. -/
structure Inputs where
  input : List Bool
  aux : List Bool
  guess : List Bool
  rand : List Bool

/-- The string on read-only tape `i`. -/
def Inputs.get (inp : Inputs) (i : Fin 4) : List Bool :=
  match i with
  | 0 => inp.input
  | 1 => inp.aux
  | 2 => inp.guess
  | 3 => inp.rand

namespace Machine

/-- The symbol in cell `h` of a read-only tape holding `s`. -/
def readRO (s : List Bool) (h : ℕ) : Sym :=
  match s[h]? with
  | some b => Sym.ofBool b
  | none => Sym.blank

/-- Writing symbol `a` in cell `h` of a read/write tape whose non-blank part is `l`. -/
def writeAt (l : List Sym) (h : ℕ) (a : Sym) : List Sym :=
  (l ++ List.replicate (h + 1 - l.length) Sym.blank).set h a

/-- The head position after a move. -/
def moveHead (m : Move) (h : ℕ) : ℕ :=
  match m with
  | Move.left => h - 1
  | Move.stay => h
  | Move.right => h + 1

/-- A configuration: state, read-only head positions, read/write tape contents and heads. -/
structure Cfg (M : Machine) where
  state : Fin M.nStates
  roHead : Fin 4 → ℕ
  rwTape : Fin (M.works + 2) → List Sym
  rwHead : Fin (M.works + 2) → ℕ

/-- The initial configuration: start state, all heads on cell `0`, read/write tapes blank. -/
def init (M : Machine) : Cfg M :=
  ⟨M.start, fun _ => 0, fun _ => [], fun _ => 0⟩

/-- Index of the output tape. -/
def outIdx (M : Machine) : Fin (M.works + 2) := ⟨M.works, by omega⟩

/-- Index of the oracle query tape. -/
def qIdx (M : Machine) : Fin (M.works + 2) := ⟨M.works + 1, by omega⟩

/-- The output word: the output tape with its trailing blanks removed. -/
def Cfg.output {M : Machine} (c : Cfg M) : List Sym :=
  ((c.rwTape M.outIdx).reverse.dropWhile (fun a => decide (a = Sym.blank))).reverse

/-- The query string: the longest prefix of `0/1` cells of the query tape, as bits. -/
def Cfg.queryString {M : Machine} (c : Cfg M) : List Bool :=
  ((c.rwTape M.qIdx).takeWhile (fun a => decide (a = Sym.zero ∨ a = Sym.one))).map
    (fun a => decide (a = Sym.one))

/-- One step with oracle `O` on read-only contents `inp`. -/
noncomputable def step (M : Machine) (O : Set (List Bool)) (inp : Inputs) (c : Cfg M) : Cfg M :=
  by
    classical
    exact
      if c.state = M.halt then c
      else if c.state = M.query then
        { c with state := if c.queryString ∈ O then M.qyes else M.qno }
      else
        let r := M.δ c.state (fun i => readRO (inp.get i) (c.roHead i))
          (fun j => (c.rwTape j).getD (c.rwHead j) Sym.blank)
        { state := r.1
          roHead := fun i => moveHead (r.2.1 i) (c.roHead i)
          rwTape := fun j => writeAt (c.rwTape j) (c.rwHead j) (r.2.2 j).1
          rwHead := fun j => moveHead (r.2.2 j).2 (c.rwHead j) }

/-- The configuration after `t` steps. -/
noncomputable def run (M : Machine) (O : Set (List Bool)) (inp : Inputs) (t : ℕ) : Cfg M :=
  (M.step O inp)^[t] M.init

/-- **Halting with output `z` within `t` steps**: after at most `t` transitions the machine is in
the halting state and its output tape holds the word `z` (blanks after). Since the halting state
is absorbing this is "halts after at most `t` steps with output `z`". -/
def HaltsWith (M : Machine) (O : Set (List Bool)) (inp : Inputs) (t : ℕ) (z : List Sym) :
    Prop :=
  (M.run O inp t).state = M.halt ∧ (M.run O inp t).output = z

/-- **Query-length bound** ("`M` only makes queries to `O` on strings of length at most `l`",
Definition 99, p.67): during its first `t` steps every oracle query has length at most `ℓ`
(`ℓ = ⊤`: no bound). -/
def QueryBounded (M : Machine) (O : Set (List Bool)) (ℓ : ℕ∞) (inp : Inputs) (t : ℕ) : Prop :=
  ∀ j < t, (M.run O inp j).state = M.query → (M.run O inp j).state ≠ M.halt →
    (((M.run O inp j).queryString.length : ℕ) : ℕ∞) ≤ ℓ

/-- **Computing a function** in time `T`: with oracle `∅` and only the input tape filled with `u`,
the machine halts within `T` steps with output the bit string `v`. -/
def Computes (M : Machine) (T : ℕ) (u v : List Bool) : Prop :=
  M.HaltsWith ∅ ⟨u, [], [], []⟩ T (bitsSym v)

end Machine

end NKtLB


