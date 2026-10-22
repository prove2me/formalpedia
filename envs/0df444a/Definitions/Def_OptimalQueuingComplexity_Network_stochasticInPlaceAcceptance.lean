-- Prove2me | Definitions.Def_OptimalQueuingComplexity_Network_stochasticInPlaceAcceptance
-- name    : OptimalQueuingComplexity_Network_stochasticInPlaceAcceptance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T10:17:02.678666+00:00
-- url     : https://prove2.me/theorems/a8634d0b-5a66-4a14-87f6-2dc78ae6376a
-- title:
--   Stochastic Turing machines and STOCHASTIC IN-PLACE ACCEPTANCE
-- statement:
--   A **stochastic Turing machine** has one tape over $\{0, 1\}$ and a finite set of states, each accepting, rejecting, nondeterministic or stochastic. Every non-final state-symbol combination $(q, a)$ has two continuations. Each continuation gives a new state, a symbol to write and a head move (left, stay, right).
--
--   On $n \ge 1$ squares, the value $v_k(x)$ of the depth-$k$ computation tree at configuration $x$ is defined as follows. An accepting state has value $1$ and a rejecting state has value $0$. A nondeterministic state takes the **maximum** of its two children and a stochastic state their **average**. A child whose head leaves the $n$ squares has value $0$, and so does a non-final node at depth $k$.
--
--   **STOCHASTIC IN-PLACE ACCEPTANCE**: given a machine $M$ and an integer $n$ in unary, does $M$ accept the input of $n$ zeroes without using space beyond the input? That is,
--   $$n \ge 1 \quad\text{and}\quad \exists k,\ v_k(\text{start state, head on square } 1, \text{ tape } 0^n) > \tfrac12 .$$
--
--   For a *precise* machine, which halts after exactly $f(n)$ steps and stays within the input squares, $v_k$ is constant for $k \ge f(n)$ and equals the paper's tree value. The condition is then the paper's: the tree evaluates to more than one half.
--
--   **Formalization Note.** The alphabet is binary, as the paper assumes in the proof of Theorem 1. Leaving the input squares is rejection. Instances are encoded as the machine's binary description followed by $n$ in unary.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 295 (stochastic Turing machines, acceptance, the STOCHASTIC IN-PLACE ACCEPTANCE problem)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Network_encNat

namespace OptimalQueuingComplexity.Network

/-- The kind of a state of a stochastic Turing machine: final (accepting or rejecting), or
non-final and either nondeterministic or stochastic. -/
inductive StateKind
  | accept
  | reject
  | nondet
  | stoch
  deriving DecidableEq

/-- Head movement of one step. -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq

/-- A **stochastic Turing machine** (Papadimitriou & Tsitsiklis 1999, p. 295) with a single tape
over the alphabet `{0, 1}` (`Bool`, `false` = 0): "a Turing machine whose states are divided into
two parts: the nondeterministic states and the stochastic states", where every non-final
state-symbol combination has two possible continuations.
* The states are `Fin numStates`, `start` is the start state and `kind` classifies each state.
* `trans q a b = (q', a', m)` is continuation `b ∈ {false, true}` from state `q` reading symbol
  `a`: go to state `q'`, write `a'`, move the head by `m`. (It is not read at final states.) -/
structure STM where
  /-- number of states -/
  numStates : ℕ
  /-- the start state -/
  start : Fin numStates
  /-- accepting / rejecting / nondeterministic / stochastic -/
  kind : Fin numStates → StateKind
  /-- the two continuations of each state-symbol combination -/
  trans : Fin numStates → Bool → Bool → Fin numStates × Bool × Move

/-- A configuration of `M` confined to the `n` input squares `0, …, n-1`: state, head position
and tape contents. -/
structure STM.Cfg (M : STM) (n : ℕ) where
  /-- current state -/
  state : Fin M.numStates
  /-- head position -/
  head : Fin n
  /-- tape contents of the `n` squares -/
  tape : Fin n → Bool

/-- The configuration reached by continuation `b`, or `none` if the head leaves the `n` input
squares (the machine would use space beyond the input). -/
def STM.next (M : STM) {n : ℕ} (x : M.Cfg n) (b : Bool) : Option (M.Cfg n) :=
  match M.trans x.state (x.tape x.head) b with
  | (q, a, m) =>
    let tape' := Function.update x.tape x.head a
    match m with
    | .stay => some ⟨q, x.head, tape'⟩
    | .left =>
      if 0 < x.head.val then
        some ⟨q, ⟨x.head.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.head.isLt⟩, tape'⟩
      else none
    | .right =>
      if h : x.head.val + 1 < n then some ⟨q, ⟨x.head.val + 1, h⟩, tape'⟩ else none

/-- The value of the depth-`k` computation tree rooted at configuration `x` (p. 295): a node in an
accepting state has value 1, in a rejecting state 0; a node of a nondeterministic state has the
**maximum** of its two children's values and a node of a stochastic state their **average**; a
child that leaves the input squares has value 0, and so does a non-final node at depth `k`. -/
def STM.value (M : STM) {n : ℕ} : ℕ → M.Cfg n → ℚ
  | 0, x => if M.kind x.state = .accept then 1 else 0
  | k + 1, x =>
    match M.kind x.state with
    | .accept => 1
    | .reject => 0
    | .nondet => max ((M.next x false).elim 0 (M.value k)) ((M.next x true).elim 0 (M.value k))
    | .stoch => ((M.next x false).elim 0 (M.value k) + (M.next x true).elim 0 (M.value k)) / 2

/-- The initial configuration on the input consisting of `n ≥ 1` zeroes: start state, head on
the first square, all squares `0`. -/
def STM.initCfg (M : STM) (n : ℕ) (h : 0 < n) : M.Cfg n :=
  ⟨M.start, ⟨0, h⟩, fun _ => false⟩

/-- Binary encoding of a machine: `numStates`, `start`, then for every state its kind (two bits)
and its four continuations `trans q a b` for `(a, b) = (0,0), (0,1), (1,0), (1,1)`, each as
target state (binary), written bit, and move (two bits). -/
def STM.enc (M : STM) : List Bool :=
  let encKind : StateKind → List Bool
    | .accept => [false, false]
    | .reject => [false, true]
    | .nondet => [true, false]
    | .stoch => [true, true]
  let encMove : Move → List Bool
    | .left => [false, false]
    | .stay => [false, true]
    | .right => [true, false]
  let encEntry : Fin M.numStates × Bool × Move → List Bool
    | (q, a, m) => encFin q ++ [a] ++ encMove m
  encNat M.numStates ++ encFin M.start ++ encTable encKind M.kind ++
    encTable (fun f : Bool → Bool → Fin M.numStates × Bool × Move =>
      encEntry (f false false) ++ encEntry (f false true) ++ encEntry (f true false) ++
        encEntry (f true true)) M.trans

/-- An instance of STOCHASTIC IN-PLACE ACCEPTANCE: a stochastic Turing machine `M` and an
integer `n`. -/
structure SIPAInstance where
  /-- the machine -/
  M : STM
  /-- the input length (the input is `n` zeroes) -/
  n : ℕ

/-- Encoding of a SIPA instance: the machine's encoding followed by `n` **in unary**
(`n` copies of `true`). -/
def SIPAInstance.enc (x : SIPAInstance) : List Bool :=
  x.M.enc ++ List.replicate x.n true

/-- **STOCHASTIC IN-PLACE ACCEPTANCE** (p. 295): "Given a stochastic Turing machine `M` and an
integer `n` in unary, does `M` accept the input consisting of `n` zeroes, without using any space
beyond that occupied by the input?" A computation that leaves the `n` input squares counts as
rejecting, and `M` accepts when its computation tree evaluates to more than one half: some
depth `k` has `value k (initCfg) > 1/2`. (`value k` is nondecreasing in `k`; for a *precise*
machine, halting after exactly `f(n)` steps, it is constant for `k ≥ f(n)` and equals the
paper's tree value, so this is the paper's acceptance condition. For `n = 0` there is no square
to scan and the answer is no.) -/
def stochasticInPlaceAcceptance (x : SIPAInstance) : Prop :=
  ∃ h : 0 < x.n, ∃ k : ℕ, (1 / 2 : ℚ) < x.M.value k (x.M.initCfg x.n h)

end OptimalQueuingComplexity.Network


