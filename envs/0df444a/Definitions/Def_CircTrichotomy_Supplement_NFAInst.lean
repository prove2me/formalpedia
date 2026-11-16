-- Prove2me | Definitions.Def_CircTrichotomy_Supplement_NFAInst
-- name    : CircTrichotomy_Supplement_NFAInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:12:59.41885+00:00
-- url     : https://prove2.me/theorems/b1f83b9f-182b-4365-b004-adf8fa80ed65
-- title:
--   Nondeterministic finite automata $A=(Q,\Sigma,\Delta,q_0,F)$, their languages $L(A)\subseteq\Sigma^+$ and their binary codes
-- statement:
--   A **nondeterministic finite automaton** (NFA) is a tuple $A=(Q,\Sigma,\Delta,q_0,F)$: a finite set $Q$ of states, a finite non-empty alphabet $\Sigma$, a transition relation $\Delta\subseteq Q\times\Sigma\times Q$, an initial state $q_0\in Q$ and a set $F\subseteq Q$ of final states. Its size is $|A|=|Q|+|\Sigma|+|\Delta|$. Its **language** $L(A)\subseteq\Sigma^+$ is the set of **non-empty** words $w=a_1\cdots a_\ell$ with a run $q_0\xrightarrow{a_1}q_1\cdots\xrightarrow{a_\ell}q_\ell$ in $\Delta$ ending in $F$; the empty word is never in $L(A)$, also when $q_0\in F$.
--
--   As an input of a decision problem, $A$ is written as a bit string: $|Q|-1$, $|\Sigma|-1$ and $|\Delta|$ in unary, each transition $(p,a,q)$ as three self-delimiting binary numbers, $q_0$ in binary, then the number of listed final states in unary and each final state in binary. A number is written in self-delimiting binary by writing each bit $b$ of its binary expansion as $1b$ and ending with $0$.
--
--   This is the input format of the membership problems of Theorem 4.1: the alphabet is part of the input.
--
--   **Formalization Note** States are $\{0,\dots,|Q|-1\}$ and letters $\{0,\dots,|\Sigma|-1\}$ (`Fin`); $\Delta$ and $F$ are lists, so an automaton has several instances (order, repetitions), all with the same language. The language is Mathlib's `NFA.accepts` with start set $\{q_0\}$, intersected with $\Sigma^+$. The code has length at least $|A|$ and polynomial in the instance, and it is self-delimiting.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §F, p.67 (definition of NFA, |A| and L(A) ⊆ Σ+); Problem F.1, p.67

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

namespace Supplement

/-- **A nondeterministic finite automaton as an input instance** (Göller, Manuel, *A Circuit
Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026,
sha256 5bef1791…), §F, p.67): "a nondeterministic finite automaton (NFA) is a tuple
A = (Q, Σ, ∆, q0, F), where Q is a finite set of states, Σ is a finite alphabet, ∆ ⊆ Q × Σ × Q is
a transition relation, q0 ∈ Q is the initial state and F ⊆ Q is a set of final states. By
|A| = |Q| + |Σ| + |∆| we denote the size of A and by L(A) ⊆ Σ+ we denote the language of A."

The states are `Q = Fin (numStates + 1)` and the letters `Σ = Fin (numLetters + 1)`; the
transitions are a finite list of triples `(p, a, q)`, the final states a finite list.

**Formalization Note** The alphabet is part of the instance. `Q` is non-empty because `q0 ∈ Q`;
`Σ` is non-empty (the paper's alphabets are finite and non-empty, Definition A.2, p.18). Listing
`∆` and `F` (possibly with repetitions or in another order) gives several instances with the same
automaton; they have the same language. -/
structure NFAInst where
  /-- `|Q| − 1` -/
  numStates : ℕ
  /-- `|Σ| − 1` -/
  numLetters : ℕ
  /-- the transition relation `∆`, as a list of triples `(p, a, q)` -/
  trans : List (Fin (numStates + 1) × Fin (numLetters + 1) × Fin (numStates + 1))
  /-- the initial state `q0` -/
  init : Fin (numStates + 1)
  /-- the final states `F` -/
  final : List (Fin (numStates + 1))

/-- The instance as a Mathlib `NFA` with start set `{q0}`. -/
def NFAInst.toNFA (A : NFAInst) : NFA (Fin (A.numLetters + 1)) (Fin (A.numStates + 1)) where
  step p a := {q | (p, a, q) ∈ A.trans}
  start := {A.init}
  accept := {q | q ∈ A.final}

/-- **The language `L(A) ⊆ Σ⁺`** (p.67): the non-empty words over `Σ = Fin (numLetters + 1)`
with an accepting run from `q0`. The empty word is never in `L(A)`, also when `q0 ∈ F`. -/
def NFAInst.lang (A : NFAInst) : Language (Fin (A.numLetters + 1)) :=
  {w | w ≠ [] ∧ w ∈ A.toNFA.accepts}

/-- Self-delimiting binary code of a natural number: each bit `b` of its binary expansion (least
significant first, `Nat.bits`) is written as `1 b`, and the code ends with `0`. -/
def encNat (n : ℕ) : List Bool := (n.bits.flatMap fun b => [true, b]) ++ [false]

/-- Unary code of a natural number: `n` ones followed by a zero. -/
def encUnary (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- **The binary encoding of an NFA** used as the input of the membership problems (Problem F.1,
p.67: "INPUT: An NFA A."): `|Q| − 1`, `|Σ| − 1` and the number of transitions in unary, then each
transition `(p, a, q)` as three self-delimiting binary numbers, then `q0` in binary, then the
number of final states in unary and each final state in binary.

**Formalization Note** The sizes are unary so that `|A| = |Q| + |Σ| + |∆|` is at most the length
of the code, and the code has length polynomial (`O(|A| log |A|)` plus the length of the list `F`)
in the instance. The code is self-delimiting, so it determines the instance, and it is decoded in
logarithmic space. -/
def NFAInst.enc (A : NFAInst) : List Bool :=
  encUnary A.numStates ++ encUnary A.numLetters ++ encUnary A.trans.length ++
    A.trans.flatMap (fun e => encNat e.1 ++ encNat e.2.1 ++ encNat e.2.2) ++
    encNat A.init ++ encUnary A.final.length ++ A.final.flatMap (fun q => encNat q)

end Supplement

end CircTrichotomy


