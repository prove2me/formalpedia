-- Prove2me | Definitions.Def_AlgSemNondet_Main_TuringMachine
-- name    : AlgSemNondet_Main_TuringMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:45:30.190472+00:00
-- url     : https://prove2.me/theorems/17e0d9a3-0c0e-47de-949f-f12ac25807d9
-- title:
--   Definition 3.1 — classical deterministic Turing machine, configurations and runs
-- statement:
--   A classical deterministic Turing machine is a seven-tuple $M = (Q, \Sigma, \Gamma, \delta, q_0, q_{\mathrm{accept}}, q_{\mathrm{reject}})$: a finite set of states $Q$, a finite tape alphabet $\Gamma$ containing a blank $B$, an input alphabet $\Sigma \subseteq \Gamma$ with $B \notin \Sigma$, a **partial** transition function $\delta : Q \times \Gamma \rightharpoonup Q \times \Gamma \times \{L, S, R\}$, a start state $q_0$, and accept and reject states. In Lean, $Q$, $\Gamma$ and $B$ are parameters of the type `TuringMachine Q Γ B`, $\Sigma$ is a set of symbols with $B \notin \Sigma$, and $\delta$ returns `none` where it is undefined.
--
--   A configuration is a state, a bi-infinite tape $\mathbb Z \to \Gamma$ and a head position in $\mathbb Z$. On input $w = w_1 \cdots w_n$ the initial configuration has $w$ written in cells $0, \dots, n-1$, every other cell blank, state $q_0$, and the head on the leftmost non-blank symbol (cell $0$ when no input letter is non-blank, e.g. on the empty input). One step in state $q$ reading $c$ with $\delta(q, c) = (q', c', D)$ writes $c'$, moves the head by $D$ ($-1, 0, +1$) and enters $q'$. The computation stops when $\delta(q, c)$ is undefined or when $q \in \{q_{\mathrm{accept}}, q_{\mathrm{reject}}\}$. `run M w n` is `some` $C_n$, the $n$-th configuration, while the computation has not stopped before step $n$, and `none` afterwards.
--
--   Formalization Note: the tape type $\mathbb Z \to \Gamma$ does not require finite support; every configuration reachable from an initial one is blank outside finitely many cells. The halting convention (also stopping in the accept and reject states) is the standard one; Definition 3.1 only states that $\delta$ is partial.
-- source:
--   Zheng, Zheng, Wang and Huang, An Algebraic Semantic Framework for Nondeterministic Computation, July 2026, Definition 3.1, p.7, held PDF SHA256 729429b16e49937f0b09fd345508cf77ac999be7b0601b781b9e37eb393587fa

import Mathlib

namespace AlgSemNondet.Main

/-- Head moves of Definition 3.1: left, stay, right. -/
inductive Dir where
  | L
  | S
  | R
  deriving DecidableEq, Repr

/-- The displacement of the head for each move. -/
def Dir.shift : Dir → ℤ
  | .L => -1
  | .S => 0
  | .R => 1

/-- Definition 3.1 (classical deterministic Turing machine)
`M = (Q, Σ, Γ, δ, q₀, q_accept, q_reject)` with finite state set `Q`, finite tape alphabet `Γ`,
input alphabet `Σ ⊆ Γ`, the blank `B ∈ Γ \ Σ`, and a *partial* transition function
`δ : Q × Γ → Q × Γ × {L, S, R}` (`none` = undefined). The finite sets `Q` and `Γ` and the blank
`B` are parameters of the type. -/
structure TuringMachine (Q Γ : Type*) [Fintype Q] [Fintype Γ] (B : Γ) where
  /-- The input alphabet `Σ ⊆ Γ`. -/
  inputAlphabet : Set Γ
  /-- The blank is not an input symbol: `B ∈ Γ \ Σ`. -/
  blank_not_mem : B ∉ inputAlphabet
  /-- The partial transition function. -/
  δ : Q → Γ → Option (Q × Γ × Dir)
  /-- Start state. -/
  q₀ : Q
  /-- Accept state. -/
  qaccept : Q
  /-- Reject state. -/
  qreject : Q

/-- A configuration: current state, the bi-infinite tape `ℤ → Γ`, and the head position. -/
structure Config (Q Γ : Type*) where
  state : Q
  tape : ℤ → Γ
  head : ℤ

namespace TuringMachine

variable {Q Γ : Type*} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ] {B : Γ}

/-- Initial head position: the leftmost non-blank symbol of the input (cell `i` holds the
`i`-th input letter); `0` when the input contains no non-blank symbol. -/
def initHead (B : Γ) (w : List Γ) : ℤ :=
  match w.findIdx? (fun c => decide (c ≠ B)) with
  | some i => (i : ℤ)
  | none => 0

/-- Initial configuration on input `w`: `w` written left to right in cells `0, …, |w| - 1`,
every other cell blank, head on the leftmost non-blank symbol, state `q₀`. -/
def initConfig (M : TuringMachine Q Γ B) (w : List Γ) : Config Q Γ where
  state := M.q₀
  tape := fun i => if h : 0 ≤ i ∧ i.toNat < w.length then w[i.toNat]'h.2 else B
  head := initHead B w

/-- One step. In state `q` reading `c` with `δ(q, c) = (q', c', D)` the machine writes `c'`,
moves the head by `D` and enters `q'`. The computation has stopped (`none`) when `δ(q, c)` is
undefined or `q ∈ {q_accept, q_reject}`. -/
def step (M : TuringMachine Q Γ B) (C : Config Q Γ) : Option (Config Q Γ) :=
  if C.state = M.qaccept ∨ C.state = M.qreject then none
  else (M.δ C.state (C.tape C.head)).map fun t =>
    { state := t.1, tape := Function.update C.tape C.head t.2.1, head := C.head + t.2.2.shift }

/-- The configuration sequence `C₀, C₁, C₂, …` of `M` on input `w`: `run M w n = some Cₙ`
while the computation has not stopped before step `n`, and `none` afterwards. -/
def run (M : TuringMachine Q Γ B) (w : List Γ) : ℕ → Option (Config Q Γ)
  | 0 => some (M.initConfig w)
  | n + 1 => (M.run w n).bind M.step

end TuringMachine

end AlgSemNondet.Main


