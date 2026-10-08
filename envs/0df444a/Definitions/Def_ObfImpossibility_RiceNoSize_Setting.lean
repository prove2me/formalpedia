-- Prove2me | Definitions.Def_ObfImpossibility_RiceNoSize_Setting
-- name    : ObfImpossibility_RiceNoSize_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:27:39.703984+00:00
-- url     : https://prove2.me/theorems/245b22d3-dfe4-48c5-b041-9b8739841fc3
-- title:
--   Step-counted Turing machines, $[M]$, $\langle M\rangle(1^t,x)$, $|M|$, descriptions, oracle runs $S^{\langle M\rangle}()$, closure under $[\cdot]$ and Conjecture A.3 (§2.1, App. A)
-- statement:
--   This file fixes the objects of Appendix A of Barak et al., *On the (Im)possibility of Obfuscating Programs*, in a Turing-machine model with literal step counts.
--
--   1. **Machines.** A machine $M$ is a one-tape Post–Turing machine over the tape alphabet $\{0,1\}$ (with $0$ the blank) and with states $\{0,1,\dots,q\}$, $0$ being the initial state. In state $s$ reading symbol $a$ it either halts or moves to a new state and performs one action: move the head left, move it right, or write a symbol. One such transition is one **step**.
--   2. **Size.** $|M| = q+1$ is the number of states. There are only finitely many machines of each size.
--   3. **Inputs and outputs.** Inputs are natural numbers written in unary: the input $x$ is the tape $1^x$ with the head on its first cell, so $|x| = x$. When $M$ halts, its output is the number of consecutive $1$s starting at the head cell and going right.
--   4. **Computed function.** $[M]:\mathbb N\rightharpoonup\mathbb N$ is the (possibly partial) function computed by $M$: $[M](x)=y$ if $M$ halts on $x$ with output $y$, undefined if it runs forever.
--   5. **Bounded run.** For $t,x\in\mathbb N$,
--   $$\langle M\rangle(1^t,x)=\begin{cases} y & \text{if } M(x) \text{ halts with output } y \text{ after at most } t \text{ steps},\\ \bot & \text{otherwise.}\end{cases}$$
--   6. **Descriptions.** Each machine has a canonical description $\ulcorner M\urcorner\in\mathbb N$, the encoding of $q$ together with its transition table, listed state by state.
--   7. **Oracle access without the size.** An oracle machine $S$ may query the total function $\langle M\rangle$: a query is a pair $(t,x)$ and the answer is $\langle M\rangle(1^t,x)$. $S^{\langle M\rangle}()$ denotes the (possibly divergent) output of $S$ run with this oracle and no other input; in particular $S$ is not given $|M|$.
--   8. **Promise problems.** For sets $\Pi_Y,\Pi_N$ of machines, $\Pi=(\Pi_Y,\Pi_N)$ is *closed under* $[\cdot]$ if $[M]=[M']$ implies $M\in\Pi_Y\iff M'\in\Pi_Y$ and $M\in\Pi_N\iff M'\in\Pi_N$. A program $T$ acting on descriptions *decides* $\Pi$ if $T(\ulcorner M\urcorner)=1$ for every $M\in\Pi_Y$ and $T(\ulcorner M\urcorner)=0$ for every $M\in\Pi_N$; nothing is required of $T$ outside $\Pi_Y\cup\Pi_N$, where it may diverge.
--   9. **Conjecture A.3** (Rice's theorem, third generalization). For every promise problem $\Pi=(\Pi_Y,\Pi_N)$ (a pair of disjoint sets of machines) that is closed under $[\cdot]$ and decidable, there is an oracle machine $S$ with
--   $$M\in\Pi_Y\Rightarrow S^{\langle M\rangle}()=1,\qquad M\in\Pi_N\Rightarrow S^{\langle M\rangle}()=0.$$
--
--   These objects are what Theorem A.4 is about: it asserts that Conjecture A.3 is false, so the size $1^{|M|}$ given to the simulator of Theorem A.2 cannot be dropped.
--
--   **Formalization Note** Machines are Mathlib's `Turing.TM0.Machine Bool (Fin (q+1))` packaged with $q$; the blank and the initial state are the `default` values `false` and `0`. $[M]$ is `TM0.eval` followed by the head read-out; $\langle M\rangle(1^t,x)$ is computed by iterating `TM0.step` at most $t$ times from `TM0.init` (`none` is $\bot$). The description is `Encodable.encode (q, table)`. Oracle machines are the uniform oracle programs `FriedbergMuchnik.Program` with semantics `oracleEval` (imported); the oracle $\langle M\rangle$ is the total function sending `Nat.pair t x` to `0` for $\bot$ and to `y+1` for output $y$, and $S^{\langle M\rangle}()$ is the run on the fixed input $0$. The decider $T$ is a `Nat.Partrec.Code` applied to descriptions. Disjointness of $\Pi_Y,\Pi_N$ appears as a hypothesis of Conjecture A.3, matching the paper's definition of a promise problem (p. A:32).
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:7 (Section 2.1: [M], ⟨M⟩(1^t,x)), p. A:32 (promise problems), pp. A:40–A:42 (Appendix A: decides, closed under [·], Conjecture A.3)

import Mathlib
import Definitions.Def_FriedbergMuchnik_Priority

namespace ObfImpossibility.RiceNoSize

open Turing

/-- Machines (§2.1, p. A:7). A machine is a Post–Turing machine (Mathlib's `TM0`) over the
tape alphabet `Bool`, whose blank symbol is `false` (`default`), with the `q + 1` states
`Fin (q + 1)`; state `0` (`default`) is the initial state. `δ s a = none` means that the
machine halts in state `s` reading `a`. -/
structure Machine where
  /-- `q + 1` is the number of states. -/
  q : ℕ
  /-- The transition function. -/
  δ : TM0.Machine Bool (Fin (q + 1))

/-- `|M|` : the size of a machine, its number of states. There are finitely many machines of
each size. -/
def size (M : Machine) : ℕ := M.q + 1

/-- Inputs are natural numbers written in unary: `x` is the tape word `1^x`, so `|x| = x`. -/
def input (x : ℕ) : List Bool := List.replicate x true

/-- The number of consecutive `1`s (`true`s) at the start of a blank-padded tape word. -/
def leadingOnes (l : ListBlank Bool) : ℕ :=
  l.liftOn (fun L => (L.takeWhile id).length) (by
    rintro a b ⟨i, rfl⟩
    induction a with
    | nil =>
      cases i with
      | zero => rfl
      | succ i => simp [List.replicate_succ]
    | cons c a ih =>
      cases c
      · simp
      · simpa using ih)

/-- Output convention: a halted configuration outputs the natural number written in unary
starting at the head, i.e. the number of consecutive `1`s from the head cell rightwards. -/
def output {k : ℕ} (c : TM0.Cfg Bool (Fin (k + 1))) : ℕ := leadingOnes c.Tape.right₀

/-- `[M]` (§2.1, p. A:7): the (possibly partial) function computed by `M`. On input `x`, run
`M` from the initial configuration on `1^x` (Mathlib's `TM0.eval`); if it halts, the output
is the unary number at the head. -/
def fn (M : Machine) : ℕ →. ℕ := fun x =>
  (TM0.eval M.δ (input x)).map leadingOnes

/-- Running `M` from configuration `c` for at most `t` steps: the output if `M` halts after
at most `t` transitions, `none` otherwise. -/
def runFor (M : Machine) : ℕ → TM0.Cfg Bool (Fin (M.q + 1)) → Option ℕ
  | 0, c =>
    match TM0.step M.δ c with
    | none => some (output c)
    | some _ => none
  | t + 1, c =>
    match TM0.step M.δ c with
    | none => some (output c)
    | some c' => runFor M t c'

/-- `⟨M⟩(1^t, x)` (§2.1, p. A:7): `some y` if `M(x)` halts with output `y` after at most `t`
steps, `none` (= `⊥`) otherwise. Steps are literal `TM0` transitions. -/
def bounded (M : Machine) (t x : ℕ) : Option ℕ := runFor M t (TM0.init (input x))

/-- Code of a `TM0` statement over `Bool`. -/
def stmtCode : TM0.Stmt Bool → ℕ
  | .move .left => 0
  | .move .right => 1
  | .write false => 2
  | .write true => 3

/-- Code of one transition-table entry (`0` = halt). -/
def entryCode {k : ℕ} : Option (Fin k × TM0.Stmt Bool) → ℕ
  | none => 0
  | some (s, a) => Nat.pair s.val (stmtCode a) + 1

/-- The canonical description `⌜M⌝ ∈ ℕ` of a machine (p. A:7: machines are identified with
their descriptions): the number of states together with the transition table listed state
by state (reading `0`, then reading `1`). -/
def desc (M : Machine) : ℕ :=
  Encodable.encode (M.q, (List.finRange (M.q + 1)).flatMap
    (fun s => [entryCode (M.δ s false), entryCode (M.δ s true)]))

/-- The oracle `⟨M⟩` as a total function on query codes: the query `(1^t, x)` is the number
`Nat.pair t x`; the answer `⊥` is encoded as `0` and the answer `y` as `y + 1`. -/
def oracle (M : Machine) (q : ℕ) : ℕ :=
  match bounded M q.unpair.1 q.unpair.2 with
  | none => 0
  | some y => y + 1

/-- `S^{⟨M⟩}()` : the run of the oracle machine `S`, with oracle access to `⟨M⟩` and no
other input (it is started on the fixed input `0`; in particular it is not given `|M|`).
Oracle machines are the uniform oracle programs `FriedbergMuchnik.Program`. -/
def simRun (S : FriedbergMuchnik.Program) (M : Machine) : Part ℕ :=
  FriedbergMuchnik.oracleEval (PFun.lift (oracle M)) S 0

/-- `Π = (Π_Y, Π_N)` is closed under `[·]` (p. A:41). -/
def ClosedUnderFn (PY PN : Set Machine) : Prop :=
  ∀ M M' : Machine, fn M = fn M' → (M ∈ PY ↔ M' ∈ PY) ∧ (M ∈ PN ↔ M' ∈ PN)

/-- The algorithm `T` (a partial recursive program run on descriptions `⌜M⌝`) decides
`Π = (Π_Y, Π_N)` (pp. A:40–A:41): it outputs `1` on every yes-instance and `0` on every
no-instance; off the promise it is unconstrained and may diverge. -/
def Decides (T : Nat.Partrec.Code) (PY PN : Set Machine) : Prop :=
  (∀ M ∈ PY, T.eval (desc M) = Part.some 1) ∧ (∀ M ∈ PN, T.eval (desc M) = Part.some 0)

/-- Conjecture A.3 (Rice's theorem — third generalization, p. A:42): for every promise
problem `Π = (Π_Y, Π_N)` (a pair of disjoint sets of machines, p. A:32) that is closed under
`[·]` and decidable, there is an oracle machine `S` with `S^{⟨M⟩}() = 1` for `M ∈ Π_Y` and
`S^{⟨M⟩}() = 0` for `M ∈ Π_N`. -/
def ConjectureA3 : Prop :=
  ∀ PY PN : Set Machine, Disjoint PY PN → ClosedUnderFn PY PN →
    (∃ T : Nat.Partrec.Code, Decides T PY PN) →
    ∃ S : FriedbergMuchnik.Program,
      (∀ M ∈ PY, simRun S M = Part.some 1) ∧ (∀ M ∈ PN, simRun S M = Part.some 0)

end ObfImpossibility.RiceNoSize


