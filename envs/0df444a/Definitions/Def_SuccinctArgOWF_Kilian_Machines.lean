-- Prove2me | Definitions.Def_SuccinctArgOWF_Kilian_Machines
-- name    : SuccinctArgOWF_Kilian_Machines
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:04.071209+00:00
-- url     : https://prove2.me/theorems/5dc3fb88-311b-4967-a1ee-671df2ab5b57
-- title:
--   §3 — strings, step-counted machines, non-uniform stateful adversaries and the cost model
-- statement:
--   This file fixes the computational model of the paper's preliminaries (§3).
--
--   **Strings.** Strings are finite bit strings $x\in\{0,1\}^*$. $\{0,1\}^m$ is the set of strings of length $m$; numbers are written in little-endian binary; $[N]=\{1,\dots,N\}$, an *interval* is $I=\{a,\dots,b\}\subseteq[N]$ with $1\le a\le b\le N$, and $m_I=m_a\cdots m_b$ is the restriction of $m$ to $I$ (positions indexed from $1$). Lists of strings are written as one string by a self-delimiting code (every bit $b$ becomes $1b$, every entry is terminated by $0$) with its decoding.
--
--   **Machines.** All machines are the deterministic multi-tape Turing machines over the alphabet $\{\sqcup,0,1\}$ of the published library `MetaSearch.Heyting.Machine`, each with a fixed binary code $\langle M\rangle$. A machine is run on a list of input strings, one per tape; it halts after $s$ steps if no rule applies after at most $s$ steps; its *running time* is the least such $s$, and the output of tape $j$ is the string from the head rightwards up to the first blank.
--
--   **Adversaries and running time.** A non-uniform probabilistic stateful adversary $A$ is given by, for each phase $p$ of a game, a machine $M_p$ and a hardwired advice string $a_p$. Every invocation in phase $p$ runs $M_p$ on the current state, the incoming message, the random tape $\omega$ and $a_p$ (plus fixed extra inputs such as a public statement); it outputs the new state and its outgoing message components. The *running time* of $A$ for a set $S$ of schedules (sequences of phases and incoming messages) is at most $t$ if for every random tape $\omega\in\{0,1\}^t$ and every schedule in $S$ all invocations halt and
--
--   $$\sum_{\text{invocations}}\text{steps}\;+\sum_{\text{distinct }(M_p,a_p)}\bigl(|\langle M_p\rangle|+|a_p|\bigr)\;\le\;t .$$
--
--   This is the convention of §3: running time is the worst-case execution time plus the bit length of the description and advice, including hardwired auxiliary inputs, also when $t$ is exponential.
--
--   **Probability and negligible functions.** $\Pr$ is the uniform probability on a finite set. $\nu:\mathbb N\to[0,\infty)$ is *negligible* if for every $c$ and all sufficiently large $n$, $\nu(n)<1/n^c$, equivalently $\nu(n)<1/p(n)$ eventually for every positive polynomial $p$.
--
--   These definitions are used by every game, reduction bound and efficiency claim of the mission.
--
--   **Formalization Note** The paper fixes no machine model; one model is fixed for all adversaries and honest parties. An adversary that uses one machine with one advice string in every phase (the paper's convention) is the special case in which all phases share the same program, whose code and advice are then counted once. The random tape has length exactly $t$, which a time-$t$ machine cannot read beyond.
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), §3 Preliminaries, p. 7 (PDF p. 9)

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-! # Strings, step-counted machines, non-uniform adversaries and the cost model (§3)

Machines are the deterministic multi-tape Turing machines over `{⊔,0,1}` with binary codes of the
published `MetaSearch.Heyting` library. On top of it this file fixes

* runs on several input strings (one per tape) and the output of each tape;
* the cost model of §3 (Dujmovic–Wichs, p.7): a stateful adversary is given by one machine with
  hardwired advice per phase of a game; its running time is the total number of steps of all its
  invocations plus the bit length of all machine codes and advice strings; it reads its random coins
  from a random tape;
* uniform probability over finite sets, negligible functions. -/

open MetaSearch.Heyting

/-- Bit strings `{0,1}^*` (`false` is the bit `0`). -/
abbrev Str := List Bool

/-! ## Strings -/

/-- All bit strings of length `m`, the set `{0,1}^m`. -/
def allStr (m : ℕ) : Finset Str := (Finset.univ : Finset (Fin m → Bool)).image List.ofFn

/-- Little-endian binary representation of a natural number. -/
def natBits (n : ℕ) : Str := n.bits

/-- The number denoted by a little-endian binary string (inverse of `natBits`). -/
def bitsVal (s : Str) : ℕ := s.foldr (fun b n => (if b then 1 else 0) + 2 * n) 0

/-- `IsInterval N a b`: `{a, a+1, …, b}` is an interval of `[N] = {1, …, N}` (`1 ≤ a ≤ b ≤ N`). -/
def IsInterval (N a b : ℕ) : Prop := 1 ≤ a ∧ a ≤ b ∧ b ≤ N

/-- The restriction `m_I = m_a ⋯ m_b` of a string to the interval `I = {a, …, b}` (positions indexed
from `1`). -/
def sub (m : Str) (a b : ℕ) : Str := (m.drop (a - 1)).take (b + 1 - a)

/-- The self-delimiting code of one string: every bit `b` becomes `1b`, then the terminator `0`. -/
def encStr (s : Str) : Str := s.flatMap (fun b => [true, b]) ++ [false]

/-- The self-delimiting code of a list of strings (the concatenation of the codes of its entries). -/
def encList (l : List Str) : Str := l.flatMap encStr

/-- Decoding helper for `encList` (`cur` holds the bits of the current entry, reversed). -/
def decAux : Str → Str → Option (List Str)
  | [], [] => some []
  | [], _ :: _ => none
  | false :: r, cur => (decAux r []).map (cur.reverse :: ·)
  | true :: b :: r, cur => decAux r (b :: cur)
  | [true], _ => none

/-- Decoding a list of strings: `decList (encList l) = some l`; `none` on a string that is not a
code. -/
def decList (s : Str) : Option (List Str) := decAux s []

/-! ## Runs on several inputs -/

/-- The start configuration of `M` with the input strings `ins` on tapes `0, 1, 2, …` (one string
per tape, heads on their first cells; missing inputs are empty and surplus inputs are dropped). -/
def startOn (M : Machine) (ins : List Str) : Config :=
  ⟨0, (List.range (M.numTapes + 1)).map fun j => Tape.ofString (ins.getD j [])⟩

/-- `M` started on `ins` has halted after at most `s` steps. -/
def HaltsAt (M : Machine) (ins : List Str) (s : ℕ) : Prop :=
  M.step (M.runFor s (startOn M ins)) = none

/-- `M` halts on `ins`. -/
def Halts (M : Machine) (ins : List Str) : Prop := ∃ s, HaltsAt M ins s

open Classical in
/-- The running time of `M` on `ins`: the number of steps until it halts (`0` if it never halts). -/
noncomputable def time (M : Machine) (ins : List Str) : ℕ :=
  if h : Halts M ins then Nat.find h else 0

/-- The string written on tape `j` after `s` steps (from the head rightwards up to the first blank). -/
def outAt (M : Machine) (ins : List Str) (s j : ℕ) : Str :=
  ((M.runFor s (startOn M ins)).tapes.getD j Tape.blank).output

/-- The output of `M` on tape `j` of its halted configuration on `ins` (meaningful when `M` halts). -/
noncomputable def out (M : Machine) (ins : List Str) (j : ℕ) : Str := outAt M ins (time M ins) j

/-! ## Adversaries and the cost model -/

/-- A non-uniform probabilistic stateful adversary (§3, p.7): for every phase `p` of a game, a
machine and its hardwired advice string. The phases of each game are fixed where the game is
defined. -/
structure Adv where
  /-- `phases[p] = (machine, advice)` used for every invocation in phase `p`. -/
  phases : List (Machine × Str)

open Classical in
/-- The description part of the cost: the total bit length of the codes and advice strings of the
distinct phase programs (a program used in several phases is counted once, so an adversary given by
a single machine with advice for all phases costs exactly its code plus its advice). -/
noncomputable def Adv.descCost (A : Adv) : ℕ :=
  (A.phases.dedup.map fun p => p.1.encode.length + p.2.length).sum

open Classical in
/-- Run the stateful adversary `A` with random tape `ω` and extra static inputs `ex` through a
schedule of invocations `(phase, incoming message)`, starting from state `st`. Invocation inputs:
tape 0 the current state, tape 1 the incoming message, tape 2 the random tape, tape 3 the advice of
the phase, tapes `4, 5, …` the extra inputs `ex`. Its outputs: tape 0 is the new state, tapes
`1, 2, …` the output components. Returns the total number of steps and the output functions of all
invocations, or `none` if some invocation names a missing phase or does not halt. -/
noncomputable def Adv.run (A : Adv) (ω : Str) (ex : List Str) :
    List (ℕ × Str) → Str → Option (ℕ × List (ℕ → Str))
  | [], _ => some (0, [])
  | (p, msg) :: rest, st =>
    match A.phases[p]? with
    | none => none
    | some (M, adv) =>
      if Halts M ([st, msg, ω, adv] ++ ex) then
        match A.run ω ex rest (out M ([st, msg, ω, adv] ++ ex) 0) with
        | none => none
        | some (s, os) =>
          some (time M ([st, msg, ω, adv] ++ ex) + s, out M ([st, msg, ω, adv] ++ ex) :: os)
      else none

/-- `A` is an adversary of running time at most `t` for the schedules `S` (with extra inputs `ex`):
on every random tape `ω ∈ {0,1}^t` and every schedule of `S` all invocations halt, and the total
number of steps plus the bit length of all codes and advice is at most `t` (worst case over coins and
schedules). -/
def Adv.RunsWithin (A : Adv) (t : ℕ) (ex : List Str) (S : Set (List (ℕ × Str))) : Prop :=
  ∀ ω : Str, ω.length = t → ∀ sch ∈ S, ∃ s os, A.run ω ex sch [] = some (s, os) ∧ A.descCost + s ≤ t

/-- The outputs of all invocations of `A` on schedule `sch` (empty if the run fails). -/
noncomputable def Adv.outs (A : Adv) (ω : Str) (ex : List Str) (sch : List (ℕ × Str)) :
    List (ℕ → Str) :=
  match A.run ω ex sch [] with
  | some (_, os) => os
  | none => []

/-- Output component `j` of invocation `i` (empty if absent). -/
def outC (os : List (ℕ → Str)) (i j : ℕ) : Str := (os.getD i (fun _ => [])) j

/-! ## Probability, polynomials, negligible functions -/

open Classical in
/-- The probability of the event `E` when `ω` is sampled uniformly from the finite set `Ω`. -/
noncomputable def prob {Ω : Type} [Fintype Ω] (E : Ω → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / (Fintype.card Ω : ℝ)

/-- A function `ν : ℕ → [0, ∞)` is negligible (p.7): for every `c` and all sufficiently large `n`,
`ν(n) < 1/n^c` (equivalently: `ν(n) < 1/p(n)` eventually, for every positive polynomial `p`). -/
def Negligible (ν : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ ν n) ∧ ∀ c : ℕ, ∀ᶠ n in Filter.atTop, ν n < 1 / (n : ℝ) ^ c

end SuccinctArgOWF.Kilian


