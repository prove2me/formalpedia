-- Prove2me | Definitions.Def_IntQuotHNP_Supplement_LasVegas
-- name    : IntQuotHNP_Supplement_LasVegas
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:02:35.61657+00:00
-- url     : https://prove2.me/theorems/1a253f26-39fd-49c0-b0cc-b74c72415e61
-- title:
--   Randomized bit time: the fair-coin stream, halting time, expected bit time and Las Vegas output
-- statement:
--   Randomized algorithms are run on a **randomized multi-tape Turing machine**: a finite transition table over finitely many tapes (alphabet of 8 symbols) that, at every tick, reads the symbols under the heads and one fresh random bit, and then halts or changes state while each tape writes one symbol or moves its head one cell. The input is on tape 0, which also holds the output. The random bits form a stream $\omega=(\omega_0,\omega_1,\dots)\in\{0,1\}^{\mathbb N}$ distributed as a sequence of independent fair coins.
--
--   For a machine $A$ and an input word $w$:
--
--   1. the **halting time** $T_A(w,\omega)\in\mathbb N\cup\{\infty\}$ is the least number of ticks after which the run fed with $\omega_0,\omega_1,\dots$ has halted ($\infty$ if it never halts); this is the **bit time** of the run;
--   2. the **expected bit time** is $\mathbb E_\omega[T_A(w,\omega)]\in[0,\infty]$;
--   3. the run on $\omega$ **outputs** a word $u$ when it halts with $u$ on tape 0 from the head rightwards; $A$ **always outputs** $u$ when every halting run does;
--   4. $A$ is **deterministic** when its transitions ignore the random bit.
--
--   These notions give meaning to "with probability one", "Las Vegas" and "expected bit time" in Definition 3.1 and Theorems 3.4 and 5.2.
--
--   **Formalization Note** The machine `MTMachine` is defined here; it uses the symbol alphabet and the number encodings of the published `OAI.MatchingFPRAS`. It has several tapes because the cost bounds of Theorems 3.4 and 5.2 are linear in a number of tests that is not polylogarithmic, and a single-tape machine can need quadratic time for the paper's bookkeeping (its proof keeps the tested values and secrets in balanced search trees). The fair-coin measure is the infinite product of uniform measures on `Bool`. The expected time is a lower Lebesgue integral in $[0,\infty]$, so a machine that fails to halt with positive probability has expected time $\infty$ and satisfies no finite bound.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 3.1, p.16 (PDF p.17); Theorem 3.4, p.20 (PDF p.21); Theorem 5.2, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_MatchingFPRAS

namespace IntQuotHNP

namespace Supplement

open MeasureTheory OAI.MatchingFPRAS

/-- **The fair-coin random bit stream.**
Kang, Lee, *Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number
Problems*, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 3.1, p.16 (PDF p.17):
"Probabilities and expectations here are over reconstruction randomness"; Theorem 3.4, p.20
(PDF p.21): "For a fixed public input, the expectation is over reconstruction randomness."

The product of countably many fair coins on `ℕ → Bool`.

**Formalization Note.** The paper names no machine model for randomized computation. A randomized
algorithm is read as a randomized multi-tape machine `MTMachine`, which reads one fresh random bit
at each tick; its random bits are the coordinates of a stream distributed by this measure. -/
noncomputable def coinMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ => (PMF.uniformOfFintype Bool).toMeasure

/-- **A randomized multi-tape Turing machine.**
Kang, Lee, *Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number
Problems*, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 3.4, p.20 (PDF p.21):
"in expected bit time poly(log p)[1 + min{|B₁|, (KZ_target)^k}]"; proof of Theorem 3.4: "Store
tested values and canonical secret encodings in balanced search trees. Each operation has
polynomial bit cost".

One finite transition table over `tapes + 1` tapes with the alphabet `Symbol = Fin 8` of the
published `OAI.MatchingFPRAS` encodings. At each tick the machine reads the symbols under its heads
and one fresh fair random bit, and either halts or moves to a new state while every tape performs
one write or one head move.

**Formalization Note.** The paper names no machine model. Its cost bounds are linear in the
number of tests `min{|B₁|, (KZ_target)^k}`, which is not polylogarithmic, and its proof keeps
dictionaries of tested values and secrets, so the model must not lose more than a polylogarithmic
factor on data-structure work. A single-tape machine can need quadratic time for such bookkeeping;
a multi-tape machine (as the multi-stack `Turing.TM2` model of the published goal) does not. Tape
`0` holds the input and, on halting, the output. -/
structure MTMachine where
  /-- the number of non-initial states -/
  states : ℕ
  /-- the number of work tapes besides tape `0` -/
  tapes : ℕ
  /-- the transition: state, the symbols under the heads, the random bit ↦ halt (`none`) or the
  next state with one action per tape -/
  transition : Fin (states + 1) → (Fin (tapes + 1) → Symbol) → Bool →
    Option (Fin (states + 1) × (Fin (tapes + 1) → Turing.TM0.Stmt Symbol))

/-- A configuration: the state (`none` once halted) and the contents of every tape. -/
structure MTConfig (A : MTMachine) where
  /-- the current state, `none` after halting -/
  state : Option (Fin (A.states + 1))
  /-- the tapes -/
  tapes : Fin (A.tapes + 1) → Turing.Tape Symbol

/-- One tick with the random bit `bit`. A halted configuration is absorbing. -/
def mtTick (A : MTMachine) (c : MTConfig A) (bit : Bool) : MTConfig A :=
  match c.state with
  | none => c
  | some s => match A.transition s (fun i => (c.tapes i).head) bit with
    | none => ⟨none, c.tapes⟩
    | some (s', act) =>
      ⟨some s', fun i => match act i with
        | .move d => (c.tapes i).move d
        | .write a => (c.tapes i).write a⟩

/-- The initial configuration: state `0`, the input on tape `0` with the head on its first symbol,
every other tape blank. -/
def mtInitial (A : MTMachine) (input : List Symbol) : MTConfig A :=
  ⟨some 0, fun i => if i = 0 then Turing.Tape.mk₁ input else Turing.Tape.mk₁ []⟩

/-- The run on a finite prefix of the random bit stream. -/
def mtRun (A : MTMachine) (input : List Symbol) {t : ℕ} (bits : Fin t → Bool) : MTConfig A :=
  (List.ofFn bits).foldl (mtTick A) (mtInitial A input)

/-- The run of `A` on `input` that uses the first `t` bits of the stream `ω`. -/
def runOn (A : MTMachine) (input : List Symbol) (ω : ℕ → Bool) (t : ℕ) : MTConfig A :=
  mtRun A input (fun i : Fin t => ω i)

open Classical in
/-- **The halting time (bit time) of a randomized run.**
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 3.4, p.20 (PDF p.21):
"in expected bit time …".

`haltTime A input ω` is the least number of ticks `t` after which the run of `A` on `input`, fed
with the first `t` bits of `ω`, has halted, and `⊤` if it never halts.

**Formalization Note.** One tick of the machine is one unit of bit time; a halted configuration is
absorbing, so the run has halted at every later tick as well. -/
noncomputable def haltTime (A : MTMachine) (input : List Symbol) (ω : ℕ → Bool) : ℕ∞ :=
  if h : ∃ t, (runOn A input ω t).state = none then (Nat.find h : ℕ∞) else ⊤

/-- **Expected bit time** of a randomized machine on an input.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 3.1 (iii), p.16
(PDF p.17): "computing R(a) has uniform expected bit cost poly(log p)"; Theorem 3.4, p.20.

The lower Lebesgue integral of the halting time against the fair-coin measure.

**Formalization Note.** The value lies in `ℝ≥0∞`; a run that fails to halt with positive
probability has expected time `⊤`, so no bound on it can hold by a junk value. -/
noncomputable def expectedTime (A : MTMachine) (input : List Symbol) : ENNReal :=
  ∫⁻ ω, ((haltTime A input ω : ℕ∞) : ENNReal) ∂coinMeasure

/-- **A run outputs a word.** On the random stream `ω`, the run of `A` on `input` halts after some
number of ticks with `out` on tape `0` from the head rightwards.

**Formalization Note.** Since halted configurations are absorbing, the tape after halting does not
depend on how many further bits are supplied, so the output of a halting run is unique. -/
def OutputsOn (A : MTMachine) (input : List Symbol) (ω : ℕ → Bool) (out : List Symbol) :
    Prop :=
  ∃ t, (runOn A input ω t).state = none ∧
    ((runOn A input ω t).tapes 0).right₀ = Turing.ListBlank.mk out

/-- **Every halting run outputs a word** (Las Vegas output): for every number of ticks `t` and
every prefix of `t` random bits, if the run has halted then tape `0` from the head rightwards holds
`out`. -/
def AlwaysOutputs (A : MTMachine) (input : List Symbol) (out : List Symbol) : Prop :=
  ∀ (t : ℕ) (bits : Fin t → Bool), (mtRun A input bits).state = none →
    ((mtRun A input bits).tapes 0).right₀ = Turing.ListBlank.mk out

/-- **Halting with an output within a number of ticks, on every random prefix.** For every prefix
of `t` random bits, the run has halted and tape `0` from the head rightwards holds `out`. For a
deterministic machine this is "outputs `out` within `t` steps". -/
def RunsWithin (A : MTMachine) (input : List Symbol) (out : List Symbol) (t : ℕ) : Prop :=
  ∀ bits : Fin t → Bool, (mtRun A input bits).state = none ∧
    ((mtRun A input bits).tapes 0).right₀ = Turing.ListBlank.mk out

/-- **A deterministic machine**: its transition ignores the random bit.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 3.4, p.20 (PDF p.21): "The
bound is deterministic when R is deterministic."

**Formalization Note.** The transition may not depend on the random bit, so every run on an input
is the same run. -/
def Deterministic (A : MTMachine) : Prop :=
  ∀ q a, A.transition q a false = A.transition q a true

end Supplement

end IntQuotHNP


