-- Prove2me | Definitions.Def_SampleMLS_ExpMoment_Model
-- name    : SampleMLS_ExpMoment_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:49:17.245391+00:00
-- url     : https://prove2.me/theorems/23d99298-bb8c-4b2c-9b23-3dc61b8f7967
-- title:
--   Running time, space, subroutine calls and encodings on the randomized log-cost RAM
-- statement:
--   The paper names no machine (§3.1, pp. 14–15, PDF 16–17: a randomized algorithm "can draw a uniform integer from $\{1,\dots,M\}$ in time polynomial in $\log M$"). Programs run on the published randomized log-cost oracle RAM `PDSEquiv.Machine` (exact $\mathrm{Ber}(a/b)$ draws charged by bit lengths, so uniform integers and uniform $t$-subsets are drawn exactly in polynomial time). This item adds:
--
--   - **Deterministic program**: no Bernoulli draw and no oracle call.
--   - **Running time** `runTime P Q x`: the largest log-cost reached on any random branch at any time ($\infty$ if unbounded; an unhalted step always costs at least one, so a finite bound forces halting).
--   - **Space** `runSpace P Q x`: the largest space of a reachable state, where a state's space is the sum over its nonzero registers and memory cells $a$ holding $v$ of $1+\mathrm{bits}(a)+\mathrm{bits}(v)$.
--   - **Subroutine calls**: an algorithm running a deterministic algorithm $A$ as a subroutine is an oracle program whose oracle answers a query $q$ with $A$'s output on $q$ (`subOracle A`). `CompositeTimeWithin P A x B`: on every branch and at every time, the program's own log-cost plus the running time of $A$ on every call made so far is at most $B$, and the program has halted by time $B$. The space of such an algorithm is its own space plus the space of $A$, which is reused from call to call.
--   - `DetComputes R x B form`: $R$ is deterministic, runs within time $B$ on $x$ and every output satisfies `form`.
--   - **Encodings**: an instance $I\in\{0,1\}^*$ is the list $N, I_1,\dots,I_N$ with $N=|I|$; a finite set of naturals is its size followed by its elements in increasing order; $(I,k)$, $(I,S)$ and $(I,X,k)$ are concatenations; an integer is (sign bit, absolute value); a rational output $[s,a,b]$ with $s\le1$, $b>0$ is $(-1)^s a/b$; yes is $[1]$, no is $[0]$.
-- source:
--   Gaspers, Monotone Local Search with Sample-Dependent Running Times, arXiv:2611.01774 (sha256 da381dca…), §3.1, pp. 14–15 (PDF 16–17); proof of Theorem 3.5(i), p. 18 (PDF 20)

import Mathlib
import Definitions.Def_PDSEquiv_Machine

set_option autoImplicit false

open scoped ENNReal

namespace SampleMLS.ExpMoment

noncomputable section

open PDSEquiv

/-!
# Time, space, subroutine calls and encodings on the randomized log-cost RAM

S. Gaspers, *Monotone Local Search with Sample-Dependent Running Times*, arXiv:2611.01774
(sha256 da381dca…), §3.1, pp. 14–15 (PDF 16–17): "We assume that a randomized algorithm can draw a
uniform integer from {1, …, M} in time polynomial in log M"; proof of Theorem 3.5(i), p. 18
(PDF 20): "Besides the space of A, the algorithm stores one sample, the current pair and a trial
counter".

**Formalization Note.** The paper names no machine. Programs run on the published randomized log-cost
oracle RAM `PDSEquiv.Machine` (exact `Ber(a/b)` draws charged by bit lengths, so a uniform integer
from `{1, …, M}` and a uniform `t`-subset of an `n`-set are drawn exactly in polynomial time). This
module adds what that machine does not have:

* `runTime`: the log-cost of a run, the supremum over times and random branches (`⊤` if unbounded,
  e.g. if the program does not halt; an unhalted step always costs at least one).
* `runSpace`: the memory of a run, the supremum over times and branches of the occupied registers
  and memory cells, each nonzero cell `a` holding `v` counting `1 + bits a + bits v`.
* Subroutine calls. An algorithm that runs a deterministic algorithm `A` as a subroutine is an oracle
  program whose oracle answers a query `q` with `A`'s output on `q` (`subOracle A`). Its time is its
  own log-cost plus the running time of `A` on every call made (`CompositeTimeWithin`); its space is
  its own space plus the space of `A`, which the caller reuses across calls.
* Encodings of instances (binary strings `I`, `N = |I|`), finite sets of naturals, integers and
  rationals as lists of naturals, and the outputs `[1]` (yes) and `[0]` (no).
-/

/-- A deterministic program: it never draws a Bernoulli variable and never calls an oracle. -/
def IsDeterministic (P : Program) : Prop :=
  ∀ i ∈ P, (∀ d a b : ℕ, i ≠ Instr.ber d a b) ∧ ∀ d a l : ℕ, i ≠ Instr.query d a l

/-- The running time (log-cost) of `P` with oracle `Q` on `input`: the largest cost reached on any
random branch at any time, `⊤` if the cost is unbounded. -/
def runTime (P : Program) (Q : Oracle) (input : List ℕ) : ℝ≥0∞ :=
  ⨆ t, ⨆ s ∈ (runLaw P Q input t).support, (s.cost : ℝ≥0∞)

/-- The space taken by a register or memory cell `a` holding `v`: nothing if `v = 0`, otherwise one
plus the bit lengths of the address and of the contents. -/
def cellSpace (a v : ℕ) : ℝ≥0∞ :=
  if v = 0 then 0 else ((1 + bits a + bits v : ℕ) : ℝ≥0∞)

/-- The space of a machine state: all nonzero memory cells and registers. -/
def stateSpace (s : MState) : ℝ≥0∞ :=
  (∑' a : ℕ, cellSpace a (s.mem a)) + ∑' r : ℕ, cellSpace r (s.reg r)

/-- The space of a run: the largest space of a state reached on any branch at any time. -/
def runSpace (P : Program) (Q : Oracle) (input : List ℕ) : ℝ≥0∞ :=
  ⨆ t, ⨆ s ∈ (runLaw P Q input t).support, stateSpace s

open Classical in
/-- The output of a deterministic program `A` on `q`: the list it halts with (probability one), and
`[]` if there is none. -/
def detOut (A : Program) (q : List ℕ) : List ℕ :=
  if h : ∃ ℓ, outMass A noOracle q ℓ = 1 then h.choose else []

/-- The oracle through which a program calls the deterministic subroutine `A`. -/
def subOracle (A : Program) : Oracle := fun q => PMF.pure (detOut A q)

/-- `P`, calling `A` as a subroutine, runs within time `B` on `input`: on every random branch, at every
time, its own log-cost plus the running times of `A` on all calls made so far is at most `B`, and it
has halted by time `B`. -/
def CompositeTimeWithin (P A : Program) (input : List ℕ) (B : ℝ) : Prop :=
  ∀ t, ∀ s ∈ (runLaw P (subOracle A) input t).support,
    (s.cost : ℝ≥0∞) + (s.queries.map fun q => runTime A noOracle q).sum ≤ ENNReal.ofReal B ∧
    (B ≤ (t : ℝ) → s.out.isSome = true)

/-- A deterministic computation on `input` within time `B` whose output satisfies `form` (the time
bound forces halting on every branch). -/
def DetComputes (R : Program) (input : List ℕ) (B : ℝ≥0∞) (form : List ℕ → Prop) : Prop :=
  IsDeterministic R ∧ runTime R noOracle input ≤ B ∧ OutputsSatisfy R noOracle input form

/-- The answer yes. -/
def yesOut : List ℕ := [1]

/-- The answer no. -/
def noOut : List ℕ := [0]

/-- A binary string as a list of bits. -/
def encBits (I : List Bool) : List ℕ := I.map fun b => if b then 1 else 0

/-- The encoding of an instance `I ∈ {0,1}*`: its length `N`, then its bits. -/
def encI (I : List Bool) : List ℕ := I.length :: encBits I

/-- The encoding of a finite set of naturals: its size, then its elements in increasing order. -/
def encSet (X : Finset ℕ) : List ℕ := X.card :: X.sort (· ≤ ·)

/-- The input `(I, k)`. -/
def encIk (I : List Bool) (k : ℕ) : List ℕ := encI I ++ [k]

/-- The input `(I, S)` of a membership test. -/
def encISet (I : List Bool) (S : Finset ℕ) : List ℕ := encI I ++ encSet S

/-- The input `(I, X, k)` of Φ-Extension. -/
def encIXk (I : List Bool) (X : Finset ℕ) (k : ℕ) : List ℕ := encI I ++ k :: encSet X

/-- The output encoding of an integer: sign bit, then absolute value. -/
def encInt (z : ℤ) : List ℕ := [if z < 0 then 1 else 0, z.natAbs]

/-- The rational number an output `[s, a, b]` with `s ≤ 1` and `0 < b` encodes, `(−1)^s a / b`. -/
def decodeRat : List ℕ → Option ℝ
  | [s, a, b] => if s ≤ 1 ∧ 0 < b then some ((if s = 1 then -1 else 1) * (a : ℝ) / b) else none
  | _ => none

/-- An output encoding a rational within `2^{-j}` of `x`. -/
def ApproxOut (x : ℝ) (j : ℕ) (o : List ℕ) : Prop :=
  ∃ v : ℝ, decodeRat o = some v ∧ |v - x| ≤ (2 : ℝ) ^ (-(j : ℤ))

end

end SampleMLS.ExpMoment


