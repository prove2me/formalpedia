-- Prove2me | Definitions.Def_ContractionLemma_Supplement_Classes
-- name    : ContractionLemma_Supplement_Classes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:19:52.853855+00:00
-- url     : https://prove2.me/theorems/58e8a5b1-2327-4fa1-887e-9a2f7fe7597b
-- title:
--   Classical time classes, advice, E and NE, MINKT, KT and MKTP (§2.6, Definitions 2.7–2.11, App. B.2)
-- statement:
--   All classes are classes of languages $L\subseteq\{0,1\}^*$. A local machine $M$ (fixed parameters and program) is run with a clock of $c\,(t(n)+1)$ steps on inputs of length $n$, $c$ depending on the machine only (time $O(t)$; for $n\ge1$ this is $c\,t(n)$ up to the constant). With $\#M(x)$ its number of accepting nondeterministic paths and $p_M(x)$ its acceptance probability with fair coins (Definition 2.8):
--
--   1. $\mathsf{DTIME}[t]$: a deterministic $M$ accepts exactly $L$; $\mathsf{NTIME}[t]$: $x\in L\iff\#M(x)>0$; $\mathsf{coNTIME}[t]$: $x\in L\iff\#M(x)=0$; $\oplus\mathsf{TIME}[t]$: $\#M(x)$ odd; $\mathsf{PPTIME}[t]$: $p_M(x)>1/2$; $\mathsf{BPTIME}[t]$: $p_M\ge2/3$ on $L$, $\le1/3$ off $L$;
--   2. $\mathsf{PostBPTIME}[t]$: a postselection bit, $1$ with positive probability, with conditional acceptance $\ge2/3$ / $\le1/3$;
--   3. $\mathsf{MATIME}[t]$: a witness $|w|\le c\,(t(n)+1)$, some $w$ giving $\ge2/3$ on $L$, every $w$ at most $1/3$ off $L$;
--   4. $\Sigma_2\mathsf{TIME}[t]$: an alternating machine whose existential states all precede its universal states.
--
--   Oracle classes $\mathcal C[t]^A$ use oracle machines; $L\in i.o.\text{-}\mathcal C[t]/a$ if a machine of the class, given on inputs of length $n$ a fixed advice string of length at most $a(n)$, decides $L$ at length $n$ for infinitely many $n$ (Definition 2.10). $\mathsf E=\bigcup_c\mathsf{DTIME}[2^{cn}]$, $\mathsf{NE}=\bigcup_c\mathsf{NTIME}[2^{cn}]$ (Definition 2.7). $t$ is **time-constructible** if $t(n)$ is computable from $1^n$ in time $C(t(n)+1)$, and the **range (1)** is $n\le t(n)=o(n\sqrt{\log n})$.
--
--   $\mathsf{MINKT}_U$ is the set of $(x,1^T,1^s)$ such that some program $p$ with $|p|\le s$ makes $U$, started with $p$ on its input tape, halt within $T$ steps with exactly $x$ on its output tape (Definition 2.11, §4.1). For a machine $U$ with random access to a string $d$, $(d,t)$ **describes** $x$ if $U^d(i,b)$ accepts within $t$ steps iff $x_i=b$, for all $i\le|x|+1$ and $b\in\{0,1,*\}$, with $x_{|x|+1}=*$; it is an **$r$-query description** if moreover $U$ makes at most $r$ queries on each input; $\mathsf{MKTP}=\{(x,\theta):\mathrm{KT}(x)\le\theta\}$ (App. B.2).
--
--   These are the classes and problems of Theorems 3, 10.2, 10.4, 12, 13 and B.1.
--
--   **Formalization Note** Acceptance is being in an accepting halting state at the clock. E and NE use local machines, which simulate multitape machines with constant overhead and conversely. Random access to $d$ is an oracle step on a binary address (least significant bit first), out-of-range addresses answering $0$.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), §2.6, p.20; Definitions 2.7–2.11, pp.20–21; §4.1, p.25; App. B.2, p.103

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_LocalMachine
import Definitions.Def_ContractionLemma_Supplement_Quantum

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Filter Topology

/-- A language: a set of binary words (§2.6, p.20, "All classes are classes of languages
`L ⊆ {0,1}*`"). -/
abbrev Lang := List Bool → Prop

/-- **The five classical acceptance conditions of `C^cl_t`** — Gajulapalli, *The Contraction Lemma
Beyond ETH* (manuscript, sha256 049caea1…), Definition 2.8, pp.20–21, and Theorem 10.2, p.41:
bounded error (`BP`), nondeterministic (`N`), co-nondeterministic (`coN`), unbounded error (`PP`),
parity (`Par`). -/
inductive ClKind
  | BP
  | N
  | coN
  | PP
  | Par

/-- `M` (with oracle `A`, auxiliary word `aux`, clocked at `T` steps) decides correctly whether
`x ∈ L` (`inL`) under the acceptance condition `kind` (Definition 2.8). -/
def ClDecides {p : LocalParams} (kind : ClKind) (M : LProgram p) (A : Lang) (x aux : List Bool)
    (T : ℕ) (inL : Prop) : Prop :=
  match kind with
  | .BP => (inL → (2 : ℝ) / 3 ≤ M.accProb A x aux T) ∧ (¬ inL → M.accProb A x aux T ≤ 1 / 3)
  | .N => (inL ↔ 0 < M.pathCount A x aux T)
  | .coN => (inL ↔ M.pathCount A x aux T = 0)
  | .PP => (inL ↔ 1 / 2 < M.accProb A x aux T)
  | .Par => (inL ↔ Odd (M.pathCount A x aux T))

/-- **The classes `BPTIME[t]^A`, `NTIME[t]^A`, `coNTIME[t]^A`, `PPTIME[t]^A`, `⊕TIME[t]^A`**
(Definitions 2.8 and 2.10): some local machine (fixed parameters, fixed program) clocked at `c·t(n)`
steps on inputs of length `n` decides `L` with oracle `A`. The plain classes take the empty oracle.

**Formalization Note.** "Time `O(t)`" is a clock of `c·(t(n)+1)` steps, `c` depending on the machine
only (p.20; for `n ≥ 1` this is `c·t(n)` up to the constant, and at `n = 0` it avoids a clock of `0`
steps); acceptance means being in an accepting halting state at the clock (halting states are
absorbing, so this is acceptance by time `c·t(n)`). -/
def ClClass (kind : ClKind) (t : ℕ → ℕ) (A : Lang) (L : Lang) : Prop :=
  ∃ (p : LocalParams) (M : LProgram p) (c : ℕ),
    ∀ x : List Bool, ClDecides kind M A x [] (c * (t x.length + 1)) (L x)

/-- `DTIME[t]^A` (Definitions 2.8, 2.10): a deterministic local machine accepts exactly `L`. -/
def DTIMEo (t : ℕ → ℕ) (A : Lang) (L : Lang) : Prop :=
  ∃ (p : LocalParams) (M : LProgram p) (c : ℕ), M.IsDet ∧
    ∀ x : List Bool, (L x ↔ M.AcceptsAt A x [] (c * (t x.length + 1)) (fun _ => false))

/-- `NTIME[t]^A` with queries of length at most `c·qlen(n)` on inputs of length `n`
(Theorem 10.4(b), "with queries of length `O(n^{9/10})`"). -/
def NTIMEoQ (t : ℕ → ℕ) (qlen : ℕ → ℝ) (A : Lang) (L : Lang) : Prop :=
  ∃ (p : LocalParams) (M : LProgram p) (c : ℕ),
    (∀ x : List Bool, M.QueriesBounded A x [] (c * (t x.length + 1)) (c * qlen x.length)) ∧
    ∀ x : List Bool, (L x ↔ 0 < M.pathCount A x [] (c * (t x.length + 1)))

/-- **PostBPTIME[t]** (Definition 2.8): the postselection bit is `1` with positive probability on
every input, and the acceptance probability conditioned on it is at least `2/3` on `L`, at most
`1/3` off `L`. -/
def PostBPTIME (t : ℕ → ℕ) (L : Lang) : Prop :=
  ∃ (p : LocalParams) (M : LProgram p) (c : ℕ), ∀ x : List Bool,
    0 < M.postCount (fun _ => False) x [] (c * (t x.length + 1)) ∧
    (L x → (2 : ℝ) / 3 * M.postCount (fun _ => False) x [] (c * (t x.length + 1)) ≤
      M.postAcceptCount (fun _ => False) x [] (c * (t x.length + 1))) ∧
    (¬ L x → (M.postAcceptCount (fun _ => False) x [] (c * (t x.length + 1)) : ℝ) ≤
      1 / 3 * M.postCount (fun _ => False) x [] (c * (t x.length + 1)))

/-- **MATIME[t]** (Definition 2.8): a probabilistic machine reads `x` and a witness `w` with
`|w| ≤ c·t(n)` (on its auxiliary tape); on `L` some witness gives acceptance probability at least
`2/3`, off `L` every witness gives at most `1/3`. -/
def MATIME (t : ℕ → ℕ) (L : Lang) : Prop :=
  ∃ (p : LocalParams) (M : LProgram p) (c : ℕ), ∀ x : List Bool,
    (L x → ∃ w : List Bool, w.length ≤ c * (t x.length + 1) ∧
      (2 : ℝ) / 3 ≤ M.accProb (fun _ => False) x w (c * (t x.length + 1))) ∧
    (¬ L x → ∀ w : List Bool, w.length ≤ c * (t x.length + 1) →
      M.accProb (fun _ => False) x w (c * (t x.length + 1)) ≤ 1 / 3)

/-- The run of an alternating machine: step `t` reads the universal choice `γ₂ t` in a universal
state and the existential choice `γ₁ t` otherwise. -/
noncomputable def altRun {p : LocalParams} (M : LProgram p) (x : List Bool) (T : ℕ)
    (γ₁ γ₂ : ℕ → Bool) : ℕ → LCfg p M
  | 0 => M.init x []
  | t + 1 =>
    let c := altRun M x T γ₁ γ₂ t
    M.step (fun _ => False) (M.readBound x [] T) (if M.univ c.state then γ₂ t else γ₁ t) c

/-- **Σ₂TIME[t]** (Definition 2.8): an alternating local machine running in time `O(t)`, whose
existential states all precede its universal states (on every run, once a universal state is reached
every later state is universal or halting), accepts exactly `L`: `x ∈ L` iff some existential choices
make every universal continuation accept. -/
def Sigma2TIME (t : ℕ → ℕ) (L : Lang) : Prop :=
  ∃ (p : LocalParams) (M : LProgram p) (c : ℕ),
    (∀ (x : List Bool) (γ₁ γ₂ : ℕ → Bool) (i j : ℕ), i ≤ j → j ≤ c * (t x.length + 1) →
      M.univ (altRun M x (c * (t x.length + 1)) γ₁ γ₂ i).state = true →
      M.univ (altRun M x (c * (t x.length + 1)) γ₁ γ₂ j).state = true ∨
        M.halting (altRun M x (c * (t x.length + 1)) γ₁ γ₂ j).state = true) ∧
    ∀ x : List Bool, (L x ↔ ∃ γ₁ : Fin (c * (t x.length + 1)) → Bool,
      ∀ γ₂ : Fin (c * (t x.length + 1)) → Bool,
        M.halting (altRun M x (c * (t x.length + 1)) (LProgram.ext γ₁) (LProgram.ext γ₂)
          (c * (t x.length + 1))).state = true ∧
        M.accept (altRun M x (c * (t x.length + 1)) (LProgram.ext γ₁) (LProgram.ext γ₂)
          (c * (t x.length + 1))).state = true)

/-- **The union of the eight classes of `C_t`** (p.8): `BPTIME[t]`, `NTIME[t]`, `coNTIME[t]`,
`PPTIME[t]`, `⊕TIME[t]`, `PostBPTIME[t]`, and `BQTIME[t]`, `PostBQTIME[t]` for the gate set `G`. -/
def InCt (G : GateSet) (t : ℕ → ℕ) (L : Lang) : Prop :=
  ClClass .BP t (fun _ => False) L ∨ ClClass .N t (fun _ => False) L ∨
  ClClass .coN t (fun _ => False) L ∨ ClClass .PP t (fun _ => False) L ∨
  ClClass .Par t (fun _ => False) L ∨ PostBPTIME t L ∨ BQTIME G t L ∨ PostBQTIME G t L

/-- `L ∈ C^cl_t = BPTIME[t] ∪ NTIME[t] ∪ coNTIME[t] ∪ PPTIME[t] ∪ ⊕TIME[t]` (Theorem 10.2). -/
def InCcl (t : ℕ → ℕ) (L : Lang) : Prop := ∃ kind : ClKind, ClClass kind t (fun _ => False) L

/-- **`L ∈ i.o.-C^cl_t/a`** (Definition 2.10): some machine of one of the five classes, given on
inputs of length `n` a fixed advice string of length at most `a(n)` (on its auxiliary tape), decides
`L` on all inputs of length `n`, for infinitely many lengths `n`. For bounded error the promise is
required only with that advice. -/
def IOAdvice (t a : ℕ → ℕ) (L : Lang) : Prop :=
  ∃ (kind : ClKind) (p : LocalParams) (M : LProgram p) (c : ℕ),
    Set.Infinite {n : ℕ | ∃ α : List Bool, α.length ≤ a n ∧
      ∀ x : List Bool, x.length = n → ClDecides kind M (fun _ => False) x α (c * (t n + 1)) (L x)}

/-- **E** (Definition 2.7): `⋃_c DTIME[2^{cn}]`. -/
def InE (L : Lang) : Prop := ∃ c : ℕ, DTIMEo (fun n => 2 ^ (c * n)) (fun _ => False) L

/-- **NE** (Definition 2.7): `⋃_c NTIME[2^{cn}]`. -/
def InNE (L : Lang) : Prop := ∃ c : ℕ, ClClass .N (fun n => 2 ^ (c * n)) (fun _ => False) L

/-- **`DTIME[2^{O(t/√log t)}]`** (Theorem 12): `⋃_c DTIME[⌈2^{c f(t(n))}⌉]`, `f(u) = u/√log(u+2)`. -/
def InDTIMEexpF (t : ℕ → ℕ) (L : Lang) : Prop :=
  ∃ c : ℕ, DTIMEo (fun n => ⌈(2 : ℝ) ^ (c * fScale (t n))⌉₊) (fun _ => False) L

/-- **Time-constructible** (§2.6, p.20): some machine, on input `1^n`, writes `t(n)` in binary
within `C·(t(n)+1)` steps.

**Formalization Note.** `O(t(n))` is `C·(t(n)+1)`: for `n ≥ 1` (where `t(n) ≥ n ≥ 1`) this is the
same bound up to the constant, and at `n = 0` it avoids the junk bound `0`, under which no machine
halts and `t(n) = n` would not be time-constructible. -/
def TimeConstructible (t : ℕ → ℕ) : Prop :=
  ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ n,
    RunsInTime A out (List.replicate n true) (countWord (t n)) (C * (t n + 1))

/-- **The range (1)** (p.9): `t` is time-constructible and `n ≤ t(n) = o(n √log n)`. -/
def Range1 (t : ℕ → ℕ) : Prop :=
  TimeConstructible t ∧ (∀ n, n ≤ t n) ∧
  Tendsto (fun n : ℕ => (t n : ℝ) / (n * Real.sqrt (Real.logb 2 (n + 2)))) atTop (𝓝 0)

open scoped Classical in
/-- **Decidable in time `2^{O(m)}` and space `poly(m)`** on `m`-bit queries (Theorems 8.2, 10.4(b)). -/
def ExpTimePolySpace (A : Lang) : Prop :=
  ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (c : ℕ), ∀ w : List Bool,
    ContractionLemma.RunsWithin D out w [decide (A w)] (c * (2 : ℝ) ^ (c * w.length))
      (c * ((w.length : ℝ) + 1) ^ c)

/-- **"`U` started with `p` on its input tape halts within `T` steps with exactly `x` on its output
tape"** (§4.1, p.25), for a deterministic local machine `U`: at time `T` the run is in a halting
state and the output tape holds `x` from cell `0`, blank elsewhere. -/
def Prints {p : LocalParams} (U : LProgram p) (prog x : List Bool) (T : ℕ) : Prop :=
  U.halting (U.run (fun _ => False) prog [] T (fun _ => false) T).state = true ∧
  ∀ i : ℤ, (U.run (fun _ => False) prog [] T (fun _ => false) T).tape U.outTape i = p.wordCell x i

/-- The encoding of a MINKT instance `(x, 1^T, 1^s)`. -/
def minktInput (x : List Bool) (T s : ℕ) : List Bool :=
  Encoding.encodeList id [x, List.replicate T true, List.replicate s true]

/-- **MINKT_U** (Definition 2.11, p.21): the triples `(x, 1^T, 1^s)` such that some program of
length at most `s` makes `U` print exactly `x` within `T` steps. -/
def MINKT {p : LocalParams} (U : LProgram p) : Lang := fun w =>
  ∃ (x : List Bool) (T s : ℕ), w = minktInput x T s ∧ ∃ prog : List Bool, prog.length ≤ s ∧ Prints U prog x T

/-- The oracle of a description `d` (App. B.2, p.103): the query word is a binary address (least
significant bit first); the reply is the bit of `d` at that address, `0` out of range. -/
def descOracle (d : List Bool) : Lang := fun w => d.getD (BinaryArithmetic.toNat w) false = true

/-- The input `(i, b)` of a B.2 machine: `i` in binary and `b ∈ {0, 1, ∗}` (`none` is `∗`). -/
def ktInput (i : ℕ) (b : Option Bool) : List Bool :=
  Encoding.encodeList id [countWord i, match b with | none => [false] | some v => [true, v]]

/-- The symbol `x_i` (`1 ≤ i ≤ |x| + 1`) with `x_{|x|+1} = ∗` (App. B.2, p.103). -/
def ktSym (x : List Bool) (i : ℕ) : Option Bool := if i ≤ x.length then some (x.getD (i - 1) false) else none

/-- **`(d, t)` describes `x`** (App. B.2, p.103): for all `1 ≤ i ≤ |x| + 1` and `b ∈ {0, 1, ∗}`,
`U^d(i, b)` accepts within `t` steps iff `x_i = b`. `U` is a deterministic local oracle machine whose
oracle is `descOracle d`. -/
def Describes {p : LocalParams} (U : LProgram p) (x d : List Bool) (t : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ x.length + 1 → ∀ b : Option Bool,
    (U.AcceptsAt (descOracle d) (ktInput i b) [] t (fun _ => false) ↔ ktSym x i = b)

/-- **An `r`-query description** (App. B.2): `(d, t)` describes `x`, and on each input `(i, b)` the
run of `t` steps makes at most `r` queries to `d`. -/
def RQueryDescribes {p : LocalParams} (U : LProgram p) (x d : List Bool) (t r : ℕ) : Prop :=
  Describes U x d t ∧ ∀ i : ℕ, 1 ≤ i → i ≤ x.length + 1 → ∀ b : Option Bool,
    U.queryCount (descOracle d) (ktInput i b) [] t ≤ r

/-- The encoding of an MKTP instance `(x, θ)`, `θ` in binary. -/
def mktpInput (x : List Bool) (θ : ℕ) : List Bool := Encoding.encodeList id [x, countWord θ]

/-- **MKTP** for the B.2 machine `U` (Definition 2.11 and App. B.2): the pairs `(x, θ)` with
`KT(x) ≤ θ`, i.e. some description `(d, t)` of `x` has `|d| + t ≤ θ`. -/
def MKTP {p : LocalParams} (U : LProgram p) : Lang := fun w =>
  ∃ (x : List Bool) (θ : ℕ), w = mktpInput x θ ∧ ∃ (d : List Bool) (t : ℕ), d.length + t ≤ θ ∧ Describes U x d t

open scoped Classical in
/-- The number of programs of length at most `s` that make `U` print `x` within `T` steps
(Theorem 3, p.25): binary strings `prog` with `|prog| ≤ s` and `Prints U prog x T`. -/
noncomputable def programCount {p : LocalParams} (U : LProgram p) (x : List Bool) (T s : ℕ) : ℕ :=
  ∑ ℓ ∈ Finset.range (s + 1),
    (Finset.univ.filter fun prog : Fin ℓ → Bool => Prints U (List.ofFn prog) x T).card

/-- `o` is `K^T_U(x)` (§4.1, p.25): `none` when `x` has no program, else the length of a shortest
program for `x`. -/
def IsKT {p : LocalParams} (U : LProgram p) (x : List Bool) (T : ℕ) : Option ℕ → Prop
  | none => ∀ prog : List Bool, ¬ Prints U prog x T
  | some k => (∃ prog : List Bool, prog.length = k ∧ Prints U prog x T) ∧
      ∀ prog : List Bool, Prints U prog x T → k ≤ prog.length

/-- `o` is a shortest program for `x` (`none` when `x` has no program). -/
def IsShortestProgram {p : LocalParams} (U : LProgram p) (x : List Bool) (T : ℕ) :
    Option (List Bool) → Prop
  | none => ∀ prog : List Bool, ¬ Prints U prog x T
  | some prog => Prints U prog x T ∧ ∀ prog' : List Bool, Prints U prog' x T → prog.length ≤ prog'.length

open scoped Classical in
/-- The number of `r`-query descriptions `(d, t)` of `x` with `|d| + t ≤ θ` (Theorem B.1, p.103). -/
noncomputable def numRQueryDesc {p : LocalParams} (U : LProgram p) (x : List Bool) (θ r : ℕ) : ℕ :=
  ∑ ℓ ∈ Finset.range (θ + 1), ∑ t ∈ Finset.range (θ + 1 - ℓ),
    (Finset.univ.filter fun d : Fin ℓ → Bool => RQueryDescribes U x (List.ofFn d) t r).card

/-- The input `(x, θ, r)` of Theorem B.1. -/
def b1Input (x : List Bool) (θ r : ℕ) : List Bool := Encoding.encodeList id [x, countWord θ, countWord r]

open scoped Classical in
/-- The admissible outputs of the three tasks of Theorem B.1: `0` decide whether an `r`-query
description with `|d| + t ≤ θ` exists (one bit), `1` count them (binary), `2` find one (`optWord`
of `(d, t)`, `none` when there is none). -/
def B1Answer {p : LocalParams} (U : LProgram p) (x : List Bool) (θ r : ℕ) :
    Fin 3 → List Bool → Prop
  | 0 => fun y => y = [decide (∃ (d : List Bool) (t : ℕ), d.length + t ≤ θ ∧ RQueryDescribes U x d t r)]
  | 1 => fun y => y = countWord (numRQueryDesc U x θ r)
  | 2 => fun y =>
      (y = optWord none ∧ ∀ (d : List Bool) (t : ℕ), d.length + t ≤ θ → ¬ RQueryDescribes U x d t r) ∨
      ∃ (d : List Bool) (t : ℕ), d.length + t ≤ θ ∧ RQueryDescribes U x d t r ∧
        y = optWord (some (Encoding.encodeList id [d, countWord t]))

end ContractionLemma.Supplement


