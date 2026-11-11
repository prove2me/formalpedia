-- Prove2me | Definitions.Def_DenseMatching_IPM_PointerMachine
-- name    : DenseMatching_IPM_PointerMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:39:47.061303+00:00
-- url     : https://prove2.me/theorems/150bc821-6976-4278-91e8-d0e7325f96e9
-- title:
--   §2 — the randomized pointer machine: K⌈log₂ N⌉-bit integer words, +, −, ×, div, mod, comparison, pointer fields, uniform/Gaussian/Poisson draws, runs, time and the input layout
-- statement:
--   The model of computation of the paper (p. 7): values are stored in $O(\log n)$-bit words addressed by pointers; time is the number of operations on words plus the number of pointer dereferences; words are never addressed by an integer, and values in words are manipulated only through addition, subtraction, multiplication, integer division, remainder and comparison; there are primitives for uniform, Gaussian and Poisson random samples.
--
--   **Memory.** A heap of records (nodes), each with pointer fields and integer word fields; pointer registers and word registers. A pointer is nil or a reference to a node created earlier. No instruction converts a pointer to a word or a word to a pointer.
--
--   **Words.** For a program with word factor $K$ (part of the program) on an input with $n$ vertices, a word is an integer $x$ with $|x|<2^{w}$,
--   $$w=K\cdot\lceil\log_2 N\rceil,\qquad N=\max(n,4).$$
--   A word result outside this range is a **fault**.
--
--   **Instructions** (each costs one step): create a node; set a pointer register to nil, copy it, load it from or store it into a pointer field (dereferencing nil is a fault); load or store a word field; word constant and copy; $+,-,\times$, integer division and remainder (Euclidean convention; division by $0$ is a fault); jump if $W[a]<W[b]$, jump if two pointers are equal, unconditional jump; three random draws; `halt`. Draws, with $h=\lfloor w/2\rfloor$:
--   - uniform: a uniform word in $\{0,\dots,2^w-1\}$;
--   - Gaussian: $\operatorname{round}(2^{h}g)$ for $g\sim N(0,1)$, clipped to the word range;
--   - Poisson: a Poisson sample of rate $a/2^{h}$ for a rate word $a\ge 0$ (a negative rate is a fault), clipped to the word range.
--
--   **Randomness.** The tape is an i.i.d. sequence of cells $(U,g,V)$, $U,V$ uniform on $[0,1]$, $g$ standard Gaussian; the $j$-th draw of a run reads cell $j$ (uniform word $\min(2^w-1,\lfloor 2^w U\rfloor)$; Poisson sample by inversion of its distribution function at $V$). Each draw thus has exactly the stated law, and distinct draws are independent.
--
--   **Input and output.** Vertices are nodes $0,\dots,n-1$ in a linked list (pointer field 0 = next; word field 0 = side, $0$ for $L$, $1$ for $R$); edges are further nodes in a linked list in the order of the input list (pointer field 0 = next, fields 1 and 2 = the two endpoint nodes). Pointer register 0 holds the first vertex, register 1 the first edge. The output is word register $0$ at `halt`.
--
--   **Runs and time.** A run executes one instruction per step; after `halt` or a fault it no longer changes. `SucceedsWithin P G T ω` says that for some $t\le T$ the run of $P$ on $G$ with tape $\omega$ has halted (so no fault occurred) after $t$ steps with output $\nu(G)$. `timeBound C n` $=C\,N^2(\log_2 N)^4(\log_2\log_2 N)^C$ with $N=\max(n,4)$ is the reading of $\ddot O(n^2\log^4 n)$, where $\ddot O$ hides $(\log\log n)^{O(1)}$ factors (footnote 1, p. 1).
--
--   **Formalization Note.** The random primitives "with $n^{-O(1)}$ error, the same order as the rounding error … of integer division on $O(\log n)$-bit words" (p. 7) are read as the exact laws of these word-precision discretizations. There is no real arithmetic, no exp/log/sqrt, no bitwise operation, no address arithmetic and no weighted-sampling primitive (the $O(\log t)$ weighted sampler of p. 8 is built from augmented search trees). A stronger machine would make the existential goal weaker.
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 7, §2 (and p. 1, footnote 1)

import Mathlib
import Definitions.Def_DenseMatching_IPM_Bipartite

namespace DenseMatching.IPM

/-!
# The randomized pointer machine of §2 (p. 7)

Dai, Peng, Sleator, Stepin, Yang, *Approaching Optimality for Dense Bipartite Matching*, STOC 2027
submission (manuscript sha256 0bdeb447…), p. 7: "values are stored in O(log n) bit words, which are
in turn addressed by pointers … The time of an algorithm is then measured by the number of
operations on words plus the number of pointer dereferences. Words are never addressed by an
integer, and values in words are only manipulated through addition, subtraction, multiplication,
integer division, remainder and comparison of integers … we assume there are primitives that
generate random samples from uniform, Gaussian, and Poisson distributions".

**Formalization Note.**
* Memory is a heap of records (nodes). Each node has pointer fields and integer word fields, indexed
  by natural numbers (a program, being a finite list, uses finitely many of them). The machine has
  pointer registers and word registers, also indexed by natural numbers.
* A pointer is `none` (nil) or `some i`, the `i`-th node created. No instruction turns a pointer into
  a word or a word into a pointer: words are never used as addresses, and pointers can only be
  copied, compared for equality and dereferenced.
* A word holds an integer `x` with `|x| < 2 ^ w`, where `w = K · ⌈log₂ N⌉`, `N = max(n, 4)`, `n` the
  number of input vertices and `K` (`Program.wordFactor`) a constant chosen by the program. A
  word result outside this range is a *fault*, as are dereferencing nil, division or remainder by
  zero, a negative Poisson rate, and a program counter outside the program. A faulted run never
  halts.
* Word operations: constants, copy, `+`, `−`, `×`, integer division `/` and remainder `%` (Lean's
  Euclidean convention on `ℤ`: the remainder lies in `[0, |b|)`), comparison with a conditional
  jump. There are no bitwise operations and no exp, log or square root.
* Random draws, each consuming the next cell of the tape (see `tapeMeasure`); `h = ⌊w/2⌋`:
  `drawUniform`: a uniform word in `[0, 2^w)`; `drawGaussian`: `round(2^h · g)` for `g ~ N(0,1)`,
  clipped to the word range; `drawPoisson a b`: a Poisson sample of rate `W[b] / 2^h`, clipped to the
  word range. This is the mission's reading of "primitives … with n^{−O(1)} error": exact laws of
  the word-precision discretizations.
* Every executed instruction costs one step (pointer dereferences and draws included). After
  `halt` (or a fault) the configuration no longer changes.
-/

/-- A pointer: `none` is nil, `some i` is the `i`-th node created. -/
abbrev Ptr := Option ℕ

/-- A record of the heap: pointer fields and word fields. -/
structure Node where
  /-- pointer field `j` -/
  ptrField : ℕ → Ptr
  /-- word field `j` -/
  wordField : ℕ → ℤ

/-- The fresh node: every pointer field nil, every word field `0`. -/
def Node.empty : Node := ⟨fun _ => none, fun _ => 0⟩

/-- The instructions. `P[p]` is pointer register `p`, `W[a]` word register `a`; `.ptr j` and
`.word j` are the fields of the node a pointer refers to. Labels are positions in the program.
* `newNode p`: `P[p] :=` a new node with nil pointer fields and zero word fields.
* `setNil p`: `P[p] := nil`;  `copyPtr p q`: `P[p] := P[q]`.
* `loadPtr p q j`: `P[p] := P[q].ptr j`;  `storePtr q j p`: `P[q].ptr j := P[p]`.
* `loadWord a q j`: `W[a] := P[q].word j`;  `storeWord q j a`: `P[q].word j := W[a]`.
* `const a k`: `W[a] := k`;  `copyWord a b`: `W[a] := W[b]`.
* `add a b c`, `sub a b c`, `mul a b c`, `div a b c`, `mod a b c`: `W[a] := W[b] ∘ W[c]`.
* `jumpLt a b l`: go to `l` if `W[a] < W[b]`;  `jumpPtrEq p q l`: go to `l` if `P[p] = P[q]`;
  `jump l`: go to `l`.
* `drawUniform a`, `drawGaussian a`, `drawPoisson a b`: random draws into `W[a]`.
* `halt`: stop; the output is `W[0]`. -/
inductive Instr where
  | newNode (p : ℕ)
  | setNil (p : ℕ)
  | copyPtr (p q : ℕ)
  | loadPtr (p q j : ℕ)
  | storePtr (q j p : ℕ)
  | loadWord (a q j : ℕ)
  | storeWord (q j a : ℕ)
  | const (a : ℕ) (k : ℤ)
  | copyWord (a b : ℕ)
  | add (a b c : ℕ)
  | sub (a b c : ℕ)
  | mul (a b c : ℕ)
  | div (a b c : ℕ)
  | mod (a b c : ℕ)
  | jumpLt (a b l : ℕ)
  | jumpPtrEq (p q l : ℕ)
  | jump (l : ℕ)
  | drawUniform (a : ℕ)
  | drawGaussian (a : ℕ)
  | drawPoisson (a b : ℕ)
  | halt

/-- A program: the word-size factor `K` and a finite list of instructions. Both are fixed before
the input is seen. -/
structure Program where
  /-- `K`: words have `K · ⌈log₂ max(n, 4)⌉` bits -/
  wordFactor : ℕ
  /-- the instructions; execution starts at position `0` -/
  code : List Instr

/-- The run status. -/
inductive Status where
  | running
  | halted
  | faulted
  deriving DecidableEq

/-- A configuration: program counter, pointer and word registers, the heap (`heap i` is node `i`,
valid for `i < size`), the number of nodes created, the tape cursor and the status. -/
structure Config where
  pc : ℕ
  ptrReg : ℕ → Ptr
  wordReg : ℕ → ℤ
  heap : ℕ → Node
  size : ℕ
  cursor : ℕ
  status : Status

/-- The number of bits of a word of `P` on inputs with `n` vertices:
`w = K · ⌈log₂ N⌉`, `N = max(n, 4)`. -/
def wordBits (P : Program) (n : ℕ) : ℕ := P.wordFactor * Nat.clog 2 (max n 4)

/-- A cell of the random tape: a uniform `U ∈ [0, 1]`, a standard Gaussian `g`, and a uniform
`V ∈ [0, 1]` (used by the Poisson draw). Each draw instruction consumes one whole cell. -/
abbrev Cell := unitInterval × ℝ × unitInterval

/-- The law of one cell: uniform ⊗ standard Gaussian ⊗ uniform. -/
noncomputable def cellLaw : MeasureTheory.Measure Cell :=
  (MeasureTheory.volume : MeasureTheory.Measure unitInterval).prod
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (MeasureTheory.volume : MeasureTheory.Measure unitInterval))

/-- The random tape: independent cells, each with law `cellLaw` (an infinite product of
probability measures). -/
noncomputable def tapeMeasure : MeasureTheory.Measure (ℕ → Cell) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => cellLaw)

/-- Clip an integer to the word range `[-(2^w - 1), 2^w - 1]`. -/
def clipWord (w : ℕ) (x : ℤ) : ℤ := max (-(2 ^ w - 1)) (min (2 ^ w - 1) x)

/-- The Poisson(`λ`) sample obtained from a uniform `v ∈ [0, 1]` by inversion of the distribution
function: the least `k` with `v < ∑_{j ≤ k} e^{-λ} λ^j / j!`. For `v` uniform this has exactly the
Poisson(`λ`) law (the value `0` for the null event `v = 1` is irrelevant). -/
noncomputable def poissonInv (lam v : ℝ) : ℕ :=
  sInf {k : ℕ | v < ∑ j ∈ Finset.range (k + 1), Real.exp (-lam) * lam ^ j / (Nat.factorial j)}

/-- The uniform word drawn from a cell: `⌊2^w U⌋`, capped at `2^w − 1` (the cap only matters on the
null event `U = 1`). It is uniform on `{0, …, 2^w − 1}`. -/
noncomputable def uniformWord (w : ℕ) (cell : Cell) : ℤ :=
  min (2 ^ w - 1) ⌊(2 : ℝ) ^ w * (cell.1 : ℝ)⌋

/-- The Gaussian word drawn from a cell: `round(2^{⌊w/2⌋} g)`, clipped to the word range. -/
noncomputable def gaussianWord (w : ℕ) (cell : Cell) : ℤ :=
  clipWord w (round ((2 : ℝ) ^ (w / 2) * cell.2.1))

/-- The Poisson word drawn from a cell for the rate word `a ≥ 0`: a Poisson sample of rate
`a / 2^{⌊w/2⌋}`, clipped to the word range. -/
noncomputable def poissonWord (w : ℕ) (a : ℤ) (cell : Cell) : ℤ :=
  clipWord w (poissonInv ((a : ℝ) / (2 : ℝ) ^ (w / 2)) (cell.2.2 : ℝ))

/-- One step of program `P` with `w`-bit words on tape `ω`. Halted and faulted configurations do
not change; every other step executes one instruction. -/
noncomputable def step (P : Program) (w : ℕ) (ω : ℕ → Cell) (s : Config) : Config :=
  match s.status with
  | .halted => s
  | .faulted => s
  | .running =>
    let nxt : Config := { s with pc := s.pc + 1 }
    let fault : Config := { s with status := .faulted }
    let setW (base : Config) (a : ℕ) (x : ℤ) : Config :=
      if |x| < 2 ^ w then { base with wordReg := Function.update s.wordReg a x } else fault
    match P.code[s.pc]? with
    | none => fault
    | some .halt => { s with status := .halted }
    | some (.newNode p) =>
        { nxt with
          ptrReg := Function.update s.ptrReg p (some s.size)
          heap := Function.update s.heap s.size Node.empty
          size := s.size + 1 }
    | some (.setNil p) => { nxt with ptrReg := Function.update s.ptrReg p none }
    | some (.copyPtr p q) => { nxt with ptrReg := Function.update s.ptrReg p (s.ptrReg q) }
    | some (.loadPtr p q j) =>
        match s.ptrReg q with
        | none => fault
        | some i => { nxt with ptrReg := Function.update s.ptrReg p ((s.heap i).ptrField j) }
    | some (.storePtr q j p) =>
        match s.ptrReg q with
        | none => fault
        | some i =>
            { nxt with
              heap := Function.update s.heap i
                ({ (s.heap i) with ptrField := Function.update (s.heap i).ptrField j (s.ptrReg p) }) }
    | some (.loadWord a q j) =>
        match s.ptrReg q with
        | none => fault
        | some i => setW nxt a ((s.heap i).wordField j)
    | some (.storeWord q j a) =>
        match s.ptrReg q with
        | none => fault
        | some i =>
            { nxt with
              heap := Function.update s.heap i
                ({ (s.heap i) with wordField := Function.update (s.heap i).wordField j (s.wordReg a) }) }
    | some (.const a k) => setW nxt a k
    | some (.copyWord a b) => setW nxt a (s.wordReg b)
    | some (.add a b c) => setW nxt a (s.wordReg b + s.wordReg c)
    | some (.sub a b c) => setW nxt a (s.wordReg b - s.wordReg c)
    | some (.mul a b c) => setW nxt a (s.wordReg b * s.wordReg c)
    | some (.div a b c) => if s.wordReg c = 0 then fault else setW nxt a (s.wordReg b / s.wordReg c)
    | some (.mod a b c) => if s.wordReg c = 0 then fault else setW nxt a (s.wordReg b % s.wordReg c)
    | some (.jumpLt a b l) => if s.wordReg a < s.wordReg b then { s with pc := l } else nxt
    | some (.jumpPtrEq p q l) => if s.ptrReg p = s.ptrReg q then { s with pc := l } else nxt
    | some (.jump l) => { s with pc := l }
    | some (.drawUniform a) =>
        setW { nxt with cursor := s.cursor + 1 } a (uniformWord w (ω s.cursor))
    | some (.drawGaussian a) =>
        setW { nxt with cursor := s.cursor + 1 } a (gaussianWord w (ω s.cursor))
    | some (.drawPoisson a b) =>
        if s.wordReg b < 0 then fault
        else setW { nxt with cursor := s.cursor + 1 } a (poissonWord w (s.wordReg b) (ω s.cursor))

/-- The initial configuration on the input `G` (input layout).
* Nodes `0, …, n − 1` are the vertices, in order: vertex `i` has pointer field `0` = the next vertex
  (nil after the last) and word field `0` = its side (`0` for `L`, `1` for `R`).
* Nodes `n, …, n + m − 1` are the edges, in the order of `G.edges`: the edge `(u, v)` has pointer
  field `0` = the next edge (nil after the last), pointer field `1` = the node of `u` and pointer
  field `2` = the node of `v`.
* Pointer register `0` holds the first vertex (nil if `n = 0`), pointer register `1` the first edge
  (nil if there is none); all other registers are nil or `0`; the program counter and the tape
  cursor are `0`. -/
noncomputable def initConfig {n : ℕ} (G : BipartiteInput n) : Config where
  pc := 0
  ptrReg := fun r =>
    if r = 0 then (if 0 < n then some 0 else none)
    else if r = 1 then (if 0 < G.edges.length then some n else none)
    else none
  wordReg := fun _ => 0
  heap := fun i =>
    if h : i < n then
      ⟨fun j => if j = 0 then (if i + 1 < n then some (i + 1) else none) else none,
       fun j => if j = 0 then (if G.side ⟨i, h⟩ then 1 else 0) else 0⟩
    else if h' : i - n < G.edges.length then
      ⟨fun j =>
          if j = 0 then (if i - n + 1 < G.edges.length then some (i + 1) else none)
          else if j = 1 then some (G.edges[i - n]'h').1.val
          else if j = 2 then some (G.edges[i - n]'h').2.val
          else none,
       fun _ => 0⟩
    else Node.empty
  size := n + G.edges.length
  cursor := 0
  status := .running

/-- The configuration of `P` after `t` steps on input `G` and tape `ω`. -/
noncomputable def runFor (P : Program) {n : ℕ} (G : BipartiteInput n) (ω : ℕ → Cell) (t : ℕ) :
    Config :=
  (step P (wordBits P n) ω)^[t] (initConfig G)

/-- `P` succeeds on `G` within time `T` on tape `ω`: for some number of steps `t ≤ T` the run has
halted (with no fault before), and its output word `W[0]` is the maximum matching size `ν(G)`. -/
def SucceedsWithin (P : Program) {n : ℕ} (G : BipartiteInput n) (T : ℝ) (ω : ℕ → Cell) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ (runFor P G ω t).status = .halted ∧
    (runFor P G ω t).wordReg 0 = (matchingNumber G : ℤ)

/-- The time bound `C · N² · (log₂ N)⁴ · (log₂ log₂ N)^C` with `N = max(n, 4)`: the reading of
`Ö(n² log⁴ n)`, where `Ö` hides `(log log n)^{O(1)}` factors (footnote 1, p. 1). -/
noncomputable def timeBound (C n : ℕ) : ℝ :=
  let N : ℝ := (max n 4 : ℕ)
  (C : ℝ) * N ^ 2 * (Real.logb 2 N) ^ 4 * (Real.logb 2 (Real.logb 2 N)) ^ C

end DenseMatching.IPM


