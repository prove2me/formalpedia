-- Prove2me | Definitions.Def_SparseWalsh_Approx_Machine
-- name    : SparseWalsh_Approx_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:02:26.527617+00:00
-- url     : https://prove2.me/theorems/1fe399e2-30b3-4e03-b45e-fae9f917bbd3
-- title:
--   The computational model of §2: a randomized real RAM with a binary bank, fair coins, a real-valued value query with a query log, and logarithmic cost for integers and addresses
-- statement:
--   Section 2 specifies the model as follows. Exact real arithmetic and comparisons cost one unit each. Binary computations are counted in elementary bit operations, and a frequency is $d$ bits, not one machine word. A value query at $x$ returns the exact value $f(x)$, and each oracle call has unit overhead. Query points may be updated in place, with a charge for each changed bit. Running time includes setup, query preparation, processing and output.
--
--   This definition makes that model precise as a randomized random-access machine that extends the published real pointer machine `SmaleNinth.RAMInstr`. A **program** is one finite list of instructions:
--   - real arithmetic $+,-,\times,\div$ with rational literals, and comparison jumps;
--   - integer pointers with set, copy, increment, decrement, $+$ and $-$, an integer memory, and a pointer-to-real cast;
--   - a **bit bank** of registers and memory over $\mathbb F_2$, with $0$, $1$, $+$, $\times$, load and store through a pointer, and jump on equality;
--   - a fair **coin**;
--   - a **value query**, which reads $d$ bits of bit memory as a point $x\in\mathbb F_2^d$, writes $f(x)$ to a real register, and appends $x$ to the **query log**;
--   - **halt**.
--
--   **Cost.** Every executed instruction costs $1$, plus the bit length of every integer value and every memory address it reads or writes. This is a logarithmic-cost RAM for integer data, so packing many bits into one integer gains nothing. A run's **work** is the sum of these costs. The coin tape is a sequence of independent fair bits.
--
--   **Input.** The integer cells $0$–$4$ hold $d$, $s$, the method ($0$ for repetition, $1$ for coding), the output flag ($0$ for $j=s$, $1$ for $j=2s$) and $k$ ($0$ for the general setting). Real cell $0$ holds $\varepsilon$.
--
--   **Output.** Integer cell $-1$ holds the number $n$ of entries. Entry $i<n$ has its frequency bit $j$ at bit cell $-1-id-j$ and its coefficient at real cell $-1-i$. Integer cell $-2$ is the abort flag. The decoded approximation is $h=\sum_{i<n}\mathrm{coeff}_i\,\chi_{\mathrm{freq}_i}$.
--
--   **Formalization Note.** The language has no floor, no real-to-integer cast, no `sqrt`, `exp` or `log`, and no instruction that reads $f$ other than `query`. Admissible programs use rational literals only. An invalid program counter is stuck and charged, so only `halt` halts, and a halted state stutters at no cost. The paper charges memory access at unit cost; logarithmic address cost differs from it by a factor logarithmic in the memory used, which the $\tilde O(\cdot)$ of Theorem 5.1 absorbs.
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 11 (value queries, non-adaptivity); p. 12 (Computational model); p. 27 (App. A.1)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_SparseWalsh_Approx_Fourier

open scoped BigOperators

namespace SparseWalsh.Approx

/-!
# The computational model of §2: a randomized real RAM with a binary bank, a fair coin, a
real-valued value query with a query log, and logarithmic cost for integers and addresses

Attias, Bshouty, Medvedev, Srebro, *Efficient Non-Adaptive Sparse Fourier Learning on the Boolean
Cube and Finite Abelian Groups*, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 11 ("A value
query at x returns the exact value f(x)", non-adaptivity), p. 12 ("Computational model"), p. 27
(App. A.1: "a frequency is not treated as one machine word"; "A coordinate index costs O(log(2d))
bits").

"We count exact real arithmetic and comparisons at unit cost, and binary computations in elementary
bit operations, with unit-cost memory access. … a frequency is represented by d bits. … Each oracle
call has unit overhead, excluding the oracle's internal evaluation cost. … Query points may be
updated in place between oracle calls. We charge for each changed bit."

**Formalization Note.**
* The scalar core is the published `SmaleNinth.RAMInstr` real pointer machine (exact `+ − × ÷` on
  reals with `x/0 = 0`, real literals, indirect real load and store through integer pointers,
  pointer set/copy/increment/decrement, jumps on `r ≤ 0` and `p ≤ p'`). Extensions: pointer `+`/`−`,
  an integer memory, a pointer-to-real cast, the **bit bank** (registers and memory over `ZMod 2`
  with `0`, `1`, `+`, `×`, load and store through a pointer, jump on equality), `coin`, `query`
  and `halt`.
* Not in the language: floor or any real-to-integer cast, `sqrt`, `exp`, `log`, pointer
  multiplication, irrational literals, a unit-cost uniform element of `F_2^d`, any instruction that
  reads `f` other than `query`. `Admissible` programs use rational literals only and no core
  `accept`/`reject`; this restricts the existentially chosen program, never the input.
* **Cost** (`work`). Every executed instruction costs `1` plus the bit length `bits z = ⌊log₂|z|⌋+1`
  (`0` for `z = 0`) of every integer value it reads or writes and of every memory address it uses
  (a logarithmic-cost RAM for integer and binary data: an integer packing `d` bits costs `Θ(d)` per
  operation, so "a frequency is not treated as one machine word"). Real arithmetic, real
  comparisons, bit operations, `coin`, `halt` and jumps cost `1` (plus the addresses and integer
  operands they touch); `query` costs `1` plus the bit length of its address (unit oracle
  overhead). The paper's unit-cost memory access differs from this by at most a logarithmic factor
  in the size of the memory used, which the `Õ(·)` of Theorem 5.1 absorbs.
* `query dst q` reads the `d` bits at bit-memory addresses `p[q], p[q]+1, …, p[q]+d−1` as a point
  `x ∈ F_2^d`, writes the exact real `f(x)` into real register `dst`, appends `x` to the **query
  log** and adds one to the query counter. Updating the query buffer in place is a sequence of bit
  stores, one per changed bit. The oracle `f` occurs only in this branch of `step`, the coin tape
  only in the `coin` branch.
* An invalid program counter is stuck and charged, so only `halt` halts; after `halt` the state
  stutters at no cost.
* Randomness is a tape of independent fair coins, one bit per executed `coin`; `coinTape` is the
  product of uniform laws on `Bool`.
* Input layout (`approxInit`): integer memory cells `0, 1, 2, 3, 4` hold `d`, `s`, the method
  (`0` repetition, `1` coding), the output flag (`0`: `j = s`, `1`: `j = 2s`) and `k` (`0`: the
  general setting); real memory cell `0` holds `ε`. Everything else is `0`.
* Output layout (read only from a halted state): integer cell `−1` holds the number `n` of output
  entries (a negative value counts as `0`); entry `i < n` has its frequency bit `j < d` at bit cell
  `−1 − i·d − j` and its real coefficient at real cell `−1 − i`; integer cell `−2` is the abort
  flag (nonzero = the run failed, e.g. a setup timeout). The decoded approximation is
  `h = Σ_{i<n} coeff_i χ_{freq_i}`.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]`.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]`.
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `coin d`: `b[d] := 1` if the next tape bit is `true`, else `0`; the cursor advances.
* `bitZero d`, `bitOne d`, `bitAdd d a b`, `bitMul d a b`: bit registers over `ZMod 2`.
* `bitLoad d q`, `bitStore q a`: `b[d] := BM[p[q]]`, `BM[p[q]] := b[a]`.
* `bitJeq a b target`: jump to `target` if `b[a] = b[b]`, else fall through.
* `query dst q`: value query at the point stored at `BM[p[q]], …, BM[p[q]+d−1]`.
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | coin (dst : ℕ)
  | bitZero (dst : ℕ)
  | bitOne (dst : ℕ)
  | bitAdd (dst a b : ℕ)
  | bitMul (dst a b : ℕ)
  | bitLoad (dst pointer : ℕ)
  | bitStore (pointer src : ℕ)
  | bitJeq (a b target : ℕ)
  | query (dst pointer : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every input. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core halting instructions do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P` (extension instructions are placeholders, dispatched by
`step`). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration (program counter, real registers, pointers, real
memory), integer memory, bit registers and bit memory, the coin-tape cursor, the halted flag, the
query counter, the query log and the work counter. -/
structure State (d : ℕ) where
  core : SmaleNinth.RAMConfig
  ints : ℤ → ℤ
  bregs : ℕ → ZMod 2
  bmem : ℤ → ZMod 2
  cursor : ℕ
  halted : Bool
  queries : ℕ
  queryLog : List (Cube d)
  work : ℕ

/-- The bit length of an integer: `⌊log₂ |z|⌋ + 1`, and `0` for `z = 0`. -/
def bits (z : ℤ) : ℕ := Nat.size z.natAbs

/-- The point of `F_2^d` stored at bit cells `base, base+1, …, base+d−1`. -/
def readPoint {d : ℕ} (bmem : ℤ → ZMod 2) (base : ℤ) : Cube d :=
  fun i => bmem (base + (i : ℕ))

/-- The cost of executing a core instruction in configuration `c`: `1` plus the bit lengths of
the integers and addresses it touches. -/
def coreCost (c : SmaleNinth.RAMConfig) : SmaleNinth.RAMInstr → ℕ
  | .load _ q => 1 + bits (c.ptrs q)
  | .store q _ => 1 + bits (c.ptrs q)
  | .pset _ z => 1 + bits z
  | .pcopy _ q' => 1 + bits (c.ptrs q')
  | .pinc q => 1 + bits (c.ptrs q) + bits (c.ptrs q + 1)
  | .pdec q => 1 + bits (c.ptrs q) + bits (c.ptrs q - 1)
  | .pjle q q' _ => 1 + bits (c.ptrs q) + bits (c.ptrs q')
  | _ => 1

/-- The cost of executing instruction `op` in state `s`. -/
def cost {d : ℕ} (s : State d) : Instr → ℕ
  | .core i => coreCost s.core i
  | .pointerAdd _ a b =>
      1 + bits (s.core.ptrs a) + bits (s.core.ptrs b) + bits (s.core.ptrs a + s.core.ptrs b)
  | .pointerSub _ a b =>
      1 + bits (s.core.ptrs a) + bits (s.core.ptrs b) + bits (s.core.ptrs a - s.core.ptrs b)
  | .integerLoad _ a => 1 + bits (s.core.ptrs a) + bits (s.ints (s.core.ptrs a))
  | .integerStore a b => 1 + bits (s.core.ptrs a) + bits (s.core.ptrs b)
  | .pointerReal _ a => 1 + bits (s.core.ptrs a)
  | .bitLoad _ q => 1 + bits (s.core.ptrs q)
  | .bitStore q _ => 1 + bits (s.core.ptrs q)
  | .query _ q => 1 + bits (s.core.ptrs q)
  | _ => 1

/-- One step of program `P` with value oracle `f` and coin tape `ω`. Halted states stutter at no
cost; every other step adds its cost to `work`. -/
noncomputable def step {d : ℕ} (P : Program) (f : Cube d → ℝ) (ω : ℕ → Bool) (s : State d) :
    State d :=
  if s.halted then s else
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some op =>
      let t : State d := { s with
        work := s.work + cost s op
        core := { s.core with pc := s.core.pc + 1 } }
      match op with
      | .core _ => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
      | .pointerAdd dst x y =>
          { t with core := { t.core with
              ptrs := Function.update s.core.ptrs dst (s.core.ptrs x + s.core.ptrs y) } }
      | .pointerSub dst x y =>
          { t with core := { t.core with
              ptrs := Function.update s.core.ptrs dst (s.core.ptrs x - s.core.ptrs y) } }
      | .integerLoad dst x =>
          { t with core := { t.core with
              ptrs := Function.update s.core.ptrs dst (s.ints (s.core.ptrs x)) } }
      | .integerStore x y =>
          { t with ints := Function.update s.ints (s.core.ptrs x) (s.core.ptrs y) }
      | .pointerReal dst x =>
          { t with core := { t.core with
              regs := Function.update s.core.regs dst (s.core.ptrs x : ℝ) } }
      | .coin dst =>
          { t with
            cursor := s.cursor + 1
            bregs := Function.update s.bregs dst (if ω s.cursor then 1 else 0) }
      | .bitZero dst => { t with bregs := Function.update s.bregs dst 0 }
      | .bitOne dst => { t with bregs := Function.update s.bregs dst 1 }
      | .bitAdd dst x y =>
          { t with bregs := Function.update s.bregs dst (s.bregs x + s.bregs y) }
      | .bitMul dst x y =>
          { t with bregs := Function.update s.bregs dst (s.bregs x * s.bregs y) }
      | .bitLoad dst q =>
          { t with bregs := Function.update s.bregs dst (s.bmem (s.core.ptrs q)) }
      | .bitStore q x =>
          { t with bmem := Function.update s.bmem (s.core.ptrs q) (s.bregs x) }
      | .bitJeq x y target =>
          if s.bregs x = s.bregs y then
            { t with core := { t.core with pc := target } }
          else t
      | .query dst q =>
          let pt : Cube d := readPoint s.bmem (s.core.ptrs q)
          { t with
            queries := s.queries + 1
            queryLog := s.queryLog ++ [pt]
            core := { t.core with regs := Function.update s.core.regs dst (f pt) } }
      | .halt => { t with halted := true }

/-- The state after `n` steps of `P` from `s₀`, with oracle `f` and coin tape `ω`. -/
noncomputable def run {d : ℕ} (P : Program) (f : Cube d → ℝ) (s₀ : State d) (ω : ℕ → Bool)
    (n : ℕ) : State d :=
  (step P f ω)^[n] s₀

/-- The fair-coin tape: the product of uniform laws on `Bool` over `ℕ`. -/
noncomputable def coinTape : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

/-- The start state: counters and registers `0`, empty query log; integer memory holds `ints`
from cell `0`, real memory holds `reals` from cell `0`; every other cell is `0`. -/
noncomputable def initState (d : ℕ) (ints : List ℤ) (reals : List ℝ) : State d :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0,
    fun _ => 0, fun _ => 0, 0, false, 0, [], 0⟩

/-- The input of Algorithm 3: integers `d, s, method (0 repetition, 1 coding), output flag
(0: j = s, 1: j = 2s), k (0: general setting)`; real `ε`. -/
noncomputable def approxInit (d s : ℕ) (ε : ℝ) (coding twoS : Bool) (k : ℕ) : State d :=
  initState d [(d : ℤ), (s : ℤ), (if coding then 1 else 0), (if twoS then 1 else 0), (k : ℤ)] [ε]

/-- The number of output entries (integer cell `−1`; a negative value counts as `0`). -/
def outLength {d : ℕ} (s : State d) : ℕ := (s.ints (-1)).toNat

/-- The frequency of output entry `i` (bit cells `−1 − i·d − j`, `j < d`). -/
def outFreq {d : ℕ} (s : State d) (i : ℕ) : Cube d :=
  fun j => s.bmem (-1 - (i : ℤ) * d - (j : ℕ))

/-- The coefficient of output entry `i` (real cell `−1 − i`). -/
def outCoeff {d : ℕ} (s : State d) (i : ℕ) : ℝ := s.core.mem (-1 - (i : ℤ))

/-- The output list of (frequency, coefficient) entries. -/
def outList {d : ℕ} (s : State d) : List (Cube d × ℝ) :=
  (List.range (outLength s)).map fun i => (outFreq s i, outCoeff s i)

/-- The decoded approximation `h = Σ_{i<n} coeff_i χ_{freq_i}`. -/
noncomputable def outPoly {d : ℕ} (s : State d) : Cube d → ℝ := poly (outList s)

/-- The abort flag (integer cell `−2`, nonzero = the run failed). -/
def aborted {d : ℕ} (s : State d) : Prop := s.ints (-2) ≠ 0

end SparseWalsh.Approx


