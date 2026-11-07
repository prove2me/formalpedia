-- Prove2me | Definitions.Def_NonadaptiveSFT_Machine
-- name    : NonadaptiveSFT_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:35.824002+00:00
-- url     : https://prove2.me/theorems/1d457d2b-7f7a-444e-b985-e0064cfe6f6a
-- title:
--   The exact arithmetic model of §2.3: a real RAM with a $\mathbb Z/2^a\mathbb Z$ coordinate bank, fair coins and point queries with a query log
-- statement:
--   The model in which "there is a randomized algorithm" is read. A program is one finite list of instructions, the same for every $a$, $d$ and input. The machine has real registers and a real memory, integer pointers and an integer memory, and a **coordinate bank** of registers and memory over $\mathbb Z/2^a\mathbb Z$. Its instructions are:
--
--   1. exact $+,-,\times,\div$ on reals (with $x/0=0$), rational literals, indirect load and store, comparison jumps $r\le0$ and $p\le p'$, and $\sqrt{\cdot}$;
--   2. pointer set, copy, increment, decrement, addition and subtraction, integer load and store, and a pointer-to-real cast;
--   3. on coordinates: the literals $0,1$, ring operations $+,-,\times$ in $\mathbb Z/2^a\mathbb Z$, load and store through a pointer, and a jump on equality;
--   4. a fair coin, a point query, and halt.
--
--   A point query reads the $d$ coordinates of a group element $t$ from coordinate memory, returns $\mathrm{Re}\,X(t)$ and $\mathrm{Im}\,X(t)$, and appends $t$ to the query log. Every executed instruction costs one unit of work; after halt the state does not change. The coin tape is a sequence of independent fair bits. Complex numbers are pairs of reals, so unit-cost complex arithmetic costs $O(1)$ steps. The primitive $2^a$-th root of unity is supplied as input data $(\cos(2\pi/2^a),\sin(2\pi/2^a))$.
--
--   There is no floor, no real-to-integer cast, no coordinate representative or order test on coordinates, no exponential, logarithm or trigonometric function, no pointer multiplication, and no unit-cost uniform element of $G$. With these exclusions an operation count is meaningful, and the query log makes nonadaptivity a property of the program.
--
--   **Formalization Note** The real core is the published `SmaleNinth.RAMInstr` pointer machine. Admissible programs use rational literals and no core accept/reject; this restricts the chosen program, never the input. Outputs are read from fixed memory cells of a halted state: up to two lists of (frequency, value) pairs, decoded to vectors on $G$ (entries with equal frequencies add), a scalar, and an abort flag.
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), §2.3 Computational model, pp.18–19 (PDF pp.20–21); nonadaptive query model, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_NonadaptiveSFT_Fourier

namespace NonadaptiveSFT

/-!
# The exact arithmetic model of §2.3: a real RAM with a `ℤ/2^aℤ` coordinate bank, fair coins and
a point-query oracle with a query log

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…), §2.3 "Computational model", pp.18–19 (PDF pp.20–21), and
the definition of the nonadaptive query model, p.2.

"The input X is fixed before the algorithm draws its randomness, and the algorithm accesses X only
through point queries. … We work in the exact arithmetic model. Arithmetic on individual coordinates
in Z/2^aZ, exact complex arithmetic, exact real comparisons, and square roots of nonnegative reals
have unit cost. A group element is represented by its d coordinates. … Each independent fair random
bit also has unit cost. … A primitive 2^a-th root of unity is supplied."

**Formalization Note.**
* The scalar core is the published `SmaleNinth.RAMInstr` real pointer machine. Its extensions:
  integer pointer `+`/`−`, an integer memory, a pointer-to-real cast, `sqrt` (`Real.sqrt`), `coin`,
  the **coordinate bank** (registers and a memory over `ZMod (2^a)` with the literals `0`, `1`, ring
  operations `+ − ×`, load and store through a pointer, and a jump on equality), `query`, and `halt`.
* Complex numbers are pairs of real registers. Each exact complex operation (`+ − × ÷`, conjugate,
  real and imaginary part) is `O(1)` real operations, so the paper's unit-cost complex arithmetic
  is the same model up to constants. Comparisons are on reals, as in the paper.
* The supplied root of unity is input data: the input layouts put `cos(2π/2^a)` and `sin(2π/2^a)`
  in real memory. It is not a literal.
* Not in the language: floor, real-to-integer cast, the representative `val` of a coordinate, an
  integer-to-coordinate cast, an order test on coordinates, `exp`/`log`/trigonometric functions,
  pointer multiplication, irrational literals, a unit-cost uniform element of `G`. No constructor
  carries a function. `Admissible` programs use rational literals only and no core
  `accept`/`reject`; this restricts the existentially chosen program, never the input.
* `query dRe dIm q` reads the `d` coordinates at coordinate-memory addresses
  `p[q], p[q]+1, …, p[q]+d−1` as a point `t ∈ G`, writes `Re X(t)` and `Im X(t)` into the real
  registers `dRe`, `dIm`, appends `t` to the **query log**, and adds one to the query counter. The
  signal `X` occurs only in this branch of `step`, the coin tape only in the `coin` branch.
* Every executed instruction costs one unit of `work`, including `query`, `coin`, jumps and `halt`.
  An invalid program counter is stuck and charged, so only `halt` halts; after `halt` the state
  stutters at no cost. Each step writes at most one memory cell, so the number of memory cells a
  run writes is at most its `work`.
* Randomness is a tape of independent fair coins, one bit per executed `coin`; `coinTape` is the
  product of uniform laws on `Bool`.
* Output layout (read only from a halted state). Up to two lists of (frequency, value) pairs:
  integer cell `−1 − ℓ` holds the length of list `ℓ ∈ {0, 1}`; entry `i` of list `ℓ` is block
  `q = 2i + ℓ`, with frequency coordinate `j < d` at coordinate cell `−q·d − 1 − j`, real part at
  real cell `−2q − 2` and imaginary part at real cell `−2q − 3`. Real cell `−1` holds a scalar
  output and integer cell `−3` an abort flag (nonzero means "aborted"). Blocks never collide. The
  decoded vector of list `ℓ` is `f ↦ Σ_{i : freq_i = f} (Re_i + i·Im_i)`, so duplicate entries add.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers.
* `core i`: a `SmaleNinth` real-RAM instruction (real `+ − × ÷` with `x/0 = 0`, literals, indirect
  real load and store, pointer set/copy/increment/decrement, jumps `r ≤ 0` and `p ≤ p'`).
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]`.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]`.
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `sqrt d a`: `r[d] := √(r[a])`.
* `coin d`: `r[d] := 1` if the next tape bit is `true`, else `0`; the cursor advances.
* `coordZero d`, `coordOne d`: `c[d] := 0`, `c[d] := 1` in `ZMod (2^a)`.
* `coordAdd d a b`, `coordSub d a b`, `coordMul d a b`: `c[d] := c[a] ± c[b]`, `c[a]·c[b]`.
* `coordLoad d q`, `coordStore q a`: `c[d] := CM[p[q]]`, `CM[p[q]] := c[a]`.
* `coordJeq a b target`: jump to `target` if `c[a] = c[b]`, else fall through.
* `query dRe dIm q`: point query at the group element stored at `CM[p[q]], …, CM[p[q]+d−1]`.
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | sqrt (dst src : ℕ)
  | coin (dst : ℕ)
  | coordZero (dst : ℕ)
  | coordOne (dst : ℕ)
  | coordAdd (dst a b : ℕ)
  | coordSub (dst a b : ℕ)
  | coordMul (dst a b : ℕ)
  | coordLoad (dst pointer : ℕ)
  | coordStore (pointer src : ℕ)
  | coordJeq (a b target : ℕ)
  | query (dstRe dstIm pointer : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every `a`, `d` and input. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core halting instructions `accept`/`reject` do not
occur (the machine stops only through `halt`). -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P`: extension instructions are placeholders here and are always
dispatched by `step`. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state for the group `G a d`: the core configuration (program counter, real registers,
pointers, real memory), integer memory, coordinate registers and memory, the coin-tape cursor, the
halted flag, the query counter, the query log and the work counter. -/
structure State (a d : ℕ) where
  core : SmaleNinth.RAMConfig
  ints : ℤ → ℤ
  cregs : ℕ → ZMod (2 ^ a)
  cmem : ℤ → ZMod (2 ^ a)
  cursor : ℕ
  halted : Bool
  queries : ℕ
  queryLog : List (G a d)
  work : ℕ

/-- The group element stored at coordinate cells `base, base+1, …, base+d−1`. -/
def readPoint {a d : ℕ} (cmem : ℤ → ZMod (2 ^ a)) (base : ℤ) : G a d :=
  fun i => cmem (base + (i : ℕ))

/-- One step of program `P` with point-query oracle `X` and coin tape `ω`. Halted states stutter at
no cost; every other step costs one unit of work. -/
noncomputable def step {a d : ℕ} (P : Program) (X : G a d → ℂ) (ω : ℕ → Bool) (s : State a d) :
    State a d :=
  if s.halted then s else
    let t : State a d := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerAdd dst x y) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs dst (s.core.ptrs x + s.core.ptrs y) } }
    | some (.pointerSub dst x y) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs dst (s.core.ptrs x - s.core.ptrs y) } }
    | some (.integerLoad dst x) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs dst (s.ints (s.core.ptrs x)) } }
    | some (.integerStore x y) =>
        { t with ints := Function.update s.ints (s.core.ptrs x) (s.core.ptrs y) }
    | some (.pointerReal dst x) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs dst (s.core.ptrs x : ℝ) } }
    | some (.sqrt dst x) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs dst (Real.sqrt (s.core.regs x)) } }
    | some (.coin dst) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with
            regs := Function.update s.core.regs dst (if ω s.cursor then 1 else 0) } }
    | some (.coordZero dst) => { t with cregs := Function.update s.cregs dst 0 }
    | some (.coordOne dst) => { t with cregs := Function.update s.cregs dst 1 }
    | some (.coordAdd dst x y) =>
        { t with cregs := Function.update s.cregs dst (s.cregs x + s.cregs y) }
    | some (.coordSub dst x y) =>
        { t with cregs := Function.update s.cregs dst (s.cregs x - s.cregs y) }
    | some (.coordMul dst x y) =>
        { t with cregs := Function.update s.cregs dst (s.cregs x * s.cregs y) }
    | some (.coordLoad dst q) =>
        { t with cregs := Function.update s.cregs dst (s.cmem (s.core.ptrs q)) }
    | some (.coordStore q x) =>
        { t with cmem := Function.update s.cmem (s.core.ptrs q) (s.cregs x) }
    | some (.coordJeq x y target) =>
        if s.cregs x = s.cregs y then
          { t with core := { t.core with pc := target } }
        else t
    | some (.query dRe dIm q) =>
        let pt : G a d := readPoint s.cmem (s.core.ptrs q)
        { t with
          queries := s.queries + 1
          queryLog := s.queryLog ++ [pt]
          core := { t.core with
            regs := Function.update (Function.update s.core.regs dRe (X pt).re) dIm (X pt).im } }
    | some .halt => { t with halted := true }

/-- The state after `n` steps of `P` from `s₀`, with oracle `X` and coin tape `ω`. -/
noncomputable def run {a d : ℕ} (P : Program) (X : G a d → ℂ) (s₀ : State a d) (ω : ℕ → Bool)
    (n : ℕ) : State a d :=
  (step P X ω)^[n] s₀

/-- The start state: program counter, registers, pointers, cursor and counters `0`, empty query log;
integer memory holds the list `ints` from cell `0`, real memory the list `reals` from cell `0`,
coordinate memory the list `coords` from cell `0`; every other cell is `0`. -/
noncomputable def initState (a d : ℕ) (ints : List ℤ) (reals : List ℝ)
    (coords : List (ZMod (2 ^ a))) : State a d :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0,
    fun _ => 0,
    fun z => if 0 ≤ z then coords.getD z.toNat 0 else 0,
    0, false, 0, [], 0⟩

/-- The fair-coin tape: the product of uniform laws on `Bool` over `ℕ`. -/
noncomputable def coinTape : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

/-- The supplied primitive `2^a`-th root of unity, as the two reals `cos(2π/2^a)`, `sin(2π/2^a)`. -/
noncomputable def rootReals (a : ℕ) : List ℝ :=
  [Real.cos (2 * Real.pi / 2 ^ a), Real.sin (2 * Real.pi / 2 ^ a)]

/-- The length of output list `ℓ` (integer cell `−1 − ℓ`; a negative entry counts as `0`). -/
def outLength {a d : ℕ} (s : State a d) (ℓ : ℕ) : ℕ := (s.ints (-1 - (ℓ : ℤ))).toNat

/-- The frequency of entry `i` of output list `ℓ` (block `q = 2i + ℓ`). -/
def outFreq {a d : ℕ} (s : State a d) (ℓ i : ℕ) : G a d :=
  fun j => s.cmem (-((2 * i + ℓ : ℕ) : ℤ) * d - 1 - (j : ℕ))

/-- The value of entry `i` of output list `ℓ`. -/
def outValue {a d : ℕ} (s : State a d) (ℓ i : ℕ) : ℂ :=
  ⟨s.core.mem (-2 * ((2 * i + ℓ : ℕ) : ℤ) - 2), s.core.mem (-2 * ((2 * i + ℓ : ℕ) : ℤ) - 3)⟩

/-- The decoded vector of output list `ℓ`: `f ↦ Σ_{i : freq_i = f} value_i`. -/
noncomputable def outVec {a d : ℕ} (s : State a d) (ℓ : ℕ) : G a d → ℂ := by
  classical exact fun f =>
    ∑ i ∈ Finset.range (outLength s ℓ), if outFreq s ℓ i = f then outValue s ℓ i else 0

/-- The set of frequencies listed in output list `ℓ`. -/
noncomputable def outFreqs {a d : ℕ} (s : State a d) (ℓ : ℕ) : Finset (G a d) := by
  classical exact (Finset.range (outLength s ℓ)).image (outFreq s ℓ)

/-- The scalar output (real cell `−1`). -/
def outScalar {a d : ℕ} (s : State a d) : ℝ := s.core.mem (-1)

/-- The abort flag (integer cell `−3`, nonzero = aborted). -/
def aborted {a d : ℕ} (s : State a d) : Prop := s.ints (-3) ≠ 0

/-- Input of the main theorem: integer memory `a, d, k`; real memory `ε, B, c, cos(2π/2^a),
sin(2π/2^a)`; coordinate memory zero. -/
noncomputable def goalInit (a d k : ℕ) (ε B c : ℝ) : State a d :=
  initState a d [(a : ℤ), (d : ℤ), (k : ℤ)] ([ε, B, c] ++ rootReals a) []

/-- Input of Theorem 15: integer memory `a, d, s`; real memory `τ, cos(2π/2^a), sin(2π/2^a)`. -/
noncomputable def recoveryInit (a d s : ℕ) (τ : ℝ) : State a d :=
  initState a d [(a : ℤ), (d : ℤ), (s : ℤ)] ([τ] ++ rootReals a) []

/-- Input of the locator (Proposition 13): integer memory `a, d`; real memory `M, T, γ,
cos(2π/2^a), sin(2π/2^a)`. -/
noncomputable def locatorInit (a d : ℕ) (M T γ : ℝ) : State a d :=
  initState a d [(a : ℤ), (d : ℤ)] ([M, T, γ] ++ rootReals a) []

/-- The coordinates of a list of group elements, element after element. -/
def coordsOf {a d : ℕ} (l : List (G a d)) : List (ZMod (2 ^ a)) :=
  l.flatMap fun t => List.ofFn t

/-- Input of the least-squares routine (Lemma 14): integer memory `a, d, n, m`; coordinate memory
the samples `t_1, …, t_n` and then the `m` listed elements of `S`, `d` coordinates each; real
memory `σ̄, cos(2π/2^a), sin(2π/2^a)` and then `Re y_1, Im y_1, …, Re y_n, Im y_n`, where
`y_b = X(t_b)` are the sample outcomes. -/
noncomputable def lsInit {a d n : ℕ} (t : Fin n → G a d) (y : Fin n → ℂ) (S : List (G a d))
    (σbar : ℝ) : State a d :=
  initState a d [(a : ℤ), (d : ℤ), (n : ℤ), (S.length : ℤ)]
    ([σbar] ++ rootReals a ++ (List.ofFn y).flatMap fun z => [z.re, z.im])
    (coordsOf (List.ofFn t ++ S))

end NonadaptiveSFT


