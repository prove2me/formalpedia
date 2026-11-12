-- Prove2me | Definitions.Def_RelatedSchedFPTAS796_Main_Machine
-- name    : RelatedSchedFPTAS796_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:27.78491+00:00
-- url     : https://prove2.me/theorems/e3cc0a81-63c8-4498-84e8-7a4074fcfecb
-- title:
--   Running programs of the randomized word RAM: encodings, word width, time, failure probability
-- statement:
--   The paper works in "the standard word RAM model of computation" (p.7 line 272) without naming an instruction set. Every algorithmic statement of the mission is stated for the published randomized word RAM `MatroidSensOracle`: words of $w$ bits; instructions load a constant one, add, subtract and multiply modulo $2^w$, unsigned division and remainder, indirect load and store, a branch on a negative word, a coin drawing a uniform number below the value of a word, and halt; every executed instruction costs one step.
--
--   1. **Input.** A run starts with the input words in cells $0,1,2,\dots$ and $0$ elsewhere. A rational $x$ is the two words $x.\mathrm{num},x.\mathrm{den}$ (lowest terms); a natural number is one word.
--   2. **Word width.** A program must work at every width $w\ge b\,(\lfloor\log_2(n+M+2)\rfloor+1)$, where $M$ is the largest absolute value of an input word, $n$ is the size parameter of the problem, and $b$ is fixed together with the program. Every input number fits in $O(1)$ words and $\log n$ bits fit in a word; the width does not grow with $n$.
--   3. **Time.** Halting within $T$ steps ($T$ real) means halting within $\lfloor T\rfloor$ executed instructions. Time bounds are worst case over all coin sequences; the failure probability of a run is the probability, under the uniform law of the coins, that it does not halt within $T$ steps with an acceptable final memory. The halting time of a run is the least number of steps after which it has halted.
--   4. **Output sets.** A finite set of vectors of $\mathbb Q^k_{\ge0}$ is written as a count $K$ in cell $0$ followed by the $K$ vectors, each coordinate as numerator and denominator (read unsigned); a set of vectors of $\mathbb N^k$ as a count followed by the coordinates.
--   5. **Soft-O.** $\tilde O(X)$ is $C\cdot X\cdot(\log_2(n+2)\log_2(2/\varepsilon)\log_2(2/q))^c$, and without a failure parameter $C\cdot X\cdot(\log_2(n+2)\log_2(2/\varepsilon))^c$ (p.7 lines 270–271). In §§3–5 the accuracy is $\varepsilon=2^{-\ell}$.
--
--   This fixes the meaning of every running-time statement in the mission, including the goal.
--
--   **Formalization Note** The machine is reused verbatim from `MatroidSensOracle_WordRAM` (its oracle layer is not used). The width threshold is part of this mission, not of the reused machine. "Halts within $T$" is `exec` with fuel `⌊T⌋₊`.
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, §2.1 p.7 lines 268–272; Theorem 1.1 p.3 lines 86–87

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main

/-!
# Running programs of the randomized word RAM: encodings, word width, time and failure

Chen, Hu, Lian, Mao, Zhang, *Faster Approximation Schemes for Scheduling on Related Machines*,
STOC 2027 submission #796 (October 2026), §2.1 p.7 lines 270–272: "All logarithms (log) in this
paper are base 2. The notation Õ(·) suppresses polynomial factors in log(|J| + 2), log(2/ε) and
log(2/q), where q is the failure parameter. We use the standard word RAM model of computation
throughout the paper."

**Formalization Note.**
* **Machine.** The published randomized word RAM `MatroidSensOracle` (instructions `one`, `add`,
  `sub`, `mul` modulo `2^w`, unsigned `udiv`/`umod`, indirect `load`/`store`, `bltz`, a uniform coin
  below a word, `halt`; one step per executed instruction; `coinLaw` the law of the coins). Only
  `Instr`, `exec`, `Coins`, `coinLaw` and `loadWords` are used, not its oracle layer.
* **Input.** A run starts on `loadWords w ws`: the input words `ws` in cells `0, 1, 2, …`, every
  other cell `0`. A rational `x` is the two words `x.num, x.den` (lowest terms, `den > 0`); a natural
  number or a vector of naturals is one word per number.
* **Word width.** A program is required to work at every width `w ≥ b·(⌊log₂(n + M + 2)⌋ + 1)`,
  `M` the largest absolute value of an input word, `n` the size parameter of the problem, and `b`
  chosen together with the program (before the input). Every input number fits in `O(1)` words and
  `log n` bits fit in a word; the width does not grow with `n` itself.
* **Time.** "Halts within `T` steps" (`T` real) means `exec` with fuel `⌊T⌋₊` halts; the bound is
  required on every coin sequence (worst case). A failure probability is the `coinLaw`-measure of the
  set of coin sequences on which the run does *not* halt within `T` with an acceptable final memory.
* **Output sets.** A finite set of vectors of `ℚ^k_{≥0}` is written as: cell `0` holds a count `K`,
  and for `r < K` and `i < k` the cells `1 + 2(rk + i)` and `2 + 2(rk + i)` hold numerator and
  denominator of coordinate `i` of the `r`-th vector (read unsigned). A set of vectors of `ℕ^k` is
  written as: cell `0` holds `K`, cell `1 + rk + i` holds coordinate `i` of the `r`-th vector.
-/

open MatroidSensOracle MeasureTheory

/-- The two input words `x.num, x.den` of a rational. -/
def ratWords (x : ℚ) : List ℤ := [x.num, (x.den : ℤ)]

/-- The words of a vector of naturals, one per coordinate. -/
def natVecWords {k : ℕ} (x : Fin k → ℕ) : List ℤ := (List.finRange k).map fun i => (x i : ℤ)

/-- The words of a vector of rationals, `num, den` per coordinate. -/
def ratVecWords {k : ℕ} (x : Fin k → ℚ) : List ℤ := (List.finRange k).flatMap fun i => ratWords (x i)

/-- `M`, the largest absolute value of an input word (`0` for no words). -/
def maxWord (ws : List ℤ) : ℕ := (ws.map Int.natAbs).foldr max 0

/-- The word-width threshold `b·(⌊log₂(n + M + 2)⌋ + 1)`. -/
def widthMin (b n M : ℕ) : ℕ := b * (Nat.log2 (n + M + 2) + 1)

/-- The run of `P` at width `w` on the input words `ws` with coins `ω`, if it halts within `T`
steps: the final memory. -/
noncomputable def runFor (P : List Instr) (w : ℕ) (ws : List ℤ) (T : ℝ) (ω : Coins) :
    Option (ℤ → BitVec w) :=
  exec P ω ⌊T⌋₊ 0 0 (loadWords w ws)

/-- Worst-case time: on every coin sequence the run halts within `T` steps. -/
def HaltsWithin (P : List Instr) (w : ℕ) (ws : List ℤ) (T : ℝ) : Prop :=
  ∀ ω : Coins, (runFor P w ws T ω).isSome

/-- Failure probability at most `q`: the probability that the run does not halt within `T` steps
with a final memory satisfying `ok` is at most `q`. -/
def FailsAtMost (P : List Instr) (w : ℕ) (ws : List ℤ) (T : ℝ) (ok : (ℤ → BitVec w) → Prop)
    (q : ℝ) : Prop :=
  coinLaw {ω : Coins | ¬ ∃ mem, runFor P w ws T ω = some mem ∧ ok mem} ≤ ENNReal.ofReal q

/-- The halting time of a run (the least fuel with which it halts; `⊤` if it never halts). -/
noncomputable def haltTime (P : List Instr) (w : ℕ) (ws : List ℤ) (ω : Coins) : ℕ∞ :=
  ⨅ t : ℕ, if (exec P ω t 0 0 (loadWords w ws)).isSome then (t : ℕ∞) else ⊤

/-- A program without coin instructions (a deterministic program). -/
def CoinFree (P : List Instr) : Prop := ∀ i j : ℤ, Instr.coin i j ∉ P

/-- The count `K` in cell `0` of an output. -/
def outCount {w : ℕ} (mem : ℤ → BitVec w) : ℕ := (mem 0).toNat

/-- The `r`-th output vector of `ℚ^k_{≥0}`, coordinate `i` read as `num / den` from the cells
`1 + 2(rk + i)` and `2 + 2(rk + i)`. -/
noncomputable def outRatVec {w : ℕ} (k : ℕ) (mem : ℤ → BitVec w) (r : ℕ) : Fin k → ℝ :=
  fun i => ((mem (1 + 2 * ((r * k + i : ℕ) : ℤ))).toNat : ℝ) /
    ((mem (2 + 2 * ((r * k + i : ℕ) : ℤ))).toNat : ℝ)

/-- The output set of vectors of `ℚ^k_{≥0}`. -/
noncomputable def outRatSet {w : ℕ} (k : ℕ) (mem : ℤ → BitVec w) : Set (Fin k → ℝ) :=
  {x | ∃ r < outCount mem, x = outRatVec k mem r}

/-- The `r`-th output vector of `ℕ^k`, coordinate `i` in cell `1 + rk + i`. -/
def outNatVec {w : ℕ} (k : ℕ) (mem : ℤ → BitVec w) (r : ℕ) : Fin k → ℕ :=
  fun i => (mem (1 + ((r * k + i : ℕ) : ℤ))).toNat

/-- The output is exactly the finite set `S ⊆ ℕ^k`, listed without repetition. -/
def OutputsNatSet {w k : ℕ} (mem : ℤ → BitVec w) (S : Finset (Fin k → ℕ)) : Prop :=
  outCount mem = S.card ∧ {x | ∃ r < outCount mem, x = outNatVec k mem r} = (S : Set (Fin k → ℕ))

/-- The accuracy `ε = 2^{-ℓ}` of §§3–5 (where `1/ε` is a power of two, p.7). -/
noncomputable def epsOf (ℓ : ℕ) : ℝ := ((2 : ℝ) ^ ℓ)⁻¹

/-- The polylogarithmic factor `(log₂(n + 2)·log₂(2/ε)·log₂(2/q))^c` behind `Õ`. -/
noncomputable def polylog3 (n : ℕ) (ε q : ℝ) (c : ℕ) : ℝ :=
  (Real.logb 2 ((n : ℝ) + 2) * Real.logb 2 (2 / ε) * Real.logb 2 (2 / q)) ^ c

/-- The polylogarithmic factor `(log₂(n + 2)·log₂(2/ε))^c` for statements without a failure
parameter. -/
noncomputable def polylog2 (n : ℕ) (ε : ℝ) (c : ℕ) : ℝ :=
  (Real.logb 2 ((n : ℝ) + 2) * Real.logb 2 (2 / ε)) ^ c

end RelatedSchedFPTAS796.Main


