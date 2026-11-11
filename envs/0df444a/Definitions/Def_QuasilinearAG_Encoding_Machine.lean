-- Prove2me | Definitions.Def_QuasilinearAG_Encoding_Machine
-- name    : QuasilinearAG_Encoding_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:41:10.386591+00:00
-- url     : https://prove2.me/theorems/df7ed651-2a45-44d4-9c68-922b60e03f8f
-- title:
--   The packed bit model on the log-cost RAM: runs, work, live bits, input and output layouts, field records and $\sigma(\varepsilon)$
-- statement:
--   Computations are runs of the published logarithmic-cost RAM `TimeSpaceMA_RAM` without coins: a program is a finite list of instructions (constant, addition, truncated subtraction, indirect load and store, conditional jump, halt) over memory cells holding natural numbers, and each executed instruction costs $1$ plus the bit lengths of every address used and every value read or written. This is the paper's packed random-access model: "We charge each read or write for the bit lengths of both the record and the address used for that access", and integer arithmetic beyond addition, subtraction and comparison must be programmed.
--
--   - **Work.** A coin-free program $p$ *computes* an output on an input list within work $W$ if, started on the memory holding the input from cell $0$ on, it halts, its output list satisfies the required property, and the accumulated cost is at most $W$. The output list is read from the final memory: cell $0$ holds its length $\ell$ and cells $1,\dots,\ell$ its entries.
--   - **Live bits.** A state holds at most $B$ live bits if every nonzero memory cell has address $<B$ and the bit lengths of all cells sum to at most $B$. A program runs *in space* $S$ if every state reached along the run (the initial one included) holds at most $S$ live bits. Inputs, outputs, buffers and recursion state are all memory cells, so all of them are counted, as in "Complete storage includes initialization, descriptions, inputs, outputs, buffers and suspended recursion state".
--   - **Field records.** With $q=2^\sigma$, the alphabet $\mathbb F_{q^2}$ is represented as $\mathbb F_2[X]/(f)$ for a polynomial $f$ of degree $2\sigma$; the integer $n<2^{2\sigma}$ stands for the element $\sum_{i<2\sigma}\mathrm{bit}_i(n)\,X^i$, its coefficient vector in the polynomial basis.
--   - **Layouts.** Every algorithm receives the binary integers $N,K,\sigma$ in cells $0,1,2$, followed by one record per field element of its vector input (or the two indices $i,j$ for the generator entry). A vector output is the list of its records, in order.
--   - $\sigma(\varepsilon)$ is the least $\sigma$ with $2^\sigma\ge 5/\varepsilon$, so $q=2^{\sigma(\varepsilon)}$ is the least power of two with $q\ge5/\varepsilon$.
--
--   **Formalization Note** The space measure also charges the extent of the occupied address range, so data cannot be hidden in the choice of far-away addresses; this matches a packed memory. Real $\varepsilon$ never enters a computation: it only determines $\sigma$ ("Real-valued gaps ... are analysis parameters").
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 7 "Computational model" (PDF 9), p. 27 §5.8 (PDF 29), §A3 p. 50 (PDF 52)

import Mathlib
import Definitions.Def_TimeSpaceMA_RAM

namespace QuasilinearAG.Encoding

/-!
# The packed bit model: runs, work, live bits, input and output layouts, field records

Chao, Liu, Li, Ma, Wang, *Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier
Bases*, STOC 2027 submission (manuscript sha256 355c15dc…), p. 7 "Computational model" (PDF 9),
p. 27 §5.8 (PDF 29) and §A3 p. 50 (PDF 52).

The machine is the published logarithmic-cost RAM `TimeSpaceMA_RAM`, run without coins: each
executed instruction costs `1` plus the bit lengths (`Nat.size`) of every address used and every
value read or written ("We charge each read or write for the bit lengths of both the record and
the address used for that access"). Integer arithmetic beyond addition, truncated subtraction and
comparison has to be programmed ("explicit bit algorithms").

* `runState p mem T` is the state after `T` steps from memory `mem` (all-`false` coin tape).
* `LiveBitsWithin st B`: the stored data of the state occupy at most `B` live bits: every nonzero
  cell has address `< B` (memory is a contiguous array, so data cannot be hidden in the choice of
  far-away addresses), and the total bit length of all cells is at most `B`. Inputs, outputs,
  buffers and recursion state are all memory cells, so all of them count ("Complete storage
  includes initialization, descriptions, inputs, outputs, buffers and suspended recursion state").
* `outputList mem`: cell `0` holds the output length `ℓ`, cells `1, …, ℓ` the output records.
* `Computes p input good W` / `ComputesInSpace p input good W S`: the coin-free program halts on
  the memory holding `input` from cell `0` on, its output list satisfies `good`, the accumulated
  work is at most `W`, and (second form) every state reached along the run has at most `S` live
  bits.
* Field records: `F_{q²}` with `q = 2^σ` is `AdjoinRoot f` for a polynomial `f` over `F₂` of degree
  `2σ`; the integer `n < 2^{2σ}` stands for the element `Σ_{i < 2σ} bit_i(n) X^i` (`decodeField`),
  i.e. its coefficient vector in the polynomial basis.
* `FieldVecOut f σ v out`: `out` is the list of the records of the vector `v`, each `< 2^{2σ}`.
* `sigmaOf ε`: the least `σ` with `2^σ ≥ 5/ε` (so `q = 2^σ` is the least power of two `≥ 5/ε`).
-/

open TimeSpaceMA

/-- The state after `T` steps of the coin-free run of `p` from memory `mem`. -/
def runState (p : Program) (mem : ℕ → ℕ) (T : ℕ) : State :=
  (p.step zeroTape)^[T] (State.init mem)

/-- The memory of `st` holds at most `B` live bits: every nonzero cell has address below `B`, and
the bit lengths of all cells sum to at most `B`. -/
def LiveBitsWithin (st : State) (B : ℝ) : Prop :=
  (∀ i, st.mem i ≠ 0 → (i : ℝ) < B) ∧
    ∀ S : Finset ℕ, ((∑ i ∈ S, (st.mem i).size : ℕ) : ℝ) ≤ B

/-- The output list of a final memory: cell `0` holds its length `ℓ`, cells `1, …, ℓ` its
entries. -/
def outputList (mem : ℕ → ℕ) : List ℕ :=
  (List.range (mem 0)).map (fun i => mem (i + 1))

/-- The coin-free program `p`, started on the memory holding `input` from cell `0` on, halts with an
output list satisfying `good`, with accumulated work at most `W`. -/
def Computes (p : Program) (input : List ℕ) (good : List ℕ → Prop) (W : ℝ) : Prop :=
  ∃ st : State, p.RunsTo zeroTape (memOf input) st ∧ good (outputList st.mem) ∧ (st.work : ℝ) ≤ W

/-- As `Computes`, and moreover every state reached along the run (from the initial memory on)
holds at most `S` live bits. -/
def ComputesInSpace (p : Program) (input : List ℕ) (good : List ℕ → Prop) (W S : ℝ) : Prop :=
  Computes p input good W ∧ ∀ T : ℕ, LiveBitsWithin (runState p (memOf input) T) S

/-- The field element of `AdjoinRoot f` whose coefficient vector in the polynomial basis
`1, X, …, X^{deg f - 1}` is the binary expansion of `n` (bit `i` of `n` is the coefficient of
`X^i`). -/
noncomputable def decodeField (f : Polynomial (ZMod 2)) (n : ℕ) : AdjoinRoot f :=
  AdjoinRoot.mk f (∑ i ∈ Finset.range f.natDegree, if n.testBit i then Polynomial.X ^ i else 0)

/-- `out` lists the records of the vector `v` over `AdjoinRoot f`, `f` of degree `2σ`: one record
`< 2^{2σ}` per coordinate, in order. -/
def FieldVecOut {n : ℕ} (f : Polynomial (ZMod 2)) (σ : ℕ) (v : Fin n → AdjoinRoot f)
    (out : List ℕ) : Prop :=
  ∃ o : Fin n → ℕ, out = List.ofFn o ∧ ∀ i, o i < 2 ^ (2 * σ) ∧ decodeField f (o i) = v i

/-- The input layout: the binary integers `N, K, σ` in cells `0, 1, 2`, followed by the records
`r 0, r 1, …` (one cell per field element). -/
def inputLayout {n : ℕ} (N K σ : ℕ) (r : Fin n → ℕ) : List ℕ :=
  [N, K, σ] ++ List.ofFn r

/-- The least `σ` with `2^σ ≥ 5/ε`: `q = 2^σ` is the least power of two with `q ≥ 5/ε`. -/
noncomputable def sigmaOf (ε : ℝ) : ℕ :=
  Nat.clog 2 ⌈5 / ε⌉₊

end QuasilinearAG.Encoding


