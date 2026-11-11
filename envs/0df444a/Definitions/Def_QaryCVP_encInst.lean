-- Prove2me | Definitions.Def_QaryCVP_encInst
-- name    : QaryCVP_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:59:04.198209+00:00
-- url     : https://prove2.me/theorems/b3512a33-ba22-4075-a793-aa3a6c17b8a5
-- title:
--   Input words, input length, runs within a budget, and the simultaneous $\gamma$-CVP success event
-- statement:
--   Algorithms run on the published randomized log-cost rational RAM `TwMSOCount.Main`, whose cells hold exact rationals and which reads a tape of independent fair bits. Time is bit time and space is bit space.
--
--   1. The **input word** of a CVP instance $(H,y)$ is $n,m,q$, then the $mn$ entries of $H$ row by row as representatives in $[0,q)$, then $y_1,\dots,y_n$, one stored rational each. A short-solution instance $(A,t)$ is encoded the same way, with $t$ in place of $y$; an exact-search instance $(H,y,b)$ appends $b$.
--   2. The **binary input length** $\ell$ of a word is the total bit length of its entries; polynomial factors are $(\ell+1)^K$.
--   3. A program **runs within** $(T,S)$ on a word if on **every** coin tape it halts with bit time at most $T$ and bit space at most $S$. It is **deterministic** on a word if its run is the same on every tape.
--   4. The output word of an integer vector is its $n$ entries; $\bot$ is the empty word.
--   5. For a matrix $H$, the **simultaneous success event** of a program $P$ for $\gamma$-CVP is the set of coin tapes $\tau$ such that for every target $y\in\mathbb Q^n$ the run of $P$ on $(H,y)$ with tape $\tau$ outputs some $x$ solving $\gamma$-CVP for $(H,y)$. $H$ is **good** with error $\varepsilon$ if this event is measurable and has probability at least $1-\varepsilon$.
--
--   One tape serves all targets, which is how "simultaneously for every $y\in\mathbb Q^n$" (Theorem 1.1) is expressed.
--
--   **Formalization Note** The paper fixes a cost model ("Integers and rationals are encoded in binary, and arithmetic on them is exact. Time is measured in bit operations and space in bits", p.13) but names no machine; this machine charges arithmetic on $\ell_1$- and $\ell_2$-bit operands $(\ell_1+\ell_2+1)^2$ and counts the address and content bits of every written cell. Its `encodeInput` and `codeGraph` belong to another paper and are not used.
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), §2.1 (cost model), p.13; §2.3, p.14; Theorem 1.1, p.2; Algorithm 1, p.18; Algorithm 3, p.33

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice

open MeasureTheory TwMSOCount.Main
open scoped ENNReal

namespace QaryCVP

/-- The entries of `H ∈ (Z/qZ)^{m×n}`, row by row, each as its canonical representative
`(H i j).val ∈ [0, q)` (R9). -/
def encMat {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) : List ℚ :=
  (List.finRange m).flatMap fun i => (List.finRange n).map fun j => ((H i j).val : ℚ)

/-- A vector of `(Z/qZ)^m`, entrywise canonical representatives. -/
def encModVec {m q : ℕ} (t : Fin m → ZMod q) : List ℚ :=
  (List.finRange m).map fun i => ((t i).val : ℚ)

/-- A rational vector, one stored rational per entry. -/
def encQVec {n : ℕ} (y : Fin n → ℚ) : List ℚ := (List.finRange n).map y

/-- The output word of an integer vector: its `n` entries. -/
def encZVec {n : ℕ} (x : Fin n → ℤ) : List ℚ := (List.finRange n).map fun i => (x i : ℚ)

/-- The input word of a CVP instance `(H, y)` (R9): `n, m, q`, then the `mn` entries of `H` row
by row as canonical representatives in `[0, q)`, then `y₁, …, yₙ`. Integers and rationals are
encoded in binary (p.13): each entry is one stored rational of the machine, of bit length
`qbits`.
Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), §2.1, p.13;
Algorithm 3, p.33. -/
def encInst {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ) : List ℚ :=
  [(n : ℚ), (m : ℚ), (q : ℚ)] ++ encMat H ++ encQVec y

/-- The input word of an exact-search instance `(H, y, b)` (Definition 3.4, p.24): the CVP word
followed by the squared radius `b`. -/
def encSearch {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ) (b : ℚ) :
    List ℚ :=
  encInst H y ++ [b]

/-- The input word of a short-solution instance `(A, t)` (Definition 3.1, p.14; Algorithm 1,
p.18): `n, m, q`, the entries of `A` row by row, then the entries of `t`, all as canonical
representatives. The sign count `a₀` is computed by the procedure from its parameters and `n`
(Algorithm 1, line 1), so it is not part of the input. -/
def encShort {m n q : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q)) (t : Fin m → ZMod q) :
    List ℚ :=
  [(n : ℚ), (m : ℚ), (q : ℚ)] ++ encMat A ++ encModVec t

/-- The binary input length `ℓ` of an input word: the total bit length of its stored rationals
(p.13: "poly denotes a polynomial factor in the binary input length"). -/
def bitLen (w : List ℚ) : ℕ := (w.map qbits).sum

/-- The polynomial factor `(ℓ + 1)^K` in the binary input length `ℓ` of `w` (R2). -/
noncomputable def polyF (K : ℕ) (w : List ℚ) : ℝ := ((bitLen w : ℝ) + 1) ^ K

/-- On input word `w`, the program `P` halts on **every** coin tape, with bit time at most `T` and
bit space at most `S` (R10: "on every input and execution"). The machine is the published
randomized log-cost rational RAM `TwMSOCount.Main` (R1). -/
def RunsWithin (P : Program) (w : List ℚ) (T S : ℝ) : Prop :=
  ∀ τ : ℕ → Bool, ∃ s : RunStats, runStats P τ (Config.init w) = some s ∧
    (s.time : ℝ) ≤ T ∧ (s.space : ℝ) ≤ S

/-- `P` is deterministic on input `w`: its run is the same on every coin tape. -/
def DetOn (P : Program) (w : List ℚ) : Prop :=
  ∀ τ : ℕ → Bool, runStats P τ (Config.init w) = runStats P zeroTape (Config.init w)

/-- The simultaneous γ-CVP success event of a program `P` on a fixed matrix `H` (Theorem 1.1,
p.2; Theorem 4.7, p.39): the set of coin tapes on which, **for every** target `y ∈ Qⁿ`, the run on
`(H, y)` halts with output a vector `x` that solves γ-CVP for `(H, y)`. One tape serves all
targets (R6). -/
def cvpGood (P : Program) (γ : ℚ) {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) :
    Set (ℕ → Bool) :=
  {τ | ∀ y : Fin n → ℚ, ∃ x : Fin n → ℤ, IsApproxCVP γ H y x ∧
      callOutput P (Config.init (encInst H y)) τ = some (encZVec x)}

/-- `H` is good for `P`: the simultaneous success event is measurable and has probability at
least `1 − ε` under fair coins. -/
def GoodMatrix (P : Program) (γ : ℚ) {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q))
    (ε : ℝ) : Prop :=
  MeasurableSet (cvpGood P γ H) ∧ 1 - ε ≤ (coinTape (cvpGood P γ H)).toReal

/-- The output word of a possibly failing procedure: the empty word for `⊥` (`none`), the entries
of `x` otherwise (distinguishable since `n ≥ 1` in every use). -/
def optWord {n : ℕ} : Option (Fin n → ℤ) → List ℚ
  | none => []
  | some x => encZVec x

/-- On input word `w`, `P` halts on every coin tape with bit time at most `T` (no space claim). -/
def TimeWithin (P : Program) (w : List ℚ) (T : ℝ) : Prop :=
  ∀ τ : ℕ → Bool, ∃ s : RunStats, runStats P τ (Config.init w) = some s ∧ (s.time : ℝ) ≤ T

/-- The success event of a first-output short solver on `(A, t)`: the tapes on which the run
outputs some vector (not `⊥`, the empty word). -/
def firstSucc (P : Program) {m n q : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod q))
    (t : Fin m → ZMod q) : Set (ℕ → Bool) :=
  {τ | ∃ v : Fin n → ℤ, callOutput P (Config.init (encShort A t)) τ = some (encZVec v)}

end QaryCVP


