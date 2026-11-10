-- Prove2me | Definitions.Def_SuperlatSVP_SolvesSVPWithin
-- name    : SuperlatSVP_SolvesSVPWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:25.063348+00:00
-- url     : https://prove2.me/theorems/c8edbc67-ab16-4597-ac23-5ca465e9ee56
-- title:
--   Solving SVP on a rational basis within given bit time and bit space, with probability $\ge 2/3$
-- statement:
--   The algorithmic statements of the mission are about a randomized **log-cost rational RAM**: the published machine `TwMSOCount.Main`, whose cells hold exact rationals and which reads fair coins. Its cost measures are:
--
--   - **bit time**: arithmetic on operands of bit lengths $\ell_1,\ell_2$ costs $(\ell_1+\ell_2+1)^2$, and a load or store costs the address and value bits;
--   - **bit space**: the address and content bits of every cell ever written, maximized over the run.
--
--   An instance is an invertible $B\in\mathbb Q^{n\times n}$. Its **input word** is $n$ followed by the entries of $B$ row by row, one stored rational each, and its **input length** $\ell$ is the total bit length of that word. A coefficient vector $x\in\mathbb Z^n$ **solves SVP** for $B$ when $Bx\ne0$ and $\|Bx\|^2\le\|By\|^2$ for every nonzero $y\in\mathbb Z^n$, i.e. $Bx$ is a nonzero vector of length $\lambda_1(L(B))$. The output word of such an answer is the list of the $n$ entries of $x$.
--
--   A program $P$ **solves SVP on $B$ within time $T$ and space $S$ with exponent $K$** when:
--
--   1. on every coin tape the run of $P$ on the input word halts, with bit time at most $T\cdot(\ell+1)^K$ and bit space at most $S\cdot(\ell+1)^K$;
--   2. the event that the output is the coefficient vector of a shortest nonzero vector of $L(B)$ is measurable and has probability at least $2/3$ under fair coins.
--
--   This is the success notion of Theorem 1.4 and Corollary 1.5.
--
--   **Formalization Note** The time bound holds on every coin tape, not in expectation. Inputs are rational, as for any algorithm. The machine's own `encodeInput` and `codeGraph` belong to another paper and are not used.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §2.1, p.14 (PDF p.14); Theorem 1.4 and Corollary 1.5, p.5

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine

open MeasureTheory TwMSOCount.Main
open scoped ENNReal

namespace SuperlatSVP

/-- The input word of a basis `B ∈ ℚ^{n×n}`: the dimension `n`, then the entries of `B` row by
row, one stored rational each. -/
def encBasis {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) : List ℚ :=
  (n : ℚ) :: (List.finRange n).flatMap fun i => (List.finRange n).map fun j => B i j

/-- The input length `ℓ`: the total bit length of the input word. -/
def inputBits {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) : ℕ := ((encBasis B).map qbits).sum

/-- Squared Euclidean norm of a rational vector. -/
def sqNorm {n : ℕ} (v : Fin n → ℚ) : ℚ := ∑ i, v i ^ 2

/-- SVP (§2.1, p.14: "Given a basis of L, the shortest vector problem (SVP) asks to find a nonzero
vector of length λ1(L)"): the integer coefficient vector `x` gives a shortest nonzero vector `Bx`
of `L(B)`, i.e. `Bx ≠ 0` and `‖Bx‖² ≤ ‖By‖²` for every nonzero `y ∈ ℤⁿ`.

**Formalization Note.** For an invertible `B`, `By ≠ 0` iff `y ≠ 0`; squared norms are compared
in `ℚ`. -/
def IsShortest {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℤ) : Prop :=
  B.mulVec (fun i => (x i : ℚ)) ≠ 0 ∧
    ∀ y : Fin n → ℤ, y ≠ 0 →
      sqNorm (B.mulVec (fun i => (x i : ℚ))) ≤ sqNorm (B.mulVec (fun i => (y i : ℚ)))

/-- The output word of a coefficient vector: its `n` integer entries. -/
def encIntVec {n : ℕ} (x : Fin n → ℤ) : List ℚ := (List.finRange n).map fun i => (x i : ℚ)

/-- The event that the run of `P` on the input word of `B` halts with output a shortest nonzero
vector of `L(B)` (as coefficients). -/
def svpSuccess (P : Program) {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) : Set (ℕ → Bool) :=
  {τ | ∃ x : Fin n → ℤ, IsShortest B x ∧
      callOutput P (Config.init (encBasis B)) τ = some (encIntVec x)}

/-- A randomized program solves SVP on the basis `B` within time bound `T·(ℓ+1)^K` and space
bound `S·(ℓ+1)^K` (Theorem 1.4, p.5; Corollary 1.5, p.5; §2, p.14: "All parameters … are
implicitly parameterized by the dimension n and the bit-length of the input basis"):

1. on **every** coin tape the run halts, with bit time at most `T·(ℓ+1)^K` and bit space at most
   `S·(ℓ+1)^K`, `ℓ = inputBits B`;
2. the success event (output a shortest nonzero vector) is measurable and has probability at least
   `2/3` under fair coins.

**Formalization Note.** The machine is the published randomized log-cost rational RAM
`TwMSOCount.Main` (bit time; bit space counts the address and content bits of every cell ever
written, maximized over the run). Its `encodeInput` and `codeGraph` belong to another paper and are
not used. -/
def SolvesSVPWithin (P : Program) (K : ℕ) (T S : ℝ) {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) :
    Prop :=
  (∀ τ : ℕ → Bool, ∃ s : RunStats, runStats P τ (Config.init (encBasis B)) = some s ∧
      (s.time : ℝ) ≤ T * ((inputBits B : ℝ) + 1) ^ K ∧
      (s.space : ℝ) ≤ S * ((inputBits B : ℝ) + 1) ^ K) ∧
    MeasurableSet (svpSuccess P B) ∧
    (2 / 3 : ℝ≥0∞) ≤ coinTape (svpSuccess P B)

end SuperlatSVP


