-- Prove2me | Definitions.Def_DIObliviousTransfer_Negligible
-- name    : DIObliviousTransfer_Negligible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:02:17.742358+00:00
-- url     : https://prove2.me/theorems/fd2126a7-b597-4cba-9bd7-3e7417ca4ce8
-- title:
--   Negligible functions, polynomial bounds, and string encodings
-- statement:
--   Throughout, $\lambda\in\mathbb N$ is the security parameter. A function $\mu:\mathbb N\to\mathbb R$ is **negligible** if it is nonnegative and for every $c$ it is eventually below $(\lambda+1)^{-c}$. A function $f:\mathbb N\to\mathbb N$ is **polynomially bounded** if $f(n)\le P(n)$ for a polynomial $P$ with natural coefficients.
--
--   Classical strings are finite bit lists. Lists of strings are encoded injectively and self-delimitingly (each bit $b$ becomes $1b$, each item is closed by $0$), and natural numbers by their binary expansion. The module also fixes $s_\lambda=\lceil\log_2^2(\lambda+2)\rceil$ and the Elias-$\gamma$ code length $2\lfloor\log_2 n\rfloor+1$ used to charge adaptive control symbols.
--
--   **Formalization Note** The bodies of `PolyBound` and `Negligible` are those of the published `TightPQRepetition_Main_Complexity` (985ecc42), restated because that module is not in this workspace.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), §2, p.13; (7), p.27; Definition 3 (ii), p.16

import Mathlib

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, *Robust and Leakage-Resilient Device-Independent Oblivious Transfer in
MiniQCrypt*, arXiv:2610.01421 (held version, sha256 8334c039…), §2 (p.13) and §2.4 (pp.16–18):
the asymptotic vocabulary. `lam` is the security parameter `λ` (a Lean keyword).

**Formalization Note** (decisions D4, D17 of the mission). A negligible function is nonnegative and
eventually below `(λ+1)^{-c}` for every `c`; `PolyBound` is a bound by a polynomial with natural
coefficients. Both bodies are those of the published `TightPQRepetition_Main_Complexity`
(985ecc42), restated because that module is not in this workspace. Strings are `List Bool`, with
the injective self-delimiting encoding `pack` of a list of strings (`b ↦ 1b`, item closed by `0`).
All logarithms are base two (p.13).
-/

/-- Classical strings. -/
abbrev Bits := List Bool

/-- `f` is bounded by a polynomial. -/
def PolyBound (f : ℕ → ℕ) : Prop := ∃ P : Polynomial ℕ, ∀ n, f n ≤ P.eval n

/-- A negligible function: nonnegative, and eventually below the inverse of every polynomial. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ f n) ∧ ∀ c : ℕ, ∃ N, ∀ n, N ≤ n → f n < 1 / ((n : ℝ) + 1) ^ c

/-- The self-delimiting encoding of one string: `b ↦ 1b`, closed by a `0`. -/
def packOne (x : Bits) : Bits := x.flatMap (fun b => [true, b]) ++ [false]

/-- The injective encoding of a list of strings as one string. -/
def pack (l : List Bits) : Bits := l.flatMap packOne

/-- Parsing of `pack`; `cur` is the reversed current item. A truncated trailing item is dropped. -/
def unpackAux : Bits → Bits → List Bits
  | [], _ => []
  | false :: rest, cur => cur.reverse :: unpackAux rest []
  | true :: b :: rest, cur => unpackAux rest (b :: cur)
  | [true], _ => []

/-- The inverse of `pack`, total on all strings. -/
def unpack (x : Bits) : List Bits := unpackAux x []

/-- The binary expansion of `n` (most significant bit first; `[]` for `0`). -/
def natBits (n : ℕ) : Bits := (Nat.bits n).reverse

/-- A natural number read from its binary expansion (most significant bit first). -/
def bitsNat (b : Bits) : ℕ := b.foldl (fun acc x => 2 * acc + if x then 1 else 0) 0

/-- A natural number as a string (`pack`-compatible field). -/
def encNat (n : ℕ) : Bits := natBits n

/-- `s_λ = ⌈log₂²(λ + 2)⌉` (p.27, (7); p.3). -/
noncomputable def sLam (lam : ℕ) : ℕ := Nat.ceil ((Real.logb 2 ((lam : ℝ) + 2)) ^ 2)

/-- Elias-γ code length of a positive integer `n`: `2⌊log₂ n⌋ + 1`. -/
def eliasGammaLen (n : ℕ) : ℕ := 2 * Nat.log 2 n + 1

end DIObliviousTransfer


