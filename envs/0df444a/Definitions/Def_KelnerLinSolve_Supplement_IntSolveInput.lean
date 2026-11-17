-- Prove2me | Definitions.Def_KelnerLinSolve_Supplement_IntSolveInput
-- name    : KelnerLinSolve_Supplement_IntSolveInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:34:38.029653+00:00
-- url     : https://prove2.me/theorems/1b88a3a8-e6f0-4f82-88cd-23aed7b375b9
-- title:
--   Input of the integer solver (Theorem 3.1) and the parameter $\tau=\max(B,\log\kappa,\log 1/\epsilon)$
-- statement:
--   An **input of the integer solver** consists of a dimension $n$, a matrix $A\in\mathbb Z^{n\times n}$ supplied as the list of its nonzero entries $(i,j,A_{ij})$ in any order, a right-hand side $b\in\mathbb Z^n$, and an integer $E\ge 0$ fixing the target accuracy $\epsilon = 2^{-E}$. The input is well formed when the listed positions are distinct and every listed value is nonzero; $m$ is the number of listed entries, and $A_{ij}$ is the listed value at a listed position and $0$ elsewhere.
--
--   The machine reads the word
--
--   $$
--   n\,\#\,E\,\#\,m\,\#\,i_1\,\#\,j_1\,\#\,a_1\,\#\cdots\#\,i_m\,\#\,j_m\,\#\,a_m\,\#\,b_1\,\#\cdots\#\,b_n ,
--   $$
--
--   with natural numbers in binary, integers in signed binary, and $0$-based indices. The word contains neither a bit bound nor the condition number.
--
--   For a bit bound $B$, the parameter of Theorem 3.1 is
--
--   $$
--   \tau = \max\bigl(B,\ \log_2\kappa_2(A),\ E\bigr),
--   $$
--
--   where $\kappa_2(A)=\|A\|_2\|A^{-1}\|_2$ is the spectral condition number of $A$ viewed as a real matrix and $E=\log_2(1/\epsilon)$.
--
--   These objects state the integer solver of Section 3, which Section 4 uses on rescaled floating-point inputs.
--
--   **Formalization Note** The structure mirrors the base mission's `KelnerLinSolve.IntInstance` with $E$ in place of the modulus exponent $s$; that structure is not reused because its encoding and exact solution read its last field as $R=2^s$. $\tau$ is a real number, not rounded.
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Theorem 3.1, p.8 (input, τ); §1.1, p.3 (encodings, base-2 logarithms); proof of Theorem 3.1, p.11 (κ = σ_max/σ_min)

import Mathlib
import Definitions.Def_IntMul_MultitapeWords
import Definitions.Def_KelnerLinSolve_encInt
import Definitions.Def_KelnerLinSolve_kappa2

open Matrix

namespace KelnerLinSolve.Supplement

/-- **An input of the integer solver of Theorem 3.1** (Kelner, *Solving Linear Systems in
Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission (sha256 d1af55cb…), Theorem 3.1, p.8): the
dimension `n`, the matrix `A ∈ ℤ^{n×n}` as a list of its nonzero entries `(i, j, A_{ij})` in any
order, the right-hand side `b ∈ ℤⁿ`, and the integer `E ≥ 0` of the target accuracy `ε = 2^{−E}`.

**Formalization Note.** This mirrors the base mission's `KelnerLinSolve.IntInstance`, with the
accuracy exponent `E` in place of the modulus exponent `s`; `IntInstance` is not reused because its
`encode` and `perturbedSolution` read its last field as `R = 2^s`. The input contains neither the
bit bound `B` nor the condition number `κ`: the algorithm is given `A`, `b` and `E` only. -/
structure IntSolveInput where
  n : ℕ
  entries : List (Fin n × Fin n × ℤ)
  rhs : Fin n → ℤ
  E : ℕ

namespace IntSolveInput

/-- The entry list lists distinct positions, each with a nonzero value. -/
def WellFormed (I : IntSolveInput) : Prop :=
  (I.entries.map fun t => (t.1, t.2.1)).Nodup ∧ ∀ t ∈ I.entries, t.2.2 ≠ 0

/-- The matrix `A` of the input: the listed value at a listed position, `0` elsewhere (for a
well-formed list at most one entry matches a position). -/
def A (I : IntSolveInput) : Matrix (Fin I.n) (Fin I.n) ℤ := fun i j =>
  ((I.entries.filter fun t => t.1 == i && t.2.1 == j).map fun t => t.2.2).sum

/-- The number `m` of listed (nonzero) entries of `A`. -/
def m (I : IntSolveInput) : ℕ := I.entries.length

/-- The input word `n # E # m # i₁ # j₁ # a₁ # ⋯ # i_m # j_m # a_m # b₁ # ⋯ # bₙ`: naturals in
binary (`encNat`), integers in signed binary (`encInt`), indices `0`-based. -/
def encode (I : IntSolveInput) : List (Option Bool) :=
  IntMul.joinSep ([encNat I.n, encNat I.E, encNat I.entries.length]
    ++ (I.entries.flatMap fun t => [encNat t.1, encNat t.2.1, encInt t.2.2])
    ++ ((List.finRange I.n).map fun i => encInt (I.rhs i)))

/-- `A` as a real matrix. -/
noncomputable def Areal (I : IntSolveInput) : Matrix (Fin I.n) (Fin I.n) ℝ :=
  I.A.map (Int.cast : ℤ → ℝ)

/-- `b` as a real vector. -/
noncomputable def breal (I : IntSolveInput) : Fin I.n → ℝ := fun i => (I.rhs i : ℝ)

/-- `τ = max(B, log κ, log 1/ε)` of Theorem 3.1 (Kelner, sha256 d1af55cb…, p.8) for a bit bound
`B`, with `κ = κ₂(A)` the spectral condition number and `log 1/ε = E` (logarithms base 2, p.3).

**Formalization Note.** A real number, not rounded. `log₂ κ` is `Real.logb 2 (kappa2 A)`; it is
`≥ 0` for nonsingular `A` with `n ≥ 1`, where `κ₂(A) ≥ 1`. -/
noncomputable def tau (I : IntSolveInput) (B : ℕ) : ℝ :=
  max (B : ℝ) (max (Real.logb 2 (kappa2 I.Areal)) (I.E : ℝ))

end IntSolveInput

end KelnerLinSolve.Supplement


