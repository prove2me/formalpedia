-- Prove2me | Definitions.Def_KelnerLinSolve_IntInstance
-- name    : KelnerLinSolve_IntInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:33.726968+00:00
-- url     : https://prove2.me/theorems/9ddfbde3-af9e-4c9f-88f5-750e72656819
-- title:
--   Integer inputs of SolvePerturbed and the exact output $(I+RA)^{-1}b$
-- statement:
--   An integer instance consists of $n$, the nonzero entries $(i,j,A_{ij})$ of $A\in\mathbb Z^{n\times n}$ listed in any order, $b\in\mathbb Z^n$, and $s$, with modulus $R = 2^s$. It is well formed if the positions are distinct and the values nonzero. Its input word lists $n$, $s$, $m$, the entries with their indices, and $b$. Its exact output is
--
--   $$
--   z = (I + RA)^{-1} b \in \mathbb Q^n ,
--   $$
--
--   computed over $\mathbb Q$; $I+RA$ is nonsingular because its determinant is $\equiv 1 \pmod R$.
--
--   **Formalization Note** Indices are $0$-based. The inverse is over $\mathbb Q$, never over $\mathbb Z$.
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Algorithm 1, p.9; Theorem 3.3, p.10

import Mathlib
import Definitions.Def_KelnerLinSolve_encInt
import Definitions.Def_KelnerLinSolve_solvePerturbedRes

open Matrix

namespace KelnerLinSolve

/-- **An integer input of `SolvePerturbed`** (Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit
Operations*, STOC 2027 submission (sha256 d1af55cb…), Algorithm 1, p.9, and Theorem 3.3, p.10): the
dimension `n`, the matrix `A ∈ ℤ^{n×n}` as a list of its nonzero entries `(i, j, A_{ij})` in any
order, the right-hand side `b ∈ ℤⁿ` as a vector, and the exponent `s` of the modulus `R = 2^s`. -/
structure IntInstance where
  n : ℕ
  entries : List (Fin n × Fin n × ℤ)
  rhs : Fin n → ℤ
  s : ℕ

namespace IntInstance

/-- The entry list lists distinct positions, each with a nonzero value. -/
def WellFormed (I : IntInstance) : Prop :=
  (I.entries.map fun t => (t.1, t.2.1)).Nodup ∧ ∀ t ∈ I.entries, t.2.2 ≠ 0

/-- The matrix `A` of the instance: the listed value at a listed position, `0` elsewhere (for a
well-formed list at most one entry matches a position). -/
def A (I : IntInstance) : Matrix (Fin I.n) (Fin I.n) ℤ := fun i j =>
  ((I.entries.filter fun t => t.1 == i && t.2.1 == j).map fun t => t.2.2).sum

/-- The number `m` of listed (nonzero) entries. -/
def m (I : IntInstance) : ℕ := I.entries.length

/-- The input word `n # s # m # i₁ # j₁ # a₁ # ⋯ # i_m # j_m # a_m # b₁ # ⋯ # bₙ`: naturals in
binary (`encNat`), integers in signed binary (`encInt`), indices `0`-based. -/
def encode (I : IntInstance) : List (Option Bool) :=
  IntMul.joinSep ([encNat I.n, encNat I.s, encNat I.entries.length]
    ++ (I.entries.flatMap fun t => [encNat t.1, encNat t.2.1, encInt t.2.2])
    ++ ((List.finRange I.n).map fun i => encInt (I.rhs i)))

/-- The exact output `z = (I + R A)⁻¹ b ∈ ℚⁿ` of `SolvePerturbed(A, b, R)` with `R = 2^s`, computed
over `ℚ`.

**Formalization Note.** The inverse is taken over `ℚ`, never over `ℤ`. `I + R A` has determinant
`≡ 1 (mod R)` for `R ≥ 2`, hence is nonsingular, so `⁻¹` is the true inverse. -/
noncomputable def perturbedSolution (I : IntInstance) : Fin I.n → ℚ :=
  (1 + ((2 : ℚ) ^ I.s) • I.A.map (Int.cast : ℤ → ℚ))⁻¹ *ᵥ fun i => (I.rhs i : ℚ)

end IntInstance

end KelnerLinSolve


