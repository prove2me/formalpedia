-- Prove2me | Definitions.Def_KelnerLinSolve_dixonRes
-- name    : KelnerLinSolve_dixonRes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:28.765085+00:00
-- url     : https://prove2.me/theorems/2828c6fb-1ae8-4cbf-a6ac-3bc6090c2dee
-- title:
--   Dixon's lifting recurrence: digits $x_i$, residuals $b_i$, prefixes $y_k$, and the norms $\|b\|_\infty$, $\|M\|_\infty$
-- statement:
--   Let $M, C \in \mathbb Z^{n\times n}$, $R\in\mathbb Z$ and $b\in\mathbb Z^n$. Dixon's lifting sets $b_0 = b$ and
--
--   $$
--   x_i = C b_i \bmod R, \qquad b_{i+1} = \frac{b_i - M x_i}{R},
--   $$
--
--   with $x_i \in \{0,\dots,R-1\}^n$ for $R\ge2$, and $y_k = \sum_{i=0}^{k-1} R^i x_i$. For an integer vector $b$, $\|b\|_\infty = \max_i|b_i|$; for an integer matrix $M$, $\|M\|_\infty = \max_i \sum_j |M_{ij}|$ is the maximum absolute row sum.
--
--   **Formalization Note** The reduction is `Int.emod` and the division `Int.ediv`; the division is exact when $MC\equiv I \pmod R$, which is a conclusion of the milestone on (1)–(3), not part of this definition.
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), §2.1, p.4, Equations (1)–(3); §2.2, p.6

import Mathlib

open Matrix

namespace KelnerLinSolve

/-- The digit `x = C b mod R` of one Dixon lifting step, Equation (2): coordinatewise
`Int.emod`, so every coordinate lies in `{0, …, R − 1}` when `R ≥ 2`.
Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission
(sha256 d1af55cb…), §2.1, p.4, Equation (2). -/
def dixonDigitOf {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (R : ℤ) (bi : Fin n → ℤ) : Fin n → ℤ :=
  fun r => (C *ᵥ bi) r % R

/-- **The residuals `b_i` of Dixon's lifting**, Equations (2)–(3) (Kelner, sha256 d1af55cb…,
§2.1, p.4): `b₀ = b`, `xᵢ = C bᵢ mod R`, `b_{i+1} = (bᵢ − M xᵢ) / R`.

**Formalization Note.** `/` on `ℤ` is `Int.ediv`, which rounds; the page's division is exact when
`M C ≡ I (mod R)`, and that exactness is a conclusion of the milestone on (1)–(3), not built into
this definition. -/
def dixonRes {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℤ) (R : ℤ) (b : Fin n → ℤ) : ℕ → (Fin n → ℤ)
  | 0 => b
  | i + 1 => fun r => (dixonRes M C R b i r - (M *ᵥ dixonDigitOf C R (dixonRes M C R b i)) r) / R

/-- The digit vector `xᵢ = C bᵢ mod R` of Dixon's lifting (Kelner, sha256 d1af55cb…, §2.1, p.4,
Equation (2)). -/
def dixonDigit {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℤ) (R : ℤ) (b : Fin n → ℤ) (i : ℕ) :
    Fin n → ℤ :=
  dixonDigitOf C R (dixonRes M C R b i)

/-- The prefix sums `y_k = ∑_{i=0}^{k−1} Rⁱ xᵢ` of Dixon's lifting (Kelner, sha256 d1af55cb…,
§2.1, p.4). -/
def dixonPrefix {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℤ) (R : ℤ) (b : Fin n → ℤ) (k : ℕ) :
    Fin n → ℤ :=
  ∑ i ∈ Finset.range k, R ^ i • dixonDigit M C R b i

/-- The max norm `‖b‖_∞ = maxᵢ |bᵢ|` of an integer vector (`0` for `n = 0`), Kelner
(sha256 d1af55cb…), Lemma 2.2, p.6. -/
def supNormZ {n : ℕ} (b : Fin n → ℤ) : ℕ := Finset.univ.sup fun i => (b i).natAbs

/-- The **maximum absolute row sum** `‖M‖_∞ = maxᵢ ∑ⱼ |M_{ij}|` of an integer matrix (`0` for
`n = 0`): "Here `‖M‖_∞ = maxᵢ ∑ⱼ |M_{ij}|` is the maximum absolute row sum", Kelner
(sha256 d1af55cb…), §2.2, p.6, before Lemma 2.2. Not the entrywise maximum. -/
def rowSumNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  Finset.univ.sup fun i => ∑ j, (M i j).natAbs

end KelnerLinSolve


