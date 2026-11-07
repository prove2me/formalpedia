-- Prove2me | Definitions.Def_GaussToomCook_Step
-- name    : GaussToomCook_Step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:10.700275+00:00
-- url     : https://prove2.me/theorems/b1ed2c77-3c10-440d-887a-773fca32b8b2
-- title:
--   Steps of the interpolation phase and their evaluation
-- statement:
--   The interpolation phase (V) of Gaussian Toom–Cook-$k$ is modelled in §9.1 as a sequence of vectors $w_1,w_2,\dots$ of $W$. With $\mathcal W_0$ the starting set and $\mathcal W_i=\mathcal W_{i-1}\cup\{w_i\}$, each new vector is computed as either
--
--   1. (i) $w_i=\lambda v+\mu u$ with $\lambda,\mu\in\mathbb Z[i]$ and $v,u\in\mathcal W_{i-1}$, or
--   2. (ii) $w_i=v/\lambda$ with $\lambda\in\mathbb Z[i]\setminus\{0\}$ and $v\in\mathcal W_{i-1}$.
--
--   This module defines a **step** (`lin a b λ μ` or `div a λ`, where $a,b$ are positions in the current list), the vector a step produces from the current list (undefined if a position is out of range or a division has $\lambda=0$), the divisor of a step of type (ii), and the **run** of a list of steps, which appends each new vector to the list and fails if some step is undefined.
--
--   A step of type (ii) is a **division**; it is a division by a multiple of $p$ when $p\mid\lambda$.
--
--   **Formalization Note** Sets are represented by lists and operands by their positions; $v=u$ is allowed. Scalars from $\mathbb Z[i]$ act on $\mathbb C^n$ through `GaussianInt.toComplex`. Allowing scalars outside $\mathbb Z[i]$ would make every $q_j$ reachable without any division.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §9.1, p. 30 (PDF p. 32)

import Mathlib

namespace GaussToomCook

/-- **One step of the interpolation phase**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §9.1, p. 30 (PDF 32).
Each new element `w_i` of the sequence is computed as either

* (i) `lin a b λ μ`: `w_i = λ v + μ u` with `λ, μ ∈ ℤ[i]`, where `v`, `u` are the vectors at positions
  `a`, `b` of the current list `W_{i−1}`; or
* (ii) `div a λ`: `w_i = v / λ` with `λ ∈ ℤ[i] \ {0}`, where `v` is the vector at position `a`.

**Formalization Note.** The current set `W_{i−1}` is represented by a list; operands are referred to by
their position in it, and `v = u` is allowed. -/
inductive Step where
  | lin (a b : ℕ) (l m : GaussianInt)
  | div (a : ℕ) (l : GaussianInt)

namespace Step

/-- The vector produced by a step from the current list `W` (§9.1, p. 30): `λ v + μ u` for a step of type
(i), `λ⁻¹ v` for a step of type (ii). The result is `none` (the step is invalid) when a position is out of
range or when a division has `λ = 0`.

**Formalization Note.** Scalars `λ, μ ∈ ℤ[i]` act on `Fin n → ℂ` through `GaussianInt.toComplex`. -/
noncomputable def apply {n : ℕ} (W : List (Fin n → ℂ)) : Step → Option (Fin n → ℂ)
  | lin a b l m =>
      match W[a]?, W[b]? with
      | some v, some u => some (GaussianInt.toComplex l • v + GaussianInt.toComplex m • u)
      | _, _ => none
  | div a l =>
      if l = 0 then none
      else
        match W[a]? with
        | some v => some ((GaussianInt.toComplex l)⁻¹ • v)
        | none => none

/-- The divisor `λ` of a step of type (ii), and `none` for a step of type (i). -/
def divisor? : Step → Option GaussianInt
  | lin _ _ _ _ => none
  | div _ l => some l

end Step

/-- **Running an interpolation program**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §9.1, p. 30 (PDF 32): starting from
the list `W₀`, each step appends its new vector `w_i`, so `W_i = W_{i−1} ∪ {w_i}`. The result is the final
list `W_N`, or `none` if some step is invalid. -/
noncomputable def run {n : ℕ} : List (Fin n → ℂ) → List Step → Option (List (Fin n → ℂ))
  | W, [] => some W
  | W, s :: prog =>
      match s.apply W with
      | some w => run (W ++ [w]) prog
      | none => none

end GaussToomCook


