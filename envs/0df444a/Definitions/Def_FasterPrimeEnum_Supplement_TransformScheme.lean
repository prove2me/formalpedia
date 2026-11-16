-- Prove2me | Definitions.Def_FasterPrimeEnum_Supplement_TransformScheme
-- name    : FasterPrimeEnum_Supplement_TransformScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:47:34.286868+00:00
-- url     : https://prove2.me/theorems/8e1136e4-0cd2-4b79-bbb2-fc8282786c1e
-- title:
--   Transform schemes over $\mathbb F_2$ and their costs $T(n)$, $K^*(n)$, $K(n)$; $C^*(n)$
-- statement:
--   A **transform pair of order $n$** (Definition 4.17) is an integer $K\ge1$ with $\mathbb F_2$-linear maps $F:\mathbb F_2[x]_n\to\mathbb F_2^K$ and $I:\mathbb F_2^K\to\mathbb F_2[x]_{2n-1}$ such that
--
--   $$
--   I\big(F(f)\cdot F(g)\big)=fg\qquad\text{for all } f,g\in\mathbb F_2[x]_n,
--   $$
--
--   where $\cdot$ is the componentwise product in $\mathbb F_2^K$.
--
--   A **transform scheme** (Definition 4.18) consists of a transform pair $(K_n,F_n,I_n)$ for each $n\ge1$, a forward algorithm computing $F_n(f)$ from $n$ and $f$, and an inverse algorithm computing $I_n(u)$ from $n$ and $u$. Its costs are:
--
--   1. $T(n)$, the larger of the worst-case running times of the forward and inverse algorithms at size $n$;
--   2. $K^*(n):=\max_{1\le m\le n}K_m/m$ and $K(n):=n\cdot K^*(n)$.
--
--   Given also a multiplication algorithm, $C^*(n):=M^*(n)+K^*(n)$ (§5.2).
--
--   Transform schemes let a polynomial that occurs in many products be transformed once and reused, which is how the core algorithm saves time.
--
--   **Formalization Note** $\mathbb F_2[x]_n$ and $\mathbb F_2^K$ are functions `Fin n → ZMod 2` and `Fin K → ZMod 2`; machines read $n$ in binary and the bit array of the argument.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Definitions 4.17–4.18, pp.23–24; §5.2, p.36

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_FasterPrimeEnum_Supplement_MulAlgorithm

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- **A transform scheme over `F₂`** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851
(held version, sha256 7fc13f17…), Definitions 4.17 and 4.18, p.23.

Definition 4.17: "Let n ⩾ 1 be an integer. By a transform pair of order n (over F₂) we mean an
integer K ⩾ 1 together with a pair of F₂-linear maps F : F₂[x]_n → F₂^K, I : F₂^K → F₂[x]_{2n−1}
with the property that I(F(f) · F(g)) = fg for any f, g ∈ F₂[x]_n. Here the dot operator means
pointwise multiplication in F₂^K."

Definition 4.18: "A transform scheme (over F₂) consists of the following data: a family of
transform pairs (K_n, F_n, I_n), one for each integer n ⩾ 1; a forward transform algorithm that
takes as input n ⩾ 1 and f ∈ F₂[x]_n and computes F_n(f) ∈ F₂^{K_n}; an inverse transform algorithm
that takes as input n ⩾ 1 and u ∈ F₂^{K_n} and computes I_n(u) ∈ F₂[x]_{2n−1}."

**Formalization Note.** `F₂[x]_n` is `Fin n → ZMod 2` (the `n` coefficients), `F₂^K` is
`Fin K → ZMod 2`, the dot is the pointwise product of functions, and `fg ∈ F₂[x]_{2n−1}` is
`convF2 f g`. The fields at `n = 0` are unconstrained. The forward machine reads the framed pair of
`n` in binary and the bit array of `f`, and halts with the `K_n` bits of `F_n(f)`; the inverse
machine reads `n` and the `K_n` bits of `u`, and halts with the `2n − 1` bits of `I_n(u)`. -/
structure TransformScheme where
  /-- The lengths `K_n`. -/
  K : ℕ → ℕ
  /-- `K_n ≥ 1` for `n ≥ 1`. -/
  K_pos : ∀ n : ℕ, 1 ≤ n → 1 ≤ K n
  /-- The forward transforms `F_n`. -/
  F : (n : ℕ) → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (K n) → ZMod 2)
  /-- The inverse transforms `I_n`. -/
  I : (n : ℕ) → (Fin (K n) → ZMod 2) →ₗ[ZMod 2] (Fin (2 * n - 1) → ZMod 2)
  /-- The transform pair property `I(F(f) · F(g)) = fg`. -/
  pair : ∀ n : ℕ, 1 ≤ n → ∀ f g : Fin n → ZMod 2, I n (F n f * F n g) = convF2 f g
  /-- The forward transform machine. -/
  fwd : PrimitiveMachine
  /-- Its output tape. -/
  fwdOut : Fin fwd.tapeCount
  /-- The inverse transform machine. -/
  inv : PrimitiveMachine
  /-- Its output tape. -/
  invOut : Fin inv.tapeCount
  /-- The forward machine computes `F_n(f)`. -/
  fwd_correct : ∀ n : ℕ, 1 ≤ n → ∀ f : Fin n → ZMod 2, ∃ τ : ℝ,
    RunsWithin fwd fwdOut (Encoding.encodeList id [binWord n, vecBits f]) (vecBits (F n f)) τ
  /-- The inverse machine computes `I_n(u)`. -/
  inv_correct : ∀ n : ℕ, 1 ≤ n → ∀ u : Fin (K n) → ZMod 2, ∃ τ : ℝ,
    RunsWithin inv invOut (Encoding.encodeList id [binWord n, vecBits u]) (vecBits (I n u)) τ

namespace TransformScheme

variable (TS : TransformScheme)

/-- `T(n)` (p.23): "We write T(n) for the running time of the forward and inverse transform
algorithms (whichever is larger)" — the worst case over all inputs of size `n`. -/
noncomputable def Tcost (n : ℕ) : ℝ :=
  max
    (((Finset.univ : Finset (Fin n → ZMod 2)).sup fun f =>
      haltTime TS.fwd (TS.fwd.init (Encoding.encodeList id [binWord n, vecBits f])) : ℕ) : ℝ)
    (((Finset.univ : Finset (Fin (TS.K n) → ZMod 2)).sup fun u =>
      haltTime TS.inv (TS.inv.init (Encoding.encodeList id [binWord n, vecBits u])) : ℕ) : ℝ)

/-- `K*(n) := max_{1 ⩽ m ⩽ n} K_m / m`, `n ≥ 1` (pp.23–24). -/
noncomputable def Kstar (n : ℕ) : ℝ := ⨆ m : Finset.Icc 1 n, (TS.K m : ℝ) / (m : ℝ)

/-- `K(n) := n · K*(n)` (p.24). -/
noncomputable def Kcost (n : ℕ) : ℝ := (n : ℝ) * TS.Kstar n

end TransformScheme

/-- `C*(n) := M*(n) + K*(n)`, `n ≥ 1` (§5.2, p.36), for the fixed multiplication algorithm and
transform scheme. -/
noncomputable def Cstar (Mul : MulAlgorithm) (TS : TransformScheme) (n : ℕ) : ℝ :=
  Mul.Mstar n + TS.Kstar n

end Supplement

end FasterPrimeEnum


