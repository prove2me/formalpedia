-- Prove2me | Definitions.Def_FasterPrimeEnum_Supplement_MulAlgorithm
-- name    : FasterPrimeEnum_Supplement_MulAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:47:03.38222+00:00
-- url     : https://prove2.me/theorems/188af3a2-6f01-477b-87fa-052afdc619e7
-- title:
--   A multiplication algorithm for $\mathbb F_2[x]$ and its cost functions $\bar M, M^*, M$
-- statement:
--   A **multiplication algorithm** for $\mathbb F_2[x]$ is a Turing machine that, for every $n\ge1$ and all polynomials $f,g\in\mathbb F_2[x]_n$ (degree less than $n$), given the coefficient arrays of $f$ and $g$, outputs the $2n-1$ coefficients of $fg$.
--
--   Its cost functions (§4.1, p.19) are, for $n\ge 1$:
--
--   1. $\bar M(n)$, the worst-case running time on inputs of degree less than $n$;
--   2. $\bar M^*(n) := \bar M(n)/(n\max(1,\log n))$;
--   3. $M^*(n) := \max_{1\le m\le n}\bar M^*(m)$, which is non-decreasing;
--   4. $M(n) := n\max(1,\log n)\cdot M^*(n)$.
--
--   The paper assumes throughout (4.2): for each $k\ge 1$, $M(kn)\ll_k M(n)$, i.e. there is $c_k>0$ with $M(kn)\le c_k M(n)$ for all $n\ge1$.
--
--   These smoothed costs are the currency in which every complexity bound of §§4–6 is stated, so that the results improve automatically with faster multiplication.
--
--   **Formalization Note** Polynomials of $\mathbb F_2[x]_n$ are given as arrays of exactly $n$ bits (leading zeros allowed). The running time of a halting run is the number of steps to the halted configuration (`haltTime`).
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), §4.1, p.19, eq. (4.2)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- A vector of `F₂^n` as a bit array, in index order (`true` = 1). Polynomials of `F₂[x]_n` (degree
`< n`) are vectors of their `n` coefficients in the monomial basis (D. Harvey, *Faster enumeration
of primes*, arXiv:2606.22851, held version, sha256 7fc13f17…, §4, p.19: "Polynomials in F₂[x] will
be represented by an array of bits, i.e., as a sequence of coefficients in F₂ with respect to the
usual monomial basis"). -/
def vecBits {n : ℕ} (v : Fin n → ZMod 2) : List Bool := List.ofFn fun i => decide (v i = 1)

/-- The product of `f, g ∈ F₂[x]_n` as an element of `F₂[x]_{2n−1}`: the coefficient of `x^k` is
`Σ_{i + j = k} f_i g_j`, for `0 ≤ k < 2n − 1`. -/
def convF2 {n : ℕ} (f g : Fin n → ZMod 2) : Fin (2 * n - 1) → ZMod 2 :=
  fun k => ∑ i : Fin n, ∑ j : Fin n, if i.val + j.val = k.val then f i * g j else 0

/-- The number of steps after which the deterministic machine `A`, started from `c`, halts. It is
the least `t` such that a run of `t` steps reaches a halted configuration; it is used only for
machines that halt on the inputs in question (it is `0` if no run halts). -/
noncomputable def haltTime (A : PrimitiveMachine) (c : A.Cfg) : ℕ :=
  sInf {t : ℕ | ∃ final : A.Cfg, Trace A.step t c final ∧ ∃ b : Bool, final.state = Sum.inl b}

/-- **A multiplication algorithm for `F₂[x]`** — D. Harvey, *Faster enumeration of primes*,
arXiv:2606.22851 (held version, sha256 7fc13f17…), §4.1, p.19: "Fix some algorithm (Turing machine)
for multiplying polynomials in F₂[x]."

A machine `A` with output tape `out` that, for every `n ≥ 1` and all `f, g ∈ F₂[x]_n` (degree
`< n`), given the framed pair of their `n`-bit coefficient arrays, halts with the `2n − 1`
coefficients of `fg` on `out`.

**Formalization Note.** Inputs of degree `< n` are given as arrays of exactly `n` bits (leading
zeros allowed), which is how the worst case over "inputs of degree less than n" is taken below. -/
structure MulAlgorithm where
  /-- The machine. -/
  A : PrimitiveMachine
  /-- Its output tape. -/
  out : Fin A.tapeCount
  /-- It multiplies every pair of polynomials of degree `< n`, for every `n ≥ 1`. -/
  correct : ∀ n : ℕ, 1 ≤ n → ∀ f g : Fin n → ZMod 2, ∃ τ : ℝ,
    RunsWithin A out (Encoding.encodeList id [vecBits f, vecBits g]) (vecBits (convF2 f g)) τ

namespace MulAlgorithm

variable (Mul : MulAlgorithm)

/-- `M̄(n)` (p.19): "the worst-case running time of the algorithm on inputs of degree less than n". -/
noncomputable def Mbar (n : ℕ) : ℝ :=
  ((Finset.univ : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2))).sup fun fg =>
    haltTime Mul.A (Mul.A.init (Encoding.encodeList id [vecBits fg.1, vecBits fg.2])) : ℕ)

/-- `M̄*(n) := M̄(n) / (n max(1, log n))`, `n ≥ 1` (p.19). -/
noncomputable def Mbarstar (n : ℕ) : ℝ := Mul.Mbar n / ((n : ℝ) * max 1 (Real.log n))

/-- `M*(n) := max_{1 ⩽ m ⩽ n} M̄*(m)`, `n ≥ 1` (p.19). -/
noncomputable def Mstar (n : ℕ) : ℝ := ⨆ m : Finset.Icc 1 n, Mul.Mbarstar m

/-- `M(n) := n max(1, log n) · M*(n)`, `n ≥ 1` (p.19). -/
noncomputable def Mcost (n : ℕ) : ℝ := (n : ℝ) * max 1 (Real.log n) * Mul.Mstar n

/-- **Assumption (4.2)**, p.19: "For technical reasons it will also be convenient to assume that
M(kn) ≪_k M(n) for each k ⩾ 1." For each `k ≥ 1` a constant `c > 0` with `M(kn) ≤ c M(n)` for every
`n ≥ 1`. -/
def Assumption42 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → Mul.Mcost (k * n) ≤ c * Mul.Mcost n

end MulAlgorithm

end Supplement

end FasterPrimeEnum


