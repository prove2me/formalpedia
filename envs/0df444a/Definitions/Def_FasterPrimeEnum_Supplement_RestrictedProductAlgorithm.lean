-- Prove2me | Definitions.Def_FasterPrimeEnum_Supplement_RestrictedProductAlgorithm
-- name    : FasterPrimeEnum_Supplement_RestrictedProductAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:48:10.448203+00:00
-- url     : https://prove2.me/theorems/90570ad1-ade7-4885-b5f1-559d7db99f79
-- title:
--   Restricted product algorithms over $\mathbb F_2$ and their costs $\bar R, R^*, R$
-- statement:
--   For $n\ge1$, $f\in\mathbb F_2[x]_{2n}$ and $g\in\mathbb F_2[x^{-1}]_n$, the restricted product $f\lhd g$ (Definition 2.2, coefficient of $x^k$ equal to $\sum_{j=0}^{k} f_{k+j}g_j$) lies in $\mathbb F_2[x]_{2n}$; this is a **restricted product of size $n$**. A **restricted product algorithm** is a Turing machine computing the $2n$ coefficients of $f\lhd g$ from those of $f$ and $g$, for every $n\ge1$.
--
--   Its costs (§4.4, p.27) are defined like those of multiplication: $\bar R(n)$ is the worst-case running time at size $n$, $\bar R^*(n):=\bar R(n)/(n\max(1,\log n))$, $R^*(n):=\max_{1\le m\le n}\bar R^*(m)$ and $R(n):=n\max(1,\log n)\cdot R^*(n)$.
--
--   Restricted products evaluate the generating function $H_2$ of Definition 2.4, one of the three series whose sum detects square-primes modulo 2.
--
--   **Formalization Note** The coefficient formula is the published `FasterPrimeEnum.restrictedProd`.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), §4.4, p.27; Definition 2.2, p.14

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_FasterPrimeEnum_restrictedProd
import Definitions.Def_FasterPrimeEnum_Supplement_MulAlgorithm

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- The restricted product `f ⊲ g ∈ F₂[x]_{2n}` of `f ∈ F₂[x]_{2n}` and `g ∈ F₂[x^{−1}]_n`, by its
`2n` coefficients: the coefficient of `x^k` is the published `restrictedProd` (Definition 2.2,
p.14) of the coefficient functions of `f` (coefficient of `x^i`) and `g` (coefficient of `x^{−j}`),
both extended by `0`. -/
def rpVec {n : ℕ} (f : Fin (2 * n) → ZMod 2) (g : Fin n → ZMod 2) : Fin (2 * n) → ZMod 2 :=
  fun k => restrictedProd (fun i => if h : i < 2 * n then f ⟨i, h⟩ else 0)
    (fun j => if h : j < n then g ⟨j, h⟩ else 0) k.val

/-- **A restricted product algorithm over `F₂`** — D. Harvey, *Faster enumeration of primes*,
arXiv:2606.22851 (held version, sha256 7fc13f17…), §4.4, p.27: "Let n ⩾ 1. If f ∈ F₂[x]_{2n} and
g ∈ F₂[x^{−1}]_n, then f ⊲ g ∈ F₂[x]_{2n}. We call this a restricted product of size n (over F₂).
Given an algorithm for performing this operation, …"

A machine `A` with output tape `out` that, for every `n ≥ 1`, given the framed pair of the `2n`
coefficients of `f` (of `x^0, …, x^{2n−1}`) and the `n` coefficients of `g` (of
`x^0, x^{−1}, …, x^{−n+1}`), halts with the `2n` coefficients of `f ⊲ g` on `out`. -/
structure RestrictedProductAlgorithm where
  /-- The machine. -/
  A : PrimitiveMachine
  /-- Its output tape. -/
  out : Fin A.tapeCount
  /-- It computes every restricted product of size `n ≥ 1`. -/
  correct : ∀ n : ℕ, 1 ≤ n → ∀ (f : Fin (2 * n) → ZMod 2) (g : Fin n → ZMod 2), ∃ τ : ℝ,
    RunsWithin A out (Encoding.encodeList id [vecBits f, vecBits g]) (vecBits (rpVec f g)) τ

namespace RestrictedProductAlgorithm

variable (RP : RestrictedProductAlgorithm)

/-- `R̄(n)` (p.27): the worst-case running time on restricted products of size `n`. -/
noncomputable def Rbar (n : ℕ) : ℝ :=
  ((Finset.univ : Finset ((Fin (2 * n) → ZMod 2) × (Fin n → ZMod 2))).sup fun fg =>
    haltTime RP.A (RP.A.init (Encoding.encodeList id [vecBits fg.1, vecBits fg.2])) : ℕ)

/-- `R̄*(n) := R̄(n) / (n max(1, log n))`, `n ≥ 1` (p.27). -/
noncomputable def Rbarstar (n : ℕ) : ℝ := RP.Rbar n / ((n : ℝ) * max 1 (Real.log n))

/-- `R*(n) := max_{1 ⩽ m ⩽ n} R̄*(m)`, `n ≥ 1` (p.27). -/
noncomputable def Rstar (n : ℕ) : ℝ := ⨆ m : Finset.Icc 1 n, RP.Rbarstar m

/-- `R(n) := n max(1, log n) · R*(n)`, `n ≥ 1` (p.27). -/
noncomputable def Rcost (n : ℕ) : ℝ := (n : ℝ) * max 1 (Real.log n) * RP.Rstar n

end RestrictedProductAlgorithm

end Supplement

end FasterPrimeEnum


