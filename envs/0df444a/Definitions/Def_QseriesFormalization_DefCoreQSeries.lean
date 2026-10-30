-- Prove2me | Definitions.Def_QseriesFormalization_DefCoreQSeries
-- name    : QseriesFormalization_DefCoreQSeries
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:23:24.493986+00:00
-- url     : https://prove2.me/theorems/bfb9420b-364d-4567-ac9a-aa6cb5379ac4
-- title:
--   Partitions, finite q-series, and Jacobi and pentagonal products
-- statement:
--   The basic definitions include the triangular number $n(n+1)/2$ on naturals, the finite $q$-Pochhammer symbols $(q;q)_n=\prod_{j=1}^n(1-q^j)$ and $(a;q)_n=\prod_{k=0}^{n-1}(1-aq^k)$ over a commutative ring (by recursion), and two finite-sum helpers: `natSum` ($f(0)+\dots+f(n)$) and `bilateralSum` ($\sum_{j=-N}^{N}f(j)$). It also defines the Gaussian ($q$-binomial) coefficient $\binom{n}{k}_q$ by the Pascal-type recursion used in Chapter 3. These are the shared building blocks for later chapters.
--
--   The definitions include the partition function $p(n)$ as the cardinality of the set of integer partitions of $n$, and the two families of generalized pentagonal numbers $k(3k-1)/2$ and $k(3k+1)/2$ on natural numbers. It also defines a computable table-based version of Euler's pentagonal recurrence for $p(n)$ (`partitionCountRec` with its helper table and step functions), used to check values against the recurrence.
--
--   The definitions include the partition generating function $\sum p(n)X^n$ over a commutative semiring, the single factor $1-X^{k+1}$, the finite formal $q$-Pochhammer product $(q;q)_N=\prod_{k<N}(1-X^{k+1})$, and the infinite product $(q;q)_\infty$ as the formal inverse of the partition series. It also contains the characteristic-$p$ instance for power series, the signed strict-partition character and count, the Jacobi triple sign $\tau(n)=(-1)^k(2k+1)$ for $n=k(k+1)/2$ ($0$ otherwise), and the theta series $\sum_n\tau(n)X^n$ over any commutative ring $R$.
--
--   The definitions include, for complex $q,z$, the infinite product $\prod_{n\ge1}(1-q^{2n})(1+zq^{2n-1})(1+z^{-1}q^{2n-1})$ (as a Lean `tprod` over positive integers), its natural-number-indexed factors and finite partial products, and the bilateral series $\sum_{n\in\mathbb{Z}}z^nq^{n^2}$. It also defines symmetric finite partial sums of that series, the pair term added at height $n+1$, its norm majorant, and partial sums of those pairs, used for convergence arguments.
--
--   These definitions use Lean’s totalized operations: $0^{-1}=0$, tsum is $0$ for a nonsummable complex family, and tprod is $1$ for a nonmultipliable complex family. Convergence is established separately under the parameter conditions of the relevant theorems.
--
--   The definitions include the left side $\prod(1+xq^k)$ of the finite $q$-binomial theorem by recursion, its general term $\binom nk_q q^{k(k-1)/2}x^k$, and its right side as a finite sum of those terms. It also defines, over $\mathbb{C}$, the Gaussian-weighted symmetric pair terms, partial sums, tails and Laurent summands that arise from the finite Jacobi triple product (using $\binom{2N}{k}_{q^2}$ and $z^{k-N}q^{(k-N)^2}$), together with the finite JTP summand and its right-hand finite sum from Chan's Eq. (3.15).
--
--   Integer powers and reciprocals use Lean’s totalized convention: $0^{-1}=0$, so $0$ raised to a negative integer is $0$. The usual reciprocal interpretation applies when the base is nonzero.
--
--   The definitions include, over $\mathbb{C}$, the factors and infinite products for Euler's pentagonal theorem (the three-residue factor $(1-q^{3(n+1)})(1-q^{3(n+1)-2})(1-q^{3(n+1)-1})$ for $n\ge0$ and the factor $1-q^{n+1}$), the mod-5 factor $1-q^{k+5n}$ used for Rogers--Ramanujan, and the infinite product side of the quintuple product identity (Chan's Eq. 2.12 form). It also defines the bilateral series side of the quintuple product (summand $(z^3/q^2)^nq^{3n^2}-(q/z)(q^4/z^3)^nq^{3n^2}$) and the shear equivalence $(a,b)\mapsto(a+2b,b)$ on $\mathbb{Z}^2$ used in the proof.
--
--   The complex sums and products are Lean’s totalized tsum and tprod, with respective defaults $0$ and $1$ when summability or multipliability fails. Inverses use $0^{-1}=0$; these definitions alone impose no convergence or nonzero-parameter assumptions.
--
--   The definitions include the formal arithmetic-progression factor $1-X^{r+mn}$ and product $(q^r;q^m)_\infty$, the two mod-5 triple products $(q,q^4,q^5;q^5)_\infty$ and $(q^2,q^3,q^5;q^5)_\infty$ with their per-$n$ factors, the pentagonal exponents $k(5k-3)/2$ and $k(5k-1)/2$ (truncated to naturals), and the bilateral theta series $\sum_k(-1)^kX^{k(5k-3)/2}$ and $\sum_k(-1)^kX^{k(5k-1)/2}$ with their coefficient functions. It further defines analytic (complex) theta terms and products and the corresponding formal multilinear series, used to compare formal and analytic Jacobi triple product sides.
--
--   The general AP product uses Lean’s tprod for arbitrary natural $r,m$; the positivity and topology conditions needed for its usual formal-product interpretation occur in separate results. The complex theta sums and products are totalized, with defaults $0$ and $1$ when summability or multipliability fails.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Basic.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).
--
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).
--
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).
--
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 2. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter02.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).
--
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 3. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter03.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).
--
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).
--
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean (definitions of this module that the uploaded theorems need; ported to Lean v4.33.1 / Mathlib 0df444a).

-- Definition group: QseriesFormalization_DefCoreQSeries; exact rendered source bodies in isolated sections.
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

-- Source module: QseriesFormalization.Basic
section

/-!
# Basic objects for q-series formalization

Definitions used throughout *An Invitation to q-Series* (Hei-Chi Chan, 2011):
partitions, triangular and pentagonal numbers, the q-Pochhammer symbol,
finite sums, and Gaussian (q-binomial) coefficients.

These live in the root `QseriesFormalization` namespace so individual
chapters (in `QseriesFormalization.PartI.Ch02` etc.) can reuse them
without prefix juggling.
-/

namespace QseriesFormalization

/-! ### Partitions (Ch 1) -/

/-! ### Triangular and pentagonal numbers (Ch 1, Ch 4) -/

/-- Triangular number `n (n + 1) / 2`. -/
def triangular (n : Nat) : Nat :=
  n * (n + 1) / 2

@[simp] theorem triangular_zero : triangular 0 = 0 := rfl

/-! ### q-Pochhammer (Ch 1) -/

section CommRing

variable {R : Type*} [CommRing R]

/-- Finite q-Pochhammer symbol `(q; q)_n = ∏_{j=1}^n (1 - q^j)`. -/
def qPochhammer (q : R) : Nat → R
  | 0 => 1
  | Nat.succ n => qPochhammer q n * (1 - q ^ (Nat.succ n))

/-- General q-Pochhammer symbol `(a; q)_n = ∏_{k=0}^{n-1} (1 - a q^k)`. -/
def qPoch (a q : R) : Nat → R
  | 0 => 1
  | Nat.succ n => qPoch a q n * (1 - a * q ^ n)

@[simp] theorem qPochhammer_zero (q : R) : qPochhammer q 0 = 1 := rfl

@[simp] theorem qPochhammer_succ (q : R) (n : Nat) :
    qPochhammer q (Nat.succ n) = qPochhammer q n * (1 - q ^ (Nat.succ n)) := rfl

@[simp] theorem qPoch_zero (a q : R) : qPoch a q 0 = 1 := rfl

@[simp] theorem qPoch_succ (a q : R) (n : Nat) :
    qPoch a q (Nat.succ n) = qPoch a q n * (1 - a * q ^ n) := rfl

end CommRing

/-! ### Finite sums (Ch 3) -/

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- A simple finite summation helper: `natSum f n = f 0 + … + f n`. -/
def natSum (f : Nat → R) : Nat → R
  | 0 => f 0
  | Nat.succ n => natSum f n + f (Nat.succ n)

@[simp] theorem natSum_zero (f : Nat → R) : natSum f 0 = f 0 := rfl

@[simp] theorem natSum_succ (f : Nat → R) (n : Nat) :
    natSum f (Nat.succ n) = natSum f n + f (Nat.succ n) := rfl

/-- Bilateral sum `∑_{j = -N}^{N} f j`. Implemented as
`f 0 + ∑_{k=1}^{N} (f k + f (-k))`. -/
def bilateralSum (f : Int → R) : Nat → R
  | 0 => f 0
  | Nat.succ n => bilateralSum f n + (f (n + 1 : Int) + f (-(n + 1 : Int)))

@[simp] theorem bilateralSum_zero (f : Int → R) : bilateralSum f 0 = f 0 := rfl

@[simp] theorem bilateralSum_succ (f : Int → R) (n : Nat) :
    bilateralSum f (Nat.succ n) =
      bilateralSum f n + (f (n + 1 : Int) + f (-(n + 1 : Int))) := rfl

/-! ### Gaussian (q-binomial) coefficients (Ch 3) -/

/-- Gaussian (q-binomial) coefficients, defined recursively as in Chapter 3. -/
def gaussianBinom (q : R) : Nat → Nat → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | Nat.succ n, Nat.succ k =>
      gaussianBinom q n (Nat.succ k) + q ^ (n - k) * gaussianBinom q n k

@[simp] theorem gaussianBinom_zero_left_succ (q : R) (k : Nat) :
    gaussianBinom q 0 (Nat.succ k) = 0 := rfl

end CommSemiring

end QseriesFormalization

end

-- Source module: QseriesFormalization.Chapter01
section

/-!
# Chapter 1: Introduction

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 1.)

Most of the introductory material—partitions, triangular numbers,
the q-Pochhammer symbol—lives in `QseriesFormalization.Basic`.
This file collects any chapter-specific lemmas that are too lightweight
to belong in `Basic.lean` but that the introduction relies on.

Currently empty; populated as we work through Chapter 1.
-/

namespace QseriesFormalization
namespace Ch01

/-- The partition function `p(n)` (Chan Def 1.1, Eq 1.8). -/
def partitionCount (n : Nat) : Nat := Fintype.card (Nat.Partition n)

/-- The generalized pentagonal number `k(3k-1)/2`. -/
def pentagonalLower (k : Nat) : Nat := k * (3 * k - 1) / 2

/-- The generalized pentagonal number `k(3k+1)/2`. -/
def pentagonalUpper (k : Nat) : Nat := k * (3 * k + 1) / 2

/-- One Euler pentagonal recurrence step, evaluated from a table of earlier values. -/
def partitionCountRecFrom (values : List Nat) (n : Nat) : Nat :=
  let term (j : Nat) : Int :=
    let k := j + 1
    let subtotal : Nat :=
      (if pentagonalLower k ≤ n then values.getD (n - pentagonalLower k) 0 else 0) +
      (if pentagonalUpper k ≤ n then values.getD (n - pentagonalUpper k) 0 else 0)
    if k % 2 = 1 then (subtotal : Int) else -((subtotal : Int))
  Int.toNat ((Finset.range n).sum term)

/-- Table of values produced by Euler's pentagonal recurrence through index `n`. -/
def partitionCountRecTable : Nat → List Nat
  | 0 => [1]
  | Nat.succ n =>
      let previous := partitionCountRecTable n
      previous ++ [partitionCountRecFrom previous (n + 1)]

/-- Pentagonal recurrence value at `n`, computed from the finite table of earlier values. -/
def partitionCountRec (n : Nat) : Nat :=
  (partitionCountRecTable n).getD n 0

/-! ## Euler's pentagonal recurrence

Euler's identity `(∑ₙ p(n) qⁿ) · ∏_{i ≥ 1} (1 - qⁱ) = 1` and the pentagonal number theorem
`∏_{i ≥ 1} (1 - qⁱ) = ∑_{k ∈ ℤ} (-1)ᵏ q^{k(3k-1)/2}` (both available in Mathlib) give, on comparing
the coefficients of `qⁿ` for `n ≥ 1`,

  `p(n) = ∑_{k ≥ 1} (-1)^{k+1} (p(n - k(3k-1)/2) + p(n - k(3k+1)/2))`,

where terms with a negative argument are omitted. `partitionCountRec` evaluates exactly this
recurrence from the table of earlier values, so it agrees with `partitionCount` for every `n`
(`partitionCountRec_eq_partitionCount`). The concrete values `p(2), …, p(11)` below (and
`p(12), …` in the companion files) then follow by evaluating `partitionCountRec`, without
enumerating partitions. -/

section EulerRecurrence

open scoped PowerSeries.WithPiTopology

end EulerRecurrence

section CommRing

variable {R : Type*} [CommRing R]

end CommRing

end Ch01
end QseriesFormalization

end

-- Source module: QseriesFormalization.Chapter19
section

namespace QseriesFormalization
namespace PartIV
namespace Ch19

open QseriesFormalization.Ch01 (partitionCount)
open PowerSeries

-- Ramanujan's deeper congruences require higher partition values.
-- Here we verify congruences using p(0)..p(11) proved in Ch01.

-- p(25n+24) ≡ 0 (mod 25) requires partitionCount_24 (not yet in Ch01).

-- Additional divisibility and modular facts

-- p(n) mod 3 for n=0..11

-- p(n) mod 4

/-! ### Modular arithmetic for primes 13, 17, 19, 23 -/

-- p(n) mod 13

-- p(n) mod 17

-- p(n) mod 19

-- p(n) mod 23

/-! ### Composite moduli -/

-- p(n) mod 10

-- p(n) mod 12

-- p(n) mod 15

/-! ### Additional divisibility facts -/

/-! ### Ramanujan's congruences verified at available indices

`p(5n+4) ≡ 0 (mod 5)` for n = 0, 1
`p(7n+5) ≡ 0 (mod 7)` for n = 0
`p(11n+6) ≡ 0 (mod 11)` for n = 0
-/

/-! ### Pentagonal recurrence agreement (Chan §1)

`partitionCountRec` is the Euler pentagonal recurrence formulation of p(n).
For n = 0..11, it agrees with the actual partition count `partitionCount n`. -/

/-! ### Specific Ramanujan-congruence identities -/

/-! ### Mod 6 patterns (composite where p(6) is divisible) -/

/-! ### Mod 8 -/

/-! ### Mod 9 -/

/-! ### Cumulative partition sums

`∑_{k=0}^n p(k)` for small n. -/

/-! ### Order properties of p -/

/-! ### Parity (mod 2) -/

/-! ### Bounds: p(n) ≥ n+1 for n=0..4, and various comparisons -/

/-! ### Growth ratios

p(n+1)/p(n) is monotonically increasing for small n. Verified numerically. -/

/-! ### Specific differences -/

/-! ### Number-theoretic properties of specific values

p(n) for n where p(n) has interesting prime factorization. -/

/-! ### Squarefree-ness checks -/

/-! ### Ramanujan family — uniform interface

A Ramanujan congruence is `m ∣ p(m·n + r)`. The classical Ramanujan congruences:
- `m = 5, r = 4`: `5 ∣ p(5n + 4)` (proved at n=0, 1)
- `m = 7, r = 5`: `7 ∣ p(7n + 5)` (proved at n=0)
- `m = 11, r = 6`: `11 ∣ p(11n + 6)` (proved at n=0)
-/

/-! ### Non-Ramanujan: counter-examples

Some `(m, r)` patterns are NOT Ramanujan families. -/

/-! ### Partition generating function and Ramanujan congruences

We use Mathlib's `Nat.Partition.genFun` infrastructure. Setting the character
function `f = (fun _ _ => 1)` gives the standard partition generating function
`∑ p(n) X^n` with the Euler product identity `∏ 1/(1 - X^(k+1))`.

This is the foundation for proving the **general** Ramanujan congruences
(`5 ∣ p(5n+4)`, etc.) by Frobenius-mod-p techniques on power series. -/

/-- The standard partition generating function over a commutative semiring `R`:
`∑_{n ≥ 0} p(n) · X^n ∈ R⟦X⟧`, where `p(n)` is the partition count of `n`. -/
noncomputable def partitionGenFun (R : Type*) [CommSemiring R] : R⟦X⟧ :=
  Nat.Partition.genFun (fun _ _ => (1 : R))

section EulerProductFormal

open scoped PowerSeries.WithPiTopology

end EulerProductFormal

/-! ### Ramanujan congruence at the power series level

Goal: prove `(partitionGenFun (ZMod 5)).coeff (5*n + 4) = 0` for all n.

This is the **algebraic** Ramanujan congruence: it says the coefficients of
the partition generating function over ZMod 5 vanish in arithmetic progression
4 mod 5. Equivalently `5 ∣ partitionCount (5n+4)` for all n.

The classical proof (Ramanujan 1919) uses:
1. Frobenius mod 5: `(1 - X^k)^5 = 1 - X^{5k}` in `(ZMod 5)⟦X⟧`.
2. `(q;q)∞^4 ≡ (q^5;q^5)∞ · J(q) (mod 5)` where `J = 1/(q;q)∞`.
3. Jacobi's identity for `(q;q)∞^3`.
4. Mod-5 coefficient analysis.

We state the result and verified instances. -/

/-! ### Frobenius endomorphism for power series over `ZMod p`

In `(ZMod p)⟦X⟧`, the map `φ ↦ φ^p` is a ring endomorphism (the Frobenius).
In particular `(a + b)^p = a^p + b^p` for all a, b. This gives us:
`(1 + c · X^k)^p = 1 + c^p · X^{kp}`

For `c = -1` (and odd `p`): `(1 - X^k)^p = 1 - X^{kp}`.

This is the algebraic key to Ramanujan's mod-p congruences. -/

/-- `PowerSeries R` inherits characteristic p from `R` via the injective embedding `C`. -/
instance powerSeries_charP (R : Type*) [CommSemiring R] (p : Nat) [CharP R p] :
    CharP R⟦X⟧ p where
  cast_eq_zero_iff n := by
    constructor
    · intro h
      -- Apply constantCoeff to extract: constantCoeff (↑n) = ↑n in R
      have h0 : (PowerSeries.constantCoeff : R⟦X⟧ →+* R) (n : R⟦X⟧) = 0 := by
        rw [h]; exact map_zero _
      rw [map_natCast] at h0
      exact (CharP.cast_eq_zero_iff R p n).mp h0
    · intro h
      have hR : (n : R) = 0 := (CharP.cast_eq_zero_iff R p n).mpr h
      have hcast : (n : R⟦X⟧) = (PowerSeries.C : R →+* R⟦X⟧) (n : R) :=
        (map_natCast (PowerSeries.C : R →+* R⟦X⟧) n).symm
      rw [hcast, hR, map_zero]

/-! ### Finite q-Pochhammer and the Euler product

The finite q-Pochhammer `(q;q)_N = ∏_{k=1}^N (1 - q^k)` is a polynomial-like
power series. Frobenius applied factor-by-factor gives:
`(q;q)_N^p ≡ (q^p; q^p)_N (mod p)` in `(ZMod p)⟦X⟧`. -/

/-- Single factor of the q-Pochhammer product: `1 - X^(k+1)` as a power series. -/
noncomputable def oneSubXPow (R : Type*) [CommRing R] (k : Nat) : R⟦X⟧ :=
  1 - (PowerSeries.X : R⟦X⟧) ^ (k + 1)

/-- Finite q-Pochhammer as a formal power series: `(q;q)_N = ∏_{k<N}(1 - X^{k+1})`. -/
noncomputable def qPochFinitePS (R : Type*) [CommRing R] (N : Nat) : R⟦X⟧ :=
  ∏ k ∈ Finset.range N, oneSubXPow R k

/-! ### The q ↦ q^p substitution on power series

Define a power series operation `subXPow p f` that sends `∑ aₙ Xⁿ` to `∑ aₙ X^{pn}`.
This is the "raise the variable" map, central to Ramanujan's argument:
in `(ZMod p)⟦X⟧`, `(q;q)∞^p = (q^p; q^p)∞`. -/

/-! ### Use Mathlib's `PowerSeries.expand` (the variable substitution X ↦ X^p)

Mathlib provides `PowerSeries.expand p hp : R⟦X⟧ →ₐ[R] R⟦X⟧` which sends
`∑ aₙ Xⁿ` to `∑ aₙ X^{p·n}`. This is the same operation as our `subXPow` but
already comes with the full algebra-homomorphism structure.

The key theorem is `MvPowerSeries.map_frobenius_expand`:
`(f.expand p).map (frobenius R p) = f ^ p`

For `R = ZMod p`, the Frobenius map on ZMod p is the identity (Fermat's little
theorem), so we get the clean form:

**`f.expand p hp = f ^ p` in `(ZMod p)⟦X⟧`** -/

/-! ### The `(q;q)∞` formal power series

We define `qPochInfPS R := (partitionGenFun R)⁻¹` (as a power series inverse,
which exists since the constant term of `partitionGenFun R` is 1, a unit).

This gives us `partitionGenFun R * qPochInfPS R = 1` algebraically. -/

/-- `(q;q)∞` as the formal power series inverse of `partitionGenFun`. -/
noncomputable def qPochInfPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.invOfUnit (partitionGenFun R) 1

section FormalEulerBridge

open scoped PowerSeries.WithPiTopology

section CoeffTprodBridge

open Filter Topology

end CoeffTprodBridge

end FormalEulerBridge

section SignedStrictPartition

open scoped PowerSeries.WithPiTopology

/-- The character function picking out strict (multiplicity-1) partitions with sign.
For `i ≥ 1` and `j = 1`: returns `-1`. For other `(i, j)`: returns `0`.

When applied via `Nat.Partition.genFun`, this gives the formal Euler product
`∏(1 - X^(i+1)) = qPochInfPS`, whose coefficient at `n` is the signed count
of strict partitions of `n`. -/
noncomputable def signedStrictChar (R : Type*) [Ring R] : ℕ → ℕ → R :=
  fun i j => if i ≥ 1 ∧ j = 1 then -1 else 0

/-- **Signed strict partition count via Nat.Partition** (using Mathlib's `Nat.Partition`).
This is the sum over partitions of `n` (with no repeated parts, weighted by sign). -/
noncomputable def signedStrictCount (R : Type*) [CommRing R] (n : ℕ) : R :=
  (Nat.Partition.genFun (signedStrictChar R)).coeff n

end SignedStrictPartition

section BridgeToCh05Pentagonal

open PowerSeries
open scoped PowerSeries.WithPiTopology

end BridgeToCh05Pentagonal

/-! ### Specific qPochInfPS coefficient values via Euler pentagonal

Derived from `coeff_qPochInfPS_eq_pentagonalSign` + `decide` on `pentagonalSign n` for
specific small n. These extend beyond the n=0..8 values proved via the J·qPoch=1 recurrence
in earlier sections. -/

/-! ### B2 groundwork: Jacobi triple product at z=1 (cube identity)

Goal: prove `(qPochInfPS R)^3 = ∑ (-1)^n (2n+1) X^{n(n+1)/2}` as formal power series.

This is the classical Jacobi identity `∏(1-q^n)^3 = ∑(-1)^n(2n+1)q^{T_n}`.
Ch04_T43 has the analytic version (`jacobiIdentity`) for `|q| < 1`.

The formal-PS version requires either:
  (a) Combinatorial proof via Sylvester-style involution on triple partitions
  (b) Analytic → formal bridge via Taylor expansion uniqueness

Both are substantial work; we define the target and prove small cases here. -/

/-- The Jacobi triple sign: `(-1)^k · (2k+1)` if `n = k(k+1)/2` for some `k ≥ 0`,
else `0`. This is the expected `n`-th coefficient of `(q;q)_∞^3`. -/
def jacobiTripleSign (n : Nat) : Int :=
  match (List.range (n + 1)).find? (fun k => n = k * (k + 1) / 2) with
  | some k => (-1 : Int) ^ k * (2 * k + 1)
  | none => 0

-- Sanity: triangular numbers 0, 1, 3, 6, 10, 15, ...
-- Values:                    1, -3, 5, -7, 9, -11, ...

/-- The Jacobi theta-like formal power series: `∑ (-1)^k (2k+1) X^{T_k}`. -/
noncomputable def jacobiThetaPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk fun n => ((jacobiTripleSign n : ℤ) : R)

-- **B2 target theorem**: `(qPochInfPS R)^3 = jacobiThetaPS R` in `R⟦X⟧`.
-- This is the formal-PS version of Jacobi's identity (Ch04.jacobiIdentity in
-- analytic form). Full proof requires either Sylvester's combinatorial bijection
-- or an analytic ↔ formal Taylor uniqueness bridge.

-- Small case verification: `(qPochInfPS R)^3 . coeff n` for small n is computable
-- via the generic `coeff_n_pow_of_constantCoeff_one` helpers in Ch20 and Euler-pentagonal
-- coefficient values. See Ch20.ramanujanTau_two for the analogous tau computation pattern.

/-! ### Conditional Ramanujan congruence

If the coefficients of `(q;q)∞^(p-1)` vanish on the arithmetic progression
`pn + r` (mod p), then by the key identity the LHS `J · (q;q)∞.expand p`
also vanishes there.

The actual vanishing of `(q;q)∞^(p-1)` coefficients on the appropriate
progression (for p=5, r=4; p=7, r=5; p=11, r=6) follows from Jacobi's
triple product identity — the next major step to formalize. -/

/-! ### Conditional Ramanujan theorem

If the coefficients of `(q;q)∞^(p-1)` vanish on the arithmetic progression
`p·n + r` (in `(ZMod p)⟦X⟧`), then `partitionCount(p·n + r) ≡ 0 (mod p)`. -/

/-! ### Ramanujan congruences — conditional corollaries

The three classical Ramanujan partition congruences are mod 5, 7, 11, each
on a specific residue class. Below are the conditional statements: assuming
the corresponding `(q;q)∞^(p-1)` coefficient vanishes on the progression. -/

/-! ### N=0 Ramanujan identity: closed-form bridge

For `0 ≤ r < p`, the algebraic identity collapses cleanly:
`((q;q)∞^(p-1)).coeff r = (p(r) : ZMod p)`.

This is the n=0 case of the conditional Ramanujan. The LHS can be computed
directly from the Euler-pentagonal coefficients of qPochInfPS via the
binomial expansion. -/

/-! ### Status note: path to full Ramanujan mod 5

**Completed real theorems**:
- `powerSeries_charP`: CharP instance for PowerSeries (R⟦X⟧ inherits char from R)
- `PowerSeries.expand_eq_pow_zmod`: Frobenius — `f.expand p = f^p` in (ZMod p)⟦X⟧
- `partitionGenFun`: formal partition generating function (via Mathlib's `Nat.Partition.genFun`)
- `coeff_partitionGenFun_int/_rat`: connection to Ch01's `partitionCount`
- `qPochInfPS`: formal `(q;q)∞` via `PowerSeries.invOfUnit`
- `partitionGenFun_mul_qPochInfPS`: `J · (q;q)∞ = 1`
- `ramanujan_key_identity`: in (ZMod p)⟦X⟧, `J · (q;q)∞.expand p = (q;q)∞^(p-1)`
- `coeff_eq_of_key_identity`: coefficient corollary

**Remaining for full Ramanujan mod 5** (each substantial):

1. **Euler pentagonal** as formal power series:
   `(q;q)∞ = ∑_{n ∈ ℤ} (-1)^n X^{n(3n-1)/2}`
   Reference: Ch04Franklin's `euler_pentagonal_combinatorial` (Franklin involution),
   bridged via `signedStrictPartitionCount n = qPochInfPS.coeff n` (cast).

2. **Jacobi identity** as formal power series:
   `(q;q)∞^3 = ∑_{k ≥ 0} (-1)^k (2k+1) X^{k(k+1)/2}`
   Reference: Ch03's Jacobi triple product, specialized.

3. **Mod-5 vanishing analysis**: show `((q;q)∞^4).coeff (5n+4) = 0` in (ZMod 5)⟦X⟧
   by analyzing pairs `(m, k)` with `m(3m-1)/2 + k(k+1)/2 = 5n+4`, showing the
   `(2k+1)` factor is always ≡ 0 (mod 5).

4. **Coefficient extraction + induction**: from `coeff_eq_of_key_identity`,
   derive the linear recurrence `partitionCount(5n+4) = -∑_{k≥1} ...`,
   then induct on n.

Steps 1-2 are substantial but reuse existing Q-series infrastructure.
Step 3 is finite combinatorial. Step 4 is straightforward induction. -/

end Ch19
end PartIV
end QseriesFormalization

end

-- Source module: QseriesFormalization.Chapter02
section

/-!
# Chapter 2 — Part I: First proof of Jacobi's triple product (functional equation)

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 2, pp. 5–10.)

Chapter 2 proves Jacobi's triple product identity by exhibiting a function
that satisfies a functional equation `F(qz) = (1 + z) F(z)` and pinning it
down via growth/uniqueness arguments.

Truncated forms of the product and bilateral series are defined here as
recursive `def`s; the infinite forms `jacobiInfiniteProduct` and
`jacobiInfiniteSeries` use Mathlib's `tprod` and `tsum`. The final identity
`jacobiTripleProduct` is proved in `Chapter03.lean`, where the finite-JTP
machinery needed for the Gaussian-tail argument is available.
-/

namespace QseriesFormalization
namespace PartI
namespace Ch02

section Field

variable {R : Type*} [Field R]

end Field

section InfiniteForms

open Filter
open scoped Topology

/--
The infinite Jacobi triple product side
`∏_{n=1}^∞ (1 - q^{2n})(1 + z q^{2n-1})(1 + z⁻¹ q^{2n-1})`.
Returns 1 if the family is not multipliable, following Mathlib's `tprod`
convention.
-/
noncomputable def jacobiInfiniteProduct (q z : ℂ) : ℂ :=
  ∏' n : ℕ+, (1 - q ^ (2 * n.val)) *
    (1 + z * q ^ (2 * n.val - 1)) *
    (1 + z⁻¹ * q ^ (2 * n.val - 1))

/-- The even product factor, Nat-indexed from exponent `2`. -/
def jacobiProductEvenFactor (q : ℂ) (n : ℕ) : ℂ :=
  1 - q ^ (2 * (n + 1))

/-- One odd product factor family, Nat-indexed from exponent `1`. -/
def jacobiProductOddFactor (q c : ℂ) (n : ℕ) : ℂ :=
  1 + c * q ^ (2 * (n + 1) - 1)

/-- The full Nat-indexed product factor for Chapter 2's JTP product side. -/
noncomputable def jacobiProductNatFactor (q z : ℂ) (n : ℕ) : ℂ :=
  jacobiProductEvenFactor q n * jacobiProductOddFactor q z n *
    jacobiProductOddFactor q z⁻¹ n

/-- The zero-based finite product corresponding to the infinite JTP product side. -/
noncomputable def jacobiProductPartial (q z : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, jacobiProductNatFactor q z n

/-- The bilateral series `∑_{n = -∞}^{∞} z^n q^{n^2}`. -/
noncomputable def jacobiInfiniteSeries (q z : ℂ) : ℂ :=
  ∑' n : ℤ, z ^ n * q ^ (n ^ 2)

/-- The symmetric finite partial sum of the bilateral JTP series. -/
noncomputable def jacobiSeriesSymmetricPartial (q z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), z ^ n * q ^ (n ^ 2)

/-- The pair of symmetric nonzero terms added at height `n + 1`. -/
noncomputable def jacobiSeriesSymmetricPairTerm (q z : ℂ) (n : ℕ) : ℂ :=
  z ^ (-(((n + 1 : ℕ) : ℤ))) * q ^ ((-(((n + 1 : ℕ) : ℤ))) ^ 2) +
    z ^ (((n + 1 : ℕ) : ℤ)) * q ^ ((((n + 1 : ℕ) : ℤ)) ^ 2)

/-- The sum of the norms of the two summands in a symmetric nonzero pair. -/
noncomputable def jacobiSeriesSymmetricPairNormMajorant (q z : ℂ) (n : ℕ) : ℝ :=
  ‖z ^ (-(((n + 1 : ℕ) : ℤ))) * q ^ ((-(((n + 1 : ℕ) : ℤ))) ^ 2)‖ +
    ‖z ^ (((n + 1 : ℕ) : ℤ)) * q ^ ((((n + 1 : ℕ) : ℤ)) ^ 2)‖

/-- The sum of the first `N` symmetric nonzero term pairs. -/
noncomputable def jacobiSeriesSymmetricPairPartial (q z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, jacobiSeriesSymmetricPairTerm q z n

end InfiniteForms

end Ch02
end PartI
end QseriesFormalization

end

-- Source module: QseriesFormalization.Chapter03
section

/-!
# Chapter 3 — Part I: Second proof (Gaussian polynomials and the q-binomial theorem)

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 3, pp. 11–20.)

Gaussian (q-binomial) coefficients are defined in `Basic.lean`. This file
states and proves the finite q-binomial theorem
`∏_{k=0}^{n-1} (1 + x q^k) = ∑_{k=0}^n [n choose k]_q q^{k(k-1)/2} x^k`.

The main theorem is proved by induction from the defining q-Pascal recursion
for Gaussian binomial coefficients.
-/

namespace QseriesFormalization
namespace PartI
namespace Ch03

section CommRing

variable {R : Type*} [CommRing R]

end CommRing

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Left side of the finite q-binomial theorem. -/
def qBinomialLHS (q x : R) : Nat → R
  | 0 => 1
  | Nat.succ n => qBinomialLHS q x n * (1 + x * q ^ n)

/-- A single term on the right side of the finite q-binomial theorem. -/
def qBinomialTerm (q x : R) (n k : Nat) : R :=
  gaussianBinom q n k * q ^ (k * (k - 1) / 2) * x ^ k

/-- Right side of the finite q-binomial theorem (closed-form finite sum). -/
def qBinomialRHS (q x : R) (n : Nat) : R :=
  natSum (fun k => qBinomialTerm q x n k) n

@[simp] theorem qBinomialLHS_zero (q x : R) : qBinomialLHS q x 0 = 1 := rfl

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

end CommRing

section ComplexLimits

open Filter
open scoped Topology

/-- The first `M` Gaussian-weighted symmetric nonzero pairs from the finite JTP RHS. -/
noncomputable def gaussianWeightedPairTerm (q z : ℂ) (N r : ℕ) : ℂ :=
  gaussianBinom (q ^ 2) (2 * N) (N - (r + 1)) *
      z ^ (-(((r + 1 : ℕ) : ℤ))) * q ^ ((-(((r + 1 : ℕ) : ℤ))) ^ 2) +
    gaussianBinom (q ^ 2) (2 * N) (N + (r + 1)) *
      z ^ (((r + 1 : ℕ) : ℤ)) * q ^ ((((r + 1 : ℕ) : ℤ)) ^ 2)

/-- The first `M` Gaussian-weighted symmetric nonzero pairs from the finite JTP RHS. -/
noncomputable def gaussianWeightedPairPartial (q z : ℂ) (N M : ℕ) : ℂ :=
  ∑ r ∈ Finset.range M, gaussianWeightedPairTerm q z N r

/-- The tail of Gaussian-weighted symmetric nonzero pairs from indices `M, ..., K - 1`. -/
noncomputable def gaussianWeightedPairTail (q z : ℂ) (N M K : ℕ) : ℂ :=
  ∑ r ∈ Finset.Ico M K, gaussianWeightedPairTerm q z N r

/--
The zero-extended shifted Gaussian tail summand. For fixed lower index `M`,
the moving finite tail `M ≤ r < N` is represented by the `k`-indexed summand
with `r = M + k`, extended by zero once `M + k ≥ N`.
-/
noncomputable def gaussianWeightedTailSummand (q z : ℂ) (N M k : ℕ) : ℂ :=
  if M + k < N then
    qPoch (q ^ 2) (q ^ 2) N * gaussianWeightedPairTerm q z N (M + k)
  else
    0

/-- The centered term plus the first `M` Gaussian-weighted symmetric nonzero pairs. -/
noncomputable def gaussianWeightedSymmetricPartial (q z : ℂ) (N M : ℕ) : ℂ :=
  gaussianBinom (q ^ 2) (2 * N) N + gaussianWeightedPairPartial q z N M

/-- A single Gaussian-weighted Laurent summand after the finite-JTP substitution. -/
noncomputable def gaussianWeightedLaurentSummand (q z : ℂ) (N k : ℕ) : ℂ :=
  gaussianBinom (q ^ 2) (2 * N) k * z ^ ((k : Int) - (N : Int)) *
    q ^ (((k : Int) - (N : Int)) ^ 2)

end ComplexLimits

section FiniteJTP

open Filter
open scoped Topology

variable {R : Type*} [Field R]

/--
The `k`-indexed summand for Chan's finite Jacobi triple product.

This encodes the bilateral index `l = k - n`, with `k = 0, ..., 2n`.
Using the integer power `(-z) ^ l` keeps the negative Laurent monomials
instead of truncating negative indices through `Int.toNat`.
-/
def finiteJTPSummand (q z : R) (n k : Nat) : R :=
  let l : Int := (k : Int) - (n : Int)
  gaussianBinom q (2 * n) k *
    q ^ ((l * (l - 1) / 2).toNat) *
    (-z) ^ l

/--
The finite bilateral sum in Chan Eq (3.15), encoded as the ordinary finite
sum over `k = 0, ..., 2n` after the change of variables `l = k - n`.
-/
def finiteJTPRHS (q z : R) (n : Nat) : R :=
  natSum (fun k => finiteJTPSummand q z n k) (2 * n)

/-! ### Summand and sum identities for the finite Jacobi triple product -/

end FiniteJTP

end Ch03

end PartI
end QseriesFormalization

end

-- Source module: QseriesFormalization.Chapter04
section

/-!
# Chapter 4 — Part I: Some applications of Jacobi's triple product

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 4, pp. 21–30.)

This chapter spins off four named identities from the Jacobi triple
product (Theorem 4.1, Euler's pentagonal theorem, Theorem 4.3, the
quintuple product identity).  The Jacobi triple product is now available;
the remaining infinite applications need the specialization and rewriting
layers connecting those products and bilateral sums to Chan's displayed forms.
-/

namespace QseriesFormalization
namespace PartI
namespace Ch04

open QseriesFormalization.PartI.Ch02 (jacobiInfiniteProduct jacobiInfiniteSeries)
open QseriesFormalization.PartI.Ch03 (finiteJTPRHS)
open Filter

open scoped Topology

section Field

variable {R : Type*} [Field R]

/- The infinite Theorem 4.1 equality is now reduced to specializing JTP and
rewriting the resulting product and bilateral series into Chan's displayed form. -/

/--
The three residue-class product factor obtained in Euler's pentagonal theorem
from the JTP substitution `Q^2 = q^3`, `z = -Q/q^2`.
-/
noncomputable def eulerPentagonalCubicProductFactor (q : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (3 * (n + 1))) *
    (1 - q ^ (3 * (n + 1) - 2)) *
    (1 - q ^ (3 * (n + 1) - 1))

/-! ## Mod-5 residue factors for Rogers-Ramanujan (Ch7 dependency)

The classical R-R proof needs:
`(q;q)_∞ = ∏_{k=1..5} (q^k;q^5)_∞`.

Each factor `(q^k;q^5)_∞` = `∏'_n (1 - q^(k + 5n))` for `n ≥ 0`. -/

/-- `(q^k; q^5)_∞` truncated factor: `1 - q^k · q^(5n) = 1 - q^(k + 5n)`. -/
def rrMod5Factor (q : ℂ) (k : ℕ) (n : ℕ) : ℂ :=
  1 - q ^ (k + 5 * n)

@[simp] theorem rrMod5Factor_def (q : ℂ) (k n : ℕ) :
    rrMod5Factor q k n = 1 - q ^ (k + 5 * n) := rfl

/-! ### Rogers-Ramanujan theta series via JTP at q^5

S₁(q) := ∑'_{j : ℤ} (-1)^j · q^(j(5j+1)/2) — JTP series at Q := Y^5, z := -Y (Y² = q).
S₂(q) := ∑'_{j : ℤ} (-1)^j · q^(j(5j+3)/2) — JTP series at Q := Y^5, z := -Y^3 (Y² = q).
-/

/-- Nat-indexed Euler product factor `1 - q^(n+1)`. -/
def eulerPentagonalProductFactor (q : ℂ) (n : ℕ) : ℂ :=
  1 - q ^ (n + 1)

/-- Euler's infinite product side, Nat-indexed from exponent `1`. -/
noncomputable def eulerPentagonalInfiniteProduct (q : ℂ) : ℂ :=
  ∏' n : ℕ, eulerPentagonalProductFactor q n

/- The infinite Euler pentagonal theorem is proved above as
`eulerPentagonalInfiniteProduct_eq_tsum`. -/

/- The infinite Theorem 4.3 identity is deferred until its JTP specialization
and rewriting layer is formalized. -/

/-- Nat-indexed quintuple product factor in Chan's Eq. (2.12) form. -/
noncomputable def quintupleProductFactor (q z : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (2 * n + 2)) *
    (1 - z * q ^ (2 * n + 1)) *
    (1 - z⁻¹ * q ^ (2 * n + 1)) *
    (1 - z ^ 2 * q ^ (4 * n)) *
    (1 - z⁻¹ ^ 2 * q ^ (4 * n + 4))

/-- Infinite product side of the quintuple product identity. -/
noncomputable def quintupleProductLHS (q z : ℂ) : ℂ :=
  ∏' n : ℕ, quintupleProductFactor q z n

/--
Complex RHS summand in Jacobi-series form:
`(z^3/q^2)^n (q^3)^{n^2} - (q/z) (q^4/z^3)^n (q^3)^{n^2}`.
-/
noncomputable def quintupleProductSeriesTerm (q z : ℂ) (n : ℤ) : ℂ :=
  (z ^ 3 / q ^ 2) ^ n * (q ^ 3) ^ (n ^ 2) -
    (q / z) * ((q ^ 4 / z ^ 3) ^ n * (q ^ 3) ^ (n ^ 2))

/-- Infinite bilateral series side of the quintuple product identity. -/
noncomputable def quintupleProductRHS (q z : ℂ) : ℂ :=
  ∑' n : ℤ, quintupleProductSeriesTerm q z n

/- The infinite quintuple product identity is deferred to the JTP specialization
and rewriting layer used in Chan's proof. -/

/-! ### Finite JTP specialized at z = 1: Euler pentagonal general identity -/

end Field

/-! ### Quintuple product identity: final assembly via Tannery-style convergence

The strategy: prove both the LHS product truncation and the qPoch⁶×combinedMonomialSum
converge to `quintupleProductLHS`, then their difference → 0, closing the identity.

Key bridge: a generic "fixed-core + uniform-tail" convergence lemma. -/

section QuintupleAssembly

open scoped Topology
open Filter

/-! ### Quintuple product: uniform tail estimate for the combined monomial sum -/

/-! Dead Route B end-cap removed: the bridge to `quintupleProductRHS` is now
done entirely via Route A (JTP product decomposition) below. The upstream
`qPoch_qsix_mul_quintupleCombinedMonomial*` and `tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomial*`
infrastructure is retained in case it's useful for future routes. -/

/-! #### Route A: Product decomposition via JTP

The quintuple product factors decompose as:
  quintupleProductFactor(n) = JacobiNatFactor(q, -z, n) × JacobiNatFactor(q², -z²/q², n) / (1-q^{4n+4})

At the infinite product level:
  quintupleProductLHS = jacobiInfiniteProduct(q, -z) × jacobiInfiniteProduct(q², -z²/q²) / (q⁴;q⁴)_∞

Then JTP converts each infinite product to a bilateral series, and the product
of two series (after mod-3 regrouping) gives ExplicitRHS. -/

/-- Sub-lemma 1: Cauchy product + shear reindex + Fubini. -/
def quintupleShearEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 + 2 * p.2, p.2)
  invFun p := (p.1 - 2 * p.2, p.2)
  left_inv := fun p => by ext <;> simp <;> ring
  right_inv := fun p => by ext <;> simp <;> ring

-- Remove old final assembly that needed hqPoch_ne
-- (no longer needed since we use the finite identity route)

end QuintupleAssembly

/- Theorem 4.3 (Jacobi's identity) lives in `Chapter04_T43.lean`. -/

end Ch04
end PartI
end QseriesFormalization

end

-- Source module: QseriesFormalization.Pending.JTP_FormalPS_Pentagonal
section

/-!
# Formal power-series shells for the mod-5 JTP pentagonal specialisations

This pending file isolates the formal objects for Hirschhorn's two
mod-5 Jacobi-triple-product specialisations.  The full analytic-to-formal
coefficient bridge is not asserted here; all declarations below are fully
proved.
-/

namespace QseriesFormalization
namespace Pending
namespace JTPFormalPSPentagonal

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

/-! ## Formal AP products -/

/-- The formal factor `1 - X^(r + m n)`. -/
noncomputable def apFactorPS (R : Type*) [CommRing R] (r m n : ℕ) : R⟦X⟧ :=
  (1 : R⟦X⟧) - PowerSeries.X ^ (r + m * n)

@[simp] theorem apFactorPS_def (R : Type*) [CommRing R] (r m n : ℕ) :
    apFactorPS R r m n = (1 : R⟦X⟧) - PowerSeries.X ^ (r + m * n) := rfl

/-- The formal AP product `(q^r;q^m)_∞ = ∏_{n≥0} (1 - X^(r+mn))`. -/
noncomputable def qPochAPPS (R : Type*) [CommRing R] [TopologicalSpace R]
    (r m : ℕ) : R⟦X⟧ :=
  ∏' n : ℕ, apFactorPS R r m n

/-- `(q,q^4,q^5;q^5)_∞` as a formal power series. -/
noncomputable def pentagonalProduct014PS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 1 5 * qPochAPPS R 4 5 * qPochAPPS R 5 5

/-- `(q^2,q^3,q^5;q^5)_∞` as a formal power series. -/
noncomputable def pentagonalProduct023PS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 2 5 * qPochAPPS R 3 5 * qPochAPPS R 5 5

/-- The per-`n` triple factor for `(q,q^4,q^5;q^5)_∞`. -/
noncomputable def pentagonalTripleFactor014PS (R : Type*) [CommRing R] (n : ℕ) : R⟦X⟧ :=
  apFactorPS R 1 5 n * apFactorPS R 4 5 n * apFactorPS R 5 5 n

/-- The per-`n` triple factor for `(q^2,q^3,q^5;q^5)_∞`. -/
noncomputable def pentagonalTripleFactor023PS (R : Type*) [CommRing R] (n : ℕ) : R⟦X⟧ :=
  apFactorPS R 2 5 n * apFactorPS R 3 5 n * apFactorPS R 5 5 n

/-! ## Formal bilateral series coefficients -/

/-- The integer exponent `(5k² - 3k)/2`, coerced to `Nat`. -/
def pentagonal014Exp (k : ℤ) : ℕ :=
  (k * (5 * k - 3) / 2).toNat

/-- The integer exponent `(5k² - k)/2`, coerced to `Nat`. -/
def pentagonal023Exp (k : ℤ) : ℕ :=
  (k * (5 * k - 1) / 2).toNat

/-- The sign `(-1)^k`, represented over an arbitrary commutative ring. -/
def negOnePowInt (R : Type*) [CommRing R] (k : ℤ) : R :=
  (-1 : R) ^ k.natAbs

/-- Coefficient of `X^n` in the first bilateral pentagonal AP series. -/
noncomputable def pentagonal014Coeff (R : Type*) [CommRing R] (n : ℕ) : R :=
  ∑ k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ),
    if pentagonal014Exp k = n then negOnePowInt R k else 0

/-- Coefficient of `X^n` in the second bilateral pentagonal AP series. -/
noncomputable def pentagonal023Coeff (R : Type*) [CommRing R] (n : ℕ) : R :=
  ∑ k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ),
    if pentagonal023Exp k = n then negOnePowInt R k else 0

/-- Formal series `∑_{k∈ℤ} (-1)^k X^((5k²-3k)/2)`. -/
noncomputable def pentagonal014SeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk (pentagonal014Coeff R)

/-- Formal series `∑_{k∈ℤ} (-1)^k X^((5k²-k)/2)`. -/
noncomputable def pentagonal023SeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk (pentagonal023Coeff R)

/-! ## Bilateral theta analytic-to-formal bridge -/

noncomputable def pentagonal014ThetaTerm (q : ℂ) (k : ℤ) : ℂ :=
  negOnePowInt ℂ k * q ^ pentagonal014Exp k

noncomputable def pentagonal023ThetaTerm (q : ℂ) (k : ℤ) : ℂ :=
  negOnePowInt ℂ k * q ^ pentagonal023Exp k

noncomputable def pentagonal014ThetaNat (q : ℂ) : ℂ :=
  ∑' k : ℤ, pentagonal014ThetaTerm q k

noncomputable def pentagonal023ThetaNat (q : ℂ) : ℂ :=
  ∑' k : ℤ, pentagonal023ThetaTerm q k

noncomputable def pentagonal014Analytic (q : ℂ) : ℂ :=
  ∑' k : ℤ, (-1 : ℂ) ^ k * q ^ (k * (5 * k - 3) / 2)

noncomputable def pentagonal023Analytic (q : ℂ) : ℂ :=
  ∑' k : ℤ, (-1 : ℂ) ^ k * q ^ (k * (5 * k - 1) / 2)

noncomputable def pentagonal014SeriesFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (pentagonal014Coeff ℂ)

noncomputable def pentagonal023SeriesFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (pentagonal023Coeff ℂ)

/-! ## Analytic identities already closed in Chapter 4, in target exponent orientation -/

/-! ## Product-side analytic functions, with the puncture at `q = 0` filled -/

/-- The analytic product `(q,q^4,q^5;q^5)_∞`. -/
noncomputable def pentagonal014ProductAnalytic (q : ℂ) : ℂ :=
  (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 5 n) *
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 4 n) *
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 1 n)

/-- The analytic product `(q^2,q^3,q^5;q^5)_∞`. -/
noncomputable def pentagonal023ProductAnalytic (q : ℂ) : ℂ :=
  (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 5 n) *
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 3 n) *
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 2 n)

/-! ## Final uniqueness step, conditional on the product-coefficient Taylor bridge -/

noncomputable def pentagonal014ProductCoeffFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (pentagonalProduct014PS ℂ).coeff n)

noncomputable def pentagonal023ProductCoeffFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (pentagonalProduct023PS ℂ).coeff n)

/-! ### Product-coefficient finite partial bridges -/

end JTPFormalPSPentagonal
end Pending
end QseriesFormalization

end


