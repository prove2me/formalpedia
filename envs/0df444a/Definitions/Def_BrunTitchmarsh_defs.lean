-- Prove2me | Definitions.Def_BrunTitchmarsh_defs
-- name    : BrunTitchmarsh_defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-07-29T14:48:23.022196+00:00
-- url     : https://prove2.me/theorems/c863bb45-13a6-486d-84a2-668a6c4219b0
-- title:
--   Selberg sieve setup for primes in short intervals: the interval sieve and the prime-counting function $\pi(x, x+y]$
-- statement:
--   This bundle sets up the sieve-theoretic framework used to prove the Brun–Titchmarsh theorem, bounding the number of primes in a short interval $[x, x+y]$.
--
--   **Main definitions.**
--
--   - `primeInterSieve x y z hz` — a `SelbergSieve` structure that sifts the integers of the interval $[\lceil x\rceil, \lfloor x+y\rfloor]$ by the primes $p \le z$. Its data are: support $= \{n \in \mathbb{N} : x \le n \le x+y\}$, sifting range encoded by the squarefree modulus $P(z) = \prod_{p \le z} p$ (the primorial), unit weights $a_n = 1$, total mass $X = y$, sieve density $\nu(d) = 1/d$ (the completely multiplicative function $d \mapsto 1/d$, realized as $\zeta/\mathrm{id}$ on arithmetic functions), and level $z$. The structure fields verify the standard sieve axioms: $\nu$ is multiplicative, $0 < \nu(p) < 1$ for every prime $p \mid P(z)$.
--
--   - `primesBetween a b` — the counting function $\pi(a,b) = \#\{p \text{ prime} : a \le p \le b\}$, defined as the cardinality of the primes in $[\lceil a\rceil, \lfloor b\rfloor]$.
--
--   **Downstream use.** Applying the Selberg sieve upper bound to `primeInterSieve` yields the Brun–Titchmarsh inequality $\pi(x, x+y] \ll y/\log y$ (with explicit constants), which in turn feeds into Chebyshev-type bounds and the prime number theorem development in the PNT+ project.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/BrunTitchmarsh.lean (definitions vendored from this file)

/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Primorial
import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Topology.Order.Compact
import Definitions.Def_Sieve_AuxResults_defs
import Definitions.Def_Sieve_Basic_defs
import Definitions.Def_Sieve_SelbergBounds_defs
import Definitions.Def_Sieve_Selberg_defs

open Sieve SelbergSieve BoundingSieve
open Filter Asymptotics
open scoped Nat ArithmeticFunction BigOperators ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section
namespace BrunTitchmarsh

/-- Sifting primes ≤ z from the interval [x, x+y] -/
def primeInterSieve (x y z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := Finset.Icc (Nat.ceil x) (Nat.floor (x+y))
  prodPrimes := primorial (Nat.floor z)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := y
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ ↦ by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ ↦ by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := z
  one_le_level := hz

/-- The number of primes in the interval [a, b] -/
def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter Nat.Prime |>.card

variable (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 ≤ z)


section Remainder


end Remainder


end BrunTitchmarsh


