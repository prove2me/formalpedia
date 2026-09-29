-- Prove2me | Definitions.Def_Sieve_SelbergBounds_defs
-- name    : Sieve_SelbergBounds_defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-07-29T14:47:11.389412+00:00
-- url     : https://prove2.me/theorems/ed168790-395d-4ba5-8b31-74e6d5927ae3
-- title:
--   Bounds for the Selberg bounding sum: complete multiplicativity and squarefree products of distinct primes
-- statement:
--   This bundle provides the definitions and squarefreeness facts needed to bound the Selberg bounding sum $S = \sum_{l \mid P,\ l^2 \le y} g(l)$ from below and to control the sieve remainder term.
--
--   **Main definitions and statements.**
--
--   - `CompletelyMultiplicative f` — the predicate that an arithmetic function $f : \mathbb{N} \to \mathbb{R}$ satisfies $f(1) = 1$ and $f(ab) = f(a)f(b)$ for all $a, b$ (no coprimality restriction). Complete multiplicativity of the sieve density $\nu$ is the hypothesis under which the bounding sum can be compared with a full sum over integers, $S \ge \sum_{n \le \sqrt{y}} \nu(n)$.
--
--   - `prodDistinctPrimes_squarefree` — for any finite set $s$ of primes, the product $\prod_{p \in s} p$ is squarefree.
--
--   - `primorial_squarefree` — the primorial $n\# = \prod_{p \le n} p$ is squarefree; this justifies using the primorial as the sifting modulus $P$ in concrete sieve instances.
--
--   **Downstream use.** The file's headline bounds (`selbergBoundingSum_ge_sum_div`, `boundingSum_ge_log`: for $\nu(n) = 1/n$ one gets $S \ge \tfrac{1}{2}\log y$, and `rem_sum_le_of_const`: bounded remainders give an error at most $C\,y\,(1 + \log y)^3$) turn the abstract Selberg upper bound $X/S + \text{remainder}$ into the explicit Brun–Titchmarsh inequality for primes in short intervals.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/SelbergBounds.lean (definitions vendored from this file)

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.SelbergSieve
import Definitions.Def_Sieve_AuxResults_defs
import Definitions.Def_Sieve_Basic_defs
import Definitions.Def_Sieve_Selberg_defs
/-!
# Bounds for the Selberg sieve
This file proves a number of results to help bound `Sieve.selbergSum`

## Main Results
* `selbergBoundingSum_ge_sum_div`: If `ν` is completely multiplicative then `S ≥ ∑_{n ≤ √y}, ν n`
* `boundingSum_ge_log`: If `ν n = 1 / n` then `S ≥ log y / 2`
* `rem_sum_le_of_const`: If `R_d ≤ C` then the error term is at most `C * y * (1 + log y)^3`
-/

set_option lang.lemmaCmd true

open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve

noncomputable section
namespace Sieve

lemma prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [←Finset.mul_prod_erase (a:=p) (h := hps), mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)]
      at h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1.1 <| symm <| (Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2
  · have : p ∣ ∏ p ∈ s, p := Trans.trans (dvd_mul_right p p) h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd this
    have heq : p = q := by
      rw [←Nat.prime_dvd_prime_iff_eq hp (h q hq.1)]
      exact hq.2
    rw [heq] at hps; exact hps hq.1

lemma primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter];
  exact fun _ h => h.2


def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b

namespace CompletelyMultiplicative
open ArithmeticFunction


end CompletelyMultiplicative


/-
Proposed generalisation :

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve)
    (hnu : CompletelyMultiplicative s.nuDivSelf) (hnu_nonneg : ∀ n, 0 ≤ s.nuDivSelf n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nuDivSelf p < 1):
    s.selbergBoundingSum ≥ ∑ m in
      (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∣ s.prodPrimes),
      s.nu m
-/


open ArithmeticFunction


end Sieve
end


