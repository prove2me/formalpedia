-- Prove2me | Definitions.Def_syracuseStep
-- name    : syracuseStep
-- status  : Definition
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:25:56.71435+00:00
-- url     : https://prove2.me/theorems/2d5fcb43-85b2-4d75-beb8-3e236e66eac3
-- title:
--   Accelerated (Syracuse) map $T(n) = (3n+1)/2^{v_2(3n+1)}$
-- statement:
--   The **Syracuse map**, also called the accelerated Collatz map, sends
--
--   $$T(n) = \frac{3n+1}{2^{\,v_2(3n+1)}},$$
--
--   where $v_2$ is the $2$-adic valuation, so that $T(n)$ is the odd part of $3n+1$.
--
--   On an odd input the classical Collatz map performs one ascending step $n \mapsto 3n+1$ followed by a run of halvings, and $T$ collapses that whole run into a single step: $T$ carries odd numbers to odd numbers, and its orbit is the subsequence of odd values along the Collatz orbit. This is the setting in which the quantitative theory of the problem is usually developed — the Terras–Everett stopping-time density theorem and Tao's almost-all result are both statements about $T$ rather than about the classical map — because the expected multiplicative drift per step of $T$ is $3/4 < 1$, whereas the classical map alternates between growth and contraction.
--
--   **Formalization Note.** The valuation is Mathlib's `(3 * n + 1).factorization 2` and the quotient is written with the `ordCompl` notation, so the definition is total on $\mathbb{N}$ and needs no hypothesis on $n$; the intended domain is the odd numbers, and hypotheses of oddness are carried by the theorems that use it rather than by the definition.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture#Syracuse_function; Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2 (the function T), https://websites.umich.edu/~lagarias/3x%2B1.html; Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252; Terence Tao, Almost All Orbits of the Collatz Map Attain Almost Bounded Values, Forum of Mathematics Pi 10 (2022), https://arxiv.org/abs/1909.03562

import Mathlib.Data.Nat.Factorization.Basic

open Nat

/-- One step of the accelerated (Syracuse) map: `n ↦ (3 * n + 1) / 2 ^ v₂(3 * n + 1)`, the odd
part of `3 * n + 1`.  On odd inputs this collapses the ascending step and the ensuing run of
halvings of the Collatz map into a single step. -/
def syracuseStep (n : ℕ) : ℕ := ordCompl[2] (3 * n + 1)


