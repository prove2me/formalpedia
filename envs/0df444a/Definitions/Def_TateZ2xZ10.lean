-- Prove2me | Definitions.Def_TateZ2xZ10
-- name    : TateZ2xZ10
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:19.201093+00:00
-- url     : https://prove2.me/theorems/2c5f43e3-1c37-4523-8681-5a910b7a5499
-- title:
--   Rational parameter formulas for a $ℤ/2ℤ × ℤ/10ℤ$ configuration
-- statement:
--   The file defines rational functions $b(u)$ and $c(u)$ for the order-$10$ Tate family, the distinguished coordinate $x_5(u)$, an auxiliary quadratic $Q_u(X)$, and a transformed coordinate $w(u,X)$. In particular, $$b(u)=((u-1)^3(u+1))/(u(u^2-4u-1)^2),\quad c(u)=((u-1)(u+1))/(u(u^2-4u-1)).$$ These formulas are the algebraic core of the forward reduction for a $ℤ/2ℤ × ℤ/10ℤ$ torsion configuration.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
/-!
# Algebraic core for the `Z/2 × Z/10` forward direction

This file only records the rational algebra after the Tate-normal-form
reduction.  The reduction from an arbitrary elliptic curve to these explicit
parameters is deliberately left to a later layer.
-/

def b10 (u : ℚ) : ℚ :=
  ((u - 1) ^ 3 * (u + 1)) / (u * (u ^ 2 - 4 * u - 1) ^ 2)

def c10 (u : ℚ) : ℚ :=
  ((u - 1) * (u + 1)) / (u * (u ^ 2 - 4 * u - 1))

def x5_10 (u : ℚ) : ℚ :=
  -((u - 1) ^ 3 * (u + 1)) / (4 * u ^ 2 * (u ^ 2 - 4 * u - 1))

def Q10 (u X : ℚ) : ℚ :=
  4 * X ^ 2
    - (8 * (u ^ 3 - 3 * u ^ 2 - u + 1) / (u ^ 2 - 4 * u - 1) ^ 2) * X
    + 4 * (u - 1) ^ 3 * (u + 1) / (u ^ 2 - 4 * u - 1) ^ 3

def w10 (u xT : ℚ) : ℚ :=
  ((u ^ 2 - 4 * u - 1) ^ 2 * xT - (u ^ 3 - 3 * u ^ 2 - u + 1)) / 2


