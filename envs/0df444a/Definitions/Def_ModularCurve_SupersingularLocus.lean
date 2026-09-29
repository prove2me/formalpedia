-- Prove2me | Definitions.Def_ModularCurve_SupersingularLocus
-- name    : ModularCurve_SupersingularLocus
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/6ad316f3-4eb4-51d4-85bc-5cf1db2b3534
-- title:
--   Tabulated supersingular invariants, weights and Weierstrass models
-- statement:
--   The module records explicit finite data attached to small primes $q$, with no moduli-theoretic content asserted. `autWeight` assigns to $q : \mathbb{N}$ and $j \in \mathbb{Z}/q$ a natural number by cases: for $q = 2$ it is $12$ at $j = 0$ and $1$ otherwise; for $q = 3$ it is $6$ at $j = 0$ and $1$ otherwise; in all remaining cases it is $3$ at $j = 0$, $2$ at $j = 1728$ (the reduction of $1728$ in $\mathbb{Z}/q$) and $1$ elsewhere. Classically this is the weight $\tfrac12\#\operatorname{Aut}(E_j)$, equivalently the intended width of a crossing point; here it is just this case-defined function. The declarations `ssSetTwo`, `ssSetThree`, `ssSetFive`, `ssSetSeven`, `ssSetEleven`, `ssSetThirteen` are the explicit finite subsets $\{0\} \subset \mathbb{Z}/2$, $\{0\} \subset \mathbb{Z}/3$, $\{0\} \subset \mathbb{Z}/5$, $\{1728\} \subset \mathbb{Z}/7$, $\{0, 1728\} \subset \mathbb{Z}/11$ and $\{5\} \subset \mathbb{Z}/13$, the elements being understood as reductions; the corresponding `ssPoly*` are the monic polynomials $\prod_{a}(X - a)$ over the respective set, of degree equal to its cardinality. Finally, `ssModelA` and `ssModelB` give, for $j \in \mathbb{Z}/q$, coefficients of a short Weierstrass equation $y^2 = x^3 + Ax + B$: $(A,B) = (0,1)$ at $j = 0$, $(A,B) = (1,0)$ at $j = 1728$, and $A = 3j(1728-j)$, $B = 2j(1728-j)^2$ otherwise. `affinePointCount q A B` is the cardinality of the set of pairs $(x,y) \in (\mathbb{Z}/q)^2$ with $y^2 = x^3 + Ax + B$; only affine solutions are counted, with no point at infinity and no nonsingularity condition. Which elements are in fact supersingular, and the compatibility of these tables with the mass formula or with point-count criteria, are matters for separate results.
--
--   **Relation to Mathlib.** Mathlib has no notion of supersingular locus or supersingular polynomial, and these tables are the project's own. The Weierstrass data are bare coefficients in $\mathbb{Z}/q$ rather than a `WeierstrassCurve`, and solutions are counted by a `Finset` filter over $(\mathbb{Z}/q)^2$.
--
--   **Where it is used.** These finite tables serve as the index data for the supersingular points in the special fibre of $X_0(q)$: the set $\mathrm{SS}_q$ together with the weights supplied by `autWeight` is what the project's component-group and width-pairing constructions are instantiated on, and the case $q = 11$ feeds the Hecke action on divisors supported on the supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_SupersingularLocus.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Polynomial

def autWeight (q : ℕ) (j : ZMod q) : ℕ :=
  if q = 2 then (if j = 0 then 12 else 1)
  else if q = 3 then (if j = 0 then 6 else 1)
  else if j = 0 then 3
  else if j = 1728 then 2
  else 1

def ssSetTwo : Finset (ZMod 2) := {0}

def ssSetThree : Finset (ZMod 3) := {0}

def ssSetFive : Finset (ZMod 5) := {0}

def ssSetSeven : Finset (ZMod 7) := {1728}

def ssSetEleven : Finset (ZMod 11) := {0, 1728}

def ssSetThirteen : Finset (ZMod 13) := {5}

def ssPolyTwo : Polynomial (ZMod 2) := ∏ a ∈ ssSetTwo, (X - C a)

def ssPolyThree : Polynomial (ZMod 3) := ∏ a ∈ ssSetThree, (X - C a)

def ssPolyFive : Polynomial (ZMod 5) := ∏ a ∈ ssSetFive, (X - C a)

def ssPolySeven : Polynomial (ZMod 7) := ∏ a ∈ ssSetSeven, (X - C a)

def ssPolyEleven : Polynomial (ZMod 11) := ∏ a ∈ ssSetEleven, (X - C a)

def ssPolyThirteen : Polynomial (ZMod 13) := ∏ a ∈ ssSetThirteen, (X - C a)

def ssModelA (q : ℕ) [NeZero q] (j : ZMod q) : ZMod q :=
  if j = 0 then 0 else if j = 1728 then 1 else 3 * j * (1728 - j)

def ssModelB (q : ℕ) [NeZero q] (j : ZMod q) : ZMod q :=
  if j = 0 then 1 else if j = 1728 then 0 else 2 * j * (1728 - j) ^ 2

def affinePointCount (q : ℕ) [NeZero q] (A B : ZMod q) : ℕ :=
  (Finset.univ.filter fun p : ZMod q × ZMod q => p.2 ^ 2 = p.1 ^ 3 + A * p.1 + B).card

end ModularCurve


