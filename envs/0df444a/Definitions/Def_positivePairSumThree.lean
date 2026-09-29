-- Prove2me | Definitions.Def_positivePairSumThree
-- name    : positivePairSumThree
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-09T08:54:51.851233+00:00
-- url     : https://prove2.me/theorems/7d12b9df-475f-4bb2-8e8c-ddf9cea77f9b
-- title:
--   Positive geometric pair support at sum three
-- statement:
--   Let A₁ and A₂ be independent positive geometric variables. This package records the two support vectors (1,2) and (2,1) and the event A₁ + A₂ = 3, together with positivity. It contains definitions only; the event mass and conditional-average identities are separate theorems.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Section 7.1, the b=3 conditional pair calculation, https://arxiv.org/html/1909.03562v7.

import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

open scoped BigOperators

def positivePair12 : Fin 2 → ℕ := ![1, 2]

def positivePair21 : Fin 2 → ℕ := ![2, 1]

def positivePairSumThree : Finset (Fin 2 → ℕ) :=
  {positivePair12, positivePair21}

def positivePairSumThreeEvent : Set (Fin 2 → ℕ) :=
  {a | (∀ i, 0 < a i) ∧ ∑ i, a i = 3}


