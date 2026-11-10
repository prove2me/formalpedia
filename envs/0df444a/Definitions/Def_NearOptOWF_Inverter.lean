-- Prove2me | Definitions.Def_NearOptOWF_Inverter
-- name    : NearOptOWF_Inverter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:10.191504+00:00
-- url     : https://prove2.me/theorems/b9889de9-a4a6-4db4-bfee-c4a293ca83a0
-- title:
--   Randomized algorithm on a tuple of strings
-- statement:
--   A **randomized algorithm** reading a tuple of strings: on input tuple $\mathrm{inp}$ it uses $\mathrm{coins}(\ell)$ uniform coins, $\ell$ the length of the encoded input, and outputs a string. Inverters of one-way functions and the inverter $A^*$ of Claim 4.7 are such algorithms.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11 (PDF p.13); §4.1, p.13 (PDF p.15)

import Mathlib

namespace NearOptOWF

/-- A **randomized algorithm** reading a tuple of strings (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 4.1, p.11 (PDF p.13):
"PPT adversaries"; §4.1, p.13 (PDF p.15): an inverter is given a polynomial-size circuit `f` and a
string `y`): on the input tuple `inp` it uses `coins ℓ` uniform coins, `ℓ` the length of the encoded
input, and outputs `run inp r`.

**Formalization Note** A probabilistic algorithm is a deterministic function of its input and its coin
string; its running time is constrained by `Inverter.IsPPT`. -/
structure Inverter where
  /-- the number of coins, as a function of the encoded input length -/
  coins : ℕ → ℕ
  /-- the output on an input tuple and a coin string -/
  run : List (List Bool) → List Bool → List Bool

end NearOptOWF


