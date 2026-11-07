-- Prove2me | Definitions.Def_LaconicBarrier_coinAvg
-- name    : LaconicBarrier_coinAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:22.026695+00:00
-- url     : https://prove2.me/theorems/9937aecf-4cfb-4ae5-9636-02c5173b0f37
-- title:
--   Average over uniform coins
-- statement:
--   For $m \in \mathbb N$ and $g : \{0,1\}^m \to \mathbb R$,
--   $$
--   \mathrm{coinAvg}(m, g) = 2^{-m} \sum_{r \in \{0,1\}^m} g(r).
--   $$
--   With $g$ the indicator of an event this is the probability of the event over uniform coins.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.1, p.15 ("The probability is over the challenger and adversary coins")

import Mathlib

namespace LaconicBarrier

/-- The average of `g` over uniform coins `r ∈ {0,1}^m`, `2^{-m} ∑_r g(r)` (Jain, Mathialagan, Roy,
STOC 2027 submission (manuscript sha256 1af78662…), §4.1.1, p.15: "The probability is over the
challenger and adversary coins"). With `g` an indicator this is the probability of an event over the
coins. -/
noncomputable def coinAvg (m : ℕ) (g : (Fin m → Bool) → ℝ) : ℝ :=
  (∑ r : Fin m → Bool, g r) / 2 ^ m

end LaconicBarrier


