-- Prove2me | Definitions.Def_BewleyGE_maxSet
-- name    : BewleyGE_maxSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:32:50.109979+00:00
-- url     : https://prove2.me/theorems/2e829e76-c319-44d2-a82b-722c8347ecc6
-- title:
--   The index set $W(p)$
-- statement:
--   For $p=(p_1,\dots,p_n,p_{n+1})\in\Lambda$ (with $p_{n+1}=r$), let
--   $$
--   W(p)=\{k : \zeta_k(p)=\max_{1\le i\le n+1}\zeta_i(p)\}\ \text{ if }p\in P,\qquad
--   W(p)=\{k : p_k=0\}\ \text{ if }p\in\Lambda\setminus P .
--   $$
--   It records the markets with the largest excess demand in the interior and the free goods on the boundary.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Proof of Theorem 1, p.29

import Mathlib
import Definitions.Def_BewleyGE_excessDemand

open MeasureTheory

namespace BewleyGE

open Classical in
/-- **The index set `W(p)`** of the proof of Theorem 1. Light, arXiv:1906.06810v2, Proof of
Theorem 1, p.29:
`W(p) = {k ∈ {1, …, n + 1} : ζₖ(p) = max{ζᵢ(p) : i = 1, …, n + 1}}` for `p ∈ P`, and
`W(p) = {k : pₖ = 0}` for `p ∈ Λ \ P`.

**Formalization Note.** `p = (p₁, …, pₙ, r)` is `π : Fin (n + 1) → ℝ`. For `π ∈ Λ`, `π ∈ P` iff all
coordinates are positive, which is the case split used here. "`ζₖ` equals the maximum" is
written `∀ i, ζᵢ ≤ ζₖ`. -/
noncomputable def maxSet {n : ℕ} (E : Economy n)
    (x : (Fin (n + 1) → ℝ) → ℝ → Fin n → ℝ) (g : (Fin (n + 1) → ℝ) → ℝ → ℝ)
    (μ : (Fin (n + 1) → ℝ) → Measure ℝ) (π : Fin (n + 1) → ℝ) : Set (Fin (n + 1)) :=
  if ∀ k, 0 < π k then {k | ∀ i, excessDemand E x g μ π i ≤ excessDemand E x g μ π k}
  else {k | π k = 0}

end BewleyGE


