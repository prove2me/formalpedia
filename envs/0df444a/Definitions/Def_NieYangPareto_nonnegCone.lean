-- Prove2me | Definitions.Def_NieYangPareto_nonnegCone
-- name    : NieYangPareto_nonnegCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:20.718981+00:00
-- url     : https://prove2.me/theorems/b7b916e3-f8ae-4ba7-a6e5-d703b7c6b86b
-- title:
--   The nonnegative polynomial cone $\mathscr P_d(K)$ of (2.3)
-- statement:
--   For a set $K\subseteq\mathbb R^n$ and a degree $d$, the **nonnegative polynomial cone** is
--
--   $$
--   \mathscr P_d(K):=\{p\in\mathbb R[x]_d:\ p(x)\ge0\ \ \forall x\in K\},
--   $$
--
--   where $\mathbb R[x]_d$ is the set of real polynomials of degree at most $d$. Under the pairing (2.1) it is dual to the moment cone.
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, eq. (2.3), p.5; ℝ[x]_d on p.4

import Mathlib

namespace NieYangPareto

open MvPolynomial

/-- **The nonnegative polynomial cone (2.3).** Nie–Yang, arXiv:2108.04336v2, eq. (2.3), p.5:
`𝒫_d(K) = {p ∈ ℝ[x]_d : p(x) ≥ 0 ∀ x ∈ K}`, where `ℝ[x]_d` is the set of polynomials of degree at
most `d` (§2, p.4). -/
def nonnegCone {n : ℕ} (K : Set (Fin n → ℝ)) (d : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | p.totalDegree ≤ d ∧ ∀ x ∈ K, 0 ≤ eval x p}

end NieYangPareto


