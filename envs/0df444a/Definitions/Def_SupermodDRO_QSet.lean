-- Prove2me | Definitions.Def_SupermodDRO_QSet
-- name    : SupermodDRO_QSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:54.463301+00:00
-- url     : https://prove2.me/theorems/9fd4637c-6bce-4a13-801c-176d617be6ea
-- title:
--   Polyhedron $\mathcal Q$ of scenario probabilities
-- statement:
--   For $R\in\mathbb R^{s\times K}$ and $\nu\in\mathbb R^s$,
--   $$
--   \mathcal Q=\{q\in\mathbb R^K \;:\; Rq\le\nu,\ q\ge0\}.
--   $$
--   It is the set of admissible probability vectors of the random scenario $\tilde k$.
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), §2.1, p.7

import Mathlib

open Matrix

namespace SupermodDRO

/-- **The polyhedron `𝒬` of scenario probabilities.** Long, Qi & Zhang, *Supermodularity in
Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022), §2.1, p.7: "q is in
a given polyhedron 𝒬 = {q | Rq ≤ ν, q ≥ 0}". Here `R` has `s` rows and `K` columns (`s` is left
unnamed in the paper). -/
def QSet {s K : ℕ} (R : Matrix (Fin s) (Fin K) ℝ) (ν : Fin s → ℝ) : Set (Fin K → ℝ) :=
  {q | R *ᵥ q ≤ ν ∧ 0 ≤ q}

end SupermodDRO


