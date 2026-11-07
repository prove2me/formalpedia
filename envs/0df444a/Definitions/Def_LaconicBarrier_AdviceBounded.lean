-- Prove2me | Definitions.Def_LaconicBarrier_AdviceBounded
-- name    : LaconicBarrier_AdviceBounded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:21.802509+00:00
-- url     : https://prove2.me/theorems/cbc8c111-097c-4293-873b-434afe405466
-- title:
--   Bounded advice
-- statement:
--   An advice mapping $F$ assigns to $(1^\lambda, x)$ a distribution on advice strings; it may be randomized and computationally unbounded. It is **bounded by $T$ on the index set $X$** if $|F(1^\lambda, x; r)| \le T(\lambda, |x|)$ for every $\lambda$, every $x \in X$ and every outcome.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.6, p.20

import Mathlib

namespace LaconicBarrier

/-- The advice mapping `F` (a possibly randomized, computationally unbounded map from `(1^λ, x)` to
a distribution on advice strings) is bounded by `T` on the index set `X` (Jain, Mathialagan, Roy,
STOC 2027 submission (manuscript sha256 1af78662…), §4.1.6, p.20: "`|F(1^λ, x; r)| ≤ T(λ, |x|)` for
every `λ`, `x ∈ X`, and choice of coins `r`"). -/
def AdviceBounded (F : ℕ → List Bool → PMF (List Bool)) (X : Set (List Bool))
    (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ (lam : ℕ), ∀ x ∈ X, ∀ z ∈ (F lam x).support, z.length ≤ T lam x.length

end LaconicBarrier


