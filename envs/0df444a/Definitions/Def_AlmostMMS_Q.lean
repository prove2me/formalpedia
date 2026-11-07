-- Prove2me | Definitions.Def_AlmostMMS_Q
-- name    : AlmostMMS_Q
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:42.41622+00:00
-- url     : https://prove2.me/theorems/b17b8223-7d47-44a2-8249-e99095b94ab2
-- title:
--   Definition 3.2, p.20 — head demands $Q$, head profiles and tail profiles
-- statement:
--   For an integer $q>0$ the possible **head demands** are
--   $$
--   Q=\Big\{\frac{q+k}{q^2} : k\in\{0,1,\dots,q^2-q\}\Big\},
--   $$
--   the multiples of $1/q^2$ from $1/q$ to $1$. A **head profile** is a finite multiset of elements of $Q$. A **tail profile** is a finite multiset of **tail demands**, positive values $\beta\le 1/q$.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Definition 3.2, p.20; display on p.32

import Mathlib

namespace AlmostMMS

open Finset

open Classical in
/-- **The set `Q` of head demand values** (Definition 3.2, p.20; display on p.32):
`Q = {(q + k)/q² : k ∈ {0, 1, …, q² - q}}`.
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…). -/
noncomputable def Q (q : ℕ) : Finset ℝ :=
  (range (q ^ 2 - q + 1)).image fun k => ((q : ℝ) + k) / (q : ℝ) ^ 2

/-- **Head profile** (Definition 3.2, p.20): a finite multiset of head demands. -/
def IsHeadProfile (q : ℕ) (π : Multiset ℝ) : Prop :=
  ∀ α ∈ π, α ∈ Q q

/-- **Tail profile** (Definition 3.2, p.20): a finite multiset of tail demands, each a positive value
`β ≤ 1/q`. -/
def IsTailProfile (q : ℕ) (ψ : Multiset ℝ) : Prop :=
  ∀ β ∈ ψ, 0 < β ∧ β ≤ 1 / (q : ℝ)

end AlmostMMS


