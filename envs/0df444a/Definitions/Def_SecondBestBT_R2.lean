-- Prove2me | Definitions.Def_SecondBestBT_R2
-- name    : SecondBestBT_R2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:00.205989+00:00
-- url     : https://prove2.me/theorems/eae8f05a-dc9b-47a7-9e56-b55f486929b3
-- title:
--   Allocation class $R_2(W)$: pointwise monotone
-- statement:
--   $$
--   R_2(W)=\Big\{x:Z_W^2\to[0,1]\ :\ x(s,b)\le x(s,b')\ \text{for all } b<b',\ \ x(s,b)\ge x(s',b)\ \text{for all } s<s'\Big\}.
--   $$
--   Every allocation in $R_2(W)$ has monotone interim allocations under every prior pair.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 4.2, p.9

import Mathlib

namespace SecondBestBT

/-- The class `R2(W)` of pointwise-monotone allocations (Liu–Qin–Ren–Wang, arXiv:2606.03849, held
version sha256 17184930…, Section 4.2, p.9): `x : Z_W² → [0, 1]` with `x(s, b) ≤ x(s, b')` for
all `b < b'` and `x(s, b) ≥ x(s', b)` for all `s < s'`.

**Formalization Note** Entries with an index above `W` are unconstrained and unused. -/
def R2 (W : ℕ) : Set (ℕ → ℕ → ℝ) :=
  {x | (∀ s ≤ W, ∀ b ≤ W, x s b ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ s ≤ W, ∀ b b', b ≤ b' → b' ≤ W → x s b ≤ x s b') ∧
    (∀ b ≤ W, ∀ s s', s ≤ s' → s' ≤ W → x s' b ≤ x s b)}

end SecondBestBT


