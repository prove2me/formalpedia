-- Prove2me | Definitions.Def_SecondBestBT_IsGridPMF
-- name    : SecondBestBT_IsGridPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:41.606914+00:00
-- url     : https://prove2.me/theorems/c073f5da-f05c-4036-af95-1e823d1ceba1
-- title:
--   Probability vector on the grid indices $\{0,\dots,N\}$
-- statement:
--   A **probability vector on $\{0,\dots,N\}$** is a list of masses $f(0),\dots,f(N)\ge0$ with $\sum_{i=0}^N f(i)=1$. Zero masses are allowed: every grid point is retained.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 3, p.6; Section 4.1, p.8

import Mathlib

namespace SecondBestBT

/-- A probability vector on the grid indices `{0, …, N}`: nonnegative masses `f(0), …, f(N)` that
sum to one (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Section 3, p.6,
"fS(i) = Pr[s = ti]", and `∆(Z_W)`, p.8).

**Formalization Note** Zero masses are allowed: every grid point is retained. Values `f i` for
`i > N` are not used by any notion of the mission. -/
def IsGridPMF (f : ℕ → ℝ) (N : ℕ) : Prop :=
  (∀ i, 0 ≤ f i) ∧ ∑ i ∈ Finset.range (N + 1), f i = 1

end SecondBestBT


