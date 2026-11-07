-- Prove2me | Definitions.Def_SecondBestBT_IsFullSupportOn
-- name    : SecondBestBT_IsFullSupportOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:24.0758+00:00
-- url     : https://prove2.me/theorems/f0087d2d-5bc9-45ea-8745-319adae0e411
-- title:
--   Seller prior with full support on $\{0,\dots,K\}$
-- statement:
--   A seller prior has **full support on $\{0,1,\dots,K\}$** if $f_S(s)>0$ for $s\le K$, $f_S(s)=0$ for $s>K$, and $\sum_{s=0}^K f_S(s)=1$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 4.3, p.10; Theorem 4.10, p.15

import Mathlib

namespace SecondBestBT

/-- A seller prior with full support on `{0, 1, …, K}` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held
version sha256 17184930…, Section 4.3, p.10, Theorem 4.10, p.15): masses `f_S(s) > 0` for
`s ≤ K`, `f_S(s) = 0` for `s > K`, summing to one. -/
def IsFullSupportOn (fS : ℕ → ℝ) (K : ℕ) : Prop :=
  (∀ s ≤ K, 0 < fS s) ∧ (∀ s, K < s → fS s = 0) ∧ ∑ s ∈ Finset.range (K + 1), fS s = 1

end SecondBestBT


