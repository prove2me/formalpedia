-- Prove2me | Definitions.Def_LawLocalComp_IsLatticeRep
-- name    : LawLocalComp_IsLatticeRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:12.533632+00:00
-- url     : https://prove2.me/theorems/09b64ade-ed04-46a9-9af3-250082b7734d
-- title:
--   Lattice law $X=b+\Delta K$
-- statement:
--   A law $X$ has the **lattice representation** $(b,\Delta,h,p)$ if $b\ge0$ and $\Delta>0$ are rational, $p_0,\dots,p_h$ are positive rationals summing to one, and
--   $$\mathbb P(X=b+i\Delta)=p_i\qquad(0\le i\le h),$$
--   i.e. $X=b+\Delta K$ with $\mathbb P(K=i)=p_i$. The case $h=0$ is the point mass at $b$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2; §7, p.13

import Mathlib
import Definitions.Def_LawLocalComp_Law

namespace LawLocalComp

/-- **A finite rational lattice law `X = b + ΔK`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("Our structured lattice laws are X = b + ∆K, with rational b ≥ 0, ∆ > 0 and positive
rational masses on consecutive 0, . . . , h"); §7, p.13 ("Write X = b + R = b + ∆K").

`IsLatticeRep X b Δ h p`: `b ≥ 0` and `Δ > 0` are rational, the rational masses `p 0, …, p h` are
positive and sum to `1`, and `X` puts mass `p i` on `b + iΔ`. `h = 0` is the point mass at `b`. -/
def IsLatticeRep (X : Law) (b Δ : ℚ) (h : ℕ) (p : ℕ → ℚ) : Prop :=
  0 ≤ b ∧ 0 < Δ ∧ (∀ i ≤ h, 0 < p i) ∧ ∑ i ∈ Finset.range (h + 1), p i = 1 ∧
    X.w = ∑ i ∈ Finset.range (h + 1), Finsupp.single ((b : ℝ) + i * (Δ : ℝ)) (p i : ℝ)

end LawLocalComp


