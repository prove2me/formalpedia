-- Prove2me | Definitions.Def_LawLocalComp_IsLatticeLC
-- name    : LawLocalComp_IsLatticeLC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:12:17.438326+00:00
-- url     : https://prove2.me/theorems/613c92b4-e7b3-41e4-bf09-7c0ff79f7857
-- title:
--   Lattice-log-concave law
-- statement:
--   A law is **lattice-log-concave** if it is $X=b+\Delta K$ with rational $b\ge0$, $\Delta>0$ and positive rational log-concave masses $p_0,\dots,p_h$ on $0,\dots,h$. Point masses are included ($h=0$), and offsets and spacings may vary between laws. Such laws are rational.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2

import Mathlib
import Definitions.Def_LawLocalComp_IsLatticeRep
import Definitions.Def_LawLocalComp_IsLCSeq

namespace LawLocalComp

/-- **Lattice-log-concave laws.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("Our structured lattice laws are X = b + ∆K … satisfying p_i² ≥ p_{i−1}p_{i+1}; point
masses are included. Offsets and spacings may vary between options").

`IsLatticeLC X`: `X = b + ΔK` for rational `b ≥ 0`, `Δ > 0` and positive rational log-concave masses on
`0, …, h`. Point masses are the case `h = 0`. Such laws are rational. -/
def IsLatticeLC (X : Law) : Prop :=
  ∃ (b Δ : ℚ) (h : ℕ) (p : ℕ → ℚ), IsLatticeRep X b Δ h p ∧ IsLCSeq h p

end LawLocalComp


