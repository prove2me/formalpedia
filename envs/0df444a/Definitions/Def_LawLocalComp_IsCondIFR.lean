-- Prove2me | Definitions.Def_LawLocalComp_IsCondIFR
-- name    : LawLocalComp_IsCondIFR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:12:03.194975+00:00
-- url     : https://prove2.me/theorems/ccdb8b89-0e56-46c4-8b83-062cf9b4444e
-- title:
--   Conditional-IFR lattice law
-- statement:
--   A law is **conditional IFR** if it is $X=b+\Delta K$ with rational $b\ge0$, $\Delta>0$ and positive rational masses on $0,\dots,h$ whose positive conditional survival ratios $S_{i+1}/S_i$ are nonincreasing, where $S_i=\mathbb P(K\ge i\mid K>0)$. Point masses are included ($h=0$) and the activity $\mathbb P(K>0)$ is arbitrary. Every lattice-log-concave law is conditional IFR (proof of Lemma 7.1, p.13).
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Corollary 8.2, p.16

import Mathlib
import Definitions.Def_LawLocalComp_IsLatticeRep
import Definitions.Def_LawLocalComp_IsIFRSeq

namespace LawLocalComp

/-- **Conditional-IFR lattice laws.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Corollary 8.2, p.16 ("finite rational lattice laws whose positive conditional survival ratios
Si+1/Si are nonincreasing, without pmf log-concavity. Masses on 0, . . . , h are positive; point
masses are separate, and offsets, spacings and activity may vary").

`IsCondIFR X`: `X = b + ΔK` for rational `b ≥ 0`, `Δ > 0` and positive rational masses on `0, …, h`
whose conditional survival ratios are nonincreasing. Point masses are the case `h = 0`. -/
def IsCondIFR (X : Law) : Prop :=
  ∃ (b Δ : ℚ) (h : ℕ) (p : ℕ → ℚ), IsLatticeRep X b Δ h p ∧ IsIFRSeq h p

end LawLocalComp


