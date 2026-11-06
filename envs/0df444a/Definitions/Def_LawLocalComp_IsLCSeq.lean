-- Prove2me | Definitions.Def_LawLocalComp_IsLCSeq
-- name    : LawLocalComp_IsLCSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:59.614596+00:00
-- url     : https://prove2.me/theorems/05e48e6e-6b9c-421a-9bf7-5dcb235b3ad4
-- title:
--   Log-concave mass sequence
-- statement:
--   Masses $p_0,\dots,p_h$ are **log-concave** if
--   $$p_i^2\ge p_{i-1}p_{i+1}\qquad(0<i<h).$$
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2

import Mathlib

namespace LawLocalComp

/-- **A log-concave mass sequence.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("positive rational masses on consecutive 0, . . . , h satisfying p_i² ≥ p_{i−1}p_{i+1}").

`IsLCSeq h p`: `p (i−1) p (i+1) ≤ p i ^ 2` for `0 < i < h`. -/
def IsLCSeq (h : ℕ) (p : ℕ → ℚ) : Prop :=
  ∀ i : ℕ, 0 < i → i < h → p (i - 1) * p (i + 1) ≤ p i ^ 2

end LawLocalComp


