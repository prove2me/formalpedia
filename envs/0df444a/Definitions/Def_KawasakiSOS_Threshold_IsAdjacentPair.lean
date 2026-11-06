-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsAdjacentPair
-- name    : KawasakiSOS_Threshold_IsAdjacentPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:28.150786+00:00
-- url     : https://prove2.me/theorems/950bbf6c-8975-4e7b-97b5-af080bec5a34
-- title:
--   Consecutive site pairs
-- statement:
--   Two site pairs are consecutive if they differ by $\pm1$ in exactly one coordinate.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11)

import Mathlib

namespace KawasakiSOS.Threshold

/-- Consecutive pairs "differ by ±1 in exactly one coordinate".

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11). -/
def IsAdjacentPair (q q' : ℕ × ℕ) : Prop :=
  (q'.2 = q.2 ∧ (q'.1 = q.1 + 1 ∨ q.1 = q'.1 + 1)) ∨
    (q'.1 = q.1 ∧ (q'.2 = q.2 + 1 ∨ q.2 = q'.2 + 1))

end KawasakiSOS.Threshold


