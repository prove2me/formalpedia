-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_block
-- name    : KawasakiSOS_Threshold_block
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:55.111696+00:00
-- url     : https://prove2.me/theorems/5cf9a9f1-6db8-46c6-bc33-d4e07d3a2707
-- title:
--   A block of five consecutive sites
-- statement:
--   The block $B=\{b_0,\dots,b_4\}$ of five consecutive sites with first site $b_0=b$, where $b_t=b+t$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.10, p. 13 (PDF p. 14)

import Mathlib

namespace KawasakiSOS.Threshold

/-- The block `B = {b, b+1, b+2, b+3, b+4}` with first site `b_0 = b`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.10, p. 13 (PDF p. 14). -/
def block {k : ℕ} (b : ZMod k) : Finset (ZMod k) :=
  (Finset.range 5).image fun t : ℕ => b + (t : ZMod k)

end KawasakiSOS.Threshold


