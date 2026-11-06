-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_windowA
-- name    : KawasakiSOS_Threshold_windowA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:52.909196+00:00
-- url     : https://prove2.me/theorems/c6cc1e46-c048-4a82-81e4-104f11f84d38
-- title:
--   The A-window $W_A(c)$
-- statement:
--   For a site $c$, the A-window at $c$ is
--
--   $$W_A(c)=\{c-1,\ c,\ c+1,\ c+2\},$$
--
--   and its interior is $\{c,c+1\}$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12)

import Mathlib

namespace KawasakiSOS.Threshold

/-- The A-window at `c`: `W_A(c) = {c−1, c, c+1, c+2}`, with interior `{c, c+1}`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12). -/
def windowA {k : ℕ} (c : ZMod k) : Finset (ZMod k) := {c - 1, c, c + 1, c + 2}

end KawasakiSOS.Threshold


