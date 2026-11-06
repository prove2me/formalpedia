-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_nextReservoir
-- name    : KawasakiSOS_Threshold_nextReservoir
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:03:06.94342+00:00
-- url     : https://prove2.me/theorems/0958601b-8f98-40ff-bb05-11c0569a2dd1
-- title:
--   The next reservoir site $\xi'$
-- statement:
--   If $\xi\in R(S')$, put $\xi'=\xi$. Otherwise $\xi'$ is the first site in clockwise order of the interior $\{c_A',c_A'+1\}$ of $W_A'$ that is not adjacent to $\xi$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), (S2), p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_reservoirSites

namespace KawasakiSOS.Threshold

/-- The site `ξ′` of step (S2): `ξ′ = ξ` if `ξ ∈ R(S′)`; otherwise the first site in clockwise order of the interior `{c′_A, c′_A + 1}` of `W′_A` that is not adjacent to `ξ`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), (S2), p. 13 (PDF p. 14). -/
def nextReservoir {k : ℕ} (S' : Stage k) (ξ : ZMod k) : ZMod k :=
  if ξ ∈ reservoirSites S' then ξ
  else if S'.cA = ξ + 1 ∨ S'.cA = ξ - 1 then S'.cA + 1 else S'.cA

end KawasakiSOS.Threshold


