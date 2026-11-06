-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_nu
-- name    : KawasakiSOS_Threshold_nu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:47.535871+00:00
-- url     : https://prove2.me/theorems/2f25114e-b81a-4dd5-8c8d-1b48d3b7f4f3
-- title:
--   The value $\nu$ at a site of $T\cup U$
-- statement:
--   For a site $u\in T\cup U$ of a stage $S$, let $\nu(u)=y(u)$ if $u\in T$ and $\nu(u)=x(u)$ if $u\in U$. This is the height of $z_{S,\xi}$ at $u$. The value $\nu'(v)$ of §4.5 is the same function for the stage $S'$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_arcT

namespace KawasakiSOS.Threshold

/-- `ν(u) = y(u)` if `u ∈ T` and `ν(u) = x(u)` if `u ∈ U` (and `ν′` is the same function for `S′`). Formalization Note: only applied to sites of `T ∪ U` of the given stage.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 12 (PDF p. 13). -/
def nu {n k : ℕ} [NeZero k] (x y : Config n k) (S : Stage k) (u : ZMod k) : ℕ :=
  if u ∈ arcT S then y.1 u else x.1 u

end KawasakiSOS.Threshold


