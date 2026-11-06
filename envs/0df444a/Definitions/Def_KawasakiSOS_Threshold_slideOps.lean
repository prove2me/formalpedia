-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_slideOps
-- name    : KawasakiSOS_Threshold_slideOps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:03:23.919962+00:00
-- url     : https://prove2.me/theorems/7a084b1e-0096-416b-8614-62f85987e137
-- title:
--   The teleports (S1), (S2), (S3) of a slide
-- statement:
--   Let $S\to S'$ be a slide with entering site $u$ and leaving site $v$. Starting from $z_{S,\xi}$ with $\xi\in R(S)$, the path performs the following teleports:
--
--   1. (S1) the $\nu(u)$ units of $u$ are teleported, one at a time, to $\xi$;
--   2. (S2) if $\xi\notin R(S')$, the reservoir is teleported, one unit at a time, from $\xi$ to $\xi'$;
--   3. (S3) $\nu'(v)$ units are teleported, one at a time, from $\xi'$ to $v$.
--
--   **Formalization Note** At step (S2) the reservoir holds $r_z(S)+\nu(u)$ units. The integer $r_z(S)$ is converted to a natural number, which is exact on admissible stages.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), (S1)–(S3), p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_nu
import Definitions.Def_KawasakiSOS_Threshold_rz
import Definitions.Def_KawasakiSOS_Threshold_reservoirSites

namespace KawasakiSOS.Threshold

/-- The teleports realizing `S → S′`: (S1) the `ν(u)` units of `u`, one at a time, to `ξ`; (S2) if `ξ ∉ R(S′)`, the reservoir, one unit at a time, from `ξ` to `ξ′`; (S3) `ν′(v)` units, one at a time, from `ξ′` to `v`. Formalization Note: the reservoir at (S2) has mass `r_z(S) + ν(u)`; `toNat` is used under admissibility.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), (S1)–(S3), p. 12 (PDF p. 13). -/
def slideOps {n k : ℕ} [NeZero k] (x y : Config n k) (S S' : Stage k) (u v ξ ξ' : ZMod k) :
    List (ZMod k × ZMod k) :=
  List.replicate (nu x y S u) (u, ξ) ++
    (if ξ ∈ reservoirSites S' then []
      else List.replicate ((rz x y S).toNat + nu x y S u) (ξ, ξ')) ++
    List.replicate (nu x y S' v) (ξ', v)

end KawasakiSOS.Threshold


