-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsSlideRealization
-- name    : KawasakiSOS_Threshold_IsSlideRealization
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:06:07.73401+00:00
-- url     : https://prove2.me/theorems/da4d8989-112c-434c-b505-99fc6cb06aac
-- title:
--   The realization of a slide
-- statement:
--   A list of states is the realization of the slide $S\to S'$ if it is the walk that starts at $z_{S,\xi}$, performs the teleports (S1), (S2), (S3), and ends at $z_{S',\xi'}$, where each teleport is expanded into its walk along a shorter arc.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_windows
import Definitions.Def_KawasakiSOS_Threshold_IsZState
import Definitions.Def_KawasakiSOS_Threshold_nextReservoir
import Definitions.Def_KawasakiSOS_Threshold_slideOps
import Definitions.Def_KawasakiSOS_Threshold_IsTeleportRun

namespace KawasakiSOS.Threshold

/-- `l` is the walk of steps (S1), (S2), (S3) from `z_{S,ξ}` to `z_{S′,ξ′}`, each teleport expanded by Lemma 2.2.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 12 (PDF p. 13). -/
def IsSlideRealization {n k : ℕ} [NeZero k] (x y : Config n k) (S S' : Stage k) (ξ ξ' : ZMod k)
    (l : List (Config n k)) : Prop :=
  ∃ (u v : ZMod k) (z z' : Config n k),
    windows S' \ windows S = {u} ∧ windows S \ windows S' = {v} ∧
    IsZState x y S ξ z ∧ IsZState x y S' ξ' z' ∧ ξ' = nextReservoir S' ξ ∧
    IsTeleportRun z (slideOps x y S S' u v ξ ξ') z' l

end KawasakiSOS.Threshold


