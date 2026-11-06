-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsTeleportRun
-- name    : KawasakiSOS_Threshold_IsTeleportRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:59.058752+00:00
-- url     : https://prove2.me/theorems/91417c0a-dbe7-4e8b-ac21-7ac44c7538a4
-- title:
--   A sequence of teleports and its realization
-- statement:
--   Paths are described as sequences of teleports $(i_1,j_1),(i_2,j_2),\dots$, each a move $z\mapsto z-e_i+e_j$ with $z(i)\ge1$ and $j\ne i$. This predicate says that such a sequence carries $z$ to $z'$, and that a given list of states is its realization, in which each teleport is expanded into the walk along a shorter arc.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 6 (PDF p. 7)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_transfer
import Definitions.Def_KawasakiSOS_Threshold_IsTeleportWalk

namespace KawasakiSOS.Threshold

/-- A sequence of teleports `ops`, each a pair (source, target), carries `z` to `z′`, and `l` is its realization: each teleport is expanded by its walk of Lemma 2.2. Paper: "From now on paths are described as sequences of teleports. Each teleport is realized by the walk of Lemma 2.2".

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 6 (PDF p. 7). -/
def IsTeleportRun {n k : ℕ} [NeZero k] :
    Config n k → List (ZMod k × ZMod k) → Config n k → List (Config n k) → Prop
  | z, [], z', l => z' = z ∧ l = [z]
  | z, (i, j) :: ops, z', l => ∃ l₁ l₂, IsTeleportWalk z i j l₁ ∧
      IsTeleportRun (transfer z i j) ops z' l₂ ∧ l = l₁ ++ l₂.tail

end KawasakiSOS.Threshold


