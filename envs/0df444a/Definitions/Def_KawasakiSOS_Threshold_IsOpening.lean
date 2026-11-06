-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsOpening
-- name    : KawasakiSOS_Threshold_IsOpening
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:03:09.222158+00:00
-- url     : https://prove2.me/theorems/f06e7716-d4a4-4c29-a363-31a962f1ff55
-- title:
--   Openings: the teleport sequences of Lemma 4.10
-- statement:
--   For a block $B$ with first site $b_0$ and last site $b_4$, a site $t$, and $h\in\Omega$, an opening is a sequence of teleports from $h$ to $h^{B,t}$, with its realization as a walk, such that every teleport endpoint $g$ satisfies $M(g)\le M(h)$ and differs from $h$ only on $B\cup\{r,o\}$. Here $r$ is the smallest column at which $h$ is maximal and $o\in\{b_0-1,b_4+1\}$.
--
--   The closing of a canonical path is the reversal of such a walk.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.10, p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_energy
import Definitions.Def_KawasakiSOS_Threshold_block
import Definitions.Def_KawasakiSOS_Threshold_IsConcentration
import Definitions.Def_KawasakiSOS_Threshold_topColumn
import Definitions.Def_KawasakiSOS_Threshold_IsTeleportRun
import Definitions.Def_KawasakiSOS_Threshold_teleportEndpoints

namespace KawasakiSOS.Threshold

/-- `ops` is a teleport sequence from `h` to `g = h^{B,t}`, realized by `l`, such that every teleport endpoint `f` satisfies `M(f) ≤ M(h)` and differs from `h` only on `B ∪ {r, o}`, with `o ∈ {b_0 − 1, b_4 + 1}`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.10, p. 13 (PDF p. 14). -/
def IsOpening {n k : ℕ} [NeZero k] (h : Config n k) (b t o : ZMod k) (g : Config n k)
    (ops : List (ZMod k × ZMod k)) (l : List (Config n k)) : Prop :=
  (o = b - 1 ∨ o = b + 5) ∧ IsConcentration h b t g ∧ IsTeleportRun h ops g l ∧
    ∀ f ∈ teleportEndpoints h ops, energy f.1 ≤ energy h.1 ∧
      ∀ i, i ∉ block b → i ≠ topColumn h → i ≠ o → f.1 i = h.1 i

end KawasakiSOS.Threshold


