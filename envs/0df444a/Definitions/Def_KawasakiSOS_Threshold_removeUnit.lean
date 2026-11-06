-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_removeUnit
-- name    : KawasakiSOS_Threshold_removeUnit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:26.247333+00:00
-- url     : https://prove2.me/theorems/fd339ea6-2514-4f40-a9dc-7a212fb08e34
-- title:
--   The vector $z-e_i$
-- statement:
--   For a height vector $z$ with $z(i)\ge1$, this is the vector $z-e_i$, with one unit removed from column $i$.
--
--   **Formalization Note** The subtraction is on natural numbers, so the definition is only used when $z(i)\ge1$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 6 (PDF p. 7)

import Mathlib

namespace KawasakiSOS.Threshold

/-- The vector `z − e_i` of Lemma 2.2, of total mass `n − 1`. Formalization Note: natural subtraction, used only under the hypothesis `z(i) ≥ 1`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 6 (PDF p. 7). -/
def removeUnit {k : ℕ} (z : ZMod k → ℕ) (i : ZMod k) : ZMod k → ℕ :=
  fun l => z l - if l = i then 1 else 0

end KawasakiSOS.Threshold


