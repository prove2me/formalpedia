-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsConcentration
-- name    : KawasakiSOS_Threshold_IsConcentration
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:07.945528+00:00
-- url     : https://prove2.me/theorems/165f56aa-347e-45a4-bfe2-85495777e7ca
-- title:
--   The configuration $h^{B,t}$
-- statement:
--   For a block $B$, a site $t\in B$ and $h\in\Omega$, this says that a configuration is $h^{B,t}$: it agrees with $h$ off $B$, vanishes on $B\setminus\{t\}$, and has $h(B)$ units at $t$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.10, p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_block

namespace KawasakiSOS.Threshold

/-- `g = h^{B,t}`: `g` agrees with `h` off `B`, vanishes on `B \ {t}`, and has `h(B)` units at `t`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.10, p. 13 (PDF p. 14). -/
def IsConcentration {n k : ℕ} [NeZero k] (h : Config n k) (b t : ZMod k) (g : Config n k) : Prop :=
  (∀ i, i ∉ block b → g.1 i = h.1 i) ∧ (∀ i, i ∈ block b → i ≠ t → g.1 i = 0) ∧
    g.1 t = ∑ i ∈ block b, h.1 i

end KawasakiSOS.Threshold


