-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsAdmissiblePair
-- name    : KawasakiSOS_Threshold_IsAdmissiblePair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:03:31.993831+00:00
-- url     : https://prove2.me/theorems/7e51b915-ee03-4c12-9924-a25da3ad5c96
-- title:
--   Admissible site pairs
-- statement:
--   A site pair $(s_a,s_b)$ with $0\le s_a\le s_b\le k-1$, in lifted coordinates, is admissible if there exist
--
--   $$a\in[s_a,s_a+1],\qquad b\in[s_b,s_b+1]\qquad\text{with}\qquad F(a)=F(b).$$
--
--   Such pairs record the sites containing two climbers at equal height on the profile $F$.
--
--   **Formalization Note** The source's site pairs come from climbers with $a\le m\le b$, so they satisfy $s_a\le s_b$. The definition includes this.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_liftF

namespace KawasakiSOS.Threshold

/-- `(s_a, s_b)` is an admissible pair: there are `a ∈ [s_a, s_a+1]`, `b ∈ [s_b, s_b+1]` with `F(a) = F(b)`. Formalization Note: `s_a`, `s_b` are lifted coordinates in `{0, …, k−1}`. Site pairs on the page record climbers with `a ≤ m ≤ b`, so `s_a ≤ s_b`, and this is part of the definition.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 10 (PDF p. 11). -/
def IsAdmissiblePair {n k : ℕ} [NeZero k] (x y : Config n k) (p0 : ZMod k) (sa sb : ℕ) : Prop :=
  sa ≤ sb ∧ sb ≤ k - 1 ∧ ∃ a ∈ Set.Icc (sa : ℝ) (sa + 1), ∃ b ∈ Set.Icc (sb : ℝ) (sb + 1),
    liftF x y p0 a = liftF x y p0 b

end KawasakiSOS.Threshold


