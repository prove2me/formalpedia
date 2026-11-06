-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_stageOf
-- name    : KawasakiSOS_Threshold_stageOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:39.366094+00:00
-- url     : https://prove2.me/theorems/d737bdd1-d2a6-4cb7-bee2-67143211bcca
-- title:
--   The stage of a site pair, formula (6)
-- statement:
--   Given a site pair $(s_a,s_b)$, let $D_U=s_b-s_a$ and $D_T=s_a+k-s_b$. The stage of the pair is
--
--   $$(c_A,c_B)=\begin{cases}(s_a,\ s_b)&\text{if }D_U\ge3\text{ and }D_T\ge2\quad(\text{mode I}),\\(s_a,\ s_a+3)&\text{if }D_U\le2\quad(\text{mode U}),\\(1,\ k-1)&\text{if }D_T=1\quad(\text{mode T}).\end{cases}$$
--
--   **Formalization Note** The formula is in lifted coordinates and is shifted by $p_0$ to give actual sites of $\mathbb Z_k$. For $k\ge6$ and $s_a\le s_b\le k-1$ the three cases are exhaustive and exclusive.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), (6), p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Stage

namespace KawasakiSOS.Threshold

/-- The stage of a site pair, in lifted coordinates shifted by `p0`: with `D_U = s_b − s_a` and `D_T = s_a + k − s_b`, `(s_a, s_b)` if `D_U ≥ 3` and `D_T ≥ 2` (mode I), `(s_a, s_a + 3)` if `D_U ≤ 2` (mode U), `(1, k − 1)` if `D_T = 1` (mode T). Formalization Note: the last branch is reached exactly when `D_T = 1` for pairs with `s_a ≤ s_b ≤ k − 1`, `k ≥ 6`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), (6), p. 12 (PDF p. 13). -/
def stageOf (k : ℕ) (p0 : ZMod k) (sa sb : ℕ) : Stage k :=
  if 3 ≤ sb - sa ∧ 2 ≤ sa + k - sb then ⟨p0 + (sa : ZMod k), p0 + (sb : ZMod k)⟩
  else if sb - sa ≤ 2 then ⟨p0 + (sa : ZMod k), p0 + ((sa + 3 : ℕ) : ZMod k)⟩
  else ⟨p0 + 1, p0 + ((k - 1 : ℕ) : ZMod k)⟩

end KawasakiSOS.Threshold


