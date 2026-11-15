-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_PatternFarness
-- name    : StreamTesting_Bipartiteness_Supplement_PatternFarness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:01:16.128434+00:00
-- url     : https://prove2.me/theorems/49d40820-9130-4083-9cb0-afbbf358b69c
-- title:
--   Coordinate-change farness from 132-freeness
-- statement:
--   A real sequence $f$ of length $n$ is $\varepsilon$-far from 132-free if every 132-free real sequence $g$ of the same length satisfies
--
--   $$\#\{i:f(i)\ne g(i)\}\ge\varepsilon n.$$
--
--   This is the universal form of the attained minimum number of coordinate changes. Constant sequences are feasible targets, so the minimum is finite and attained among the integers $0,\ldots,n$. There is no distinct-values or permutation surrogate.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §1.2, printed/PDF p.5; §6, printed/PDF pp.29–36.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_Pattern132

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def Far132 {n : ℕ} (f : Fin n → ℝ) (ε : ℝ) : Prop := by
  classical
  exact ∀ g : Fin n → ℝ, Free132 g →
    ε * (n : ℝ) ≤ ((Finset.univ.filter fun i => f i ≠ g i).card : ℝ)

end StreamTesting.Bipartiteness.Supplement


