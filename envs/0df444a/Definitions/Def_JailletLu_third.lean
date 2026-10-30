-- Prove2me | Definitions.Def_JailletLu_third
-- name    : JailletLu_third
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:27:42.405+00:00
-- url     : https://prove2.me/theorems/9caa643b-7bba-4d42-aa2f-8deb105432fb
-- title:
--   The bracket of the third line of the §5.4 chain
-- statement:
--   For an advertiser $a$, the numerator of the third line of the competitive-ratio chain is
--   $$
--   1-e^{-f_a}+\frac1e\sum_{a_1\in A^*_a}g(f_a,m_{a,a_1})-\frac1{2e}\Big(\sum_{a_1\in A^*_a}g(f_{a_1},m_{a_1,a})\Big)^2+\frac1{2e}\sum_{a_1\in A^*_a}g(f_a,m_{a,a_1})^2,
--   $$
--   where $f_{a_1}$ for $a_1\in A^*$ uses the convention $f_{a_d}=1$. The paper bounds the competitive ratio below by the minimum over $a$ of this quantity divided by $f_a$.
--
--   **Formalization Note** The index orders $m_{a,a_1}$ and $m_{a_1,a}$ are kept as printed.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15, third line of the chain

import Mathlib
import Definitions.Def_JailletLu_fTot
import Definitions.Def_JailletLu_fStar
import Definitions.Def_JailletLu_m
import Definitions.Def_JailletLu_Astar
import Definitions.Def_JailletLu_g

namespace JailletLu

/-- **The bracket of the third line of the §5.4 chain.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15, third line of the chain:
"min_{a∈A} [1 − e^{−f_a} + (1/e) Σ_{a1∈A*_a} g(f_a, m_{a,a1}) − (1/(2e)) (Σ_{a1∈A*_a} g(f_{a1}, m_{a1,a}))²
+ (1/(2e)) Σ_{a1∈A*_a} g(f_a, m_{a,a1})²] / f_a".

`third r f ord a` is the numerator for advertiser `a` (the paper divides it by `f_a`). The index
orders `m_{a,a1}` and `m_{a1,a}` are kept as printed, and `f_{a1}` is `fStar` (with
`f_{a_d} = 1`). -/
noncomputable def third {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] (r : I → ℝ)
    (f : A → I → ℝ) (ord : I → List (Option A)) (a : A) : ℝ :=
  1 - Real.exp (-fTot f a)
    + (1 / Real.exp 1) * ∑ b ∈ Astar a, g (fTot f a) (m r f ord (some a) b)
    - (1 / (2 * Real.exp 1)) * (∑ b ∈ Astar a, g (fStar f b) (m r f ord b (some a))) ^ 2
    + (1 / (2 * Real.exp 1)) * ∑ b ∈ Astar a, g (fTot f a) (m r f ord (some a) b) ^ 2

end JailletLu


