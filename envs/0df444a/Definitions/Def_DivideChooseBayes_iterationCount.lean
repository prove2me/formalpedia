-- Prove2me | Definitions.Def_DivideChooseBayes_iterationCount
-- name    : DivideChooseBayes_iterationCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:27:48.744119+00:00
-- url     : https://prove2.me/theorems/aa28f6a1-be0f-4865-a0e0-fee18c48d5c5
-- title:
--   Number of iterations of the main loop of Algorithm 1
-- statement:
--   The main loop of Algorithm 1 runs "while $P>0$". Its number of iterations is the first $k$ with $P_k\le 0$; iterations $0,\dots,K-1$ are those with $P_k>0$.
--
--   **Formalization Note** Defined as the infimum of $\{k\in\mathbb N : P_k\le 0\}$. For $\delta>0$ the set is nonempty and $P_k$ is decreasing. For $\delta\le 0$ the loop would not terminate and the value is the default $0$; the theorems assume $\gamma>0$ and $g^D\ne 0$.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Algorithm 1, line 4, p.9

import Mathlib
import Definitions.Def_DivideChooseBayes_algP

namespace DivideChooseBayes

/-- **Number of iterations of the main loop of Algorithm 1.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Algorithm 1, line 4, p.9: "while P > 0 do".

The loop runs iterations `k = 0, 1, …` as long as `P_k > 0`; the number of iterations is the
first `k` with `P_k ≤ 0`.

**Formalization Note.** Defined as `sInf {k | P_k ≤ 0}`. For `δ > 0` this set is nonempty and
`P_k` is decreasing, so iterations `0, …, iterationCount − 1` are exactly those with `P_k > 0`. (For
`δ ≤ 0` the loop would not terminate and the `sInf` of the empty set is `0`; the theorems assume
`γ > 0` and `gᴰ ≠ 0`.) -/
noncomputable def iterationCount {ι : Type*} [Fintype ι] (gD : ι → ℝ) (γ : ℝ) : ℕ :=
  sInf {k : ℕ | algP gD γ k ≤ 0}

end DivideChooseBayes


