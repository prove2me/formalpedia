-- Prove2me | Definitions.Def_MinSumClust_coinAvg
-- name    : MinSumClust_coinAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:33.420114+00:00
-- url     : https://prove2.me/theorems/ff5b0509-f2df-42a7-b20f-2d20dbd185cf
-- title:
--   Expectation over uniform coin strings
-- statement:
--   A randomized algorithm is a deterministic machine that also reads a string of fair coins. For an instance $I$, a polynomial $p$ and a real function $g$ of coin strings,
--
--   $$\mathrm{coinAvg}(I,p,g)=2^{-N}\sum_{w\in\{0,1\}^N} g(w),\qquad N=p(|\mathrm{enc}(I)|),$$
--
--   is the exact expectation of $g$ when the coins are uniform on strings of length $p(|\mathrm{enc}(I)|)$. This is the expectation in "randomized polynomial-time approximation" (Theorem 1) and "expected cost" (Theorem 3).
--
--   **Formalization Note** One polynomial $p$ is fixed before the instance; the coin length depends only on the instance's encoding length.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Theorem 1, p.1 (PDF p.3); Theorem 3, p.4 (PDF p.6); reading of the mission (paper.md decision 4)

import Mathlib
import Definitions.Def_MinSumClust_Inst
import Definitions.Def_MinSumClust_encInst

namespace MinSumClust

/-- **Expectation over the coin strings** of a randomized algorithm.

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Theorem 1, p.1 ("randomized"), and Theorem 3, p.4
("expected cost").

`coinAvg I p g` is the exact uniform average of `g w` over all `2^N` coin strings `w` of length
`N = p(|enc I|)`.

**Formalization Note.** Randomness is a coin string read by a deterministic machine. One polynomial
`p` is fixed before the instance; on instance `I` the coins are uniform on `{0,1}^{p(|enc I|)}`. -/
noncomputable def coinAvg (I : Inst) (p : Polynomial ℕ) (g : List Bool → ℝ) : ℝ :=
  ((2 : ℝ) ^ (p.eval (encInst I).length))⁻¹ *
    ∑ w : Fin (p.eval (encInst I).length) → Bool, g (List.ofFn w)

end MinSumClust


