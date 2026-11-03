-- Prove2me | Definitions.Def_WeightedCongestionBR_moveBound
-- name    : WeightedCongestionBR_moveBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:13.395407+00:00
-- url     : https://prove2.me/theorems/362c8a13-61d4-40a6-8f3b-1a34b5e13011
-- title:
--   Move bound $T(n,m,d)$ from the proof of Theorem 4
-- statement:
--   The proof of Theorem 4 bounds the number $\tau$ of best-response moves of phase $0$ by $n\alpha g(\alpha p+1)$ and of each phase $i\ge1$ by $n g(\alpha p+1)p$. Summed over the $m$ phases,
--
--   $$
--   T(n,m,d)=n\,\alpha\, g\,(\alpha p+1)+(m-1)\,n\,g\,(\alpha p+1)\,p .
--   $$
--
--   **Formalization Note** Real-valued; $m-1$ is real subtraction and the statements assume $m\ge1$.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, proof of Theorem 4, pp.18–19

import Mathlib
import Definitions.Def_WeightedCongestionBR_alphaC
import Definitions.Def_WeightedCongestionBR_pConst
import Definitions.Def_WeightedCongestionBR_gConst
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- The bound on the number of best-response moves of Algorithm 1 obtained in the proof of Theorem 4
(Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.19): phase `0` makes at most `n α g (α p + 1)` moves and each of the phases `1, …, m − 1`
at most `n g (α p + 1) p`, so
`T(n, m, d) := n α g (α p + 1) + (m − 1) n g (α p + 1) p`.

**Formalization Note** `m − 1` is real subtraction; the statements assume `1 ≤ m`. -/
noncomputable def moveBound (n m d : ℕ) : ℝ :=
  (n : ℝ) * alphaC d * gConst n d m * (alphaC d * pConst d + 1) +
    ((m : ℝ) - 1) * n * gConst n d m * (alphaC d * pConst d + 1) * pConst d

end WeightedCongestionBR


