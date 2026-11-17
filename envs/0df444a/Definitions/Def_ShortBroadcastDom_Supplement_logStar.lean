-- Prove2me | Definitions.Def_ShortBroadcastDom_Supplement_logStar
-- name    : ShortBroadcastDom_Supplement_logStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:38:34.41743+00:00
-- url     : https://prove2.me/theorems/0b40f5cc-1efd-40f4-a411-c792877d2cb3
-- title:
--   The iterated binary logarithm $\log^* n$
-- statement:
--   For a natural number $n$, the **iterated binary logarithm** $\log^* n$ is the least $k\ge0$ such that applying the integer binary logarithm $m\mapsto\lfloor\log_2 m\rfloor$ exactly $k$ times sends $n$ to a value at most one:
--
--   $$
--   \log^*n=\min\{k\in\mathbb N:(\lfloor\log_2\rfloor)^{\circ k}(n)\le1\}.
--   $$
--
--   Thus $\log^*0=\log^*1=0$, $\log^*2=\log^*3=1$, and $\log^*4=2$. This is the slowly growing function in the deterministic round bound of Theorem D.
--
--   **Formalization Note** One iteration is Mathlib's `Nat.log 2`. Repeated integer binary logarithms strictly decrease above one, so the defining set is always nonempty.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §1.3, p.4 (PDF p.7), Theorem D; proof §8, pp.49–50 (PDF pp.52–53)

import Mathlib

namespace ShortBroadcastDom.Supplement

/-- **The iterated binary logarithm `log* n`** used in the round bound of Theorem D: the least
number of applications of the integer binary logarithm that sends `n` to a value at most one.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), Theorem D, §1.3, p.4 (PDF 7), and §8, pp.49–50 (PDF 52–53): the deterministic scheme
uses `O(log* n)` rounds.

**Formalization Note** One iteration is Mathlib's `Nat.log 2`, i.e. `⌊log₂ n⌋`; thus
`logStar 0 = logStar 1 = 0`, `logStar 2 = logStar 3 = 1`, and `logStar 4 = 2`. The defining set
is nonempty for every natural number because repeated integer binary logarithms strictly decrease
above one. This is deliberately not the published `PredAdvice.logStar`, which iterates the real
binary logarithm and already differs at `n = 3`. -/
noncomputable def logStar (n : ℕ) : ℕ :=
  sInf {k : ℕ | (Nat.log 2)^[k] n ≤ 1}

end ShortBroadcastDom.Supplement


