-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_Binomial
-- name    : OAI_Probability_RandomSAT_Binomial
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:33:21.688014+00:00
-- url     : https://prove2.me/theorems/9bae4c86-81be-4966-9f7a-045051005e24
-- title:
--   Binomial expectations by recursion and the replacement difference
-- statement:
--   1. **Binomial mean.** For a real number $p$, $m\in\mathbb{N}$ and $f:\mathbb{N}\to\mathbb{R}$, the quantity $\mathcal{B}_p^mf$ is defined by the recursion
--   $$
--   \mathcal{B}_p^0f=f(0),\qquad \mathcal{B}_p^{m+1}f=(1-p)\,\mathcal{B}_p^mf+p\,\mathcal{B}_p^m\big(d\mapsto f(d+1)\big).
--   $$
--   Unwinding the recursion gives $\mathcal{B}_p^mf=\sum_{d=0}^{m}\binom md p^d(1-p)^{m-d}f(d)$. So for $0\le p\le1$ it is the expectation $\mathbb{E}[f(D)]$ for a binomial random variable $D\sim\mathrm{Bin}(m,p)$, the number of successes in $m$ independent trials with success probability $p$.
--   2. **Replacement difference.** For $P:\mathbb{N}\to\mathbb{R}$ and $g,j,d\in\mathbb{N}$,
--   $$
--   \Delta_P(g,j,d)=P(j-d)-P\big(j+(g-1)d\big).
--   $$
--   It compares the value of $P$ when $d$ of $j$ units are removed with its value when each of those $d$ units is replaced by $g$ units.
--
--   In the random $k$-SAT argument, the number of random clauses that contain a distinguished variable is binomial, and each such clause is traded for a block of $g$ fresh clauses. The binomial mean of $\Delta_P$ measures the expected cost of that trade, and these quantities enter telescoping estimates summed over the clause count $j$.
--
--   **Formalization Note** In $\Delta_P$, both $j-d$ and $g-1$ are natural-number subtractions, truncated at $0$. Only the recursion is the definition; the closed binomial sum above is an explanatory remark.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Binomial.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Binomial.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FixedClauseThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess

namespace OAI

/-!
Finite Bernoulli-count expectations and integrated telescoping estimates.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def binomialMean (p : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, f => f 0
  | m + 1, f => (1 - p) * binomialMean p m f +
      p * binomialMean p m (fun d => f (d + 1))

def replacementDifference (P : ℕ → ℝ) (g j d : ℕ) : ℝ :=
  P (j - d) - P (j + (g - 1) * d)

end

end FixedClauseThreshold

end OAI


