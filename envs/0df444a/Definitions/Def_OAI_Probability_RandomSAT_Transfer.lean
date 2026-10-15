-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_Transfer
-- name    : OAI_Probability_RandomSAT_Transfer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:41:50.538159+00:00
-- url     : https://prove2.me/theorems/2f45e628-2fe2-4196-bb74-8a4ca518c906
-- title:
--   Distinct-variable probability, repeat pairs and transfer constants between auxiliary and proper clauses
-- statement:
--   Let $L_k=2^{k+1}$ be the cap multiplier and $W_{n,k}=n^{1-\delta_k}$, with $\delta_k=(k-2)/(4k)$, the fluctuation window.
--
--   1. **Proper fraction.**
--   $$
--   \pi(n,k)=\frac{n^{\underline{k}}}{n^k}=\frac{n(n-1)\cdots(n-k+1)}{n^k},
--   $$
--   the probability that $k$ independent uniform variables from $\{0,\dots,n-1\}$ are pairwise distinct, i.e. that a uniform auxiliary $k$-clause uses no variable twice.
--   2. **Repeat pairs.** $\binom k2$, the number of pairs of positions in a $k$-clause at which a variable could repeat. It is $0$ for $k=0$.
--   3. **Transfer factor and lower constant.**
--   $$
--   \tau_k=\exp\Big(-2L_k\binom k2\Big),\qquad \tau_k^-=\frac{\tau_k}{2}.
--   $$
--   4. **Sampling error.**
--   $$
--   s(n,k)=\frac{L_k\,n}{W_{n,k}^2},
--   $$
--   which equals $L_k\,n^{2\delta_k-1}$ for $n\ge1$.
--
--   These constants control the transfer of auxiliary satisfiability probabilities to the proper-clause model. The distinct-variable probability $\pi(n,k)$ is compared with $1$ through birthday-type bounds in terms of $\binom k2$. For $k\ge3$ and $n$ large enough, the constant $\tau_k^-$ is a uniform lower bound for auxiliary satisfiability probabilities at clause counts that lie below $n\,c_k(n)$ by at least the window $W_{n,k}$, and $s(n,k)$ is the error term in the two-block version of that bound.
--
--   **Formalization Note** $n^{\underline{k}}$ is `Nat.descFactorial`, and the quotients are real divisions, so $\pi(0,k)=0$ for $k\ge1$ and $s(0,k)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Transfer.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Transfer.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FixedClauseThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
The exact probability of distinct variables, birthday bounds, and deletion and
thinning comparisons transfer auxiliary probabilities to the proper-clause law.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def properFraction (n k : ℕ) : ℝ := (n.descFactorial k : ℝ) / (n : ℝ)^k

def repeatPairs (k : ℕ) : ℝ := (k.choose 2 : ℝ)

@[simp] theorem repeatPairs_zero : repeatPairs 0 = 0 := by norm_num [repeatPairs]

def transferFactor (k : ℕ) : ℝ := Real.exp (-2 * (capMultiplier k : ℝ) * repeatPairs k)

def transferLower (k : ℕ) : ℝ := transferFactor k / 2

def samplingError (n k : ℕ) : ℝ :=
  (capMultiplier k : ℝ) * n / (fluctuationWindow n k)^2

end

end FixedClauseThreshold

end OAI


