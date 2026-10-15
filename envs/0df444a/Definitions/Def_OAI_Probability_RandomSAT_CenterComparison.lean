-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_CenterComparison
-- name    : OAI_Probability_RandomSAT_CenterComparison
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:43:34.552285+00:00
-- url     : https://prove2.me/theorems/4f8c1cda-5ad5-4f8f-a4d7-a0d779857207
-- title:
--   Density windows, neighbor constants and regularity conditions for comparing centers
-- statement:
--   Recall the cap multiplier $L_k=2^{k+1}$, the exponent $\delta_k=(k-2)/(4k)$, the fluctuation window $W_{n,k}=n^{1-\delta_k}$, the concentration error $\mathrm{err}_{n,k}$, the sampling error $s(n,k)$, the transfer lower constant $\tau_k^-$, the normalized center $c_k(n)$, and the lower center bound $c_-=e^{-2}/16$.
--
--   1. **Density window.** $\omega_{n,k}=n^{-\delta_k}$, which equals $W_{n,k}/n$ for $n\ge1$.
--   2. **Neighbor constants.** $\nu_k=\exp(-2L_k)$ and $\nu_k^-=\nu_k\,\tau_k^-$.
--   3. **Regularity.** A size $n$ is *center-regular* for the clause size $k$ if all nine of the following conditions hold:
--   $$
--   \begin{gathered}
--   k+1\le n,\qquad 2\binom k2\le n,\qquad \mathrm{err}_{n,k}\le\tfrac12,\qquad s(n,k)\le\tfrac14,\qquad \mathrm{err}_{n,k}<\tfrac12(\tau_k^-)^2,\\
--   \mathrm{err}_{n,k}<\nu_k^-,\qquad c_-\le c_k(n),\qquad 2\,\omega_{n,k}\le c_-,\qquad L_k\le W_{n,k}.
--   \end{gathered}
--   $$
--
--   The module also records that the auxiliary satisfiability probability with zero clauses equals $1$.
--
--   These conditions collect the hypotheses used to compare centers of different sizes. The resulting comparisons, valid for all sufficiently large sizes $r,s$ when $k\ge3$, are $\min\big(c_k(r),c_k(s)\big)-4\,\omega_{\min(r,s),k}\le c_k(r+s)$ for two blocks and $c_k(s)-4\,\omega_{s,k}\le c_k(s+1)$ for neighboring sizes. For $k\ge3$ every condition is designed to hold for all sufficiently large $n$, since the error terms and $\omega_{n,k}$ tend to $0$, $W_{n,k}$ tends to infinity, and the centers are eventually at least $c_-$.
--
--   **Formalization Note** `CenterRegular k n` is a structure of type `Prop` whose nine fields are exactly the conditions above, in the order listed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/CenterComparison.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/CenterComparison.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_RandomSAT_Transfer

namespace OAI

/-!
Partition interpolation and concentration yield summable-error comparisons
for centers of two blocks and of neighboring sizes.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def densityWindow (n k : ℕ) : ℝ := (n : ℝ)^(-delta k)

def neighborFactor (k : ℕ) : ℝ := Real.exp (-2 * (capMultiplier k : ℝ))

def neighborLower (k : ℕ) : ℝ := neighborFactor k * transferLower k

@[simp] theorem auxiliaryProbability_zero (n k : ℕ) : auxiliaryProbability n k 0 = 1 := by
  simp only [auxiliaryProbability, auxiliarySurvival, Function.iterate_zero, id_eq, alive_univ]

structure CenterRegular (k n : ℕ) : Prop where
  size : k + 1 ≤ n
  repetition : 2 * repeatPairs k ≤ n
  error : concentrationError n k ≤ 1 / 2
  sampling : samplingError n k ≤ 1 / 4
  sumError : concentrationError n k < (transferLower k)^2 / 2
  neighborError : concentrationError n k < neighborLower k
  centerLower : lowerCenterBound ≤ center n k
  densitySmall : 2 * densityWindow n k ≤ lowerCenterBound
  windowLarge : (capMultiplier k : ℝ) ≤ fluctuationWindow n k

end

end FixedClauseThreshold

end OAI


