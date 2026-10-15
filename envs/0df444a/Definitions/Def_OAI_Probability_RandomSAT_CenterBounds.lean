-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
-- name    : OAI_Probability_RandomSAT_CenterBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:38:20.580948+00:00
-- url     : https://prove2.me/theorems/8afa4639-eeb0-4075-95bb-27cbf26dc864
-- title:
--   Numerical constants for upper and lower bounds on the normalized centers
-- statement:
--   This module fixes three explicit constants:
--   $$
--   \beta=\frac{2}{e},\qquad \rho=\frac{e^{-2}}{4},\qquad c_-=\frac{\rho}{4}=\frac{e^{-2}}{16}.
--   $$
--
--   1. **First-moment base** $\beta=2e^{-1}$. Since $\beta<1$, it serves as the base of an exponentially small first-moment estimate $\beta^n$ for the probability that a random formula with $2^kn$ proper $k$-clauses on $n\ge k$ variables is satisfiable.
--   2. **Small density** $\rho=e^{-2}/4$, calibrated so that $e^2\rho=1/4$. For $3\le k\le n$ and clause counts $m\le\rho n$, a union bound over obstructions to a matching-type satisfiability criterion shows that a random formula is satisfiable with probability at least $1-1/n$.
--   3. **Lower center bound** $c_-=\rho/4=e^{-2}/16$, the positive lower bound for the normalized centers $c_k(n)$ for all large $n$.
--
--   The module also records that the forced variables of a single assignment are all variables.
--
--   For $k\ge3$ these constants give the eventual bounds $c_-\le c_k(n)\le2^k+1$ on the normalized centers. Keeping the centers in a fixed compact subinterval of $(0,\infty)$ is what makes the limiting threshold positive and finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/CenterBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/CenterBounds.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Finite union bounds, a matching criterion for satisfiability, and positive finite
bounds for the normalized centers.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

@[simp] theorem forcedVariables_singleton {n : ℕ} (σ : Assignment n) :
    forcedVariables ({σ} : Finset (Assignment n)) = Finset.univ := by
  ext i
  simp [forcedVariables]

def firstMomentBase : ℝ := 2 * Real.exp (-1)

def smallDensity : ℝ := Real.exp (-2) / 4

def lowerCenterBound : ℝ := smallDensity / 4

end

end FixedClauseThreshold

end OAI


