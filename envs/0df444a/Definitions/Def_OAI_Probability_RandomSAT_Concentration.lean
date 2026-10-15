-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_Concentration
-- name    : OAI_Probability_RandomSAT_Concentration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:37:01.291746+00:00
-- url     : https://prove2.me/theorems/c63abf4d-8f3f-4902-aa43-e974a6718443
-- title:
--   Capped normalized centers and concentration scales for random proper $k$-SAT
-- statement:
--   Fix the clause size $k$ and the number of variables $n$, and let $\Omega_n$ be the set of all $2^n$ assignments.
--
--   1. **Cap.** The cap multiplier is $L_k=2^{k+1}$, and the main cap is $M_{n,k}=2^{k+1}n$ clauses.
--   2. **Center.** The normalized center is
--   $$
--   c_k(n)=\frac{1}{n}\,\mathbb{E}_F\big[L_{M_{n,k}}(\Omega_n,F)\big],
--   $$
--   where $F$ is a uniformly random formula of $M_{n,k}$ proper $k$-clauses on $n$ variables and $L_M(\Omega_n,F)$ is its satisfiable lifetime, the number of $t\le M$ for which the first $t$ clauses of $F$ form a satisfiable formula. Thus $c_k(n)$ is the expected clause density (clauses per variable) up to which a random sequence of clauses stays satisfiable, capped at density $2^{k+1}$.
--   3. **Exponents, window and error.**
--   $$
--   \delta_k=\frac{k-2}{4k},\qquad \eta_k=\frac{k-2}{2k},\qquad W_{n,k}=n^{1-\delta_k},\qquad \mathrm{err}_{n,k}=V_k\,n^{-\eta_k},
--   $$
--   where $V_k=2L_k^3\,k\,(2k+L_k+2)$ is the variance constant. Here $W_{n,k}$ is the fluctuation window for the lifetime and $\mathrm{err}_{n,k}$ is the error probability in the concentration estimate.
--
--   The module also records that $\Omega_n$ is alive: it is never empty, even for $n=0$.
--
--   The threshold of the main theorem is obtained as a limit of these centers. For $k\ge3$ and $n\ge k+1$, the lifetime concentrates around $n\,c_k(n)$ within the window $W_{n,k}$ except with probability at most $\mathrm{err}_{n,k}$. For $k\ge3$ the exponents $\delta_k$ and $\eta_k$ are positive, so $W_{n,k}/n\to0$ and $\mathrm{err}_{n,k}\to0$.
--
--   **Formalization Note** The center divides by $n$ in $\mathbb{R}$, so $c_k(0)=0$. The exponents $\delta_k,\eta_k$ are computed in $\mathbb{R}$, and $n^{1-\delta_k}$ and $n^{-\eta_k}$ are real powers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Concentration.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Concentration.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Normalized capped centers and polynomial concentration of the proper-clause
satisfiability probability.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def capMultiplier (k : ℕ) : ℕ := 2^(k + 1)

def mainCap (n k : ℕ) : ℕ := capMultiplier k * n

def center (n k : ℕ) : ℝ :=
  lifetimeMean k (mainCap n k) (Finset.univ : Finset (Assignment n)) / n

def varianceConstant (k : ℕ) : ℝ :=
  2 * (capMultiplier k : ℝ)^3 * k * (2 * k + capMultiplier k + 2)

theorem alive_univ (n : ℕ) : alive (Finset.univ : Finset (Assignment n)) = 1 := by
  simp [alive]

def delta (k : ℕ) : ℝ := ((k : ℝ) - 2) / (4 * k)

def eta (k : ℕ) : ℝ := ((k : ℝ) - 2) / (2 * k)

def fluctuationWindow (n k : ℕ) : ℝ := (n : ℝ) ^ (1 - delta k)

def concentrationError (n k : ℕ) : ℝ := varianceConstant k * (n : ℝ) ^ (-eta k)

end

end FixedClauseThreshold

end OAI


