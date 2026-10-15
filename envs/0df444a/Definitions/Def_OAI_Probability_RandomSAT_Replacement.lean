-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_Replacement
-- name    : OAI_Probability_RandomSAT_Replacement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:30:23.930799+00:00
-- url     : https://prove2.me/theorems/850edb46-2ee5-42ca-ab27-c92c96feaf97
-- title:
--   Kill fraction, block unsatisfiability probability, and the scale for replacing a shorter clause
-- statement:
--   This module fixes the quantities used to compare one random proper clause of a given length with a block of independent random proper clauses of the next length. Assignments, proper clauses, satisfaction and uniform probabilities are as in the clause module.
--
--   1. **Kill fraction.** For natural numbers $b,n,r$,
--   $$
--   \kappa(b,n,r)=\frac{\binom br}{\binom nr\,2^r}.
--   $$
--   If $S$ is a nonempty set of assignments on $n$ variables with exactly $b$ forced variables, then $\binom br$ of the $\binom nr2^r$ proper $r$-clauses kill $S$. So $\kappa(b,n,r)$ is the probability that a uniformly random proper $r$-clause kills $S$: all its $r$ variables are forced and all its signs oppose the forced values. For $r=0$ the value is $\kappa(b,n,0)=1$.
--   2. **Block unsatisfiability probability.** For a set $S$ of assignments on $n$ variables and $g\in\mathbb{N}$,
--   $$
--   U_{k,g}(S)=\Pr_F\big[\text{no }\sigma\in S\text{ satisfies every clause of }F\big],
--   $$
--   where $F=(C_1,\dots,C_g)$ is a uniformly random formula of $g$ proper $k$-clauses, that is, $g$ independent uniform proper $k$-clauses.
--   3. **Replacement scale, error and block size.** For $n,k\in\mathbb{N}$,
--   $$
--   a_{n,k}=n^{1/k},\qquad \varepsilon_{n,k}=a_{n,k}^{-(k-1)},\qquad g_{n,k}=\big\lceil 2k\,n^{1/k}\big\rceil .
--   $$
--   For $n\ge1$ and $k\ge1$ the error is $\varepsilon_{n,k}=n^{-(k-1)/k}$. The block size $g_{n,k}$ is the number of independent proper $k$-clauses that stand in for one proper $(k-1)$-clause, and $\varepsilon_{n,k}$ is the additive error allowed in that replacement.
--
--   Erasing the literal of one variable from a clause of length $k$ leaves a clause of length $k-1$, which is much more likely to kill a solution set. These definitions quantify the statement that, up to the error $\varepsilon_{n,k}$, such a shorter clause is no more likely to kill a solution set than a block of $g_{n,k}$ fresh full-length clauses, uniformly over the solution set.
--
--   **Formalization Note** `killFraction` uses real division, so it equals $0$ when $r>n$ (zero denominator). The power $n^{1/k}$ is the real power with $1/k$ computed in $\mathbb{R}$, so it equals $1$ for $k=0$. The exponent $k-1$ in `replacementError` is natural-number subtraction, and `replacementBlock` is the natural-number ceiling.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Replacement.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Replacement.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FixedClauseThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses

namespace OAI

/-!
Quantitative comparison of a shorter clause with a block of independent proper
clauses, uniformly over the background solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def killFraction (b n r : ℕ) : ℝ := (b.choose r : ℝ) / ((n.choose r : ℝ) * 2 ^ r)

@[simp] theorem killFraction_zero (b n : ℕ) : killFraction b n 0 = 1 := by
  simp [killFraction]

def blockUNSATProbability {n : ℕ} (k g : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformProbability (fun F : Formula n k g =>
    ¬ ∃ σ ∈ S, Satisfies σ F)

def replacementScale (n k : ℕ) : ℝ := (n : ℝ) ^ (1 / (k : ℝ))

def replacementError (n k : ℕ) : ℝ := (replacementScale n k)⁻¹ ^ (k - 1)

def replacementBlock (n k : ℕ) : ℕ := ⌈2 * (k : ℝ) * replacementScale n k⌉₊

end

end FixedClauseThreshold

end OAI


