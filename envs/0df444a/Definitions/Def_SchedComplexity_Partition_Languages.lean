-- Prove2me | Definitions.Def_SchedComplexity_Partition_Languages
-- name    : SchedComplexity_Partition_Languages
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T22:01:59.675977+00:00
-- url     : https://prove2.me/theorems/906b799d-0c51-4d7e-b254-80aef81df954
-- title:
--   Recognition languages of $n|2|I|C_{\max}$ and $n|2|I|\sum w_jC_j$
-- statement:
--   Following Section 2 of Brucker, Lenstra & Rinnooy Kan, an optimization problem is replaced by its recognition version: *is there a feasible schedule with value $\le y$?* for an integer threshold $y$.
--
--   1. The language of $n|2|I|C_{\max}$ consists of the binary codes of the triples $(n, (p_1,\dots,p_n), y)$ with $y\in\mathbb N$ for which some feasible schedule on two identical machines satisfies
--   $$C_j \le y \quad\text{for every job } j,$$
--   that is, $C_{\max}=\max_j C_j\le y$.
--   2. The language of $n|2|I|\sum w_jC_j$ consists of the binary codes of $(n, (p_j,w_j)_{j=1}^n, y)$ with $y\in\mathbb N$ for which some feasible schedule satisfies
--   $$\sum_{j=1}^n w_jC_j \le y.$$
--
--   The code of an instance lists the numbers $n, p_1,\dots,p_n, y$ (resp. $n, p_1, w_1, \dots, p_n, w_n, y$) in binary, each followed by a separator; it determines the instance. The number of machines is fixed to $2$ by the problem class and is not written.
--
--   These are the target languages of Theorem 3.
--
--   **Formalization Note** "$C_{\max}\le y$" is written as $C_j\le y$ for all $j$, which equals $\max_j C_j \le y$ for $n\ge1$ and is the natural reading for $n=0$; no supremum is used. The thresholds are natural numbers, as all data are.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 4, Section 2 (recognition versions) and pp. 6–7, Section 3

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_SchedComplexity_Partition_TwoMachineModel

namespace SchedComplexity.Partition

open ProjSchedTW.Complexity (BSym encNats)

/-- The code of an instance of `n|2|I|C_max` with processing times `p` and threshold `y`: the
numbers `n`, then `p_j` for `j < n`, then `y` in binary (`encNats`). The number of machines is fixed to `2` by
the problem class and is not written. The code determines `(n, p, y)`: the separators delimit the
numbers, and `n` says how many processing times follow. -/
def cmaxCode (n : ℕ) (p : Fin n → ℕ) (y : ℕ) : List BSym :=
  encNats (n :: List.ofFn p ++ [y])

/-- The recognition version of `n|2|I|C_max` (Section 2, p. 4; Section 3, pp. 6–7): codes of
instances `(n, p)` on two identical machines and thresholds `y ∈ ℕ` such that some feasible
schedule has `C_max ≤ y`, written as `C_j ≤ y` for every job `j`. -/
def cmaxLang : CookPvsNP.Lang BSym :=
  { c | ∃ (n : ℕ) (p : Fin n → ℕ) (y : ℕ),
      (∃ σ : Schedule n, σ.IsFeasible p ∧ ∀ j, σ.completion p j ≤ y) ∧ c = cmaxCode n p y }

/-- The code of an instance of `n|2|I|Σw_jC_j` with processing times `p`, weights `w` and
threshold `y`: the numbers `n`, then `p_j, w_j` for each `j < n` in increasing order, then `y` in binary
(`encNats`), job by job. The number of machines is fixed to `2` and is not written. The code
determines `(n, p, w, y)`. -/
def sumWCCode (n : ℕ) (p w : Fin n → ℕ) (y : ℕ) : List BSym :=
  encNats (n :: (List.ofFn fun j => [p j, w j]).flatten ++ [y])

/-- The recognition version of `n|2|I|Σw_jC_j`: codes of instances `(n, p, w)` on two identical
machines and thresholds `y ∈ ℕ` such that some feasible schedule has `Σ_j w_j C_j ≤ y`. -/
def sumWCLang : CookPvsNP.Lang BSym :=
  { c | ∃ (n : ℕ) (p w : Fin n → ℕ) (y : ℕ),
      (∃ σ : Schedule n, σ.IsFeasible p ∧ σ.sumWC p w ≤ y) ∧ c = sumWCCode n p w y }

end SchedComplexity.Partition


