-- Prove2me | Definitions.Def_BorelNormality_Complexity
-- name    : BorelNormality_Complexity
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T17:08:51.454203+00:00
-- url     : https://prove2.me/theorems/47d47348-2dce-4b80-9f8b-a44f17a56913
-- title:
--   Subword complexity of digit expansions
-- statement:
--   The **subword complexity** of an infinite digit sequence $s$ over the alphabet $\{0, \dots, b-1\}$ is the function $p(n)$ counting the distinct blocks of $n$ consecutive digits that occur somewhere in $s$. For a real number $x$, the complexity of its base-$b$ expansion is the complexity of its digit sequence.
--
--   This is the complexity function $p(n)$ of Adamczewski–Bugeaud (*On the complexity of algebraic numbers I*, Ann. of Math. 165 (2007), §2). A sequence normal in base $b$ satisfies $p(n) = b^n$ for every $n$; their Theorem 1 proves $\liminf_{n \to \infty} p(n)/n = +\infty$ for irrational algebraic numbers. The definition is reusable in combinatorics on words and transcendence.
--
--   **Formalization Note.** `seqComplexity` filters the finite set `Normal.strs b n` of length-$n$ words by the existence of a positive occurrence count `Normal.count s w N`; `complexity` specialises to `Normal.digit b x`. Classical decidability is used for the filter; both definitions are noncomputable.
-- source:
--   B. Adamczewski, Y. Bugeaud, On the complexity of algebraic numbers I. Expansions in integer bases, Ann. of Math. (2) 165 (2007), no. 2, 547–565, Section 2 (definition of the complexity function p(n)), https://doi.org/10.4007/annals.2007.165.547

import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false

open scoped Classical

namespace BorelNormality

/-- The subword complexity `p(n)` of a digit sequence `s` over base `b`: the number of
distinct words of length `n` over `{0, …, b-1}` that occur somewhere in `s`. -/
noncomputable def seqComplexity (b : ℕ) (s : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((Normal.strs b n).filter (fun w => ∃ N : ℕ, 0 < Normal.count s w N)).card

/-- The complexity function of the base-`b` expansion of a real number `x`. -/
noncomputable def complexity (b : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  seqComplexity b (Normal.digit b x) n

end BorelNormality


