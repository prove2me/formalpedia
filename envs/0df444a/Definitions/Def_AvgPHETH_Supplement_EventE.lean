-- Prove2me | Definitions.Def_AvgPHETH_Supplement_EventE
-- name    : AvgPHETH_Supplement_EventE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:57:37.85736+00:00
-- url     : https://prove2.me/theorems/46f6522c-e3d0-43d5-9199-8c67241bd9ff
-- title:
--   The event $E_{k,n}$
-- statement:
--   $E_{k,n}$ is the event that, after $J_k(n)$ restriction rounds, there exists some $x\in\{0,1\}^n$ such that $B^k_x$ is unset and $T^k_x$ has a complete subtree with arity $2^{a_k(n)}$ which has all selectors unset.
--
--   On this event a hard formula of Theorem 7.1 can be embedded into the still undetermined part of $T^k_x$. Lemma 8.2 shows $\Pr[E_{k,n}]=1-o(1)$ for every fixed $k$.
--
--   **Formalization Note** The event is a property of the seeds of the restriction rounds only; "all selectors" includes the root selector $S^k_x$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "The construction", p.40 (PDF 42)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_rawRestr
import Definitions.Def_AvgPHETH_Supplement_HasUnsetSubtree
import Definitions.Def_AvgPHETH_Supplement_JPar

namespace AvgPHETH.Supplement

/-- The event `E_{k,n}` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, p.40 (PDF 42)): "after `J_k(n)` such restrictions
there exists some `x ∈ {0,1}^n` such that `B^k_x` is unset and `T^k_x` has a complete subtree with arity
`2^{a_k(n)}` which has all selectors unset."

**Formalization Note** The event is a property of the seeds `U` of the restriction rounds; it does not
depend on the reserved lengths `n_s`, whose choice refers to its probability. "All selectors" includes
the root selector `S^k_x` (proof of Lemma 8.2, p.42 (PDF 44)). -/
def EventE (ε : ℕ → ℝ) (U : ℕ → CVar → ℕ → ℝ) (k n : ℕ) : Prop :=
  ∃ x : List Bool, x.length = n ∧ rawRestr ε U (JPar ε k n) ⟨k, x, true, []⟩ = none ∧
    HasUnsetSubtree ε (rawRestr ε U (JPar ε k n)) k x k []

end AvgPHETH.Supplement


