-- Prove2me | Definitions.Def_SubmodMFG_lowerLearning
-- name    : SubmodMFG_lowerLearning
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:52.185033+00:00
-- url     : https://prove2.me/theorems/6b96423a-cf50-4915-9eb3-4cecb6d534db
-- title:
--   The lower learning procedure $\underline\mu^n$
-- statement:
--   The **lower learning procedure** is the sequence in $L$ defined by
--   $$
--   \underline\mu^0:=\inf L,\qquad \underline\mu^n:=\inf R(\underline\mu^{n-1}),\quad n\ge1 .
--   $$
--
--   Starting from the least distribution, each step plays the least best response to the previous one. Theorem 2.6 b) shows that it increases to the least equilibrium.
--
--   **Formalization Note** $\inf L$ is the bottom element $\bot$; the value at $n+1$ is $\inf R$ of the value at $n$.
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.3, Theorem 2.6 b), p.7

import Mathlib
import Definitions.Def_SubmodMFG_bestResponse

namespace SubmodMFG

/-- **The lower learning procedure `µ̲ⁿ`.**
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, Theorem 2.6 b), p.7: "the learning procedure µ̲⁰ := inf L and
µ̲ⁿ := inf R(µ̲ⁿ⁻¹), for n ∈ ℕ".

**Formalization Note.** `inf L` is the bottom element `⊥` of the complete lattice `L`, and the
recursion `µ̲ⁿ := inf R(µ̲ⁿ⁻¹)` for `n ≥ 1` is written `lowerLearning p J (n + 1) =
sInf (bestResponse p J (lowerLearning p J n))`; `lowerLearning p J n` is `µ̲ⁿ` for every `n`. -/
noncomputable def lowerLearning {E L : Type*} [CompleteLattice L] (p : E → L)
    (J : E → L → ℝ) : ℕ → L
  | 0 => ⊥
  | n + 1 => sInf (bestResponse p J (lowerLearning p J n))

end SubmodMFG


