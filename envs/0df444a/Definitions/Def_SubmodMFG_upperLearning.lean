-- Prove2me | Definitions.Def_SubmodMFG_upperLearning
-- name    : SubmodMFG_upperLearning
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:02.495993+00:00
-- url     : https://prove2.me/theorems/2adc317b-d9bc-48d5-b330-81b89b2444d9
-- title:
--   The upper learning procedure $\overline\mu^n$
-- statement:
--   The **upper learning procedure** is the sequence in $L$ defined by
--   $$
--   \overline\mu^0:=\sup L,\qquad \overline\mu^n:=\sup R(\overline\mu^{n-1}),\quad n\ge1 .
--   $$
--
--   Starting from the greatest distribution, each step plays the greatest best response to the previous one. Theorem 2.6 c) shows that it decreases to the greatest equilibrium.
--
--   **Formalization Note** $\sup L$ is the top element $\top$; the value at $n+1$ is $\sup R$ of the value at $n$.
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.3, Theorem 2.6 c), p.7

import Mathlib
import Definitions.Def_SubmodMFG_bestResponse

namespace SubmodMFG

/-- **The upper learning procedure `µ̄ⁿ`.**
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, Theorem 2.6 c), p.7: "the learning procedure µ̄⁰ := sup L and
µ̄ⁿ := sup R(µ̄ⁿ⁻¹), for n ∈ ℕ".

**Formalization Note.** `sup L` is the top element `⊤` of the complete lattice `L`, and the
recursion `µ̄ⁿ := sup R(µ̄ⁿ⁻¹)` for `n ≥ 1` is written `upperLearning p J (n + 1) =
sSup (bestResponse p J (upperLearning p J n))`; `upperLearning p J n` is `µ̄ⁿ` for every `n`. -/
noncomputable def upperLearning {E L : Type*} [CompleteLattice L] (p : E → L)
    (J : E → L → ℝ) : ℕ → L
  | 0 => ⊤
  | n + 1 => sSup (bestResponse p J (upperLearning p J n))

end SubmodMFG


