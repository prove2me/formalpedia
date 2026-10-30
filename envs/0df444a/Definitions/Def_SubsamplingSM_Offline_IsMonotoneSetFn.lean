-- Prove2me | Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
-- name    : SubsamplingSM_Offline_IsMonotoneSetFn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:46:46.402087+00:00
-- url     : https://prove2.me/theorems/c81d668d-e71c-4437-ac67-619c4aa1d6b2
-- title:
--   Monotone set function
-- statement:
--   A set function $f:2^N\to\mathbb R$ is **monotone** if
--   $$f(A)\le f(B)\qquad\text{for all } A\subseteq B\subseteq N.$$
--
--   Monotone submodular objectives get the improved ratio $p+1$ in Theorem 1.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, §3, p. 5

import Mathlib

namespace SubsamplingSM.Offline

/-- **Monotone set function.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, §3, p. 5 (unnumbered): "A function f is monotone if `f(A) ≤ f(B)` for all sets
`A ⊆ B`." -/
def IsMonotoneSetFn {α : Type*} (f : Finset α → ℝ) : Prop :=
  ∀ A B : Finset α, A ⊆ B → f A ≤ f B

end SubsamplingSM.Offline


