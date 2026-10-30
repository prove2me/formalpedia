-- Prove2me | Definitions.Def_SubsamplingSM_Offline_IsLinearSetFn
-- name    : SubsamplingSM_Offline_IsLinearSetFn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:47:01.978083+00:00
-- url     : https://prove2.me/theorems/7706efe2-34ad-49fb-8a8d-d346f99ad3ff
-- title:
--   Linear set function
-- statement:
--   A set function $f:2^N\to\mathbb R$ is **linear** if inequality (1) holds with equality:
--   $$f(A\cup\{e\})-f(A)=f(B\cup\{e\})-f(B)\qquad\text{for all } A\subseteq B\subseteq N \text{ and } e\notin B.$$
--
--   Equivalently $f(S)=f(\emptyset)+\sum_{e\in S}f(e\mid\emptyset)$, so a linear function in this sense is affine; $f(\emptyset)$ need not vanish. Linear objectives get the ratio $p$ in Theorem 1, with sampling probability $q=1/p$.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, §3, p. 5

import Mathlib

namespace SubsamplingSM.Offline

/-- **Linear set function.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, §3, p. 5 (unnumbered): "A function f is linear if (1) holds with equality for all
`A ⊆ B` and `e ∉ B`."

`IsLinearSetFn f` is inequality (1) of `IsSubmodular` with `=`.

**Formalization Note.** As on the page, `f ∅ = 0` is **not** required: a linear function in
this sense is affine, `f(S) = f(∅) + Σ_{e ∈ S} f(e | ∅)`. -/
def IsLinearSetFn {α : Type*} [DecidableEq α] (f : Finset α → ℝ) : Prop :=
  ∀ A B : Finset α, ∀ e : α, A ⊆ B → e ∉ B →
    f (insert e B) - f B = f (insert e A) - f A

end SubsamplingSM.Offline


