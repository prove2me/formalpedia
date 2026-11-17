-- Prove2me | Definitions.Def_ArithmeticKakeya_ak
-- name    : ArithmeticKakeya_ak
-- status  : Definition
-- author  : @Lucas
-- created : 2026-11-16T21:55:08.661446+00:00
-- url     : https://prove2.me/theorems/8899b891-204c-4545-b8ca-fefc9d1ecca3
-- title:
--   The arithmetic Kakeya statement AK(α)
-- statement:
--   `AK α` is the arithmetic Kakeya statement at exponent $\alpha$: for every $\epsilon>0$ there are $C>0$ and a finite non-empty dilate set $X\subset\mathbb Z^2$ with no element of coordinate-sum zero, such that for every finite $G\subset\mathbb Z^2$ some $\mathbf{x}\in X$ satisfies $|(1,-1)\cdot G|\le C\,|\mathbf{x}\cdot G|^{\alpha+\epsilon}$, where $\mathbf{x}\cdot G=\{x_1g_1+x_2g_2:(g_1,g_2)\in G\}$. Since $X$ is finite and non-empty and $C>0$, the $\exists\,\mathbf{x}\in X$ form is equivalent to the source's $\max_{\mathbf{x}\in X}$ form. The conjecture is $\mathrm{AK}(1)$.
-- source:
--   https://epoch.ai/frontiermath/open-problems/arithmetic-kakeya (Verifiable Set-up / Introduction)

import Mathlib

namespace ArithmeticKakeya

/-- `AK α`: for every `ε > 0` there are `C > 0` and a finite non-empty `X ⊂ ℤ²` with no
element of coordinate-sum zero, such that for every finite `G ⊂ ℤ²` some `x ∈ X` has
`|(1,-1)·G| ≤ C · |x·G|^{α+ε}`. Equivalent to the source's `max_{x∈X}` form. -/
noncomputable def AK (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ X : Finset (ℤ × ℤ), X.Nonempty ∧
    (∀ x ∈ X, x.1 + x.2 ≠ 0) ∧
    ∀ G : Finset (ℤ × ℤ), ∃ x ∈ X,
      ((G.image (fun g => g.1 - g.2)).card : ℝ) ≤
        C * ((G.image (fun g => x.1 * g.1 + x.2 * g.2)).card : ℝ) ^ (α + ε)

end ArithmeticKakeya


