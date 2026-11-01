-- Prove2me | Definitions.Def_SConvexGS_IsCoercive
-- name    : SConvexGS_IsCoercive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:23.571034+00:00
-- url     : https://prove2.me/theorems/224beff9-3566-454c-a570-ce00b4211207
-- title:
--   Coercive function
-- statement:
--   A concave function $f$ is **coercive** if
--
--   $$\lim_{\|x\|_2\to+\infty}\frac{f(x)}{\|x\|_2}=-\infty.$$
--
--   Coercivity makes $f(x)-p^{T}x$ tend to $-\infty$ at infinity for each $p$.
--
--   **Formalization Note** To avoid a division in `EReal`, the limit is written as: for every real $M$ there is $R$ with $f(x)\le M\|x\|_2$ whenever $\|x\|_2\ge R$. The length is the Euclidean $\sqrt{x^{T}x}$. At $n=0$ the condition always holds.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), p.21

import Mathlib

open Matrix

namespace SConvexGS

/-- Coercivity (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of
2021-10-29), p.21): "A concave function is coercive if `lim_{‖x‖₂→+∞} f(x)/‖x‖₂ = −∞`".

Formalization Note: to avoid a division in `EReal`, the limit is written as: for every real `M` there is `R` with `f(x) ≤ M‖x‖₂` whenever `‖x‖₂ ≥ R`. This is equivalent to
the limit, because `R` can always be enlarged. The length is the Euclidean `√(x ⬝ᵥ x)`, not the sup
norm of `Fin n → ℝ`. At `n = 0` the condition holds for every `f` (take `R = 1`). -/
def IsCoercive {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ x : Fin n → ℝ, R ≤ Real.sqrt (x ⬝ᵥ x) →
    f x ≤ ((M * Real.sqrt (x ⬝ᵥ x) : ℝ) : EReal)

end SConvexGS


