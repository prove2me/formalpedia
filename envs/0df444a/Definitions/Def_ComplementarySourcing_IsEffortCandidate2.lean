-- Prove2me | Definitions.Def_ComplementarySourcing_IsEffortCandidate2
-- name    : ComplementarySourcing_IsEffortCandidate2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:32.92943+00:00
-- url     : https://prove2.me/theorems/3e7083bd-762a-4c26-a8f8-8cecc14a008b
-- title:
--   The candidate effort $x_2$
-- statement:
--   A real $x$ is the paper's $x_2$ when $x\in[0,\epsilon_2]$ and
--
--   $$\frac{1+\alpha(2\epsilon_2-x)}{(1+\alpha x)^3}\,\epsilon_2=x,\qquad\epsilon_2=\epsilon_0-\sigma.$$
--
--   The factor after the fraction is $\epsilon_2$, not $\epsilon_0$. Lemma 3 proves that exactly one such value exists.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.13, Lemma 3

import Mathlib

namespace ComplementarySourcing

/-- `x` is the paper's `x₂`: a value in `[0, ϵ₂]` with `(1 + α(2ϵ₂ − x)) / (1 + αx)³ · ϵ₂ = x`, where
`ϵ₂ = ϵ₀ − σ`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Lemma 3, p.13 (PDF 13).

**Formalization Note.** A predicate; Lemma 3 proves it has exactly one solution. The factor after
the fraction is `ϵ₂`, not `ϵ₀`, as printed. -/
def IsEffortCandidate2 (α ε₀ σ x : ℝ) : Prop :=
  x ∈ Set.Icc 0 (ε₀ - σ) ∧
    (1 + α * (2 * (ε₀ - σ) - x)) / (1 + α * x) ^ 3 * (ε₀ - σ) = x

end ComplementarySourcing


