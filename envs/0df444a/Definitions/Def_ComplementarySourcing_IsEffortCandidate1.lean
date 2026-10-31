-- Prove2me | Definitions.Def_ComplementarySourcing_IsEffortCandidate1
-- name    : ComplementarySourcing_IsEffortCandidate1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:31.179102+00:00
-- url     : https://prove2.me/theorems/cd597fae-1245-4137-8dcb-193e906ba554
-- title:
--   The candidate effort $x_1$
-- statement:
--   A real $x$ is the paper's $x_1$ when $x\in[0,\epsilon_1]$ and
--
--   $$\frac{1+\alpha(2\epsilon_1-x)}{(1+\alpha x)^3}\,\epsilon_0=x,\qquad\epsilon_1=\epsilon_0+\sigma.$$
--
--   Lemma 3 proves that exactly one such value exists.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.13, Lemma 3

import Mathlib

namespace ComplementarySourcing

/-- `x` is the paper's `x₁`: a value in `[0, ϵ₁]` with `(1 + α(2ϵ₁ − x)) / (1 + αx)³ · ϵ₀ = x`, where
`ϵ₁ = ϵ₀ + σ`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Lemma 3, p.13 (PDF 13).

**Formalization Note.** A predicate; Lemma 3 proves it has exactly one solution, so later items
take `x₁` as a real with this hypothesis. -/
def IsEffortCandidate1 (α ε₀ σ x : ℝ) : Prop :=
  x ∈ Set.Icc 0 (ε₀ + σ) ∧
    (1 + α * (2 * (ε₀ + σ) - x)) / (1 + α * x) ^ 3 * ε₀ = x

end ComplementarySourcing


