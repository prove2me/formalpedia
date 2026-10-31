-- Prove2me | Definitions.Def_FoundationsRL_DECLowerExamples_gaussianBanditClass
-- name    : FoundationsRL_DECLowerExamples_gaussianBanditClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:24.897334+00:00
-- url     : https://prove2.me/theorems/899df2f9-a419-4621-92a2-e875a88e676c
-- title:
--   Gaussian multi-armed bandit class $\mathcal M_{\mathrm{MAB\text{-}G}}$
-- statement:
--   Let $\Pi=[A]$ be a set of $A$ actions, with reward space $\mathcal R=\mathbb R$ and no observations ($\mathcal O=\{\varnothing\}$). The **Gaussian multi-armed bandit class** is
--   $$
--   \mathcal M_{\mathrm{MAB\text{-}G}}=\bigl\{M:\ M(\pi)=\mathcal N(f(\pi),1),\ f:\Pi\to[0,1]\bigr\}.
--   $$
--   Each model draws the reward of action $\pi$ from a unit-variance Gaussian whose mean $f(\pi)$ lies in $[0,1]$.
--
--   It is the basic example on which the constrained Decision-Estimation Coefficient is computed (Example 6.4).
--
--   **Formalization Note** Actions are `Fin A` (0-based). The empty observation is `Unit`, and $\mathcal N(m,1)$ is paired with it through the measurable map $r\mapsto(r,())$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Example 6.4, p. 98

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FoundationsRL.DECLowerExamples

/-- **Multi-armed bandit with Gaussian rewards** `M_MAB-G = {M : M(π) = N(f(π), 1), f : Π → [0, 1]}`,
`Π = [A]`, `R = ℝ`, `O = {∅}`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Example 6.4, p. 98.

A model is a kernel `M : Fin A → Δ(ℝ × Unit)`; it belongs to the class when there is
`f : Fin A → [0, 1]` with `M(π) = N(f(π), 1)` (the reward) paired with the trivial observation.

**Formalization Note.** Actions `[A] = {1, …, A}` are `Fin A` (0-based). The empty observation
`O = {∅}` is `Unit`, and `N(m, 1) ⊗ δ_∅` is the image of `gaussianReal m 1` under the measurable
map `r ↦ (r, ())`. -/
def gaussianBanditClass (A : ℕ) : Set (Kernel (Fin A) (ℝ × Unit)) :=
  {M | ∃ f : Fin A → ℝ, (∀ π, f π ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ π, M π = (gaussianReal (f π) 1).map (fun r => (r, ()))}

end FoundationsRL.DECLowerExamples


