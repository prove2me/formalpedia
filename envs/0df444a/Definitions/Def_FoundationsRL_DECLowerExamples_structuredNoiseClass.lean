-- Prove2me | Definitions.Def_FoundationsRL_DECLowerExamples_structuredNoiseClass
-- name    : FoundationsRL_DECLowerExamples_structuredNoiseClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:28.226246+00:00
-- url     : https://prove2.me/theorems/e084929a-d92b-4c25-9f10-d31bb18d01f8
-- title:
--   Bandits with structured noise $\mathcal M_{\mathrm{MAB\text{-}SN}}$
-- statement:
--   Let $\Pi=[A]$, $\mathcal R=\mathbb R$ and $\mathcal O=\{\varnothing\}$. For $i\in[A]$ let $M_i(\pi)=\mathcal N(1/2,1)$ for $\pi\ne i$ and $M_i(i)=\mathrm{Ber}(3/4)$, and let $\widehat M(\pi)=\mathcal N(1/2,1)$ for every $\pi$. The class of **bandits with structured noise** is
--   $$
--   \mathcal M_{\mathrm{MAB\text{-}SN}}=\{M_1,\dots,M_A\}\cup\{\widehat M\}.
--   $$
--   In model $M_i$ the optimal action $i$ is the only one with Bernoulli rewards, so its rewards are a.s. in $\{0,1\}$ while the other actions give Gaussian rewards.
--
--   The example shows that the information in the shape of the reward distribution, not only in its mean, is what the Decision-Estimation Coefficient measures.
--
--   **Formalization Note** Actions are `Fin A` (0-based); $\mathrm{Ber}(3/4)$ is the law on $\mathbb R$ with mass $3/4$ at $1$ and $1/4$ at $0$; each reward law is paired with the trivial observation.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Example 6.5, p. 99

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FoundationsRL.DECLowerExamples

/-- **Bandits with structured noise** `M_MAB-SN = {M₁, …, M_A} ∪ {M̂}`, where
`M_i(π) = N(1/2, 1)` for `π ≠ i`, `M_i(i) = Ber(3/4)`, and `M̂(π) = N(1/2, 1)` for all `π`;
`Π = [A]`, `R = ℝ`, `O = {∅}`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Example 6.5, p. 99 (recalled on p. 111).

**Formalization Note.** Actions are `Fin A` (0-based); `O = {∅}` is `Unit`. `Ber(3/4)` is the
law on `ℝ` with mass `3/4` at `1` and `1/4` at `0`. Each reward law is paired with the trivial
observation by the measurable map `r ↦ (r, ())`. The class includes `M̂`, as in the definition of
the symbol on p. 99. -/
def structuredNoiseClass (A : ℕ) : Set (Kernel (Fin A) (ℝ × Unit)) :=
  {M | (∀ π, M π = (gaussianReal (1 / 2) 1).map (fun r => (r, ()))) ∨
    ∃ i : Fin A, ∀ π, M π =
      if π = i then
        ((3 / 4 : ℝ≥0∞) • Measure.dirac (1 : ℝ) + (1 / 4 : ℝ≥0∞) • Measure.dirac (0 : ℝ)).map
          (fun r => (r, ()))
      else (gaussianReal (1 / 2) 1).map (fun r => (r, ()))}

end FoundationsRL.DECLowerExamples


