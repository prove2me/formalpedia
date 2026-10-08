-- Prove2me | Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2
-- name    : HighDimProb_Concentration_SubgaussianNorm_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:16:33.265653+00:00
-- url     : https://prove2.me/theorems/6b67a4a9-2481-4820-a52d-44be95d82e6b
-- title:
--   The sub-gaussian (Orlicz $\psi_2$) norm of a real random variable, valued in $[0,\infty]$
-- statement:
--   This is the **sub-gaussian norm** (Orlicz $\psi_2$ norm) of a real random variable, the standard non-asymptotic measure of how light-tailed it is.
--
--   Fix a probability space $(\Omega,\mathcal F,P)$ and a random variable $X:\Omega\to\mathbb R$. The sub-gaussian norm of $X$ is
--   $$
--   \|X\|_{\psi_2} := \inf\{t>0 : \mathbb E\exp(X^2/t^2)\le 2\} \in [0,\infty],
--   $$
--   with the convention $\inf\emptyset = +\infty$. $X$ is **sub-gaussian** (Definition 2.5.6) exactly when $\|X\|_{\psi_2}<\infty$; for a sub-gaussian $X$ the value is the book's infimum (2.13), and e.g. a standard Gaussian, any bounded variable, and any Rademacher variable are sub-gaussian with finite norm, while a heavy-tailed variable (for instance $\omega\mapsto\omega^{-1}$ on $(0,1]$) has norm $+\infty$.
--
--   **Formalization Note.** The retired definition `HighDimProb_Concentration_SubgaussianNorm` took the infimum in $\mathbb R$, where `sInf ∅ = 0`, so a non-sub-gaussian variable received the junk value $0$ and every hypothesis "$\|X\|_{\psi_2}\le K$" held vacuously for it; this is the mechanism of the accepted disproofs of Theorems 4.4.5, 8.1.3, 9.1.1 and 9.4.2 of this series. The corrected definition is valued in `ℝ≥0∞` and takes the infimum (`⨅`) over the admissible $t>0$ in that complete lattice, so the empty family gives $\top=+\infty$. The admissible set keeps the `Integrable` conjunct (Mathlib's Bochner integral of a non-integrable function is $0$, so "$\int\le 2$" alone would admit infinite moments); `Integrable` also carries a.e.-strong measurability, so a non-measurable $X$ has norm $+\infty$, consistent with the book's convention that random variables are measurable. The namespace and declaration name (`HighDimProb.Concentration.subgaussianNorm`) are unchanged so that statements read as before.
-- source:
--   Vershynin, High-Dimensional Probability (CUP 2018), Definition 2.5.6, Eq. (2.13), p. 28 (PDF p. 36)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace HighDimProb.Concentration

/-- The sub-gaussian (Orlicz `ψ₂`) norm of a real random variable `X` on a probability
space `(Ω, P)`. Vershynin, *High-Dimensional Probability* (2018), Definition 2.5.6 /
Eq. (2.13): the smallest `t > 0` such that the exponential moment `E[exp(X² / t²)]` is
*finite* and `≤ 2`, i.e.

`‖X‖_{ψ₂} := inf {t > 0 : exp(X² / t²) is integrable and E exp(X² / t²) ≤ 2}`.

**Corrected version (`_v2`) of `HighDimProb_Concentration_SubgaussianNorm`.** The norm is
valued in `ℝ≥0∞`, not `ℝ`. The retired version took `sInf` of the admissible set in `ℝ`, so a
random variable that is *not* sub-gaussian (empty admissible set) received the junk value
`sInf ∅ = 0`, and every hypothesis of the form `‖X‖_{ψ₂} ≤ K` was then satisfied vacuously by
heavy-tailed (even non-integrable) variables. Here the infimum is taken in the complete lattice
`ℝ≥0∞`, where the infimum of an empty family is `⊤`: a random variable is sub-gaussian in the
sense of Definition 2.5.6 **exactly when** `subgaussianNorm P X ≠ ⊤`, and a hypothesis
`subgaussianNorm P X ≤ K` with `K : ℝ≥0` (coerced to `ℝ≥0∞`) says precisely "`X` is
sub-gaussian with `‖X‖_{ψ₂} ≤ K`", matching the book's `K = max ‖·‖_{ψ₂}` (a finite number by
assumption). For a sub-gaussian `X` the value is `ENNReal.ofReal` of the book's infimum (2.13).

The `Integrable` conjunct is kept from the original: Mathlib's Bochner integral of a
non-integrable function is `0` by convention, so without it every `t` for which the moment is
actually infinite would vacuously satisfy `∫ … ≤ 2`. `Integrable` also carries
`AEStronglyMeasurable`, so a non-measurable `X` has norm `⊤` (the book's random variables are
measurable by convention). -/
noncomputable def subgaussianNorm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ) (_ : 0 < t) (_ : Integrable (fun ω => Real.exp ((X ω) ^ 2 / t ^ 2)) P)
    (_ : ∫ ω, Real.exp ((X ω) ^ 2 / t ^ 2) ∂P ≤ 2), ENNReal.ofReal t

end HighDimProb.Concentration


