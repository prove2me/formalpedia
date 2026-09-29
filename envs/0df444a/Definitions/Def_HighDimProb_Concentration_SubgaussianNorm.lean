-- Prove2me | Definitions.Def_HighDimProb_Concentration_SubgaussianNorm
-- name    : HighDimProb_Concentration_SubgaussianNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:35:01.780877+00:00
-- url     : https://prove2.me/theorems/7f631528-dde6-4af1-9da1-9303f96e26e2
-- title:
--   The sub-gaussian (Orlicz $\psi_2$) norm of a real random variable
-- statement:
--   This is the **sub-gaussian norm** (also called the Orlicz $\psi_2$ norm), the standard
--   non-asymptotic measure of how light-tailed a real random variable is.
--
--   Fix a probability space $(\Omega, \mathcal F, P)$ and a random variable $X : \Omega \to
--   \mathbb R$. The sub-gaussian norm of $X$ is
--
--   $$
--   \|X\|_{\psi_2} \;:=\; \inf\bigl\{t > 0 : \mathbb E \exp(X^2/t^2) \le 2\bigr\}.
--   $$
--
--   $X$ is called **sub-gaussian** exactly when this infimum is taken over a nonempty set,
--   i.e. when some finite $t$ makes the bound $\mathbb E \exp(X^2/t^2) \le 2$ hold; in that
--   case $\|X\|_{\psi_2}$ is finite and the definition recovers the usual Gaussian-type tail
--   bound $P\{|X| \ge s\} \le 2\exp(-cs^2/\|X\|_{\psi_2}^2)$ for an absolute constant $c$. A
--   standard Gaussian, any bounded random variable, and in particular any Bernoulli or
--   Rademacher (symmetric Bernoulli) random variable are all sub-gaussian.
--
--   **Formalization Note** The definition is Vershynin's Definition 2.5.6 / Eq. (2.13)
--   verbatim, stated as a genuine infimum (`sInf`) over the set of admissible `t`, rather than
--   via Mathlib's `HasSubgaussianMGF` (which bounds the moment generating function directly
--   with a variance-proxy parameter, a different — though equivalent up to an absolute
--   constant — convention). If $X$ is not sub-gaussian, the underlying set is empty and `sInf`
--   returns Mathlib's junk value `0` for the infimum of the empty set; this convention plays
--   no role in any theorem of this mission, since every hypothesis using this norm also
--   assumes the random variable is sub-gaussian.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Definition 2.5.6, Eq. (2.13), p. 28 (PDF p. 36)

import Mathlib

open MeasureTheory

namespace HighDimProb.Concentration

/-- The sub-gaussian (Orlicz `ψ₂`) norm of a real random variable `X` on a probability
space `(Ω, P)`. Vershynin, *High-Dimensional Probability* (2018), Definition 2.5.6 /
Eq. (2.13): the smallest `t > 0` such that the exponential moment `E[exp(X² / t²)]` is
*finite* and `≤ 2`, i.e.

`‖X‖_{ψ₂} := inf {t > 0 : exp(X² / t²) is integrable and E exp(X² / t²) ≤ 2}`.

The `Integrable` conjunct is essential: Mathlib's Bochner integral of a non-integrable
function is `0` by convention, so without it every `t` for which the moment is actually
infinite would vacuously satisfy `∫ … ≤ 2` and enter the infimum, collapsing the norm of
genuinely non-sub-gaussian (and even sub-gaussian) variables to `0`. If no `t` exists with
both conjuncts holding (`X` is not sub-gaussian), `sInf` of the empty set defaults to `0`,
Mathlib's usual junk value for an unbounded-below or empty set. -/
noncomputable def subgaussianNorm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ Integrable (fun ω => Real.exp ((X ω) ^ 2 / t ^ 2)) P ∧
                ∫ ω, Real.exp ((X ω) ^ 2 / t ^ 2) ∂P ≤ 2}

end HighDimProb.Concentration


