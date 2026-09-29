-- Prove2me | Definitions.Def_HighDimProb_Concentration_SubexponentialNorm
-- name    : HighDimProb_Concentration_SubexponentialNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:35:25.329449+00:00
-- url     : https://prove2.me/theorems/6a4468f9-c888-4809-8699-b02b3f1d2bf1
-- title:
--   The sub-exponential (Orlicz $\psi_1$) norm of a real random variable
-- statement:
--   This is the **sub-exponential norm** (also called the Orlicz $\psi_1$ norm), the
--   non-asymptotic measure of tail heaviness one step below sub-gaussian.
--
--   Fix a probability space $(\Omega, \mathcal F, P)$ and a random variable $X : \Omega \to
--   \mathbb R$. The sub-exponential norm of $X$ is
--
--   $$
--   \|X\|_{\psi_1} \;:=\; \inf\bigl\{t > 0 : \mathbb E \exp(|X|/t) \le 2\bigr\}.
--   $$
--
--   $X$ is called **sub-exponential** exactly when this infimum is taken over a nonempty set.
--   A finite $\|X\|_{\psi_1}$ is equivalent (up to an absolute constant) to an exponential-type
--   tail bound $P\{|X| \ge s\} \le 2\exp(-cs/\|X\|_{\psi_1})$. Every sub-gaussian random
--   variable is sub-exponential, and the square of a sub-gaussian random variable is always
--   sub-exponential even when it is not itself sub-gaussian — the canonical example is the
--   squared coordinate of a standard Gaussian vector, whose tail is exponential rather than
--   Gaussian.
--
--   **Formalization Note** The definition is Vershynin's Definition 2.7.5 / Eq. (2.21)
--   verbatim, stated as a genuine infimum (`sInf`), in the same convention as
--   `subgaussianNorm` above (Mathlib has no sub-exponential analogue of `HasSubgaussianMGF`).
--   As with `subgaussianNorm`, `sInf` of the empty set defaults to `0` when $X$ is not
--   sub-exponential; every hypothesis using this norm in this mission also assumes the random
--   variable is sub-exponential, so this convention is never exercised.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Definition 2.7.5, Eq. (2.21), p. 33 (PDF p. 41)

import Mathlib

open MeasureTheory

namespace HighDimProb.Concentration

/-- The sub-exponential (Orlicz `ψ₁`) norm of a real random variable `X` on a probability
space `(Ω, P)`. Vershynin, *High-Dimensional Probability* (2018), Definition 2.7.5 /
Eq. (2.21): the smallest `t > 0` such that the exponential moment `E[exp(|X| / t)]` is
*finite* and `≤ 2`, i.e.

`‖X‖_{ψ₁} := inf {t > 0 : exp(|X| / t) is integrable and E exp(|X| / t) ≤ 2}`.

The `Integrable` conjunct is essential: Mathlib's Bochner integral of a non-integrable
function is `0` by convention, so without it every `t` for which the moment is actually
infinite would vacuously satisfy `∫ … ≤ 2` and enter the infimum, collapsing the norm of
genuinely non-sub-exponential (and even sub-exponential) variables to `0`. If no `t` exists
with both conjuncts holding (`X` is not sub-exponential), `sInf` of the empty set defaults
to `0`, Mathlib's usual junk value for an unbounded-below or empty set. -/
noncomputable def subexponentialNorm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ Integrable (fun ω => Real.exp (|X ω| / t)) P ∧
                ∫ ω, Real.exp (|X ω| / t) ∂P ≤ 2}

end HighDimProb.Concentration


