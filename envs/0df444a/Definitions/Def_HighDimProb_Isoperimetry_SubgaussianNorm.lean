-- Prove2me | Definitions.Def_HighDimProb_Isoperimetry_SubgaussianNorm
-- name    : HighDimProb_Isoperimetry_SubgaussianNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:38:27.686585+00:00
-- url     : https://prove2.me/theorems/576f0d8c-8fc1-4784-9c8b-e99d5f811976
-- title:
--   The sub-gaussian (Orlicz $\psi_2$) norm of a real random variable
-- statement:
--   This is the **sub-gaussian norm** (also called the Orlicz $\psi_2$ norm), the standard
--   non-asymptotic measure of how light-tailed a real random variable is. It is restated here,
--   identically to Vershynin's own Definition 2.5.6, inside this chapter's namespace so the
--   chapter's theorems can be stated self-contained.
--
--   Fix a probability space $(\Omega, \mathcal F, P)$ and a random variable $X : \Omega \to
--   \mathbb R$. The sub-gaussian norm of $X$ is
--
--   $$
--   \|X\|_{\psi_2} \;:=\; \inf\bigl\{t > 0 : \mathbb E \exp(X^2/t^2) \le 2\bigr\}.
--   $$
--
--   $X$ is called **sub-gaussian** exactly when this infimum is taken over a nonempty set. A
--   standard Gaussian and any bounded random variable are sub-gaussian; in this mission the
--   coordinates of a point uniformly distributed on a Euclidean sphere are the running example
--   (Theorem 5.1.4).
--
--   **Formalization Note** The definition is Vershynin's Definition 2.5.6 / Eq. (2.13)
--   verbatim, stated as a genuine infimum (`sInf`) over the set of admissible `t`. If $X$ is
--   not sub-gaussian, the underlying set is empty and `sInf` returns Mathlib's junk value `0`;
--   this convention plays no role in this mission's theorems, since every hypothesis using this
--   norm also assumes (via the Lipschitz/sub-gaussian structure of the goal) that the relevant
--   random variable is sub-gaussian.
--
--   **Moderator's note.** The defining set requires the exponential moment to be *finite* (Bochner-integrable) as well as at most $2$; Mathlib's integral of a non-integrable function is $0$, which would otherwise admit every $t$ with an infinite moment.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Definition 2.5.6, Eq. (2.13), p. 28 (PDF p. 36)

import Mathlib

open MeasureTheory

namespace HighDimProb.Isoperimetry

/-- The sub-gaussian (Orlicz `ψ₂`) norm of a real random variable `X` on a probability
space `(Ω, P)`. Vershynin, *High-Dimensional Probability* (2018), Definition 2.5.6 /
Eq. (2.13), restated in this chapter's namespace: the smallest `t > 0` such that
the exponential moment `E[exp(X² / t²)]` is finite (integrable) and `≤ 2`, i.e.

`‖X‖_{ψ₂} := inf {t > 0 : E exp(X² / t²) ≤ 2}`.

If no such `t` exists (`X` is not sub-gaussian), `sInf` of the empty set defaults to `0`,
Mathlib's usual junk value for an unbounded-below or empty set. -/
noncomputable def subgaussianNorm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ MeasureTheory.Integrable (fun ω => Real.exp ((X ω) ^ 2 / t ^ 2)) P ∧
                ∫ ω, Real.exp ((X ω) ^ 2 / t ^ 2) ∂P ≤ 2}

end HighDimProb.Isoperimetry


