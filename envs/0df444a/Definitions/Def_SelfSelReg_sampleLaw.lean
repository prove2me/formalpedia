-- Prove2me | Definitions.Def_SelfSelReg_sampleLaw
-- name    : SelfSelReg_sampleLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:49.688698+00:00
-- url     : https://prove2.me/theorems/30830495-686b-4cae-bf2e-f0a60769d436
-- title:
--   The law of one observation $(X,Y_{\max})$ and of an i.i.d. sample stream with fair coins
-- statement:
--   In the self-selection model one observes independent samples $(X,Y_{\max})$, where $X\sim N(0,I_n)$ and $Y_{\max}=\max_{i\in[k]}(\langle w_i,X\rangle+\xi_i)$; the index attaining the maximum is not observed. The **law of one observation** is the image of the joint law of $(X,\xi)$ under $(x,\xi)\mapsto(x,\max_i(\langle w_i,x\rangle+\xi_i))$, a probability measure on $\mathbb R^{n+1}$.
--
--   The randomness available to an algorithm with sample access is a tape of independent fair coins together with, independently, an infinite i.i.d. stream of observations with this law.
--
--   This is the only way the unknown regressors enter the goal theorem: the algorithm sees them only through samples.
--
--   **Formalization Note** One observation is one vector of $\mathbb R^{n+1}$, with $X$ in coordinates $0,\dots,n-1$ and $Y_{\max}$ in coordinate $n$, so that one `sample` instruction of the `GaussMixHH` machine in dimension $n+1$ reads one observation. The coin tape is the published `GaussMixHH.coinTape`.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Definition 1.1, p.2 (PDF p.5); Theorem 1.3, p.2 (PDF p.5)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_SelfSelReg_jointLaw

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- One observation `(X, Y_max)` written as one vector of `ℝ^{n+1}`: coordinates `0, …, n − 1` are
`X`, coordinate `n` is `Y_max` (Definition 1.1, p.2, PDF p.5). -/
noncomputable def sampleOf {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 fun m : Fin (n + 1) =>
    if h : (m : ℕ) < n then z.1 ⟨m, h⟩ else yMax w z.1 z.2

/-- **The law of one observation** of the self-selection model: the pushforward of `jointLaw n k`
under `(x, ξ) ↦ (x, max_i (⟨w_i, x⟩ + ξ_i))`.

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Definition 1.1, p.2 (PDF p.5): "we observe independent samples
(X, Y_max)… Note that the maximizing index is not observed."

**Formalization Note.** One sample is one vector of `ℝ^{n+1}` with `Y_max` last, so that one
`sample` instruction of the `GaussMixHH` machine in dimension `n + 1` writes one observation. The
regressors `w` enter only through this law. -/
noncomputable def sampleLaw {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
  (jointLaw n k).map (sampleOf w)

/-- The randomness of a run: a fair-coin tape (`GaussMixHH.coinTape`) and, independent of it, an
i.i.d. stream of observations with law `sampleLaw w` ("independent samples", "sample access",
Theorem 1.3, p.2). -/
noncomputable def sampleSpace {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    Measure ((ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin (n + 1)))) :=
  GaussMixHH.coinTape.prod (Measure.infinitePi fun _ : ℕ => sampleLaw w)

end SelfSelReg


