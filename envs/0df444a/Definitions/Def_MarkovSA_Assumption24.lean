-- Prove2me | Definitions.Def_MarkovSA_Assumption24
-- name    : MarkovSA_Assumption24
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:10.127902+00:00
-- url     : https://prove2.me/theorems/a3d23afc-2212-4a1c-9d8a-9fb818d09451
-- title:
--   Assumption 2.4 — martingale-difference noise with affine growth
-- statement:
--   **Assumption 2.4.** Along the iterates $x_k$, the noise $(w_k)$ satisfies, with constants $A_2,B_2>0$:
--
--   1. $\mathbb E[w_k\mid\mathcal F_k]=0$ for all $k\ge0$;
--   2. $\|w_k\|_c\le A_2\|x_k\|_c+B_2$ for all $k\ge0$.
--
--   Thus $(w_k)$ is a martingale-difference sequence with respect to $(\mathcal F_k)$ that grows at most linearly in the iterate.
--
--   **Formalization Note** Each $w_k$ is assumed measurable, so that the conditional expectation is meaningful. Part 2 is required almost surely, which a pathwise bound implies (reading R8).
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Assumption 2.4, p.6

import Mathlib
import Definitions.Def_MarkovSA_sigmaF
open MeasureTheory

namespace MarkovSA

/-- **Assumption 2.4** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.6) for the noise `w` along the iterates `x`, with constants `A₂, B₂ > 0`:
(1) `E[w_k | 𝓕_k] = 0` for all `k`; (2) `‖w_k‖_c ≤ A₂‖x_k‖_c + B₂` for all `k`.

**Formalization Note.** Each `w k` is measurable, so that the conditional expectation is not a junk
value. Part (2) is required almost surely (reading R8: a pathwise bound implies it). -/
def Assumption24 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] [MeasurableSpace 𝒴] [MeasurableSingletonClass 𝒴] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Pr : Measure Ω) (x : ℕ → Ω → E) (Y : ℕ → Ω → 𝒴) (w : ℕ → Ω → E) (A₂ B₂ : ℝ) : Prop :=
  0 < A₂ ∧ 0 < B₂ ∧ (∀ k, Measurable (w k)) ∧
    (∀ k, Pr[w k | sigmaF x Y w k] =ᵐ[Pr] 0) ∧
    ∀ k, ∀ᵐ ω ∂Pr, ‖w k ω‖ ≤ A₂ * ‖x k ω‖ + B₂

end MarkovSA


