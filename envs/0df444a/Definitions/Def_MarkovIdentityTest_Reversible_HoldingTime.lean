-- Prove2me | Definitions.Def_MarkovIdentityTest_Reversible_HoldingTime
-- name    : MarkovIdentityTest_Reversible_HoldingTime
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:37:49.014623+00:00
-- url     : https://prove2.me/theorems/5efa95ec-ad19-41cf-a23f-539e172b02a3
-- title:
--   The continuous holding-time model, the discounted Green matrix $G=(I-zP)^{-1}$ and $U=G\,\mathrm{diag}(\pi)^{-1}$
-- statement:
--   **Holding-time model** (§6.3.1). Run the chain $P$ from $x$ up to an independent positive geometric time $T$ of mean $M$, and attach an independent exponential holding time of mean one before every observed transition. Formally, given the discrete path of $t$ transitions, take an independent family $E_{i,k}$ ($i\in[n]$, $k<t$) of $\mathrm{Exp}(1)$ variables and let
--   $$\ell_i=\sum_{k<N_i}E_{i,k},$$
--   the total holding time at $i$ (a sum of $N_i$ independent unit exponentials, as in the paper). The expectation of $g(\ell)$ is $\sum_t\Pr(T=t)\sum_\omega\Pr_{P,x}(\omega)\,\mathbb E[g(\ell)\mid\omega]$; integrability requires each inner integral to exist and the outer series of $\mathbb E|g(\ell)|$ to converge.
--
--   With $z=1-1/M$ the **discounted Green matrix** is $G=(I-zP)^{-1}$ and the **normalized Green matrix** is $U=G\,\mathrm{diag}(\pi)^{-1}$, i.e. $U_{xy}=G_{xy}/\pi_y$.
--
--   **Formalization Note.** `Matrix.inv` returns $0$ for a singular matrix; for stochastic $P$ and $M\ge1$ we have $0\le z<1$, so $I-zP$ is invertible.
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 33 §6.3.1

import Mathlib
import Definitions.Def_MarkovIdentityTest_Reversible_Trajectory

set_option autoImplicit false

open Finset MeasureTheory ProbabilityTheory

namespace MarkovIdentityTest.Reversible

/-- Total holding times (§6.3.1, p. 33 / PDF 35): given the discrete path `ω` of `t` transitions
and a family `E (i, k)` of holding times, `ℓᵢ = ∑_{k < Nᵢ} E (i, k)` — one holding time before
every observed departure from `i`. -/
noncomputable def holdingTimes {n t : ℕ} (ω : Fin (t + 1) → Fin n) (E : Fin n × Fin t → ℝ)
    (i : Fin n) : ℝ :=
  ∑ k : Fin t, if (k : ℕ) < departures ω i then E (i, k) else 0

/-- The law of the holding-time family: independent exponential variables of mean one. -/
noncomputable def holdingLaw (n t : ℕ) : Measure (Fin n × Fin t → ℝ) :=
  Measure.pi fun _ => expMeasure 1

/-- Expectation of `g(ℓ₁, …, ℓₙ)` in the holding-time model of §6.3.1: `T` positive geometric with
mean `M`, the discrete path from `x` under `P` up to `T`, and independent `Exp(1)` holding times. -/
noncomputable def holdingExp {n : ℕ} (M : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n)
    (g : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑' t, geomPmf M t * ∑ ω, trajProb P x t ω * ∫ E, g (holdingTimes ω E) ∂(holdingLaw n t)

/-- `g(ℓ)` is integrable in the holding-time model. -/
def HoldingIntegrable {n : ℕ} (M : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n)
    (g : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ (t : ℕ) (ω : Fin (t + 1) → Fin n),
      Integrable (fun E => g (holdingTimes ω E)) (holdingLaw n t)) ∧
    Summable fun t => geomPmf M t * ∑ ω, trajProb P x t ω *
      ∫ E, |g (holdingTimes ω E)| ∂(holdingLaw n t)

/-- The discounted Green matrix `G = (I - zP)⁻¹` with `z = 1 - 1/M` (§6.3.1). -/
noncomputable def greenMatrix {n : ℕ} (M : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 - (1 - 1 / M) • P)⁻¹

/-- The normalized Green matrix `U = G diag(π)⁻¹` (§6.3.1). -/
noncomputable def normalizedGreen {n : ℕ} (M : ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (π : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  greenMatrix M P * Matrix.diagonal fun i => 1 / π i

end MarkovIdentityTest.Reversible


