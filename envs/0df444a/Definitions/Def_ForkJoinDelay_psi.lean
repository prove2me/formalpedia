-- Prove2me | Definitions.Def_ForkJoinDelay_psi
-- name    : ForkJoinDelay_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:19.850771+00:00
-- url     : https://prove2.me/theorems/94c2eb6d-2d34-4d70-ace6-f95d3f105025
-- title:
--   The joint Laplace–Stieltjes transform $\Psi_{k,h_1,h_2}(w_0,w_{FJ})$
-- statement:
--   For a fork-join service model and a state $(k,h_1,h_2)$, the **joint Laplace–Stieltjes transform** of the tagged customer's sojourn times is
--
--   $$\Psi_{k,h_1,h_2}(w_0,w_{FJ})=\mathbb E\bigl[e^{-w_0S_0-w_{FJ}S_{FJ}}\bigr],$$
--
--   where $S_0$ is the sojourn time in the first station and $S_{FJ}=\max\{S_1,S_2\}$ the sojourn time in the fork-join part, in the network started in state $(k,h_1,h_2)$: $k$ customers at $Q_0$, $h_1$ at UFJ and $h_2$ at LFJ.
--
--   This is the paper's target quantity; setting $w_{FJ}=0$, $w_0=0$ or $w_{FJ}=w_0$ gives the transforms of $S_0$, $S_{FJ}$ and the total sojourn time.
--
--   **Formalization Note** The conditional expectation given the state is modelled by the network started in that state with fresh exponential services; the state enters the construction, not the probability space. The arguments $w_0,w_{FJ}$ are complex numbers; for nonnegative real parts the integrand has modulus at most $1$ almost surely.
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), §2, p.8 (definition of Ψk,h1,h2(w0,wFJ))

import Mathlib
import Definitions.Def_ForkJoinDelay_sojournQ0
import Definitions.Def_ForkJoinDelay_sojournFJ

open MeasureTheory

namespace ForkJoinDelay

/-- **The joint Laplace–Stieltjes transform `Ψ_{k,h₁,h₂}(w₀, w_FJ)`.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, §2, p.8: "Our goal is to determine
Ψk,h1,h2(w0,wFJ) ≡ Ek,h1,h2[e^{−w0S0−wFJSFJ}], the joint Laplace–Stieltjes transform of S0 and
SFJ, given that, at the arrival epoch of the tagged customer in Q0, there are k customers in the
first station, h1 customers in the UFJ station, and h2 customers in the LFJ station."

`psi P V U G k h₁ h₂ w₀ wFJ = ∫ exp (-(w₀ S₀ + w_FJ S_FJ)) dP`, where `S₀ = sojournQ0 V k` and
`S_FJ = sojournFJ V U G k h₁ h₂` are the tagged customer's sojourn times in the network started
in state `(k, h₁, h₂)` and built from the service times `V`, `U`, `G`.

**Formalization Note.** The conditional expectation `E_{k,h₁,h₂}` is modelled by the system
started in state `(k, h₁, h₂)` with fresh exponential services (`IsFJModel`); the state is a
parameter of the construction, not of the probability space. The arguments `w₀, w_FJ` are
complex; for `Re w₀, Re w_FJ ≥ 0` the integrand has modulus at most `1` almost surely. -/
noncomputable def psi {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V U G : ℕ → Ω → ℝ)
    (k h₁ h₂ : ℕ) (w₀ wFJ : ℂ) : ℂ :=
  ∫ ω, Complex.exp (-(w₀ * (sojournQ0 V k ω : ℂ) + wFJ * (sojournFJ V U G k h₁ h₂ ω : ℂ))) ∂P

end ForkJoinDelay


