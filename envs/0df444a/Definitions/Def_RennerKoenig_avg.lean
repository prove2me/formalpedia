-- Prove2me | Definitions.Def_RennerKoenig_avg
-- name    : RennerKoenig_avg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:14.203005+00:00
-- url     : https://prove2.me/theorems/6644e095-cf08-45f0-9e5d-1291379388b5
-- title:
--   The density operator $[\rho]$ of a random state
-- statement:
--   A random state on a Hilbert space is a function $\rho$ from a discrete probability space $(\Omega,P)$ to density operators. For an observer ignorant of the randomness, the system is described by
--
--   $$
--   [\rho]=\sum_{\omega\in\Omega}P(\omega)\,\rho(\omega).
--   $$
--
--   **Formalization Note** An unconditional sum in operator norm, which converges because density operators have operator norm at most $1$.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.2, p.4

import Mathlib

namespace RennerKoenig

/-- **The density operator of a random state**, `[ρ] = ∑_ω P(ω) ρ(ω)`. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.2, p.4.

**Formalization Note** The sum is an unconditional sum in operator norm. It converges for random
states, whose values have operator norm at most `1`. -/
noncomputable def avg {Ω : Type*} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (P : PMF Ω) (ρ : Ω → K →L[ℂ] K) : K →L[ℂ] K :=
  ∑' ω, ((P ω).toReal : ℂ) • ρ ω

end RennerKoenig


