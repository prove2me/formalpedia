-- Prove2me | Definitions.Def_RennerKoenig_cond
-- name    : RennerKoenig_cond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:51.04509+00:00
-- url     : https://prove2.me/theorems/c2015f66-88c5-4733-b7ac-5831bb5d2891
-- title:
--   The conditional density operator $[\rho|\mathcal E]$
-- statement:
--   For a random state $\rho$ and an event $\mathcal E$ of positive probability,
--
--   $$
--   [\rho|\mathcal E]=\frac1{\Pr[\mathcal E]}\sum_{\omega\in\mathcal E}P(\omega)\,\rho(\omega).
--   $$
--
--   **Formalization Note** The Lean value is $0$ when $\Pr[\mathcal E]=0$, where the paper leaves it undefined. Each use in the mission carries a factor of $\Pr[\mathcal E]$.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.2, p.4

import Mathlib
import Definitions.Def_RennerKoenig_prob

namespace RennerKoenig

/-- **Density operator conditioned on an event**,
`[ρ|E] = Pr[E]⁻¹ ∑_{ω ∈ E} P(ω) ρ(ω)`. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.2, p.4.

**Formalization Note** The page leaves `[ρ|E]` undefined when `Pr[E] = 0`; here it is `0`. Every
use in this mission multiplies it by a positive power of `Pr[E]`, so the value never matters. -/
noncomputable def cond {Ω : Type*} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (P : PMF Ω) (ρ : Ω → K →L[ℂ] K) (E : Set Ω) :
    K →L[ℂ] K :=
  ((prob P E : ℝ) : ℂ)⁻¹ • ∑' ω, E.indicator (fun ω => ((P ω).toReal : ℂ) • ρ ω) ω

end RennerKoenig


