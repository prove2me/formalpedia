-- Prove2me | Definitions.Def_RennerKoenig_prob
-- name    : RennerKoenig_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:01.112972+00:00
-- url     : https://prove2.me/theorems/0e2bff0e-df3b-4341-830d-159eb945bcaa
-- title:
--   Probability of an event
-- statement:
--   For a discrete probability space $(\Omega,P)$ and an event $\mathcal E\subseteq\Omega$,
--
--   $$
--   \Pr[\mathcal E]=\sum_{\omega\in\mathcal E}P(\omega).
--   $$
--
--   **Formalization Note** A discrete probability space is a `PMF` on an arbitrary type $\Omega$, and every subset is an event.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.2, p.3

import Mathlib

namespace RennerKoenig

/-- **Probability** `Pr[E] = ∑_{ω ∈ E} P(ω)` of an event of the discrete probability space
`(Ω, P)`. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.2, p.3.

**Formalization Note** A discrete probability space is a `PMF` on any type `Ω`; every subset is an
event. -/
noncomputable def prob {Ω : Type*} (P : PMF Ω) (E : Set Ω) : ℝ :=
  ∑' ω, E.indicator (fun ω => (P ω).toReal) ω

end RennerKoenig


