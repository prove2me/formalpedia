-- Prove2me | Definitions.Def_FoundationsRL_DECLower_hellingerSq
-- name    : FoundationsRL_DECLower_hellingerSq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:06:24.531599+00:00
-- url     : https://prove2.me/theorems/895a743c-2cb5-4749-b37a-b7d8400932a9
-- title:
--   Squared Hellinger distance $D^2_{\mathrm H}(P,Q)=\int(\sqrt{dP/d\nu}-\sqrt{dQ/d\nu})^2\,d\nu$
-- statement:
--   Let $P$ and $Q$ be measures on a measurable space $(\Omega,\mathcal F)$. The **squared Hellinger distance** is
--
--   $$
--   D^2_{\mathrm H}(P,Q)=\int_\Omega\left(\sqrt{\frac{dP}{d\nu}}-\sqrt{\frac{dQ}{d\nu}}\right)^2 d\nu,\qquad \nu=P+Q .
--   $$
--
--   It is the $f$-divergence with $f(t)=(1-\sqrt t)^2$. There is no factor $1/2$: for probability measures $D^2_{\mathrm H}(P,Q)\in[0,2]$.
--
--   It is the divergence in which the information constraint of the constrained Decision-Estimation Coefficient is measured, and it appears in Lemma 19 and in (6.40).
--
--   **Formalization Note** The notes use densities against "a common dominating measure $\nu$"; $\nu=P+Q$ is one, and the value does not depend on the choice. The value lies in $[0,\infty]$ (a Lebesgue integral of a nonnegative function), like Mathlib's KL divergence. This is a local copy of the same object drafted in the mission on Foster, Kakade, Qian & Rakhlin (2021), which is not yet published.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.2, p. 96 (squared Hellinger distance)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.DECLower

/-- **Squared Hellinger distance** `D²_H(P, Q) = ∫ (√(dP/dν) − √(dQ/dν))² dν`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §6.2, p. 96 ("Choosing f(t) = (1 − √t)² gives squared Hellinger distance").

The densities are taken against the dominating measure `ν = μ + ν'`.

**Formalization Note.** p. 96 defines the divergences with densities against "a common dominating
measure ν"; `μ + ν'` is one such measure, and the value does not depend on the choice. There is no
factor `1/2`: for probability measures the value lies in `[0, 2]` (p. 97, "Hellinger (by 2)").
The value is in `ℝ≥0∞` (a lower Lebesgue integral of a nonnegative measurable function), like
Mathlib's `klDiv`. -/
noncomputable def hellingerSq {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((Real.sqrt (μ.rnDeriv (μ + ν) x).toReal
      - Real.sqrt (ν.rnDeriv (μ + ν) x).toReal) ^ 2) ∂(μ + ν)

end FoundationsRL.DECLower


