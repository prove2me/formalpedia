-- Prove2me | Definitions.Def_SigRoute_condProb
-- name    : SigRoute_condProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:51.059249+00:00
-- url     : https://prove2.me/theorems/2465e4d1-29e1-40e0-af93-fc9e628c0e88
-- title:
--   Conditional probability $\mathbb P[E\mid\mathcal G]$
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a measure space, $\mathcal G$ a σ-algebra on $\Omega$ and $E\subseteq\Omega$ an event. The **conditional probability** of $E$ given $\mathcal G$ is the conditional expectation of the indicator of $E$:
--
--   $$
--   \mathbb P[E\mid\mathcal G]=\mathbb E[\mathbf 1_E\mid\mathcal G].
--   $$
--
--   It is defined up to $\mu$-null sets, so a statement such as "$\mathbb P[E\mid\mathcal F_{j-1}]\le p$" means that the bound holds almost surely, as in the paper's convention (§2, p.4: "for every history").
--
--   **Formalization Note** This is Mathlib's `condExp` applied to the indicator of $E$. For a measurable $E$ and a sub-σ-algebra $\mathcal G$ of the ambient one, the indicator is integrable and the conditional expectation is a genuine version; every event to which the mission applies it is measurable by the adaptedness of the run.
-- source:
--   Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), §2 "Filtrations", p.4

import Mathlib

namespace SigRoute

open MeasureTheory

/-- The conditional probability `P[E | 𝒢]` of an event `E` given a σ-algebra `𝒢`, as the conditional
expectation of the indicator of `E` (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), §2 "Filtrations", p.4: statements such as
"P[E | F_{j−1}] ≤ p" hold almost surely).

**Formalization Note** This is Mathlib's `condExp` of the indicator `1_E`; it is defined up to
`μ`-null sets, so every statement about it in this mission holds `μ`-almost everywhere, as in the paper.
The indicator is bounded, so for a measurable `E` and `𝒢` below the ambient σ-algebra it is integrable
and the conditional expectation is not Lean's junk value `0`. -/
noncomputable def condProb {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (𝒢 : MeasurableSpace Ω)
    (E : Set Ω) : Ω → ℝ :=
  condExp 𝒢 μ (E.indicator fun _ => (1 : ℝ))

end SigRoute


