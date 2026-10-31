-- Prove2me | Definitions.Def_FoundationsRL_StatLearning_popLoss
-- name    : FoundationsRL_StatLearning_popLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:15.704162+00:00
-- url     : https://prove2.me/theorems/23084787-0df4-4579-b3ae-43cfd9ede677
-- title:
--   Population loss $L(f)$
-- statement:
--   Let $M^\star$ be a distribution on $\mathcal X\times\mathcal Y$ and $\ell:\mathcal Y'\times\mathcal Y\to\mathbb R$ a loss. The **population (test) loss** of a predictor $f:\mathcal X\to\mathcal Y'$ is
--
--   $$
--   L(f)=\mathbb E_{(x,y)\sim M^\star}\big[\ell(f(x),y)\big].
--   $$
--
--   This is the quantity a learner wants to make small, and every guarantee of the mission is stated in terms of it.
--
--   **Formalization Note** The expectation is a Bochner integral, whose value is the junk $0$ on a non-integrable integrand, so the theorems using $L$ carry or derive integrability.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §1.4, (1.3), p. 7

import Mathlib
open MeasureTheory

namespace FoundationsRL.StatLearning

/-- **Population (test) loss** `L(f) := E_{(x,y)∼M⋆}[ℓ(f(x), y)]`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §1.4, (1.3), p. 7.

**Formalization Note.** `M` is the distribution `M⋆` on `X × Y`, `ℓ : Y' → Y → ℝ` the loss, and the
expectation is the Bochner integral. It is the zero junk value when `(x, y) ↦ ℓ(f x, y)` is not
integrable, so every theorem using `popLoss` carries (or derives) that integrability. -/
noncomputable def popLoss {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (M : Measure (X × Y)) (ℓ : Y' → Y → ℝ) (f : X → Y') : ℝ :=
  ∫ z, ℓ (f z.1) z.2 ∂M

end FoundationsRL.StatLearning


