-- Prove2me | Definitions.Def_AutobidSPPE_valueLaw
-- name    : AutobidSPPE_valueLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:49.311939+00:00
-- url     : https://prove2.me/theorems/60473f59-2b5d-4ba9-8c5d-0dabd4a94e69
-- title:
--   Independent uniform value law $\prod_i \mathrm{Unif}[0,\bar v_i]$
-- statement:
--   Let $n$ bidders have true support endpoints $\bar v_1,\dots,\bar v_n$. The **value law** is the independent product
--   $$
--   \mathcal D = \prod_{i=1}^n \mathrm{Unif}[0,\bar v_i],
--   $$
--   so bidder $i$'s value $v_i$ is uniform on $[0,\bar v_i]$, independently of the other bidders. All expectations $\mathbb E_{v\sim\mathcal D}$ in the model (losses and spending) are taken under this law.
--
--   **Formalization Note** $\mathrm{Unif}[0,\bar v_i]$ is Lebesgue measure conditioned on $[0,\bar v_i]$ and the joint law is the product measure on $\mathbb R^n$ (bidders indexed by `Fin n`). The positivity $\bar v_i>0$ is a hypothesis of the theorems.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Assumption 2.3, p.11; Problem 1.1, p.4

import Mathlib

namespace AutobidSPPE

/-- The independent uniform value law `D = ∏ᵢ Unif[0, v̄ᵢ]` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Assumption 2.3, p.11;
Problem 1.1, p.4). Bidder `i`'s value `vᵢ` is uniform on `[0, v̄ᵢ]`, independently across bidders.

**Formalization Note** `Unif[0, v̄ᵢ]` is Lebesgue measure conditioned on `Set.Icc 0 (v̄ᵢ)`
(`ProbabilityTheory.cond`), and the joint law is `Measure.pi`. Bidders are `Fin n`. The positivity
`0 < v̄ᵢ` is a hypothesis of the theorems, not part of this definition. -/
noncomputable def valueLaw {n : ℕ} (vbar : Fin n → ℝ) : MeasureTheory.Measure (Fin n → ℝ) :=
  MeasureTheory.Measure.pi
    (fun i => ProbabilityTheory.cond MeasureTheory.volume (Set.Icc (0 : ℝ) (vbar i)))

end AutobidSPPE


