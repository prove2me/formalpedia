-- Prove2me | Definitions.Def_MWCSherali_volD4
-- name    : MWCSherali_volD4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:07.772205+00:00
-- url     : https://prove2.me/theorems/0b99c78a-54f4-4ce8-bf76-3a394b539da9
-- title:
--   The volume element $dt$ on $\Delta_4$
-- statement:
--   On $\Delta_4$ the paper uses $dt=dt_1\,dt_2\,dt_3$ with $t_4=1-t_1-t_2-t_3$: the image of Lebesgue measure on $\{s\in\mathbb R^3\mid s\ge0,\ s_1+s_2+s_3\le1\}$ under $s\mapsto(s_1,s_2,s_3,1-s_1-s_2-s_3)$. Any other three coordinates give the same measure.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §4, p.32

import Mathlib

namespace MWCSherali

open MeasureTheory

/-- **The volume element `dt` on `Δ₄`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), §4, p.32: "we use
`dt = dt₁ dt₂ dt₃` with `t₄ = 1 − t₁ − t₂ − t₃` to compute the integral over `Δ₄`".

It is the image of Lebesgue measure on `{s ∈ ℝ³ | s ≥ 0, s₀ + s₁ + s₂ ≤ 1}` under
`s ↦ (s₀, s₁, s₂, 1 − s₀ − s₁ − s₂)`, a measure on `ℝ⁴` carried by `Δ₄`.

**Formalization Note.** Coordinates are 0-based: the paper's `t₁, t₂, t₃, t₄` are `t 0, …, t 3`.
Using any other three coordinates gives the same measure (p.32). -/
noncomputable def volD4 : Measure (Fin 4 → ℝ) :=
  Measure.map (fun s : Fin 3 → ℝ => ![s 0, s 1, s 2, 1 - s 0 - s 1 - s 2])
    (volume.restrict {s : Fin 3 → ℝ | (∀ i, 0 ≤ s i) ∧ s 0 + s 1 + s 2 ≤ 1})

end MWCSherali


