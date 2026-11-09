-- Prove2me | Definitions.Def_MWCSherali_planeMeasure
-- name    : MWCSherali_planeMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:23.462795+00:00
-- url     : https://prove2.me/theorems/6c20db96-fed4-40db-bcd3-c36b21a6ed05
-- title:
--   The area element $dt_i\,dt_j$ on a slice $\{t_a=h\}$
-- statement:
--   For $a\in[4]$ and $h\in\mathbb R$, the measure $dt_i\,dt_j$ on the plane $\{t\mid t_a=h,\ \sum_\ell t_\ell=1\}$ is the image of Lebesgue measure on $\mathbb R^2$ under $(s,s')\mapsto t$ with $t_a=h$, $t_i=s$, $t_j=s'$, $t_l=1-h-s-s'$, where $i<j<l$ are the indices other than $a$. It is used for the cross sections $\{t_a=\alpha\}$ of the corners in (9)–(10) and the exit faces $\{t_a=0\}$ in Lemma 4.7.
--
--   **Formalization Note** Choosing any two of the three free coordinates gives the same measure. The measure is infinite and is only used restricted to bounded regions.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (9), (10), p.33; Lemma 4.7, p.40

import Mathlib

namespace MWCSherali

open MeasureTheory

/-- **The area element `dt_i dt_j` on a slice `{t_a = h}` of the simplex.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026),
(9), (10), p.33, and the definition of `ν_a` in Lemma 4.7, p.40 ("`dt_i dt_j`, `i ≠ j ∈ [4] ∖ {a}`").

`planeMeasure a h` is the image of Lebesgue measure on `ℝ²` under
`(s₀, s₁) ↦ t` with `t_a = h`, `t_i = s₀`, `t_j = s₁`, `t_l = 1 − h − s₀ − s₁`, where
`i < j < l` are the three indices other than `a`: the measure `dt_i dt_j` on the plane
`{t | t_a = h, ∑ t = 1}`.

**Formalization Note.** The point is `Fin.insertNth a h ![s₀, s₁, 1 − h − s₀ − s₁]`. Choosing any
other two of the three free coordinates gives the same measure (the projection has Jacobian 1),
as the paper notes. The measure is infinite; it is only used restricted to bounded regions. -/
noncomputable def planeMeasure (a : Fin 4) (h : ℝ) : Measure (Fin 4 → ℝ) :=
  Measure.map (fun s : Fin 2 → ℝ => Fin.insertNth a h ![s 0, s 1, 1 - h - s 0 - s 1]) volume

end MWCSherali


