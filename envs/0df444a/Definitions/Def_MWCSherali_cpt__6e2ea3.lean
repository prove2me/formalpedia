-- Prove2me | Definitions.Def_MWCSherali_cpt__6e2ea3
-- name    : MWCSherali_cpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:18.146624+00:00
-- url     : https://prove2.me/theorems/6e2ea383-ebcb-4445-949d-fe65bd6e25f6
-- title:
--   Coordinates of the special points of the central region
-- statement:
--   $$o=\big(\tfrac14,\tfrac14,\tfrac14,\tfrac14\big),\quad v=(\alpha,1-\alpha-\beta,\beta,0),$$
--
--   $v_{ij}$ is $v$ with coordinates $i$ and $j$ swapped, and
--
--   $$h_c=\big(\alpha,\tfrac{1-\alpha}3,\tfrac{1-\alpha}3,\tfrac{1-\alpha}3\big),\quad h_s=\big(\tfrac13,\tfrac13,\tfrac13,0\big),\quad h_t=\big(\tfrac{1-\beta}2,\tfrac{1-\beta}2,\tfrac\beta2,\tfrac\beta2\big),$$
--
--   the centres of $Z\cap K_1$, $Z\cap\Gamma_4$ and $Z\cap T_{12}$. All vertices of $Z$ are coordinate permutations of $v$.
--
--   **Formalization Note** The paper's 1-based swaps $v_{12},v_{23},v_{34}$ exchange the 0-based Lean coordinates $(0,1),(1,2),(2,3)$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §4.4, p.37

import Mathlib
import Definitions.Def_MWCSherali_CPt

namespace MWCSherali

/-- **Coordinates of the special points of the central region.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), §4.4, p.37:
`o = (1/4, 1/4, 1/4, 1/4)`, `v = (α, 1 − α − β, β, 0)`, `v_{ij}` = `v` with coordinates `i` and `j`
swapped, `h_c = (α, (1−α)/3, (1−α)/3, (1−α)/3)`, `h_s = (1/3, 1/3, 1/3, 0)`,
`h_t = ((1−β)/2, (1−β)/2, β/2, β/2)` (the centres of `Z ∩ K₁`, `Z ∩ Γ₄` and `Z ∩ T₁₂`).

**Formalization Note.** Vectors are written in Lean's 0-based coordinates `t 0, …, t 3`; the
paper's 1-based swaps `v₁₂, v₂₃, v₃₄` exchange Lean coordinates `(0,1)`, `(1,2)`, `(2,3)`:
`v₁₂ = (1−α−β, α, β, 0)`, `v₂₃ = (α, β, 1−α−β, 0)`, `v₃₄ = (α, 1−α−β, 0, β)`. -/
noncomputable def cpt (α β : ℝ) : CPt → Fin 4 → ℝ
  | .o => ![1 / 4, 1 / 4, 1 / 4, 1 / 4]
  | .v => ![α, 1 - α - β, β, 0]
  | .v12 => ![1 - α - β, α, β, 0]
  | .v23 => ![α, β, 1 - α - β, 0]
  | .v34 => ![α, 1 - α - β, 0, β]
  | .hc => ![α, (1 - α) / 3, (1 - α) / 3, (1 - α) / 3]
  | .hs => ![1 / 3, 1 / 3, 1 / 3, 0]
  | .ht => ![(1 - β) / 2, (1 - β) / 2, β / 2, β / 2]

end MWCSherali


