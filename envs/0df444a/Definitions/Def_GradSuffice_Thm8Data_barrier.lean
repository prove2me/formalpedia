-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_barrier
-- name    : GradSuffice_Thm8Data_barrier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:58.574681+00:00
-- url     : https://prove2.me/theorems/d93fb815-d466-43ce-82bd-395662a4b898
-- title:
--   Barrier term $H_k(y_k(w))$
-- statement:
--   For a noise realization, $H_k(w):=\rho_k(w)+b_{1,k}-2$, and the barrier term of copy $k$ is $H_k(y_k(w))$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7, p.19

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data_rho
import Definitions.Def_GradSuffice_Thm8Data_y
import Definitions.Def_GradSuffice_Thm8Data_b

namespace GradSuffice

/-- **The barrier term `H_k(y_k(w))`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7, p.19: `H_k(w) := ρ_k(w) + b_{1,k} − 2`,
evaluated at `y_k(w)`.

**Formalization Note.** 0-based: `b_{1,k}` is `b 0 k`. -/
noncomputable def Thm8Data.barrier {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) (k : Fin c.κ) (Z : c.NoiseIdx → ℝ)
    (w : X) : ℝ :=
  c.rho k Z (c.y k w) + c.b 0 k - 2

end GradSuffice


