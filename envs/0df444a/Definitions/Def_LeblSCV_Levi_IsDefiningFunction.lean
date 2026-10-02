-- Prove2me | Definitions.Def_LeblSCV_Levi_IsDefiningFunction
-- name    : LeblSCV_Levi_IsDefiningFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:38:00.69181+00:00
-- url     : https://prove2.me/theorems/f5a111bd-21c7-4edc-b1bb-27f651fba418
-- title:
--   Definition 2.2.1 — defining function of an open set with smooth boundary at $p$
-- statement:
--   Treat $\mathbb{C}^n$ as $\mathbb{R}^{2n}$. Let $U \subset \mathbb{C}^n$ and $p \in \mathbb{C}^n$. A real function $r$ on an open neighbourhood $V$ of $p$ is a **defining function** for $\partial U$ at $p$ (with $r<0$ on $U$) if
--   - $r$ is $C^\infty$ on $V$ and its real derivative never vanishes on $V$;
--   - $\partial U \cap V = \{ x \in V : r(x) = 0 \}$;
--   - $r < 0$ at points of $U \cap V$, and $r > 0$ at points of $V$ not in the closure of $U$.
--
--   **Formalization Note.** `IsDefiningFunction U p V r` is a structure with these fields; `r` is an ambient function `(Fin n → ℂ) → ℝ` whose values off `V` are irrelevant. The book's "$r > 0$ for points not in $U$" is read as "not in $\overline{U}$", since $r = 0$ on $\partial U \cap V$ by the second condition. "Smooth" is $C^\infty$ (`ContDiffOn ℝ ∞`).
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 54, Definition 2.2.1

import Mathlib

open scoped ContDiff

namespace LeblSCV.Levi

/-- Definition 2.2.1 (Lebl, p. 54), `k = ∞`: `r` (on the open neighbourhood `V` of `p`) is a
defining function of the boundary of the open set `U ⊆ ℂⁿ ≅ ℝ^{2n}` at `p`: `r` is smooth on
`V` with nonvanishing real derivative, `∂U ∩ V = {x ∈ V : r x = 0}`, `r < 0` on `U ∩ V` and
`r > 0` at the points of `V` outside the closure of `U`. -/
structure IsDefiningFunction {n : ℕ} (U : Set (Fin n → ℂ)) (p : Fin n → ℂ)
    (V : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ) : Prop where
  isOpen : IsOpen V
  mem : p ∈ V
  smooth : ContDiffOn ℝ ∞ r V
  fderiv_ne_zero : ∀ x ∈ V, fderiv ℝ r x ≠ 0
  frontier_inter : frontier U ∩ V = {x | x ∈ V ∧ r x = 0}
  neg_of_mem : ∀ x ∈ U ∩ V, r x < 0
  pos_of_not_mem_closure : ∀ x ∈ V, x ∉ closure U → 0 < r x

end LeblSCV.Levi


