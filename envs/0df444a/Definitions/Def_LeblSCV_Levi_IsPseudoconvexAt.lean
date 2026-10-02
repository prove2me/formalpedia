-- Prove2me | Definitions.Def_LeblSCV_Levi_IsPseudoconvexAt
-- name    : LeblSCV_Levi_IsPseudoconvexAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:39:23.369583+00:00
-- url     : https://prove2.me/theorems/6723508c-f7ff-4dd8-ad48-eef0f882c2ff
-- title:
--   Definition 2.3.5 — (strongly) pseudoconvex at a boundary point
-- statement:
--   Let $U \subset \mathbb{C}^n$ be an open set with smooth boundary and $p \in \partial U$. $U$ is **(Levi) pseudoconvex at $p$** if, for a defining function $r$ at $p$ with $r < 0$ on $U$,
--   $$\sum_{k=1,\ell=1}^{n} \bar a_k a_\ell \left.\frac{\partial^2 r}{\partial \bar z_k \partial z_\ell}\right|_p \ge 0 \quad\text{for all } X_p = \sum_{k=1}^n a_k \left.\frac{\partial}{\partial z_k}\right|_p \in T^{(1,0)}_p\partial U,$$
--   and **strongly pseudoconvex at $p$** if the inequality is strict for every nonzero such $X_p$.
--
--   **Formalization Note.** The file defines `IsPseudoconvexAt` and `IsStronglyPseudoconvexAt`. Both assert the existence of one defining function with the sign property; by Proposition 2.3.6 (a milestone of this mission) the choice does not matter. The Levi form is compared through its real part, which is the whole value for real $r$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 66, Definition 2.3.5

import Mathlib
import Definitions.Def_LeblSCV_Levi_HasSmoothBoundary
import Definitions.Def_LeblSCV_Levi_holTangent
import Definitions.Def_LeblSCV_Levi_leviForm

namespace LeblSCV.Levi

/-- Definition 2.3.5 (Lebl, p. 66): the open set `U` with smooth boundary is (Levi) pseudoconvex
at `p ∈ ∂U` if, for a defining function `r` at `p` (`r < 0` on `U`), the Levi form is `≥ 0` on
`T_p^{(1,0)} ∂U`. -/
def IsPseudoconvexAt {n : ℕ} (U : Set (Fin n → ℂ)) (p : Fin n → ℂ) : Prop :=
  HasSmoothBoundary U ∧ p ∈ frontier U ∧
    ∃ (V : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ), IsDefiningFunction U p V r ∧
      ∀ a ∈ holTangent r p, 0 ≤ (leviForm r p a).re

/-- Definition 2.3.5 (Lebl, p. 66): strongly pseudoconvex at `p`: the Levi form is `> 0` on every
nonzero `X_p ∈ T_p^{(1,0)} ∂U`. -/
def IsStronglyPseudoconvexAt {n : ℕ} (U : Set (Fin n → ℂ)) (p : Fin n → ℂ) : Prop :=
  HasSmoothBoundary U ∧ p ∈ frontier U ∧
    ∃ (V : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ), IsDefiningFunction U p V r ∧
      ∀ a ∈ holTangent r p, a ≠ 0 → 0 < (leviForm r p a).re

end LeblSCV.Levi


