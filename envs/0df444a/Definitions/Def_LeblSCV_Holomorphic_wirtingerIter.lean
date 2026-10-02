-- Prove2me | Definitions.Def_LeblSCV_Holomorphic_wirtingerIter
-- name    : LeblSCV_Holomorphic_wirtingerIter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:01:35.014116+00:00
-- url     : https://prove2.me/theorems/1d924a84-d4d9-4149-a882-e9fb4a3da9b1
-- title:
--   Multi-index derivative $\partial^{|\alpha|}/\partial z^\alpha$
-- statement:
--   For a multi-index $\alpha = (\alpha_1, \dots, \alpha_n) \in \mathbb{N}_0^n$,
--   $$\frac{\partial^{|\alpha|}}{\partial z^\alpha} = \frac{\partial^{\alpha_1}}{\partial z_1^{\alpha_1}} \frac{\partial^{\alpha_2}}{\partial z_2^{\alpha_2}} \cdots \frac{\partial^{\alpha_n}}{\partial z_n^{\alpha_n}},$$
--   that is, the Wirtinger operator $\partial/\partial z_k$ applied $\alpha_k$ times for each $k$, with $|\alpha| = \alpha_1 + \dots + \alpha_n$.
--
--   **Formalization Note.** Multi-indices are `Fin n → ℕ`. The operators are composed with the $z_n$-derivatives applied first and the $z_1$-derivatives last, matching the written order; for the smooth (holomorphic) functions to which the mission applies it, the order does not matter.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 18 (multi-index notation)

import Mathlib
import Definitions.Def_LeblSCV_Holomorphic_wirtinger

namespace LeblSCV.Holomorphic

/-- Multi-index derivative `∂^{|α|}/∂z^α = ∂^{α_1}/∂z_1^{α_1} ∂^{α_2}/∂z_2^{α_2} ⋯ ∂^{α_n}/∂z_n^{α_n}`
(Lebl, p. 18) for `α ∈ ℕ₀ⁿ` (here `Fin n → ℕ`): the Wirtinger operator `∂/∂z_k` applied `α_k`
times for each `k`, the `z_n`-derivatives innermost and the `z_1`-derivatives outermost. -/
noncomputable def wirtingerIter {n : ℕ} (α : Fin n → ℕ) (f : (Fin n → ℂ) → ℂ) :
    (Fin n → ℂ) → ℂ :=
  (List.finRange n).foldr (fun k g => (wirtinger k)^[α k] g) f

end LeblSCV.Holomorphic


