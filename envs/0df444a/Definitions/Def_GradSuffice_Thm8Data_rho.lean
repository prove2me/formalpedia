-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_rho
-- name    : GradSuffice_Thm8Data_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:21:48.961317+00:00
-- url     : https://prove2.me/theorems/a12a5e8e-a85b-4dcc-85c3-e6bbee076991
-- title:
--   Noisy barriers $\rho_k$
-- statement:
--   The noisy barrier is
--   $$\rho(w)=\max_{\xi\text{ a node of the tree}}\max\{Z^+_\xi+\xi\cdot w,\ -\xi\cdot w+Z^-_\xi\},$$
--   and $\rho_1,\dots,\rho_\kappa$ are independent copies of $\rho$ (each with its own noise variables).
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7, pp.18–19

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data_NoiseIdx

namespace GradSuffice

/-- **The noisy barriers `ρ_k`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7, pp.18–19:
`ρ(w) = max_{ξ a node in the tree} max{Z⁺_ξ + ξ · w, −ξ · w + Z⁻_ξ}`, and `ρ₁, …, ρ_κ` are
independent copies of `ρ`.

**Formalization Note.** Copy `k` uses the noise variables `Z (inl (k, v))` (`Z⁺`) and
`Z (inr (inl (k, v)))` (`Z⁻`) of each node `v`. The maximum over the finitely many nodes is a real
`⨆` over the nonempty finite type of nodes (nonempty since `DL ≥ 1`). -/
noncomputable def Thm8Data.rho {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) (k : Fin c.κ) (Z : c.NoiseIdx → ℝ)
    (w : X) : ℝ :=
  ⨆ v : TreeNode (c.D * thm8L c.θ c.D),
    max (Z (.inl (k, v)) + c.ξ v.1 v.2 w) (-(c.ξ v.1 v.2 w) + Z (.inr (.inl (k, v))))

end GradSuffice


