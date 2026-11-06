-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_NoiseIdx
-- name    : GradSuffice_Thm8Data_NoiseIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:32.803701+00:00
-- url     : https://prove2.me/theorems/82904825-a8ed-4c77-bf46-9404a45d5e1f
-- title:
--   Index set of the auxiliary noise of Theorem 8
-- statement:
--   The construction of Theorem 8 uses independent auxiliary noise variables: for each copy $k$ and each node $\xi$ of the tree a pair $Z^+_\xi$, $Z^-_\xi$ (the copy $\rho_k$ of the barrier $\rho$ has its own pair), and for each $t\le D$, $k\le\kappa$ a variable $Z_{t,k}$. This finite type indexes them.
--
--   **Formalization Note** `inl (k, v)` indexes $Z^+$ of node $v$ in copy $k$, `inr (inl (k, v))` indexes $Z^-$, and `inr (inr (t, k))` indexes $Z_{t,k}$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7, p.19

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data
import Definitions.Def_GradSuffice_TreeNode

namespace GradSuffice

/-- **Index set of the auxiliary noise.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7, p.19: the variables `Z⁺_ξ`, `Z⁻_ξ` of the
barrier `ρ` (one pair per node of the tree, for each of the `κ` independent copies `ρ₁, …, ρ_κ`)
and the variables `Z_{t,k}`, `t ≤ D`, `k ≤ κ`.

**Formalization Note.** `inl (k, v)` indexes `Z⁺` of node `v` in copy `k`, `inr (inl (k, v))`
indexes `Z⁻`, and `inr (inr (t, k))` indexes `Z_{t,k}` (0-based `t`, `k`). -/
abbrev Thm8Data.NoiseIdx {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) : Type :=
  (Fin c.κ × TreeNode (c.D * thm8L c.θ c.D)) ⊕
    ((Fin c.κ × TreeNode (c.D * thm8L c.θ c.D)) ⊕ (Fin c.D × Fin c.κ))

end GradSuffice


