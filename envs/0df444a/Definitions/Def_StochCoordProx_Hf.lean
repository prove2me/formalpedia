-- Prove2me | Definitions.Def_StochCoordProx_Hf
-- name    : StochCoordProx_Hf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:07.168095+00:00
-- url     : https://prove2.me/theorems/31b16dd5-2114-43fc-a165-2ae5af21a37b
-- title:
--   Step parameter $H_{f,U}$ of SCPG
-- statement:
--   Given the constant $L_U$ of the sampled matrix $U$ and a chosen parameter $\eta_U>0$, Algorithm 1 (SCPG) uses
--
--   $$
--   H_{f,U}=\begin{cases}\dfrac{L_U+\eta_U}{2}&\text{if }\psi\text{ is convex along the subspaces from }\mathcal U,\\[1ex] L_U+\eta_U&\text{otherwise.}\end{cases}
--   $$
--
--   The condition "$\psi$ convex along the subspaces from $\mathcal U$" is the global property of Definition 3. It is not a choice made at each step.
--
--   **Formalization Note** The case distinction is decided classically.
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, Algorithm 1 (SCPG), step 1, p.6

import Mathlib
import Definitions.Def_StochCoordProx_ConvexAlongSubspaces

namespace StochCoordProx

open Classical in
/-- **The step parameter `H_{f,U}` of SCPG** (Algorithm 1, step 1): given the smoothness constant
`L_U` of the sampled matrix and the chosen `η_U > 0`,
`H_{f,U} = (L_U + η_U)/2` if `ψ` is convex along the subspaces from `𝒰` (Definition 3), and
`H_{f,U} = L_U + η_U` otherwise.

Necoara & Chorobura, arXiv:2104.13370v3, Algorithm 1 (SCPG), step 1, p.6.

**Formalization Note.** "ψ convex along subspaces from 𝒰" is the single global property
`ConvexAlongSubspaces ψ 𝒰` of the pair `(ψ, 𝒰)`, decided classically; it is not a per-step
choice. The arguments `LU` and `η` are the numbers `L_U` and `η_U`. -/
noncomputable def Hf {n p : ℕ} (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (𝒰 : Set (Matrix (Fin n) (Fin p) ℝ)) (LU η : ℝ) : ℝ :=
  if ConvexAlongSubspaces ψ 𝒰 then (LU + η) / 2 else LU + η

end StochCoordProx


