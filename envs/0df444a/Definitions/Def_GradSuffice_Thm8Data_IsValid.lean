-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_IsValid
-- name    : GradSuffice_Thm8Data_IsValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:34.886563+00:00
-- url     : https://prove2.me/theorems/1200f80d-af7e-43a5-967c-379274d6e006
-- title:
--   Standing assumptions of the Theorem 8 construction
-- statement:
--   The data of the Theorem 8 construction are **valid** for a set $W\subseteq X$ if
--   1. $W$ is a convex, symmetric subset of the unit ball $B$;
--   2. $0<\theta<1$, $D\ge1$ and $0<\nu\le\theta/(512D)$;
--   3. the tree $\bar\xi$ is $B^\star$-valued;
--   4. for each $k$, $w_{\sigma_k}\in W$ realizes the branch $\sigma_k$ at margin $\theta$: $\sigma_{k,i}\,\xi_i(\sigma_{k,<i})\cdot w_{\sigma_k}\ge\theta$ for every level $i$.
--
--   **Formalization Note** $D\ge1$ is a free parameter here. In the paper $D=\lfloor(\theta^2m/(65536\log(16m^2)))^{1/3}\rfloor$ for the depth $m$ of the original shattered tree, which is then cut to depth $DL$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 8 and §7, pp.18–19

import Mathlib
import Definitions.Def_NondualOpt_histPrefix
import Definitions.Def_GradSuffice_signR
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_Thm8Data

namespace GradSuffice

/-- **Standing assumptions of the Theorem 8 construction.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 8 and §7, pp.18–19:
`W ⊆ B` is convex and symmetric, the tree is `B⋆`-valued, the margin satisfies `0 < θ < 1`,
`D ≥ 1`, the noise level satisfies `0 < ν ≤ θ/(512D)` (p.19), and `w_{σ_k} ∈ W` is the witness for
branch `σ_k` of the tree, shattered at margin `θ` (Eq. (6) along `σ_k`).

**Formalization Note.** `D` is a free parameter `≥ 1` here; in the paper it is
`⌊(θ²m/(65536 log(16m²)))^{1/3}⌋` for the depth `m` of the original tree, which is then truncated
to depth `DL`. -/
def Thm8Data.IsValid {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) (W : Set X) : Prop :=
  W ⊆ Metric.closedBall 0 1 ∧ Convex ℝ W ∧ (∀ w ∈ W, -w ∈ W) ∧
  0 < c.θ ∧ c.θ < 1 ∧ 1 ≤ c.D ∧ 0 < c.ν ∧ c.ν ≤ c.θ / (512 * c.D) ∧
  IsDualValued c.ξ ∧
  ∀ k : Fin c.κ, c.wσ k ∈ W ∧
    ∀ i : Fin (c.D * thm8L c.θ c.D),
      c.θ ≤ signR (c.σ k i) * c.ξ i (NondualOpt.histPrefix (c.σ k) i) (c.wσ k)

end GradSuffice


