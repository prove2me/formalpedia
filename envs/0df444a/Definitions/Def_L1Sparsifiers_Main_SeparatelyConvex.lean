-- Prove2me | Definitions.Def_L1Sparsifiers_Main_SeparatelyConvex
-- name    : L1Sparsifiers_Main_SeparatelyConvex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:14.124217+00:00
-- url     : https://prove2.me/theorems/8050b5a0-c2bf-4e89-aecd-c4cffe78b2bd
-- title:
--   Separately convex functions on $\Omega^m$
-- statement:
--   Let $\Omega\subseteq\mathbb R$ be convex. A function $f:\Omega^m\to\mathbb R$ is **separately convex** if for every $t\in\Omega^m$ and every $j\in[m]$ the function
--   $$s\mapsto f(t+s e_j)$$
--   is convex (on the interval of $s$ for which $t+se_j\in\Omega^m$). Separate convexity is convexity in each coordinate with the others fixed; it does not imply joint convexity (for instance $f(x)=-x_1x_2$ is separately convex but not convex).
--
--   The paper uses it with $\Omega=[-1,1]$ (functions on the cube) and $\Omega=\mathbb R_{\ge0}$ (volumes of eroded bodies as functions of segment lengths).
--
--   **Formalization Note** $f$ is a total function on $\mathbb R^m$ and only its values on $\Omega^m$ are constrained. Since $t+se_j$ stays in $\Omega^m$ exactly when its $j$-th coordinate lies in $\Omega$, the condition is written as convexity on $\Omega$ of $u\mapsto f(t_1,\dots,t_{j-1},u,t_{j+1},\dots,t_m)$, for every $t\in\Omega^m$.
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §2, 'Convex functions', p.7

import Mathlib

namespace L1Sparsifiers.Main

/-- **Separately convex function on `Ω^m`** (§2, "Convex functions", p.7): for a convex
`Ω ⊆ ℝ`, `f : Ω^m → ℝ` is separately convex if for every `t ∈ Ω^m` and `j ∈ [m]` the function
`s ↦ f(t + s eⱼ)` is convex (on the set of `s` with `t + s eⱼ ∈ Ω^m`). This does not imply joint
convexity.

**Formalization Note.** `f` is a total function on `ℝ^m`; only its values on `Ω^m` matter. The
line `t + s eⱼ` through `t ∈ Ω^m` stays in `Ω^m` exactly when its `j`-th coordinate lies in `Ω`, so
the condition is written as convexity on `Ω` of `u ↦ f(t with tⱼ replaced by u)`. -/
def SepConvexOn {m : ℕ} (Ω : Set ℝ) (f : (Fin m → ℝ) → ℝ) : Prop :=
  ∀ t : Fin m → ℝ, (∀ i, t i ∈ Ω) → ∀ j : Fin m, ConvexOn ℝ Ω (fun u => f (Function.update t j u))

end L1Sparsifiers.Main


