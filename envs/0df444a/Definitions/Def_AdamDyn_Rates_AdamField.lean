-- Prove2me | Definitions.Def_AdamDyn_Rates_AdamField
-- name    : AdamDyn_Rates_AdamField
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:01:47.891358+00:00
-- url     : https://prove2.me/theorems/a034a5e1-1581-4f6d-86eb-4078ba188d78
-- title:
--   The continuous-time Adam vector field $h(t,z)$ (3.3) and global solutions of (ODE) from $(x_0,0,0)$
-- statement:
--   Fix $d\in\mathbb N$, constants $a,b,\varepsilon$, a function $F:\mathbb R^d\to\mathbb R$ with gradient $\nabla F$ and a map $S:\mathbb R^d\to\mathbb R^d$. Points of $\mathcal Z=\mathbb R^d\times\mathbb R^d\times\mathbb R^d$ are written $z=(x,m,v)$; $\mathcal Z_+=\mathbb R^d\times\mathbb R^d\times[0,+\infty)^d$. For $t>0$ the **continuous-time Adam vector field** is
--
--   $$h(t,z)=\begin{pmatrix} -\dfrac{(1-e^{-at})^{-1}\,m}{\varepsilon+\sqrt{(1-e^{-bt})^{-1}\,|v|}}\\[2mm] a(\nabla F(x)-m)\\[1mm] b(S(x)-v)\end{pmatrix},$$
--
--   where the first block is computed coordinatewise. On $\mathcal Z_+$ one has $|v|=v$; the absolute value is the paper's extension of $h$ to all of $\mathcal Z$.
--
--   The Adam ODE is $\dot z(t)=h(t,z(t))$. A map $z:[0,+\infty)\to\mathcal Z_+$ is a **global solution with initial condition $(x_0,0,0)$** if
--
--   1. $z$ is continuous on $[0,+\infty)$ and takes values in $\mathcal Z_+$ (the $v$ block is coordinatewise nonnegative);
--   2. $z$ is continuously differentiable on $(0,+\infty)$;
--   3. $\dot z(t)=h(t,z(t))$ for every $t>0$;
--   4. $z(0)=(x_0,0,0)$.
--
--   This ODE is the small-step limit of the Adam algorithm with bias correction; the factors $(1-e^{-at})^{-1}$ and $(1-e^{-bt})^{-1}$ are the continuous-time counterpart of the debiasing steps, and they make $h$ singular at $t=0$.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and $\mathcal Z$ is the product `E × E × E`. A solution is a map `ℝ → E × E × E`; only its values on $[0,+\infty)$ are constrained, so uniqueness statements must compare solutions on $[0,+\infty)$ only. The field is meaningful only for $t>0$ (at $t=0$ Lean's $0^{-1}=0$ would give a junk value); the ODE is required only at $t>0$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 5, Eq. (3.3), (ODE) and the definition of global solution; p. 12 (extension by |v|)

import Mathlib

open Real

namespace AdamDyn.Rates

/-- The continuous-time Adam vector field `h(t, z)` of Barakat–Bianchi, Eq. (3.3), p. 5, for
`t > 0` and `z = (x, m, v)`:
`h(t, z) = ( −(1 − e^{−at})^{−1} m / (ε + √((1 − e^{−bt})^{−1} |v|)), a(∇F(x) − m), b(S(x) − v) )`,
the first block coordinatewise. The `|v|` is the paper's extension of `h` from `𝒵₊` to `𝒵` (p. 12);
on `𝒵₊` it is `v`. The formula is only meaningful for `t > 0`. -/
noncomputable def adamField {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a b ε t : ℝ)
    (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) :=
  (WithLp.toLp 2 (fun i => -((1 - exp (-a * t))⁻¹ * z.2.1 i /
      (ε + √((1 - exp (-b * t))⁻¹ * |z.2.2 i|)))),
    a • (gradient F z.1 - z.2.1),
    b • (S z.1 - z.2.2))

/-- A global solution to (ODE) `ż(t) = h(t, z(t))` with initial condition `(x0, 0, 0)`
(Barakat–Bianchi, p. 5): `z` is continuous on `[0, +∞)` with values in
`𝒵₊ = ℝ^d × ℝ^d × [0, +∞)^d`, continuously differentiable on `(0, +∞)`, satisfies the ODE at every
`t > 0`, and `z(0) = (x0, 0, 0)`. The map is defined on `ℝ`; only its restriction to `[0, +∞)`
matters. -/
def IsGlobalSolution {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a b ε : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d))
    (z : ℝ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    Prop :=
  ContinuousOn z (Set.Ici 0) ∧
  (∀ t, 0 ≤ t → ∀ i, 0 ≤ (z t).2.2 i) ∧
  ContDiffOn ℝ 1 z (Set.Ioi 0) ∧
  (∀ t, 0 < t → HasDerivAt z (adamField F S a b ε t (z t)) t) ∧
  z 0 = (x0, 0, 0)

end AdamDyn.Rates


