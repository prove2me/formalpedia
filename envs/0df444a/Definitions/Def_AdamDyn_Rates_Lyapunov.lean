-- Prove2me | Definitions.Def_AdamDyn_Rates_Lyapunov
-- name    : AdamDyn_Rates_Lyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:01:53.883965+00:00
-- url     : https://prove2.me/theorems/7ecad9cb-3a28-4471-8b34-8b2fa614daf6
-- title:
--   The Lyapunov functions $U$, $V$ (3.4)–(3.5), $\tilde W_\delta$ (7.11) and $w_\delta(t)=\tilde W_\delta(t,z(t))$
-- statement:
--   Let $a,b,\varepsilon>0$, $F:\mathbb R^d\to\mathbb R$ and $S:\mathbb R^d\to\mathbb R^d$. For $t>0$ and $v\in[0,+\infty)^d$ define the vector $U(t,v)$ coordinatewise by
--
--   $$U_i(t,v)=a\,(1-e^{-at})\left(\varepsilon+\sqrt{\frac{v_i}{1-e^{-bt}}}\right),$$
--
--   and for $z=(x,m,v)$ define
--
--   $$V(t,z)=F(x)+\tfrac12\|m\|^2_{U(t,v)^{-1}}=F(x)+\frac12\sum_{i=1}^d\frac{m_i^2}{U_i(t,v)}.$$
--
--   For $\delta>0$ the perturbed function of the convergence-rate proof is
--
--   $$\tilde W_\delta(t,(x,m,v))=V(t,(x,m,v))-\delta\langle\nabla F(x),m\rangle+\delta\|S(x)-v\|^2,$$
--
--   and along a trajectory $z(\cdot)$ one writes $w_\delta(t):=\tilde W_\delta(t,z(t))$.
--
--   $V$ is the Lyapunov function of the non-autonomous Adam ODE: it decreases along solutions when $0<b\le 4a$. The correction terms in $\tilde W_\delta$ make its time derivative control $\|\nabla F(x)\|^2$ and $\|S(x)-v\|^2$ as well as $\|m\|^2$, which is what the Łojasiewicz argument needs.
--
--   **Formalization Note** Norms and inner products on $\mathbb R^d$ are Euclidean (`EuclideanSpace ℝ (Fin d)`). The formulas are meaningful for $t>0$ and $v\ge0$, the domain the paper uses; outside it Lean's conventions ($\sqrt{\cdot}$ of a negative number is $0$, $0^{-1}=0$) give junk values, which no statement here evaluates.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 5, Eqs. (3.4)–(3.5); p. 20, Eq. (7.11) and the definition of w_δ

import Mathlib

open Real

namespace AdamDyn.Rates

/-- The map `U(t, v) = a(1 − e^{−at})(ε + √(v / (1 − e^{−bt})))` of Barakat–Bianchi, Eq. (3.5),
p. 5, coordinatewise, for `t > 0` and `v ∈ [0, +∞)^d`. -/
noncomputable def U {d : ℕ} (a b ε t : ℝ) (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) : ℝ :=
  a * (1 - exp (-a * t)) * (ε + √(v i / (1 - exp (-b * t))))

/-- The Lyapunov function `V(t, z) = F(x) + ½ ‖m‖²_{U(t,v)^{−1}} = F(x) + ½ Σᵢ mᵢ² / Uᵢ(t, v)` of
Barakat–Bianchi, Eq. (3.4), p. 5, for `t > 0` and `z = (x, m, v) ∈ 𝒵₊`. -/
noncomputable def V {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (a b ε t : ℝ)
    (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ :=
  F z.1 + (1 / 2) * ∑ i, (U a b ε t z.2.2 i)⁻¹ * (z.2.1 i) ^ 2

/-- The perturbed non-autonomous Lyapunov function of Barakat–Bianchi, Eq. (7.11), p. 20:
`W̃_δ(t, (x, m, v)) = V(t, (x, m, v)) − δ⟨∇F(x), m⟩ + δ‖S(x) − v‖²`. -/
noncomputable def Wtilde {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a b ε δ t : ℝ)
    (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ :=
  V F a b ε t z - δ * inner ℝ (gradient F z.1) z.2.1 + δ * ‖S z.1 - z.2.2‖ ^ 2

/-- `w_δ(t) := W̃_δ(t, z(t))` along a trajectory `z` (Barakat–Bianchi, §7.4, p. 20). -/
noncomputable def wδ {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a b ε δ : ℝ)
    (z : ℝ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
    (t : ℝ) : ℝ :=
  Wtilde F S a b ε δ t (z t)

end AdamDyn.Rates


