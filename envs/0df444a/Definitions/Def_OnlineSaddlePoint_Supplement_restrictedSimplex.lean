-- Prove2me | Definitions.Def_OnlineSaddlePoint_Supplement_restrictedSimplex
-- name    : OnlineSaddlePoint_Supplement_restrictedSimplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:50:42.168193+00:00
-- url     : https://prove2.me/theorems/1dc2031c-0db5-4873-99c3-ed0a6de696ca
-- title:
--   Restricted simplex $\Delta_\theta$, display (10)
-- statement:
--   For $d\in\mathbb N$ and $\theta\in\mathbb R$ the **restricted simplex** is
--
--   $$
--   \Delta_\theta=\{z\in\mathbb R^d:\ \|z\|_1=1,\ z_i\ge\theta\ \text{for } i=1,\dots,d\}.
--   $$
--
--   For $\theta=0$ it is the probability simplex $\Delta=\{x\in\mathbb R^d: x\ge0,\ \|x\|_1=1\}$ of mixed strategies over $d$ actions; for $0<\theta\le1/d$ it is the set of mixed strategies that play every action with probability at least $\theta$, and for $\theta>1/d$ it is empty. The paper writes $\Delta_{X,\theta}$, $\Delta_{Y,\theta}$ for the two players' restricted simplexes in dimensions $d_1$, $d_2$.
--
--   On $\Delta_\theta$ with $\theta>0$ the negative entropy is Lipschitz, which is why OMG-RFTL plays there.
--
--   **Formalization Note** $\mathbb R^d$ with the $\ell_1$ norm is `PiLp 1 (fun _ : Fin d => ℝ)`. Every statement of the mission takes $\theta\ge0$, where $\|z\|_1=1$ with $z\ge\theta$ is the same as $\sum_i z_i=1$ with $z\ge\theta$.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, display (10), p.16; probability simplex, p.15

import Mathlib

namespace OnlineSaddlePoint.Supplement

/-- **Restricted simplex** `Δ_θ`. Rivera Cardoso, Wang, Xu, arXiv:1806.08301v3, display (10), p.16:
"`Δ_θ = {z ∈ ℝ^d : ‖z‖₁ = 1, z_i ≥ θ, i = 1, ..., d}`. The tuning parameter `θ ∈ [0, 1/d]` …
(Notice that when `θ > 1/d`, the set is empty.)" With `θ = 0` it is the probability simplex
`Δ = {x ∈ ℝ^d : x ≥ 0, ‖x‖₁ = 1}` of p.15; `Δ_{X,θ}` and `Δ_{Y,θ}` are `restrictedSimplex d₁ θ` and
`restrictedSimplex d₂ θ`.

**Formalization Note.** `ℝ^d` with the `ℓ₁` norm is `PiLp 1 (fun _ : Fin d => ℝ)`, whose norm is
`‖z‖ = ∑ i, |z i|` (`PiLp.norm_eq_of_L1`); coordinates are `z i` for `i : Fin d`. Every statement
of this mission that uses the set takes `θ ≥ 0`, where `‖z‖₁ = 1` with `z ≥ θ` is the same as
`∑ i, z i = 1` with `z ≥ θ`. -/
def restrictedSimplex (d : ℕ) (θ : ℝ) : Set (PiLp 1 (fun _ : Fin d => ℝ)) :=
  {z | ‖z‖ = 1 ∧ ∀ i, θ ≤ z i}

end OnlineSaddlePoint.Supplement


