-- Prove2me | Definitions.Def_WhittFLT_FirstPassage_M1
-- name    : WhittFLT_FirstPassage_M1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:31.244255+00:00
-- url     : https://prove2.me/theorems/01dcb8de-2a94-4459-b942-eca1dde159d5
-- title:
--   Skorohod's M₁ convergence on D([0, ∞), ℝ), with the origin convention x(0−) = 0
-- statement:
--   The paper uses Skorohod's (1956) $M_1$ topology (§6, p. 80) without defining it. This file fixes the definition used in the mission, for real-valued paths on $[0,\infty)$.
--
--   1. **Left limits.** $x(t-)$ is the left limit of $x$ at $t>0$, and at the origin $x(0-):=0$.
--   2. **Completed graph.** For $b>0$, the completed graph of $x$ on $[0,b]$ is $$\Gamma_x=\{(t,z): 0\le t\le b,\ z=\alpha\,x(t-)+(1-\alpha)\,x(t)\text{ for some }\alpha\in[0,1]\}.$$ At a jump it contains the vertical segment from $x(t-)$ to $x(t)$; at the origin it contains the segment from $0$ to $x(0)$.
--   3. **Order and parametric representations.** $(t_1,z_1)\le(t_2,z_2)$ if $t_1<t_2$, or $t_1=t_2$ and $|z_1-x(t_1-)|\le|z_2-x(t_1-)|$. A parametric representation of $\Gamma_x$ is a continuous map $s\mapsto(r(s),u(s))$ from $[0,1]$ onto $\Gamma_x$ that is nondecreasing for this order.
--   4. **$M_1$ convergence on $[0,b]$.** $x_n\to x$ when for every $\varepsilon>0$, for all large $n$, there are parametric representations $(r_n,u_n)$ of $\Gamma_{x_n}$ and $(r,u)$ of $\Gamma_x$ with $$\sup_{0\le s\le1}|u_n(s)-u(s)|<\varepsilon,\qquad \sup_{0\le s\le1}|r_n(s)-r(s)|<\varepsilon.$$
--   5. **$M_1$ convergence on $[0,\infty)$.** $x_n\to x(M_1)$ when every $x_n$ and $x$ lie in $D([0,\infty),\mathbb R)$ and the restrictions converge in $M_1$ on $[0,b]$ for every $b>0$ at which $x$ is continuous.
--
--   This is the topology in which the first passage time map is continuous (Theorem 7.1), and through which the paper proves the $J_1$ continuity at strictly increasing paths (Theorem 7.2).
--
--   **Formalization Note** The construction follows Skorohod and Whitt and is adapted from `ChenWhitt93.JumpDiffusion.M1`, with one change: at the origin the left limit is $0$ instead of $x(0)$. With the convention $x(0-)=x(0)$ Theorem 7.1 is false on $E$: for $x(s)=(s-1)^+$ and $x_n=x+1/n$ (all in $E$, $x_n\to x$ uniformly) one has $x_n^{-1}(t)=0$ for $t<1/n$ while $x^{-1}(0)=1$, so the graphs of $x_n^{-1}$ start at $(0,0)$ and that of $x^{-1}$ at $(0,1)$. With $x(0-)=0$ the graph of $x^{-1}$ contains the segment from $(0,0)$ to $(0,1)$ and the convergence holds. This is the convention Whitt later calls $M_1'$ (*Stochastic-Process Limits*, 2002, §13.6). It is weaker than standard $M_1$ only at the origin: the value at $0$ is no longer matched. The monotone motion along each jump segment (the order in item 3) is part of the standard definition.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §6, p. 80 (M₁ used, not defined); proof of Theorem 7.1, p. 82 (completed graphs, parametric representations); Skorohod (1956)

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.FirstPassage

open Set Filter Topology

/-!
Skorohod's (1956) `M₁` topology on `D([0, ∞), ℝ)`, which Whitt (1980) uses in §§6–7 (p. 80) without
defining it. The text is adapted from `ChenWhitt93.JumpDiffusion.M1` (completed graph, its order,
parametric representations), specialised to real-valued paths on `[0, b]`, with one change: the left
limit at the origin is `0` (`x(0−) := 0`), so the completed graph of `x` on `[0, b]` contains the
vertical segment from `(0, 0)` to `(0, x(0))`.
-/

/-- The left limit of `x` at `t`, with the convention `x(0−) = 0` at the origin; for `t ≠ 0` it is
`Function.leftLim x t` (which is `x t` when the left limit does not exist). -/
noncomputable def leftLim0 (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t = 0 then 0 else Function.leftLim x t

/-- The completed graph of the restriction of `x` to `[0, b]`: the pairs `(t, z)` with
`t ∈ [0, b]` and `z = α x(t−) + (1 − α) x(t)` for some `α ∈ [0, 1]`, where `x(0−) = 0`. -/
def completedGraph (b : ℝ) (x : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc 0 b ∧ ∃ α ∈ Icc (0 : ℝ) 1, p.2 = α * leftLim0 x p.1 + (1 - α) * x p.1}

/-- The order of the completed graph: `(t₁, z₁) ≤ (t₂, z₂)` if `t₁ < t₂`, or `t₁ = t₂` and `z₁` is
at most as far from `x(t₁−)` as `z₂` along the jump segment. -/
def graphLE (x : ℝ → ℝ) (p q : ℝ × ℝ) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ |p.2 - leftLim0 x p.1| ≤ |q.2 - leftLim0 x q.1|)

/-- A parametric representation of the completed graph of `x` on `[0, b]`: a continuous map
`s ↦ (r s, u s)` from `[0, 1]` onto the completed graph, nondecreasing for `graphLE`. -/
def IsParamRep (b : ℝ) (x : ℝ → ℝ) (r u : ℝ → ℝ) : Prop :=
  ContinuousOn r (Icc 0 1) ∧ ContinuousOn u (Icc 0 1) ∧
  (fun s => (r s, u s)) '' Icc 0 1 = completedGraph b x ∧
  ∀ s₁ ∈ Icc (0 : ℝ) 1, ∀ s₂ ∈ Icc (0 : ℝ) 1, s₁ ≤ s₂ →
    graphLE x (r s₁, u s₁) (r s₂, u s₂)

/-- `xₙ → x` in `M₁` on `[0, b]`: for every `ε > 0`, eventually there are parametric
representations `(r', u')` of `xₙ` and `(r, u)` of `x` on `[0, b]` that are uniformly `ε`-close in
both components. -/
def M1TendstoOn (b : ℝ) (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∃ r' u' r u : ℝ → ℝ,
    IsParamRep b (xs n) r' u' ∧ IsParamRep b x r u ∧
    ∀ s ∈ Icc (0 : ℝ) 1, |u' s - u s| < ε ∧ |r' s - r s| < ε

/-- `xₙ → x(M₁)` in `D([0, ∞), ℝ)`: every path is càdlàg on `[0, ∞)` and the restrictions
converge in `M₁` on `[0, b]` for every `b > 0` at which `x` is continuous. -/
def M1Tendsto (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  (∀ n, WhittFLT.Composition.IsCadlagOn (Ici 0) (xs n)) ∧ WhittFLT.Composition.IsCadlagOn (Ici 0) x ∧
    ∀ b : ℝ, 0 < b → ContinuousAt x b → M1TendstoOn b xs x

end WhittFLT.FirstPassage


