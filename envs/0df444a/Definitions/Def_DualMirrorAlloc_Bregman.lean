-- Prove2me | Definitions.Def_DualMirrorAlloc_Bregman
-- name    : DualMirrorAlloc_Bregman
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:01:52.106165+00:00
-- url     : https://prove2.me/theorems/a274e3e6-1a31-44c3-905d-b406efe1086b
-- title:
--   Bregman divergence on $\mathbb R^m_+$, $\ell_1$ strong convexity, essential smoothness, Assumption 2
-- statement:
--   This module fixes the reference-function vocabulary of dual mirror descent.
--
--   1. The **nonnegative orthant** $\mathbb R^m_+=\{\mu\in\mathbb R^m:\mu\ge0\}$ and the **$\ell_1$ norm** $\|v\|_1=\sum_j|v_j|$.
--   2. The **Bregman divergence** of a reference function $h$ relative to a set $D\subseteq\mathbb R^m$,
--   $$
--   V_h(x,y)=h(x)-h(y)-\nabla h(y)^\top(x-y),
--   $$
--   where $\nabla h(y)$ is the derivative of $h$ at $y$ within $D$.
--   3. **$\sigma$-strong convexity in $\|\cdot\|_1$ on $D$**: $h(\mu_1)\ge h(\mu_2)+\nabla h(\mu_2)^\top(\mu_1-\mu_2)+\frac\sigma2\|\mu_1-\mu_2\|_1^2$ for all $\mu_1,\mu_2\in D$ such that $\nabla h(\mu_2)$ exists.
--   4. **Essential smoothness in $\mathbb R^m_+$**: $h$ is differentiable on the open orthant and $\|\nabla h(\nu)\|\to\infty$ as $\nu$ approaches any boundary point of $\mathbb R^m_+$ from the open orthant.
--   5. **Assumption 2** with modulus $\sigma$: $h$ is differentiable in $\mathbb R^m_+$ or essentially smooth in $\mathbb R^m_+$, and $h$ is $\sigma$-strongly convex in $\|\cdot\|_1$ on $\mathbb R^m_+$.
--
--   These are the hypotheses on the reference function under which the dual update (4) of Algorithm 1 is well defined and mirror descent has regret $O(\eta T+1/\eta)$.
--
--   **Formalization Note** $\mathbb R^m$ is `Fin m → ℝ`. $\nabla h(y)$ is `fderivWithin ℝ h D y`; on the orthant (convex with nonempty interior) it is unique and equals the gradient wherever $h$ is differentiable. At a point where $h$ is not differentiable within $D$, Lean returns the zero map, so strong convexity is only required at points where the derivative exists, and every use of $V_h(\cdot,y)$ in the mission assumes differentiability at $y$. Essential smoothness is the notion of Bauschke, Borwein and Combettes (2001) with domain $\mathbb R^m_+$; convexity is supplied by part 2 of Assumption 2. "Differentiable in $\mathbb R^m_+$" is differentiability within the orthant (one-sided at the boundary).
-- source:
--   Balseiro–Lu–Mirrokni, The Best of Many Worlds: Dual Mirror Descent for Online Allocation Problems, arXiv:2011.10124v3, Algorithm 1 (Bregman divergence), p.11; §2.3 Assumption 2, p.13; Appendix G, Proposition 5, p.59

import Mathlib

open Filter Topology

namespace DualMirrorAlloc

/-- **The nonnegative orthant `ℝ^m_+`.** Balseiro–Lu–Mirrokni, *The Best of Many Worlds: Dual
Mirror Descent for Online Allocation Problems*, arXiv:2011.10124v3, §2.1, p.10: the dual variables
`µ ∈ ℝ^m_+`.

**Formalization Note.** `ℝ^m` is `Fin m → ℝ` and `ℝ^m_+ = {µ | 0 ≤ µ}` (coordinatewise). -/
def orthant (m : ℕ) : Set (Fin m → ℝ) := Set.Ici 0

/-- **The `ℓ₁` norm `‖v‖₁ = Σ_j |v_j|`.** arXiv:2011.10124v3, §2.3, p.13: "We equip … the
Lagrangian dual space with the ℓ1 norm ‖·‖1".

**Formalization Note.** Written as an explicit sum: Mathlib's `‖·‖` on `Fin m → ℝ` is the sup
norm, so it is not used for `‖·‖₁`. -/
def l1norm {m : ℕ} (v : Fin m → ℝ) : ℝ := ∑ j, |v j|

/-- **The Bregman divergence `V_h(x, y) = h(x) − h(y) − ∇h(y)ᵀ(x − y)` relative to a set `D`.**
arXiv:2011.10124v3, Algorithm 1, p.11 ("where Vh(x, y) = h(x) − h(y) − ∇h(y)⊤(x − y) is the
Bregman divergence"), and Proposition 5, p.59 (on a convex set `D ⊆ ℝ^m`).

**Formalization Note.** `∇h(y)ᵀ(x − y)` is `fderivWithin ℝ h D y (x − y)`, the derivative of `h`
at `y` within `D`. The mission uses `D = ℝ^m_+` (`orthant m`) for Algorithm 1 and Assumption 2,
and a general convex `D` for Proposition 5. On `ℝ^m_+` (convex with nonempty interior) the
derivative within `D` is unique, and it equals the gradient of `h` wherever `h` is differentiable
on `ℝ^m`. At a point `y` where `h` is not differentiable within `D`, Lean's `fderivWithin` is `0`:
every hypothesis of the mission that uses `V_h(·, y)` requires differentiability at `y`. -/
noncomputable def bregman {m : ℕ} (D : Set (Fin m → ℝ)) (h : (Fin m → ℝ) → ℝ)
    (x y : Fin m → ℝ) : ℝ :=
  h x - h y - fderivWithin ℝ h D y (x - y)

/-- **σ-strong convexity in `‖·‖₁` on a set `D`** (gradient form). arXiv:2011.10124v3, Assumption
2.2, p.13: "h(µ) is σ-strongly convex in ∥·∥1-norm in Rm+, i.e., h(µ1) ≥ h(µ2) + ∇h(µ2)⊤(µ1 − µ2) +
σ/2 ∥µ1 − µ2∥1² for any µ1, µ2 ∈ Rm+"; Proposition 5, p.59, with `D` in place of `ℝ^m_+`.

**Formalization Note.** The inequality is required at every `µ₁ ∈ D` and at every `µ₂ ∈ D` at
which `h` is differentiable within `D`, since `∇h(µ₂)` exists only there. Without this guard, the
junk value `fderivWithin = 0` at a non-differentiable boundary point would add the condition
`h(µ₁) ≥ h(µ₂) + σ/2‖µ₁ − µ₂‖₁²`, which the paper does not state. When `h` is differentiable within
`D` everywhere (the first branch of Assumption 2.1), the guard is vacuous. -/
def IsStronglyConvexL1 {m : ℕ} (D : Set (Fin m → ℝ)) (h : (Fin m → ℝ) → ℝ) (σ : ℝ) : Prop :=
  ∀ mu₁ ∈ D, ∀ mu₂ ∈ D, DifferentiableWithinAt ℝ h D mu₂ →
    h mu₂ + fderivWithin ℝ h D mu₂ (mu₁ - mu₂) + σ / 2 * (l1norm (mu₁ - mu₂)) ^ 2 ≤ h mu₁

/-- **Essential smoothness in `ℝ^m_+`.** arXiv:2011.10124v3, Assumption 2.1, p.13: "h(µ) is either
differentiable or essentially smooth (Bauschke et al., 2001) in Rm+". Following Bauschke, Borwein
and Combettes (2001) and Rockafellar (*Convex Analysis*, §26), with domain `ℝ^m_+`: `h` is
differentiable at every point of the open orthant `int ℝ^m_+`, and `‖∇h(ν)‖ → ∞` as `ν → µ` within
`int ℝ^m_+`, for every boundary point `µ` of `ℝ^m_+`.

**Formalization Note.** This is the cited notion restricted to the domain `ℝ^m_+`: the paper's `h`
is real valued and only its restriction to `ℝ^m_+` is used. Convexity, which the cited definition
presupposes, is supplied by Assumption 2.2 (`IsStronglyConvexL1`). The norm of `fderiv ℝ h ν` is
the operator norm; all norms on `ℝ^m` are equivalent, so the blow-up condition does not depend on
the choice. -/
def IsEssentiallySmoothOrthant {m : ℕ} (h : (Fin m → ℝ) → ℝ) : Prop :=
  (∀ mu ∈ interior (orthant m), DifferentiableAt ℝ h mu) ∧
    ∀ mu ∈ frontier (orthant m),
      Tendsto (fun ν => ‖fderiv ℝ h ν‖) (𝓝[interior (orthant m)] mu) atTop

/-- **Assumption 2 (assumptions on the reference function), p.13**, with modulus `σ`:
1. `h` is differentiable in `ℝ^m_+` or essentially smooth in `ℝ^m_+`;
2. `h` is `σ`-strongly convex in `‖·‖₁` on `ℝ^m_+`.

**Formalization Note.** Branch 1(a), "differentiable in `ℝ^m_+`", is `DifferentiableOn ℝ h ℝ^m_+`
(one-sided at the boundary, the weaker of the two readings). Branch 1(b) is
`IsEssentiallySmoothOrthant`. Both branches are kept. `σ > 0` is a separate hypothesis of every
theorem. -/
def Assumption2 {m : ℕ} (h : (Fin m → ℝ) → ℝ) (σ : ℝ) : Prop :=
  (DifferentiableOn ℝ h (orthant m) ∨ IsEssentiallySmoothOrthant h) ∧
    IsStronglyConvexL1 (orthant m) h σ

end DualMirrorAlloc


