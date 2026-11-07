-- Prove2me | Definitions.Def_PolySampIso_PsiPI
-- name    : PolySampIso_PsiPI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:23.929524+00:00
-- url     : https://prove2.me/theorems/2b02ccdf-d271-4e3f-aef4-746404d0b3d2
-- title:
--   Definition 2: the ψ-Poincaré inequality
-- statement:
--   Let $X\subseteq\mathbb R^d$ be open, $\pi$ a probability measure on $X$, and $\psi:X\to\mathbb R$ strictly convex and twice differentiable. Then $\pi$ satisfies a **$\psi$-Poincaré inequality with constant $\alpha$** ($\alpha$-$\psi$-PI) if for every smooth $f:X\to\mathbb R$
--
--   $$\mathrm{Var}_\pi[f]\le\frac1\alpha\,\mathbb E_\pi\Big[\|\nabla f\|^2_{(\nabla^2\psi)^{-1}}\Big].$$
--
--   It is a Poincaré inequality in the Riemannian geometry of the Hessian of $\psi$; for the log barrier it is what makes the proximal sampler of [GST26] contract (Proposition 1).
--
--   **Formalization Note** $\|\nabla f(x)\|^2_{(\nabla^2\psi(x))^{-1}}$ is written as $\sup_w\big(2\,Df(x)[w]-D^2\psi(x)[w,w]\big)$, which equals $\nabla f^\top(\nabla^2\psi)^{-1}\nabla f$ for a positive definite Hessian, and is computed in $[0,\infty]$; the variance is the extended variance ($\infty$ off $L^2$). The hypotheses on $\psi$ are carried by the theorems.
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Definition 2, p.9 (PDF p.11)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolySampIso

/-!
# The ψ-Poincaré inequality (Definition 2)

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Definition 2, p.9 (PDF p.11): "Definition 2 (ψ-PI,
Definition 3, [GST26]). Let π ∈ P(X) for an open X ⊆ Rd, and let ψ : X → R be strictly convex and
twice-differentiable. We say that π satisfies a ψ-Poincaré inequality with constant α (abbreviated
as α-ψ-PI) if, for all smooth functions f : X → R, Varπ[f] ≤ (1/α) Eπ[∥∇f∥²_{(∇²ψ)−1}]."

**Formalization Note.**
* `ψ` and `f` are functions on `ℝᵈ` (`EuclideanSpace ℝ (Fin d)`); only their values on the open
  set `X` matter, since `π(Xᶜ) = 0` in every use and derivatives at points of an open set depend
  only on values nearby. "Smooth" is `ContDiffOn ℝ ∞ f X`. The hypotheses on `ψ` (strictly convex,
  twice differentiable) are hypotheses of the theorems that use the definition.
* `dualGradSq ψ f x = ‖∇f(x)‖²_{(∇²ψ(x))⁻¹}` is written as the Legendre form
  `sup_w (2 Df(x)[w] − D²ψ(x)[w, w])`, which equals `∇f(x)⊤(∇²ψ(x))⁻¹∇f(x)` when `∇²ψ(x) ≻ 0`. It is
  computed in `ℝ≥0∞` (the supremum of `ofReal`), so it is never a junk value.
* `Var_π[f]` is `evariance f π ∈ ℝ≥0∞` (`∞` when `f ∉ L²(π)`), the right side is a lower integral,
  and `1/α` is `ENNReal.ofReal α⁻¹` (used for `α > 0`).
-/

/-- `‖∇f(x)‖²_{(∇²ψ(x))⁻¹}`, as `sup_w (2 Df(x)[w] − D²ψ(x)[w, w])` in `ℝ≥0∞`. -/
noncomputable def dualGradSq {d : ℕ} (ψ f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨆ w : EuclideanSpace ℝ (Fin d),
    ENNReal.ofReal (2 * fderiv ℝ f x w - fderiv ℝ (fderiv ℝ ψ) x w w)

/-- `π` satisfies an `α`-ψ-Poincaré inequality on `X` (Definition 2). -/
def SatisfiesPsiPI {d : ℕ} (π : Measure (EuclideanSpace ℝ (Fin d)))
    (X : Set (EuclideanSpace ℝ (Fin d))) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (α : ℝ) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f X →
    evariance f π ≤ ENNReal.ofReal α⁻¹ * ∫⁻ x, dualGradSq ψ f x ∂π

end PolySampIso


