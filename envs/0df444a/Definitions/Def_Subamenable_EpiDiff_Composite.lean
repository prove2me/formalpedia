-- Prove2me | Definitions.Def_Subamenable_EpiDiff_Composite
-- name    : Subamenable_EpiDiff_Composite
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:50.537167+00:00
-- url     : https://prove2.me/theorems/6d8a6fbd-5e49-47d1-9bcc-e25cb53079cf
-- title:
--   Definitions 3.2 and 4.2 — metric subregularity and full subamenability
-- statement:
--   For a composite function $\varphi=\vartheta\circ f$ near $\bar x$, the metric subregularity qualification condition is the local error bound
--
--   $$\operatorname{dist}(x,\{u:f(u)\in\operatorname{dom}\vartheta\})\le\kappa\,\operatorname{dist}(f(x),\operatorname{dom}\vartheta),\qquad\kappa\ge0.$$
--
--   A fully subamenable representation consists of a function $\varphi$ agreeing near $\bar x$ with $\vartheta\circ f$, where $f$ is twice differentiable at $\bar x$, $\vartheta$ is convex piecewise linear-quadratic, and this error bound holds. For $\bar v\in\partial\varphi(\bar x)$ the multiplier set is $\Lambda(\bar x,\bar v)=\{\lambda\in\partial\vartheta(f(\bar x)): \nabla f(\bar x)^*\lambda=\bar v\}$.
--
--   These definitions provide the data for the paper's second-order chain formula.
--
--   **Formalization Note** Twice differentiability includes differentiability near $\bar x$ and differentiability of the derivative at $\bar x$. The composite equality is local. The limiting subdifferential is the published `NonconvexSplitting.Shared.LimitingSubdiff`; for the lower semicontinuous functions used here, it agrees with the paper's geometric definition.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, pp. 9–10, 16, 19, Definition 3.2, (3.5), Definition 4.2, (4.6)

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_PWLQ
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open Filter Topology
open scoped InnerProductSpace

namespace Subamenable.EpiDiff

/-- The distance estimate (3.5), with the same nonnegative modulus as Definition 3.2. -/
noncomputable def MSQC {n m : ℕ} (theta : E m → EReal) (f : E n → E m)
    (xbar : E n) (kappa : ℝ) : Prop :=
  0 ≤ kappa ∧ ∃ U ∈ 𝓝 xbar,
    ∀ x ∈ U, Metric.infDist x (f ⁻¹' dom theta) ≤
      kappa * Metric.infDist (f x) (dom theta)

/-- Rockafellar–Wets twice differentiability at a point, as used by Definition 4.2. -/
def TwiceDiffAt {n m : ℕ} (f : E n → E m) (xbar : E n) : Prop :=
  (∀ᶠ x in 𝓝 xbar, DifferentiableAt ℝ f x) ∧
    DifferentiableAt ℝ (fderiv ℝ f) xbar

/-- An explicit local representation of a fully subamenable function, Definition 4.2. -/
def IsFullySubamenableRep {n m : ℕ} (phi : E n → EReal) (theta : E m → EReal)
    (f : E n → E m) (xbar : E n) : Prop :=
  xbar ∈ dom phi ∧ (∀ x, phi x ≠ ⊥) ∧
    (∃ U ∈ 𝓝 xbar, ∀ x ∈ U, phi x = theta (f x)) ∧
    TwiceDiffAt f xbar ∧ IsConvexPWLQ theta ∧
    ∃ kappa : ℝ, MSQC theta f xbar kappa

/-- The multiplier set (4.6) at `xbar`. -/
noncomputable def Lam {n m : ℕ} (theta : E m → EReal) (f : E n → E m)
    (xbar vbar : E n) : Set (E m) :=
  {lam | (fderiv ℝ f xbar).adjoint lam = vbar ∧
    lam ∈ NonconvexSplitting.Shared.LimitingSubdiff theta (f xbar)}

/-- The expression maximized in (4.7) and (5.3). -/
noncomputable def multiplierValue {n m : ℕ} (theta : E m → EReal)
    (f : E n → E m) (xbar w : E n) (lam : E m) : EReal :=
  secondSubderiv theta (f xbar) lam (fderiv ℝ f xbar w) +
    ((⟪lam, fderiv ℝ (fderiv ℝ f) xbar w w⟫_ℝ : ℝ) : EReal)

end Subamenable.EpiDiff


