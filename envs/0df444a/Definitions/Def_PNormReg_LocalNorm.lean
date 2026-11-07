-- Prove2me | Definitions.Def_PNormReg_LocalNorm
-- name    : PNormReg_LocalNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:16.657388+00:00
-- url     : https://prove2.me/theorems/40bea7ca-5391-4aad-a703-fd2da855cc28
-- title:
--   Local-norm setups and local estimators (Definitions 5–6)
-- statement:
--   A local-norm setup consists of a product domain $Z=X\times Y$ of compact convex sets, a norm $\|\cdot\|_z$ on $\mathbb R^d\times\mathbb R^n$ for each $z\in Z$, a differentiable convex $r:Z\to\mathbb R$ with range $\Xi=\max_{z,z'\in Z}(r(z)-r(z'))$, and a map clip. With $V_z(z')=r(z')-r(z)-\nabla r(z)^\top(z'-z)$ and $\|\gamma\|_*^2=\max_{w\in Z}\|\gamma\|_w^2$, it must satisfy, for all $z,z'\in Z$ and all $\gamma$,
--
--   $$\gamma^\top(z-z')-V_z(z')\le\tfrac12\|\gamma\|_*^2,$$
--
--   $$|\mathrm{clip}(\gamma)^\top(z-z')|-V_z(z')\le\|\gamma\|_z^2,\qquad|(\gamma-\mathrm{clip}(\gamma))^\top z|\le\|\gamma\|_z^2.$$
--
--   A stochastic estimator $\tilde g$ of an operator $g$ is $L$-local if, for every $z,w\in Z$, $\mathbb E[\tilde g(z)]=g(z)$ and $\mathbb E[\|\tilde g(z)\|_w^2]\le L^2$.
--
--   This is the framework in which stochastic mirror descent controls its variance by a geometry adapted to the current iterate.
--
--   **Formalization Note** The gradient of $r$ is a field tied to $r$ by differentiability within $Z$. Estimators have finite support (finite outcome type, weights, values), so expectations are finite sums; every estimator in the paper has this form.
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Definitions 5–6, p.36

import Mathlib

open Matrix

namespace PNormReg

/-!
# Local-norm setups and local estimators

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…), Definition 5 (= [CJST20, Definition 1]) and
Definition 6 (= [CJST20, Definition 3]), p.36.

**Formalization Note.**
* The gradient `∇r` is a field, tied to `r` by `grad_r`: `r` is differentiable within `Z`, with
  derivative `γ ↦ ∇r(z)⊤γ` at every `z ∈ Z`. No smoothness beyond Definition 5 is bundled.
* `∥γ∥_z` is the field `localNorm z γ`; (46)–(48) use its square.
* `dualSq` is the real `sSup` of `∥γ∥²_w` over `w ∈ Z`, and `dual_attained` makes it the printed `max`.
* Definition 6's estimators are finite-support here: a finite outcome type `Ω`, weights and values,
  so its expectations are finite sums. Every estimator of the paper has this form.
-/

variable {d n : ℕ}

/-- `ℝ^d × ℝ^n`. -/
abbrev Pair (d n : ℕ) := (Fin d → ℝ) × (Fin n → ℝ)

/-- The inner product `γ⊤z` on `ℝ^d × ℝ^n`. -/
def pairDot (γ z : Pair d n) : ℝ := γ.1 ⬝ᵥ z.1 + γ.2 ⬝ᵥ z.2

/-- `f` is a norm on `ℝ^d × ℝ^n`. -/
def IsNormOn (f : Pair d n → ℝ) : Prop :=
  (∀ v, 0 ≤ f v) ∧ (∀ v, f v = 0 → v = 0) ∧ (∀ (c : ℝ) v, f (c • v) = |c| * f v) ∧
    ∀ u v, f (u + v) ≤ f u + f v

/-- The data of a local-norm setup: `X`, `Y`, `∥·∥_z`, `r`, `∇r`, `Ξ`, `clip`. -/
structure LocalNormData (d n : ℕ) where
  X : Set (Fin d → ℝ)
  Y : Set (Fin n → ℝ)
  localNorm : Pair d n → Pair d n → ℝ
  r : Pair d n → ℝ
  gradR : Pair d n → Pair d n
  Xi : ℝ
  clip : Pair d n → Pair d n

namespace LocalNormData

/-- The product domain `Z := X × Y`. -/
def Z (S : LocalNormData d n) : Set (Pair d n) := S.X ×ˢ S.Y

/-- The Bregman divergence `V_z(z′) := r(z′) − r(z) − ∇r(z)⊤(z′ − z)`. -/
def bregman (S : LocalNormData d n) (z z' : Pair d n) : ℝ :=
  S.r z' - S.r z - pairDot (S.gradR z) (z' - z)

/-- `∥γ∥²_∗ := max_{w∈Z} ∥γ∥²_w`. -/
noncomputable def dualSq (S : LocalNormData d n) (γ : Pair d n) : ℝ :=
  sSup ((fun w => S.localNorm w γ ^ 2) '' S.Z)

/-- Definition 5: `X` and `Y` are compact and convex; `∥·∥_z` is a norm for each `z ∈ Z`; `r` is convex
and differentiable on `Z` with gradient `∇r`; `Ξ` is its range; and (46), (47), (48) hold. -/
structure IsLocalNormSetup (S : LocalNormData d n) : Prop where
  compact_X : IsCompact S.X
  convex_X : Convex ℝ S.X
  compact_Y : IsCompact S.Y
  convex_Y : Convex ℝ S.Y
  norm_at : ∀ z ∈ S.Z, IsNormOn (S.localNorm z)
  convex_r : ConvexOn ℝ S.Z S.r
  grad_r : ∀ z ∈ S.Z, ∃ L : Pair d n →L[ℝ] ℝ,
    HasFDerivWithinAt S.r L S.Z z ∧ ∀ v, L v = pairDot (S.gradR z) v
  range : IsGreatest {t | ∃ z ∈ S.Z, ∃ z' ∈ S.Z, t = S.r z - S.r z'} S.Xi
  dual_attained : ∀ γ, ∃ w ∈ S.Z, ∀ w' ∈ S.Z, S.localNorm w' γ ^ 2 ≤ S.localNorm w γ ^ 2
  ineq_46 : ∀ z ∈ S.Z, ∀ z' ∈ S.Z, ∀ γ,
    pairDot γ (z - z') - S.bregman z z' ≤ (1 / 2) * S.dualSq γ
  ineq_47 : ∀ z ∈ S.Z, ∀ z' ∈ S.Z, ∀ γ,
    |pairDot (S.clip γ) (z - z')| - S.bregman z z' ≤ S.localNorm z γ ^ 2
  ineq_48 : ∀ z ∈ S.Z, ∀ γ, |pairDot (γ - S.clip γ) z| ≤ S.localNorm z γ ^ 2

/-- Definition 6: the finite-support estimator with law `weight z` and values `est z` is `L`-local for
the operator `g`: for every `z, w ∈ Z`, `E[g̃(z)] = g(z)` and `E[∥g̃(z)∥²_w] ≤ L²`. -/
structure IsLocalEstimator (S : LocalNormData d n) (g : Pair d n → Pair d n) {Ω : Type*}
    [Fintype Ω] (weight : Pair d n → Ω → ℝ) (est : Pair d n → Ω → Pair d n) (L : ℝ) : Prop where
  nonneg : ∀ z ∈ S.Z, ∀ o, 0 ≤ weight z o
  sum_one : ∀ z ∈ S.Z, ∑ o, weight z o = 1
  unbiased : ∀ z ∈ S.Z, ∑ o, weight z o • est z o = g z
  second_moment : ∀ z ∈ S.Z, ∀ w ∈ S.Z, ∑ o, weight z o * S.localNorm w (est z o) ^ 2 ≤ L ^ 2

end LocalNormData

end PNormReg


