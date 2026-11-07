-- Prove2me | Definitions.Def_QuadPTFLearn_Regularity
-- name    : QuadPTFLearn_Regularity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:42.630262+00:00
-- url     : https://prove2.me/theorems/1b42c7c3-f918-4a79-ba14-3cda78bc6b0b
-- title:
--   $(\tau,V)$-regularity, the decomposition along $V$, residual coefficients $\theta\in S_V$ and the Gaussian replacement $\tilde p(z,G)$
-- statement:
--   The regularity notion and the Gaussian surrogate of Section 3.
--
--   Let $V\subseteq\mathbb R^d$ be a subspace, $z=\mathrm{proj}_Vx$ and $w=\mathrm{proj}_{V^\perp}x$.
--
--   1. **Regularity (Definition 3.1).** For a polynomial $p$ of degree at most two and a unit vector $v$, $\inf_p(v)=\mathbb E[(v\cdot\nabla p(x))^2]$. The polynomial $p$ is $(\tau,V)$-regular if $\inf_p(v)\le\tau^2\,\mathrm{Var}[p]$ for every unit $v\in V^\perp$.
--   2. **Decomposition.** $p(x)=q(z)+b^\top w+z^\top Lw+w^\top Aw-\mathrm{tr}(A)$ with $q(z)=\mathbb E[p(x)\mid z]$, $b\in V^\perp$, $L:V^\perp\to V$ and $A$ symmetric on $V^\perp$. The coefficient norms $\|b\|_2,\|L\|_{op},\|A\|_{op}$ are read off the directional derivatives of $p$ along $V^\perp$.
--   3. **Residual coefficients.** $S_V=\{\theta\in\mathbb R^N:\mathbb E[\theta\cdot\Phi_2(x)\mid z]=0\}$, and $p(x)=q(z)+\theta\cdot\Phi_2(x)$ for a unique $\theta\in S_V$; here $\theta_j=\mathbb E[(p(x)-q(z))\Phi_2(x)_j]$.
--   4. **Gaussian replacement.** $\tilde p(z,G)=q(z)+\theta\cdot G$ with $G\sim N(0,I_N)$ independent of $x$, the same $G$ for all defining polynomials, and the surrogate $\tilde f(z,G)=1\{\tilde p_i(z,G)\ge0\ \forall i\}$. Its randomized error along $u\in\mathbb R^N$ is taken in the joint Gaussian model.
--   5. **Assumptions of Lemma 3.3.** $\tau\in(0,1)$ and, for every $i$, $\deg p_i\le2$, $\|p_i\|_2=1$ and $\|b_i\|_2,\|L_i\|_{op},\|A_i\|_{op}\le\tau$.
--
--   **Formalization Note** The three coefficient bounds are stated as $|\partial_up(0)|\le\tau$, $|\partial_up(z)-\partial_up(0)|\le\tau$ and $|\partial_{u'}\partial_up|\le2\tau$ for unit $u,u'\in V^\perp$ and unit $z\in V$, which equal $|b\cdot u|$, $|z^\top Lu|$ and $2|u^\top Au'|$. $S_V$ is written as the span of the set above, which is the set itself.
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Definition 3.1; Notation and Gaussian replacement, p.15 (PDF p.17); p.16 (PDF p.18); assumptions of Lemma 3.3, p.16

import Mathlib
import Definitions.Def_QuadPTFLearn_Gaussian

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-!
# `(τ, V)`-regularity, the decomposition along `V`, and the Gaussian replacement

I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Definition 3.1, p.15 (PDF p.17); "Notation and Gaussian replacement", p.16 (PDF p.18); the
assumptions of Lemma 3.3, p.16.

**Formalization Note.**
* `z = proj_V x` and `w = proj_{V⊥} x` are the orthogonal projections (`Submodule.starProjection`).
* `infl p v = E[(v · ∇p(x))²]`, and `p` is `(τ, V)`-regular when `infl p v ≤ τ² Var[p]` for every
  unit `v ∈ V⊥` (Definition 3.1; the standing `τ ∈ (0, 1)` and `deg p ≤ 2` are hypotheses of the
  theorems that use it).
* `condV V p` is `q(z) = E[p(x) | z]`, written as `x ↦ ∫ p(proj_V x + proj_{V⊥} y) dN(0, I)(y)`.
* The residual coefficient vector `θ = resid V p ∈ ℝᴺ` is the vector of Hermite coefficients
  `θ_j = E[(p(x) − q(z)) Φ₂(x)_j]`. For `deg p ≤ 2`, `p − q(z)` has mean zero and degree at most
  two, so it equals `θ · Φ₂(x)`; this is the unique `θ ∈ S_V` of p.16 with `p(x) = q(z) + θ · Φ₂(x)`.
* `S_V = {θ ∈ ℝᴺ : E[θ · Φ₂(x) | z] = 0}` is a linear subspace; `SV V` is written as the span of
  that set, which is the set itself.
* The Gaussian replacement is `p̃(z, G) = q(z) + θ · G` with `G ∈ ℝᴺ`; as a function it takes the
  point `x` (through `q(z) = condV V p x`) and `G`.
* The coefficient norms of the decomposition `p − q(z) = bᵀw + zᵀLw + wᵀAw − tr(A)` are read off
  directional derivatives along `V⊥`, where `q(z)` contributes nothing:
  `b · u = ∂_u p(0)`, `zᵀLu = ∂_u p(z) − ∂_u p(0)` for `z ∈ V`, and `2 uᵀAu′ = ∂_{u′}∂_u p`.
  So `‖b‖₂ ≤ τ`, `‖L‖_op ≤ τ` and `‖A‖_op ≤ τ` (`A` symmetric) are the three clauses of
  `CoeffBounded`, with suprema over unit vectors of `V` and `V⊥`.
-/

/-- The orthogonal projection `proj_V x`. -/
noncomputable def projV {d : ℕ} (V : Submodule ℝ (Pt d)) (x : Pt d) : Pt d := V.starProjection x

/-- The directional influence `inf_p(v) = E_{x∼N(0,I)}[(v · ∇p(x))²]`. -/
noncomputable def infl {d : ℕ} (p : Poly d) (v : Pt d) : ℝ :=
  ∫ x, (peval (dirDeriv v p) x) ^ 2 ∂gauss d

/-- Definition 3.1: `p` is `(τ, V)`-regular. -/
def IsRegular {d : ℕ} (τ : ℝ) (V : Submodule ℝ (Pt d)) (p : Poly d) : Prop :=
  ∀ v ∈ Vᗮ, ‖v‖ = 1 → infl p v ≤ τ ^ 2 * var (peval p)

/-- `q(z) = E[p(x) | z]`, `z = proj_V x`, as a function of `x`. -/
noncomputable def condV {d : ℕ} (V : Submodule ℝ (Pt d)) (p : Poly d) (x : Pt d) : ℝ :=
  ∫ y, peval p (projV V x + projV Vᗮ y) ∂gauss d

/-- The residual coefficient vector `θ` of `p` with respect to `V`. -/
noncomputable def resid {d : ℕ} (V : Submodule ℝ (Pt d)) (p : Poly d) : Lift d :=
  WithLp.toLp 2 (fun j => ∫ x, (peval p x - condV V p x) * phi2 x j ∂gauss d)

/-- The set `{θ ∈ ℝᴺ : E[θ · Φ₂(x) | z] = 0}`. -/
def SVset {d : ℕ} (V : Submodule ℝ (Pt d)) : Set (Lift d) :=
  {θ | ∀ x, ∫ y, ⟪θ, phi2 (projV V x + projV Vᗮ y)⟫ ∂gauss d = 0}

/-- The subspace `S_V` of residual coefficient vectors. -/
noncomputable def SV {d : ℕ} (V : Submodule ℝ (Pt d)) : Submodule ℝ (Lift d) :=
  Submodule.span ℝ (SVset V)

/-- The Gaussian replacement `p̃(z, G) = q(z) + θ · G`. -/
noncomputable def ptilde {d : ℕ} (V : Submodule ℝ (Pt d)) (p : Poly d) (x : Pt d) (G : Lift d) :
    ℝ :=
  condV V p x + ⟪resid V p, G⟫

/-- The Gaussian surrogate `f̃(z, G) = 1{p̃_i(z, G) ≥ 0 for all i}`. -/
noncomputable def surrogate {d k : ℕ} (V : Submodule ℝ (Pt d)) (p : Fin k → Poly d) (x : Pt d)
    (G : Lift d) : ℝ :=
  if ∀ i, 0 ≤ ptilde V (p i) x G then 1 else 0

/-- `Rand_{f̃}(u)` in the Gaussian model `(x_V, G)`, along a direction `u ∈ ℝᴺ`. -/
noncomputable def randSurrogate {d k : ℕ} (V : Submodule ℝ (Pt d)) (p : Fin k → Poly d)
    (u : Lift d) : ℝ :=
  ∫ x, Rand (surrogate V p x) u ∂gauss d

/-- The coefficient norms `‖b‖₂`, `‖L‖_op`, `‖A‖_op` of the decomposition of `p` are all at
most `τ`. -/
def CoeffBounded {d : ℕ} (τ : ℝ) (V : Submodule ℝ (Pt d)) (p : Poly d) : Prop :=
  (∀ u ∈ Vᗮ, ‖u‖ = 1 → |peval (dirDeriv u p) 0| ≤ τ) ∧
  (∀ z ∈ V, ‖z‖ = 1 → ∀ u ∈ Vᗮ, ‖u‖ = 1 →
      |peval (dirDeriv u p) z - peval (dirDeriv u p) 0| ≤ τ) ∧
  (∀ u ∈ Vᗮ, ‖u‖ = 1 → ∀ u' ∈ Vᗮ, ‖u'‖ = 1 → |peval (dirDeriv u' (dirDeriv u p)) 0| ≤ 2 * τ)

/-- The assumptions of Lemma 3.3 (p.16): `τ ∈ (0, 1)`; every `p_i` has degree at most two,
`‖p_i‖₂ = 1`, and coefficient norms at most `τ`. -/
def Lemma33Assumptions {d k : ℕ} (τ : ℝ) (V : Submodule ℝ (Pt d)) (p : Fin k → Poly d) : Prop :=
  0 < τ ∧ τ < 1 ∧ ∀ i, (p i).totalDegree ≤ 2 ∧ l2norm (peval (p i)) = 1 ∧ CoeffBounded τ V (p i)

/-- A polynomial depending only on `x_V`. -/
def DependsOnlyOn {d : ℕ} (V : Submodule ℝ (Pt d)) (a : Poly d) : Prop :=
  ∀ x, peval a x = peval a (projV V x)

end QuadPTFLearn


