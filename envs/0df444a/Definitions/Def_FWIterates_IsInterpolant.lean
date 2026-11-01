-- Prove2me | Definitions.Def_FWIterates_IsInterpolant
-- name    : FWIterates_IsInterpolant
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:26.777113+00:00
-- url     : https://prove2.me/theorems/9aace5d7-46f5-46af-92da-3382792fd289
-- title:
--   Theorem 3.1, conclusions (iv)–(x), p.4 — a smooth convex interpolant of the sketches
-- statement:
--   For an open convex $\mathcal D\subset\mathbb R^2$, an integer $d$, sketch data $(\mathcal P_\ell,V_k,u_k,\delta_\ell)$, a function $f$ and levels $(\eta_\ell)$, the conclusions of Theorem 3.1 are: $f$ is convex and $d$-times continuously differentiable on $\mathcal D$, and for all $k,\ell\in\mathbb N$, writing $\mathcal L_\ell=\{x\in\mathcal D\mid f(x)\le\eta_\ell\}$,
--
--   1. (iv) $\eta_{\ell+1}<\eta_\ell$;
--   2. (v) $\mathcal P_\ell\subset\mathcal L_\ell$;
--   3. (vi) $f(V)=\eta_\ell$ for all $V\in\operatorname{vert}\mathcal P_\ell$;
--   4. (vii) $\mathcal L_\ell$ is compact and $\operatorname{dist}(\mathcal P_\ell,\mathcal L_\ell)\le\delta_\ell$ (Hausdorff distance, defined in §2.1 for nonempty compact sets);
--   5. (viii) $\mathcal L_\ell$ has positive curvature: at every $x\in\mathcal D$ with $f(x)=\eta_\ell$, $\nabla f(x)\ne0$ and $\nabla^2f(x)(\tau,\tau)>0$ for every $\tau\neq0$ with $\langle\tau,\nabla f(x)\rangle=0$;
--   6. (ix) $\nabla f(V_k)=c\,u_k$ for some $c>0$;
--   7. (x) $\operatorname{arg\,min}_{\mathcal D}f=\bigcap_{\ell}\mathcal P_\ell$, and $\nabla^2f(x)$ is positive definite at every $x\in\mathcal D\setminus\bigcap_\ell\mathcal P_\ell$.
--
--   **Formalization Note** $f$ is a total function on $\mathbb R^2$ with every property on $\mathcal D$; sublevel sets are taken inside $\mathcal D$. The Hessian form is `fderiv ℝ (fderiv ℝ f) x h h`. (vii) uses `Metric.hausdorffEDist` with values in $[0,\infty]$, so an unbounded sublevel set violates it. The reading of (viii) is the positive curvature $\tau^\top\nabla^2f\,\tau/\|\nabla f\|$ of the level curve bounding $\mathcal L_\ell$. In (x) the equality $\operatorname{arg\,min}_{\mathcal D}f=\bigcap_\ell\mathcal P_\ell$ is a separate clause.
-- source:
--   Bolte, Combettes & Pauwels, The Iterates of the Frank-Wolfe Algorithm May Not Converge, arXiv:2202.08711v1, Theorem 3.1, conclusions (iv)–(x), p.4

import Mathlib

open scoped RealInnerProductSpace

namespace FWIterates

/-- **The conclusions of Theorem 3.1** (arXiv:2202.08711v1, Theorem 3.1, conclusions, p.4) for an
open convex `D ⊂ ℝ²`, an integer `d`, sketch data `P, V, u, δ`, a function `f` and levels `η`:
`f` is convex and `d`-times continuously differentiable on `D`, and for all `k, ℓ`:

* (iv) `η (ℓ+1) < η ℓ`;
* (v) `P ℓ ⊆ {x | f x ≤ η ℓ}`;
* (vi) `f V = η ℓ` for every vertex `V` of `P ℓ`;
* (vii) `{x | f x ≤ η ℓ}` is compact and its Hausdorff distance to `P ℓ` is at most `δ ℓ`;
* (viii) `{x | f x ≤ η ℓ}` has positive curvature;
* (ix) `∇f (V k)` is positively colinear to `u k`;
* (x) `argmin_D f = ⋂ ℓ, P ℓ`, and `∇²f` is positive definite outside of it.

**Formalization Note** The paper's `f : D → ℝ` is a total `f : ℝ² → ℝ` with every property on
`D`; sublevel sets are taken inside `D`, `{x ∈ D | f x ≤ η ℓ}`. The Hessian quadratic form is
`fderiv ℝ (fderiv ℝ f) x h h`, the true second derivative at `x ∈ D` since `D` is open and
`d ≥ 2` in every use. (vii): §2.1 (p.2) defines `dist` for two nonempty compact sets only, so the
page's (vii) includes that the sublevel set is compact (clause `isCompact_sublevel`; nonempty by
(v)). It uses `Metric.hausdorffEDist` (in `[0, ∞]`), so no junk value applies. (viii) is read as: at every `x ∈ D` on
the level `f x = η ℓ`, `∇f x ≠ 0` and `∇²f(x)(τ, τ) > 0` for every nonzero tangent `τ ⟂ ∇f x`;
for a `C²` function this is positive curvature `τᵀ∇²f τ / ‖∇f‖ > 0` of the level curve bounding the
sublevel set. (x) is two clauses: the equality of the minimizer set of `f` on `D` with `⋂ ℓ, P ℓ`
(the paper writes it as notation inside (x)) and positive definiteness of the Hessian on
`D \ ⋂ ℓ, P ℓ`. The data `δ` enter only through (vii). -/
structure IsInterpolant (D : Set (EuclideanSpace ℝ (Fin 2))) (d : ℕ)
    (P : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (V u : ℕ → EuclideanSpace ℝ (Fin 2)) (δ : ℕ → ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (η : ℕ → ℝ) : Prop where
  convexOn : ConvexOn ℝ D f
  contDiffOn : ContDiffOn ℝ d f D
  level_strictAnti : ∀ ℓ, η (ℓ + 1) < η ℓ
  subset_sublevel : ∀ ℓ, P ℓ ⊆ {x | x ∈ D ∧ f x ≤ η ℓ}
  vertex_level : ∀ ℓ, ∀ W ∈ Set.extremePoints ℝ (P ℓ), f W = η ℓ
  isCompact_sublevel : ∀ ℓ, IsCompact {x | x ∈ D ∧ f x ≤ η ℓ}
  hausdorff_le : ∀ ℓ,
    Metric.hausdorffEDist (P ℓ) {x | x ∈ D ∧ f x ≤ η ℓ} ≤ ENNReal.ofReal (δ ℓ)
  positive_curvature : ∀ ℓ, ∀ x ∈ D, f x = η ℓ →
    gradient f x ≠ 0 ∧
      ∀ τ : EuclideanSpace ℝ (Fin 2), τ ≠ 0 → ⟪τ, gradient f x⟫ = 0 →
        0 < fderiv ℝ (fderiv ℝ f) x τ τ
  gradient_colinear : ∀ k, ∃ c : ℝ, 0 < c ∧ gradient f (V k) = c • u k
  argmin_eq : {x | x ∈ D ∧ ∀ y ∈ D, f x ≤ f y} = ⋂ ℓ, P ℓ
  hessian_posDef : ∀ x ∈ D, x ∉ ⋂ ℓ, P ℓ →
    ∀ h : EuclideanSpace ℝ (Fin 2), h ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) x h h

end FWIterates


