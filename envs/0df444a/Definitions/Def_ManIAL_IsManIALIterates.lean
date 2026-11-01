-- Prove2me | Definitions.Def_ManIAL_IsManIALIterates
-- name    : ManIAL_IsManIALIterates
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:53.977695+00:00
-- url     : https://prove2.me/theorems/657a7157-22b7-42c9-a3d4-cb3d21bd0757
-- title:
--   Outer recursion of ManIAL (Algorithm 1, steps 2 and 5–7)
-- statement:
--   Let $(\sigma_k)$ be a penalty sequence, $\beta_0>0$, $x_0\in\mathbb R^n$, $y_0\in\mathbb R^m$. Sequences $(x^k,y^k,z^k)$ follow the **outer recursion of ManIAL** if $x^0=x_0$, $y^0=y_0$, $z^0=0$ and for every $k\ge0$
--
--   1. $y^{k+1}=\operatorname{prox}_{h/\sigma_k}(\mathcal Ax^{k+1}-z^k/\sigma_k)$, i.e. $y^{k+1}$ minimizes $h(\cdot)+\frac{\sigma_k}2\|\cdot-(\mathcal Ax^{k+1}-z^k/\sigma_k)\|^2$;
--   2. $z^{k+1}=z^k-\beta_{k+1}(\mathcal Ax^{k+1}-y^{k+1})$ with $\beta_{k+1}$ the dual step size (3.13).
--
--   How $x^{k+1}$ is produced (step 4, a subroutine applied to $\psi_k$) is left open here; the two options of Algorithm 1 are separate definitions.
--
--   **Formalization Note** The prox is the published predicate `SAGA.StronglyConvex.IsProxPoint` with parameter $1/\sigma_k$. The paper initializes $y^0=\mathcal Ax^0$; here $y^0$ is a free parameter, with $y^0=\mathcal Ax^0$ as a special case.
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Algorithm 1, steps 2, 5–7, p.9

import Mathlib
import Definitions.Def_SAGA_StronglyConvex_IsProxPoint
import Definitions.Def_ManIAL_dualStep

open SAGA.StronglyConvex

namespace ManIAL

/-- The outer recursion of Algorithm 1 (ManIAL) (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.9), for
a penalty sequence `σ` and any primal sequence `x`: `x⁰ = x₀`, `y⁰ = y₀`, `z⁰ = 0`, and for every
`k`,
* step 5: `y^{k+1} = prox_{h/σ_k}(Ax^{k+1} − z^k/σ_k)`;
* steps 6–7: `z^{k+1} = z^k − β_{k+1}(Ax^{k+1} − y^{k+1})` with `β_{k+1}` from (3.13).

How `x^{k+1}` is produced (step 4) is not constrained here: see `IsRunOptionI`,
`IsRunOptionII`.

**Formalization Note.** `p = prox_{h/σ}(w)` is `IsProxPoint h (1/σ) w p`: `p` minimizes
`h(·) + (σ/2)‖· − w‖²` (for convex continuous `h` the minimizer exists and is unique). The paper
initializes `y⁰ = Ax⁰`; here `y⁰ = y₀` is arbitrary (with `y₀ = Ax₀` as a special case), and
the dual step size `β₀` enters through `dualStep`. -/
def IsManIALIterates {n m : ℕ} (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β₀ : ℝ) (σ : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (y₀ : EuclideanSpace ℝ (Fin m))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m)) : Prop :=
  x 0 = x₀ ∧ y 0 = y₀ ∧ z 0 = 0 ∧
    ∀ k : ℕ,
      IsProxPoint h (1 / σ k) (A (x (k + 1)) - (σ k)⁻¹ • z k) (y (k + 1)) ∧
      z (k + 1) = z k - dualStep β₀ A x₀ y₀ k (x (k + 1)) (y (k + 1)) • (A (x (k + 1)) - y (k + 1))

end ManIAL


