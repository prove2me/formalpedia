-- Prove2me | Definitions.Def_FTPLLinBandit_ellInfoQ
-- name    : FTPLLinBandit_ellInfoQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:02:22.316629+00:00
-- url     : https://prove2.me/theorems/ea77a3aa-bfad-459a-858d-d6a78d8d47fc
-- title:
--   Shifted elliptical information $\mathcal J^v(P_\Sigma)$ and its clipped version $\mathcal J^{v,L}(P_\Sigma)$ (Definition 2), as quadratic forms
-- statement:
--   Fix an elliptical family $P_\Sigma$ with radial profile $f$, a shape matrix $\Sigma\succ0$ and $v\in\mathbb R^d$. Definition 2 sets
--   $$\mathcal J^v(P_\Sigma)=\int_{\mathbb R^d}\frac{P_{\Sigma+vv^\top}(z)^2}{P_\Sigma(z+v)}\,\Sigma^{-1}zz^\top\Sigma^{-1}\,dz,\qquad \mathcal J^{v,L}(P_\Sigma)=\int_{\mathcal E_\Sigma(L)}\frac{P_{\Sigma+vv^\top}(z)^2}{P_\Sigma(z+v)}\,\Sigma^{-1}zz^\top\Sigma^{-1}\,dz .$$
--   For a measurable domain $D\subseteq\mathbb R^d$ and $u\in\mathbb R^d$ this definition is the quadratic form
--   $$\int_D\frac{P_{\Sigma+vv^\top}(z)^2}{P_\Sigma(z+v)}\,\big(u^\top\Sigma^{-1}z\big)^2\,dz\in[0,\infty],$$
--   which is $u^\top\mathcal J^v(P_\Sigma)u$ for $D=\mathbb R^d$ and $u^\top\mathcal J^{v,L}(P_\Sigma)u$ for $D=\mathcal E_\Sigma(L)$. Theorem 10 bounds the elliptical stability term $B_t$ through it.
--
--   **Formalization Note** Values lie in $[0,\infty]$: Table 4 records that $\mathcal J^v$ is infinite for Student-$t_2$, which is $\infty$ here, not a junk $0$.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Definition 2, Eqs. (15)–(16), p.12

import Mathlib
import Definitions.Def_FTPLLinBandit_ellDens

open MeasureTheory Matrix
open scoped ENNReal

namespace FTPLLinBandit

/-- **The shifted elliptical information matrix `J^v(P_Σ)` and its clipped version
`J^{v,L}(P_Σ)` (Definition 2), as quadratic forms.** Wei, arXiv:2610.17818, Definition 2,
Eqs. (15)–(16), p.12: "J^v(P_Σ) := ∫_{ℝ^d} P_{Σ+vvᵀ}(z)² / P_Σ(z + v) · Σ⁻¹zzᵀΣ⁻¹ dz … the clipped
version J^{v,L}(P_Σ) := ∫_{E_Σ(L)} P_{Σ+vvᵀ}(z)² / P_Σ(z + v) · Σ⁻¹zzᵀΣ⁻¹ dz".

`ellInfoQ f Σ v D u = ∫_D P_{Σ+vvᵀ}(z)² / P_Σ(z + v) · (uᵀΣ⁻¹z)² dz ∈ [0, ∞]`, where `P_Σ` is
`ellDens f Σ`. With `D = univ` it is `uᵀ J^v(P_Σ) u`; with `D = ellipsoid Σ L` it is
`uᵀ J^{v,L}(P_Σ) u`.

**Formalization Note.** `uᵀΣ⁻¹zzᵀΣ⁻¹u = (uᵀΣ⁻¹z)²`. Extended nonnegative value: Table 4 records
that `J^v` is infinite for Student-t₂, which is `∞` here, not a junk `0`. -/
noncomputable def ellInfoQ {d : ℕ} (f : ℝ → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (D : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∫⁻ z in D, ENNReal.ofReal
    (ellDens f (S + vecMulVec (WithLp.ofLp v) (WithLp.ofLp v)) z ^ 2 / ellDens f S (z + v) *
      (WithLp.ofLp u ⬝ᵥ (S⁻¹ *ᵥ WithLp.ofLp z)) ^ 2)

end FTPLLinBandit


