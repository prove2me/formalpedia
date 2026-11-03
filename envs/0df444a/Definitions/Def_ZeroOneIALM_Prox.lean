-- Prove2me | Definitions.Def_ZeroOneIALM_Prox
-- name    : ZeroOneIALM_Prox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:28:54.162536+00:00
-- url     : https://prove2.me/theorems/904aaf77-62f1-43a8-bc42-0b2c723b6acb
-- title:
--   The proximal operator of $\lambda\|(\cdot)_+\|_0$, for vectors and for scalars
-- statement:
--   Let $\lambda,\alpha>0$. For $z\in\mathbb R^n$, the **proximal operator** of $\lambda\|(\cdot)_+\|_0$ with constant $\alpha$ is the set of minimizers
--   $$
--   \mathrm{Prox}_{\alpha\lambda\|(\cdot)_+\|_0}(z):=\arg\min_{u\in\mathbb R^n}\ \lambda\|u_+\|_0+\frac1{2\alpha}\|u-z\|^2 .
--   $$
--   For a scalar $t\in\mathbb R$, the scalar operator is the set of minimizers over $s\in\mathbb R$ of $\lambda\,\ell_{0/1}(s)+\frac1{2\alpha}(s-t)^2$.
--
--   The operator is genuinely set-valued: the objective is discontinuous, and the minimizer need not be unique. Stopping criterion (32b) and P-stationarity are both stated through this set.
--
--   **Formalization Note** Both are instances of the published proximal mapping `GenNewtonSubgrad.ProxReg.prox`, the set of minimizers of $y\mapsto\varphi(y)+\|y-x\|^2/(2\lambda)$ for an extended-real $\varphi$. The definition is the argmin; the closed form is a theorem of this mission.
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, p.5, definition of the proximal operator and display (4)

import Mathlib
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
import Definitions.Def_ZeroOneIALM_ZeroOneLoss

namespace ZeroOneIALM

/-- `Prox_{αλ‖(·)₊‖₀}(z)` for a vector `z ∈ ℝⁿ`, Zhang & Xiu, arXiv:2112.00440v1, p.5: the **set** of
minimizers of `u ↦ λ‖u₊‖₀ + ‖u - z‖² / (2α)`.

**Formalization Note.** It is the published proximal mapping `GenNewtonSubgrad.ProxReg.prox`
applied to `g = λ‖(·)₊‖₀`, a real-valued function coerced to `EReal`, with the constant `α` in the
denominator as on p.5. It is an argmin, not the formula (4); the formula is `property_1_ii`. -/
def proxVec {n : ℕ} (lam α : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  GenNewtonSubgrad.ProxReg.prox (fun u => ((lam * posCount u : ℝ) : EReal)) α z

/-- The scalar operator `Prox_{αλ‖(·)₊‖₀}(zᵢ)` occurring in display (4), arXiv:2112.00440v1, p.5:
the set of minimizers over `s ∈ ℝ` of `λ ℓ_{0/1}(s) + (s - t)² / (2α)`. -/
def proxScalar (lam α t : ℝ) : Set ℝ :=
  GenNewtonSubgrad.ProxReg.prox (fun s => ((lam * zeroOneLoss s : ℝ) : EReal)) α t

end ZeroOneIALM


